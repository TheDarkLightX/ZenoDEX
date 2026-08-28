"""Render the nginx local-testnet config from the template.

Loads `.docker/nginx.local-testnet.conf.template`, substitutes the
upstream addresses + bearer tokens, and writes the result to the
out-dir. The orchestrator mounts the rendered file read-only into the
nginx container.

Security contract:
  - The rendered file CONTAINS the live writer + stdlib bearer tokens.
    It is loopback-only and never committed.
  - The MANIFEST never contains the raw tokens, only their sha256.
  - The UI runtime config (`zenodex-config.json`) NEVER contains tokens
    (nginx injects them server-side).
  - The leak-check helpers below MUST pass before `up` returns.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from pathlib import Path
from string import Template


REPO_ROOT = Path(__file__).resolve().parents[2]
TEMPLATE_PATH = REPO_ROOT / ".docker" / "nginx.local-testnet.conf.template"
UI_SURFACE_CONTRACT_PATH = REPO_ROOT / "tools" / "dex-ui" / "public" / "zenodex-ui-contract.json"

EXPECTED_LOCATION_BLOCKS = (
    "location = /api/health",
    "location = /status",
    "location = /features",
    "location = /tokens",
    "location = /network",
    "location = /public_network_config.json",
    "location ^~ /ledger-bundle/",
    "location = /live",
    "location ^~ /live/",
    "location = /api/pools",
    "location = /api/swap",
    "location = /api/liquidity/create",
    "location = /api/liquidity/add",
    "location = /api/liquidity/remove",
    "location = /api/testnet/faucet",
    "location = /api/tokenomics/status",
    "location = /api/tokenomics/active-participant/claim",
    "location = /tx",
    "location ^~ /api/oracle/",
    "location ^~ /api/",
)

WRITER_MUTATION_LOCATION_BLOCKS = (
    "location = /api/swap",
    "location = /api/liquidity/create",
    "location = /api/liquidity/add",
    "location = /api/liquidity/remove",
    "location = /api/testnet/faucet",
    "location = /api/tokenomics/active-participant/claim",
    "location = /tx",
)


def load_ui_surface_contract(*, contract_path: Path = UI_SURFACE_CONTRACT_PATH) -> dict[str, object]:
    if not contract_path.is_file():
        raise FileNotFoundError(f"UI surface contract missing: {contract_path}")
    parsed = json.loads(contract_path.read_text(encoding="utf-8"))
    if not isinstance(parsed, dict):
        raise ValueError("UI surface contract must be a JSON object")
    schema = parsed.get("schema")
    version = parsed.get("version")
    if schema != "zenodex.dex_ui.surface_contract.v1":
        raise ValueError(f"unexpected UI surface contract schema: {schema!r}")
    if not isinstance(version, str) or not version:
        raise ValueError("UI surface contract version must be non-empty")
    return parsed


def ui_surface_contract_version(*, contract_path: Path = UI_SURFACE_CONTRACT_PATH) -> str:
    return str(load_ui_surface_contract(contract_path=contract_path)["version"])


def ui_surface_contract_hash(*, contract_path: Path = UI_SURFACE_CONTRACT_PATH) -> str:
    contract = load_ui_surface_contract(contract_path=contract_path)
    canonical = json.dumps(contract, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return "sha256:" + hashlib.sha256(canonical).hexdigest()


@dataclass(frozen=True)
class NginxRenderInputs:
    writer_upstream: str  # e.g. "zeno-ledger-writer:8787"
    stdlib_upstream: str  # e.g. "zenodex-api:8000"
    oracle_upstream: str  # e.g. "zenodex-oracle:9100"
    writer_token: str
    stdlib_token: str


def render_nginx_conf(inputs: NginxRenderInputs, *, template_path: Path = TEMPLATE_PATH) -> str:
    """Substitute placeholders in the template and return the rendered
    nginx config string. Raises if any placeholder is missing."""
    if not template_path.is_file():
        raise FileNotFoundError(f"nginx template missing: {template_path}")
    if not inputs.writer_token or not inputs.stdlib_token:
        raise ValueError("writer_token and stdlib_token must be non-empty")
    for upstream in (inputs.writer_upstream, inputs.stdlib_upstream, inputs.oracle_upstream):
        if not upstream or ":" not in upstream:
            raise ValueError(f"upstream must be 'host:port', got {upstream!r}")

    # The template contains nginx variables like `$binary_remote_addr` and
    # `$remote_addr` that collide with string.Template's placeholder syntax.
    # Use safe_substitute (leaves unknown $vars alone) and then explicitly
    # check that OUR placeholders all got substituted.
    template = Template(template_path.read_text(encoding="utf-8"))
    rendered = template.safe_substitute(
        WRITER_UPSTREAM=inputs.writer_upstream,
        STDLIB_UPSTREAM=inputs.stdlib_upstream,
        ORACLE_UPSTREAM=inputs.oracle_upstream,
        WRITER_TOKEN=inputs.writer_token,
        STDLIB_TOKEN=inputs.stdlib_token,
    )

    unsubstituted = [
        name
        for name in ("WRITER_UPSTREAM", "STDLIB_UPSTREAM", "ORACLE_UPSTREAM", "WRITER_TOKEN", "STDLIB_TOKEN")
        if f"${{{name}}}" in rendered or f"${name}" in rendered
    ]
    if unsubstituted:
        raise ValueError(
            f"nginx template placeholder(s) not substituted: {unsubstituted}. "
            "Template and renderer have drifted."
        )

    errors = validate_rendered_conf(rendered, inputs=inputs)
    if errors:
        raise ValueError(f"rendered nginx config failed validation: {errors}")
    return rendered


def validate_rendered_conf(rendered: str, *, inputs: NginxRenderInputs) -> list[str]:
    """Structural checks on the rendered nginx config. Returns errors list."""
    errors: list[str] = []
    for block in EXPECTED_LOCATION_BLOCKS:
        if block not in rendered:
            errors.append(f"missing expected location block: {block!r}")
    # Bearer header must appear for both writer and stdlib (oracle does NOT
    # get token injection per the design).
    if f"Bearer {inputs.writer_token}" not in rendered:
        errors.append("writer bearer token injection missing")
    if f"Bearer {inputs.stdlib_token}" not in rendered:
        errors.append("stdlib bearer token injection missing")
    # Each upstream must be referenced exactly where expected.
    for upstream in (inputs.writer_upstream, inputs.stdlib_upstream, inputs.oracle_upstream):
        if upstream not in rendered:
            errors.append(f"upstream {upstream!r} missing from rendered config")
    if "map $http_origin $zenodex_origin_ok" not in rendered:
        errors.append("origin guard map missing")
    if 'map "$request_method:$http_content_type" $zenodex_write_content_type_ok' not in rendered:
        errors.append("writer content-type guard map missing")
    for block in WRITER_MUTATION_LOCATION_BLOCKS:
        try:
            chunk = _extract_location_block(rendered, block)
        except ValueError as exc:
            errors.append(str(exc))
            continue
        if "if ($zenodex_origin_ok = 0) { return 403; }" not in chunk:
            errors.append(f"{block}: origin guard missing")
        if "if ($zenodex_write_content_type_ok = 0) { return 415; }" not in chunk:
            errors.append(f"{block}: JSON content-type guard missing")
    try:
        stdlib_chunk = _extract_location_block(rendered, "location ^~ /api/ {")
    except ValueError as exc:
        errors.append(str(exc))
    else:
        if "if ($zenodex_origin_ok = 0) { return 403; }" not in stdlib_chunk:
            errors.append("stdlib API origin guard missing")
    return errors


def _extract_location_block(rendered: str, marker: str) -> str:
    marker_idx = rendered.find(marker)
    if marker_idx < 0:
        raise ValueError(f"missing expected location block: {marker!r}")
    brace_idx = rendered.find("{", marker_idx)
    if brace_idx < 0:
        raise ValueError(f"malformed location block: {marker!r}")
    depth = 0
    for idx in range(brace_idx, len(rendered)):
        char = rendered[idx]
        if char == "{":
            depth += 1
        elif char == "}":
            depth -= 1
            if depth == 0:
                return rendered[marker_idx:idx + 1]
    raise ValueError(f"unterminated location block: {marker!r}")


def write_rendered_conf(rendered: str, *, out_path: Path) -> None:
    out_path.parent.mkdir(parents=True, exist_ok=True)
    # Permissions: 0o600 — the file holds bearer tokens. The nginx
    # container reads it via bind mount; the host user owns it.
    out_path.write_text(rendered, encoding="utf-8")
    try:
        out_path.chmod(0o600)
    except OSError:
        # Best effort; some filesystems (Windows, network mounts) don't support chmod
        pass


def assert_no_token_in_file(file_path: Path, token: str) -> None:
    """Defensive: assert `token` does NOT appear in `file_path`. Used to
    verify that the manifest and UI runtime config don't accidentally
    leak bearer tokens."""
    if not file_path.is_file():
        return
    if not token:
        raise ValueError("token must be non-empty")
    body = file_path.read_text(encoding="utf-8")
    if token in body:
        raise AssertionError(
            f"SECURITY: bearer token literal leaked into {file_path}. "
            "Refusing to proceed."
        )


def render_runtime_config(*, demo_mode: bool = False, extra: dict[str, object] | None = None) -> str:
    """Render `zenodex-config.json` for the UI. Loaded at runtime by
    `tools/dex-ui/src/main.jsx` into `window.__ZENODEX_CONFIG__`.

    The runtime config NEVER contains bearer tokens. The browser client
    already calls `/api/*` relative paths; nginx injects the right token
    server-side.
    """
    default_external_signer: dict[str, object] = {
        "schema": "zenodex/dex-ui/runtime-default-external-signer/v0",
        "signerSecurityProfile": "native-desktop-loopback-signer-v0",
        "connectUrl": "http://127.0.0.1:8799/public-receipt",
        "signTauTransactionPayloadUrl": "http://127.0.0.1:8799/sign-tau-transaction-payload",
        "signDexIntentForEngineUrl": "http://127.0.0.1:8799/sign-dex-intent",
    }
    config: dict[str, object] = {
        "demoMode": bool(demo_mode),
        "allowDemoMode": False,
        "apiBase": "",
        "zenoOracleApiBase": "",
        "oracleApiBase": "",
        "deployment": "local-testnet",
        "allowBrowserKeyGeneration": True,
        "allowDefaultExternalSigner": True,
        "defaultExternalSigner": default_external_signer,
        "perpsWalletUiEnabled": False,
        "zusdTauWalletUiEnabled": False,
        "zusdMonetaryWalletUiEnabled": False,
        "uiSurfaceContractSchema": "zenodex.dex_ui.surface_contract.v1",
        "uiSurfaceContractVersion": ui_surface_contract_version(),
        "uiSurfaceContractHash": ui_surface_contract_hash(),
    }
    if extra:
        for key, value in extra.items():
            if key in (
                "demoMode",
                "allowDemoMode",
                "apiBase",
                "zenoOracleApiBase",
                "oracleApiBase",
                "deployment",
                "allowBrowserKeyGeneration",
                "allowDefaultExternalSigner",
                "defaultExternalSigner",
                "perpsWalletUiEnabled",
                "zusdTauWalletUiEnabled",
                "zusdMonetaryWalletUiEnabled",
                "uiSurfaceContractSchema",
                "uiSurfaceContractVersion",
                "uiSurfaceContractHash",
            ):
                raise ValueError(f"extra runtime-config key {key!r} conflicts with built-in")
            config[key] = value
    return json.dumps(config, indent=2, sort_keys=True) + "\n"
