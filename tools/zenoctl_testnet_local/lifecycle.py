"""`up`/`down`/`status` lifecycle for `zenoctl testnet local`.

The orchestrator drives:
  1. Preflight (external/tau-testnet present, no conflicting stack without --force).
  2. Generate deterministic fixture bundle with accepted live profile shapes.
  3. Initialize a writable Oracle home under the local out-dir.
  4. Render nginx config and UI runtime config into <out_dir>/rendered/.
  5. Write manifest at <out_dir>/local_testnet_manifest.json.
  6. `compose up -d` the local-testnet overlay.
  7. Wait for base service health through nginx.
  8. Seed ledger/zUSD/perps state so the mounted tabs are actually usable.
  9. Run lane readiness checks and print a short summary.
"""

from __future__ import annotations

import json
import os
import re
import secrets
import shutil
import subprocess
import sys
import tempfile
import textwrap
import time
import urllib.error
import urllib.parse
import urllib.request
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

from src.integration.zusd_tau_token import derive_zusd_tau_asset_id

from . import compose as cm
from . import fixtures as fx
from . import manifest as mf
from . import nginx as ng


REPO_ROOT = Path(__file__).resolve().parents[2]
COMPOSE_FILE = REPO_ROOT / "docker-compose.local-testnet.yml"
NGINX_TEMPLATE = REPO_ROOT / ".docker" / "nginx.local-testnet.conf.template"

DEFAULT_UI_PORT = 18080
DEFAULT_CHAIN_ID = "zeno-ledger-localtest-v0"
DEFAULT_NETWORK_ID = "zeno-ledger-localtest-v0"
DEFAULT_HEALTH_TIMEOUT_S = 120.0

OPERATOR_TOOLS_IMAGE = "zenodex/operator-tools:local"
TAU_LOCAL_IMAGE = "zenodex/tau-local:local-testnet"
UI_NGINX_IMAGE = "zenodex:local"

DEFAULT_MARKET_ID = "perp:ch2p:localtest-zusd-perps-v1"
E8 = 100_000_000
DEFAULT_ORACLE_PRICE_E8 = 20_000_000 * E8
DEFAULT_ZUSD_BOOTSTRAP_COLLATERAL_E8 = 1_000
DEFAULT_ZUSD_BOOTSTRAP_MINT_E8 = 100 * E8
SMOKE_NITRO_PCR0 = "a" * 96
SMOKE_NITRO_PCR8 = "b" * 96
SMOKE_CONFIDENTIAL_MEASUREMENT = f"nitro:pcr0:{SMOKE_NITRO_PCR0}:pcr8:{SMOKE_NITRO_PCR8}"
SMOKE_CONFIDENTIAL_POLICY_DIGEST = "0x" + ("d" * 64)


@dataclass(frozen=True)
class UpOptions:
    out_dir: Path
    chain_id: str = DEFAULT_CHAIN_ID
    network_id: str = DEFAULT_NETWORK_ID
    ui_port: int = DEFAULT_UI_PORT
    engine: str = "auto"  # "auto" | "docker" | "podman"
    force: bool = False
    health_timeout_s: float = DEFAULT_HEALTH_TIMEOUT_S
    seed_override_hex: str | None = None
    use_random_seed: bool = False


@dataclass(frozen=True)
class DownOptions:
    out_dir: Path
    engine: str = "auto"


@dataclass(frozen=True)
class StatusOptions:
    out_dir: Path
    engine: str = "auto"
    as_json: bool = False


@dataclass(frozen=True)
class SmokeOptions:
    out_dir: Path
    engine: str = "auto"
    browser: str = "auto"  # "auto" | "off" | "required"
    chrome_bin: Path | None = None
    browser_timeout_s: float = 60.0


@dataclass(frozen=True)
class LogsOptions:
    out_dir: Path
    engine: str = "auto"
    service: str | None = None
    tail: int | None = None


@dataclass(frozen=True)
class ResetOptions:
    out_dir: Path
    engine: str = "auto"


def cmd_up(opts: UpOptions) -> int:
    paths = mf.ManifestPaths.from_out_dir(opts.out_dir)
    existing_manifest = _load_manifest_if_present(paths.manifest_path)
    if existing_manifest is not None:
        if not opts.force:
            return _cmd_up_existing(opts=opts, paths=paths, manifest=existing_manifest)
        _log("preflight", f"force reset requested for {paths.out_dir}")
        _reset_stack(paths=paths, engine_name=opts.engine, manifest=existing_manifest)

    paths.out_dir.mkdir(parents=True, exist_ok=True)
    paths.reports_dir.mkdir(parents=True, exist_ok=True)
    cm.check_external_tau_testnet_present(REPO_ROOT)
    cm.check_host_port_free(opts.ui_port)

    engine = cm.detect_engine(opts.engine)
    _log("preflight", f"engine={engine.binary}")

    seed = _resolve_fixture_seed(opts)
    _log("fixtures", "generating deterministic fixture bundle")
    bundle = fx.generate_fixture_bundle(
        out_dir=paths.out_dir,
        chain_id=opts.chain_id,
        network_id=opts.network_id,
        seed_override_hex=seed.hex(),
        use_random=False,
    )
    key_bundle = _load_json_file(bundle.key_bundle, label="key bundle")
    roles = _role_materials(key_bundle)

    _log("oracle", "initializing Oracle home")
    _init_oracle_home(paths.oracle_home_dir)
    _install_oracle_authority_profile(
        home_dir=paths.oracle_home_dir,
        authority_profile_path=bundle.oracle_authority_profile,
    )

    writer_token = fx.derive_writer_token(seed)
    stdlib_token = _derive_stdlib_token(seed)

    _log("render", "rendering nginx + UI runtime config")
    rendered_nginx = ng.render_nginx_conf(
        ng.NginxRenderInputs(
            writer_upstream="zeno-ledger-writer:8787",
            stdlib_upstream="zenodex-api:8000",
            oracle_upstream="zenodex-oracle:9100",
            writer_token=writer_token,
            stdlib_token=stdlib_token,
        ),
        template_path=NGINX_TEMPLATE,
    )
    ng.write_rendered_conf(rendered_nginx, out_path=paths.rendered_nginx)
    paths.rendered_runtime_config.parent.mkdir(parents=True, exist_ok=True)
    paths.rendered_runtime_config.write_text(ng.render_runtime_config(demo_mode=False), encoding="utf-8")

    manifest = mf.build_manifest(
        out_dir=paths.out_dir,
        chain_id=opts.chain_id,
        network_id=opts.network_id,
        ports={"ui": opts.ui_port},
        service_urls={
            "ui": f"http://127.0.0.1:{opts.ui_port}",
            "stdlib_api": "compose://zenodex-api:8000",
            "writer": "compose://zeno-ledger-writer:8787",
            "oracle": "compose://zenodex-oracle:9100",
            "tau": "compose://tau-local:65432",
        },
        image_refs={
            "operator_tools": OPERATOR_TOOLS_IMAGE,
            "tau_local": TAU_LOCAL_IMAGE,
            "ui_nginx": UI_NGINX_IMAGE,
        },
        enabled_lanes=[
            "DEX_API_ENABLED",
            "PERPS_API_ENABLED",
            "PERPS_WALLET_API_ENABLED",
            "ZUSD_API_ENABLED",
            "ZUSD_TAU_WALLET_API_ENABLED",
            "ZUSD_MONETARY_WALLET_API_ENABLED",
            "AUTOTRADER_LIVE_API_ENABLED",
            "CONFIDENTIAL_ATTESTATION_API_ENABLED",
        ],
        fixture_paths=bundle.as_manifest_paths(),
        ledger_bundle_manifest=str(paths.out_dir / "ledger" / "public_testnet_manifest.json"),
        writer_token=writer_token,
        created_at_ms=int(time.time() * 1000),
    )
    mf.save_manifest(manifest, paths.manifest_path)
    ng.assert_no_token_in_file(paths.manifest_path, writer_token)
    ng.assert_no_token_in_file(paths.manifest_path, stdlib_token)
    ng.assert_no_token_in_file(paths.rendered_runtime_config, writer_token)
    ng.assert_no_token_in_file(paths.rendered_runtime_config, stdlib_token)

    env = _compose_env(
        paths=paths,
        ui_port=opts.ui_port,
        chain_id=opts.chain_id,
        network_id=opts.network_id,
        writer_token=writer_token,
        stdlib_token=stdlib_token,
        roles=roles,
    )
    project = str(manifest["compose_project"])

    _log("compose", f"compose up project={project}")
    cm.compose_up(
        engine=engine,
        project_name=project,
        compose_files=[COMPOSE_FILE],
        env=env,
        extra_args=["--build"],
    )

    try:
        ui_base = f"http://127.0.0.1:{opts.ui_port}"
        _wait_for_base_services(ui_base=ui_base, timeout_s=opts.health_timeout_s)

        _log("seed", "seeding ledger writer with initial pool and faucet state")
        controller_report = _seed_ledger_controller(
            engine=engine,
            project=project,
            env=env,
            chain_id=opts.chain_id,
            timeout_s=max(float(opts.health_timeout_s), 900.0),
        )
        _write_json(paths.reports_dir / "ledger_controller_report.json", controller_report)

        _log("seed", "seeding zUSD monetary state and perps market")
        seed_report = _seed_api_state(
            engine=engine,
            project=project,
            env=env,
            roles=roles,
            chain_id=opts.chain_id,
        )
        _write_json(paths.reports_dir / "api_seed_report.json", seed_report)

        readiness = _wait_for_lane_readiness(ui_base=ui_base, timeout_s=opts.health_timeout_s)
        _write_json(paths.reports_dir / "readiness_report.json", readiness)
    except Exception as exc:
        _log("failure", f"{type(exc).__name__}: {exc}")
        _tail_service_logs(engine=engine, project=project, env=env)
        cm.compose_down(
            engine=engine,
            project_name=project,
            compose_files=[COMPOSE_FILE],
            remove_volumes=False,
            env=env,
        )
        return 1

    _log("done", f"stack up: http://127.0.0.1:{opts.ui_port}")
    sys.stderr.write(_summary_text(manifest))
    return 0


def _cmd_up_existing(*, opts: UpOptions, paths: mf.ManifestPaths, manifest: Mapping[str, Any]) -> int:
    """Restart an existing local-testnet stack from its saved artifacts.

    The manifest intentionally stores token hashes only. The only place raw
    local bearer tokens persist is the rendered nginx config inside the
    operator-selected out-dir. For restart, recover those tokens from the
    rendered config, verify the writer token hash against the manifest, and
    rebuild the compose environment without printing secrets.
    """
    engine = cm.detect_engine(opts.engine)
    manifest_port = _manifest_ui_port(manifest)
    if opts.ui_port != DEFAULT_UI_PORT and opts.ui_port != manifest_port:
        _log(
            "preflight",
            f"existing manifest uses ui_port={manifest_port}; use --force to recreate on {opts.ui_port}",
        )
        return 2

    project = str(manifest["compose_project"])
    env = _runtime_env_for_existing_manifest(manifest=manifest, paths=paths)
    _log("preflight", f"existing manifest detected; restarting compose project={project}")
    cm.compose_up(
        engine=engine,
        project_name=project,
        compose_files=[COMPOSE_FILE],
        env=env,
        extra_args=["--build"],
    )

    ui_base = str((manifest.get("service_urls") or {}).get("ui") or f"http://127.0.0.1:{manifest_port}")
    try:
        _wait_for_base_services(ui_base=ui_base, timeout_s=opts.health_timeout_s)
        readiness = _wait_for_lane_readiness(ui_base=ui_base, timeout_s=opts.health_timeout_s)
        _write_json(paths.reports_dir / "readiness_report.json", readiness)
    except Exception as exc:
        _log("failure", f"{type(exc).__name__}: {exc}")
        _tail_service_logs(engine=engine, project=project, env=env)
        cm.compose_down(
            engine=engine,
            project_name=project,
            compose_files=[COMPOSE_FILE],
            remove_volumes=False,
            env=env,
        )
        return 1

    _log("done", f"stack up: {ui_base}")
    sys.stderr.write(_summary_text(manifest))
    return 0


def cmd_down(opts: DownOptions) -> int:
    paths = mf.ManifestPaths.from_out_dir(opts.out_dir)
    manifest = _load_manifest_if_present(paths.manifest_path)
    if manifest is None:
        _log("down", f"no manifest at {paths.manifest_path}; nothing to do")
        return 0
    engine = cm.detect_engine(opts.engine)
    project = str(manifest["compose_project"])
    _log("down", f"compose down project={project} (preserving volumes and out-dir)")
    cm.compose_down(
        engine=engine,
        project_name=project,
        compose_files=[COMPOSE_FILE],
        remove_volumes=False,
        env=_lifecycle_env_for_compose(manifest, paths),
    )
    return 0


def cmd_status(opts: StatusOptions) -> int:
    paths = mf.ManifestPaths.from_out_dir(opts.out_dir)
    manifest = _load_manifest_if_present(paths.manifest_path)
    if manifest is None:
        report = {"ok": False, "status": "no_manifest", "manifest_path": str(paths.manifest_path)}
        _emit_status(report, as_json=opts.as_json)
        return 1

    engine = cm.detect_engine(opts.engine)
    services = cm.compose_ps_json(
        engine=engine,
        project_name=str(manifest["compose_project"]),
        compose_files=[COMPOSE_FILE],
        env=_lifecycle_env_for_compose(manifest, paths),
    )
    ui_base = str(manifest["service_urls"]["ui"])
    base_health = _probe_base_services(ui_base=ui_base)
    lanes = _collect_lane_readiness(ui_base=ui_base) if base_health["ok"] else {"ok": False, "lanes": {}}
    report = {
        "ok": bool(base_health["ok"]) and bool(lanes.get("ok")) and len(services) > 0,
        "manifest_path": str(paths.manifest_path),
        "compose_project": manifest["compose_project"],
        "ui_url": ui_base,
        "base_health": base_health,
        "lanes": lanes,
        "service_count": len(services),
        "services": [
            {
                "name": svc.get("Service") or svc.get("Name") or "<unknown>",
                "state": svc.get("State") or svc.get("Status") or "<unknown>",
                "health": svc.get("Health") or "<n/a>",
            }
            for svc in services
        ],
    }
    _emit_status(report, as_json=opts.as_json)
    return 0 if report["ok"] else 1


def cmd_smoke(opts: SmokeOptions) -> int:
    paths = mf.ManifestPaths.from_out_dir(opts.out_dir)
    manifest = _load_manifest_if_present(paths.manifest_path)
    if manifest is None:
        report = {"ok": False, "status": "no_manifest", "manifest_path": str(paths.manifest_path)}
        _write_json(paths.reports_dir / "local_smoke_report.json", report)
        print(json.dumps(report, indent=2, sort_keys=True))
        return 1

    engine = cm.detect_engine(opts.engine)
    services = cm.compose_ps_json(
        engine=engine,
        project_name=str(manifest["compose_project"]),
        compose_files=[COMPOSE_FILE],
        env=_lifecycle_env_for_compose(manifest, paths),
    )
    ui_base = str(manifest["service_urls"]["ui"])
    base_health = _probe_base_services(ui_base=ui_base)
    readiness = (
        _collect_lane_readiness(ui_base=ui_base)
        if base_health["ok"]
        else {"ok": False, "checks": {}, "lanes": {}}
    )
    report: dict[str, Any] = {
        "schema": "zenodex.local_testnet.smoke_report.v1",
        "ok": False,
        "manifest_path": str(paths.manifest_path),
        "compose_project": manifest["compose_project"],
        "ui_url": ui_base,
        "service_count": len(services),
        "base_health": base_health,
        "readiness": readiness,
        "feature_checks": {},
        "browser_checks": {"mode": opts.browser, "checks": {}, "skipped": False},
    }

    if base_health["ok"] and readiness.get("ok") is True:
        try:
            report["feature_checks"] = _run_feature_smoke(ui_base=ui_base, paths=paths, manifest=manifest)
        except Exception as exc:
            report["feature_checks"] = {"ok": False, "error": f"{type(exc).__name__}: {exc}"}

    browser_ok = True
    if opts.browser != "off":
        browser_report = _run_browser_smoke(
            ui_base=ui_base,
            paths=paths,
            manifest=manifest,
            chrome_bin=opts.chrome_bin,
            mode=opts.browser,
            timeout_s=opts.browser_timeout_s,
        )
        report["browser_checks"] = browser_report
        browser_ok = bool(browser_report.get("ok"))

    feature_ok = bool((report.get("feature_checks") or {}).get("ok"))
    report["ok"] = (
        bool(base_health["ok"])
        and bool(readiness.get("ok"))
        and feature_ok
        and browser_ok
        and len(services) > 0
    )
    _write_json(paths.reports_dir / "local_smoke_report.json", report)
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


def cmd_logs(opts: LogsOptions) -> int:
    paths = mf.ManifestPaths.from_out_dir(opts.out_dir)
    manifest = _load_manifest_if_present(paths.manifest_path)
    if manifest is None:
        _log("logs", f"no manifest at {paths.manifest_path}")
        return 1
    engine = cm.detect_engine(opts.engine)
    output = cm.compose_logs(
        engine=engine,
        project_name=str(manifest["compose_project"]),
        compose_files=[COMPOSE_FILE],
        service=opts.service,
        tail=opts.tail,
        env=_lifecycle_env_for_compose(manifest, paths),
    )
    sys.stdout.write(output)
    return 0


def cmd_reset(opts: ResetOptions) -> int:
    paths = mf.ManifestPaths.from_out_dir(opts.out_dir)
    manifest = _load_manifest_if_present(paths.manifest_path)
    _reset_stack(paths=paths, engine_name=opts.engine, manifest=manifest)
    return 0


_LIFECYCLE_PLACEHOLDER = "unused-for-lifecycle-op"
_BEARER_HEADER_RE = re.compile(r'proxy_set_header\s+Authorization\s+"Bearer\s+([^"]+)";')

# Directories that would be catastrophic to rmtree. We don't try to limit
# the out-dir to /tmp or ~/ — legitimate operators may use /var/lib or
# similar — but `/`, the user home itself, and core system dirs are never
# valid local-testnet out-dirs and must never be rm-rf'd by accident.
_FORBIDDEN_RESET_DIRS: tuple[str, ...] = (
    "/",
    "/root",
    "/home",
    "/etc",
    "/usr",
    "/var",
    "/bin",
    "/sbin",
    "/opt",
    "/lib",
    "/lib64",
    "/dev",
    "/proc",
    "/sys",
    "/boot",
    "/mnt",
    "/srv",
)


def _refuse_unsafe_reset_target(out_dir: Path) -> None:
    """Refuse destructive operations on system roots or the user's home
    directory. A typo like `--out-dir /` must not be able to wipe the
    filesystem."""
    raw = str(Path(out_dir).absolute())
    resolved = str(Path(out_dir).resolve())
    if raw in _FORBIDDEN_RESET_DIRS or resolved in _FORBIDDEN_RESET_DIRS:
        raise ValueError(
            f"refusing destructive operation on {resolved!r}: pick a dedicated "
            "--out-dir (e.g. /tmp/zen-local) instead of a system path."
        )
    home = str(Path.home().resolve())
    if home and resolved == home:
        raise ValueError(
            f"refusing destructive operation on the user home directory {home!r}. "
            "Use a dedicated subdirectory (e.g. ~/zen-local)."
        )


def _reset_stack(*, paths: mf.ManifestPaths, engine_name: str, manifest: Mapping[str, Any] | None) -> None:
    _refuse_unsafe_reset_target(paths.out_dir)
    # If there is no manifest and the out-dir contains unrelated entries,
    # refuse to rmtree it. An empty/nonexistent dir is safe to skip.
    if manifest is None and paths.out_dir.exists():
        try:
            entries = {p.name for p in paths.out_dir.iterdir()}
        except OSError:
            entries = set()
        known = {"fixtures", "rendered", "reports", "oracle-home", "ledger", mf.MANIFEST_FILENAME}
        unexpected = entries - known
        if unexpected:
            raise ValueError(
                f"refusing to reset {paths.out_dir}: no manifest, and the directory "
                f"contains unrelated entries {sorted(unexpected)[:5]}. Move or empty it first."
            )
    if manifest is not None:
        engine = cm.detect_engine(engine_name)
        cm.compose_down(
            engine=engine,
            project_name=str(manifest["compose_project"]),
            compose_files=[COMPOSE_FILE],
            remove_volumes=True,
            env=_lifecycle_env_for_compose(dict(manifest), paths),
        )
    shutil.rmtree(paths.out_dir, ignore_errors=True)


def _compose_env(
    *,
    paths: mf.ManifestPaths,
    ui_port: int,
    chain_id: str,
    network_id: str,
    writer_token: str,
    stdlib_token: str,
    roles: Mapping[str, Mapping[str, Any]],
) -> dict[str, str]:
    return {
        "ZENO_LEDGER_WRITER_TOKEN": writer_token,
        "DEMO_API_TOKEN": stdlib_token,
        "RENDERED_NGINX_CONF_PATH": str(paths.rendered_nginx),
        "RENDERED_RUNTIME_CONFIG_PATH": str(paths.rendered_runtime_config),
        "FIXTURES_DIR": str(paths.fixtures_dir),
        "ORACLE_HOME_DIR": str(paths.oracle_home_dir),
        "HOST_UID": str(_host_uid()),
        "HOST_GID": str(_host_gid()),
        "UI_PORT": str(ui_port),
        "CHAIN_ID": chain_id,
        "NETWORK_ID": network_id,
        "TAU_DEX_TOKEN_OPERATOR_PUBKEY": str(roles["operator"]["public_key"]),
        "TAU_DEX_ORACLE_PUBKEY": str(roles["oracle_authority"]["public_key"]),
        "TAU_DEX_ZUSD_ORACLE_PUBKEY": str(roles["alice"]["public_key"]),
    }


def _lifecycle_env_for_compose(manifest: dict[str, Any], paths: mf.ManifestPaths) -> dict[str, str]:
    host_paths = manifest.get("host_paths") if isinstance(manifest.get("host_paths"), Mapping) else {}
    return {
        "ZENO_LEDGER_WRITER_TOKEN": _LIFECYCLE_PLACEHOLDER,
        "DEMO_API_TOKEN": _LIFECYCLE_PLACEHOLDER,
        "RENDERED_NGINX_CONF_PATH": str(
            ((manifest.get("rendered_paths") or {}).get("nginx_conf"))
            or paths.rendered_nginx
        ),
        "RENDERED_RUNTIME_CONFIG_PATH": str(
            ((manifest.get("rendered_paths") or {}).get("runtime_config"))
            or paths.rendered_runtime_config
        ),
        "FIXTURES_DIR": str(host_paths.get("fixtures_dir") or paths.fixtures_dir),
        "ORACLE_HOME_DIR": str(host_paths.get("oracle_home_dir") or paths.oracle_home_dir),
        "HOST_UID": str(_host_uid()),
        "HOST_GID": str(_host_gid()),
        "UI_PORT": str(manifest["ports"]["ui"]),
        "CHAIN_ID": str(manifest["chain_id"]),
        "NETWORK_ID": str(manifest["network_id"]),
        "TAU_DEX_TOKEN_OPERATOR_PUBKEY": _LIFECYCLE_PLACEHOLDER,
        "TAU_DEX_ORACLE_PUBKEY": _LIFECYCLE_PLACEHOLDER,
        "TAU_DEX_ZUSD_ORACLE_PUBKEY": _LIFECYCLE_PLACEHOLDER,
    }


def _runtime_env_for_existing_manifest(*, manifest: Mapping[str, Any], paths: mf.ManifestPaths) -> dict[str, str]:
    writer_token, stdlib_token = _recover_tokens_from_rendered_nginx(manifest=manifest, paths=paths)
    expected_writer_hash = manifest.get("writer_token_sha256")
    actual_writer_hash = mf.writer_token_sha256(writer_token)
    if expected_writer_hash != actual_writer_hash:
        raise ValueError("rendered nginx writer token does not match manifest writer_token_sha256")

    fixture_paths = manifest.get("fixture_paths") if isinstance(manifest.get("fixture_paths"), Mapping) else {}
    key_bundle_path = Path(str(fixture_paths.get("key_bundle") or (paths.fixtures_dir / "keys.json")))
    key_bundle = _load_json_file(key_bundle_path, label="key bundle")
    roles = _role_materials(key_bundle)

    return _compose_env(
        paths=paths,
        ui_port=_manifest_ui_port(manifest),
        chain_id=str(manifest["chain_id"]),
        network_id=str(manifest["network_id"]),
        writer_token=writer_token,
        stdlib_token=stdlib_token,
        roles=roles,
    )


def _recover_tokens_from_rendered_nginx(*, manifest: Mapping[str, Any], paths: mf.ManifestPaths) -> tuple[str, str]:
    rendered_paths = manifest.get("rendered_paths") if isinstance(manifest.get("rendered_paths"), Mapping) else {}
    nginx_path = Path(str(rendered_paths.get("nginx_conf") or paths.rendered_nginx))
    if not nginx_path.is_file():
        raise FileNotFoundError(f"rendered nginx config missing: {nginx_path}")
    rendered = nginx_path.read_text(encoding="utf-8")

    writer_block = _extract_nginx_location_block(rendered, "location = /api/pools")
    stdlib_block = _extract_nginx_location_block(rendered, "location = /api/health")
    writer_token = _extract_bearer_token(writer_block, label="writer")
    stdlib_token = _extract_bearer_token(stdlib_block, label="stdlib")
    return writer_token, stdlib_token


def _extract_nginx_location_block(rendered: str, marker: str) -> str:
    marker_idx = rendered.find(marker)
    if marker_idx < 0:
        raise ValueError(f"rendered nginx config missing {marker!r} location block")
    brace_idx = rendered.find("{", marker_idx)
    if brace_idx < 0:
        raise ValueError(f"rendered nginx config has malformed {marker!r} location block")
    depth = 0
    for idx in range(brace_idx, len(rendered)):
        char = rendered[idx]
        if char == "{":
            depth += 1
        elif char == "}":
            depth -= 1
            if depth == 0:
                return rendered[marker_idx:idx + 1]
    raise ValueError(f"rendered nginx config has unterminated {marker!r} location block")


def _extract_bearer_token(block: str, *, label: str) -> str:
    match = _BEARER_HEADER_RE.search(block)
    if not match:
        raise ValueError(f"rendered nginx {label} bearer token missing")
    token = match.group(1).strip()
    if not token:
        raise ValueError(f"rendered nginx {label} bearer token empty")
    return token


def _manifest_ui_port(manifest: Mapping[str, Any]) -> int:
    ports = manifest.get("ports")
    if not isinstance(ports, Mapping):
        raise ValueError("manifest ports missing")
    port = ports.get("ui")
    if not isinstance(port, int) or not (1 <= port <= 65535):
        raise ValueError(f"manifest ui port invalid: {port!r}")
    return port


def _resolve_fixture_seed(opts: UpOptions) -> bytes:
    if opts.seed_override_hex is not None:
        try:
            seed = bytes.fromhex(opts.seed_override_hex)
        except ValueError as exc:
            raise ValueError(f"--seed must be valid hex: {exc}") from None
        if len(seed) != 32:
            raise ValueError(f"--seed must be 32 bytes, got {len(seed)}")
        return seed
    if opts.use_random_seed:
        return secrets.token_bytes(32)
    return fx.derive_seed(out_dir=opts.out_dir, chain_id=opts.chain_id)


def _host_uid() -> int:
    getuid = getattr(os, "getuid", None)
    return int(getuid()) if callable(getuid) else 1000


def _host_gid() -> int:
    getgid = getattr(os, "getgid", None)
    return int(getgid()) if callable(getgid) else 1000


def _derive_stdlib_token(seed: bytes) -> str:
    import hashlib

    if len(seed) != 32:
        raise ValueError("seed must be 32 bytes")
    domain = b"zenodex.local_testnet.stdlib_api_token.v1"
    return hashlib.blake2b(seed + b"|" + domain, digest_size=32).hexdigest()


def _load_manifest_if_present(path: Path) -> dict[str, Any] | None:
    if not path.exists():
        return None
    return mf.load_manifest(path)


def _load_json_file(path: Path, *, label: str) -> dict[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, dict):
        raise ValueError(f"{label} must be a JSON object")
    return obj


def _role_materials(key_bundle: Mapping[str, Any]) -> dict[str, dict[str, Any]]:
    roles = key_bundle.get("roles")
    if not isinstance(roles, Mapping):
        raise ValueError("key bundle roles missing")
    out: dict[str, dict[str, Any]] = {}
    for role_name, raw in roles.items():
        if not isinstance(raw, Mapping):
            raise ValueError(f"key bundle role {role_name!r} invalid")
        privkey_hex = str(raw.get("privkey_hex") or "")
        public_key = str(raw.get("public_key") or "")
        if not privkey_hex or not public_key:
            raise ValueError(f"key bundle role {role_name!r} missing key material")
        out[str(role_name)] = {
            "privkey_hex": privkey_hex,
            "public_key": public_key,
            "privkey_int": int(privkey_hex[2:] if privkey_hex.startswith("0x") else privkey_hex, 16),
        }
    return out


def _init_oracle_home(home_dir: Path) -> None:
    if home_dir.exists():
        shutil.rmtree(home_dir)
    home_dir.parent.mkdir(parents=True, exist_ok=True)
    cmd = [sys.executable, "tools/zenodex_oracle.py", "init", "--home", str(home_dir)]
    result = subprocess.run(
        cmd,
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode != 0:
        raise RuntimeError(
            f"oracle init failed (exit {result.returncode}): {result.stderr.strip() or result.stdout.strip()}"
        )


def _install_oracle_authority_profile(*, home_dir: Path, authority_profile_path: Path) -> None:
    authority_dir = home_dir / "authority"
    authority_dir.mkdir(parents=True, exist_ok=True)
    target = authority_dir / "production_authority_profile.json"
    shutil.copy2(authority_profile_path, target)


def _seed_ledger_controller(
    *,
    engine: cm.ComposeEngine,
    project: str,
    env: dict[str, str],
    chain_id: str,
    timeout_s: float,
) -> dict[str, Any]:
    report_out = "/tmp/localtest-controller-report.json"
    timeout_seconds = str(max(int(timeout_s), 300))
    result = cm.compose_run(
        engine=engine,
        project_name=project,
        compose_files=[COMPOSE_FILE],
        service="zeno-ledger-bootstrap",
        command=[
            "tools/zeno_ledger_multidocker_scenario.py",
            "controller",
            "--machine-count",
            "3",
            "--writer-url",
            "http://zeno-ledger-writer:8787",
            "--forwarder-url",
            "http://zeno-ledger-forwarder:8787",
            "--readonly-url",
            "http://zeno-ledger-readonly:8787",
            "--node-data-dir",
            "/app/data/local-testnet/node-writer",
            "--node-data-dir",
            "/app/data/local-testnet/node-forwarder",
            "--node-data-dir",
            "/app/data/local-testnet/node-readonly",
            "--chain-id",
            chain_id,
            "--network-id",
            chain_id,
            "--timeout-seconds",
            timeout_seconds,
            "--write-auth-token-env",
            "ZENO_LEDGER_WRITER_TOKEN",
            "--report-out",
            report_out,
        ],
        env=env,
        capture=True,
    )
    if result.returncode != 0:
        raise RuntimeError(result.stderr.strip() or result.stdout.strip() or "ledger controller failed")
    try:
        parsed = json.loads(result.stdout)
    except json.JSONDecodeError:
        report = _extract_json_from_text(result.stdout)
    else:
        if not isinstance(parsed, dict):
            raise RuntimeError("ledger controller did not emit a JSON object")
        report = parsed
    if report.get("ok") is not True:
        raise RuntimeError(f"ledger controller rejected: {report}")
    return report


def _seed_api_state(
    *,
    engine: cm.ComposeEngine,
    project: str,
    env: dict[str, str],
    roles: Mapping[str, Mapping[str, Any]],
    chain_id: str,
) -> dict[str, Any]:
    payload = {
        "chain_id": chain_id,
        "market_id": DEFAULT_MARKET_ID,
        "oracle_price_e8": DEFAULT_ORACLE_PRICE_E8,
        "roles": {
            "alice": {
                "public_key": str(roles["alice"]["public_key"]),
                "privkey_int": int(roles["alice"]["privkey_int"]),
            },
            "bob": {
                "public_key": str(roles["bob"]["public_key"]),
                "privkey_int": int(roles["bob"]["privkey_int"]),
            },
        },
    }
    script = textwrap.dedent(
        f"""
        import json
        import time

        from src.core.zusd import E8
        from src.integration.tau_net_client import (
            TauNetTcpClient,
            TauNetTcpConfig,
            sign_perp_op_for_engine,
            tau_rpc_response_is_success,
        )
        from src.integration.zusd_tau_token import derive_zusd_tau_asset_id

        PAYLOAD = json.loads({json.dumps(json.dumps(payload, sort_keys=True))})
        client = TauNetTcpClient(TauNetTcpConfig(host="tau-local", port=65432, timeout_s=10.0))
        quote_asset = derive_zusd_tau_asset_id(chain_id=str(PAYLOAD["chain_id"]))
        deadline = int(time.time()) + 3600
        owner = PAYLOAD["roles"]["alice"]
        counterparty = PAYLOAD["roles"]["bob"]
        def load_state():
            payload = json.loads(client.getappstate(full=True))
            app_state = payload.get("app_state")
            if not isinstance(app_state, dict):
                raise RuntimeError("Tau app_state missing")
            return app_state

        def require_success(response, *, label):
            if not tau_rpc_response_is_success(response):
                raise RuntimeError(f"{{label}} failed: {{response}}")

        def send_and_mine(label, *, privkey, operations):
            send_response = client.send_signed_tx(
                privkey=int(privkey),
                operations=operations,
                expiration_seconds=3600,
            )
            require_success(send_response, label=f"{{label}} send")
            last_block_response = None
            for attempt in range(1, 11):
                block_response = client.createblock()
                if tau_rpc_response_is_success(block_response):
                    return {{"send": send_response, "createblock": block_response, "createblock_attempts": attempt}}
                last_block_response = block_response
                if "Mempool is empty" not in str(block_response):
                    break
                time.sleep(0.5)
            require_success(last_block_response, label=f"{{label}} createblock")
            return {{"send": send_response, "createblock": last_block_response}}

        report = {{
            "ok": True,
            "chain_id": PAYLOAD["chain_id"],
            "quote_asset": quote_asset,
            "market_id": PAYLOAD["market_id"],
            "steps": {{}},
        }}

        report["steps"]["materialize_owner"] = send_and_mine(
            "materialize_owner",
            privkey=owner["privkey_int"],
            operations={{"1": [[owner["public_key"][2:], owner["public_key"][2:], "1"]]}},
        )
        report["steps"]["bootstrap_oracle_and_deposit"] = send_and_mine(
            "bootstrap_oracle_and_deposit",
            privkey=owner["privkey_int"],
            operations={{
                "11": [
                    {{
                        "module": "ZUSDFinance",
                        "version": "0.1",
                        "action": "bootstrap_oracle",
                        "price_e8": int(PAYLOAD["oracle_price_e8"]),
                        "nonce": 1,
                        "deadline": deadline,
                    }},
                    {{
                        "module": "ZUSDFinance",
                        "version": "0.1",
                        "action": "deposit_collateral",
                        "owner_pubkey": owner["public_key"],
                        "amount_e8": {DEFAULT_ZUSD_BOOTSTRAP_COLLATERAL_E8},
                        "nonce": 2,
                        "deadline": deadline,
                    }},
                ]
            }},
        )
        report["steps"]["mint_zusd"] = send_and_mine(
            "mint_zusd",
            privkey=owner["privkey_int"],
            operations={{
                "11": [{{
                    "module": "ZUSDFinance",
                    "version": "0.1",
                    "action": "mint_zusd",
                    "owner_pubkey": owner["public_key"],
                    "amount_e8": {DEFAULT_ZUSD_BOOTSTRAP_MINT_E8},
                    "nonce": 3,
                    "deadline": deadline,
                }}]
            }},
        )

        init_market = {{
            "module": "TauPerp",
            "version": "1.0",
            "market_id": PAYLOAD["market_id"],
            "action": "init_market_2p",
            "quote_asset": quote_asset,
            "account_a_pubkey": owner["public_key"],
            "account_b_pubkey": counterparty["public_key"],
            "deadline": deadline,
            "nonce_a": 1,
            "nonce_b": 1,
        }}
        init_market["sig_a"] = sign_perp_op_for_engine(
            init_market,
            privkey=int(owner["privkey_int"]),
            chain_id=str(PAYLOAD["chain_id"]),
            signer_pubkey=str(owner["public_key"]),
            nonce=1,
        )
        init_market["sig_b"] = sign_perp_op_for_engine(
            init_market,
            privkey=int(counterparty["privkey_int"]),
            chain_id=str(PAYLOAD["chain_id"]),
            signer_pubkey=str(counterparty["public_key"]),
            nonce=1,
        )
        report["steps"]["init_market_2p"] = send_and_mine(
            "init_market_2p",
            privkey=owner["privkey_int"],
            operations={{"8": [init_market]}},
        )
        report["steps"]["perps_deposit_collateral"] = send_and_mine(
            "perps_deposit_collateral",
            privkey=owner["privkey_int"],
            operations={{
                "8": [{{
                    "module": "TauPerp",
                    "version": "1.0",
                    "market_id": PAYLOAD["market_id"],
                    "action": "deposit_collateral",
                    "account_pubkey": owner["public_key"],
                    "amount": 25,
                }}]
            }},
        )
        report["steps"]["perps_advance_epoch"] = send_and_mine(
            "perps_advance_epoch",
            privkey=owner["privkey_int"],
            operations={{
                "8": [{{
                    "module": "TauPerp",
                    "version": "1.0",
                    "market_id": PAYLOAD["market_id"],
                    "action": "advance_epoch",
                    "delta": 1,
                }}]
            }},
        )

        app_state = load_state()
        zusd_state = app_state.get("zusd_monetary")
        dex_state = app_state.get("dex_state")
        if not isinstance(zusd_state, dict):
            raise RuntimeError("zusd_monetary state missing after seed")
        if not isinstance(dex_state, dict):
            raise RuntimeError("dex_state missing after seed")
        perps = dex_state.get("perps")
        markets = perps.get("markets") if isinstance(perps, dict) else None
        if not isinstance(markets, list) or not markets:
            raise RuntimeError("perps markets missing after seed")
        market_row = None
        for row in markets:
            if isinstance(row, dict) and row.get("market_id") == PAYLOAD["market_id"]:
                market_row = row
                break
        if market_row is None:
            raise RuntimeError("seeded perps market not found")

        balances = dex_state.get("balances")
        owner_zusd_balance = 0
        if isinstance(balances, list):
            for row in balances:
                if not isinstance(row, dict):
                    continue
                if str(row.get("pubkey")).strip().lower() != str(owner["public_key"]).strip().lower():
                    continue
                if str(row.get("asset")).strip().lower() != str(quote_asset).strip().lower():
                    continue
                owner_zusd_balance = int(row.get("amount", 0))
                break
        core = zusd_state.get("core")
        report["zusd"] = {{
            "owner_balance_units": owner_zusd_balance,
            "core": core,
        }}
        report["perps"] = {{
            "market_count": len(markets),
            "market": market_row,
        }}
        print(json.dumps(report, sort_keys=True))
        """
    ).strip()
    result = cm.compose_run(
        engine=engine,
        project_name=project,
        compose_files=[COMPOSE_FILE],
        service="zenodex-api",
        command=["-c", script],
        env=env,
        capture=True,
    )
    if result.returncode != 0:
        raise RuntimeError(result.stderr.strip() or result.stdout.strip() or "Tau seed bootstrap failed")
    report = _extract_json_from_text(result.stdout)
    if report.get("ok") is not True:
        raise RuntimeError(f"Tau seed bootstrap failed: {report}")
    return report


def _wait_for_base_services(*, ui_base: str, timeout_s: float) -> None:
    deadline = time.monotonic() + timeout_s
    last_error = "no attempts made"
    while time.monotonic() < deadline:
        probe = _probe_base_services(ui_base=ui_base)
        if probe["ok"]:
            return
        last_error = json.dumps(probe, sort_keys=True)
        time.sleep(1.0)
    raise TimeoutError(f"base services did not become ready: {last_error}")


def _wait_for_lane_readiness(*, ui_base: str, timeout_s: float) -> dict[str, Any]:
    deadline = time.monotonic() + timeout_s
    last_report: dict[str, Any] = {"ok": False, "checks": {}, "lanes": {}}
    while time.monotonic() < deadline:
        last_report = _collect_lane_readiness(ui_base=ui_base)
        if last_report.get("ok") is True:
            return last_report
        time.sleep(1.0)
    raise TimeoutError(
        "lane readiness checks did not pass: "
        + json.dumps(last_report.get("checks") or {}, sort_keys=True)
    )


def _probe_base_services(*, ui_base: str) -> dict[str, Any]:
    ui_health = _safe_get_json(f"{ui_base}/health")
    api_health = _safe_get_json(f"{ui_base}/api/health")
    oracle_health = _safe_get_json(f"{ui_base}/api/oracle/health")
    return {
        "ok": bool(ui_health.get("ok")) and bool(api_health.get("ok")) and bool(oracle_health.get("ok")),
        "ui": ui_health,
        "api": api_health,
        "oracle": oracle_health,
    }


def _collect_lane_readiness(*, ui_base: str) -> dict[str, Any]:
    lanes = {
        "spot": _safe_get_json(f"{ui_base}/api/pools"),
        "zusd_wallet": _safe_get_json(f"{ui_base}/api/zusd/wallet/status"),
        "zusd_monetary": _safe_get_json(f"{ui_base}/api/zusd/monetary/status"),
        "perps_wallet": _safe_get_json(f"{ui_base}/api/perps/wallet/status"),
        "autotrader": _safe_get_json(f"{ui_base}/api/strategy/autotrader/status"),
        "oracle_health": _safe_get_json(f"{ui_base}/api/oracle/health"),
        "oracle_dashboard": _safe_get_json(f"{ui_base}/api/oracle/dashboard"),
        "confidential": _safe_get_json(f"{ui_base}/api/confidential/status"),
    }
    checks = {
        "spot": bool(lanes["spot"].get("ok")) and isinstance(lanes["spot"].get("pools"), list) and len(lanes["spot"]["pools"]) > 0,
        "zusd_wallet": bool(lanes["zusd_wallet"].get("ok"))
        and bool(((lanes["zusd_wallet"].get("status") or {}).get("node_reachable"))),
        "zusd_monetary": bool(lanes["zusd_monetary"].get("ok"))
        and bool(((lanes["zusd_monetary"].get("status") or {}).get("node_reachable")))
        and bool(((lanes["zusd_monetary"].get("status") or {}).get("monetary_state_present"))),
        "perps_wallet": bool(lanes["perps_wallet"].get("ok"))
        and bool(((lanes["perps_wallet"].get("status") or {}).get("node_reachable")))
        and int(((lanes["perps_wallet"].get("status") or {}).get("market_count") or 0)) >= 1
        and bool((((lanes["perps_wallet"].get("status") or {}).get("wallet_authority") or {}).get("ok")))
        and bool((((lanes["perps_wallet"].get("status") or {}).get("oracle_authority") or {}).get("ok"))),
        "autotrader": bool(lanes["autotrader"].get("ok"))
        and bool((((lanes["autotrader"].get("status") or {}).get("supervisor") or {}).get("ok"))),
        "oracle_health": bool(lanes["oracle_health"].get("ok")),
        "oracle_dashboard": bool(lanes["oracle_dashboard"].get("ok")),
        "confidential": bool(lanes["confidential"].get("ok")),
    }
    return {"ok": all(checks.values()), "checks": checks, "lanes": lanes}


def _run_feature_smoke(*, ui_base: str, paths: mf.ManifestPaths, manifest: Mapping[str, Any]) -> dict[str, Any]:
    key_bundle_path = Path(str(manifest["fixture_paths"]["key_bundle"]))
    roles = _role_materials(_load_json_file(key_bundle_path, label="key bundle"))
    seed_report = _load_json_file(paths.reports_dir / "api_seed_report.json", label="api seed report")
    deadline = int(time.time()) + 3600
    run_id = _smoke_run_id()
    chain_id = str(manifest["chain_id"])

    checks: dict[str, Any] = {}

    def capture(name: str, fn: Any) -> None:
        try:
            checks[name] = fn()
        except Exception as exc:
            checks[name] = {"ok": False, "error": f"{type(exc).__name__}: {exc}"}

    capture(
        "spot_swap",
        lambda: _summarize_response(
            _post_json(
                f"{ui_base}/api/swap",
                {
                    "from": "tASSET0",
                    "to": "tASSET1",
                    "amountIn": 1,
                    "minAmountOut": 0,
                    "senderPubkey": _role_pubkey(roles, "alice"),
                    "recipient": _role_pubkey(roles, "alice"),
                    "deadline": deadline,
                },
            ),
            require_any=("tx_accepted", "ok"),
        ),
    )
    capture(
        "zusd_wallet_transfer",
        lambda: _summarize_response(
            _post_json(
                f"{ui_base}/api/zusd/wallet/submit",
                _zusd_transfer_payload(ui_base=ui_base, roles=roles, deadline=deadline),
            ),
        ),
    )
    capture(
        "zusd_monetary_advance_epoch",
        lambda: _summarize_response(
            _post_json(
                f"{ui_base}/api/zusd/monetary/submit",
                {
                    "action": "advance_epoch",
                    "actor_pubkey": _role_pubkey(roles, "alice"),
                    "delta": 1,
                    "deadline": deadline,
                    "tx_fee_limit": "0",
                    "signer_privkey": _role_privkey_int(roles, "alice"),
                },
            ),
        ),
    )
    capture(
        "perps_publish_clearing_price",
        lambda: _run_perps_wallet_cycle_smoke(
            ui_base=ui_base,
            market_id=str(seed_report["market_id"]),
            roles=roles,
            deadline=deadline,
        ),
    )
    capture(
        "oracle_write_flow",
        lambda: _run_oracle_write_smoke(ui_base=ui_base, run_id=run_id),
    )
    capture(
        "autotrader_live_prepare",
        lambda: _summarize_response(
            _post_json(
                f"{ui_base}/api/strategy/autotrader/prepare",
                {
                    "acknowledge_experimental_live_risk": True,
                    "signer_privkey": _role_privkey_int(roles, "alice"),
                    "chain_id": chain_id,
                },
            ),
        ),
    )
    capture(
        "confidential_runtime_execute",
        lambda: _summarize_response(
            _post_json(
                f"{ui_base}/api/confidential/attestation/execute",
                _confidential_runtime_payload(run_id=run_id),
            ),
        ),
    )

    return {
        "ok": all(bool(value.get("ok")) for value in checks.values()),
        "checks": checks,
        "run_id": run_id,
    }


def _run_browser_smoke(
    *,
    ui_base: str,
    paths: mf.ManifestPaths,
    manifest: Mapping[str, Any],
    chrome_bin: Path | None,
    mode: str,
    timeout_s: float,
) -> dict[str, Any]:
    chrome = _resolve_chrome_bin(chrome_bin)
    if chrome is None:
        skipped = {"ok": mode == "auto", "mode": mode, "skipped": True, "reason": "chrome_not_found", "checks": {}}
        if mode == "required":
            skipped["error"] = "chrome_not_found"
        return skipped

    key_bundle_path = Path(str(manifest["fixture_paths"]["key_bundle"]))
    roles = _role_materials(_load_json_file(key_bundle_path, label="key bundle"))
    seed_report = _load_json_file(paths.reports_dir / "api_seed_report.json", label="api seed report")
    checks: dict[str, Any] = {}
    for item in _browser_smoke_cases(ui_base=ui_base, roles=roles, seed_report=seed_report):
        checks[str(item["name"])] = _run_browser_case(
            chrome=chrome,
            url=str(item["url"]),
            snippets=tuple(str(s) for s in item["snippets"]),
            timeout_s=timeout_s,
        )
    return {
        "ok": all(bool(value.get("ok")) for value in checks.values()),
        "mode": mode,
        "skipped": False,
        "chrome": chrome,
        "checks": checks,
    }


def _run_browser_case(*, chrome: str, url: str, snippets: tuple[str, ...], timeout_s: float) -> dict[str, Any]:
    with tempfile.TemporaryDirectory(prefix="zenodex-localtest-chrome-") as profile:
        try:
            result = subprocess.run(
                [
                    chrome,
                    "--headless=new",
                    "--disable-gpu",
                    "--no-sandbox",
                    f"--user-data-dir={profile}",
                    "--virtual-time-budget=25000",
                    "--dump-dom",
                    url,
                ],
                check=False,
                capture_output=True,
                text=True,
                timeout=max(5.0, float(timeout_s)),
            )
        except subprocess.TimeoutExpired:
            return {"ok": False, "error": "browser_timeout"}
    dom = result.stdout or ""
    missing = [snippet for snippet in snippets if snippet not in dom]
    failed_text = " failed " in f" {dom.lower()} " or "rejected" in dom.lower()
    return {
        "ok": result.returncode == 0 and not missing and not failed_text,
        "returncode": result.returncode,
        "missing_snippets": missing,
        "stderr_tail": (result.stderr or "")[-1000:],
    }


def _browser_smoke_cases(
    *,
    ui_base: str,
    roles: Mapping[str, Mapping[str, Any]],
    seed_report: Mapping[str, Any],
) -> list[dict[str, Any]]:
    deadline = int(time.time()) + 3600
    alice = _role_pubkey(roles, "alice")
    bob = _role_pubkey(roles, "bob")
    alice_priv = str(_role_privkey_int(roles, "alice"))
    oracle_priv = str(_role_privkey_int(roles, "oracle_authority"))
    operator_priv = str(_role_privkey_int(roles, "operator"))
    market_id = str(seed_report["market_id"])

    def url(params: Mapping[str, str]) -> str:
        return f"{ui_base}/?{urllib.parse.urlencode(params)}"

    return [
        {
            "name": "spot_swap_ui",
            "url": url(
                {
                    "tab": "swap",
                    "demo": "false",
                    "zenodexUiSmokeSwap": "1",
                    "walletAddress": alice,
                    "smokeAmountIn": "1",
                }
            ),
            "snippets": ("Swap Confirmed",),
        },
        {
            "name": "zusd_wallet_ui",
            "url": url(
                {
                    "tab": "zusd",
                    "demo": "false",
                    "zenodexUiSmokeZusd": "1",
                    "zusdAction": "transfer",
                    "senderPubkey": alice,
                    "recipientPubkey": bob,
                    "signerPrivkey": alice_priv,
                    "zusdAmount": "1",
                    "zusdDeadline": str(deadline),
                }
            ),
            "snippets": ("zUSD Wallet Transport", "\"ok\": true"),
        },
        {
            "name": "zusd_monetary_ui",
            "url": url(
                {
                    "tab": "zusd",
                    "demo": "false",
                    "zenodexUiSmokeZusdMonetary": "1",
                    "zusdMonetaryAction": "advance_epoch",
                    "actorPubkey": alice,
                    "signerPrivkey": alice_priv,
                    "zusdDelta": "1",
                    "zusdDeadline": str(deadline),
                }
            ),
            "snippets": ("zUSD Monetary Vault", "preflight accepted"),
        },
        {
            "name": "zusd_quick_mint_ui",
            "url": url(
                {
                    "tab": "zusd",
                    "demo": "false",
                    "zenodexUiSmokeZusdQuickMint": "1",
                    "ownerPubkey": alice,
                    "signerPrivkey": alice_priv,
                    "zusdCollateral": "0",
                    "zusdMint": "1",
                    "zusdDeadline": str(deadline),
                    "zusdAcceptProtocolResponse": "1",
                }
            ),
            "snippets": ("Quick Mint zUSD", "mint request completed"),
        },
        {
            "name": "perps_wallet_ui",
            "url": url(
                {
                    "tab": "perps",
                    "demo": "false",
                    "zenodexUiSmokePerpsWallet": "1",
                    "perpsWalletAction": "publish_clearing_price",
                    "marketId": market_id,
                    "oraclePrivkey": oracle_priv,
                    "priceE8": str(E8),
                    "perpsDeadline": str(deadline),
                }
            ),
            "snippets": ("Live Perps Wallet", "submit accepted"),
        },
        {
            "name": "oracle_ui",
            "url": url(
                {
                    "tab": "oracle",
                    "oracleView": "Receipts",
                    "demo": "false",
                    "zenodexUiSmokeOracleWrites": "1",
                }
            ),
            "snippets": ("ZenoOracle", "oracle write smoke accepted"),
        },
        {
            "name": "autotrader_ui",
            "url": url(
                {
                    "tab": "strategy",
                    "demo": "false",
                    "zenodexUiSmokeStrategyLive": "1",
                    "signerPrivkey": alice_priv,
                }
            ),
            "snippets": ("AutoTrader Live Prepare", "accepted"),
        },
        {
            "name": "confidential_ui",
            "url": url(
                {
                    "tab": "confidential",
                    "demo": "false",
                    "zenodexUiSmokeConfidentialVerify": "1",
                }
            ),
            "snippets": ("Confidential trading", "Runtime receipt"),
        },
    ]


def _safe_get_json(url: str, *, timeout_s: float = 5.0) -> dict[str, Any]:
    try:
        request = urllib.request.Request(url, method="GET")
        with urllib.request.urlopen(request, timeout=timeout_s) as response:
            body = json.loads(response.read().decode("utf-8"))
        if isinstance(body, dict):
            return {"ok": True, "status_code": response.status, **body}
        return {"ok": False, "status_code": response.status, "error": "non_object_json"}
    except urllib.error.HTTPError as exc:
        payload = _decode_error_json(exc)
        return {"ok": False, "status_code": exc.code, **payload}
    except Exception as exc:
        return {"ok": False, "error": f"{type(exc).__name__}: {exc}"}


def _post_json(url: str, payload: Mapping[str, Any], *, timeout_s: float = 10.0) -> dict[str, Any]:
    data = json.dumps(payload, sort_keys=True).encode("utf-8")
    request = urllib.request.Request(
        url,
        data=data,
        headers={"Content-Type": "application/json"},
        method="POST",
    )
    try:
        with urllib.request.urlopen(request, timeout=timeout_s) as response:
            body = json.loads(response.read().decode("utf-8"))
        if isinstance(body, dict):
            return {"status_code": response.status, **body}
        raise ValueError("non_object_json")
    except urllib.error.HTTPError as exc:
        payload = _decode_error_json(exc)
        return {"status_code": exc.code, **payload}


def _summarize_response(payload: Mapping[str, Any], *, require_any: tuple[str, ...] = ("ok",)) -> dict[str, Any]:
    accepted = any(payload.get(key) is True for key in require_any)
    summary: dict[str, Any] = {
        "ok": bool(accepted),
        "status_code": payload.get("status_code"),
        "status": payload.get("status"),
        "error": payload.get("error"),
    }
    for key in (
        "height",
        "tx_id",
        "receipt_hash",
        "runtime_receipt_hash",
        "action",
        "surface",
    ):
        if key in payload:
            summary[key] = payload.get(key)
    submission = payload.get("submission")
    if isinstance(submission, Mapping):
        summary["submission_ok"] = "SUCCESS:" in str(submission.get("sendtx_response", ""))
        if "createblock_response" in submission:
            summary["mined"] = "SUCCESS:" in str(submission.get("createblock_response", ""))
    report = payload.get("report")
    if isinstance(report, Mapping):
        summary["action"] = report.get("action", summary.get("action"))
        preflight = report.get("preflight")
        if isinstance(preflight, Mapping):
            summary["preflight_ok"] = bool(preflight.get("ok"))
            summary["preflight_error"] = preflight.get("error")
    receipt = payload.get("receipt")
    if isinstance(receipt, Mapping):
        summary["receipt_accepted"] = bool(receipt.get("accepted"))
    return summary


def _role_pubkey(roles: Mapping[str, Mapping[str, Any]], role: str) -> str:
    value = roles.get(role, {}).get("public_key")
    if not isinstance(value, str) or not value:
        raise ValueError(f"missing public key for role {role!r}")
    return value


def _role_privkey_int(roles: Mapping[str, Mapping[str, Any]], role: str) -> int:
    value = roles.get(role, {}).get("privkey_int")
    if not isinstance(value, int):
        raise ValueError(f"missing private key for role {role!r}")
    return int(value)


def _smoke_run_id() -> str:
    import hashlib

    raw = f"{time.time_ns()}:{os.getpid()}".encode("utf-8")
    return hashlib.sha256(raw).hexdigest()[:16]


def _resolve_chrome_bin(chrome_bin: Path | None) -> str | None:
    if chrome_bin is not None:
        return str(chrome_bin)
    for name in ("google-chrome", "google-chrome-stable", "chromium", "chromium-browser"):
        found = shutil.which(name)
        if found:
            return found
    return None


def _zusd_transfer_payload(
    *,
    ui_base: str,
    roles: Mapping[str, Mapping[str, Any]],
    deadline: int,
) -> dict[str, Any]:
    alice = _role_pubkey(roles, "alice")
    bob = _role_pubkey(roles, "bob")
    alice_inspect = _post_json(
        f"{ui_base}/api/zusd/wallet/inspect",
        {"action": "transfer", "sender_pubkey": alice, "recipient_pubkey": bob, "amount": 1, "deadline": deadline},
    )
    bob_inspect = _post_json(
        f"{ui_base}/api/zusd/wallet/inspect",
        {"action": "transfer", "sender_pubkey": bob, "recipient_pubkey": alice, "amount": 1, "deadline": deadline},
    )
    alice_balance = int(((alice_inspect.get("transport") or {}).get("sender_balance_before") or 0))
    bob_balance = int(((bob_inspect.get("transport") or {}).get("sender_balance_before") or 0))
    if bob_balance > alice_balance:
        sender_role, recipient = "bob", alice
    else:
        sender_role, recipient = "alice", bob
    return {
        "action": "transfer",
        "sender_pubkey": _role_pubkey(roles, sender_role),
        "recipient_pubkey": recipient,
        "amount": 1,
        "deadline": deadline,
        "signer_privkey": _role_privkey_int(roles, sender_role),
    }


def _confidential_runtime_payload(*, run_id: str) -> dict[str, Any]:
    return {
        "attestation_payload": {
            "provider": "nitro",
            "nonce": f"local-smoke-{run_id}",
            "summary": {"pcrs": {"0": SMOKE_NITRO_PCR0, "8": SMOKE_NITRO_PCR8}},
        },
        "extension_id": "route-premium-v1",
        "provider_id": "provider-1",
        "request_id": f"req-local-smoke-{run_id}",
        "policy_version": "tee-policy-v1",
        "do_execute": 1,
        "policy_ok": 1,
        "nonce_unused": 1,
        "output_bound_ok": 1,
        "current_epoch": 10,
        "max_attestation_age": 2,
        "fee_charged": 7,
        "receipt_fee": 7,
        "credit_before": 40,
        "credit_after": 33,
        "provider_balance_before": 9,
        "provider_balance_after": 16,
        "expected_policy_digest": SMOKE_CONFIDENTIAL_POLICY_DIGEST,
        "execution_id": f"exec-local-smoke-{run_id}",
        "execution_kind": "private_route_quote",
        "result_code": "bounded_route_selected",
    }


def _run_perps_wallet_cycle_smoke(
    *,
    ui_base: str,
    market_id: str,
    roles: Mapping[str, Mapping[str, Any]],
    deadline: int,
) -> dict[str, Any]:
    """Exercise a clearinghouse perps price cycle and leave it reusable.

    The local-testnet clearinghouse requires a published price before settle,
    and a settled epoch before the next advance. This smoke publishes a price,
    settles it, then advances once so the browser/UI smoke can publish again.
    """
    steps: dict[str, dict[str, Any]] = {}

    def submit(name: str, payload: Mapping[str, Any]) -> dict[str, Any]:
        response = _post_json(f"{ui_base}/api/perps/wallet/submit", payload, timeout_s=20.0)
        summary = _summarize_response(response)
        steps[name] = summary
        _require_ok(response, label=f"perps {name}")
        if summary.get("preflight_ok") is not True:
            raise RuntimeError(f"perps {name} preflight failed: {summary.get('preflight_error')}")
        if summary.get("submission_ok") is not True:
            raise RuntimeError(f"perps {name} submission was not accepted")
        return response

    operator_privkey = _role_privkey_int(roles, "operator")
    oracle_privkey = _role_privkey_int(roles, "oracle_authority")
    common = {"market_id": market_id, "deadline": deadline, "tx_fee_limit": "0"}

    status_before = _safe_get_json(f"{ui_base}/api/perps/wallet/status")
    market_before = _find_perps_market(status_before, market_id=market_id)
    prep = _perps_pre_publish_step(market_before)
    if prep == "settle_then_advance":
        submit(
            "settle_epoch_before_publish",
            {
                **common,
                "action": "settle_epoch",
                "operator_privkey": operator_privkey,
            },
        )
        submit(
            "advance_epoch_before_publish",
            {
                **common,
                "action": "advance_epoch",
                "delta": 1,
                "operator_privkey": operator_privkey,
            },
        )
    elif prep == "advance":
        submit(
            "advance_epoch_before_publish",
            {
                **common,
                "action": "advance_epoch",
                "delta": 1,
                "operator_privkey": operator_privkey,
            },
        )

    publish = submit(
        "publish_clearing_price",
        {
            **common,
            "action": "publish_clearing_price",
            "price_e8": E8,
            "oracle_privkey": oracle_privkey,
        },
    )
    submit(
        "settle_epoch",
        {
            **common,
            "action": "settle_epoch",
            "operator_privkey": operator_privkey,
        },
    )
    submit(
        "advance_epoch_after_settle",
        {
            **common,
            "action": "advance_epoch",
            "delta": 1,
            "operator_privkey": operator_privkey,
        },
    )
    return {
        "ok": all(bool(item.get("ok")) for item in steps.values()),
        "status_code": publish.get("status_code"),
        "action": "publish_clearing_price",
        "steps": steps,
    }


def _find_perps_market(status_payload: Mapping[str, Any], *, market_id: str) -> Mapping[str, Any] | None:
    status = status_payload.get("status")
    markets = status.get("markets") if isinstance(status, Mapping) else None
    if not isinstance(markets, list):
        return None
    for item in markets:
        if isinstance(item, Mapping) and str(item.get("market_id")) == market_id:
            return item
    return None


def _perps_pre_publish_step(market: Mapping[str, Any] | None) -> str:
    if market is None:
        return "none"
    now_epoch = int(market.get("now_epoch") or 0)
    clearing_epoch = int(market.get("clearing_price_epoch") or 0)
    oracle_last_update = int(market.get("oracle_last_update_epoch") or 0)
    if now_epoch == 0 or oracle_last_update >= now_epoch:
        return "advance"
    if clearing_epoch >= now_epoch:
        return "settle_then_advance"
    return "none"


def _run_oracle_write_smoke(*, ui_base: str, run_id: str) -> dict[str, Any]:
    import hashlib

    def digest(label: str) -> str:
        return "sha256:" + hashlib.sha256(f"{label}:{run_id}".encode("utf-8")).hexdigest()

    query_id = digest("query")
    action_id = digest("action")
    action_facts_hash = digest("action_facts")
    pre_state_hash = digest("pre_state")
    source_id = f"source:local-smoke-{run_id}"
    steps: dict[str, Any] = {}

    def call(name: str, path: str, payload: Mapping[str, Any]) -> dict[str, Any]:
        response = _post_json(f"{ui_base}{path}", payload)
        steps[name] = _summarize_response(response)
        _require_ok(response, label=f"oracle {name}")
        return response

    call("identity", "/api/oracle/identity/create", {"force": True})
    call(
        "query_register",
        "/api/oracle/query/register",
        {
            "base_asset": "AGRS",
            "quote_asset": "ZDEX",
            "query_id": query_id,
            "source_policy_id": "source-policy:registered-diverse-v1",
            "min_reporters": 1,
            "report_reward_e8": 17,
            "force": True,
        },
    )
    call("query_fund", "/api/oracle/query/fund", {"query_id": query_id, "amount_e8": 20})
    call("reporter_register", "/api/oracle/reporter/register", {"query_id": query_id, "required_bond_e8": 1, "force": True})
    call("reporter_bond", "/api/oracle/reporter/bond", {"amount_e8": 1})
    call(
        "source_register",
        "/api/oracle/source/register",
        {
            "source_id": source_id,
            "source_kind": "cex",
            "control_group_id": f"control:local-smoke-{run_id}",
            "venue_id": f"venue:local-smoke-{run_id}",
            "data_family_id": "price:cex-last-trade",
            "transport_id": "api:https:local-smoke",
            "asset_class": "crypto",
            "query_id": query_id,
            "assurance_class": "S3",
            "force": True,
        },
    )
    submitted = call(
        "report_submit",
        "/api/oracle/report/submit",
        {
            "query_id": query_id,
            "price_e8": 123456789,
            "source_observed_epoch": 12,
            "source_id": source_id,
        },
    )
    aggregate = call("aggregate_build", "/api/oracle/aggregate/build", {"query_id": query_id, "epoch": 12})
    read = call(
        "read_accept",
        "/api/oracle/read/accept",
        {
            "aggregate_id": aggregate.get("aggregate_id"),
            "consumer_module": "zenodex.zusd",
            "profile_id": "critical-zusd-v1",
        },
    )
    authorization = call(
        "authorization_build",
        "/api/oracle/authorization/build",
        {
            "read_id": read.get("read_id"),
            "action_kind": "mint",
            "action_id": action_id,
            "action_facts_hash": action_facts_hash,
            "pre_state_hash": pre_state_hash,
            "now_epoch": 12,
        },
    )
    reward = call("reward_pay", "/api/oracle/rewards/pay", {"amount_e8": 5})
    return {
        "ok": True,
        "query_id": query_id,
        "report_id": submitted.get("report_id"),
        "aggregate_id": aggregate.get("aggregate_id"),
        "read_id": read.get("read_id"),
        "authorization_id": authorization.get("authorization_id"),
        "reward_receipt_id": reward.get("receipt_id") or reward.get("reward_receipt_id"),
        "steps": steps,
    }


def _decode_error_json(exc: urllib.error.HTTPError) -> dict[str, Any]:
    raw = exc.read().decode("utf-8", errors="replace")
    try:
        parsed = json.loads(raw)
    except json.JSONDecodeError:
        return {"error": raw or exc.reason}
    if isinstance(parsed, dict):
        return parsed
    return {"error": raw or exc.reason}


def _require_ok(payload: Mapping[str, Any], *, label: str) -> None:
    if payload.get("ok") is True:
        return
    raise RuntimeError(f"{label} failed: {json.dumps(payload, sort_keys=True)}")


def _extract_json_from_text(text: str) -> dict[str, Any]:
    lines = [line.strip() for line in text.splitlines() if line.strip()]
    for line in reversed(lines):
        try:
            obj = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(obj, dict):
            return obj
    raise RuntimeError("expected JSON object in command output")


def _write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _tail_service_logs(*, engine: cm.ComposeEngine, project: str, env: dict[str, str]) -> None:
    for svc in ("tau-local", "zeno-ledger-writer", "zenodex-api", "zenodex-oracle", "zenodex-nginx"):
        tail = cm.compose_logs(
            engine=engine,
            project_name=project,
            compose_files=[COMPOSE_FILE],
            service=svc,
            tail=40,
            env=env,
        )
        sys.stderr.write(f"--- {svc} (last 40 lines) ---\n{tail}\n")


def _summary_text(manifest: dict[str, Any]) -> str:
    lines = [
        "",
        "ZenoDEX local-testnet is up.",
        "",
        f"  UI:                {manifest['service_urls']['ui']}",
        f"  Compose project:   {manifest['compose_project']}",
        f"  Chain ID:          {manifest['chain_id']}",
        f"  Manifest:          {manifest['out_dir']}/local_testnet_manifest.json",
        f"  Fixtures:          {manifest['fixture_paths']['key_bundle']}",
        f"  Oracle home:       {manifest['host_paths']['oracle_home_dir']}",
        f"  Reports:           {manifest['host_paths']['reports_dir']}",
        "",
        "  Stop the stack (preserves state):",
        f"    python3 tools/zenoctl.py testnet local down --out-dir {manifest['out_dir']}",
        "",
    ]
    return "\n".join(lines)


def _emit_status(report: dict[str, Any], *, as_json: bool) -> None:
    if as_json:
        print(json.dumps(report, indent=2, sort_keys=True))
        return
    sys.stdout.write(f"ok={report['ok']} ui={report.get('ui_url')}\n")
    base_health = report.get("base_health") or {}
    sys.stdout.write(f"base_health_ok={base_health.get('ok')}\n")
    for name, ok in sorted(((report.get("lanes") or {}).get("checks") or {}).items()):
        sys.stdout.write(f"lane.{name}={ok}\n")
    for svc in report.get("services", []):
        sys.stdout.write(f"  - {svc['name']}: state={svc['state']} health={svc['health']}\n")


def _log(phase: str, msg: str) -> None:
    sys.stderr.write(f"[testnet-local phase={phase}] {msg}\n")
