"""Manifest schema for the local-testnet stack.

Records the running local-testnet stack: compose project, allocated host
ports, in-network service URLs, image SHAs, enabled API lanes, fixture file
paths, the ledger bundle manifest, and the SHA-256 of the writer bearer
token (not the token itself, so the manifest is safe to inspect or share).
"""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping


SCHEMA_V1 = "zeno_ledger.local_testnet_manifest.v1"
SCHEMA_V0 = "zeno_ledger.local_testnet_manifest.v0"
SUPPORTED_SCHEMAS = frozenset({SCHEMA_V0, SCHEMA_V1})
MANIFEST_FILENAME = "local_testnet_manifest.json"

_SHA256_HEX_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
_COMPOSE_PROJECT_RE = re.compile(r"^zenodex-local-testnet-[0-9a-f]{8}$")


@dataclass(frozen=True)
class ManifestPaths:
    out_dir: Path
    fixtures_dir: Path
    reports_dir: Path
    oracle_home_dir: Path
    rendered_nginx: Path
    rendered_compose_overlay: Path
    rendered_runtime_config: Path
    manifest_path: Path

    @classmethod
    def from_out_dir(cls, out_dir: Path) -> "ManifestPaths":
        out = Path(out_dir).resolve()
        return cls(
            out_dir=out,
            fixtures_dir=out / "fixtures",
            reports_dir=out / "reports",
            oracle_home_dir=out / "oracle-home",
            rendered_nginx=out / "rendered" / "nginx.local-testnet.conf",
            rendered_compose_overlay=out / "rendered" / "docker-compose.local-testnet.yml",
            rendered_runtime_config=out / "rendered" / "zenodex-config.json",
            manifest_path=out / MANIFEST_FILENAME,
        )


def writer_token_sha256(token: str) -> str:
    """Returns `sha256:<hex>` for a writer bearer token. Used to record the
    token in the manifest without recording its value."""
    if not isinstance(token, str) or not token:
        raise ValueError("token must be a non-empty string")
    digest = hashlib.sha256(token.encode("utf-8")).hexdigest()
    return f"sha256:{digest}"


def compose_project_name(out_dir: Path | str) -> str:
    """Derive a stable, collision-resistant compose project name from the
    output directory's absolute path. Allows multiple parallel stacks on
    one machine without name conflict."""
    abs_path = str(Path(out_dir).resolve()).encode("utf-8")
    hash8 = hashlib.blake2b(abs_path, digest_size=4).hexdigest()
    return f"zenodex-local-testnet-{hash8}"


def build_manifest(
    *,
    out_dir: Path,
    chain_id: str,
    network_id: str,
    ports: Mapping[str, int],
    service_urls: Mapping[str, str],
    image_refs: Mapping[str, str],
    enabled_lanes: list[str],
    fixture_paths: Mapping[str, str],
    ledger_bundle_manifest: str,
    writer_token: str,
    created_at_ms: int,
) -> dict[str, Any]:
    """Construct a manifest dict from already-validated inputs. Caller is
    responsible for ensuring inputs are sane; `validate_manifest` should
    be called on the result before persisting."""
    return {
        "schema": SCHEMA_V1,
        "compose_project": compose_project_name(out_dir),
        "out_dir": str(Path(out_dir).resolve()),
        "chain_id": chain_id,
        "network_id": network_id,
        "ports": dict(ports),
        "service_urls": dict(service_urls),
        "image_refs": dict(image_refs),
        "enabled_lanes": list(enabled_lanes),
        "fixture_paths": dict(fixture_paths),
        "ledger_bundle_manifest": ledger_bundle_manifest,
        "writer_token_sha256": writer_token_sha256(writer_token),
        "rendered_paths": {
            "nginx_conf": str(ManifestPaths.from_out_dir(out_dir).rendered_nginx),
            "runtime_config": str(ManifestPaths.from_out_dir(out_dir).rendered_runtime_config),
        },
        "host_paths": {
            "fixtures_dir": str(ManifestPaths.from_out_dir(out_dir).fixtures_dir),
            "oracle_home_dir": str(ManifestPaths.from_out_dir(out_dir).oracle_home_dir),
            "reports_dir": str(ManifestPaths.from_out_dir(out_dir).reports_dir),
        },
        "created_at_ms": int(created_at_ms),
    }


def save_manifest(manifest: Mapping[str, Any], path: Path) -> None:
    errors = validate_manifest(manifest)
    if errors:
        raise ValueError(f"refusing to save invalid manifest: {errors}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def load_manifest(path: Path) -> dict[str, Any]:
    manifest = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(manifest, dict):
        raise ValueError(f"{path}: manifest must be a JSON object")
    errors = validate_manifest(manifest)
    if errors:
        raise ValueError(f"{path}: manifest validation failed: {errors}")
    return manifest


REQUIRED_KEYS = (
    "schema",
    "compose_project",
    "out_dir",
    "chain_id",
    "network_id",
    "ports",
    "service_urls",
    "image_refs",
    "enabled_lanes",
    "fixture_paths",
    "ledger_bundle_manifest",
    "writer_token_sha256",
    "created_at_ms",
)
V1_REQUIRED_KEYS = ("rendered_paths", "host_paths")

REQUIRED_PORT_KEYS = ("ui",)
REQUIRED_SERVICE_KEYS = (
    "ui",
    "stdlib_api",
    "writer",
    "oracle",
    "tau",
)
REQUIRED_IMAGE_KEYS = ("operator_tools", "tau_local")
REQUIRED_FIXTURE_KEYS = (
    "key_bundle",
    "oracle_authority_profile",
    "perps_wallet_authority_profile",
    "autotrader_supervisor_profile",
    "guardian_quorum",
)
V1_REQUIRED_RENDERED_KEYS = ("nginx_conf", "runtime_config")
V1_REQUIRED_HOST_KEYS = ("fixtures_dir", "oracle_home_dir", "reports_dir")


def validate_manifest(manifest: Mapping[str, Any]) -> list[str]:
    """Return a list of validation errors. Empty list means valid."""
    errors: list[str] = []

    if not isinstance(manifest, Mapping):
        return ["manifest must be a mapping"]

    for key in REQUIRED_KEYS:
        if key not in manifest:
            errors.append(f"missing required key: {key}")

    schema = manifest.get("schema")
    if schema not in SUPPORTED_SCHEMAS:
        errors.append(
            f"schema must be one of {sorted(SUPPORTED_SCHEMAS)!r}, got {schema!r}"
        )
    is_v1 = schema == SCHEMA_V1

    project = manifest.get("compose_project", "")
    if not isinstance(project, str) or not _COMPOSE_PROJECT_RE.match(project):
        errors.append(
            f"compose_project must match {_COMPOSE_PROJECT_RE.pattern!r}, got {project!r}"
        )

    out_dir = manifest.get("out_dir")
    if not isinstance(out_dir, str) or not out_dir.startswith("/"):
        errors.append(f"out_dir must be an absolute path string, got {out_dir!r}")

    chain_id = manifest.get("chain_id")
    if not isinstance(chain_id, str) or not chain_id:
        errors.append(f"chain_id must be a non-empty string, got {chain_id!r}")

    network_id = manifest.get("network_id")
    if not isinstance(network_id, str) or not network_id:
        errors.append(f"network_id must be a non-empty string, got {network_id!r}")

    ports = manifest.get("ports")
    if not isinstance(ports, Mapping):
        errors.append("ports must be a mapping")
    else:
        for key in REQUIRED_PORT_KEYS:
            if key not in ports:
                errors.append(f"ports missing required key: {key}")
        for key, value in ports.items():
            if not isinstance(value, int) or not (1 <= value <= 65535):
                errors.append(f"ports[{key}] must be a TCP port in [1, 65535], got {value!r}")

    service_urls = manifest.get("service_urls")
    if not isinstance(service_urls, Mapping):
        errors.append("service_urls must be a mapping")
    else:
        for key in REQUIRED_SERVICE_KEYS:
            if key not in service_urls:
                errors.append(f"service_urls missing required key: {key}")
        for key, value in service_urls.items():
            if not isinstance(value, str) or not value:
                errors.append(f"service_urls[{key}] must be non-empty string, got {value!r}")

    image_refs = manifest.get("image_refs")
    if not isinstance(image_refs, Mapping):
        errors.append("image_refs must be a mapping")
    else:
        for key in REQUIRED_IMAGE_KEYS:
            if key not in image_refs:
                errors.append(f"image_refs missing required key: {key}")
        for key, value in image_refs.items():
            if not isinstance(value, str) or not value:
                errors.append(f"image_refs[{key}] must be non-empty string, got {value!r}")

    lanes = manifest.get("enabled_lanes")
    if not isinstance(lanes, list):
        errors.append("enabled_lanes must be a list")
    else:
        for lane in lanes:
            if not isinstance(lane, str) or not lane:
                errors.append(f"enabled_lanes entries must be non-empty strings, got {lane!r}")

    fixture_paths = manifest.get("fixture_paths")
    if not isinstance(fixture_paths, Mapping):
        errors.append("fixture_paths must be a mapping")
    else:
        for key in REQUIRED_FIXTURE_KEYS:
            if key not in fixture_paths:
                errors.append(f"fixture_paths missing required key: {key}")
        for key, value in fixture_paths.items():
            if not isinstance(value, str) or not value:
                errors.append(f"fixture_paths[{key}] must be non-empty string, got {value!r}")

    bundle = manifest.get("ledger_bundle_manifest")
    if not isinstance(bundle, str) or not bundle:
        errors.append(f"ledger_bundle_manifest must be non-empty string, got {bundle!r}")

    token_hash = manifest.get("writer_token_sha256")
    if not isinstance(token_hash, str) or not _SHA256_HEX_RE.match(token_hash):
        errors.append(
            f"writer_token_sha256 must match {_SHA256_HEX_RE.pattern!r}, got {token_hash!r}"
        )

    created_at = manifest.get("created_at_ms")
    if not isinstance(created_at, int) or created_at < 0:
        errors.append(f"created_at_ms must be a non-negative int, got {created_at!r}")

    if is_v1:
        for key in V1_REQUIRED_KEYS:
            if key not in manifest:
                errors.append(f"missing required key: {key}")
        rendered_paths = manifest.get("rendered_paths")
        if not isinstance(rendered_paths, Mapping):
            errors.append("rendered_paths must be a mapping")
        else:
            for key in V1_REQUIRED_RENDERED_KEYS:
                value = rendered_paths.get(key)
                if not isinstance(value, str) or not value.startswith("/"):
                    errors.append(f"rendered_paths[{key}] must be an absolute path string, got {value!r}")
        host_paths = manifest.get("host_paths")
        if not isinstance(host_paths, Mapping):
            errors.append("host_paths must be a mapping")
        else:
            for key in V1_REQUIRED_HOST_KEYS:
                value = host_paths.get(key)
                if not isinstance(value, str) or not value.startswith("/"):
                    errors.append(f"host_paths[{key}] must be an absolute path string, got {value!r}")

    return errors


def manifest_contains_literal(manifest: Mapping[str, Any], needle: str) -> bool:
    """Defensive grep over the serialized manifest. Used by callers to
    assert that secrets (like the raw writer token) never end up in the
    manifest. Returns True if the literal appears anywhere in the JSON
    serialization."""
    if not isinstance(needle, str) or not needle:
        raise ValueError("needle must be a non-empty string")
    serialized = json.dumps(manifest, sort_keys=True)
    return needle in serialized
