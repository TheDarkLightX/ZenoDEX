"""Manifest schema for the local-testnet stack.

Records the running local-testnet stack: compose project, allocated host
ports, in-network service URLs, image SHAs, enabled API lanes, fixture file
paths, the ledger bundle manifest, and the SHA-256 of the writer bearer
and stdlib bearer tokens (not the tokens themselves, so the manifest is safe
to inspect or share).
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import stat
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

from src.integration.local_route_quarantine import (
    CURRENT_LOCAL_OPERATOR_PROFILE_DIGEST_V1,
    CURRENT_LOCAL_OPERATOR_PROFILE_ID_V1,
)

SCHEMA_V4 = "zeno_ledger.local_testnet_manifest.v4"
SCHEMA_V3 = "zeno_ledger.local_testnet_manifest.v3"
SCHEMA_V2 = "zeno_ledger.local_testnet_manifest.v2"
SCHEMA_V1 = "zeno_ledger.local_testnet_manifest.v1"
SCHEMA_V0 = "zeno_ledger.local_testnet_manifest.v0"
SUPPORTED_SCHEMAS = frozenset({SCHEMA_V0, SCHEMA_V1, SCHEMA_V2, SCHEMA_V3, SCHEMA_V4})
MANIFEST_FILENAME = "local_testnet_manifest.json"

_SHA256_HEX_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
_ARTIFACT_HASH_RE = re.compile(r"^(?:0x|sha256:)[0-9a-f]{64}$")
_COMPOSE_PROJECT_RE = re.compile(r"^zenodex-local-testnet-v2-[0-9a-f]{32}$")
ZK_MODES = frozenset({"auto-strict", "strict", "open"})
ZK_EFFECTIVE_MODES = frozenset({"strict", "open"})
PROOF_VERIFIER_KINDS = frozenset({"disabled", "subprocess", "misconfigured"})
LOCAL_TESTNET_MOUNTABLE_LANES = (
    "DEX_API_ENABLED",
    "CONFIDENTIAL_ATTESTATION_API_ENABLED",
)
_LOCAL_TESTNET_MOUNTABLE_LANE_SET = frozenset(LOCAL_TESTNET_MOUNTABLE_LANES)


def canonical_nonsymlink_out_dir(out_dir: Path | str) -> Path:
    """Return one normalized absolute path after rejecting symlink components."""

    lexical = Path(os.path.abspath(os.fspath(out_dir)))
    current = Path(lexical.anchor)
    for part in lexical.parts[1:]:
        current /= part
        try:
            entry = os.lstat(current)
        except FileNotFoundError:
            continue
        if stat.S_ISLNK(entry.st_mode):
            raise ValueError(f"local-testnet out-dir contains symlink component: {current}")
    return lexical


@dataclass(frozen=True)
class ManifestPaths:
    out_dir: Path
    fixtures_dir: Path
    secrets_dir: Path
    reports_dir: Path
    oracle_home_dir: Path
    rendered_nginx: Path
    rendered_compose_overlay: Path
    rendered_runtime_config: Path
    manifest_path: Path

    @classmethod
    def from_out_dir(cls, out_dir: Path) -> "ManifestPaths":
        out = canonical_nonsymlink_out_dir(out_dir)
        return cls(
            out_dir=out,
            fixtures_dir=out / "fixtures",
            secrets_dir=out / "secrets",
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


def legacy_compose_project_name(out_dir: Path | str) -> str:
    """Return the retired 32-bit project identity for legacy recovery only."""
    abs_path = str(canonical_nonsymlink_out_dir(out_dir)).encode("utf-8")
    hash8 = hashlib.blake2b(abs_path, digest_size=4).hexdigest()
    return f"zenodex-local-testnet-{hash8}"


def compose_project_name(out_dir: Path | str) -> str:
    """Derive the versioned 128-bit project identity for a selected out-dir."""
    abs_path = str(canonical_nonsymlink_out_dir(out_dir)).encode("utf-8")
    hash128 = hashlib.blake2b(abs_path, digest_size=16).hexdigest()
    return f"zenodex-local-testnet-v2-{hash128}"


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
    stdlib_token: str,
    created_at_ms: int,
    zk_posture: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    """Construct a manifest dict from already-validated inputs. Caller is
    responsible for ensuring inputs are sane; `validate_manifest` should
    be called on the result before persisting."""
    posture = _default_zk_posture() if zk_posture is None else dict(zk_posture)
    return {
        "schema": SCHEMA_V4,
        "compose_project": compose_project_name(out_dir),
        "out_dir": str(canonical_nonsymlink_out_dir(out_dir)),
        "chain_id": chain_id,
        "network_id": network_id,
        "ports": dict(ports),
        "service_urls": dict(service_urls),
        "image_refs": dict(image_refs),
        "enabled_lanes": list(enabled_lanes),
        "local_operator_profile_id": CURRENT_LOCAL_OPERATOR_PROFILE_ID_V1,
        "local_operator_profile_digest": CURRENT_LOCAL_OPERATOR_PROFILE_DIGEST_V1,
        "fixture_paths": dict(fixture_paths),
        "ledger_bundle_manifest": ledger_bundle_manifest,
        "writer_token_sha256": writer_token_sha256(writer_token),
        "stdlib_token_sha256": writer_token_sha256(stdlib_token),
        "rendered_paths": {
            "nginx_conf": str(ManifestPaths.from_out_dir(out_dir).rendered_nginx),
            "runtime_config": str(ManifestPaths.from_out_dir(out_dir).rendered_runtime_config),
        },
        "host_paths": {
            "fixtures_dir": str(ManifestPaths.from_out_dir(out_dir).fixtures_dir),
            "secrets_dir": str(ManifestPaths.from_out_dir(out_dir).secrets_dir),
            "oracle_home_dir": str(ManifestPaths.from_out_dir(out_dir).oracle_home_dir),
            "reports_dir": str(ManifestPaths.from_out_dir(out_dir).reports_dir),
        },
        "zk_mode_requested": posture.get("zk_mode_requested"),
        "zk_mode_effective": posture.get("zk_mode_effective"),
        "zk_required": posture.get("zk_required"),
        "zk_fallback_reason": posture.get("zk_fallback_reason"),
        "proof_verifier_kind": posture.get("proof_verifier_kind"),
        "proof_artifact_hashes": dict(posture.get("proof_artifact_hashes") or {}),
        "production_security_claim": posture.get("production_security_claim"),
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
V2_REQUIRED_KEYS = (
    "stdlib_token_sha256",
    "zk_mode_requested",
    "zk_mode_effective",
    "zk_required",
    "zk_fallback_reason",
    "proof_verifier_kind",
    "proof_artifact_hashes",
    "production_security_claim",
)
V3_REQUIRED_KEYS = (
    "local_operator_profile_id",
    "local_operator_profile_digest",
)

REQUIRED_PORT_KEYS = ("ui",)
REQUIRED_SERVICE_KEYS = (
    "ui",
    "stdlib_api",
    "writer",
    "oracle",
)
LEGACY_RETIRED_TAU_SERVICE_KEYS = ("tau",)
REQUIRED_IMAGE_KEYS = ("operator_tools",)
LEGACY_RETIRED_TAU_IMAGE_KEYS = ("tau_local",)
REQUIRED_FIXTURE_KEYS = (
    "key_bundle",
    "oracle_authority_profile",
    "perps_wallet_authority_profile",
    "autotrader_supervisor_profile",
    "guardian_quorum",
)
V2_REQUIRED_FIXTURE_KEYS = (
    "perps_wallet_recovery_exercise",
    "perps_wallet_rotation_exercise",
    "perps_wallet_device_approval_exercise",
    "perps_wallet_signer_device_integration",
    "perps_wallet_signer_prompt_capture",
    "perps_wallet_signer_execution_exercise",
    "perps_wallet_encrypted_sss_backup",
    "perps_wallet_encrypted_sss_recipient_keys",
)
V1_REQUIRED_RENDERED_KEYS = ("nginx_conf", "runtime_config")
V1_REQUIRED_HOST_KEYS = ("fixtures_dir", "oracle_home_dir", "reports_dir")
V2_REQUIRED_HOST_KEYS = ("secrets_dir",)


def validate_manifest(manifest: object) -> list[str]:
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
    is_v1_or_later = schema in {SCHEMA_V1, SCHEMA_V2, SCHEMA_V3, SCHEMA_V4}
    is_v2_or_later = schema in {SCHEMA_V2, SCHEMA_V3, SCHEMA_V4}
    is_profile_bound = schema in {SCHEMA_V3, SCHEMA_V4}
    is_v4 = schema == SCHEMA_V4

    project = manifest.get("compose_project", "")
    if not isinstance(project, str) or not _COMPOSE_PROJECT_RE.match(project):
        errors.append(
            f"compose_project must match {_COMPOSE_PROJECT_RE.pattern!r}, got {project!r}"
        )

    out_dir = manifest.get("out_dir")
    if not isinstance(out_dir, str) or not out_dir.startswith("/"):
        errors.append(f"out_dir must be an absolute path string, got {out_dir!r}")
    elif project != compose_project_name(out_dir):
        errors.append(
            "compose_project does not match the project derived from out_dir: "
            f"expected {compose_project_name(out_dir)!r}, got {project!r}"
        )

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
            if type(value) is not int or not (1 <= value <= 65535):
                errors.append(f"ports[{key}] must be a TCP port in [1, 65535], got {value!r}")

    service_urls = manifest.get("service_urls")
    if not isinstance(service_urls, Mapping):
        errors.append("service_urls must be a mapping")
    else:
        required_service_keys = REQUIRED_SERVICE_KEYS + (
            () if is_v4 else LEGACY_RETIRED_TAU_SERVICE_KEYS
        )
        for key in required_service_keys:
            if key not in service_urls:
                errors.append(f"service_urls missing required key: {key}")
        if is_v4 and any(key in service_urls for key in LEGACY_RETIRED_TAU_SERVICE_KEYS):
            errors.append("v4 service_urls must exclude the retired Tau service")
        for key, value in service_urls.items():
            if not isinstance(value, str) or not value:
                errors.append(f"service_urls[{key}] must be non-empty string, got {value!r}")
        ui_port = ports.get("ui") if isinstance(ports, Mapping) else None
        ui_url = service_urls.get("ui")
        if type(ui_port) is int and 1 <= ui_port <= 65535:
            expected_ui_url = f"http://127.0.0.1:{ui_port}"
            if ui_url != expected_ui_url:
                errors.append(
                    "service_urls[ui] must equal the canonical loopback origin "
                    f"{expected_ui_url!r}, got {ui_url!r}"
                )

    image_refs = manifest.get("image_refs")
    if not isinstance(image_refs, Mapping):
        errors.append("image_refs must be a mapping")
    else:
        required_image_keys = REQUIRED_IMAGE_KEYS + (
            () if is_v4 else LEGACY_RETIRED_TAU_IMAGE_KEYS
        )
        for key in required_image_keys:
            if key not in image_refs:
                errors.append(f"image_refs missing required key: {key}")
        if is_v4 and any(key in image_refs for key in LEGACY_RETIRED_TAU_IMAGE_KEYS):
            errors.append("v4 image_refs must exclude the retired Tau image")
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
        unmountable_lanes = sorted(
            lane
            for lane in lanes
            if isinstance(lane, str) and lane and lane not in _LOCAL_TESTNET_MOUNTABLE_LANE_SET
        )
        if unmountable_lanes:
            errors.append(f"enabled_lanes contains unmountable lanes: {unmountable_lanes}")

    fixture_paths = manifest.get("fixture_paths")
    if not isinstance(fixture_paths, Mapping):
        errors.append("fixture_paths must be a mapping")
    else:
        for key in REQUIRED_FIXTURE_KEYS:
            if key not in fixture_paths:
                errors.append(f"fixture_paths missing required key: {key}")
        if is_v2_or_later:
            for key in V2_REQUIRED_FIXTURE_KEYS:
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

    if is_v2_or_later:
        stdlib_token_hash = manifest.get("stdlib_token_sha256")
        if not isinstance(stdlib_token_hash, str) or not _SHA256_HEX_RE.match(stdlib_token_hash):
            errors.append(
                f"stdlib_token_sha256 must match {_SHA256_HEX_RE.pattern!r}, got {stdlib_token_hash!r}"
            )

    created_at = manifest.get("created_at_ms")
    if not isinstance(created_at, int) or created_at < 0:
        errors.append(f"created_at_ms must be a non-negative int, got {created_at!r}")

    if is_v1_or_later:
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
            if is_v2_or_later:
                for key in V2_REQUIRED_HOST_KEYS:
                    value = host_paths.get(key)
                    if not isinstance(value, str) or not value.startswith("/"):
                        errors.append(f"host_paths[{key}] must be an absolute path string, got {value!r}")

    if is_v2_or_later:
        for key in V2_REQUIRED_KEYS:
            if key not in manifest:
                errors.append(f"missing required key: {key}")
        requested = manifest.get("zk_mode_requested")
        if requested not in ZK_MODES:
            errors.append(f"zk_mode_requested must be one of {sorted(ZK_MODES)!r}, got {requested!r}")
        effective = manifest.get("zk_mode_effective")
        if effective not in ZK_EFFECTIVE_MODES:
            errors.append(f"zk_mode_effective must be one of {sorted(ZK_EFFECTIVE_MODES)!r}, got {effective!r}")
        if not isinstance(manifest.get("zk_required"), bool):
            errors.append("zk_required must be bool")
        fallback_reason = manifest.get("zk_fallback_reason")
        if fallback_reason is not None and not isinstance(fallback_reason, str):
            errors.append("zk_fallback_reason must be null or string")
        verifier_kind = manifest.get("proof_verifier_kind")
        if verifier_kind not in PROOF_VERIFIER_KINDS:
            errors.append(
                f"proof_verifier_kind must be one of {sorted(PROOF_VERIFIER_KINDS)!r}, got {verifier_kind!r}"
            )
        artifact_hashes = manifest.get("proof_artifact_hashes")
        if not isinstance(artifact_hashes, Mapping):
            errors.append("proof_artifact_hashes must be a mapping")
        else:
            for key, value in artifact_hashes.items():
                if not isinstance(key, str) or not key:
                    errors.append(f"proof_artifact_hashes key must be non-empty string, got {key!r}")
                if not isinstance(value, str) or _ARTIFACT_HASH_RE.fullmatch(value) is None:
                    errors.append(
                        f"proof_artifact_hashes[{key}] must be 0x/sha256 32-byte hash, got {value!r}"
                    )
        if not isinstance(manifest.get("production_security_claim"), bool):
            errors.append("production_security_claim must be bool")
        elif manifest.get("production_security_claim") is not False:
            errors.append("production_security_claim must be false for local-testnet manifests")
        strict_artifacts_ready = isinstance(artifact_hashes, Mapping) and all(
            key in artifact_hashes for key in ("verifier", "circuit")
        )
        if effective == "strict":
            if manifest.get("zk_required") is not True:
                errors.append("strict zk mode requires zk_required=true")
            if verifier_kind != "subprocess":
                errors.append("strict zk mode requires proof_verifier_kind=subprocess")
            if not strict_artifacts_ready:
                errors.append("strict zk mode requires verifier and circuit artifact hashes")

    if is_profile_bound:
        for key in V3_REQUIRED_KEYS:
            if key not in manifest:
                errors.append(f"missing required key: {key}")
        if manifest.get("local_operator_profile_id") != CURRENT_LOCAL_OPERATOR_PROFILE_ID_V1:
            errors.append(
                "local_operator_profile_id must equal the current fail-closed profile"
            )
        if manifest.get("local_operator_profile_digest") != CURRENT_LOCAL_OPERATOR_PROFILE_DIGEST_V1:
            errors.append(
                "local_operator_profile_digest must equal the current profile digest"
            )
    return errors


def _default_zk_posture() -> dict[str, Any]:
    return {
        "zk_mode_requested": "auto-strict",
        "zk_mode_effective": "open",
        "zk_required": False,
        "zk_fallback_reason": "strict ZK verifier/artifacts were not supplied to build_manifest",
        "proof_verifier_kind": "disabled",
        "proof_artifact_hashes": {},
        "production_security_claim": False,
    }


def manifest_contains_literal(manifest: Mapping[str, Any], needle: str) -> bool:
    """Defensive grep over the serialized manifest. Used by callers to
    assert that secrets (like the raw writer token) never end up in the
    manifest. Returns True if the literal appears anywhere in the JSON
    serialization."""
    if not isinstance(needle, str) or not needle:
        raise ValueError("needle must be a non-empty string")
    serialized = json.dumps(manifest, sort_keys=True)
    return needle in serialized
