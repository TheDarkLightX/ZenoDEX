#!/usr/bin/env python3
"""Run a ZenoLedger v0 follower/watcher node.

The v0 node wraps the existing deterministic public-testnet bundle and watcher
primitives. It can bootstrap a bundle, replay it as an independent operator,
emit a watcher attestation, and serve the resulting node status over HTTP.
"""

from __future__ import annotations

import argparse
import hashlib
import hmac
import json
import re
import sys
import threading
import time
from http import HTTPStatus
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Any, Mapping, Sequence
from urllib.error import HTTPError
from urllib.parse import urljoin
from urllib.request import Request, urlopen

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.zeno_ledger_mirror import validate_mirror_index_v0
from src.integration.zeno_ledger_live_quorum_v0 import build_live_checkpoint_quorum_admission_v0
from src.integration.zeno_ledger_signer_registry import verify_signature_quorum_v0
from src.integration.zeno_ledger_v0 import (
    BATCH_CUTOFF_SCHEMA_V0,
    BODY_SCHEMA_V0,
    INGRESS_RECEIPT_SCHEMA_V0,
    build_checkpoint_v0,
    build_header_v0,
    build_tx_receipt_v0,
    canonical_body_root_v0,
    canonical_header_hash_v0,
    compute_app_hash_v0,
    compute_evidence_root_v0,
    compute_ingress_root_v0,
    compute_tx_root_v0,
    dex_state_root_v0,
    hash_v0,
    tx_hash_v0,
    validate_body_v0,
)
from src.integration.zeno_ledger_validator_schedule_v0 import build_fork_choice_report_v0
from src.integration.dex_snapshot import snapshot_from_state, state_from_snapshot
from src.state.canonical import canonical_hex_fixed_allow_0x
from tools.zeno_ledger_make_public_testnet_bundle import build_public_testnet_bundle_v0
from tools.zeno_ledger_make_testnet_bundle import (
    DEFAULT_CHAIN_ID,
    DEFAULT_SEQUENCER_ID,
    DEFAULT_TIME_MS,
)
from tools.zeno_ledger_operator_rehearsal import run_operator_rehearsal_v0
from tools.zeno_ledger_run_local import ZERO_ROOT, build_local_block_v0


NODE_STATUS_SCHEMA = "zenodex.zeno_ledger.node_status.v0"
NODE_REPORT_SCHEMA = "zenodex.zeno_ledger.node_report.v0"
NODE_SYNC_REPORT_SCHEMA = "zenodex.zeno_ledger.node_sync_report.v0"
NODE_APPEND_REPORT_SCHEMA = "zenodex.zeno_ledger.node_append_report.v0"
NODE_PULL_REPORT_SCHEMA = "zenodex.zeno_ledger.node_pull_report.v0"
NODE_EVIDENCE_REPORT_SCHEMA = "zenodex.zeno_ledger.node_evidence_report.v0"
NODE_JOIN_CONFIG_SCHEMA = "zenodex.zeno_ledger.node_join_config.v0"
NODE_JOIN_REPORT_SCHEMA = "zenodex.zeno_ledger.node_join_report.v0"
NODE_PEER_CHECK_REPORT_SCHEMA = "zenodex.zeno_ledger.node_peer_check_report.v0"
NODE_PEER_FOLLOW_REPORT_SCHEMA = "zenodex.zeno_ledger.node_peer_follow_report.v0"
NODE_PUBLIC_NETWORK_CONFIG_SCHEMA = "zenodex.zeno_ledger.public_network_config.v0"
NODE_PUBLIC_NETWORK_CONFIG_QUORUM_ADMISSION_SCHEMA = (
    "zenodex.zeno_ledger.public_network_config_quorum_admission.v0"
)
NODE_DOCTOR_REPORT_SCHEMA = "zenodex.zeno_ledger.node_doctor_report.v0"
MAX_REMOTE_ARTIFACT_BYTES = 16 * 1024 * 1024
MAX_HTTP_POST_BYTES = 2 * 1024 * 1024
MAX_TESTNET_FAUCET_AMOUNT = 1_000_000_000_000
TESTNET_FAUCET_KIND = "ZENODEX_TESTNET_FAUCET"
TESTNET_TOKEN_CREATE_KIND = "ZENODEX_TESTNET_TOKEN_CREATE"
MAX_TESTNET_TOKEN_SYMBOL_LEN = 16
MAX_TESTNET_TOKEN_NAME_LEN = 80
_TESTNET_TOKEN_SYMBOL_RE = re.compile(r"^t[A-Z0-9][A-Z0-9_]{0,14}$")
PUBLIC_NETWORK_CONFIG_QUORUM_FIELDS = frozenset(
    {
        "config_signer_registry",
        "config_signature_envelopes",
        "config_quorum_report",
        "config_quorum_admission",
    }
)


def _load_json_object(path: Path) -> Mapping[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError(f"{path} must decode to a JSON object")
    return obj


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _is_safe_relative(path_text: str) -> bool:
    path = Path(path_text)
    return path_text != "" and not path.is_absolute() and ".." not in path.parts


def _remote_url(base_url: str, rel_path: str) -> str:
    if not _is_safe_relative(rel_path):
        raise ValueError(f"unsafe remote path: {rel_path}")
    base = base_url.rstrip("/") + "/"
    return urljoin(base, rel_path)


def _fetch_remote_bytes(url: str, *, max_bytes: int = MAX_REMOTE_ARTIFACT_BYTES) -> bytes:
    with urlopen(url, timeout=30) as response:  # noqa: S310 - explicit user-supplied mirror URL
        length = response.headers.get("Content-Length")
        if length is not None:
            try:
                if int(length) > max_bytes:
                    raise ValueError(f"remote artifact too large: {url}")
            except ValueError:
                raise
        data = response.read(max_bytes + 1)
    if len(data) > max_bytes:
        raise ValueError(f"remote artifact too large: {url}")
    return data


def _normalize_transport_auth_token_v0(value: object, *, name: str) -> str:
    if not isinstance(value, str) or value == "":
        raise ValueError(f"{name} must be a non-empty string")
    if any(ord(ch) < 33 or ord(ch) > 126 for ch in value):
        raise ValueError(f"{name} must be printable ASCII without whitespace")
    return value


def _read_transport_auth_token_file_v0(path: Path | None) -> str | None:
    if path is None:
        return None
    token = path.read_text(encoding="utf-8").strip()
    return _normalize_transport_auth_token_v0(token, name=str(path))


def _auth_headers_v0(auth_token: str | None) -> dict[str, str]:
    if auth_token is None:
        return {}
    token = _normalize_transport_auth_token_v0(auth_token, name="auth_token")
    return {"Authorization": f"Bearer {token}"}


def _fetch_remote_bytes_auth(
    url: str,
    *,
    max_bytes: int = MAX_REMOTE_ARTIFACT_BYTES,
    auth_token: str | None = None,
) -> bytes:
    headers = _auth_headers_v0(auth_token)
    request: str | Request = Request(url, headers=headers) if headers else url
    with urlopen(request, timeout=30) as response:  # noqa: S310 - explicit operator-configured URL
        length = response.headers.get("Content-Length")
        if length is not None:
            try:
                if int(length) > max_bytes:
                    raise ValueError(f"remote artifact too large: {url}")
            except ValueError:
                raise
        data = response.read(max_bytes + 1)
    if len(data) > max_bytes:
        raise ValueError(f"remote artifact too large: {url}")
    return data


def _write_remote_file(*, base_url: str, rel_path: str, out_root: Path) -> bytes:
    data = _fetch_remote_bytes(_remote_url(base_url, rel_path))
    out_path = out_root / rel_path
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_bytes(data)
    return data


def _download_json(*, base_url: str, rel_path: str, out_root: Path) -> dict[str, Any]:
    data = _write_remote_file(base_url=base_url, rel_path=rel_path, out_root=out_root)
    obj = json.loads(data.decode("utf-8"))
    if not isinstance(obj, dict):
        raise ValueError(f"{rel_path} must decode to a JSON object")
    return obj


def _fetch_json_url(url: str, *, auth_token: str | None = None) -> dict[str, Any]:
    data = _fetch_remote_bytes_auth(url, auth_token=auth_token)
    obj = json.loads(data.decode("utf-8"))
    if not isinstance(obj, dict):
        raise ValueError(f"{url} must decode to a JSON object")
    return obj


def _post_json_url(
    url: str,
    value: Mapping[str, Any],
    *,
    auth_token: str | None = None,
) -> tuple[dict[str, Any], HTTPStatus]:
    payload = json.dumps(dict(value), sort_keys=True).encode("utf-8")
    headers = {"Content-Type": "application/json", **_auth_headers_v0(auth_token)}
    request = Request(
        url,
        data=payload,
        headers=headers,
        method="POST",
    )
    try:
        with urlopen(request, timeout=30) as response:  # noqa: S310 - explicit operator-configured peer URL
            status = HTTPStatus(response.status)
            data = response.read(MAX_REMOTE_ARTIFACT_BYTES + 1)
    except HTTPError as exc:
        status = HTTPStatus(exc.code)
        data = exc.read(MAX_REMOTE_ARTIFACT_BYTES + 1)
    if len(data) > MAX_REMOTE_ARTIFACT_BYTES:
        raise ValueError(f"remote response too large: {url}")
    obj = json.loads(data.decode("utf-8"))
    if not isinstance(obj, dict):
        raise ValueError(f"{url} must decode to a JSON object")
    return obj, status


def _sha256_bytes(data: bytes) -> str:
    return "0x" + hashlib.sha256(data).hexdigest()


def _safe_bundle_path(raw: object, *, bundle_root: Path, fallback: Path) -> Path:
    if isinstance(raw, str) and raw:
        path = Path(raw)
        if path.is_absolute() and path.exists():
            return path
        if not path.is_absolute() and ".." not in path.parts:
            candidate = bundle_root / path
            if candidate.exists():
                return candidate
    if fallback.exists():
        return fallback
    raise ValueError(f"missing bundle path: {fallback}")


def _header_heights(headers_dir: Path) -> list[int]:
    if not headers_dir.is_dir():
        return []
    heights: list[int] = []
    for path in headers_dir.glob("*.json"):
        try:
            heights.append(int(path.stem))
        except ValueError:
            continue
    return sorted(heights)


def _as_path(value: object, *, name: str) -> Path:
    if not isinstance(value, str) or value == "":
        raise ValueError(f"{name} must be a non-empty string path")
    return Path(value)


def _as_string_list(value: object, *, name: str) -> list[str]:
    if value is None:
        return []
    if not isinstance(value, list) or not all(isinstance(item, str) for item in value):
        raise ValueError(f"{name} must be a list of strings")
    return list(value)


def _as_path_list(value: object, *, name: str) -> list[Path]:
    return [Path(item) for item in _as_string_list(value, name=name)]


def _unique_strings(items: list[str]) -> list[str]:
    seen: set[str] = set()
    out: list[str] = []
    for item in items:
        if item not in seen:
            seen.add(item)
            out.append(item)
    return out


def _read_public_manifest(bundle_root: Path) -> dict[str, Any]:
    manifest_path = bundle_root / "public_testnet_manifest.json"
    obj = dict(_load_json_object(manifest_path))
    if obj.get("schema") != "zenodex.zeno_ledger.public_testnet_bundle.v0":
        raise ValueError("public testnet manifest schema mismatch")
    return obj


def _read_feature_suite(bundle_root: Path, public_manifest: Mapping[str, Any]) -> dict[str, Any]:
    suite_path = _safe_bundle_path(
        public_manifest.get("core_suite_path"),
        bundle_root=bundle_root,
        fallback=bundle_root / "core_features" / "feature_suite.json",
    )
    return dict(_load_json_object(suite_path))


def _download_mirror_artifacts(
    *,
    base_url: str,
    out_root: Path,
    mirror_root_rel: str,
    mirror_index_rel: str,
) -> dict[str, Any]:
    """Download one mirror index and all artifacts it binds."""

    if not _is_safe_relative(mirror_root_rel):
        raise ValueError(f"unsafe mirror root: {mirror_root_rel}")
    if not _is_safe_relative(mirror_index_rel):
        raise ValueError(f"unsafe mirror index path: {mirror_index_rel}")
    index_path_rel = str(Path(mirror_root_rel) / mirror_index_rel)
    index = _download_json(base_url=base_url, rel_path=index_path_rel, out_root=out_root)
    artifacts = index.get("artifacts")
    if not isinstance(artifacts, list):
        raise ValueError(f"{index_path_rel} artifacts must be a list")
    for raw_entry in artifacts:
        if not isinstance(raw_entry, Mapping):
            raise ValueError(f"{index_path_rel} artifact entry must be an object")
        rel = raw_entry.get("relative_path")
        expected_sha = raw_entry.get("sha256")
        if not isinstance(rel, str) or not _is_safe_relative(rel):
            raise ValueError(f"{index_path_rel} artifact relative_path is unsafe")
        if not isinstance(expected_sha, str) or not expected_sha.startswith("0x"):
            raise ValueError(f"{index_path_rel} artifact sha256 is invalid")
        artifact_rel = str(Path(mirror_root_rel) / rel)
        data = _write_remote_file(base_url=base_url, rel_path=artifact_rel, out_root=out_root)
        if _sha256_bytes(data) != expected_sha:
            raise ValueError(f"artifact hash mismatch: {artifact_rel}")
    validate_mirror_index_v0(index=index, mirror_root=out_root / mirror_root_rel)
    return index


def sync_public_bundle_from_url_v0(*, base_url: str, out_dir: Path) -> dict[str, Any]:
    """Download and verify a public ZenoLedger bundle from an HTTP directory."""

    out_dir.mkdir(parents=True, exist_ok=True)
    public_manifest = _download_json(
        base_url=base_url,
        rel_path="public_testnet_manifest.json",
        out_root=out_dir,
    )
    if public_manifest.get("schema") != "zenodex.zeno_ledger.public_testnet_bundle.v0":
        raise ValueError("public testnet manifest schema mismatch")

    bootstrap_manifest_path = str(public_manifest.get("bootstrap_manifest_path", "bootstrap/manifest.json"))
    if not _is_safe_relative(bootstrap_manifest_path):
        raise ValueError("bootstrap_manifest_path must be relative and safe")
    bootstrap_root = Path(bootstrap_manifest_path).parent.as_posix()
    bootstrap_index = _download_mirror_artifacts(
        base_url=base_url,
        out_root=out_dir,
        mirror_root_rel=bootstrap_root,
        mirror_index_rel="mirror_index.json",
    )

    core_suite_path = str(public_manifest.get("core_suite_path", "core_features/feature_suite.json"))
    if not _is_safe_relative(core_suite_path):
        raise ValueError("core_suite_path must be relative and safe")
    feature_suite = _download_json(base_url=base_url, rel_path=core_suite_path, out_root=out_dir)
    features = feature_suite.get("features")
    if not isinstance(features, list):
        raise ValueError("feature_suite.features must be a list")

    feature_indexes: list[dict[str, Any]] = []
    suite_root = Path(core_suite_path).parent
    for raw_feature in features:
        if not isinstance(raw_feature, Mapping):
            raise ValueError("feature entry must be an object")
        manifest_path = raw_feature.get("manifest_path")
        if not isinstance(manifest_path, str) or not _is_safe_relative(manifest_path):
            raise ValueError("feature manifest_path must be relative and safe")
        feature_root = (suite_root / Path(manifest_path).parent).as_posix()
        mirror_index_rel = str(raw_feature.get("mirror_index_path", "mirror_index.json"))
        if not _is_safe_relative(mirror_index_rel):
            raise ValueError("feature mirror_index_path must be relative and safe")
        feature_indexes.append(
            _download_mirror_artifacts(
                base_url=base_url,
                out_root=out_dir,
                mirror_root_rel=feature_root,
                mirror_index_rel=mirror_index_rel,
            )
        )

    # Re-read through the same local validators used by node run.
    local_public_manifest = _read_public_manifest(out_dir)
    local_feature_suite = _read_feature_suite(out_dir, local_public_manifest)
    return {
        "schema": NODE_SYNC_REPORT_SCHEMA,
        "ok": True,
        "status": "accepted",
        "base_url": base_url,
        "bundle_root": str(out_dir),
        "network_id": local_public_manifest["network_id"],
        "chain_id": local_public_manifest["chain_id"],
        "bootstrap_mirror_index_hash": bootstrap_index["mirror_index_hash"],
        "feature_suite_hash": local_feature_suite["feature_suite_hash"],
        "feature_count": local_feature_suite["feature_count"],
        "feature_mirror_count": len(feature_indexes),
        "downloaded_mirror_count": 1 + len(feature_indexes),
        "downloaded_artifact_count": int(bootstrap_index["artifact_count"])
        + sum(int(index["artifact_count"]) for index in feature_indexes),
    }


def _node_status_hash(status: Mapping[str, Any]) -> str:
    body = {key: value for key, value in status.items() if key != "node_status_hash"}
    return hash_v0("node_status_v0", body)


def _public_network_config_hash_v0(config: Mapping[str, Any]) -> str:
    excluded = {"network_config_hash", *PUBLIC_NETWORK_CONFIG_QUORUM_FIELDS}
    body = {key: value for key, value in config.items() if key not in excluded}
    return hash_v0("public_network_config_v0", body)


def _has_public_network_config_quorum_fields_v0(config: Mapping[str, Any]) -> bool:
    return any(field in config for field in PUBLIC_NETWORK_CONFIG_QUORUM_FIELDS)


def _public_network_config_quorum_admission_v0(
    *,
    network_config_hash: str,
    quorum_report: Mapping[str, Any],
) -> dict[str, Any]:
    body = {
        "schema": NODE_PUBLIC_NETWORK_CONFIG_QUORUM_ADMISSION_SCHEMA,
        "ok": True,
        "status": "accepted",
        "payload_kind": "public_network_config",
        "network_config_hash": _require_root_v0(network_config_hash, name="network_config_hash"),
        "registry_hash": quorum_report["registry_hash"],
        "threshold": quorum_report["threshold"],
        "accepted_weight": quorum_report["accepted_weight"],
        "accepted_signature_count": len(quorum_report["accepted_signatures"]),
        "quorum_report_hash": quorum_report["quorum_report_hash"],
    }
    return {**body, "admission_hash": hash_v0("public_network_config_quorum_admission_v0", body)}


def attach_public_network_config_quorum_v0(
    *,
    network_config: Mapping[str, Any],
    registry: Mapping[str, Any],
    envelopes: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    """Attach signer-quorum evidence to a public network config."""

    config = dict(network_config)
    if config.get("schema") != NODE_PUBLIC_NETWORK_CONFIG_SCHEMA:
        raise ValueError("public network config schema mismatch")
    network_config_hash = _public_network_config_hash_v0(config)
    if config.get("network_config_hash") != network_config_hash:
        raise ValueError("public network config hash mismatch")
    quorum_report = verify_signature_quorum_v0(
        registry=registry,
        payload_kind="public_network_config",
        payload_hash=network_config_hash,
        envelopes=envelopes,
    )
    return {
        **config,
        "config_signer_registry": dict(registry),
        "config_signature_envelopes": [dict(envelope) for envelope in envelopes],
        "config_quorum_report": quorum_report,
        "config_quorum_admission": _public_network_config_quorum_admission_v0(
            network_config_hash=network_config_hash,
            quorum_report=quorum_report,
        ),
    }


def validate_public_network_config_quorum_v0(
    *,
    network_config: Mapping[str, Any],
    expected_config_signer_registry_hash: str | None = None,
) -> dict[str, Any]:
    """Validate signer-quorum evidence attached to a public network config."""

    config = dict(network_config)
    if config.get("schema") != NODE_PUBLIC_NETWORK_CONFIG_SCHEMA:
        raise ValueError("public network config schema mismatch")
    network_config_hash = _public_network_config_hash_v0(config)
    if config.get("network_config_hash") != network_config_hash:
        raise ValueError("public network config hash mismatch")
    registry = config.get("config_signer_registry")
    if not isinstance(registry, Mapping):
        raise ValueError("public network config quorum registry is required")
    envelopes = config.get("config_signature_envelopes")
    if not isinstance(envelopes, Sequence) or isinstance(envelopes, (str, bytes, bytearray)):
        raise ValueError("public network config quorum envelopes are required")
    if expected_config_signer_registry_hash is not None:
        expected_hash = _require_root_v0(
            expected_config_signer_registry_hash,
            name="expected_config_signer_registry_hash",
        )
        if registry.get("registry_hash") != expected_hash:
            raise ValueError("public network config signer registry hash did not match expected hash")
    quorum_report = verify_signature_quorum_v0(
        registry=registry,
        payload_kind="public_network_config",
        payload_hash=network_config_hash,
        envelopes=[dict(envelope) for envelope in envelopes],
    )
    if config.get("config_quorum_report") != quorum_report:
        raise ValueError("public network config quorum report mismatch")
    admission = _public_network_config_quorum_admission_v0(
        network_config_hash=network_config_hash,
        quorum_report=quorum_report,
    )
    if config.get("config_quorum_admission") != admission:
        raise ValueError("public network config quorum admission mismatch")
    return admission


def build_node_status_v0(
    *,
    bundle_root: Path,
    node_id: str,
    data_dir: Path,
    operator_report: Mapping[str, Any],
) -> dict[str, Any]:
    """Build a compact status object for a verified follower/watcher node."""

    public_manifest = _read_public_manifest(bundle_root)
    feature_suite = _read_feature_suite(bundle_root, public_manifest)
    bootstrap_manifest_path = _safe_bundle_path(
        public_manifest.get("bootstrap_manifest_path"),
        bundle_root=bundle_root,
        fallback=bundle_root / "bootstrap" / "manifest.json",
    )
    bootstrap_root = bootstrap_manifest_path.parent
    bootstrap_manifest = _load_json_object(bootstrap_manifest_path)
    heights = _header_heights(bootstrap_root / "ledger" / "headers")
    latest_height = heights[-1] if heights else 0
    covered_features = list(operator_report.get("covered_features", []))
    body = {
        "schema": NODE_STATUS_SCHEMA,
        "ok": operator_report.get("ok") is True,
        "status": "accepted" if operator_report.get("ok") is True else "rejected",
        "node_id": node_id,
        "node_role": "follower_watcher",
        "network_id": public_manifest["network_id"],
        "chain_id": public_manifest["chain_id"],
        "bundle_root": str(bundle_root),
        "data_dir": str(data_dir),
        "latest_height": latest_height,
        "last_header_hash": operator_report.get("last_header_hash"),
        "last_app_hash": operator_report.get("last_app_hash"),
        "operator_attestation_path": operator_report.get("operator_attestation_path"),
        "operator_attestation_hash": operator_report.get("operator_attestation_hash"),
        "combined_testnet_status_path": operator_report.get("combined_testnet_status_path"),
        "combined_testnet_status_hash": operator_report.get("combined_testnet_status_hash"),
        "combined_watcher_count": operator_report.get("combined_watcher_count"),
        "sequencer_set_hash": bootstrap_manifest["sequencer_set_hash"],
        "mirror_index_hash": operator_report.get("mirror_index_hash"),
        "feature_suite_hash": operator_report.get("feature_suite_hash"),
        "covered_feature_count": len(covered_features),
        "covered_features": covered_features,
        "required_features": list(feature_suite.get("required_features", [])),
        "token_symbol": public_manifest.get("token_symbol"),
        "token_posture": dict(public_manifest.get("token_posture", {})),
        "test_token_catalog": list(public_manifest.get("test_token_catalog", [])),
        "testnet_faucet_posture": dict(public_manifest.get("testnet_faucet_posture", {})),
        "testnet_token_support": {
            "native_test_symbol": public_manifest.get("token_symbol"),
            "fixture_tokens": "core feature suites use deterministic test assets",
            "faucet_scope": "testnet-only feature lanes",
            "release_scope": str(dict(public_manifest.get("token_posture", {})).get("release_scope", "")),
        },
    }
    return {**body, "node_status_hash": hash_v0("node_status_v0", body)}


def run_node_once_v0(
    *,
    bundle_root: Path,
    node_id: str,
    data_dir: Path,
    observed_time_ms: int | None = None,
    peer_watcher_attestation_paths: list[Path] | None = None,
) -> dict[str, Any]:
    """Replay a bundle as a node and write node status artifacts."""

    peers = list(peer_watcher_attestation_paths or [])
    data_dir.mkdir(parents=True, exist_ok=True)
    operator_report = run_operator_rehearsal_v0(
        bundle_root=bundle_root,
        operator_id=node_id,
        out_dir=data_dir,
        observed_time_ms=observed_time_ms,
        peer_watcher_attestation_paths=peers,
    )
    operator_report_path = data_dir / "operator_rehearsal_report.json"
    _write_json(operator_report_path, operator_report)
    status = build_node_status_v0(
        bundle_root=bundle_root.resolve(),
        node_id=node_id,
        data_dir=data_dir.resolve(),
        operator_report=operator_report,
    )
    status_path = data_dir / "node_status.json"
    _write_json(status_path, status)
    return {
        "schema": NODE_REPORT_SCHEMA,
        "ok": operator_report.get("ok") is True and status.get("ok") is True,
        "status": "accepted" if operator_report.get("ok") is True and status.get("ok") is True else "rejected",
        "node_id": node_id,
        "node_status_path": str(status_path),
        "node_status_hash": status["node_status_hash"],
        "operator_rehearsal_report_path": str(operator_report_path),
        "operator_attestation_path": operator_report.get("operator_attestation_path"),
        "combined_testnet_status_path": operator_report.get("combined_testnet_status_path"),
        "combined_testnet_status_hash": operator_report.get("combined_testnet_status_hash"),
        "combined_watcher_count": operator_report.get("combined_watcher_count"),
        "latest_height": status["latest_height"],
        "covered_feature_count": status["covered_feature_count"],
        "covered_features": status["covered_features"],
    }


def _empty_evidence_v0() -> dict[str, list[object]]:
    return {
        "upba_certificates": [],
        "price_grid_tables": [],
        "uniform_batch_hypergraph_roots": [],
        "oracle_packets": [],
        "proof_receipts": [],
        "rejection_receipts": [],
    }


def _ingress_receipt_v0(
    *,
    chain_id: str,
    tx_hash: str,
    height: int,
    time_ms: int,
    sequencer_id: str,
) -> dict[str, Any]:
    body = {
        "schema": INGRESS_RECEIPT_SCHEMA_V0,
        "chain_id": chain_id,
        "tx_hash": tx_hash,
        "received_time_ms": time_ms,
        "received_sequence": height * 1_000,
        "sequencer_id": sequencer_id,
        "status": "included",
        "height": height,
        "index": 0,
        "reject_code": None,
    }
    return {**body, "receipt_hash": hash_v0("node_ingress_receipt_v0", body)}


def _body_for_tx_v0(
    *,
    chain_id: str,
    height: int,
    time_ms: int,
    sequencer_id: str,
    tx: Mapping[str, Any],
) -> dict[str, Any]:
    tx_obj = dict(tx)
    tx_hash = tx_hash_v0(tx_obj)
    body = {
        "schema": BODY_SCHEMA_V0,
        "chain_id": chain_id,
        "height": height,
        "ingress": {
            "batch_cutoff": {
                "schema": BATCH_CUTOFF_SCHEMA_V0,
                "chain_id": chain_id,
                "height": height,
                "cutoff_time_ms": time_ms,
                "cutoff_sequence": height * 1_000,
                "sequencer_id": sequencer_id,
                "policy_id": "zeno_ledger_node_live_append_v0",
                "policy_digest": hash_v0(
                    "node_live_append_policy_v0",
                    {"chain_id": chain_id, "policy_id": "zeno_ledger_node_live_append_v0"},
                ),
            },
            "ingress_receipts": [
                _ingress_receipt_v0(
                    chain_id=chain_id,
                    tx_hash=tx_hash,
                    height=height,
                    time_ms=time_ms,
                    sequencer_id=sequencer_id,
                )
            ],
            "forced_inclusion_requests": [],
            "forced_inclusion_decisions": [],
        },
        "transactions": [tx_obj],
        "settlement_envelopes": [],
        "evidence": _empty_evidence_v0(),
    }
    validate_body_v0(body)
    return body


def _read_http_json_body(handler: BaseHTTPRequestHandler) -> dict[str, Any]:
    raw_length = handler.headers.get("Content-Length")
    if raw_length is None:
        raise ValueError("Content-Length is required")
    try:
        length = int(raw_length)
    except ValueError as exc:
        raise ValueError("Content-Length must be an integer") from exc
    if length < 0 or length > MAX_HTTP_POST_BYTES:
        raise ValueError("request body too large")
    payload = handler.rfile.read(length)
    obj = json.loads(payload.decode("utf-8"))
    if not isinstance(obj, dict):
        raise ValueError("request body must be a JSON object")
    return obj


def _require_pubkey_v0(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise ValueError(f"{name} must be a string")
    return canonical_hex_fixed_allow_0x(value, nbytes=48, name=name)


def _require_asset_v0(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise ValueError(f"{name} must be a string")
    return canonical_hex_fixed_allow_0x(value, nbytes=32, name=name)


def _require_root_v0(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise ValueError(f"{name} must be a string")
    return canonical_hex_fixed_allow_0x(value, nbytes=32, name=name)


def _require_positive_amount_v0(value: object, *, name: str, maximum: int) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value <= 0:
        raise ValueError(f"{name} must be a positive int")
    if value > maximum:
        raise ValueError(f"{name} exceeds maximum")
    return int(value)


def _faucet_tx_v0(
    *,
    tx_id: str,
    to_pubkey: str,
    asset: str,
    amount: int,
) -> dict[str, Any]:
    return {
        "tx_id": tx_id,
        "kind": TESTNET_FAUCET_KIND,
        "to_pubkey": to_pubkey,
        "asset": asset,
        "amount": amount,
    }


def _testnet_token_registry_path(data_dir: Path) -> Path:
    return data_dir / "testnet_token_registry.json"


def _testnet_token_registry_hash_v0(registry: Mapping[str, Any]) -> str:
    body = {key: value for key, value in dict(registry).items() if key != "token_registry_hash"}
    return hash_v0("testnet_token_registry_v0", body)


def _empty_testnet_token_registry_v0() -> dict[str, Any]:
    body = {
        "schema": "zenodex.zeno_ledger.testnet_token_registry.v0",
        "tokens": [],
    }
    return {**body, "token_registry_hash": _testnet_token_registry_hash_v0(body)}


def _load_testnet_token_registry_v0(data_dir: Path) -> dict[str, Any]:
    path = _testnet_token_registry_path(data_dir)
    if not path.is_file():
        return _empty_testnet_token_registry_v0()
    registry = dict(_load_json_object(path))
    if registry.get("schema") != "zenodex.zeno_ledger.testnet_token_registry.v0":
        raise ValueError("testnet token registry schema mismatch")
    expected = _testnet_token_registry_hash_v0(registry)
    if registry.get("token_registry_hash") != expected:
        raise ValueError("testnet token registry hash mismatch")
    tokens = registry.get("tokens")
    if not isinstance(tokens, list):
        raise ValueError("testnet token registry tokens must be a list")
    return registry


def _write_testnet_token_registry_v0(data_dir: Path, registry: Mapping[str, Any]) -> dict[str, Any]:
    body = {key: value for key, value in dict(registry).items() if key != "token_registry_hash"}
    out = {**body, "token_registry_hash": _testnet_token_registry_hash_v0(body)}
    _write_json(_testnet_token_registry_path(data_dir), out)
    return out


def _require_token_symbol_v0(value: object) -> str:
    if not isinstance(value, str):
        raise ValueError("symbol must be a string")
    raw = value.strip()
    symbol = "t" + raw[1:].upper() if raw[:1].lower() == "t" else raw.upper()
    if len(symbol) > MAX_TESTNET_TOKEN_SYMBOL_LEN or not _TESTNET_TOKEN_SYMBOL_RE.fullmatch(symbol):
        raise ValueError("symbol must match t[A-Z0-9][A-Z0-9_]{0,14}")
    return symbol


def _require_token_name_v0(value: object) -> str:
    if not isinstance(value, str):
        raise ValueError("name must be a string")
    name = " ".join(value.strip().split())
    if not name or len(name) > MAX_TESTNET_TOKEN_NAME_LEN:
        raise ValueError("name must be non-empty and at most 80 characters")
    return name


def _require_token_decimals_v0(value: object) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0 or value > 18:
        raise ValueError("decimals must be an int in [0, 18]")
    return int(value)


def _derive_testnet_asset_id_v0(*, symbol: str, name: str, decimals: int, creator_pubkey: str, salt: str) -> str:
    return hash_v0(
        "testnet_asset_id_v0",
        {
            "symbol": symbol,
            "name": name,
            "decimals": decimals,
            "creator_pubkey": creator_pubkey,
            "salt": salt,
        },
    )


def _token_create_tx_v0(
    *,
    tx_id: str,
    asset: str,
    symbol: str,
    name: str,
    decimals: int,
    creator_pubkey: str,
) -> dict[str, Any]:
    return {
        "tx_id": tx_id,
        "kind": TESTNET_TOKEN_CREATE_KIND,
        "asset": asset,
        "symbol": symbol,
        "name": name,
        "decimals": decimals,
        "creator_pubkey": creator_pubkey,
    }


def _is_faucet_body_v0(body: Mapping[str, Any]) -> bool:
    txs = body.get("transactions")
    if not isinstance(txs, list) or len(txs) != 1 or not isinstance(txs[0], Mapping):
        return False
    return txs[0].get("kind") == TESTNET_FAUCET_KIND


def _is_token_create_body_v0(body: Mapping[str, Any]) -> bool:
    txs = body.get("transactions")
    if not isinstance(txs, list) or len(txs) != 1 or not isinstance(txs[0], Mapping):
        return False
    return txs[0].get("kind") == TESTNET_TOKEN_CREATE_KIND


def _latest_live_state_path(data_dir: Path) -> Path:
    return data_dir / "live_state.json"


def _live_base_paths(*, bundle_root: Path, data_dir: Path, node_status: Mapping[str, Any]) -> dict[str, Path | int]:
    live_state_path = _latest_live_state_path(data_dir)
    if live_state_path.is_file():
        live_state = _load_json_object(live_state_path)
        latest_height = int(live_state["latest_height"])
        return {
            "latest_height": latest_height,
            "prev_header_path": Path(str(live_state["latest_header_path"])),
            "pre_snapshot_path": Path(str(live_state["latest_snapshot_path"])),
        }

    latest_height = int(node_status["latest_height"])
    bootstrap_root = bundle_root / "bootstrap"
    return {
        "latest_height": latest_height,
        "prev_header_path": bootstrap_root / "ledger" / "headers" / f"{latest_height}.json",
        "pre_snapshot_path": bootstrap_root / "ledger" / "snapshots" / f"{latest_height}.json",
    }


def _write_live_state(
    *,
    data_dir: Path,
    height: int,
    header_path: str,
    snapshot_path: str,
    header_hash: str,
    app_hash: str,
) -> None:
    live_state = {
        "schema": "zenodex.zeno_ledger.node_live_state.v0",
        "latest_height": height,
        "latest_header_path": header_path,
        "latest_snapshot_path": snapshot_path,
        "latest_header_hash": header_hash,
        "latest_app_hash": app_hash,
    }
    _write_json(_latest_live_state_path(data_dir), live_state)


def append_dex_transaction_v0(
    *,
    data_dir: Path,
    tx: Mapping[str, Any],
    time_ms: int,
    require_intent_signatures: bool = True,
    allow_unsigned_intents_if_tx_sender_matches: bool = False,
) -> dict[str, Any]:
    """Append one testnet DEX transaction to a node-local live ledger.

    Preconditions:
    - `tx` may come from an untrusted network boundary.
    - unsigned intent bypass is only safe when an outer transport has already
      authenticated `tx_sender_pubkey`. Public node intake does not provide that
      binding, so the secure default requires per-intent signatures.

    Postcondition:
    - rejected DEX transactions do not advance the node's live tip.
    """

    node_status = load_node_status_v0(data_dir)
    bundle_root = Path(str(node_status["bundle_root"]))
    public_manifest = _read_public_manifest(bundle_root)
    bootstrap_manifest = _load_json_object(bundle_root / "bootstrap" / "manifest.json")
    base = _live_base_paths(bundle_root=bundle_root, data_dir=data_dir, node_status=node_status)
    latest_height = int(base["latest_height"])
    height = latest_height + 1
    sequencer_id = str(public_manifest["sequencer_id"])
    chain_id = str(public_manifest["chain_id"])
    body = _body_for_tx_v0(
        chain_id=chain_id,
        height=height,
        time_ms=time_ms,
        sequencer_id=sequencer_id,
        tx=tx,
    )
    live_body_path = data_dir / "live_bodies" / f"{height}.json"
    _write_json(live_body_path, body)
    live_ledger_dir = data_dir / "live_ledger"
    block_report = build_local_block_v0(
        body_path=live_body_path,
        out_dir=live_ledger_dir,
        time_ms=time_ms,
        pre_snapshot_path=Path(str(base["pre_snapshot_path"])),
        prev_header_path=Path(str(base["prev_header_path"])),
        trusted_prev_header_hash=ZERO_ROOT,
        sequencer_set_hash=str(bootstrap_manifest["sequencer_set_hash"]),
        data_availability_root=ZERO_ROOT,
        proof_journal_hash=ZERO_ROOT,
        config_digest=str(bootstrap_manifest["config_digest"]),
        module_versions_digest=str(bootstrap_manifest["module_versions_digest"]),
        signature_set_root=ZERO_ROOT,
        allow_missing_settlement=True,
        require_intent_signatures=require_intent_signatures,
        allow_unsigned_intents_if_tx_sender_matches=allow_unsigned_intents_if_tx_sender_matches,
    )
    receipts_path = Path(str(block_report["receipts_path"]))
    receipts = json.loads(receipts_path.read_text(encoding="utf-8"))
    accepted = bool(receipts and isinstance(receipts[0], Mapping) and receipts[0].get("accepted") is True)
    receipt = dict(receipts[0]) if receipts and isinstance(receipts[0], Mapping) else None
    if not accepted:
        return {
            "schema": NODE_APPEND_REPORT_SCHEMA,
            "ok": False,
            "status": "rejected",
            "node_id": node_status["node_id"],
            "tx_accepted": False,
            "height": height,
            "tx_hash": tx_hash_v0(dict(tx)),
            "receipt": receipt,
            "body_path": block_report["body_path"],
            "receipts_path": block_report["receipts_path"],
        }
    _write_live_state(
        data_dir=data_dir,
        height=height,
        header_path=str(block_report["header_path"]),
        snapshot_path=str(block_report["post_snapshot_path"]),
        header_hash=str(block_report["header_hash"]),
        app_hash=str(block_report["app_hash"]),
    )
    report = {
        "schema": NODE_APPEND_REPORT_SCHEMA,
        "ok": True,
        "status": "accepted",
        "node_id": node_status["node_id"],
        "tx_accepted": accepted,
        "height": height,
        "tx_hash": tx_hash_v0(dict(tx)),
        "header_hash": block_report["header_hash"],
        "app_hash": block_report["app_hash"],
        "body_path": block_report["body_path"],
        "header_path": block_report["header_path"],
        "checkpoint_path": block_report["checkpoint_path"],
        "receipts_path": block_report["receipts_path"],
        "post_snapshot_path": block_report["post_snapshot_path"],
        "receipt": receipts[0] if receipts else None,
    }
    append_report_path = data_dir / "append_reports" / f"{height}.json"
    _write_json(append_report_path, report)
    return {**report, "append_report_path": str(append_report_path)}


def _build_faucet_block_from_body_v0(
    *,
    data_dir: Path,
    body: Mapping[str, Any],
    time_ms: int,
    prev_header_path: Path,
    pre_snapshot_path: Path,
    sequencer_set_hash: str,
    config_digest: str,
    module_versions_digest: str,
) -> dict[str, Any]:
    body_obj = dict(body)
    validate_body_v0(body_obj)
    if not _is_faucet_body_v0(body_obj):
        raise ValueError("body is not a testnet faucet body")
    tx = dict(body_obj["transactions"][0])
    to_pubkey = _require_pubkey_v0(tx.get("to_pubkey"), name="faucet.to_pubkey")
    asset = _require_asset_v0(tx.get("asset"), name="faucet.asset")
    amount = _require_positive_amount_v0(
        tx.get("amount"),
        name="faucet.amount",
        maximum=MAX_TESTNET_FAUCET_AMOUNT,
    )
    pre_snapshot = _load_json_object(pre_snapshot_path)
    pre_state = state_from_snapshot(pre_snapshot)
    pre_state_root = dex_state_root_v0(pre_state)
    pre_state.balances.add(to_pubkey, asset, amount)
    post_state_root = dex_state_root_v0(pre_state)
    post_snapshot = snapshot_from_state(pre_state).data
    height = int(body_obj["height"])
    chain_id = str(body_obj["chain_id"])
    prev_header = dict(_load_json_object(prev_header_path))
    prev_header_hash = canonical_header_hash_v0(prev_header)
    evidence_root = compute_evidence_root_v0(body_obj["evidence"])  # type: ignore[arg-type]
    app_hash = compute_app_hash_v0(
        {
            "chain_id": chain_id,
            "height": height,
            "post_state_root": post_state_root,
            "evidence_root": evidence_root,
            "config_digest": config_digest,
            "module_versions_digest": module_versions_digest,
        }
    )
    header = build_header_v0(
        chain_id=chain_id,
        height=height,
        time_ms=time_ms,
        prev_header_hash=prev_header_hash,
        sequencer_set_hash=sequencer_set_hash,
        ingress_root=compute_ingress_root_v0(body_obj["ingress"]),  # type: ignore[arg-type]
        tx_root=compute_tx_root_v0(body_obj["transactions"]),  # type: ignore[arg-type]
        pre_state_root=pre_state_root,
        post_state_root=post_state_root,
        app_hash=app_hash,
        evidence_root=evidence_root,
        body_root=canonical_body_root_v0(body_obj),
        data_availability_root=ZERO_ROOT,
        proof_journal_hash=ZERO_ROOT,
        config_digest=config_digest,
        module_versions_digest=module_versions_digest,
        signature_set_root=ZERO_ROOT,
    )
    checkpoint = build_checkpoint_v0(header)
    header_hash = canonical_header_hash_v0(header)
    tx_hash = tx_hash_v0(tx)
    receipt = build_tx_receipt_v0(
        tx_hash=tx_hash,
        height=height,
        index=0,
        accepted=True,
        error_code=None,
        state_changed=True,
    )
    live_ledger_dir = data_dir / "live_ledger"
    header_path = live_ledger_dir / "headers" / f"{height}.json"
    body_path = live_ledger_dir / "bodies" / f"{height}.json"
    checkpoint_path = live_ledger_dir / "checkpoints" / f"{height}.json"
    receipts_path = live_ledger_dir / "receipts" / f"{height}.json"
    snapshot_path = live_ledger_dir / "snapshots" / f"{height}.json"
    _write_json(header_path, header)
    _write_json(body_path, body_obj)
    _write_json(checkpoint_path, checkpoint)
    _write_json(receipts_path, [receipt])
    _write_json(snapshot_path, post_snapshot)
    return {
        "height": height,
        "tx_hash": tx_hash,
        "header_hash": header_hash,
        "app_hash": app_hash,
        "body_path": str(body_path),
        "header_path": str(header_path),
        "checkpoint_path": str(checkpoint_path),
        "receipts_path": str(receipts_path),
        "post_snapshot_path": str(snapshot_path),
        "receipt": receipt,
    }


def _token_registry_entry_from_tx_v0(*, tx: Mapping[str, Any], height: int) -> dict[str, Any]:
    asset = _require_asset_v0(tx.get("asset"), name="token.asset")
    symbol = _require_token_symbol_v0(tx.get("symbol"))
    name = _require_token_name_v0(tx.get("name"))
    decimals = _require_token_decimals_v0(tx.get("decimals"))
    creator_pubkey = _require_pubkey_v0(tx.get("creator_pubkey"), name="token.creator_pubkey")
    tx_id = str(tx.get("tx_id", ""))
    if not tx_id:
        raise ValueError("token.tx_id is required")
    return {
        "asset": asset,
        "symbol": symbol,
        "name": name,
        "decimals": decimals,
        "creator_pubkey": creator_pubkey,
        "created_height": height,
        "tx_id": tx_id,
        "tx_hash": tx_hash_v0(dict(tx)),
    }


def _apply_token_create_to_registry_v0(*, data_dir: Path, body: Mapping[str, Any]) -> dict[str, Any]:
    if not _is_token_create_body_v0(body):
        raise ValueError("body is not a testnet token-create body")
    tx = body["transactions"][0]
    if not isinstance(tx, Mapping):
        raise ValueError("token-create transaction must be an object")
    entry = _token_registry_entry_from_tx_v0(tx=tx, height=int(body["height"]))
    registry = _load_testnet_token_registry_v0(data_dir)
    tokens = list(registry.get("tokens", []))
    for existing in tokens:
        if not isinstance(existing, Mapping):
            raise ValueError("testnet token registry entry must be an object")
        if existing.get("asset") == entry["asset"] or existing.get("symbol") == entry["symbol"]:
            if dict(existing) == entry:
                return registry
            raise ValueError("testnet token asset or symbol already registered")
    tokens.append(entry)
    tokens.sort(key=lambda item: (str(item["symbol"]), str(item["asset"])))
    return _write_testnet_token_registry_v0(data_dir, {**registry, "tokens": tokens})


def _build_token_create_block_from_body_v0(
    *,
    data_dir: Path,
    body: Mapping[str, Any],
    time_ms: int,
    prev_header_path: Path,
    pre_snapshot_path: Path,
    sequencer_set_hash: str,
    config_digest: str,
    module_versions_digest: str,
) -> dict[str, Any]:
    body_obj = dict(body)
    validate_body_v0(body_obj)
    if not _is_token_create_body_v0(body_obj):
        raise ValueError("body is not a testnet token-create body")
    tx = dict(body_obj["transactions"][0])
    _token_registry_entry_from_tx_v0(tx=tx, height=int(body_obj["height"]))
    pre_snapshot = _load_json_object(pre_snapshot_path)
    pre_state = state_from_snapshot(pre_snapshot)
    pre_state_root = dex_state_root_v0(pre_state)
    post_state_root = pre_state_root
    height = int(body_obj["height"])
    chain_id = str(body_obj["chain_id"])
    prev_header = dict(_load_json_object(prev_header_path))
    prev_header_hash = canonical_header_hash_v0(prev_header)
    evidence_root = compute_evidence_root_v0(body_obj["evidence"])  # type: ignore[arg-type]
    app_hash = compute_app_hash_v0(
        {
            "chain_id": chain_id,
            "height": height,
            "post_state_root": post_state_root,
            "evidence_root": evidence_root,
            "config_digest": config_digest,
            "module_versions_digest": module_versions_digest,
        }
    )
    header = build_header_v0(
        chain_id=chain_id,
        height=height,
        time_ms=time_ms,
        prev_header_hash=prev_header_hash,
        sequencer_set_hash=sequencer_set_hash,
        ingress_root=compute_ingress_root_v0(body_obj["ingress"]),  # type: ignore[arg-type]
        tx_root=compute_tx_root_v0(body_obj["transactions"]),  # type: ignore[arg-type]
        pre_state_root=pre_state_root,
        post_state_root=post_state_root,
        app_hash=app_hash,
        evidence_root=evidence_root,
        body_root=canonical_body_root_v0(body_obj),
        data_availability_root=ZERO_ROOT,
        proof_journal_hash=ZERO_ROOT,
        config_digest=config_digest,
        module_versions_digest=module_versions_digest,
        signature_set_root=ZERO_ROOT,
    )
    checkpoint = build_checkpoint_v0(header)
    header_hash = canonical_header_hash_v0(header)
    tx_hash = tx_hash_v0(tx)
    receipt = build_tx_receipt_v0(
        tx_hash=tx_hash,
        height=height,
        index=0,
        accepted=True,
        error_code=None,
        state_changed=False,
    )
    live_ledger_dir = data_dir / "live_ledger"
    header_path = live_ledger_dir / "headers" / f"{height}.json"
    body_path = live_ledger_dir / "bodies" / f"{height}.json"
    checkpoint_path = live_ledger_dir / "checkpoints" / f"{height}.json"
    receipts_path = live_ledger_dir / "receipts" / f"{height}.json"
    snapshot_path = live_ledger_dir / "snapshots" / f"{height}.json"
    _write_json(header_path, header)
    _write_json(body_path, body_obj)
    _write_json(checkpoint_path, checkpoint)
    _write_json(receipts_path, [receipt])
    _write_json(snapshot_path, pre_snapshot)
    registry = _apply_token_create_to_registry_v0(data_dir=data_dir, body=body_obj)
    return {
        "height": height,
        "tx_hash": tx_hash,
        "header_hash": header_hash,
        "app_hash": app_hash,
        "body_path": str(body_path),
        "header_path": str(header_path),
        "checkpoint_path": str(checkpoint_path),
        "receipts_path": str(receipts_path),
        "post_snapshot_path": str(snapshot_path),
        "receipt": receipt,
        "testnet_token_registry_hash": registry["token_registry_hash"],
        "testnet_token": _token_registry_entry_from_tx_v0(tx=tx, height=height),
    }


def append_testnet_faucet_v0(
    *,
    data_dir: Path,
    to_pubkey: str,
    asset: str,
    amount: int,
    time_ms: int,
    tx_id: str = "node-testnet-faucet-v0",
) -> dict[str, Any]:
    """Append a testnet-only faucet mint to the node-local live ledger."""

    node_status = load_node_status_v0(data_dir)
    bundle_root = Path(str(node_status["bundle_root"]))
    public_manifest = _read_public_manifest(bundle_root)
    bootstrap_manifest = _load_json_object(bundle_root / "bootstrap" / "manifest.json")
    base = _live_base_paths(bundle_root=bundle_root, data_dir=data_dir, node_status=node_status)
    latest_height = int(base["latest_height"])
    height = latest_height + 1
    tx = _faucet_tx_v0(
        tx_id=tx_id,
        to_pubkey=_require_pubkey_v0(to_pubkey, name="to_pubkey"),
        asset=_require_asset_v0(asset, name="asset"),
        amount=_require_positive_amount_v0(amount, name="amount", maximum=MAX_TESTNET_FAUCET_AMOUNT),
    )
    body = _body_for_tx_v0(
        chain_id=str(public_manifest["chain_id"]),
        height=height,
        time_ms=time_ms,
        sequencer_id=str(public_manifest["sequencer_id"]),
        tx=tx,
    )
    block_report = _build_faucet_block_from_body_v0(
        data_dir=data_dir,
        body=body,
        time_ms=time_ms,
        prev_header_path=Path(str(base["prev_header_path"])),
        pre_snapshot_path=Path(str(base["pre_snapshot_path"])),
        sequencer_set_hash=str(bootstrap_manifest["sequencer_set_hash"]),
        config_digest=str(bootstrap_manifest["config_digest"]),
        module_versions_digest=str(bootstrap_manifest["module_versions_digest"]),
    )
    _write_live_state(
        data_dir=data_dir,
        height=height,
        header_path=str(block_report["header_path"]),
        snapshot_path=str(block_report["post_snapshot_path"]),
        header_hash=str(block_report["header_hash"]),
        app_hash=str(block_report["app_hash"]),
    )
    report = {
        "schema": NODE_APPEND_REPORT_SCHEMA,
        "ok": True,
        "status": "accepted",
        "node_id": node_status["node_id"],
        "append_kind": "testnet_faucet",
        **block_report,
    }
    append_report_path = data_dir / "append_reports" / f"{height}.json"
    _write_json(append_report_path, report)
    return {**report, "append_report_path": str(append_report_path)}


def append_testnet_token_create_v0(
    *,
    data_dir: Path,
    symbol: str,
    name: str,
    decimals: int,
    creator_pubkey: str,
    time_ms: int,
    tx_id: str = "node-testnet-token-create-v0",
    asset: str | None = None,
    salt: str = "default",
) -> dict[str, Any]:
    """Append a testnet-only token metadata registration to the live ledger."""

    node_status = load_node_status_v0(data_dir)
    bundle_root = Path(str(node_status["bundle_root"]))
    public_manifest = _read_public_manifest(bundle_root)
    bootstrap_manifest = _load_json_object(bundle_root / "bootstrap" / "manifest.json")
    base = _live_base_paths(bundle_root=bundle_root, data_dir=data_dir, node_status=node_status)
    latest_height = int(base["latest_height"])
    height = latest_height + 1
    checked_symbol = _require_token_symbol_v0(symbol)
    checked_name = _require_token_name_v0(name)
    checked_decimals = _require_token_decimals_v0(decimals)
    checked_creator = _require_pubkey_v0(creator_pubkey, name="creator_pubkey")
    checked_asset = (
        _require_asset_v0(asset, name="asset")
        if asset is not None
        else _derive_testnet_asset_id_v0(
            symbol=checked_symbol,
            name=checked_name,
            decimals=checked_decimals,
            creator_pubkey=checked_creator,
            salt=salt,
        )
    )
    tx = _token_create_tx_v0(
        tx_id=tx_id,
        asset=checked_asset,
        symbol=checked_symbol,
        name=checked_name,
        decimals=checked_decimals,
        creator_pubkey=checked_creator,
    )
    body = _body_for_tx_v0(
        chain_id=str(public_manifest["chain_id"]),
        height=height,
        time_ms=time_ms,
        sequencer_id=str(public_manifest["sequencer_id"]),
        tx=tx,
    )
    block_report = _build_token_create_block_from_body_v0(
        data_dir=data_dir,
        body=body,
        time_ms=time_ms,
        prev_header_path=Path(str(base["prev_header_path"])),
        pre_snapshot_path=Path(str(base["pre_snapshot_path"])),
        sequencer_set_hash=str(bootstrap_manifest["sequencer_set_hash"]),
        config_digest=str(bootstrap_manifest["config_digest"]),
        module_versions_digest=str(bootstrap_manifest["module_versions_digest"]),
    )
    _write_live_state(
        data_dir=data_dir,
        height=height,
        header_path=str(block_report["header_path"]),
        snapshot_path=str(block_report["post_snapshot_path"]),
        header_hash=str(block_report["header_hash"]),
        app_hash=str(block_report["app_hash"]),
    )
    report = {
        "schema": NODE_APPEND_REPORT_SCHEMA,
        "ok": True,
        "status": "accepted",
        "node_id": node_status["node_id"],
        "append_kind": "testnet_token_create",
        **block_report,
    }
    append_report_path = data_dir / "append_reports" / f"{height}.json"
    _write_json(append_report_path, report)
    return {**report, "append_report_path": str(append_report_path)}


def _live_artifact_path(*, data_dir: Path, kind: str, height: int) -> Path:
    if kind == "header":
        return data_dir / "live_ledger" / "headers" / f"{height}.json"
    if kind == "body":
        return data_dir / "live_ledger" / "bodies" / f"{height}.json"
    if kind == "checkpoint":
        return data_dir / "live_ledger" / "checkpoints" / f"{height}.json"
    if kind == "snapshot":
        return data_dir / "live_ledger" / "snapshots" / f"{height}.json"
    raise ValueError(f"unsupported live artifact kind: {kind}")


def pull_live_from_peer_v0(
    *,
    data_dir: Path,
    peer_url: str,
    peer_auth_token: str | None = None,
    live_quorum_registry: Mapping[str, Any] | None = None,
    live_quorum_envelopes_by_height: Mapping[int, Sequence[Mapping[str, Any]]] | None = None,
) -> dict[str, Any]:
    """Pull live blocks from a peer and accept only deterministic replays."""

    node_status = load_node_status_v0(data_dir)
    bundle_root = Path(str(node_status["bundle_root"]))
    base = _live_base_paths(bundle_root=bundle_root, data_dir=data_dir, node_status=node_status)
    local_latest = int(base["latest_height"])
    peer_check = check_peer_status_v0(data_dir=data_dir, peer_urls=[peer_url], peer_auth_token=peer_auth_token)
    peer_report = peer_check["peers"][0] if peer_check.get("peers") else None
    if peer_check.get("ok") is not True:
        return {
            "schema": NODE_PULL_REPORT_SCHEMA,
            "ok": False,
            "status": "rejected",
            "peer_url": peer_url,
            "pulled_count": 0,
            "local_latest_height": local_latest,
            "peer_latest_height": (
                dict(peer_report).get("peer_tip", {}).get("height")
                if isinstance(peer_report, Mapping)
                else None
            ),
            "reject_reason": "peer_check_rejected",
            "peer_check": peer_check,
        }
    peer_live = _fetch_json_url(urljoin(peer_url.rstrip("/") + "/", "live"), auth_token=peer_auth_token)
    if peer_live.get("ok") is not True or peer_live.get("live") is not True:
        return {
            "schema": NODE_PULL_REPORT_SCHEMA,
            "ok": True,
            "status": "accepted",
            "pulled_count": 0,
            "local_latest_height": local_latest,
            "peer_live": False,
            "peer_check": peer_check,
        }
    peer_state = peer_live.get("state")
    if not isinstance(peer_state, Mapping):
        raise ValueError("peer live state must be an object")
    peer_latest = int(peer_state["latest_height"])
    if peer_latest <= local_latest:
        return {
            "schema": NODE_PULL_REPORT_SCHEMA,
            "ok": True,
            "status": "accepted",
            "pulled_count": 0,
            "local_latest_height": local_latest,
            "peer_latest_height": peer_latest,
            "peer_check": peer_check,
        }

    quorum_admissions_by_height: dict[int, dict[str, Any]] = {}
    if live_quorum_registry is not None:
        for height in range(local_latest + 1, peer_latest + 1):
            envelopes = (
                dict(live_quorum_envelopes_by_height or {}).get(height)
                if live_quorum_envelopes_by_height is not None
                else None
            )
            if envelopes is None:
                return {
                    "schema": NODE_PULL_REPORT_SCHEMA,
                    "ok": False,
                    "status": "rejected",
                    "peer_url": peer_url,
                    "pulled_count": 0,
                    "local_latest_height": local_latest,
                    "peer_latest_height": peer_latest,
                    "reject_reason": "live_quorum_missing_envelopes",
                    "height": height,
                    "peer_check": peer_check,
                }
            try:
                peer_header = _fetch_json_url(
                    urljoin(peer_url.rstrip("/") + "/", f"live/header/{height}"),
                    auth_token=peer_auth_token,
                )
                peer_checkpoint = _fetch_json_url(
                    urljoin(peer_url.rstrip("/") + "/", f"live/checkpoint/{height}"),
                    auth_token=peer_auth_token,
                )
                quorum_admissions_by_height[height] = build_live_checkpoint_quorum_admission_v0(
                    header=peer_header,
                    checkpoint=peer_checkpoint,
                    registry=live_quorum_registry,
                    envelopes=envelopes,
                )
            except Exception as exc:
                return {
                    "schema": NODE_PULL_REPORT_SCHEMA,
                    "ok": False,
                    "status": "rejected",
                    "peer_url": peer_url,
                    "pulled_count": 0,
                    "local_latest_height": local_latest,
                    "peer_latest_height": peer_latest,
                    "reject_reason": "live_quorum_rejected",
                    "height": height,
                    "errors": [str(exc)],
                    "peer_check": peer_check,
                }

    public_manifest = _read_public_manifest(bundle_root)
    bootstrap_manifest = _load_json_object(bundle_root / "bootstrap" / "manifest.json")
    pulled: list[dict[str, Any]] = []
    quorum_admissions: list[dict[str, Any]] = []
    current_prev_header = Path(str(base["prev_header_path"]))
    current_pre_snapshot = Path(str(base["pre_snapshot_path"]))
    live_ledger_dir = data_dir / "live_ledger"
    for height in range(local_latest + 1, peer_latest + 1):
        peer_body = _fetch_json_url(
            urljoin(peer_url.rstrip("/") + "/", f"live/body/{height}"),
            auth_token=peer_auth_token,
        )
        peer_header = _fetch_json_url(
            urljoin(peer_url.rstrip("/") + "/", f"live/header/{height}"),
            auth_token=peer_auth_token,
        )
        if live_quorum_registry is not None:
            quorum_admissions.append(quorum_admissions_by_height[height])
        if _is_faucet_body_v0(peer_body):
            block_report = _build_faucet_block_from_body_v0(
                data_dir=data_dir,
                body=peer_body,
                time_ms=int(peer_header["time_ms"]),
                prev_header_path=current_prev_header,
                pre_snapshot_path=current_pre_snapshot,
                sequencer_set_hash=str(bootstrap_manifest["sequencer_set_hash"]),
                config_digest=str(bootstrap_manifest["config_digest"]),
                module_versions_digest=str(bootstrap_manifest["module_versions_digest"]),
            )
        elif _is_token_create_body_v0(peer_body):
            block_report = _build_token_create_block_from_body_v0(
                data_dir=data_dir,
                body=peer_body,
                time_ms=int(peer_header["time_ms"]),
                prev_header_path=current_prev_header,
                pre_snapshot_path=current_pre_snapshot,
                sequencer_set_hash=str(bootstrap_manifest["sequencer_set_hash"]),
                config_digest=str(bootstrap_manifest["config_digest"]),
                module_versions_digest=str(bootstrap_manifest["module_versions_digest"]),
            )
        else:
            body_path = data_dir / "pulled_bodies" / f"{height}.json"
            _write_json(body_path, peer_body)
            block_report = build_local_block_v0(
                body_path=body_path,
                out_dir=live_ledger_dir,
                time_ms=int(peer_header["time_ms"]),
                pre_snapshot_path=current_pre_snapshot,
                prev_header_path=current_prev_header,
                trusted_prev_header_hash=ZERO_ROOT,
                sequencer_set_hash=str(bootstrap_manifest["sequencer_set_hash"]),
                data_availability_root=ZERO_ROOT,
                proof_journal_hash=ZERO_ROOT,
                config_digest=str(bootstrap_manifest["config_digest"]),
                module_versions_digest=str(bootstrap_manifest["module_versions_digest"]),
                signature_set_root=ZERO_ROOT,
                allow_missing_settlement=True,
                require_intent_signatures=True,
                allow_unsigned_intents_if_tx_sender_matches=False,
            )
        local_header = _load_json_object(Path(str(block_report["header_path"])))
        if dict(local_header) != dict(peer_header):
            raise ValueError(f"peer header mismatch at height {height}")
        if canonical_header_hash_v0(dict(local_header)) != canonical_header_hash_v0(dict(peer_header)):
            raise ValueError(f"peer header hash mismatch at height {height}")
        current_prev_header = Path(str(block_report["header_path"]))
        current_pre_snapshot = Path(str(block_report["post_snapshot_path"]))
        pulled.append(
            {
                "height": height,
                "header_hash": block_report["header_hash"],
                "app_hash": block_report["app_hash"],
            }
        )

    last = pulled[-1]
    _write_live_state(
        data_dir=data_dir,
        height=int(last["height"]),
        header_path=str(current_prev_header),
        snapshot_path=str(current_pre_snapshot),
        header_hash=str(last["header_hash"]),
        app_hash=str(last["app_hash"]),
    )
    report = {
        "schema": NODE_PULL_REPORT_SCHEMA,
        "ok": True,
        "status": "accepted",
        "peer_url": peer_url,
        "network_id": public_manifest["network_id"],
        "chain_id": public_manifest["chain_id"],
        "from_height": local_latest + 1,
        "to_height": peer_latest,
        "pulled_count": len(pulled),
        "pulled": pulled,
        "local_latest_height": peer_latest,
        "live_quorum_required": live_quorum_registry is not None,
        "live_quorum_admissions": quorum_admissions,
        "peer_check": peer_check,
    }
    pull_report_path = data_dir / "pull_reports" / f"{peer_latest}.json"
    _write_json(pull_report_path, report)
    return {**report, "pull_report_path": str(pull_report_path)}


def poll_live_peers_once_v0(
    *,
    data_dir: Path,
    peer_urls: list[str],
    peer_auth_token: str | None = None,
    live_quorum_registry: Mapping[str, Any] | None = None,
    live_quorum_envelopes_by_height: Mapping[int, Sequence[Mapping[str, Any]]] | None = None,
) -> dict[str, Any]:
    """Poll all configured peers once and persist an operator-visible report."""

    status = load_node_status_v0(data_dir)
    peer_reports: list[dict[str, Any]] = []
    for peer_url in peer_urls:
        try:
            pull_report = pull_live_from_peer_v0(
                data_dir=data_dir,
                peer_url=peer_url,
                peer_auth_token=peer_auth_token,
                live_quorum_registry=live_quorum_registry,
                live_quorum_envelopes_by_height=live_quorum_envelopes_by_height,
            )
            peer_reports.append(
                {
                    "peer_url": peer_url,
                    "ok": pull_report.get("ok") is True,
                    "status": pull_report.get("status", "accepted"),
                    "pulled_count": pull_report.get("pulled_count", 0),
                    "local_latest_height": pull_report.get("local_latest_height"),
                    "peer_latest_height": pull_report.get("peer_latest_height", pull_report.get("to_height")),
                    "pull_report": pull_report,
                }
            )
        except Exception as exc:
            peer_reports.append(
                {
                    "peer_url": peer_url,
                    "ok": False,
                    "status": "rejected",
                    "error": str(exc),
                }
            )
    ok = all(report.get("ok") is True for report in peer_reports)
    latest_tip = _local_tip_v0(data_dir=data_dir, node_status=status)
    report = {
        "schema": NODE_PEER_FOLLOW_REPORT_SCHEMA,
        "ok": ok,
        "status": "accepted" if ok else "rejected",
        "node_id": status["node_id"],
        "network_id": status["network_id"],
        "chain_id": status["chain_id"],
        "peer_count": len(peer_urls),
        "local_tip": latest_tip,
        "peers": peer_reports,
    }
    _write_json(data_dir / "peer_follow_state.json", report)
    return report


def load_node_status_v0(data_dir: Path) -> dict[str, Any]:
    status = dict(_load_json_object(data_dir / "node_status.json"))
    if status.get("schema") != NODE_STATUS_SCHEMA:
        raise ValueError("node status schema mismatch")
    if status.get("node_status_hash") != _node_status_hash(status):
        raise ValueError("node status hash mismatch")
    return status


def _local_header_hash_at_height_v0(*, data_dir: Path, bundle_root: Path, height: int) -> str:
    live_header_path = _live_artifact_path(data_dir=data_dir, kind="header", height=height)
    if live_header_path.is_file():
        return canonical_header_hash_v0(dict(_load_json_object(live_header_path)))
    bootstrap_header_path = bundle_root / "bootstrap" / "ledger" / "headers" / f"{height}.json"
    if bootstrap_header_path.is_file():
        return canonical_header_hash_v0(dict(_load_json_object(bootstrap_header_path)))
    raise ValueError(f"local header missing at height {height}")


def _local_tip_v0(*, data_dir: Path, node_status: Mapping[str, Any]) -> dict[str, Any]:
    live_path = _latest_live_state_path(data_dir)
    if live_path.is_file():
        live_state = dict(_load_json_object(live_path))
        return {
            "live": True,
            "height": int(live_state["latest_height"]),
            "header_hash": str(live_state["latest_header_hash"]),
            "app_hash": str(live_state["latest_app_hash"]),
        }
    return {
        "live": False,
        "height": int(node_status["latest_height"]),
        "header_hash": str(node_status["last_header_hash"]),
        "app_hash": str(node_status["last_app_hash"]),
    }


def _peer_tip_from_http_v0(
    *,
    peer_url: str,
    peer_status: Mapping[str, Any],
    peer_auth_token: str | None = None,
) -> dict[str, Any]:
    peer_live = _fetch_json_url(urljoin(peer_url.rstrip("/") + "/", "live"), auth_token=peer_auth_token)
    if peer_live.get("ok") is True and peer_live.get("live") is True:
        state = peer_live.get("state")
        if not isinstance(state, Mapping):
            raise ValueError("peer live state must be an object")
        return {
            "live": True,
            "height": int(state["latest_height"]),
            "header_hash": str(state["latest_header_hash"]),
            "app_hash": str(state["latest_app_hash"]),
        }
    return {
        "live": False,
        "height": int(peer_status["latest_height"]),
        "header_hash": str(peer_status["last_header_hash"]),
        "app_hash": str(peer_status["last_app_hash"]),
    }


def _peer_header_hash_at_height_v0(
    *,
    peer_url: str,
    peer_status: Mapping[str, Any],
    height: int,
    peer_auth_token: str | None = None,
) -> str:
    bootstrap_latest = int(peer_status["latest_height"])
    if height == bootstrap_latest:
        return str(peer_status["last_header_hash"])
    if height > bootstrap_latest:
        peer_header = _fetch_json_url(
            urljoin(peer_url.rstrip("/") + "/", f"live/header/{height}"),
            auth_token=peer_auth_token,
        )
        return canonical_header_hash_v0(dict(peer_header))
    raise ValueError(f"cannot fetch peer bootstrap header at height {height}")


def _fork_choice_tip_v0(
    *,
    node_status: Mapping[str, Any],
    tip: Mapping[str, Any],
    name: str,
) -> dict[str, Any]:
    sequencer_set_hash = node_status.get("sequencer_set_hash")
    if not isinstance(sequencer_set_hash, str) or sequencer_set_hash == "":
        raise ValueError(f"{name} sequencer_set_hash is required")
    return {
        "chain_id": node_status["chain_id"],
        "height": int(tip["height"]),
        "header_hash": str(tip["header_hash"]),
        "validator_set_hash": sequencer_set_hash,
    }


def check_peer_status_v0(
    *,
    data_dir: Path,
    peer_urls: list[str],
    peer_auth_token: str | None = None,
) -> dict[str, Any]:
    """Check that peer nodes are on the same network and common live prefix."""

    node_status = load_node_status_v0(data_dir)
    bundle_root = Path(str(node_status["bundle_root"]))
    local_tip = _local_tip_v0(data_dir=data_dir, node_status=node_status)
    peer_reports: list[dict[str, Any]] = []
    for peer_url in peer_urls:
        try:
            peer_status = _fetch_json_url(
                urljoin(peer_url.rstrip("/") + "/", "status"),
                auth_token=peer_auth_token,
            )
            if peer_status.get("schema") != NODE_STATUS_SCHEMA:
                raise ValueError("peer node status schema mismatch")
            if peer_status.get("node_status_hash") != _node_status_hash(peer_status):
                raise ValueError("peer node status hash mismatch")
            peer_tip = _peer_tip_from_http_v0(
                peer_url=peer_url,
                peer_status=peer_status,
                peer_auth_token=peer_auth_token,
            )
            network_match = peer_status.get("network_id") == node_status.get("network_id")
            chain_match = peer_status.get("chain_id") == node_status.get("chain_id")
            feature_suite_match = peer_status.get("feature_suite_hash") == node_status.get("feature_suite_hash")
            common_height = min(int(local_tip["height"]), int(peer_tip["height"]))
            if common_height == int(local_tip["height"]):
                local_common_hash = str(local_tip["header_hash"])
            else:
                local_common_hash = _local_header_hash_at_height_v0(
                    data_dir=data_dir,
                    bundle_root=bundle_root,
                    height=common_height,
                )
            peer_common_hash = _peer_header_hash_at_height_v0(
                peer_url=peer_url,
                peer_status=peer_status,
                height=common_height,
                peer_auth_token=peer_auth_token,
            )
            common_header_match = local_common_hash == peer_common_hash
            fork_choice_report = build_fork_choice_report_v0(
                local_tip=_fork_choice_tip_v0(
                    node_status=node_status,
                    tip=local_tip,
                    name="local_tip",
                ),
                candidate_tip=_fork_choice_tip_v0(
                    node_status=peer_status,
                    tip=peer_tip,
                    name="peer_tip",
                ),
                common_height=common_height,
                local_common_header_hash=local_common_hash,
                candidate_common_header_hash=peer_common_hash,
            )
            fork_choice_compatible = fork_choice_report["decision"] in {
                "follow_candidate",
                "same_tip",
                "keep_local",
            }
            compatible = bool(network_match and chain_match and feature_suite_match and fork_choice_compatible)
            if int(peer_tip["height"]) > int(local_tip["height"]):
                relation = "peer_ahead"
            elif int(peer_tip["height"]) < int(local_tip["height"]):
                relation = "peer_behind"
            else:
                relation = "same_height"
            peer_reports.append(
                {
                    "peer_url": peer_url,
                    "ok": compatible,
                    "status": "accepted" if compatible else "rejected",
                    "peer_node_id": peer_status.get("node_id"),
                    "network_match": network_match,
                    "chain_match": chain_match,
                    "feature_suite_match": feature_suite_match,
                    "common_header_match": common_header_match,
                    "fork_choice_compatible": fork_choice_compatible,
                    "fork_choice": fork_choice_report,
                    "height_relation": relation,
                    "local_tip": local_tip,
                    "peer_tip": peer_tip,
                    "common_height": common_height,
                    "common_header_hash": local_common_hash if common_header_match else None,
                    "local_common_header_hash": local_common_hash,
                    "peer_common_header_hash": peer_common_hash,
                }
            )
        except Exception as exc:
            peer_reports.append(
                {
                    "peer_url": peer_url,
                    "ok": False,
                    "status": "rejected",
                    "error": str(exc),
                    "local_tip": local_tip,
                }
            )
    ok = all(report.get("ok") is True for report in peer_reports)
    return {
        "schema": NODE_PEER_CHECK_REPORT_SCHEMA,
        "ok": ok,
        "status": "accepted" if ok else "rejected",
        "node_id": node_status["node_id"],
        "network_id": node_status["network_id"],
        "chain_id": node_status["chain_id"],
        "feature_suite_hash": node_status["feature_suite_hash"],
        "local_tip": local_tip,
        "peer_count": len(peer_reports),
        "peers": peer_reports,
    }


def build_node_evidence_report_v0(
    *,
    data_dir: Path,
    peer_urls: list[str] | None = None,
    peer_auth_token: str | None = None,
) -> dict[str, Any]:
    """Build a compact operator evidence report for a joined node."""

    status = load_node_status_v0(data_dir)
    token_registry = _load_testnet_token_registry_v0(data_dir)
    local_tip = _local_tip_v0(data_dir=data_dir, node_status=status)
    peer_check = (
        check_peer_status_v0(data_dir=data_dir, peer_urls=list(peer_urls or []), peer_auth_token=peer_auth_token)
        if peer_urls
        else None
    )
    ok = (
        status.get("ok") is True
        and status.get("covered_feature_count") == len(status.get("required_features", []))
        and (peer_check is None or peer_check.get("ok") is True)
    )
    return {
        "schema": NODE_EVIDENCE_REPORT_SCHEMA,
        "ok": ok,
        "status": "accepted" if ok else "rejected",
        "node_id": status["node_id"],
        "network_id": status["network_id"],
        "chain_id": status["chain_id"],
        "node_status_hash": status["node_status_hash"],
        "feature_suite_hash": status["feature_suite_hash"],
        "covered_feature_count": status["covered_feature_count"],
        "required_features": status["required_features"],
        "local_tip": local_tip,
        "testnet_token_catalog": status["test_token_catalog"],
        "created_test_token_count": len(token_registry["tokens"]),
        "created_test_tokens": token_registry["tokens"],
        "testnet_token_registry_hash": token_registry["token_registry_hash"],
        "peer_check": peer_check,
    }


def _load_optional_json(path_text: object) -> object | None:
    if not isinstance(path_text, str) or path_text == "":
        return None
    path = Path(path_text)
    if not path.is_file():
        return None
    return _load_json_object(path)


def make_node_http_server_v0(
    *,
    data_dir: Path,
    host: str,
    port: int,
    enable_testnet_intake: bool = False,
    enable_testnet_faucet: bool = False,
    submit_peer_url: str | None = None,
    node_auth_token: str | None = None,
    submit_peer_auth_token: str | None = None,
    peer_urls: list[str] | None = None,
    poll_seconds: int = 0,
) -> ThreadingHTTPServer:
    """Create a small read-only HTTP server for node status artifacts."""

    root = data_dir.resolve()
    append_lock = threading.Lock()
    required_auth = (
        _normalize_transport_auth_token_v0(node_auth_token, name="node_auth_token")
        if node_auth_token is not None
        else None
    )
    submit_auth = (
        _normalize_transport_auth_token_v0(submit_peer_auth_token, name="submit_peer_auth_token")
        if submit_peer_auth_token is not None
        else None
    )

    class Handler(BaseHTTPRequestHandler):
        server_version = "ZenoLedgerNode/0"

        def _send_json(self, value: object, *, status: HTTPStatus = HTTPStatus.OK) -> None:
            payload = json.dumps(value, indent=2, sort_keys=True).encode("utf-8") + b"\n"
            self.send_response(int(status))
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(payload)))
            self.end_headers()
            self.wfile.write(payload)

        def _authorized(self) -> bool:
            if required_auth is None:
                return True
            expected = f"Bearer {required_auth}"
            return hmac.compare_digest(self.headers.get("Authorization", ""), expected)

        def _require_authorized(self) -> bool:
            if self._authorized():
                return True
            self._send_json(
                {
                    "ok": False,
                    "error": "node_transport_auth_required",
                    "auth_scheme": "bearer",
                },
                status=HTTPStatus.UNAUTHORIZED,
            )
            return False

        def do_GET(self) -> None:  # noqa: N802
            try:
                if not self._require_authorized():
                    return
                status = load_node_status_v0(root)
                parts = [part for part in self.path.split("?", 1)[0].split("/") if part]
                if len(parts) == 3 and parts[0] == "live" and parts[1] in {"header", "body", "checkpoint", "snapshot"}:
                    try:
                        height = int(parts[2])
                    except ValueError:
                        self._send_json({"ok": False, "error": "invalid_height"}, status=HTTPStatus.BAD_REQUEST)
                        return
                    artifact_path = _live_artifact_path(data_dir=root, kind=parts[1], height=height)
                    if not artifact_path.is_file():
                        self._send_json({"ok": False, "error": "live_artifact_missing"}, status=HTTPStatus.NOT_FOUND)
                    else:
                        self._send_json(_load_json_object(artifact_path))
                    return
                if self.path in {"/", "/health"}:
                    self._send_json(
                        {
                            "ok": status["ok"],
                            "node_id": status["node_id"],
                            "node_status_hash": status["node_status_hash"],
                            "latest_height": status["latest_height"],
                        }
                    )
                    return
                if self.path == "/status":
                    self._send_json(status)
                    return
                if self.path == "/features":
                    self._send_json(
                        {
                            "feature_suite_hash": status["feature_suite_hash"],
                            "covered_feature_count": status["covered_feature_count"],
                            "covered_features": status["covered_features"],
                            "required_features": status["required_features"],
                        }
                    )
                    return
                if self.path == "/tokens":
                    registry = _load_testnet_token_registry_v0(root)
                    self._send_json(
                        {
                            "token_symbol": status["token_symbol"],
                            "token_posture": status["token_posture"],
                            "test_token_catalog": status["test_token_catalog"],
                            "testnet_faucet_posture": status["testnet_faucet_posture"],
                            "created_test_tokens": registry["tokens"],
                            "created_test_token_count": len(registry["tokens"]),
                            "testnet_token_registry_hash": registry["token_registry_hash"],
                        }
                    )
                    return
                if self.path == "/network":
                    self._send_json(
                        {
                            "schema": "zenodex.zeno_ledger.node_network_status.v0",
                            "ok": status["ok"],
                            "node_id": status["node_id"],
                            "node_role": status["node_role"],
                            "network_id": status["network_id"],
                            "chain_id": status["chain_id"],
                            "bootstrap_latest_height": status["latest_height"],
                            "local_tip": _local_tip_v0(data_dir=root, node_status=status),
                            "peer_urls": list(peer_urls or []),
                            "peer_count": len(peer_urls or []),
                            "submit_peer_url": submit_peer_url,
                            "peer_follow": {
                                "enabled": bool(peer_urls) and poll_seconds > 0,
                                "poll_seconds": poll_seconds,
                                "state_path": str(root / "peer_follow_state.json"),
                            },
                            "capabilities": {
                                "transport_auth_required": required_auth is not None,
                                "testnet_intake_enabled": enable_testnet_intake,
                                "testnet_faucet_enabled": enable_testnet_faucet,
                                "submission_forwarding_enabled": submit_peer_url is not None,
                                "peer_follow_enabled": bool(peer_urls) and poll_seconds > 0,
                            },
                        }
                    )
                    return
                if self.path == "/follow":
                    follow_path = root / "peer_follow_state.json"
                    if not follow_path.is_file():
                        self._send_json(
                            {
                                "ok": True,
                                "live": False,
                                "peer_count": len(peer_urls or []),
                                "poll_seconds": poll_seconds,
                            }
                        )
                    else:
                        self._send_json(_load_json_object(follow_path))
                    return
                if self.path == "/live":
                    live_path = root / "live_state.json"
                    if not live_path.is_file():
                        self._send_json({"ok": True, "live": False})
                    else:
                        self._send_json({"ok": True, "live": True, "state": _load_json_object(live_path)})
                    return
                if self.path == "/attestation":
                    attestation = _load_optional_json(status.get("operator_attestation_path"))
                    if attestation is None:
                        self._send_json({"ok": False, "error": "attestation_missing"}, status=HTTPStatus.NOT_FOUND)
                    else:
                        self._send_json(attestation)
                    return
                if self.path == "/testnet-status":
                    testnet_status = _load_optional_json(status.get("combined_testnet_status_path"))
                    if testnet_status is None:
                        self._send_json({"ok": False, "error": "testnet_status_missing"}, status=HTTPStatus.NOT_FOUND)
                    else:
                        self._send_json(testnet_status)
                    return
                self._send_json({"ok": False, "error": "not_found"}, status=HTTPStatus.NOT_FOUND)
            except Exception as exc:
                self._send_json({"ok": False, "error": str(exc)}, status=HTTPStatus.INTERNAL_SERVER_ERROR)

        def do_POST(self) -> None:  # noqa: N802
            try:
                if not self._require_authorized():
                    return
                if self.path == "/tx":
                    if not enable_testnet_intake:
                        self._send_json({"ok": False, "error": "testnet_intake_disabled"}, status=HTTPStatus.FORBIDDEN)
                        return
                    payload = _read_http_json_body(self)
                    if submit_peer_url:
                        report, peer_status = _post_json_url(
                            urljoin(submit_peer_url.rstrip("/") + "/", "tx"),
                            payload,
                            auth_token=submit_auth,
                        )
                        self._send_json({**report, "forwarded_to": submit_peer_url}, status=peer_status)
                        return
                    tx_raw = payload.get("tx", payload)
                    if not isinstance(tx_raw, Mapping):
                        self._send_json({"ok": False, "error": "tx_must_be_object"}, status=HTTPStatus.BAD_REQUEST)
                        return
                    time_ms = payload.get("time_ms")
                    if time_ms is None:
                        time_ms = int(time.time() * 1000)
                    if not isinstance(time_ms, int) or isinstance(time_ms, bool) or time_ms < 0:
                        self._send_json({"ok": False, "error": "time_ms_must_be_nonnegative_int"}, status=HTTPStatus.BAD_REQUEST)
                        return
                    with append_lock:
                        report = append_dex_transaction_v0(data_dir=root, tx=tx_raw, time_ms=int(time_ms))
                    self._send_json(report, status=HTTPStatus.OK if report["ok"] else HTTPStatus.BAD_REQUEST)
                    return
                if self.path == "/faucet":
                    if not enable_testnet_faucet:
                        self._send_json({"ok": False, "error": "testnet_faucet_disabled"}, status=HTTPStatus.FORBIDDEN)
                        return
                    payload = _read_http_json_body(self)
                    if submit_peer_url:
                        report, peer_status = _post_json_url(
                            urljoin(submit_peer_url.rstrip("/") + "/", "faucet"),
                            payload,
                            auth_token=submit_auth,
                        )
                        self._send_json({**report, "forwarded_to": submit_peer_url}, status=peer_status)
                        return
                    time_ms = payload.get("time_ms")
                    if time_ms is None:
                        time_ms = int(time.time() * 1000)
                    if not isinstance(time_ms, int) or isinstance(time_ms, bool) or time_ms < 0:
                        self._send_json({"ok": False, "error": "time_ms_must_be_nonnegative_int"}, status=HTTPStatus.BAD_REQUEST)
                        return
                    with append_lock:
                        report = append_testnet_faucet_v0(
                            data_dir=root,
                            to_pubkey=str(payload.get("to_pubkey", "")),
                            asset=str(payload.get("asset", "")),
                            amount=payload.get("amount"),
                            tx_id=str(payload.get("tx_id", "node-testnet-faucet-v0")),
                            time_ms=int(time_ms),
                        )
                    self._send_json(report)
                    return
                if self.path == "/tokens":
                    if not enable_testnet_faucet:
                        self._send_json({"ok": False, "error": "testnet_token_create_disabled"}, status=HTTPStatus.FORBIDDEN)
                        return
                    payload = _read_http_json_body(self)
                    if submit_peer_url:
                        report, peer_status = _post_json_url(
                            urljoin(submit_peer_url.rstrip("/") + "/", "tokens"),
                            payload,
                            auth_token=submit_auth,
                        )
                        self._send_json({**report, "forwarded_to": submit_peer_url}, status=peer_status)
                        return
                    time_ms = payload.get("time_ms")
                    if time_ms is None:
                        time_ms = int(time.time() * 1000)
                    if not isinstance(time_ms, int) or isinstance(time_ms, bool) or time_ms < 0:
                        self._send_json({"ok": False, "error": "time_ms_must_be_nonnegative_int"}, status=HTTPStatus.BAD_REQUEST)
                        return
                    asset = payload.get("asset")
                    with append_lock:
                        report = append_testnet_token_create_v0(
                            data_dir=root,
                            symbol=str(payload.get("symbol", "")),
                            name=str(payload.get("name", "")),
                            decimals=payload.get("decimals"),
                            creator_pubkey=str(payload.get("creator_pubkey", "")),
                            asset=str(asset) if asset is not None else None,
                            salt=str(payload.get("salt", "default")),
                            tx_id=str(payload.get("tx_id", "node-testnet-token-create-v0")),
                            time_ms=int(time_ms),
                        )
                    self._send_json(report)
                    return
                self._send_json({"ok": False, "error": "not_found"}, status=HTTPStatus.NOT_FOUND)
            except Exception as exc:
                self._send_json({"ok": False, "error": str(exc)}, status=HTTPStatus.BAD_REQUEST)

        def log_message(self, format: str, *args: object) -> None:
            return

    return ThreadingHTTPServer((host, port), Handler)


def _start_peer_follow_loop(
    *,
    data_dir: Path,
    peer_urls: list[str],
    poll_seconds: int,
    peer_auth_token: str | None = None,
) -> threading.Thread | None:
    if not peer_urls or poll_seconds <= 0:
        return None

    def _loop() -> None:
        while True:
            poll_live_peers_once_v0(
                data_dir=data_dir,
                peer_urls=peer_urls,
                peer_auth_token=peer_auth_token,
            )
            time.sleep(poll_seconds)

    thread = threading.Thread(target=_loop, daemon=True)
    thread.start()
    return thread


def serve_node_v0(
    *,
    data_dir: Path,
    host: str,
    port: int,
    peer_urls: list[str] | None = None,
    poll_seconds: int = 0,
    enable_testnet_intake: bool = False,
    enable_testnet_faucet: bool = False,
    submit_peer_url: str | None = None,
    peer_auth_token: str | None = None,
    node_auth_token: str | None = None,
    submit_peer_auth_token: str | None = None,
) -> None:
    _start_peer_follow_loop(
        data_dir=data_dir,
        peer_urls=list(peer_urls or []),
        poll_seconds=poll_seconds,
        peer_auth_token=peer_auth_token,
    )
    server = make_node_http_server_v0(
        data_dir=data_dir,
        host=host,
        port=port,
        enable_testnet_intake=enable_testnet_intake,
        enable_testnet_faucet=enable_testnet_faucet,
        submit_peer_url=submit_peer_url,
        node_auth_token=node_auth_token,
        submit_peer_auth_token=submit_peer_auth_token,
        peer_urls=list(peer_urls or []),
        poll_seconds=poll_seconds,
    )
    address, actual_port = server.server_address
    print(
        json.dumps(
            {
                "schema": "zenodex.zeno_ledger.node_server_ready.v0",
                "ok": True,
                "host": address,
                "port": actual_port,
                "peer_count": len(peer_urls or []),
                "poll_seconds": poll_seconds,
                "testnet_intake_enabled": enable_testnet_intake,
                "testnet_faucet_enabled": enable_testnet_faucet,
                "transport_auth_required": node_auth_token is not None,
                "submit_peer_url": submit_peer_url,
                "status_url": f"http://{address}:{actual_port}/status",
            },
            indent=2,
            sort_keys=True,
        ),
        flush=True,
    )
    server.serve_forever()


def join_public_node_from_config_v0(
    *,
    config_path: Path,
    peer_auth_token: str | None = None,
) -> dict[str, Any]:
    """Sync, verify, and optionally serve a node from one operator config."""

    config = dict(_load_json_object(config_path))
    if config.get("schema") not in {None, NODE_JOIN_CONFIG_SCHEMA}:
        raise ValueError("node join config schema mismatch")
    node_id = str(config.get("node_id", "")).strip()
    if node_id == "":
        raise ValueError("node_id is required")
    data_dir = _as_path(config.get("data_dir"), name="data_dir")
    bundle_root: Path
    sync_report: dict[str, Any] | None = None
    base_url = config.get("base_url")
    if base_url is not None:
        if not isinstance(base_url, str) or base_url == "":
            raise ValueError("base_url must be a non-empty string")
        bundle_root = _as_path(config.get("bundle_root"), name="bundle_root")
        sync_report = sync_public_bundle_from_url_v0(base_url=base_url, out_dir=bundle_root)
    else:
        bundle_root = _as_path(config.get("bundle_root"), name="bundle_root")
        _read_public_manifest(bundle_root)

    peer_watcher_attestations = _as_path_list(
        config.get("peer_watcher_attestation_paths"),
        name="peer_watcher_attestation_paths",
    )
    if not peer_watcher_attestations:
        default_attestation = bundle_root / "bootstrap" / "watcher_attestations" / "bootstrap_range_1_5.json"
        if default_attestation.is_file():
            peer_watcher_attestations = [default_attestation]

    observed_time_ms = config.get("observed_time_ms")
    if observed_time_ms is not None and (not isinstance(observed_time_ms, int) or isinstance(observed_time_ms, bool)):
        raise ValueError("observed_time_ms must be an integer")
    run_report = run_node_once_v0(
        bundle_root=bundle_root,
        node_id=node_id,
        data_dir=data_dir,
        observed_time_ms=observed_time_ms,
        peer_watcher_attestation_paths=peer_watcher_attestations,
    )
    local_peer_auth_token = peer_auth_token
    if local_peer_auth_token is None and config.get("peer_auth_token_file") is not None:
        local_peer_auth_token = _read_transport_auth_token_file_v0(
            _as_path(config.get("peer_auth_token_file"), name="peer_auth_token_file")
        )
    peer_urls = _as_string_list(config.get("peer_urls"), name="peer_urls")
    peer_check = (
        check_peer_status_v0(data_dir=data_dir, peer_urls=peer_urls, peer_auth_token=local_peer_auth_token)
        if peer_urls
        else None
    )
    ok = (
        run_report.get("ok") is True
        and (sync_report is None or sync_report.get("ok") is True)
        and (peer_check is None or peer_check.get("ok") is True)
    )
    report = {
        "schema": NODE_JOIN_REPORT_SCHEMA,
        "ok": ok,
        "status": "accepted",
        "config_path": str(config_path),
        "node_id": node_id,
        "bundle_root": str(bundle_root),
        "data_dir": str(data_dir),
        "submit_peer_url": config.get("submit_peer_url"),
        "sync_report": sync_report,
        "run_report": run_report,
        "peer_check": peer_check,
        "peer_count": len(peer_urls),
    }
    if peer_check is not None and peer_check.get("ok") is not True:
        report["status"] = "peer_check_rejected"
    elif report["ok"] is True:
        report["status"] = "accepted"
    else:
        report["status"] = "rejected"
    _write_json(data_dir / "node_join_report.json", report)
    return report


def build_public_network_config_v0(
    *,
    bundle_root: Path,
    mirror_base_url: str,
    writer_urls: list[str],
    peer_urls: list[str],
    poll_seconds: int,
    node_port: int,
    enable_testnet_intake: bool = True,
    enable_testnet_faucet: bool = True,
) -> dict[str, Any]:
    """Build a public operator config for joining a ZenoLedger testnet."""

    if not writer_urls:
        raise ValueError("at least one writer URL is required")
    if poll_seconds < 0:
        raise ValueError("poll_seconds must be nonnegative")
    if node_port <= 0 or node_port > 65535:
        raise ValueError("node_port must be a valid TCP port")
    public_manifest = _read_public_manifest(bundle_root)
    feature_suite = _read_feature_suite(bundle_root, public_manifest)
    config = {
        "schema": NODE_PUBLIC_NETWORK_CONFIG_SCHEMA,
        "ok": True,
        "status": "accepted",
        "network_id": public_manifest["network_id"],
        "chain_id": public_manifest["chain_id"],
        "token_symbol": public_manifest.get("token_symbol"),
        "mirror_base_url": mirror_base_url.rstrip("/") + "/",
        "writer_urls": _unique_strings(writer_urls),
        "peer_urls": _unique_strings([*writer_urls, *peer_urls]),
        "feature_suite_hash": feature_suite["feature_suite_hash"],
        "feature_count": feature_suite["feature_count"],
        "test_token_catalog": list(public_manifest.get("test_token_catalog", [])),
        "testnet_faucet_posture": dict(public_manifest.get("testnet_faucet_posture", {})),
        "recommended_node": {
            "host": "0.0.0.0",
            "port": node_port,
            "poll_seconds": poll_seconds,
            "enable_testnet_intake": enable_testnet_intake,
            "enable_testnet_faucet": enable_testnet_faucet,
            "submit_peer_url": writer_urls[0],
        },
    }
    return {**config, "network_config_hash": _public_network_config_hash_v0(config)}


def _public_network_config_to_join_config_v0(
    *,
    network_config: Mapping[str, Any],
    node_id: str,
    bundle_root: Path,
    data_dir: Path,
    host: str,
    port: int | None,
    poll_seconds: int | None,
    serve: bool,
    require_network_config_quorum: bool = False,
    expected_config_signer_registry_hash: str | None = None,
) -> dict[str, Any]:
    if network_config.get("schema") != NODE_PUBLIC_NETWORK_CONFIG_SCHEMA:
        raise ValueError("public network config schema mismatch")
    expected_hash = network_config.get("network_config_hash")
    if expected_hash is not None and expected_hash != _public_network_config_hash_v0(network_config):
        raise ValueError("public network config hash mismatch")
    config_quorum_admission: dict[str, Any] | None = None
    if require_network_config_quorum or expected_config_signer_registry_hash is not None:
        if not _has_public_network_config_quorum_fields_v0(network_config):
            raise ValueError("public network config quorum is required")
    if require_network_config_quorum or expected_config_signer_registry_hash is not None or _has_public_network_config_quorum_fields_v0(network_config):
        config_quorum_admission = validate_public_network_config_quorum_v0(
            network_config=network_config,
            expected_config_signer_registry_hash=expected_config_signer_registry_hash,
        )
    writer_urls = _as_string_list(network_config.get("writer_urls"), name="writer_urls")
    peer_urls = _as_string_list(network_config.get("peer_urls"), name="peer_urls")
    if not writer_urls:
        raise ValueError("public network config must contain at least one writer URL")
    recommended = network_config.get("recommended_node")
    if not isinstance(recommended, Mapping):
        recommended = {}
    effective_port = port if port is not None else int(recommended.get("port", 8788))
    effective_poll = poll_seconds if poll_seconds is not None else int(recommended.get("poll_seconds", 5))
    return {
        "schema": NODE_JOIN_CONFIG_SCHEMA,
        "base_url": str(network_config["mirror_base_url"]),
        "bundle_root": str(bundle_root),
        "node_id": node_id,
        "data_dir": str(data_dir),
        "peer_urls": _unique_strings([*writer_urls, *peer_urls]),
        "serve": serve,
        "host": host or str(recommended.get("host", "0.0.0.0")),
        "port": effective_port,
        "poll_seconds": effective_poll,
        "enable_testnet_intake": bool(recommended.get("enable_testnet_intake", True)),
        "enable_testnet_faucet": bool(recommended.get("enable_testnet_faucet", True)),
        "submit_peer_url": str(recommended.get("submit_peer_url", writer_urls[0])),
        "network_config_quorum_required": require_network_config_quorum,
        "network_config_quorum_admission": config_quorum_admission,
    }


def doctor_public_node_v0(
    *,
    config_url: str | None = None,
    expected_network_config_hash: str | None = None,
    require_network_config_quorum: bool = False,
    expected_config_signer_registry_hash: str | None = None,
) -> dict[str, Any]:
    """Check local and optional remote prerequisites before joining a testnet."""

    checks: list[dict[str, Any]] = []
    python_ok = sys.version_info >= (3, 10)
    checks.append(
        {
            "name": "python_version",
            "ok": python_ok,
            "value": f"{sys.version_info.major}.{sys.version_info.minor}.{sys.version_info.micro}",
            "minimum": "3.10",
        }
    )
    repo_files = [
        ROOT / "tools" / "zeno_ledger_node.py",
        ROOT / "tools" / "zeno_ledger_make_public_testnet_bundle.py",
        ROOT / "src" / "integration" / "zeno_ledger_v0.py",
    ]
    repo_ok = all(path.is_file() for path in repo_files)
    checks.append(
        {
            "name": "repo_layout",
            "ok": repo_ok,
            "root": str(ROOT),
            "required_files": [str(path.relative_to(ROOT)) for path in repo_files],
        }
    )
    remote_summary: dict[str, Any] | None = None
    if config_url is not None:
        try:
            network_config = _fetch_json_url(config_url)
            if network_config.get("schema") != NODE_PUBLIC_NETWORK_CONFIG_SCHEMA:
                raise ValueError("public network config schema mismatch")
            expected_hash = network_config.get("network_config_hash")
            actual_hash = _public_network_config_hash_v0(network_config)
            if expected_hash != actual_hash:
                raise ValueError("public network config hash mismatch")
            if expected_network_config_hash is not None:
                pinned_hash = _require_root_v0(
                    expected_network_config_hash,
                    name="expected_network_config_hash",
                )
                if actual_hash != pinned_hash:
                    raise ValueError("public network config hash did not match expected hash")
            config_quorum_admission: dict[str, Any] | None = None
            if require_network_config_quorum or expected_config_signer_registry_hash is not None:
                if not _has_public_network_config_quorum_fields_v0(network_config):
                    raise ValueError("public network config quorum is required")
            if (
                require_network_config_quorum
                or expected_config_signer_registry_hash is not None
                or _has_public_network_config_quorum_fields_v0(network_config)
            ):
                config_quorum_admission = validate_public_network_config_quorum_v0(
                    network_config=network_config,
                    expected_config_signer_registry_hash=expected_config_signer_registry_hash,
                )
            writer_urls = _as_string_list(network_config.get("writer_urls"), name="writer_urls")
            peer_urls = _as_string_list(network_config.get("peer_urls"), name="peer_urls")
            if not writer_urls:
                raise ValueError("public network config must contain at least one writer URL")
            remote_summary = {
                "network_id": network_config.get("network_id"),
                "chain_id": network_config.get("chain_id"),
                "network_config_hash": actual_hash,
                "mirror_base_url": network_config.get("mirror_base_url"),
                "writer_urls": writer_urls,
                "peer_urls": peer_urls,
                "feature_suite_hash": network_config.get("feature_suite_hash"),
                "feature_count": network_config.get("feature_count"),
                "network_config_quorum_required": require_network_config_quorum,
                "network_config_quorum_admission": config_quorum_admission,
            }
            checks.append({"name": "public_network_config", "ok": True, **remote_summary})
        except Exception as exc:
            checks.append(
                {
                    "name": "public_network_config",
                    "ok": False,
                    "config_url": config_url,
                    "error": str(exc),
                }
            )
    ok = all(check.get("ok") is True for check in checks)
    return {
        "schema": NODE_DOCTOR_REPORT_SCHEMA,
        "ok": ok,
        "status": "accepted" if ok else "rejected",
        "root": str(ROOT),
        "config_url": config_url,
        "expected_network_config_hash": expected_network_config_hash,
        "require_network_config_quorum": require_network_config_quorum,
        "expected_config_signer_registry_hash": expected_config_signer_registry_hash,
        "checks": checks,
        "remote_network": remote_summary,
    }


def join_public_node_from_network_config_url_v0(
    *,
    config_url: str,
    node_id: str,
    bundle_root: Path,
    data_dir: Path,
    host: str,
    port: int | None,
    poll_seconds: int | None,
    serve: bool,
    expected_network_config_hash: str | None = None,
    require_network_config_quorum: bool = False,
    expected_config_signer_registry_hash: str | None = None,
    peer_auth_token: str | None = None,
) -> dict[str, Any]:
    """Join a public ZenoLedger testnet from one published network config URL."""

    network_config = _fetch_json_url(config_url)
    if expected_network_config_hash is not None:
        expected_hash = _require_root_v0(expected_network_config_hash, name="expected_network_config_hash")
        actual_hash = network_config.get("network_config_hash")
        if actual_hash != expected_hash:
            raise ValueError("public network config hash did not match expected hash")
    join_config = _public_network_config_to_join_config_v0(
        network_config=network_config,
        node_id=node_id,
        bundle_root=bundle_root,
        data_dir=data_dir,
        host=host,
        port=port,
        poll_seconds=poll_seconds,
        serve=serve,
        require_network_config_quorum=require_network_config_quorum,
        expected_config_signer_registry_hash=expected_config_signer_registry_hash,
    )
    data_dir.mkdir(parents=True, exist_ok=True)
    network_config_path = data_dir / "public_network_config.json"
    join_config_path = data_dir / "node_join_config.json"
    _write_json(network_config_path, network_config)
    _write_json(join_config_path, join_config)
    report = join_public_node_from_config_v0(
        config_path=join_config_path,
        peer_auth_token=peer_auth_token,
    )
    report["network_config_url"] = config_url
    report["network_config_path"] = str(network_config_path)
    report["network_config_hash"] = network_config.get("network_config_hash")
    report["expected_network_config_hash"] = expected_network_config_hash
    report["network_config_quorum_required"] = require_network_config_quorum
    report["network_config_quorum_admission"] = join_config.get("network_config_quorum_admission")
    report["expected_config_signer_registry_hash"] = expected_config_signer_registry_hash
    return report


def _cmd_bootstrap(args: argparse.Namespace) -> int:
    try:
        report = build_public_testnet_bundle_v0(
            out_dir=args.out_dir,
            network_id=args.network_id,
            chain_id=args.chain_id,
            sequencer_id=args.sequencer_id,
            time_ms=args.time_ms,
            token_symbol=args.token_symbol,
        )
    except Exception as exc:
        report = {"schema": NODE_REPORT_SCHEMA, "ok": False, "status": "rejected", "errors": [str(exc)]}
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report.get("ok") is True else 1


def _cmd_sync(args: argparse.Namespace) -> int:
    try:
        report = sync_public_bundle_from_url_v0(
            base_url=args.base_url,
            out_dir=args.out_dir,
        )
    except Exception as exc:
        report = {"schema": NODE_SYNC_REPORT_SCHEMA, "ok": False, "status": "rejected", "errors": [str(exc)]}
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report.get("ok") is True else 1


def _cmd_write_network_config(args: argparse.Namespace) -> int:
    try:
        report = build_public_network_config_v0(
            bundle_root=args.bundle_root,
            mirror_base_url=args.mirror_base_url,
            writer_urls=list(args.writer_url),
            peer_urls=list(args.peer_url),
            poll_seconds=args.poll_seconds,
            node_port=args.node_port,
        )
        if args.config_signature_envelope and args.config_signer_registry is None:
            raise ValueError("config signer registry is required when config signature envelopes are supplied")
        if args.config_signer_registry is not None:
            report = attach_public_network_config_quorum_v0(
                network_config=report,
                registry=_load_json_object(args.config_signer_registry),
                envelopes=[
                    _load_json_object(path)
                    for path in args.config_signature_envelope
                ],
            )
        _write_json(args.out, report)
        report = {**report, "config_path": str(args.out)}
    except Exception as exc:
        report = {"schema": NODE_PUBLIC_NETWORK_CONFIG_SCHEMA, "ok": False, "status": "rejected", "errors": [str(exc)]}
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if "errors" not in report else 1


def _cmd_run(args: argparse.Namespace) -> int:
    try:
        report = run_node_once_v0(
            bundle_root=args.bundle_root,
            node_id=args.node_id,
            data_dir=args.data_dir,
            observed_time_ms=args.observed_time_ms,
            peer_watcher_attestation_paths=list(args.peer_watcher_attestation),
        )
    except Exception as exc:
        report = {"schema": NODE_REPORT_SCHEMA, "ok": False, "status": "rejected", "errors": [str(exc)]}
    print(json.dumps(report, indent=2, sort_keys=True))
    if report.get("ok") is not True:
        return 1
    if args.serve:
        peer_auth_token = _read_transport_auth_token_file_v0(args.peer_auth_token_file)
        node_auth_token = _read_transport_auth_token_file_v0(args.node_auth_token_file)
        submit_peer_auth_token = _read_transport_auth_token_file_v0(args.submit_peer_auth_token_file)
        serve_node_v0(
            data_dir=args.data_dir,
            host=args.host,
            port=args.port,
            peer_urls=list(args.peer_url),
            poll_seconds=args.poll_seconds,
            enable_testnet_intake=args.enable_testnet_intake,
            enable_testnet_faucet=args.enable_testnet_faucet,
            submit_peer_url=args.submit_peer_url,
            peer_auth_token=peer_auth_token,
            node_auth_token=node_auth_token,
            submit_peer_auth_token=submit_peer_auth_token,
        )
    return 0


def _cmd_append(args: argparse.Namespace) -> int:
    try:
        tx = _load_json_object(args.tx)
        report = append_dex_transaction_v0(
            data_dir=args.data_dir,
            tx=tx,
            time_ms=args.time_ms,
        )
    except Exception as exc:
        report = {"schema": NODE_APPEND_REPORT_SCHEMA, "ok": False, "status": "rejected", "errors": [str(exc)]}
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report.get("ok") is True else 1


def _cmd_pull_live(args: argparse.Namespace) -> int:
    try:
        report = pull_live_from_peer_v0(
            data_dir=args.data_dir,
            peer_url=args.peer_url,
            peer_auth_token=_read_transport_auth_token_file_v0(args.peer_auth_token_file),
        )
    except Exception as exc:
        report = {"schema": NODE_PULL_REPORT_SCHEMA, "ok": False, "status": "rejected", "errors": [str(exc)]}
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report.get("ok") is True else 1


def _cmd_follow_once(args: argparse.Namespace) -> int:
    try:
        report = poll_live_peers_once_v0(
            data_dir=args.data_dir,
            peer_urls=list(args.peer_url),
            peer_auth_token=_read_transport_auth_token_file_v0(args.peer_auth_token_file),
        )
    except Exception as exc:
        report = {"schema": NODE_PEER_FOLLOW_REPORT_SCHEMA, "ok": False, "status": "rejected", "errors": [str(exc)]}
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report.get("ok") is True else 1


def _cmd_check_peers(args: argparse.Namespace) -> int:
    try:
        report = check_peer_status_v0(
            data_dir=args.data_dir,
            peer_urls=list(args.peer_url),
            peer_auth_token=_read_transport_auth_token_file_v0(args.peer_auth_token_file),
        )
    except Exception as exc:
        report = {"schema": NODE_PEER_CHECK_REPORT_SCHEMA, "ok": False, "status": "rejected", "errors": [str(exc)]}
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report.get("ok") is True else 1


def _cmd_evidence(args: argparse.Namespace) -> int:
    try:
        report = build_node_evidence_report_v0(
            data_dir=args.data_dir,
            peer_urls=list(args.peer_url),
            peer_auth_token=_read_transport_auth_token_file_v0(args.peer_auth_token_file),
        )
        if args.out is not None:
            _write_json(args.out, report)
            report = {**report, "evidence_report_path": str(args.out)}
    except Exception as exc:
        report = {"schema": NODE_EVIDENCE_REPORT_SCHEMA, "ok": False, "status": "rejected", "errors": [str(exc)]}
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report.get("ok") is True else 1


def _cmd_join(args: argparse.Namespace) -> int:
    try:
        report = join_public_node_from_config_v0(
            config_path=args.config,
            peer_auth_token=_read_transport_auth_token_file_v0(args.peer_auth_token_file),
        )
    except Exception as exc:
        report = {"schema": NODE_JOIN_REPORT_SCHEMA, "ok": False, "status": "rejected", "errors": [str(exc)]}
    print(json.dumps(report, indent=2, sort_keys=True))
    if report.get("ok") is not True:
        return 1
    config = dict(_load_json_object(args.config))
    if config.get("serve") is True:
        node_auth_token = _read_transport_auth_token_file_v0(
            _as_path(config.get("node_auth_token_file"), name="node_auth_token_file")
            if config.get("node_auth_token_file") is not None
            else args.node_auth_token_file
        )
        peer_auth_token = _read_transport_auth_token_file_v0(
            _as_path(config.get("peer_auth_token_file"), name="peer_auth_token_file")
            if config.get("peer_auth_token_file") is not None
            else args.peer_auth_token_file
        )
        submit_peer_auth_token = _read_transport_auth_token_file_v0(
            _as_path(config.get("submit_peer_auth_token_file"), name="submit_peer_auth_token_file")
            if config.get("submit_peer_auth_token_file") is not None
            else args.submit_peer_auth_token_file
        )
        serve_node_v0(
            data_dir=_as_path(config.get("data_dir"), name="data_dir"),
            host=str(config.get("host", "127.0.0.1")),
            port=int(config.get("port", 8787)),
            peer_urls=_as_string_list(config.get("peer_urls"), name="peer_urls"),
            poll_seconds=int(config.get("poll_seconds", 0)),
            enable_testnet_intake=config.get("enable_testnet_intake") is True,
            enable_testnet_faucet=config.get("enable_testnet_faucet") is True,
            submit_peer_url=str(config["submit_peer_url"]) if config.get("submit_peer_url") else None,
            peer_auth_token=peer_auth_token,
            node_auth_token=node_auth_token,
            submit_peer_auth_token=submit_peer_auth_token,
        )
    return 0


def _cmd_join_network(args: argparse.Namespace) -> int:
    try:
        report = join_public_node_from_network_config_url_v0(
            config_url=args.config_url,
            node_id=args.node_id,
            bundle_root=args.bundle_root,
            data_dir=args.data_dir,
            host=args.host,
            port=args.port,
            poll_seconds=args.poll_seconds,
            serve=args.serve,
            expected_network_config_hash=args.expected_network_config_hash,
            require_network_config_quorum=args.require_network_config_quorum,
            expected_config_signer_registry_hash=args.expected_config_signer_registry_hash,
            peer_auth_token=_read_transport_auth_token_file_v0(args.peer_auth_token_file),
        )
    except Exception as exc:
        report = {"schema": NODE_JOIN_REPORT_SCHEMA, "ok": False, "status": "rejected", "errors": [str(exc)]}
    print(json.dumps(report, indent=2, sort_keys=True))
    if report.get("ok") is not True:
        return 1
    if args.serve:
        join_config = dict(_load_json_object(args.data_dir / "node_join_config.json"))
        peer_auth_token = _read_transport_auth_token_file_v0(args.peer_auth_token_file)
        node_auth_token = _read_transport_auth_token_file_v0(args.node_auth_token_file)
        submit_peer_auth_token = _read_transport_auth_token_file_v0(args.submit_peer_auth_token_file)
        serve_node_v0(
            data_dir=args.data_dir,
            host=str(join_config.get("host", "0.0.0.0")),
            port=int(join_config.get("port", 8788)),
            peer_urls=_as_string_list(join_config.get("peer_urls"), name="peer_urls"),
            poll_seconds=int(join_config.get("poll_seconds", 5)),
            enable_testnet_intake=join_config.get("enable_testnet_intake") is True,
            enable_testnet_faucet=join_config.get("enable_testnet_faucet") is True,
            submit_peer_url=str(join_config["submit_peer_url"]) if join_config.get("submit_peer_url") else None,
            peer_auth_token=peer_auth_token,
            node_auth_token=node_auth_token,
            submit_peer_auth_token=submit_peer_auth_token,
        )
    return 0


def _cmd_doctor(args: argparse.Namespace) -> int:
    try:
        report = doctor_public_node_v0(
            config_url=args.config_url,
            expected_network_config_hash=args.expected_network_config_hash,
            require_network_config_quorum=args.require_network_config_quorum,
            expected_config_signer_registry_hash=args.expected_config_signer_registry_hash,
        )
    except Exception as exc:
        report = {"schema": NODE_DOCTOR_REPORT_SCHEMA, "ok": False, "status": "rejected", "errors": [str(exc)]}
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report.get("ok") is True else 1


def _cmd_faucet(args: argparse.Namespace) -> int:
    try:
        report = append_testnet_faucet_v0(
            data_dir=args.data_dir,
            to_pubkey=args.to_pubkey,
            asset=args.asset,
            amount=args.amount,
            tx_id=args.tx_id,
            time_ms=args.time_ms,
        )
    except Exception as exc:
        report = {"schema": NODE_APPEND_REPORT_SCHEMA, "ok": False, "status": "rejected", "errors": [str(exc)]}
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report.get("ok") is True else 1


def _cmd_create_token(args: argparse.Namespace) -> int:
    try:
        report = append_testnet_token_create_v0(
            data_dir=args.data_dir,
            symbol=args.symbol,
            name=args.name,
            decimals=args.decimals,
            creator_pubkey=args.creator_pubkey,
            asset=args.asset,
            salt=args.salt,
            tx_id=args.tx_id,
            time_ms=args.time_ms,
        )
    except Exception as exc:
        report = {"schema": NODE_APPEND_REPORT_SCHEMA, "ok": False, "status": "rejected", "errors": [str(exc)]}
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report.get("ok") is True else 1


def _cmd_serve(args: argparse.Namespace) -> int:
    load_node_status_v0(args.data_dir)
    serve_node_v0(
        data_dir=args.data_dir,
        host=args.host,
        port=args.port,
        peer_urls=list(args.peer_url),
        poll_seconds=args.poll_seconds,
        enable_testnet_intake=args.enable_testnet_intake,
        enable_testnet_faucet=args.enable_testnet_faucet,
        submit_peer_url=args.submit_peer_url,
        peer_auth_token=_read_transport_auth_token_file_v0(args.peer_auth_token_file),
        node_auth_token=_read_transport_auth_token_file_v0(args.node_auth_token_file),
        submit_peer_auth_token=_read_transport_auth_token_file_v0(args.submit_peer_auth_token_file),
    )
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run a ZenoLedger follower/watcher node")
    sub = parser.add_subparsers(dest="command", required=True)

    bootstrap = sub.add_parser("bootstrap", help="build a public-testnet bundle")
    bootstrap.add_argument("--out-dir", required=True, type=Path)
    bootstrap.add_argument("--network-id", default=DEFAULT_CHAIN_ID)
    bootstrap.add_argument("--chain-id", default=DEFAULT_CHAIN_ID)
    bootstrap.add_argument("--sequencer-id", default=DEFAULT_SEQUENCER_ID)
    bootstrap.add_argument("--time-ms", type=int, default=DEFAULT_TIME_MS)
    bootstrap.add_argument("--token-symbol", default="tZENO")
    bootstrap.set_defaults(func=_cmd_bootstrap)

    sync = sub.add_parser("sync", help="download and verify a public-testnet bundle from an HTTP mirror")
    sync.add_argument("--base-url", required=True)
    sync.add_argument("--out-dir", required=True, type=Path)
    sync.set_defaults(func=_cmd_sync)

    write_network_config = sub.add_parser(
        "write-network-config",
        help="write a public network config that remote nodes can join from",
    )
    write_network_config.add_argument("--bundle-root", required=True, type=Path)
    write_network_config.add_argument("--mirror-base-url", required=True)
    write_network_config.add_argument("--writer-url", action="append", required=True)
    write_network_config.add_argument("--peer-url", action="append", default=[])
    write_network_config.add_argument("--poll-seconds", type=int, default=5)
    write_network_config.add_argument("--node-port", type=int, default=8788)
    write_network_config.add_argument("--config-signer-registry", type=Path)
    write_network_config.add_argument("--config-signature-envelope", action="append", default=[], type=Path)
    write_network_config.add_argument("--out", required=True, type=Path)
    write_network_config.set_defaults(func=_cmd_write_network_config)

    join = sub.add_parser("join", help="sync, replay, and optionally serve a node from a JSON config")
    join.add_argument("--config", required=True, type=Path)
    join.add_argument("--peer-auth-token-file", type=Path)
    join.add_argument("--node-auth-token-file", type=Path)
    join.add_argument("--submit-peer-auth-token-file", type=Path)
    join.set_defaults(func=_cmd_join)

    join_network = sub.add_parser("join-network", help="join a public testnet from one network config URL")
    join_network.add_argument("--config-url", required=True)
    join_network.add_argument("--node-id", required=True)
    join_network.add_argument("--bundle-root", required=True, type=Path)
    join_network.add_argument("--data-dir", required=True, type=Path)
    join_network.add_argument("--serve", action="store_true")
    join_network.add_argument("--host", default="0.0.0.0")
    join_network.add_argument("--port", type=int)
    join_network.add_argument("--poll-seconds", type=int)
    join_network.add_argument("--expected-network-config-hash")
    join_network.add_argument("--require-network-config-quorum", action="store_true")
    join_network.add_argument("--expected-config-signer-registry-hash")
    join_network.add_argument("--peer-auth-token-file", type=Path)
    join_network.add_argument("--node-auth-token-file", type=Path)
    join_network.add_argument("--submit-peer-auth-token-file", type=Path)
    join_network.set_defaults(func=_cmd_join_network)

    doctor = sub.add_parser("doctor", help="check local and optional public-network bootstrap prerequisites")
    doctor.add_argument("--config-url")
    doctor.add_argument("--expected-network-config-hash")
    doctor.add_argument("--require-network-config-quorum", action="store_true")
    doctor.add_argument("--expected-config-signer-registry-hash")
    doctor.set_defaults(func=_cmd_doctor)

    run = sub.add_parser("run", help="replay a bundle and optionally serve node status")
    run.add_argument("--bundle-root", required=True, type=Path)
    run.add_argument("--node-id", required=True)
    run.add_argument("--data-dir", required=True, type=Path)
    run.add_argument("--observed-time-ms", type=int)
    run.add_argument("--peer-watcher-attestation", action="append", default=[], type=Path)
    run.add_argument("--serve", action="store_true")
    run.add_argument("--host", default="127.0.0.1")
    run.add_argument("--port", type=int, default=8787)
    run.add_argument("--peer-url", action="append", default=[])
    run.add_argument("--poll-seconds", type=int, default=0)
    run.add_argument("--enable-testnet-intake", action="store_true")
    run.add_argument("--enable-testnet-faucet", action="store_true")
    run.add_argument("--submit-peer-url")
    run.add_argument("--peer-auth-token-file", type=Path)
    run.add_argument("--node-auth-token-file", type=Path)
    run.add_argument("--submit-peer-auth-token-file", type=Path)
    run.set_defaults(func=_cmd_run)

    append = sub.add_parser("append", help="append one testnet DEX transaction to a node-local live ledger")
    append.add_argument("--data-dir", required=True, type=Path)
    append.add_argument("--tx", required=True, type=Path)
    append.add_argument("--time-ms", type=int, default=DEFAULT_TIME_MS + 1_000_000)
    append.set_defaults(func=_cmd_append)

    pull_live = sub.add_parser("pull-live", help="pull and replay live blocks from a peer node")
    pull_live.add_argument("--data-dir", required=True, type=Path)
    pull_live.add_argument("--peer-url", required=True)
    pull_live.add_argument("--peer-auth-token-file", type=Path)
    pull_live.set_defaults(func=_cmd_pull_live)

    follow_once = sub.add_parser("follow-once", help="poll all configured peers once and write peer_follow_state.json")
    follow_once.add_argument("--data-dir", required=True, type=Path)
    follow_once.add_argument("--peer-url", action="append", required=True)
    follow_once.add_argument("--peer-auth-token-file", type=Path)
    follow_once.set_defaults(func=_cmd_follow_once)

    check_peers = sub.add_parser("check-peers", help="check peer compatibility and common header prefixes")
    check_peers.add_argument("--data-dir", required=True, type=Path)
    check_peers.add_argument("--peer-url", action="append", required=True)
    check_peers.add_argument("--peer-auth-token-file", type=Path)
    check_peers.set_defaults(func=_cmd_check_peers)

    evidence = sub.add_parser("evidence", help="write a compact joined-node evidence report")
    evidence.add_argument("--data-dir", required=True, type=Path)
    evidence.add_argument("--peer-url", action="append", default=[])
    evidence.add_argument("--peer-auth-token-file", type=Path)
    evidence.add_argument("--out", type=Path)
    evidence.set_defaults(func=_cmd_evidence)

    faucet = sub.add_parser("faucet", help="append a testnet-only faucet mint to the live ledger")
    faucet.add_argument("--data-dir", required=True, type=Path)
    faucet.add_argument("--to-pubkey", required=True)
    faucet.add_argument("--asset", required=True)
    faucet.add_argument("--amount", required=True, type=int)
    faucet.add_argument("--tx-id", default="node-testnet-faucet-v0")
    faucet.add_argument("--time-ms", type=int, default=DEFAULT_TIME_MS + 1_000_000)
    faucet.set_defaults(func=_cmd_faucet)

    create_token = sub.add_parser("create-token", help="register a testnet-only token in the live ledger")
    create_token.add_argument("--data-dir", required=True, type=Path)
    create_token.add_argument("--symbol", required=True)
    create_token.add_argument("--name", required=True)
    create_token.add_argument("--decimals", required=True, type=int)
    create_token.add_argument("--creator-pubkey", required=True)
    create_token.add_argument("--asset")
    create_token.add_argument("--salt", default="default")
    create_token.add_argument("--tx-id", default="node-testnet-token-create-v0")
    create_token.add_argument("--time-ms", type=int, default=DEFAULT_TIME_MS + 1_000_000)
    create_token.set_defaults(func=_cmd_create_token)

    serve = sub.add_parser("serve", help="serve an existing node data directory")
    serve.add_argument("--data-dir", required=True, type=Path)
    serve.add_argument("--host", default="127.0.0.1")
    serve.add_argument("--port", type=int, default=8787)
    serve.add_argument("--peer-url", action="append", default=[])
    serve.add_argument("--poll-seconds", type=int, default=0)
    serve.add_argument("--enable-testnet-intake", action="store_true")
    serve.add_argument("--enable-testnet-faucet", action="store_true")
    serve.add_argument("--submit-peer-url")
    serve.add_argument("--peer-auth-token-file", type=Path)
    serve.add_argument("--node-auth-token-file", type=Path)
    serve.add_argument("--submit-peer-auth-token-file", type=Path)
    serve.set_defaults(func=_cmd_serve)

    args = parser.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
