#!/usr/bin/env python3
"""Run a ZenoLedger v0 follower/watcher node.

The v0 node wraps the existing deterministic public-testnet bundle and watcher
primitives. It can bootstrap a bundle, replay it as an independent operator,
emit a watcher attestation, and serve the resulting node status over HTTP.
"""

from __future__ import annotations

import argparse
import hmac
import hashlib
import json
import os
import socket
import sys
import threading
import time
from http import HTTPStatus
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Any, Mapping
from urllib.error import HTTPError
from urllib.parse import urljoin, urlparse
from urllib.request import Request, urlopen

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.zeno_ledger_mirror import validate_mirror_index_v0
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
from tools.operator_report_output import print_operator_json, write_public_json


NODE_STATUS_SCHEMA = "zenodex.zeno_ledger.node_status.v0"
NODE_REPORT_SCHEMA = "zenodex.zeno_ledger.node_report.v0"
NODE_SYNC_REPORT_SCHEMA = "zenodex.zeno_ledger.node_sync_report.v0"
NODE_APPEND_REPORT_SCHEMA = "zenodex.zeno_ledger.node_append_report.v0"
NODE_PULL_REPORT_SCHEMA = "zenodex.zeno_ledger.node_pull_report.v0"
NODE_JOIN_CONFIG_SCHEMA = "zenodex.zeno_ledger.node_join_config.v0"
NODE_JOIN_REPORT_SCHEMA = "zenodex.zeno_ledger.node_join_report.v0"
NODE_PREFLIGHT_REPORT_SCHEMA = "zenodex.zeno_ledger.node_preflight_report.v0"
NODE_PEER_CHECK_REPORT_SCHEMA = "zenodex.zeno_ledger.node_peer_check_report.v0"
NODE_PUBLIC_NETWORK_CONFIG_SCHEMA = "zenodex.zeno_ledger.public_network_config.v0"
MAX_REMOTE_ARTIFACT_BYTES = 16 * 1024 * 1024
MAX_HTTP_POST_BYTES = 2 * 1024 * 1024
MAX_TESTNET_FAUCET_AMOUNT = 1_000_000_000_000
TESTNET_FAUCET_KIND = "ZENODEX_TESTNET_FAUCET"


def _load_json_object(path: Path) -> Mapping[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError(f"{path} must decode to a JSON object")
    return obj


def _write_json(path: Path, value: object) -> None:
    write_public_json(path, value)


def _is_safe_relative(path_text: str) -> bool:
    path = Path(path_text)
    return (
        path_text != ""
        and not path.is_absolute()
        and ".." not in path.parts
        and "://" not in path_text
        and "\\" not in path_text
    )


def _remote_url(base_url: str, rel_path: str) -> str:
    if not _is_http_url(base_url):
        raise ValueError("base_url must be an http(s) URL without embedded credentials")
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
                    raise ValueError("remote artifact too large")
            except ValueError:
                raise
        data = response.read(max_bytes + 1)
    if len(data) > max_bytes:
        raise ValueError("remote artifact too large")
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


def _fetch_json_url(url: str) -> dict[str, Any]:
    if not _is_http_url(url):
        raise ValueError("url must be an http(s) URL without embedded credentials")
    data = _fetch_remote_bytes(url)
    obj = json.loads(data.decode("utf-8"))
    if not isinstance(obj, dict):
        raise ValueError(f"{url} must decode to a JSON object")
    return obj


def _auth_bearer_header(token: str | None) -> dict[str, str]:
    if token is None:
        return {}
    return {"Authorization": f"Bearer {token}"}


def _auth_token_from_env_name(env_name: object, *, name: str) -> str | None:
    if env_name is None:
        return None
    if not isinstance(env_name, str) or env_name == "":
        raise ValueError(f"{name} must be a non-empty environment variable name")
    token = os.environ.get(env_name)
    if not token:
        raise ValueError(f"{name} points to an unset or empty environment variable")
    return token


def _auth_token_from_config(config: Mapping[str, Any], *, token_key: str, env_key: str) -> str | None:
    inline_token = config.get(token_key)
    env_name = config.get(env_key)
    if inline_token is not None and env_name is not None:
        raise ValueError(f"{token_key} and {env_key} must not both be set")
    if inline_token is not None:
        if not isinstance(inline_token, str) or inline_token == "":
            raise ValueError(f"{token_key} must be a non-empty string")
        return inline_token
    return _auth_token_from_env_name(env_name, name=env_key)


def _post_json_url(url: str, value: Mapping[str, Any], *, bearer_token: str | None = None) -> tuple[dict[str, Any], HTTPStatus]:
    if not _is_http_url(url):
        raise ValueError("url must be an http(s) URL without embedded credentials")
    payload = json.dumps(dict(value), sort_keys=True).encode("utf-8")
    request = Request(
        url,
        data=payload,
        headers={"Content-Type": "application/json", **_auth_bearer_header(bearer_token)},
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


def _is_http_url(value: str) -> bool:
    parsed = urlparse(value)
    return parsed.scheme in {"http", "https"} and bool(parsed.netloc) and not parsed.username and not parsed.password


def _tcp_port_available(host: str, port: int) -> bool:
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as sock:
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        try:
            sock.bind((host, port))
        except OSError:
            return False
    return True


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
    body = {key: value for key, value in config.items() if key != "network_config_hash"}
    return hash_v0("public_network_config_v0", body)


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


def _require_positive_amount_v0(value: object, *, name: str, maximum: int) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value <= 0:
        raise ValueError(f"{name} must be a positive int")
    if value > maximum:
        raise ValueError(f"{name} exceeds maximum")
    return int(value)


def _ui_amount_int_v0(value: object, *, name: str, maximum: int, allow_zero: bool = False) -> int:
    if isinstance(value, bool):
        raise ValueError(f"{name} must be an int")
    if isinstance(value, int):
        amount = value
    elif isinstance(value, float) and value.is_integer():
        amount = int(value)
    elif isinstance(value, str):
        stripped = value.strip()
        if stripped == "":
            raise ValueError(f"{name} must be an int")
        amount = int(stripped, 10)
    else:
        raise ValueError(f"{name} must be an int")
    if allow_zero:
        if amount < 0:
            raise ValueError(f"{name} must be a nonnegative int")
    elif amount <= 0:
        raise ValueError(f"{name} must be a positive int")
    if amount > maximum:
        raise ValueError(f"{name} exceeds maximum")
    return amount


def _latest_snapshot_for_ui_v0(*, data_dir: Path, node_status: Mapping[str, Any]) -> tuple[int, Mapping[str, Any]]:
    bundle_root = Path(str(node_status["bundle_root"]))
    base = _live_base_paths(bundle_root=bundle_root, data_dir=data_dir, node_status=node_status)
    snapshot_path = Path(str(base["pre_snapshot_path"]))
    return int(base["latest_height"]), _load_json_object(snapshot_path)


def _ui_token_catalog_v0(node_status: Mapping[str, Any]) -> tuple[dict[str, str], dict[str, dict[str, str]]]:
    by_asset: dict[str, str] = {}
    by_symbol: dict[str, dict[str, str]] = {}
    raw_catalog = node_status.get("test_token_catalog", [])
    if not isinstance(raw_catalog, list):
        return by_asset, by_symbol
    for row in raw_catalog:
        if not isinstance(row, Mapping):
            continue
        raw_symbol = row.get("symbol")
        raw_asset = row.get("asset_id")
        if not isinstance(raw_symbol, str) or not raw_symbol.strip() or not isinstance(raw_asset, str):
            continue
        try:
            asset = canonical_hex_fixed_allow_0x(raw_asset, nbytes=32, name="test_token_catalog.asset_id")
        except Exception:
            continue
        symbol = raw_symbol.strip()
        purpose = row.get("purpose")
        by_asset[asset] = symbol
        by_symbol[symbol.upper()] = {
            "symbol": symbol,
            "asset_id": asset,
            "purpose": purpose if isinstance(purpose, str) else "",
        }
    return by_asset, by_symbol


def _ui_pool_rows_from_snapshot_v0(
    *,
    snapshot: Mapping[str, Any],
    node_status: Mapping[str, Any],
) -> list[dict[str, Any]]:
    by_asset, _by_symbol = _ui_token_catalog_v0(node_status)
    raw_pools = snapshot.get("pools", [])
    if not isinstance(raw_pools, list):
        raise ValueError("snapshot.pools must be a list")
    rows: list[dict[str, Any]] = []
    for raw in raw_pools:
        if not isinstance(raw, Mapping):
            continue
        asset0 = _require_asset_v0(raw.get("asset0"), name="pool.asset0")
        asset1 = _require_asset_v0(raw.get("asset1"), name="pool.asset1")
        pool_id = str(raw.get("pool_id", ""))
        if pool_id == "":
            continue
        status = str(raw.get("status", "ACTIVE"))
        rows.append(
            {
                "pool_id": pool_id,
                "poolId": pool_id,
                "asset0": asset0,
                "asset1": asset1,
                "token0": by_asset.get(asset0, asset0),
                "token1": by_asset.get(asset1, asset1),
                "reserve0": int(raw.get("reserve0", 0)),
                "reserve1": int(raw.get("reserve1", 0)),
                "fee_bps": int(raw.get("fee_bps", 30)),
                "feeBps": int(raw.get("fee_bps", 30)),
                "lp_supply": int(raw.get("lp_supply", 0)),
                "lpSupply": int(raw.get("lp_supply", 0)),
                "status": status,
            }
        )
    return rows


def _ui_pools_response_v0(*, data_dir: Path, node_status: Mapping[str, Any]) -> dict[str, Any]:
    latest_height, snapshot = _latest_snapshot_for_ui_v0(data_dir=data_dir, node_status=node_status)
    pools = _ui_pool_rows_from_snapshot_v0(snapshot=snapshot, node_status=node_status)
    pool_assets = {
        str(pool[asset_key])
        for pool in pools
        for asset_key in ("asset0", "asset1")
        if isinstance(pool.get(asset_key), str)
    }
    by_asset, _by_symbol = _ui_token_catalog_v0(node_status)
    tokens = [
        {"symbol": symbol, "asset_id": asset}
        for asset, symbol in sorted(by_asset.items(), key=lambda item: item[1].upper())
        if asset in pool_assets
    ]
    return {
        "ok": True,
        "schema": "zenodex.zeno_ledger.ui_pools.v0",
        "source": "zeno_ledger_node_live",
        "latest_height": latest_height,
        "pools": pools,
        "tokens": tokens,
    }


def _snapshot_last_nonce_v0(snapshot: Mapping[str, Any], pubkey: str) -> int:
    raw_nonces = snapshot.get("nonces", [])
    if not isinstance(raw_nonces, list):
        return 0
    for row in raw_nonces:
        if not isinstance(row, Mapping):
            continue
        if row.get("pubkey") == pubkey:
            raw_last = row.get("last_nonce", 0)
            if isinstance(raw_last, int) and not isinstance(raw_last, bool) and raw_last >= 0:
                return raw_last
    return 0


def _asset_from_ui_symbol_v0(
    raw: object,
    *,
    by_symbol: Mapping[str, Mapping[str, str]],
    name: str,
) -> str:
    if not isinstance(raw, str) or raw.strip() == "":
        raise ValueError(f"{name} is required")
    text = raw.strip()
    try:
        return _require_asset_v0(text, name=name)
    except Exception:
        token = by_symbol.get(text.upper())
        if token and isinstance(token.get("asset_id"), str):
            return token["asset_id"]
    raise ValueError(f"{name} does not match a testnet token")


def _find_ui_swap_pool_v0(
    *,
    snapshot: Mapping[str, Any],
    node_status: Mapping[str, Any],
    payload: Mapping[str, Any],
) -> tuple[Mapping[str, Any], str, str]:
    _by_asset, by_symbol = _ui_token_catalog_v0(node_status)
    raw_pools = snapshot.get("pools", [])
    if not isinstance(raw_pools, list):
        raise ValueError("snapshot.pools must be a list")
    pool_id_hint = payload.get("pool_id", payload.get("poolId"))
    requested_pool_id = pool_id_hint if isinstance(pool_id_hint, str) and pool_id_hint.strip() else None
    asset_in_raw = payload.get("asset_in", payload.get("assetIn", payload.get("from")))
    asset_out_raw = payload.get("asset_out", payload.get("assetOut", payload.get("to")))
    asset_in = _asset_from_ui_symbol_v0(asset_in_raw, by_symbol=by_symbol, name="asset_in")
    asset_out = _asset_from_ui_symbol_v0(asset_out_raw, by_symbol=by_symbol, name="asset_out")
    if asset_in == asset_out:
        raise ValueError("asset_in and asset_out must differ")

    for row in raw_pools:
        if not isinstance(row, Mapping):
            continue
        row_pool_id = str(row.get("pool_id", ""))
        if requested_pool_id is not None and row_pool_id != requested_pool_id:
            continue
        row_asset0 = _require_asset_v0(row.get("asset0"), name="pool.asset0")
        row_asset1 = _require_asset_v0(row.get("asset1"), name="pool.asset1")
        if {row_asset0, row_asset1} == {asset_in, asset_out}:
            if str(row.get("status", "ACTIVE")) != "ACTIVE":
                raise ValueError("pool is not active")
            return row, asset_in, asset_out
    raise ValueError("matching pool not found")


def _ui_swap_tx_v0(
    *,
    data_dir: Path,
    node_status: Mapping[str, Any],
    payload: Mapping[str, Any],
    time_ms: int,
) -> dict[str, Any]:
    sender_raw = payload.get("sender_pubkey", payload.get("senderPubkey", payload.get("sender")))
    recipient_raw = payload.get("recipient", sender_raw)
    sender = _require_pubkey_v0(sender_raw, name="sender_pubkey")
    recipient = _require_pubkey_v0(recipient_raw, name="recipient")
    amount_in = _ui_amount_int_v0(
        payload.get("amount_in", payload.get("amountIn")),
        name="amount_in",
        maximum=MAX_TESTNET_FAUCET_AMOUNT,
    )
    min_amount_out = _ui_amount_int_v0(
        payload.get("min_amount_out", payload.get("minAmountOut", 1)),
        name="min_amount_out",
        maximum=MAX_TESTNET_FAUCET_AMOUNT,
        allow_zero=True,
    )
    deadline = _ui_amount_int_v0(
        payload.get("deadline", 1_999_999_999),
        name="deadline",
        maximum=9_999_999_999,
    )
    latest_height, snapshot = _latest_snapshot_for_ui_v0(data_dir=data_dir, node_status=node_status)
    pool, asset_in, asset_out = _find_ui_swap_pool_v0(snapshot=snapshot, node_status=node_status, payload=payload)
    nonce_raw = payload.get("nonce")
    if nonce_raw is None:
        nonce = _snapshot_last_nonce_v0(snapshot, sender) + 1
    else:
        nonce = _ui_amount_int_v0(nonce_raw, name="nonce", maximum=9_223_372_036_854_775_807)
    pool_id = str(pool["pool_id"])
    tx_id_raw = payload.get("tx_id", payload.get("txId"))
    tx_id = str(tx_id_raw).strip() if isinstance(tx_id_raw, str) and tx_id_raw.strip() else f"ui-swap-{latest_height + 1}-{nonce}"
    intent_payload = {
        "sender_pubkey": sender,
        "recipient": recipient,
        "pool_id": pool_id,
        "asset_in": asset_in,
        "asset_out": asset_out,
        "amount_in": amount_in,
        "min_amount_out": min_amount_out,
        "nonce": nonce,
    }
    return {
        "tx_id": tx_id,
        "block_timestamp": time_ms // 1000,
        "tx_sender_pubkey": sender,
        "operations": {
            "2": [
                {
                    "module": "TauSwap",
                    "version": "0.1",
                    "kind": "SWAP_EXACT_IN",
                    "intent_id": hash_v0("ui_swap_intent_v0", intent_payload),
                    "sender_pubkey": sender,
                    "deadline": deadline,
                    "nonce": nonce,
                    "pool_id": pool_id,
                    "asset_in": asset_in,
                    "asset_out": asset_out,
                    "amount_in": amount_in,
                    "min_amount_out": min_amount_out,
                    "recipient": recipient,
                }
            ]
        },
    }


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


def _is_faucet_body_v0(body: Mapping[str, Any]) -> bool:
    txs = body.get("transactions")
    if not isinstance(txs, list) or len(txs) != 1 or not isinstance(txs[0], Mapping):
        return False
    return txs[0].get("kind") == TESTNET_FAUCET_KIND


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
) -> dict[str, Any]:
    """Append one testnet DEX transaction to a node-local live ledger."""

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
        require_intent_signatures=False,
    )
    receipts_path = Path(str(block_report["receipts_path"]))
    receipts = json.loads(receipts_path.read_text(encoding="utf-8"))
    accepted = bool(receipts and isinstance(receipts[0], Mapping) and receipts[0].get("accepted") is True)
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
) -> dict[str, Any]:
    """Pull live blocks from a peer and accept only deterministic replays."""

    peer_admission = check_peer_status_v0(data_dir=data_dir, peer_urls=[peer_url])
    if peer_admission.get("ok") is not True:
        raise ValueError("peer admission rejected")

    node_status = load_node_status_v0(data_dir)
    bundle_root = Path(str(node_status["bundle_root"]))
    public_manifest = _read_public_manifest(bundle_root)
    bootstrap_manifest = _load_json_object(bundle_root / "bootstrap" / "manifest.json")
    base = _live_base_paths(bundle_root=bundle_root, data_dir=data_dir, node_status=node_status)
    local_latest = int(base["latest_height"])
    peer_live = _fetch_json_url(urljoin(peer_url.rstrip("/") + "/", "live"))
    if peer_live.get("ok") is not True or peer_live.get("live") is not True:
        return {
            "schema": NODE_PULL_REPORT_SCHEMA,
            "ok": True,
            "status": "accepted",
            "pulled_count": 0,
            "local_latest_height": local_latest,
            "peer_live": False,
            "peer_admission": peer_admission,
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
            "peer_admission": peer_admission,
        }

    pulled: list[dict[str, Any]] = []
    current_prev_header = Path(str(base["prev_header_path"]))
    current_pre_snapshot = Path(str(base["pre_snapshot_path"]))
    live_ledger_dir = data_dir / "live_ledger"
    for height in range(local_latest + 1, peer_latest + 1):
        peer_body = _fetch_json_url(urljoin(peer_url.rstrip("/") + "/", f"live/body/{height}"))
        peer_header = _fetch_json_url(urljoin(peer_url.rstrip("/") + "/", f"live/header/{height}"))
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
                require_intent_signatures=False,
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
        "peer_admission": peer_admission,
    }
    pull_report_path = data_dir / "pull_reports" / f"{peer_latest}.json"
    _write_json(pull_report_path, report)
    return {**report, "pull_report_path": str(pull_report_path)}


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


def _peer_tip_from_http_v0(*, peer_url: str, peer_status: Mapping[str, Any]) -> dict[str, Any]:
    peer_live = _fetch_json_url(urljoin(peer_url.rstrip("/") + "/", "live"))
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
) -> str:
    bootstrap_latest = int(peer_status["latest_height"])
    if height == bootstrap_latest:
        return str(peer_status["last_header_hash"])
    if height > bootstrap_latest:
        peer_header = _fetch_json_url(urljoin(peer_url.rstrip("/") + "/", f"live/header/{height}"))
        return canonical_header_hash_v0(dict(peer_header))
    raise ValueError(f"cannot fetch peer bootstrap header at height {height}")


def check_peer_status_v0(*, data_dir: Path, peer_urls: list[str]) -> dict[str, Any]:
    """Check that peer nodes are on the same network and common live prefix."""

    node_status = load_node_status_v0(data_dir)
    bundle_root = Path(str(node_status["bundle_root"]))
    local_tip = _local_tip_v0(data_dir=data_dir, node_status=node_status)
    peer_reports: list[dict[str, Any]] = []
    for peer_url in peer_urls:
        try:
            peer_status = _fetch_json_url(urljoin(peer_url.rstrip("/") + "/", "status"))
            if peer_status.get("schema") != NODE_STATUS_SCHEMA:
                raise ValueError("peer node status schema mismatch")
            if peer_status.get("node_status_hash") != _node_status_hash(peer_status):
                raise ValueError("peer node status hash mismatch")
            peer_tip = _peer_tip_from_http_v0(peer_url=peer_url, peer_status=peer_status)
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
            )
            common_header_match = local_common_hash == peer_common_hash
            compatible = bool(network_match and chain_match and feature_suite_match and common_header_match)
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
    write_auth_token: str | None = None,
    submit_peer_auth_token: str | None = None,
    peer_urls: list[str] | None = None,
) -> ThreadingHTTPServer:
    """Create a small read-only HTTP server for node status artifacts."""

    root = data_dir.resolve()
    append_lock = threading.Lock()

    class Handler(BaseHTTPRequestHandler):
        server_version = "ZenoLedgerNode/0"

        def _send_json(self, value: object, *, status: HTTPStatus = HTTPStatus.OK) -> None:
            payload = json.dumps(value, indent=2, sort_keys=True).encode("utf-8") + b"\n"
            self.send_response(int(status))
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(payload)))
            self.end_headers()
            self.wfile.write(payload)

        def _require_write_auth(self) -> bool:
            if write_auth_token is None:
                return True
            expected = f"Bearer {write_auth_token}"
            got = self.headers.get("Authorization", "")
            if hmac.compare_digest(got, expected):
                return True
            self._send_json({"ok": False, "error": "unauthorized"}, status=HTTPStatus.UNAUTHORIZED)
            return False

        def do_GET(self) -> None:  # noqa: N802
            try:
                status = load_node_status_v0(root)
                request_path = self.path.split("?", 1)[0]
                parts = [part for part in request_path.split("/") if part]
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
                if request_path in {"/", "/health"}:
                    self._send_json(
                        {
                            "ok": status["ok"],
                            "node_id": status["node_id"],
                            "node_status_hash": status["node_status_hash"],
                            "latest_height": status["latest_height"],
                        }
                    )
                    return
                if request_path == "/status":
                    self._send_json(status)
                    return
                if request_path == "/features":
                    self._send_json(
                        {
                            "feature_suite_hash": status["feature_suite_hash"],
                            "covered_feature_count": status["covered_feature_count"],
                            "covered_features": status["covered_features"],
                            "required_features": status["required_features"],
                        }
                    )
                    return
                if request_path == "/tokens":
                    self._send_json(
                        {
                            "token_symbol": status["token_symbol"],
                            "token_posture": status["token_posture"],
                            "test_token_catalog": status["test_token_catalog"],
                            "testnet_faucet_posture": status["testnet_faucet_posture"],
                        }
                    )
                    return
                if request_path == "/network":
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
                            "capabilities": {
                                "testnet_intake_enabled": enable_testnet_intake,
                                "testnet_faucet_enabled": enable_testnet_faucet,
                                "write_auth_required": write_auth_token is not None,
                                "submission_forwarding_enabled": submit_peer_url is not None,
                                "submit_peer_auth_configured": submit_peer_auth_token is not None,
                            },
                        }
                    )
                    return
                if request_path == "/api/pools":
                    self._send_json(_ui_pools_response_v0(data_dir=root, node_status=status))
                    return
                if request_path == "/live":
                    live_path = root / "live_state.json"
                    if not live_path.is_file():
                        self._send_json({"ok": True, "live": False})
                    else:
                        self._send_json({"ok": True, "live": True, "state": _load_json_object(live_path)})
                    return
                if request_path == "/attestation":
                    attestation = _load_optional_json(status.get("operator_attestation_path"))
                    if attestation is None:
                        self._send_json({"ok": False, "error": "attestation_missing"}, status=HTTPStatus.NOT_FOUND)
                    else:
                        self._send_json(attestation)
                    return
                if request_path == "/testnet-status":
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
                request_path = self.path.split("?", 1)[0]
                if request_path == "/api/swap":
                    if not self._require_write_auth():
                        return
                    if not enable_testnet_intake:
                        self._send_json({"ok": False, "error": "testnet_intake_disabled"}, status=HTTPStatus.FORBIDDEN)
                        return
                    payload = _read_http_json_body(self)
                    if submit_peer_url:
                        report, peer_status = _post_json_url(
                            urljoin(submit_peer_url.rstrip("/") + "/", "api/swap"),
                            payload,
                            bearer_token=submit_peer_auth_token,
                        )
                        self._send_json({**report, "forwarded_to": submit_peer_url}, status=peer_status)
                        return
                    time_ms = payload.get("time_ms", payload.get("timeMs"))
                    if time_ms is None:
                        time_ms = int(time.time() * 1000)
                    if not isinstance(time_ms, int) or isinstance(time_ms, bool) or time_ms < 0:
                        self._send_json({"ok": False, "error": "time_ms_must_be_nonnegative_int"}, status=HTTPStatus.BAD_REQUEST)
                        return
                    status = load_node_status_v0(root)
                    tx = _ui_swap_tx_v0(data_dir=root, node_status=status, payload=payload, time_ms=int(time_ms))
                    with append_lock:
                        report = append_dex_transaction_v0(data_dir=root, tx=tx, time_ms=int(time_ms))
                    receipt = report.get("receipt")
                    accepted = bool(isinstance(receipt, Mapping) and receipt.get("accepted") is True)
                    response = {
                        **report,
                        "ok": accepted,
                        "txHash": report["tx_hash"],
                        "tx_hash": report["tx_hash"],
                        "tx_accepted": accepted,
                        "receipt": receipt,
                    }
                    self._send_json(response, status=HTTPStatus.OK if accepted else HTTPStatus.BAD_REQUEST)
                    return
                if request_path == "/tx":
                    if not self._require_write_auth():
                        return
                    if not enable_testnet_intake:
                        self._send_json({"ok": False, "error": "testnet_intake_disabled"}, status=HTTPStatus.FORBIDDEN)
                        return
                    payload = _read_http_json_body(self)
                    if submit_peer_url:
                        report, peer_status = _post_json_url(
                            urljoin(submit_peer_url.rstrip("/") + "/", "tx"),
                            payload,
                            bearer_token=submit_peer_auth_token,
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
                if request_path == "/faucet":
                    if not self._require_write_auth():
                        return
                    if not enable_testnet_faucet:
                        self._send_json({"ok": False, "error": "testnet_faucet_disabled"}, status=HTTPStatus.FORBIDDEN)
                        return
                    payload = _read_http_json_body(self)
                    if submit_peer_url:
                        report, peer_status = _post_json_url(
                            urljoin(submit_peer_url.rstrip("/") + "/", "faucet"),
                            payload,
                            bearer_token=submit_peer_auth_token,
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
) -> None:
    if not peer_urls or poll_seconds <= 0:
        return

    def _loop() -> None:
        while True:
            for peer_url in peer_urls:
                try:
                    pull_live_from_peer_v0(data_dir=data_dir, peer_url=peer_url)
                except Exception:
                    # Peer polling is best-effort. Manual `pull-live` returns
                    # exact errors for operator diagnosis.
                    pass
            time.sleep(poll_seconds)

    thread = threading.Thread(target=_loop, daemon=True)
    thread.start()


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
    write_auth_token: str | None = None,
    submit_peer_auth_token: str | None = None,
) -> None:
    _start_peer_follow_loop(
        data_dir=data_dir,
        peer_urls=list(peer_urls or []),
        poll_seconds=poll_seconds,
    )
    server = make_node_http_server_v0(
        data_dir=data_dir,
        host=host,
        port=port,
        enable_testnet_intake=enable_testnet_intake,
        enable_testnet_faucet=enable_testnet_faucet,
        submit_peer_url=submit_peer_url,
        write_auth_token=write_auth_token,
        submit_peer_auth_token=submit_peer_auth_token,
        peer_urls=list(peer_urls or []),
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
                "write_auth_required": write_auth_token is not None,
                "submit_peer_url": submit_peer_url,
                "submit_peer_auth_configured": submit_peer_auth_token is not None,
                "status_url": f"http://{address}:{actual_port}/status",
            },
            indent=2,
            sort_keys=True,
        ),
        flush=True,
    )
    server.serve_forever()


def preflight_node_join_config_v0(
    *,
    config_path: Path,
    check_port: bool = True,
    strict_exposure: bool = False,
    public_operator: bool = False,
) -> dict[str, Any]:
    """Validate an operator join config before sync/replay/serve side effects."""

    errors: list[str] = []
    warnings: list[str] = []
    checks: dict[str, bool] = {}
    try:
        config = dict(_load_json_object(config_path))
    except Exception as exc:
        return {
            "schema": NODE_PREFLIGHT_REPORT_SCHEMA,
            "ok": False,
            "status": "rejected",
            "config_path": str(config_path),
            "errors": [str(exc)],
            "warnings": [],
            "checks": {},
        }

    if config.get("schema") not in {None, NODE_JOIN_CONFIG_SCHEMA}:
        errors.append("node join config schema mismatch")
    checks["schema"] = not errors

    node_id = str(config.get("node_id", "")).strip()
    if node_id == "":
        errors.append("node_id is required")
    checks["node_id"] = node_id != ""

    data_dir_ok = False
    data_dir_parent_ok = False
    try:
        data_dir = _as_path(config.get("data_dir"), name="data_dir")
        data_dir_ok = True
        data_dir_parent_ok = data_dir.parent.exists()
        if data_dir.exists() and not data_dir.is_dir():
            errors.append("data_dir exists but is not a directory")
        if not data_dir_parent_ok:
            warnings.append(f"data_dir parent does not exist yet: {data_dir.parent}")
    except Exception as exc:
        errors.append(str(exc))
        data_dir = None
    checks["data_dir"] = data_dir_ok
    checks["data_dir_parent"] = data_dir_parent_ok

    bundle_root_ok = False
    base_url = config.get("base_url")
    if base_url is not None:
        if not isinstance(base_url, str) or not _is_http_url(base_url):
            errors.append("base_url must be an http(s) URL without embedded credentials")
        else:
            bundle_root_ok = True
    try:
        bundle_root = _as_path(config.get("bundle_root"), name="bundle_root")
        if base_url is None:
            _read_public_manifest(bundle_root)
            bundle_root_ok = True
        elif bundle_root.is_file():
            errors.append("bundle_root must not be a file")
    except Exception as exc:
        errors.append(str(exc))
    checks["bundle_source"] = bundle_root_ok

    peer_urls_ok = True
    try:
        peer_urls = _as_string_list(config.get("peer_urls"), name="peer_urls")
    except Exception as exc:
        errors.append(str(exc))
        peer_urls = []
        peer_urls_ok = False
    for peer_url in peer_urls:
        if not _is_http_url(peer_url):
            errors.append(f"peer_url must be an http(s) URL without embedded credentials: {peer_url}")
            peer_urls_ok = False
    checks["peer_urls"] = peer_urls_ok

    submit_peer_url = config.get("submit_peer_url")
    if submit_peer_url is not None and (not isinstance(submit_peer_url, str) or not _is_http_url(submit_peer_url)):
        errors.append("submit_peer_url must be an http(s) URL without embedded credentials")
        checks["submit_peer_url"] = False
    else:
        checks["submit_peer_url"] = True

    write_auth_inline = config.get("write_auth_token") is not None
    submit_peer_auth_inline = config.get("submit_peer_auth_token") is not None
    write_auth_env_configured = (
        isinstance(config.get("write_auth_token_env"), str)
        and config.get("write_auth_token_env") != ""
    )
    submit_peer_auth_env_configured = (
        isinstance(config.get("submit_peer_auth_token_env"), str)
        and config.get("submit_peer_auth_token_env") != ""
    )
    try:
        write_auth_token = _auth_token_from_config(
            config,
            token_key="write_auth_token",
            env_key="write_auth_token_env",
        )
    except Exception as exc:
        errors.append(str(exc))
        write_auth_token = None
    try:
        submit_peer_auth_token = _auth_token_from_config(
            config,
            token_key="submit_peer_auth_token",
            env_key="submit_peer_auth_token_env",
        )
    except Exception as exc:
        errors.append(str(exc))
        submit_peer_auth_token = None
    checks["write_auth"] = write_auth_token is not None
    checks["submit_peer_auth"] = submit_peer_url is None or submit_peer_auth_token is not None
    checks["inline_auth_tokens_absent"] = not (write_auth_inline or submit_peer_auth_inline)
    if write_auth_inline or submit_peer_auth_inline:
        warnings.append("inline auth tokens are present in the config; prefer *_auth_token_env for operator configs")

    serve = config.get("serve") is True
    checks["serve_flag"] = isinstance(config.get("serve"), bool) or config.get("serve") is None
    if not checks["serve_flag"]:
        errors.append("serve must be a boolean when present")

    host = str(config.get("host", "127.0.0.1"))
    raw_port = config.get("port", 8787)
    raw_poll_seconds = config.get("poll_seconds", 0)
    port = int(raw_port) if isinstance(raw_port, int) and not isinstance(raw_port, bool) else -1
    poll_seconds = (
        int(raw_poll_seconds)
        if isinstance(raw_poll_seconds, int) and not isinstance(raw_poll_seconds, bool)
        else -1
    )
    checks["port_range"] = 0 < port <= 65535
    checks["poll_seconds"] = poll_seconds >= 0
    if not checks["port_range"]:
        errors.append("port must be an integer in 1..65535")
    if not checks["poll_seconds"]:
        errors.append("poll_seconds must be a nonnegative integer")
    if serve and check_port and checks["port_range"]:
        port_available = _tcp_port_available(host, port)
        checks["port_available"] = port_available
        if not port_available:
            errors.append(f"port is not available for bind: {host}:{port}")
    elif serve:
        checks["port_available"] = True

    testnet_mutation_enabled = (
        serve
        and (config.get("enable_testnet_faucet") is True or config.get("enable_testnet_intake") is True)
    )
    public_bind = serve and host in {"0.0.0.0", "::"}
    if public_bind:
        message = "serve host exposes the node on all interfaces; place it behind firewall/auth controls"
        warnings.append(message)
        if strict_exposure:
            errors.append(f"strict_exposure: {message}")
    if config.get("enable_testnet_faucet") is True:
        message = "testnet faucet is enabled; never expose this on a real-value network"
        warnings.append(message)
        if strict_exposure and public_bind:
            errors.append(f"strict_exposure: {message}")
    if config.get("enable_testnet_intake") is True and serve:
        message = "testnet transaction intake is enabled; this endpoint accepts unsigned fixture traffic"
        warnings.append(message)
        if strict_exposure and public_bind:
            errors.append(f"strict_exposure: {message}")
    if testnet_mutation_enabled and write_auth_token is None:
        message = "write auth is not configured for enabled testnet mutation endpoints"
        warnings.append(message)
        if strict_exposure and public_bind:
            errors.append(f"strict_exposure: {message}")
    if submit_peer_url is not None and submit_peer_auth_token is None:
        warnings.append("submit_peer_auth_token_env is not configured; forwarded writes will be unauthenticated")
    if config.get("enable_testnet_faucet") is True and config.get("enable_testnet_intake") is not True:
        warnings.append("faucet is enabled while testnet intake is disabled; faucet requests will not be useful")

    checks["public_operator_bind"] = not public_operator or not public_bind
    checks["public_operator_inline_auth"] = not public_operator or not (write_auth_inline or submit_peer_auth_inline)
    checks["public_operator_write_auth_env"] = (
        not public_operator
        or not testnet_mutation_enabled
        or write_auth_env_configured
    )
    checks["public_operator_submit_peer_auth_env"] = (
        not public_operator
        or submit_peer_url is None
        or submit_peer_auth_env_configured
    )
    if public_operator:
        if public_bind:
            errors.append("public_operator: serve host must bind locally behind an authenticated reverse proxy")
            if testnet_mutation_enabled:
                errors.append("public_operator: public binds must not expose testnet faucet or intake endpoints")
        if write_auth_inline or submit_peer_auth_inline:
            errors.append("public_operator: inline auth tokens are forbidden; use *_auth_token_env")
        if testnet_mutation_enabled and not write_auth_env_configured:
            errors.append("public_operator: enabled mutation endpoints require write_auth_token_env")
        if submit_peer_url is not None and not submit_peer_auth_env_configured:
            errors.append("public_operator: submit_peer_url requires submit_peer_auth_token_env")

    ok = not errors
    return {
        "schema": NODE_PREFLIGHT_REPORT_SCHEMA,
        "ok": ok,
        "status": "accepted" if ok else "rejected",
        "config_path": str(config_path),
        "node_id": node_id,
        "serve": serve,
        "host": host,
        "port": port,
        "peer_count": len(peer_urls),
        "check_port": check_port,
        "strict_exposure": strict_exposure,
        "public_operator": public_operator,
        "errors": errors,
        "warnings": warnings,
        "checks": checks,
    }


def join_public_node_from_config_v0(*, config_path: Path) -> dict[str, Any]:
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
    peer_urls = _as_string_list(config.get("peer_urls"), name="peer_urls")
    peer_check = check_peer_status_v0(data_dir=data_dir, peer_urls=peer_urls) if peer_urls else None
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
            "enable_testnet_intake": True,
            "enable_testnet_faucet": True,
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
) -> dict[str, Any]:
    if network_config.get("schema") != NODE_PUBLIC_NETWORK_CONFIG_SCHEMA:
        raise ValueError("public network config schema mismatch")
    expected_hash = network_config.get("network_config_hash")
    if expected_hash is not None and expected_hash != _public_network_config_hash_v0(network_config):
        raise ValueError("public network config hash mismatch")
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
    write_auth_token_env: str | None = None,
    submit_peer_auth_token_env: str | None = None,
) -> dict[str, Any]:
    """Join a public ZenoLedger testnet from one published network config URL."""

    network_config = _fetch_json_url(config_url)
    join_config = _public_network_config_to_join_config_v0(
        network_config=network_config,
        node_id=node_id,
        bundle_root=bundle_root,
        data_dir=data_dir,
        host=host,
        port=port,
        poll_seconds=poll_seconds,
        serve=serve,
    )
    if write_auth_token_env:
        join_config["write_auth_token_env"] = write_auth_token_env
    if submit_peer_auth_token_env:
        join_config["submit_peer_auth_token_env"] = submit_peer_auth_token_env
    data_dir.mkdir(parents=True, exist_ok=True)
    network_config_path = data_dir / "public_network_config.json"
    join_config_path = data_dir / "node_join_config.json"
    _write_json(network_config_path, network_config)
    _write_json(join_config_path, join_config)
    report = join_public_node_from_config_v0(config_path=join_config_path)
    report["network_config_url"] = config_url
    report["network_config_path"] = str(network_config_path)
    report["network_config_hash"] = network_config.get("network_config_hash")
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
    print_operator_json(report)
    return 0 if report.get("ok") is True else 1


def _cmd_sync(args: argparse.Namespace) -> int:
    try:
        report = sync_public_bundle_from_url_v0(
            base_url=args.base_url,
            out_dir=args.out_dir,
        )
    except Exception as exc:
        report = {"schema": NODE_SYNC_REPORT_SCHEMA, "ok": False, "status": "rejected", "errors": [str(exc)]}
    print_operator_json(report)
    return 0 if report.get("ok") is True else 1


def _cmd_preflight(args: argparse.Namespace) -> int:
    report = preflight_node_join_config_v0(
        config_path=args.config,
        check_port=not args.skip_port_check,
        strict_exposure=args.strict_exposure,
        public_operator=args.public_operator,
    )
    print_operator_json(report)
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
        _write_json(args.out, report)
        report = {**report, "config_path": str(args.out)}
    except Exception as exc:
        report = {"schema": NODE_PUBLIC_NETWORK_CONFIG_SCHEMA, "ok": False, "status": "rejected", "errors": [str(exc)]}
    print_operator_json(report)
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
    print_operator_json(report)
    if report.get("ok") is not True:
        return 1
    if args.serve:
        serve_node_v0(
            data_dir=args.data_dir,
            host=args.host,
            port=args.port,
            peer_urls=list(args.peer_url),
            poll_seconds=args.poll_seconds,
            enable_testnet_intake=args.enable_testnet_intake,
            enable_testnet_faucet=args.enable_testnet_faucet,
            submit_peer_url=args.submit_peer_url,
            write_auth_token=_auth_token_from_env_name(args.write_auth_token_env, name="write_auth_token_env"),
            submit_peer_auth_token=_auth_token_from_env_name(args.submit_peer_auth_token_env, name="submit_peer_auth_token_env"),
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
    print_operator_json(report)
    return 0 if report.get("ok") is True else 1


def _cmd_pull_live(args: argparse.Namespace) -> int:
    try:
        report = pull_live_from_peer_v0(
            data_dir=args.data_dir,
            peer_url=args.peer_url,
        )
    except Exception as exc:
        report = {"schema": NODE_PULL_REPORT_SCHEMA, "ok": False, "status": "rejected", "errors": [str(exc)]}
    print_operator_json(report)
    return 0 if report.get("ok") is True else 1


def _cmd_check_peers(args: argparse.Namespace) -> int:
    try:
        report = check_peer_status_v0(
            data_dir=args.data_dir,
            peer_urls=list(args.peer_url),
        )
    except Exception as exc:
        report = {"schema": NODE_PEER_CHECK_REPORT_SCHEMA, "ok": False, "status": "rejected", "errors": [str(exc)]}
    print_operator_json(report)
    return 0 if report.get("ok") is True else 1


def _cmd_join(args: argparse.Namespace) -> int:
    try:
        report = join_public_node_from_config_v0(config_path=args.config)
    except Exception as exc:
        report = {"schema": NODE_JOIN_REPORT_SCHEMA, "ok": False, "status": "rejected", "errors": [str(exc)]}
    print_operator_json(report)
    if report.get("ok") is not True:
        return 1
    config = dict(_load_json_object(args.config))
    if config.get("serve") is True:
        serve_node_v0(
            data_dir=_as_path(config.get("data_dir"), name="data_dir"),
            host=str(config.get("host", "127.0.0.1")),
            port=int(config.get("port", 8787)),
            peer_urls=_as_string_list(config.get("peer_urls"), name="peer_urls"),
            poll_seconds=int(config.get("poll_seconds", 0)),
            enable_testnet_intake=config.get("enable_testnet_intake") is True,
            enable_testnet_faucet=config.get("enable_testnet_faucet") is True,
            submit_peer_url=str(config["submit_peer_url"]) if config.get("submit_peer_url") else None,
            write_auth_token=_auth_token_from_config(
                config,
                token_key="write_auth_token",
                env_key="write_auth_token_env",
            ),
            submit_peer_auth_token=_auth_token_from_config(
                config,
                token_key="submit_peer_auth_token",
                env_key="submit_peer_auth_token_env",
            ),
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
            write_auth_token_env=args.write_auth_token_env,
            submit_peer_auth_token_env=args.submit_peer_auth_token_env,
        )
    except Exception as exc:
        report = {"schema": NODE_JOIN_REPORT_SCHEMA, "ok": False, "status": "rejected", "errors": [str(exc)]}
    print_operator_json(report)
    if report.get("ok") is not True:
        return 1
    if args.serve:
        join_config = dict(_load_json_object(args.data_dir / "node_join_config.json"))
        serve_node_v0(
            data_dir=args.data_dir,
            host=str(join_config.get("host", "0.0.0.0")),
            port=int(join_config.get("port", 8788)),
            peer_urls=_as_string_list(join_config.get("peer_urls"), name="peer_urls"),
            poll_seconds=int(join_config.get("poll_seconds", 5)),
            enable_testnet_intake=join_config.get("enable_testnet_intake") is True,
            enable_testnet_faucet=join_config.get("enable_testnet_faucet") is True,
            submit_peer_url=str(join_config["submit_peer_url"]) if join_config.get("submit_peer_url") else None,
            write_auth_token=_auth_token_from_config(
                join_config,
                token_key="write_auth_token",
                env_key="write_auth_token_env",
            ),
            submit_peer_auth_token=_auth_token_from_config(
                join_config,
                token_key="submit_peer_auth_token",
                env_key="submit_peer_auth_token_env",
            ),
        )
    return 0


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
    print_operator_json(report)
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
        write_auth_token=_auth_token_from_env_name(args.write_auth_token_env, name="write_auth_token_env"),
        submit_peer_auth_token=_auth_token_from_env_name(args.submit_peer_auth_token_env, name="submit_peer_auth_token_env"),
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

    preflight = sub.add_parser("preflight", help="validate a node join config before sync/replay/serve")
    preflight.add_argument("--config", required=True, type=Path)
    preflight.add_argument("--skip-port-check", action="store_true")
    preflight.add_argument(
        "--strict-exposure",
        action="store_true",
        help="reject public binds with testnet faucet or unsigned testnet intake exposure",
    )
    preflight.add_argument(
        "--public-operator",
        action="store_true",
        help="reject inline secrets and public all-interface binds for operator-facing configs",
    )
    preflight.set_defaults(func=_cmd_preflight)

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
    write_network_config.add_argument("--out", required=True, type=Path)
    write_network_config.set_defaults(func=_cmd_write_network_config)

    join = sub.add_parser("join", help="sync, replay, and optionally serve a node from a JSON config")
    join.add_argument("--config", required=True, type=Path)
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
    join_network.add_argument("--write-auth-token-env")
    join_network.add_argument("--submit-peer-auth-token-env")
    join_network.set_defaults(func=_cmd_join_network)

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
    run.add_argument("--write-auth-token-env")
    run.add_argument("--submit-peer-auth-token-env")
    run.set_defaults(func=_cmd_run)

    append = sub.add_parser("append", help="append one testnet DEX transaction to a node-local live ledger")
    append.add_argument("--data-dir", required=True, type=Path)
    append.add_argument("--tx", required=True, type=Path)
    append.add_argument("--time-ms", type=int, default=DEFAULT_TIME_MS + 1_000_000)
    append.set_defaults(func=_cmd_append)

    pull_live = sub.add_parser("pull-live", help="pull and replay live blocks from a peer node")
    pull_live.add_argument("--data-dir", required=True, type=Path)
    pull_live.add_argument("--peer-url", required=True)
    pull_live.set_defaults(func=_cmd_pull_live)

    check_peers = sub.add_parser("check-peers", help="check peer compatibility and common header prefixes")
    check_peers.add_argument("--data-dir", required=True, type=Path)
    check_peers.add_argument("--peer-url", action="append", required=True)
    check_peers.set_defaults(func=_cmd_check_peers)

    faucet = sub.add_parser("faucet", help="append a testnet-only faucet mint to the live ledger")
    faucet.add_argument("--data-dir", required=True, type=Path)
    faucet.add_argument("--to-pubkey", required=True)
    faucet.add_argument("--asset", required=True)
    faucet.add_argument("--amount", required=True, type=int)
    faucet.add_argument("--tx-id", default="node-testnet-faucet-v0")
    faucet.add_argument("--time-ms", type=int, default=DEFAULT_TIME_MS + 1_000_000)
    faucet.set_defaults(func=_cmd_faucet)

    serve = sub.add_parser("serve", help="serve an existing node data directory")
    serve.add_argument("--data-dir", required=True, type=Path)
    serve.add_argument("--host", default="127.0.0.1")
    serve.add_argument("--port", type=int, default=8787)
    serve.add_argument("--peer-url", action="append", default=[])
    serve.add_argument("--poll-seconds", type=int, default=0)
    serve.add_argument("--enable-testnet-intake", action="store_true")
    serve.add_argument("--enable-testnet-faucet", action="store_true")
    serve.add_argument("--submit-peer-url")
    serve.add_argument("--write-auth-token-env")
    serve.add_argument("--submit-peer-auth-token-env")
    serve.set_defaults(func=_cmd_serve)

    args = parser.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
