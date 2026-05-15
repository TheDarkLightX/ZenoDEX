#!/usr/bin/env python3
"""Run a ZenoLedger v0 follower/watcher node.

The v0 node wraps the existing deterministic public-testnet bundle and watcher
primitives. It can bootstrap a bundle, replay it as an independent operator,
emit a watcher attestation, and serve the resulting node status over HTTP.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
import threading
import time
from http import HTTPStatus
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Any, Mapping
from urllib.parse import urljoin
from urllib.request import urlopen

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


NODE_STATUS_SCHEMA = "zenodex.zeno_ledger.node_status.v0"
NODE_REPORT_SCHEMA = "zenodex.zeno_ledger.node_report.v0"
NODE_SYNC_REPORT_SCHEMA = "zenodex.zeno_ledger.node_sync_report.v0"
NODE_APPEND_REPORT_SCHEMA = "zenodex.zeno_ledger.node_append_report.v0"
NODE_PULL_REPORT_SCHEMA = "zenodex.zeno_ledger.node_pull_report.v0"
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
    data = _fetch_remote_bytes(url)
    obj = json.loads(data.decode("utf-8"))
    if not isinstance(obj, dict):
        raise ValueError(f"{url} must decode to a JSON object")
    return obj


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
        "ok": accepted,
        "status": "accepted" if accepted else "rejected",
        "node_id": node_status["node_id"],
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

        def do_GET(self) -> None:  # noqa: N802
            try:
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
                    self._send_json(
                        {
                            "token_symbol": status["token_symbol"],
                            "token_posture": status["token_posture"],
                            "test_token_catalog": status["test_token_catalog"],
                            "testnet_faucet_posture": status["testnet_faucet_posture"],
                        }
                    )
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
                if self.path == "/tx":
                    if not enable_testnet_intake:
                        self._send_json({"ok": False, "error": "testnet_intake_disabled"}, status=HTTPStatus.FORBIDDEN)
                        return
                    payload = _read_http_json_body(self)
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
                "status_url": f"http://{address}:{actual_port}/status",
            },
            indent=2,
            sort_keys=True,
        ),
        flush=True,
    )
    server.serve_forever()


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
        serve_node_v0(
            data_dir=args.data_dir,
            host=args.host,
            port=args.port,
            peer_urls=list(args.peer_url),
            poll_seconds=args.poll_seconds,
            enable_testnet_intake=args.enable_testnet_intake,
            enable_testnet_faucet=args.enable_testnet_faucet,
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
        )
    except Exception as exc:
        report = {"schema": NODE_PULL_REPORT_SCHEMA, "ok": False, "status": "rejected", "errors": [str(exc)]}
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
    serve.set_defaults(func=_cmd_serve)

    args = parser.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
