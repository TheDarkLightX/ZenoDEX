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
from http import HTTPStatus
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Any, Mapping
from urllib.parse import urljoin
from urllib.request import urlopen

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.zeno_ledger_v0 import hash_v0
from src.integration.zeno_ledger_mirror import validate_mirror_index_v0
from tools.zeno_ledger_make_public_testnet_bundle import build_public_testnet_bundle_v0
from tools.zeno_ledger_make_testnet_bundle import (
    DEFAULT_CHAIN_ID,
    DEFAULT_SEQUENCER_ID,
    DEFAULT_TIME_MS,
)
from tools.zeno_ledger_operator_rehearsal import run_operator_rehearsal_v0


NODE_STATUS_SCHEMA = "zenodex.zeno_ledger.node_status.v0"
NODE_REPORT_SCHEMA = "zenodex.zeno_ledger.node_report.v0"
NODE_SYNC_REPORT_SCHEMA = "zenodex.zeno_ledger.node_sync_report.v0"
MAX_REMOTE_ARTIFACT_BYTES = 16 * 1024 * 1024


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


def make_node_http_server_v0(*, data_dir: Path, host: str, port: int) -> ThreadingHTTPServer:
    """Create a small read-only HTTP server for node status artifacts."""

    root = data_dir.resolve()

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

        def log_message(self, format: str, *args: object) -> None:
            return

    return ThreadingHTTPServer((host, port), Handler)


def serve_node_v0(*, data_dir: Path, host: str, port: int) -> None:
    server = make_node_http_server_v0(data_dir=data_dir, host=host, port=port)
    address, actual_port = server.server_address
    print(
        json.dumps(
            {
                "schema": "zenodex.zeno_ledger.node_server_ready.v0",
                "ok": True,
                "host": address,
                "port": actual_port,
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
        serve_node_v0(data_dir=args.data_dir, host=args.host, port=args.port)
    return 0


def _cmd_serve(args: argparse.Namespace) -> int:
    load_node_status_v0(args.data_dir)
    serve_node_v0(data_dir=args.data_dir, host=args.host, port=args.port)
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
    run.set_defaults(func=_cmd_run)

    serve = sub.add_parser("serve", help="serve an existing node data directory")
    serve.add_argument("--data-dir", required=True, type=Path)
    serve.add_argument("--host", default="127.0.0.1")
    serve.add_argument("--port", type=int, default=8787)
    serve.set_defaults(func=_cmd_serve)

    args = parser.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
