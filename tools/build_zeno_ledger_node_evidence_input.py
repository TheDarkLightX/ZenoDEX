#!/usr/bin/env python3
"""Build one machine's input files for a two-machine ZenoLedger evidence archive."""

from __future__ import annotations

import argparse
import json
import platform
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.zeno_ledger_watcher import build_watcher_attestation_v0  # noqa: E402
from tools.zeno_ledger_node import (  # noqa: E402
    _public_network_config_hash_v0,
    load_node_status_v0,
)
from tools.zeno_ledger_verify import (  # noqa: E402
    STRUCTURAL_DIAGNOSTIC_MODE,
    ZERO_ROOT,
    verify_zeno_ledger_v0,
)

REPORT_SCHEMA = "zenodex.zeno_ledger.node_evidence_input_report.v0"
MACHINE_SCHEMA = "zenodex.zeno_ledger.node_evidence_input.v0"


def build_node_evidence_input_v0(
    *,
    data_dir: Path,
    network_config_path: Path | None,
    machine_out: Path,
    attestation_out: Path,
    commit_sha: str | None = None,
    observed_time_ms: int | None = None,
) -> dict[str, Any]:
    errors: list[str] = []
    try:
        status = load_node_status_v0(data_dir)
        if status.get("ok") is not True or status.get("status") != "accepted":
            raise ValueError("node status must be accepted")
        bundle_root = Path(str(status["bundle_root"]))
        network_config = _load_network_config(
            explicit_path=network_config_path,
            data_dir=data_dir,
            bundle_root=bundle_root,
        )
        network_config_hash = _validated_network_config_hash(network_config)
        archive_commit = commit_sha if commit_sha is not None else _git_commit_sha()
        if archive_commit is None:
            raise ValueError("commit_sha was not supplied and git rev-parse HEAD failed")

        tip = _local_tip(data_dir=data_dir, status=status)
        verify_report = _verify_node_range(data_dir=data_dir, status=status, tip_height=int(tip["height"]))
        if verify_report.get("ok") is not True:
            raise ValueError("node range verification rejected")
        if verify_report.get("last_header_hash") != tip["header_hash"]:
            raise ValueError("verified last header hash does not match local tip")

        machine = {
            "schema": MACHINE_SCHEMA,
            "machine_id": status["node_id"],
            "commit_sha": archive_commit,
            "python_version": platform.python_version(),
            "network_config_hash": network_config_hash,
            "feature_suite_hash": status["feature_suite_hash"],
            "header_hash": tip["header_hash"],
            "height": tip["height"],
            "node_status_hash": status["node_status_hash"],
            "network_id": status["network_id"],
            "chain_id": status["chain_id"],
        }
        attestation = build_watcher_attestation_v0(
            verify_report=verify_report,
            watcher_id=str(status["node_id"]),
            observed_time_ms=(
                int(observed_time_ms)
                if observed_time_ms is not None
                else int(time.time() * 1000)
            ),
            verifier_ref="tools/build_zeno_ledger_node_evidence_input.py@v0",
        )
        _write_json(machine_out, machine)
        _write_json(attestation_out, attestation)
        return {
            "schema": REPORT_SCHEMA,
            "ok": True,
            "status": "accepted",
            "machine_out": str(machine_out),
            "attestation_out": str(attestation_out),
            "machine_id": machine["machine_id"],
            "commit_sha": machine["commit_sha"],
            "python_version": machine["python_version"],
            "network_config_hash": network_config_hash,
            "feature_suite_hash": machine["feature_suite_hash"],
            "header_hash": machine["header_hash"],
            "height": machine["height"],
            "checked_heights": verify_report["checked_heights"],
            "attestation_hash": attestation["attestation_hash"],
            "verify_report": verify_report,
        }
    except Exception as exc:
        errors.append(str(exc))
        return {
            "schema": REPORT_SCHEMA,
            "ok": False,
            "status": "rejected",
            "errors": errors,
        }


def _load_json_object(path: Path) -> Mapping[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError(f"{path} must decode to a JSON object")
    return obj


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _load_network_config(
    *,
    explicit_path: Path | None,
    data_dir: Path,
    bundle_root: Path,
) -> Mapping[str, Any]:
    candidates = []
    if explicit_path is not None:
        candidates.append(explicit_path)
    candidates.extend(
        [
            data_dir / "public_network_config.json",
            bundle_root / "public_network_config.json",
        ]
    )
    for path in candidates:
        if path.is_file():
            return _load_json_object(path)
    raise ValueError("network config not found; pass --network-config")


def _validated_network_config_hash(config: Mapping[str, Any]) -> str:
    config_hash = config.get("network_config_hash")
    expected_hash = _public_network_config_hash_v0(config)
    if config_hash is not None and config_hash != expected_hash:
        raise ValueError("public network config hash mismatch")
    return expected_hash


def _git_commit_sha() -> str | None:
    try:
        proc = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=ROOT,
            check=False,
            capture_output=True,
            text=True,
            timeout=5,
        )
    except Exception:
        return None
    commit = proc.stdout.strip()
    return commit if proc.returncode == 0 and commit else None


def _local_tip(*, data_dir: Path, status: Mapping[str, Any]) -> dict[str, Any]:
    live_state_path = data_dir / "live_state.json"
    if live_state_path.is_file():
        live_state = _load_json_object(live_state_path)
        return {
            "height": int(live_state["latest_height"]),
            "header_hash": str(live_state["latest_header_hash"]),
            "app_hash": str(live_state["latest_app_hash"]),
        }
    return {
        "height": int(status["latest_height"]),
        "header_hash": str(status["last_header_hash"]),
        "app_hash": str(status["last_app_hash"]),
    }


def _verify_node_range(
    *,
    data_dir: Path,
    status: Mapping[str, Any],
    tip_height: int,
) -> dict[str, Any]:
    bootstrap_latest = int(status["latest_height"])
    bundle_root = Path(str(status["bundle_root"]))
    with tempfile.TemporaryDirectory(prefix="zeno-ledger-node-evidence-") as tmp:
        tmp_root = Path(tmp)
        headers_dir = tmp_root / "headers"
        bodies_dir = tmp_root / "bodies"
        checkpoints_dir = tmp_root / "checkpoints"
        headers_dir.mkdir()
        bodies_dir.mkdir()
        checkpoints_dir.mkdir()
        for height in range(1, tip_height + 1):
            source_root = (
                bundle_root / "bootstrap" / "ledger"
                if height <= bootstrap_latest
                else data_dir / "live_ledger"
            )
            _copy_height_artifact(source_root / "headers" / f"{height}.json", headers_dir)
            _copy_height_artifact(source_root / "bodies" / f"{height}.json", bodies_dir)
            _copy_height_artifact(source_root / "checkpoints" / f"{height}.json", checkpoints_dir)
        return verify_zeno_ledger_v0(
            headers_dir=headers_dir,
            bodies_dir=bodies_dir,
            checkpoints_dir=checkpoints_dir,
            profile_path=None,
            from_height=1,
            to_height=tip_height,
            trusted_prev_header_hash=ZERO_ROOT,
            mode=STRUCTURAL_DIAGNOSTIC_MODE,
        )


def _copy_height_artifact(source: Path, dest_dir: Path) -> None:
    if not source.is_file():
        raise ValueError(f"missing node ledger artifact: {source}")
    shutil.copyfile(source, dest_dir / source.name)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data-dir", required=True, type=Path)
    parser.add_argument("--network-config", type=Path)
    parser.add_argument("--machine-out", required=True, type=Path)
    parser.add_argument("--attestation-out", required=True, type=Path)
    parser.add_argument("--commit-sha")
    parser.add_argument("--observed-time-ms", type=int)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)

    report = build_node_evidence_input_v0(
        data_dir=args.data_dir,
        network_config_path=args.network_config,
        machine_out=args.machine_out,
        attestation_out=args.attestation_out,
        commit_sha=args.commit_sha,
        observed_time_ms=args.observed_time_ms,
    )
    print(json.dumps(report, indent=2 if args.pretty else None, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
