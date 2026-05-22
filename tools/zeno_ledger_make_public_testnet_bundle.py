#!/usr/bin/env python3
"""Build and execute a ZenoLedger public-testnet candidate bundle."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Any, Mapping, Sequence

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.zeno_ledger_testnet_status import (
    build_testnet_status_v0,
    validate_testnet_status_v0,
)
from tools.zeno_ledger_make_core_feature_suite import build_core_feature_suite_v0
from tools.zeno_ledger_make_testnet_bundle import (
    DEFAULT_ASSET0,
    DEFAULT_ASSET1,
    DEFAULT_CHAIN_ID,
    DEFAULT_SEQUENCER_ID,
    DEFAULT_TIME_MS,
    build_testnet_bundle_v0,
)
from tools.operator_report_output import operator_json_dumps, public_storage_json_dumps


REPORT_SCHEMA = "zenodex.zeno_ledger.make_public_testnet_bundle_report.v0"
LAUNCH_MANIFEST_SCHEMA = "zenodex.zeno_ledger.public_testnet_bundle.v0"
RUN_MANIFEST_SCRIPT = ROOT / "tools" / "zeno_ledger_run_manifest.py"
RUN_FEATURE_SUITE_SCRIPT = ROOT / "tools" / "zeno_ledger_run_feature_suite.py"


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(public_storage_json_dumps(value) + "\n", encoding="utf-8")


def _load_json_object(path: Path) -> Mapping[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError(f"{path} must decode to a JSON object")
    return obj


def _rel(root: Path, path: Path) -> str:
    return path.resolve().relative_to(root.resolve()).as_posix()


def _resolve_relative_to(path_text: object, *, root: Path, name: str) -> Path:
    if not isinstance(path_text, str) or path_text == "":
        raise ValueError(f"{name} must be a non-empty string")
    path = Path(path_text)
    if path.is_absolute():
        return path
    if ".." in path.parts:
        raise ValueError(f"{name} must not escape its bundle root")
    return root / path


def _run_command(command: Sequence[str], *, cwd: Path) -> dict[str, Any]:
    proc = subprocess.run(
        list(command),
        cwd=cwd,
        text=True,
        capture_output=True,
    )
    stdout_json: object | None = None
    if proc.stdout.strip():
        try:
            stdout_json = json.loads(proc.stdout)
        except json.JSONDecodeError:
            stdout_json = None
    return {
        "command": list(command),
        "returncode": int(proc.returncode),
        "stdout_json": stdout_json,
        "stderr": proc.stderr,
    }


def _require_ok_report(report: Mapping[str, Any], *, name: str) -> Mapping[str, Any]:
    if report.get("returncode") != 0:
        raise RuntimeError(f"{name} command failed")
    stdout_json = report.get("stdout_json")
    if not isinstance(stdout_json, Mapping) or stdout_json.get("ok") is not True:
        raise RuntimeError(f"{name} command did not return ok=true")
    return stdout_json


def build_public_testnet_bundle_v0(
    *,
    out_dir: Path,
    network_id: str,
    chain_id: str,
    sequencer_id: str,
    time_ms: int,
    token_symbol: str,
) -> dict[str, Any]:
    bootstrap_dir = out_dir / "bootstrap"
    core_suite_dir = out_dir / "core_features"
    launch_manifest_path = out_dir / "public_testnet_manifest.json"
    bootstrap_run_report_path = out_dir / "bootstrap_run_report.json"
    core_suite_build_report_path = out_dir / "core_suite_build_report.json"
    core_suite_run_report_path = out_dir / "core_suite_run_report.json"
    testnet_status_path = out_dir / "testnet_status.json"

    bootstrap_build_report = build_testnet_bundle_v0(
        out_dir=bootstrap_dir,
        chain_id=chain_id,
        sequencer_id=sequencer_id,
        time_ms=time_ms,
        token_symbol=token_symbol,
        proof_required=False,
    )
    bootstrap_manifest_path = Path(str(bootstrap_build_report["manifest_path"]))
    bootstrap_run_command = [
        "python3",
        "tools/zeno_ledger_run_manifest.py",
        "--manifest",
        str(bootstrap_manifest_path),
        "--cwd",
        str(ROOT),
    ]
    bootstrap_run_report = _run_command(bootstrap_run_command, cwd=ROOT)
    _write_json(bootstrap_run_report_path, bootstrap_run_report)
    _require_ok_report(bootstrap_run_report, name="bootstrap run")

    core_suite_build_report = build_core_feature_suite_v0(
        out_dir=core_suite_dir,
        chain_id=chain_id,
        sequencer_id=sequencer_id,
        time_ms=time_ms + 100_000,
        token_symbol=token_symbol,
    )
    _write_json(core_suite_build_report_path, core_suite_build_report)
    core_suite_path = Path(str(core_suite_build_report["suite_path"]))
    core_suite_run_command = [
        "python3",
        "tools/zeno_ledger_run_feature_suite.py",
        "--suite",
        str(core_suite_path),
        "--cwd",
        str(ROOT),
    ]
    core_suite_run_report = _run_command(core_suite_run_command, cwd=ROOT)
    core_suite_run_stdout = _require_ok_report(core_suite_run_report, name="core feature suite run")
    _write_json(core_suite_run_report_path, core_suite_run_stdout)

    bootstrap_manifest = _load_json_object(bootstrap_manifest_path)
    token_asset_id = str(bootstrap_manifest["token_asset_id"])
    mirror_index_path = _resolve_relative_to(
        bootstrap_manifest.get("mirror_index_path"),
        root=bootstrap_manifest_path.parent,
        name="bootstrap_manifest.mirror_index_path",
    )
    watcher_attestation_path = _resolve_relative_to(
        bootstrap_manifest.get("attestation_path"),
        root=bootstrap_manifest_path.parent,
        name="bootstrap_manifest.attestation_path",
    )
    mirror_index = _load_json_object(mirror_index_path)
    watcher_attestation = _load_json_object(watcher_attestation_path)
    feature_suite = _load_json_object(core_suite_path)
    testnet_status = build_testnet_status_v0(
        network_id=network_id,
        mirror_index=mirror_index,
        mirror_root=bootstrap_dir,
        watcher_attestations=[watcher_attestation],
        feature_suite=feature_suite,
        feature_suite_run_report=core_suite_run_stdout,
    )
    _write_json(testnet_status_path, testnet_status)
    validate_testnet_status_v0(
        status=testnet_status,
        mirror_index=mirror_index,
        mirror_root=bootstrap_dir,
        watcher_attestations=[watcher_attestation],
        feature_suite=feature_suite,
        feature_suite_run_report=core_suite_run_stdout,
    )

    launch_manifest = {
        "schema": LAUNCH_MANIFEST_SCHEMA,
        "network_id": network_id,
        "chain_id": chain_id,
        "sequencer_id": sequencer_id,
        "token_symbol": token_symbol,
        "bootstrap_manifest_path": _rel(out_dir, bootstrap_manifest_path),
        "bootstrap_run_command": [
            "python3",
            "tools/zeno_ledger_run_manifest.py",
            "--manifest",
            _rel(out_dir, bootstrap_manifest_path),
            "--cwd",
            ".",
        ],
        "bootstrap_run_report_path": _rel(out_dir, bootstrap_run_report_path),
        "core_suite_path": _rel(out_dir, core_suite_path),
        "core_suite_run_command": [
            "python3",
            "tools/zeno_ledger_run_feature_suite.py",
            "--suite",
            _rel(out_dir, core_suite_path),
            "--cwd",
            ".",
        ],
        "core_suite_build_report_path": _rel(out_dir, core_suite_build_report_path),
        "core_suite_run_report_path": _rel(out_dir, core_suite_run_report_path),
        "testnet_status_path": _rel(out_dir, testnet_status_path),
        "testnet_status_hash": testnet_status["testnet_status_hash"],
        "covered_features": core_suite_run_stdout["covered_features"],
        "tau_posture": {
            "preferred_release_adapter": "tau_net",
            "current_status": "handoff_adapter_available",
            "testnet_liveness_dependency": "zeno_ledger",
        },
        "token_posture": {
            "testnet_scope": "zeno_ledger_testnet",
            "release_scope": "tau_net_exclusive",
            "external_minting_allowed": False,
        },
        "test_token_catalog": [
            {
                "symbol": token_symbol,
                "asset_id": token_asset_id,
                "purpose": "testnet ZenoDEX accounting token",
            },
            {
                "symbol": "tASSET0",
                "asset_id": DEFAULT_ASSET0,
                "purpose": "deterministic spot and feature-suite asset",
            },
            {
                "symbol": "tASSET1",
                "asset_id": DEFAULT_ASSET1,
                "purpose": "deterministic spot and feature-suite asset",
            },
        ],
        "testnet_faucet_posture": {
            "scope": "testnet_only",
            "operation_key": "7",
            "supports_fixture_mint": True,
            "supports_token_ops": True,
        },
    }
    _write_json(launch_manifest_path, launch_manifest)

    return {
        "schema": REPORT_SCHEMA,
        "ok": True,
        "status": "accepted",
        "network_id": network_id,
        "chain_id": chain_id,
        "launch_manifest_path": str(launch_manifest_path),
        "bootstrap_manifest_path": str(bootstrap_manifest_path),
        "core_suite_path": str(core_suite_path),
        "core_suite_run_report_path": str(core_suite_run_report_path),
        "testnet_status_path": str(testnet_status_path),
        "testnet_status_hash": testnet_status["testnet_status_hash"],
        "covered_feature_count": len(core_suite_run_stdout["covered_features"]),
        "covered_features": core_suite_run_stdout["covered_features"],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Build and execute a public ZenoLedger testnet candidate bundle")
    parser.add_argument("--out-dir", required=True, type=Path)
    parser.add_argument("--network-id", default=DEFAULT_CHAIN_ID)
    parser.add_argument("--chain-id", default=DEFAULT_CHAIN_ID)
    parser.add_argument("--sequencer-id", default=DEFAULT_SEQUENCER_ID)
    parser.add_argument("--time-ms", type=int, default=DEFAULT_TIME_MS)
    parser.add_argument("--token-symbol", default="tZENO")
    args = parser.parse_args(argv)

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
        report = {
            "schema": REPORT_SCHEMA,
            "ok": False,
            "status": "rejected",
            "errors": [str(exc)],
        }
    print(operator_json_dumps(report))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
