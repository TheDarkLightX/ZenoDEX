#!/usr/bin/env python3
"""Run every feature lane listed in a ZenoLedger feature-suite manifest."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.zeno_ledger_feature_suite import validate_feature_suite_manifest_v0


REPORT_SCHEMA = "zenodex.zeno_ledger.run_feature_suite_report.v0"
RUN_MANIFEST_SCRIPT = ROOT / "tools" / "zeno_ledger_run_manifest.py"


def _load_json_object(path: Path) -> Mapping[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError(f"{path} must decode to a JSON object")
    return obj


def _resolve_suite_path(path_text: str, *, suite_base_dir: Path) -> Path:
    path = Path(path_text)
    if path.is_absolute():
        return path
    if path_text == "" or ".." in path.parts:
        raise ValueError(f"unsafe feature lane path: {path_text}")
    return suite_base_dir / path


def _run_lane_manifest(path: Path, *, cwd: Path) -> dict[str, Any]:
    proc = subprocess.run(
        [
            sys.executable,
            str(RUN_MANIFEST_SCRIPT),
            "--manifest",
            str(path),
            "--cwd",
            str(cwd),
        ],
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
        "command": [
            sys.executable,
            str(RUN_MANIFEST_SCRIPT),
            "--manifest",
            str(path),
            "--cwd",
            str(cwd),
        ],
        "returncode": proc.returncode,
        "stdout_json": stdout_json,
        "stderr": proc.stderr,
    }


def run_feature_suite_v0(*, suite_path: Path, cwd: Path) -> dict[str, Any]:
    suite = dict(_load_json_object(suite_path))
    suite_base_dir = suite_path.parent
    validate_feature_suite_manifest_v0(suite, base_dir=suite_base_dir)
    lane_reports: list[dict[str, Any]] = []
    covered_features: list[str] = []
    for feature in suite["features"]:
        feature_id = str(feature["feature_id"])
        manifest_path = _resolve_suite_path(str(feature["manifest_path"]), suite_base_dir=suite_base_dir)
        lane_report = _run_lane_manifest(manifest_path, cwd=cwd)
        stdout_json = lane_report.get("stdout_json")
        lane_ok = lane_report["returncode"] == 0 and isinstance(stdout_json, dict) and stdout_json.get("ok") is True
        lane_reports.append(
            {
                "feature_id": feature_id,
                "manifest_path": str(manifest_path),
                "ok": lane_ok,
                "run_report": lane_report,
            }
        )
        if not lane_ok:
            raise RuntimeError(f"feature lane failed: {feature_id}")
        covered_features.append(feature_id)
    return {
        "schema": REPORT_SCHEMA,
        "ok": True,
        "status": "accepted",
        "suite_path": str(suite_path),
        "feature_suite_hash": suite["feature_suite_hash"],
        "covered_features": covered_features,
        "lane_reports": lane_reports,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run a ZenoLedger feature-suite manifest")
    parser.add_argument("--suite", required=True, type=Path)
    parser.add_argument("--cwd", type=Path, default=Path.cwd())
    args = parser.parse_args(argv)

    try:
        report = run_feature_suite_v0(suite_path=args.suite, cwd=args.cwd)
    except Exception as exc:
        report = {
            "schema": REPORT_SCHEMA,
            "ok": False,
            "status": "rejected",
            "errors": [str(exc)],
        }
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
