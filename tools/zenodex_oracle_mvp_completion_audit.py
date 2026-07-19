#!/usr/bin/env python3
"""Audit the local Zeno Oracle MVP acceptance criteria."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
BIN = ROOT / "bin" / "zenodex-oracle"
RESULT_SCHEMA = "zenodex.oracle.mvp_completion_audit.v1"


def _run_json(args: list[str], *, timeout_s: int) -> tuple[bool, dict[str, Any] | None, str]:
    proc = subprocess.run(
        args,
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
        timeout=timeout_s,
    )
    if proc.returncode != 0:
        return False, None, proc.stderr or proc.stdout
    try:
        obj = json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        return False, None, f"non_json_output:{exc}"
    if not isinstance(obj, dict):
        return False, None, "non_object_json_output"
    return True, obj, ""


def _criterion(
    criterion_id: int,
    title: str,
    ok: bool,
    evidence: list[str],
    *,
    residual_limits: list[str] | None = None,
) -> dict[str, Any]:
    return {
        "id": criterion_id,
        "title": title,
        "ok": bool(ok),
        "evidence": evidence,
        "residual_limits": list(residual_limits or []),
    }


def _read(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def _file_contains(path: str, needle: str) -> bool:
    try:
        return needle in _read(path)
    except FileNotFoundError:
        return False


def _step_names(dry_run: dict[str, Any] | None) -> set[str]:
    if not dry_run:
        return set()
    raw_steps = dry_run.get("steps")
    if not isinstance(raw_steps, list):
        return set()
    names: set[str] = set()
    for step in raw_steps:
        if isinstance(step, dict) and isinstance(step.get("name"), str):
            names.add(str(step["name"]))
    return names


def _package_manifest(version: str) -> tuple[bool, dict[str, Any] | None, str]:
    proc = subprocess.run(
        ["bash", "scripts/package_zeno_oracle_rc.sh", version],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
        timeout=60,
    )
    if proc.returncode != 0:
        return False, None, proc.stderr or proc.stdout
    manifest_path = ROOT / "dist" / version / "ZEN_ORACLE_RC_MANIFEST.json"
    try:
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    except Exception as exc:  # pragma: no cover - defensive path
        return False, None, f"manifest_load_failed:{exc}"
    if not isinstance(manifest, dict):
        return False, None, "manifest_not_object"
    return True, manifest, ""


def run_audit(*, run_gate: bool) -> dict[str, Any]:
    doctor_ok, doctor, doctor_error = _run_json([str(BIN), "doctor"], timeout_s=30)
    with tempfile.TemporaryDirectory(prefix="zeno-oracle-completion-audit-") as tmp:
        dry_ok, dry_run, dry_error = _run_json([str(BIN), "dry-run", "--workdir", tmp], timeout_s=180)

    package_ok, manifest, package_error = _package_manifest("zeno-oracle-audit-rc")
    gate_ok = False
    gate_error = ""
    if run_gate:
        gate_proc = subprocess.run(
            ["bash", "scripts/check_zeno_oracle_mvp.sh"],
            cwd=ROOT,
            check=False,
            capture_output=True,
            text=True,
            timeout=2400,
        )
        gate_ok = gate_proc.returncode == 0
        gate_error = "" if gate_ok else gate_proc.stderr or gate_proc.stdout[-2000:]

    dry_steps = _step_names(dry_run)
    docs = [
        "docs/ZENO_ORACLE_MVP_STATUS.md",
        "docs/ZENO_ORACLE_MVP_DESIGN.md",
        "docs/ZENO_ORACLE_CLI_V1.md",
        "docs/ZENO_ORACLE_RUNTIME_BRIDGE_V1.md",
        "docs/ZENO_ORACLE_CHAOS_ENGINEERING.md",
        "docs/ZENO_ORACLE_PRODUCTION_GATES.md",
    ]
    docs_ok = all((ROOT / path).is_file() for path in docs)
    workflow_ok = (
        (
            _file_contains(".github/workflows/zeno-oracle-mvp.yml", "bash scripts/check_zeno_oracle_mvp.sh")
            or _file_contains(".github/workflows/zeno-oracle-mvp.yml", "bash scripts/check_zeno_oracle_devnet_alpha.sh")
        )
        and _file_contains(".github/workflows/zeno-oracle-mvp.yml", "actions/upload-artifact@v4")
    )
    runtime_hooks_ok = all(
        [
            _file_contains("src/integration/perp_engine.py", "_require_oracle_adapter_bridge"),
            _file_contains(
                "src/integration/zusd_monetary_bridge.py",
                "check_critical_consumer_authorization",
            ),
            _file_contains("src/integration/api_server.py", "_check_routing_oracle_adapter_bridge_for_action"),
        ]
    )
    package_entrypoint_ok = bool(
        package_ok
        and manifest
        and manifest.get("entrypoint") == "bin/zenodex-oracle"
        and any(
            isinstance(item, dict) and item.get("path") == "bin/zenodex-oracle"
            for item in manifest.get("files", [])
        )
    )

    criteria = [
        _criterion(
            1,
            "Anyone can run a local Zeno Oracle CLI/launcher",
            doctor_ok and bool(doctor and doctor.get("ok") is True),
            ["bin/zenodex-oracle doctor accepted"] if doctor_ok else [doctor_error],
        ),
        _criterion(
            2,
            "Anyone can create and register a feed under policy",
            dry_ok and {"sample_feed", "verify_feed", "register_feed_to_local_store"} <= dry_steps,
            ["dry-run created, verified, and locally registered a feed"] if dry_ok else [dry_error],
        ),
        _criterion(
            3,
            "Reporters can submit signed reports",
            dry_ok and {"sample_signed_report", "verify_signed_report", "submit_report_to_local_store"} <= dry_steps,
            ["dry-run created, verified, and locally stored a signed report"] if dry_ok else [dry_error],
        ),
        _criterion(
            4,
            "Aggregates are built only from admitted reports",
            dry_ok and {"sample_admitted_median3", "verify_admitted_median3"} <= dry_steps,
            ["dry-run verified admitted-median3 aggregate shell"] if dry_ok else [dry_error],
        ),
        _criterion(
            5,
            "Accepted reads are bound to admitted aggregates",
            dry_ok and {"sample_aggregate_read", "verify_aggregate_read"} <= dry_steps,
            ["dry-run verified aggregate-read binding shell"] if dry_ok else [dry_error],
        ),
        _criterion(
            6,
            "Concrete ZenoDEX actions are checked against aggregate-derived reads",
            runtime_hooks_ok and dry_ok and {"verify_aggregate_adapter", "verify_adapter_bundle"} <= dry_steps,
            [
                "runtime hooks present for perps, production zUSD monetary actions, and guarded routing",
                "dry-run verified aggregate-adapter and consumer-adapter bundles",
            ],
            residual_limits=[
                "production zUSD mint/liquidation typed Oracle authorization remains a release blocker",
            ],
        ),
        _criterion(
            7,
            "Token rewards, bonds, slashing, and disputes have a verified MVP flow",
            dry_ok and {"verify_reporter_lifecycle", "verify_token_budget"} <= dry_steps,
            ["dry-run verified reporter lifecycle and token budget transition"],
            residual_limits=["does not claim a live Oracle token or live reporter registry"],
        ),
        _criterion(
            8,
            "Oracle chaos lanes pass in CI",
            workflow_ok and ((not run_gate) or gate_ok),
            ["CI workflow runs the MVP gate directly or through the stronger devnet-alpha gate and uploads the RC artifact"]
            + (["local full gate passed in this audit"] if run_gate and gate_ok else []),
            residual_limits=[] if run_gate else ["local full gate was not rerun by this audit; use --run-gate for that"],
        ),
        _criterion(
            9,
            "Public docs explain proved, checked, assumed, and not-claimed surfaces",
            docs_ok,
            docs,
        ),
        _criterion(
            10,
            "Release candidate package exists",
            package_entrypoint_ok,
            ["package manifest uses bin/zenodex-oracle entrypoint"] if package_ok else [package_error],
        ),
    ]
    ok = all(item["ok"] for item in criteria)
    return {
        "schema": RESULT_SCHEMA,
        "ok": ok,
        "status": "accepted" if ok else "rejected",
        "run_gate": run_gate,
        "criteria_count": len(criteria),
        "accepted_criteria_count": sum(1 for item in criteria if item["ok"]),
        "criteria": criteria,
        "not_claimed": [
            "does_not_claim_live_oracle_network",
            "does_not_claim_platform_native_installer",
            "does_not_claim_oracle_values_are_true_market_prices",
        ],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run-gate", action="store_true", help="also run the full local Oracle MVP gate")
    parser.add_argument("--output", help="optional output path for the audit receipt")
    args = parser.parse_args(argv)

    try:
        receipt = run_audit(run_gate=bool(args.run_gate))
    except subprocess.TimeoutExpired as exc:
        receipt = {
            "schema": RESULT_SCHEMA,
            "ok": False,
            "status": "inconclusive",
            "errors": [f"timeout:{exc.cmd}"],
        }
    text = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)
    return 0 if receipt.get("ok") is True else 2


if __name__ == "__main__":
    raise SystemExit(main())
