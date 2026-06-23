from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Sequence


REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.fire.registry.bundle_v1 import load_fire_registry_bundle  # noqa: E402
from src.fire.registry.replay_input_v1 import load_fire_replay_input  # noqa: E402
from src.fire.verifier.settlement_v1 import fire_witness_binding_hash  # noqa: E402

APPLY_CLI = REPO_ROOT / "tools" / "apply_fire_settlement.py"
CHECK_ARTIFACT_RECEIPT_CLI = REPO_ROOT / "tools" / "check_fire_settlement_apply_artifact_receipt.py"
CHECK_OBJECT_PACKAGE_CLI = REPO_ROOT / "tools" / "check_fire_object_package.py"
CHECK_REPORT_SCHEMA = "zenodex/fire-settlement-replay-gate-check-report/v1"

_REPLAY_CASES: tuple[dict[str, object], ...] = (
    {
        "case_id": "burn_boost_call_v1",
        "bundle_dir_name": "burn_boost_call_v1",
        "default_balances": {"holder": 100, "writer": 250},
        "witness_flags": (
            ("--witness-final", "BurnCertificate[TDEX]"),
        ),
    },
    {
        "case_id": "fee_note_v1",
        "bundle_dir_name": "fee_note_v1",
        "default_balances": {"holder": 40, "writer": 90},
        "witness_flags": (
            ("--witness-final", "FeeIndexPacket"),
        ),
    },
    {
        "case_id": "lp_loss_cover_v1",
        "bundle_dir_name": "lp_loss_cover_v1",
        "default_balances": {"holder": 80, "writer": 200},
        "witness_flags": (
            ("--witness-hodl-final", "HODLValuePacket"),
            ("--witness-lpv-final", "LPValuePacket"),
        ),
    },
)


def _derived_manifest_args(
    bundle_dir: Path,
    case: dict[str, object],
    *,
    require_bundle_replay_input: bool,
) -> tuple[list[str], dict[str, int], str]:
    bundle_manifest, _, object_manifest, object_instance, _ = load_fire_registry_bundle(bundle_dir)
    if bundle_manifest.replay_input_path is not None:
        replay_input, _ = load_fire_replay_input(bundle_dir / bundle_manifest.replay_input_path)
        flag_by_runtime_key = {
            flag.removeprefix("--").replace("-", "_"): flag
            for flag, _witness_name in case.get("witness_flags", ())
        }
        args = [
            "--holder-posted",
            str(replay_input.holder_posted),
            "--writer-posted",
            str(replay_input.writer_posted),
            "--holder-balance",
            str(replay_input.holder_balance),
            "--writer-balance",
            str(replay_input.writer_balance),
        ]
        for runtime_key, value in replay_input.witness_inputs.items():
            flag_name = flag_by_runtime_key[runtime_key]
            args.extend([flag_name, str(value)])
        return (
            args,
            dict(replay_input.witness_inputs),
            "bundle",
        )
    if require_bundle_replay_input:
        raise ValueError("bundle_replay_input_required")
    witness_bounds = {item.name: item.lower for item in object_manifest.witnesses}
    witness_values: dict[str, int] = {}
    for flag_name, witness_name in case.get("witness_flags", ()):
        lower_bound = witness_bounds[witness_name]
        witness_values[str(flag_name)] = int(lower_bound)

    args = [
        "--holder-posted",
        str(object_manifest.holder_collateral_required),
        "--writer-posted",
        str(object_manifest.writer_collateral_required),
        "--holder-balance",
        str(dict(case["default_balances"])["holder"]),
        "--writer-balance",
        str(dict(case["default_balances"])["writer"]),
    ]
    for flag_name, witness_name in case.get("witness_flags", ()):
        args.extend([str(flag_name), str(witness_values[str(flag_name)])])
    normalized_witness_values = {
        str(flag_name).removeprefix("--").replace("-", "_"): value
        for flag_name, value in witness_values.items()
    }
    return args, normalized_witness_values, "fallback"


def _run_json(cmd: list[str]) -> tuple[bool, dict[str, object] | None, str | None]:
    proc = subprocess.run(
        cmd,
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    raw = proc.stdout if proc.returncode == 0 else proc.stderr
    try:
        payload = json.loads(raw) if raw else None
    except json.JSONDecodeError:
        payload = None
    if proc.returncode != 0:
        detail = raw.strip() or f"command failed: {' '.join(cmd)}"
        return False, payload, detail
    return True, payload, None


def _run_case(
    snapshot_dir: Path,
    output_dir: Path,
    case: dict[str, object],
    *,
    require_bundle_replay_input: bool,
) -> tuple[bool, dict[str, object]]:
    case_id = str(case["case_id"])
    bundle_dir = snapshot_dir / str(case["bundle_dir_name"])
    case_out = output_dir / case_id
    case_out.mkdir(parents=True, exist_ok=True)
    report_path = case_out / "apply_report.json"
    receipt_path = case_out / "apply_artifact_receipt.json"
    try:
        manifest_args, witness_values, replay_input_source = _derived_manifest_args(
            bundle_dir,
            case,
            require_bundle_replay_input=require_bundle_replay_input,
        )
    except (FileNotFoundError, OSError, KeyError, TypeError, ValueError) as exc:
        return False, {
            "case_id": case_id,
            "ok": False,
            "bundle_dir": str(bundle_dir.resolve()),
            "error": f"bundle_inputs_unavailable:{exc}",
        }

    package_check_cmd = [
        sys.executable,
        str(CHECK_OBJECT_PACKAGE_CLI),
        "--bundle-dir",
        str(bundle_dir),
    ]
    ok, package_payload, package_err = _run_json(package_check_cmd)
    if not ok or not isinstance(package_payload, dict):
        return False, {
            "case_id": case_id,
            "ok": False,
            "bundle_dir": str(bundle_dir.resolve()),
            "error": package_err or "object_package_check_failed",
        }

    apply_cmd = [
        sys.executable,
        str(APPLY_CLI),
        "--bundle-dir",
        str(bundle_dir),
        *manifest_args,
        "--output-report-file",
        str(report_path),
        "--output-artifact-receipt-file",
        str(receipt_path),
    ]
    ok, apply_payload, apply_err = _run_json(apply_cmd)
    if not ok or not isinstance(apply_payload, dict):
        return False, {
            "case_id": case_id,
            "ok": False,
            "bundle_dir": str(bundle_dir.resolve()),
            "error": apply_err or "apply_failed",
        }

    expected_witness_hash = fire_witness_binding_hash(witness_values)
    check_cmd = [
        sys.executable,
        str(CHECK_ARTIFACT_RECEIPT_CLI),
        "--receipt-file",
        str(receipt_path),
        "--expected-bundle-dir",
        str(bundle_dir),
        "--expected-witness-hash",
        expected_witness_hash,
    ]
    ok, check_payload, check_err = _run_json(check_cmd)
    if not ok or not isinstance(check_payload, dict):
        return False, {
            "case_id": case_id,
            "ok": False,
            "bundle_dir": str(bundle_dir.resolve()),
            "apply_report_path": str(report_path.resolve()),
            "apply_artifact_receipt_path": str(receipt_path.resolve()),
            "error": check_err or "artifact_receipt_check_failed",
        }

    return True, {
        "case_id": case_id,
        "ok": True,
        "bundle_dir": str(bundle_dir.resolve()),
        "apply_report_path": str(report_path.resolve()),
        "apply_artifact_receipt_path": str(receipt_path.resolve()),
        "package_check_ok": True,
        "derived_witness_values": witness_values,
        "replay_input_source": replay_input_source,
        "report_hash": apply_payload.get("report_hash"),
        "bundle_hash": check_payload.get("bundle_hash"),
        "object_hash": check_payload.get("object_hash"),
        "instance_hash": check_payload.get("instance_hash"),
        "cert_sha256": check_payload.get("cert_sha256"),
        "witness_hash": check_payload.get("witness_hash"),
        "expected_witness_hash": expected_witness_hash,
        "holder_delta": apply_payload.get("holder_delta"),
        "writer_delta": apply_payload.get("writer_delta"),
        "artifact_schemas_valid": package_payload.get("artifact_schemas_valid"),
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Replay-check pinned FIRE settlement cases against expected bundle dirs.")
    parser.add_argument(
        "--snapshot-dir",
        type=Path,
        default=REPO_ROOT / "docs" / "fire_registry" / "devnet_v1",
        help="Snapshot directory containing FIRE bundle subdirectories",
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=REPO_ROOT / "internal" / "release_artifacts" / "fire_settlement_replay_gate",
        help="Directory where apply reports and artifact receipts will be written",
    )
    parser.add_argument(
        "--require-bundle-replay-input",
        action="store_true",
        help="Fail closed if any bundle lacks canonical replay_input.json",
    )
    parser.add_argument("--pretty", action="store_true", help="Pretty-print the JSON report")
    args = parser.parse_args(argv)

    args.output_dir.mkdir(parents=True, exist_ok=True)
    case_reports: list[dict[str, object]] = []
    all_ok = True
    for case in _REPLAY_CASES:
        ok, report = _run_case(
            args.snapshot_dir,
            args.output_dir,
            case,
            require_bundle_replay_input=args.require_bundle_replay_input,
        )
        all_ok = all_ok and ok
        case_reports.append(report)

    payload = {
        "schema": CHECK_REPORT_SCHEMA,
        "ok": all_ok,
        "snapshot_dir": str(args.snapshot_dir.resolve()),
        "output_dir": str(args.output_dir.resolve()),
        "require_bundle_replay_input": args.require_bundle_replay_input,
        "case_count": len(case_reports),
        "cases": case_reports,
    }
    rendered = json.dumps(payload, indent=2 if args.pretty else None, sort_keys=True)
    stream = sys.stdout if all_ok else sys.stderr
    stream.write(rendered + "\n")
    return 0 if all_ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
