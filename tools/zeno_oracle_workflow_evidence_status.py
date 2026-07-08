#!/usr/bin/env python3
"""Check the public ZenoOracle workflow-evidence lanes."""

from __future__ import annotations

import argparse
import importlib.util
import json
import sys
import tempfile
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
TOOLS = ROOT / "tools"
if str(TOOLS) not in sys.path:
    sys.path.insert(1, str(TOOLS))
MORPH = ROOT / "external" / "Morph"
if MORPH.is_dir() and str(MORPH) not in sys.path:
    sys.path.append(str(MORPH))

SCHEMA = "zenodex.oracle.workflow_evidence_status.v1"


def _artifact_case(
    lane_id: str,
    *,
    files: list[str],
    replay_command: str,
    evidence_class: str,
) -> dict[str, Any]:
    missing = [path for path in files if not (ROOT / path).exists()]
    return {
        "lane_id": lane_id,
        "status": "accepted" if not missing else "rejected",
        "ok": not missing,
        "evidence_class": evidence_class,
        "replay_command": replay_command,
        "files": files,
        "missing_files": missing,
    }


def _morph_case() -> dict[str, Any]:
    files = [
        "tests/morph_domains/oracle_clamp_envelope_domain.py",
        "tools/perp_oracle_manipulation_lp_sweep.py",
    ]
    missing = [path for path in files if not (ROOT / path).exists()]
    errors: list[str] = []
    check = None
    check2 = None
    if not missing:
        try:
            from morph.domain import Goal, ProblemState, Representation
            from morph.triviality_safe import CheckResult

            domain_path = ROOT / files[0]
            spec = importlib.util.spec_from_file_location(
                "zeno_oracle_oracle_clamp_envelope_domain",
                domain_path,
            )
            if spec is None or spec.loader is None:
                raise RuntimeError(f"could not load Morph domain at {domain_path}")
            module = importlib.util.module_from_spec(spec)
            sys.modules[spec.name] = module
            spec.loader.exec_module(module)
            OracleClampEnvelopeDomain = module.OracleClampEnvelopeDomain

            sigma = {
                "schema": "zenodex/oracle-clamp-envelope-sigma0/v1",
                "reserve_base": 100_000,
                "reserve_quote_values": [100_000],
                "fee_bps_values": [30],
                "protocol_fee_share_values": [5_000],
                "lp_share_bps": 5_000,
                "max_r": 1,
                "max_pos_abs": 1,
                "target_profit_quote": 1,
                "protocol_fee_rounding": "ceil",
                "min_claimed_points": 1,
                "max_r_check2": 1,
                "max_pos_abs_check2": 1,
            }
            rule = {
                "schema": "zenodex/oracle-clamp-envelope-rule/v1",
                "rq_le_200": 200,
                "base_bound": 0,
                "pfs_low_threshold": 5_000,
                "fee_hi_threshold": 30,
                "rq_ge_fee_hi": 17_000,
                "rq_ge_high": 24_000,
                "tight_bound": 0,
                "tighten_fee_hi": True,
                "tighten_high_rq": True,
                "tighten_requires_low_pfs": True,
            }
            state = ProblemState(
                Goal("oracle clamp envelope smoke"),
                (),
                (),
                Representation(json.dumps(sigma, sort_keys=True)),
                (),
                (),
            )
            domain = OracleClampEnvelopeDomain()
            check = domain.check(state, json.dumps(rule, sort_keys=True))
            check2 = domain.check2(state, json.dumps(rule, sort_keys=True))
            if check != CheckResult.PASS:
                errors.append(f"morph_check_failed:{check}")
            if check2 != CheckResult.PASS:
                errors.append(f"morph_check2_failed:{check2}")
        except Exception as exc:  # pragma: no cover - exercised when Morph is unavailable.
            errors.append(f"morph_smoke_failed:{type(exc).__name__}:{exc}")
    ok = not missing and not errors
    return {
        "lane_id": "morph_oracle_clamp_envelope_smoke",
        "status": "accepted" if ok else "rejected",
        "ok": ok,
        "evidence_class": "morph_domain_smoke",
        "replay_command": "python3 tools/zeno_oracle_workflow_evidence_status.py --format text",
        "files": files,
        "missing_files": missing,
        "check": None if check is None else str(check),
        "check2": None if check2 is None else str(check2),
        "errors": errors,
    }


def build_morph_oracle_clamp_envelope_status() -> dict[str, Any]:
    lane = _morph_case()
    lane_ok = lane.get("ok") is True
    return {
        "schema": "zenodex.oracle.morph_oracle_clamp_envelope_replay.v1",
        "ok": lane_ok,
        "status": "accepted" if lane_ok else "rejected",
        "lane": lane,
    }


def _popperpad_case() -> dict[str, Any]:
    files = ["tools/popper_pad.py"]
    missing = [path for path in files if not (ROOT / path).exists()]
    errors: list[str] = []
    summary: dict[str, Any] | None = None
    if not missing:
        try:
            from tools.popper_pad import PopperPad

            with tempfile.TemporaryDirectory(prefix="zeno-oracle-popperpad-") as tmp:
                pad = PopperPad(Path(tmp) / "pad.jsonl")
                hyp = pad.add_hypothesis(
                    claim="ZenoOracle workflow status checker rejects missing replay evidence",
                    test="Run zeno_oracle_workflow_evidence_status and require ok true",
                    domain="zeno-oracle",
                    agent="workflow-status",
                )
                pad.falsify(
                    hyp,
                    counterexample="temporary negative-evidence smoke entry",
                    agent="workflow-status",
                    evidence_path="tools/zeno_oracle_workflow_evidence_status.py",
                )
                summary = pad.summary()
                if int(summary.get("total_entries", 0)) != 2:
                    errors.append("popperpad_append_count_mismatch")
        except Exception as exc:  # pragma: no cover
            errors.append(f"popperpad_smoke_failed:{type(exc).__name__}:{exc}")
    ok = not missing and not errors
    return {
        "lane_id": "popperpad_append_only_smoke",
        "status": "accepted" if ok else "rejected",
        "ok": ok,
        "evidence_class": "temporary_pad_smoke",
        "replay_command": "python3 tools/zeno_oracle_workflow_evidence_status.py --format text",
        "files": files,
        "missing_files": missing,
        "summary": summary,
        "errors": errors,
        "non_claims": ["does_not_publish_internal_popperpad_entries"],
    }


def build_status() -> dict[str, Any]:
    lanes = [
        _artifact_case(
            "tla_oracle_recovery_lifecycle",
            files=[
                "formal/tla/OracleRecoveryLifecycle.tla",
                "formal/tla/OracleRecoveryLifecycle.cfg",
                "tests/formal/test_tla_oracle_recovery_lifecycle.py",
            ],
            replay_command="PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q -p no:cacheprovider tests/formal/test_tla_oracle_recovery_lifecycle.py",
            evidence_class="tla_public_replay",
        ),
        _artifact_case(
            "ltlf_oracle_recovery",
            files=[
                "formal/ltlf/oracle_recovery_ltlf_v1.yaml",
                "formal/ltlf/oracle_recovery_goal_family_v1.json",
                "tests/formal/test_oracle_recovery_ltlf.py",
            ],
            replay_command="PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q -p no:cacheprovider tests/formal/test_oracle_recovery_ltlf.py",
            evidence_class="ltlf_public_replay",
        ),
        _artifact_case(
            "esso_zusd_oracle_recovery_lifecycle",
            files=[
                "src/kernels/dex/zusd_oracle_recovery_lifecycle_v1.yaml",
                "tests/formal/test_esso_zusd_oracle_recovery_lifecycle_v1.py",
            ],
            replay_command="PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q -p no:cacheprovider tests/formal/test_esso_zusd_oracle_recovery_lifecycle_v1.py",
            evidence_class="esso_public_replay",
        ),
        _popperpad_case(),
    ]
    failed = [lane for lane in lanes if not lane["ok"]]
    return {
        "schema": SCHEMA,
        "ok": not failed,
        "status": "accepted" if not failed else "rejected",
        "lane_count": len(lanes),
        "accepted_lane_count": len(lanes) - len(failed),
        "failed_lane_count": len(failed),
        "lanes": lanes,
        "external_research_lanes": [
            {
                "lane_id": "morph_oracle_clamp_envelope_smoke",
                "evidence_class": "morph_domain_smoke",
                "status": "external_not_required",
                "reason": "Morph is an external research tool and is not a ZenoDEX runtime or release dependency",
                "replay_command": "run from a separate Morph checkout when doing research review",
            }
        ],
        "non_claims": [
            "does_not_claim_internal_popperpad_publication",
            "does_not_claim_external_morph_execution",
            "does_not_claim_external_tla_ltlf_esso_execution",
            "does_not_claim_production_oracle_truth",
        ],
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--format", choices=("json", "text"), default="json")
    parser.add_argument("--output")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    status = build_status()
    text = json.dumps(status, indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(text, encoding="utf-8")
    if args.format == "json":
        sys.stdout.write(text)
    else:
        sys.stdout.write(
            "\n".join(
                [
                    f"lane_count = {status['lane_count']}",
                    f"accepted_lane_count = {status['accepted_lane_count']}",
                    f"failed_lane_count = {status['failed_lane_count']}",
                    f"status = {status['status']}",
                ]
            )
            + "\n"
        )
    return 0 if status["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
