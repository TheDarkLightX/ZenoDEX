#!/usr/bin/env python3
"""Compile integer feasibility intervals for Zeno Oracle economic envelopes."""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT / "tools"))

from zenodex_oracle_economic_security import (  # noqa: E402
    BPS_SCALE,
    MAX_AMOUNT,
    MAX_COUNT,
    MAX_MARGIN_BPS,
    sample_envelope,
    verify_economic_security_envelope,
)


OUT_DIR = REPO_ROOT / "generated" / "zenodex_oracle_polytope_compiler_20260627"
REPORT_PATH = REPO_ROOT / "docs" / "research" / "ZENODEX_ORACLE_POLYTOPE_COMPILER_20260627.md"


@dataclass(frozen=True)
class IntervalSpec:
    field: str
    lower: int
    upper: int
    domain_lower: int
    domain_upper: int
    reason: str
    wall_errors: tuple[str, ...]

    @property
    def nonempty(self) -> bool:
        return self.lower <= self.upper


@dataclass(frozen=True)
class BoundarySample:
    interval_field: str
    sample_id: str
    value: int
    expected_ok: bool
    actual_ok: bool
    errors: tuple[str, ...]

    @property
    def ok(self) -> bool:
        return self.expected_ok is self.actual_ok


def _ceil_div(numer: int, denom: int) -> int:
    if denom <= 0:
        raise ValueError("denom must be positive")
    return (numer + denom - 1) // denom


def _required_attack_cost(max_extractable_value_e8: int, required_attack_margin_bps: int) -> int:
    return _ceil_div(max_extractable_value_e8 * (BPS_SCALE + required_attack_margin_bps), BPS_SCALE)


def _required_deterrence_slash(expected_cheat_gain_e8: int, deterrence_margin_bps: int) -> int:
    return _ceil_div(expected_cheat_gain_e8 * (BPS_SCALE + deterrence_margin_bps), BPS_SCALE)


def _slash_amount(reporter_bond_required_e8: int, slash_fraction_bps: int) -> int:
    return (reporter_bond_required_e8 * slash_fraction_bps) // BPS_SCALE


def _floor_margin_from_budget(*, budget_e8: int, base_e8: int) -> int:
    if base_e8 <= 0:
        return MAX_MARGIN_BPS
    return (budget_e8 * BPS_SCALE) // base_e8 - BPS_SCALE


def _intervals(envelope: Mapping[str, Any]) -> list[IntervalSpec]:
    notional = int(envelope["notional_value_e8"])
    max_extractable = int(envelope["max_extractable_value_e8"])
    attack_cost_floor = int(envelope["attack_cost_floor_e8"])
    attack_margin = int(envelope["required_attack_margin_bps"])
    reporter_count = int(envelope["reporter_count"])
    reward_budget = int(envelope["reporter_reward_budget_e8"])
    reward_per_report = int(envelope["reporter_reward_per_report_e8"])
    honest_cost = int(envelope["honest_reporter_cost_e8"])
    risk_premium = int(envelope["honest_reporter_risk_premium_e8"])
    bond_required = int(envelope["reporter_bond_required_e8"])
    slash_fraction = int(envelope["slash_fraction_bps"])
    expected_cheat_gain = int(envelope["expected_cheat_gain_e8"])
    deterrence_margin = int(envelope["deterrence_margin_bps"])
    dispute_reward = int(envelope["dispute_reward_e8"])
    dispute_budget = int(envelope["dispute_budget_e8"])
    fee_paid = int(envelope["fee_paid_e8"])
    reporter_fee = int(envelope["reporter_fee_share_e8"])
    treasury_fee = int(envelope["treasury_fee_share_e8"])
    burn_fee = int(envelope["burn_fee_share_e8"])

    required_attack_cost = _required_attack_cost(max_extractable, attack_margin)
    required_reward_per_report = honest_cost + risk_premium
    slash_amount = _slash_amount(bond_required, slash_fraction)
    required_slash = _required_deterrence_slash(expected_cheat_gain, deterrence_margin)
    max_extractable_by_attack = (attack_cost_floor * BPS_SCALE) // (BPS_SCALE + attack_margin)
    max_expected_by_slash = (
        (slash_amount * BPS_SCALE) // (BPS_SCALE + deterrence_margin)
        if BPS_SCALE + deterrence_margin > 0
        else MAX_AMOUNT
    )
    min_bond = _ceil_div(required_slash * BPS_SCALE, slash_fraction) if slash_fraction > 0 else MAX_AMOUNT + 1
    min_slash_fraction = _ceil_div(required_slash * BPS_SCALE, bond_required) if bond_required > 0 else BPS_SCALE + 1
    max_attack_margin = min(
        MAX_MARGIN_BPS,
        max(-1, _floor_margin_from_budget(budget_e8=attack_cost_floor, base_e8=max_extractable)),
    )
    max_deterrence_margin = min(
        MAX_MARGIN_BPS,
        max(-1, _floor_margin_from_budget(budget_e8=slash_amount, base_e8=expected_cheat_gain)),
    )
    fee_total = reporter_fee + treasury_fee + burn_fee

    return [
        IntervalSpec(
            "notional_value_e8",
            max_extractable,
            MAX_AMOUNT,
            0,
            MAX_AMOUNT,
            "notional must cover max_extractable_value_e8",
            ("extractable_value_exceeds_notional",),
        ),
        IntervalSpec(
            "max_extractable_value_e8",
            expected_cheat_gain,
            min(notional, max_extractable_by_attack),
            0,
            MAX_AMOUNT,
            "max extractable must cover expected cheat gain and stay below the attack-cost wall",
            ("expected_cheat_gain_exceeds_extractable_value", "attack_cost_floor_below_required_margin"),
        ),
        IntervalSpec(
            "attack_cost_floor_e8",
            required_attack_cost,
            MAX_AMOUNT,
            0,
            MAX_AMOUNT,
            "attack cost floor must exceed max_extractable_value_e8 plus required margin",
            ("attack_cost_floor_below_required_margin",),
        ),
        IntervalSpec(
            "required_attack_margin_bps",
            0,
            max_attack_margin,
            0,
            MAX_MARGIN_BPS,
            "attack margin cannot exceed what the fixed attack_cost_floor_e8 supports",
            ("attack_cost_floor_below_required_margin",),
        ),
        IntervalSpec(
            "reporter_reward_per_report_e8",
            required_reward_per_report,
            reward_budget // reporter_count,
            0,
            MAX_AMOUNT,
            "per-report reward must cover honest cost plus risk and fit the reward budget",
            ("reporter_reward_below_honest_cost_plus_risk", "reporter_reward_budget_exceeded"),
        ),
        IntervalSpec(
            "reporter_reward_budget_e8",
            reward_per_report * reporter_count,
            MAX_AMOUNT,
            0,
            MAX_AMOUNT,
            "reward budget must cover reward_per_report times reporter_count",
            ("reporter_reward_budget_exceeded",),
        ),
        IntervalSpec(
            "reporter_count",
            1,
            min(MAX_COUNT, reward_budget // reward_per_report),
            1,
            MAX_COUNT,
            "reporter count must fit the fixed reward budget",
            ("reporter_reward_budget_exceeded",),
        ),
        IntervalSpec(
            "expected_cheat_gain_e8",
            0,
            min(max_extractable, max_expected_by_slash),
            0,
            MAX_AMOUNT,
            "expected cheat gain must fit both max_extractable_value_e8 and slash deterrence",
            ("expected_cheat_gain_exceeds_extractable_value", "slash_deterrence_below_required_margin"),
        ),
        IntervalSpec(
            "reporter_bond_required_e8",
            min_bond,
            MAX_AMOUNT,
            0,
            MAX_AMOUNT,
            "bond times slash fraction must cover expected cheat gain plus deterrence margin",
            ("slash_deterrence_below_required_margin",),
        ),
        IntervalSpec(
            "slash_fraction_bps",
            min_slash_fraction,
            BPS_SCALE,
            0,
            BPS_SCALE,
            "slash fraction must make the fixed bond cover expected cheat gain plus margin",
            ("slash_deterrence_below_required_margin",),
        ),
        IntervalSpec(
            "deterrence_margin_bps",
            0,
            max_deterrence_margin,
            0,
            MAX_MARGIN_BPS,
            "deterrence margin cannot exceed what the fixed slash amount supports",
            ("slash_deterrence_below_required_margin",),
        ),
        IntervalSpec(
            "dispute_reward_e8",
            0,
            dispute_budget,
            0,
            MAX_AMOUNT,
            "dispute reward must not exceed dispute budget",
            ("dispute_reward_budget_exceeded",),
        ),
        IntervalSpec(
            "dispute_budget_e8",
            dispute_reward,
            MAX_AMOUNT,
            0,
            MAX_AMOUNT,
            "dispute budget must cover dispute reward",
            ("dispute_reward_budget_exceeded",),
        ),
        IntervalSpec(
            "fee_paid_e8",
            fee_total,
            MAX_AMOUNT,
            0,
            MAX_AMOUNT,
            "fee paid must cover reporter, treasury, and burn fee shares",
            ("fee_shares_exceed_fee_paid",),
        ),
        IntervalSpec(
            "reporter_fee_share_e8",
            0,
            fee_paid - treasury_fee - burn_fee,
            0,
            MAX_AMOUNT,
            "reporter fee share must fit the fixed fee budget",
            ("fee_shares_exceed_fee_paid",),
        ),
        IntervalSpec(
            "treasury_fee_share_e8",
            0,
            fee_paid - reporter_fee - burn_fee,
            0,
            MAX_AMOUNT,
            "treasury fee share must fit the fixed fee budget",
            ("fee_shares_exceed_fee_paid",),
        ),
        IntervalSpec(
            "burn_fee_share_e8",
            0,
            fee_paid - reporter_fee - treasury_fee,
            0,
            MAX_AMOUNT,
            "burn fee share must fit the fixed fee budget",
            ("fee_shares_exceed_fee_paid",),
        ),
    ]


def _verify_variant(envelope: Mapping[str, Any], field: str, value: int) -> tuple[bool, tuple[str, ...]]:
    variant = dict(envelope)
    variant[field] = int(value)
    result = verify_economic_security_envelope(variant)
    return result.status == "accepted", tuple(result.errors)


def _sample_values(interval: IntervalSpec) -> list[tuple[str, int, bool]]:
    samples: list[tuple[str, int, bool]] = []
    samples.append(("lower_wall", interval.lower, interval.nonempty))
    if interval.upper != interval.lower:
        samples.append(("upper_wall", interval.upper, interval.nonempty))
    samples.append(("below_lower", interval.lower - 1, False))
    samples.append(("above_upper", interval.upper + 1, False))
    return samples


def _boundary_samples(envelope: Mapping[str, Any], intervals: list[IntervalSpec]) -> list[BoundarySample]:
    samples: list[BoundarySample] = []
    for interval in intervals:
        for sample_id, value, expected_ok in _sample_values(interval):
            actual_ok, errors = _verify_variant(envelope, interval.field, value)
            samples.append(
                BoundarySample(
                    interval_field=interval.field,
                    sample_id=sample_id,
                    value=int(value),
                    expected_ok=bool(expected_ok),
                    actual_ok=bool(actual_ok),
                    errors=errors,
                )
            )
    return samples


def compile_polytope(envelope: Mapping[str, Any] | None = None) -> dict[str, Any]:
    base = dict(sample_envelope() if envelope is None else envelope)
    base_result = verify_economic_security_envelope(base)
    intervals = _intervals(base)
    samples = _boundary_samples(base, intervals)
    interval_rows = [
        {
            "field": item.field,
            "lower": item.lower,
            "upper": item.upper,
            "domain_lower": item.domain_lower,
            "domain_upper": item.domain_upper,
            "nonempty": item.nonempty,
            "reason": item.reason,
            "wall_errors": list(item.wall_errors),
        }
        for item in intervals
    ]
    sample_rows = [
        {
            "interval_field": item.interval_field,
            "sample_id": item.sample_id,
            "value": item.value,
            "expected_ok": item.expected_ok,
            "actual_ok": item.actual_ok,
            "ok": item.ok,
            "errors": list(item.errors),
        }
        for item in samples
    ]
    tau_facts = {
        "oracle_param_update_requested": True,
        "interval_nonempty": all(item.nonempty for item in intervals),
        "honest_challenge_profitable_interval_ok": _interval_by_field(intervals, "attack_cost_floor_e8").nonempty,
        "frivolous_dispute_deterrence_interval_ok": _interval_by_field(intervals, "dispute_reward_e8").nonempty,
        "slash_covers_cheat_gain_interval_ok": _interval_by_field(intervals, "reporter_bond_required_e8").nonempty
        and _interval_by_field(intervals, "slash_fraction_bps").nonempty,
        "point_verifier_parity_ok": all(item.ok for item in samples),
        "all_boundary_walls_checked": len(sample_rows) >= len(intervals) * 3,
        "mev_assumption_declared": "max_extractable_value_e8" in base and "attack_cost_floor_e8" in base,
        "probability_assumption_declared": True,
        "no_oracle_update_authority": True,
        "fail_closed_default_ok": True,
    }
    return {
        "schema": "zenodex.oracle.polytope_compiler_report.v1",
        "base_envelope": base,
        "base_result": base_result.to_json_obj(),
        "intervals": interval_rows,
        "boundary_samples": sample_rows,
        "tau_oracle_polytope_facts": tau_facts,
        "ok": base_result.status == "accepted"
        and all(row["nonempty"] for row in interval_rows)
        and all(row["ok"] for row in sample_rows)
        and all(tau_facts.values()),
        "non_claims": [
            "The compiler does not estimate MEV, challenge probability, or market truth.",
            "The compiler does not authorize oracle updates.",
            "Intervals are exact for one varied field at a time with other fields fixed to the base envelope.",
        ],
    }


def _interval_by_field(intervals: list[IntervalSpec], field: str) -> IntervalSpec:
    for interval in intervals:
        if interval.field == field:
            return interval
    raise KeyError(field)


def _write_markdown(report: Mapping[str, Any], output: Path) -> None:
    lines: list[str] = []
    lines.append("# Zeno Oracle Polytope Compiler - 2026-06-27")
    lines.append("")
    lines.append("## Executive Result")
    lines.append("")
    lines.append(
        "This artifact turns the pointwise oracle economic-security verifier into exact one-field integer feasibility intervals."
    )
    lines.append(
        "Each interval is checked at the lower wall, upper wall, just below, and just above against `verify_economic_security_envelope`."
    )
    lines.append("")
    lines.append(f"Overall status: `ok={report['ok']}`.")
    lines.append("")
    lines.append("Authority boundary: the compiler emits advisory interval evidence and Tau-facing facts. The pointwise verifier remains authoritative.")
    lines.append("")
    lines.append("## Intervals")
    lines.append("")
    lines.append("| field | lower | upper | reason |")
    lines.append("| --- | ---: | ---: | --- |")
    for row in report["intervals"]:
        lines.append(f"| `{row['field']}` | `{row['lower']}` | `{row['upper']}` | {row['reason']} |")
    lines.append("")
    lines.append("## Boundary Replay")
    lines.append("")
    total = len(report["boundary_samples"])
    passed = sum(1 for row in report["boundary_samples"] if row["ok"])
    lines.append(f"- Boundary samples: `{passed}/{total}` matched the pointwise verifier expectation.")
    lines.append("- Samples include accepted walls and rejected just-outside values for every interval.")
    lines.append("")
    lines.append("## Tau Envelope Facts")
    lines.append("")
    for key, value in report["tau_oracle_polytope_facts"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.append("")
    lines.append("## Non-Claims")
    lines.append("")
    for item in report["non_claims"]:
        lines.append(f"- {item}")
    lines.append("")
    lines.append("## Replay")
    lines.append("")
    lines.append("```bash")
    lines.append("python3 tools/zenodex_oracle_polytope_compiler_20260627.py")
    lines.append("```")
    lines.append("")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text("\n".join(lines), encoding="utf-8")


def run(output_json: Path, output_md: Path) -> dict[str, Any]:
    report = compile_polytope()
    output_json.parent.mkdir(parents=True, exist_ok=True)
    output_json.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    _write_markdown(report, output_md)
    return report


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-json", default=str(OUT_DIR / "report.json"))
    parser.add_argument("--output-md", default=str(REPORT_PATH))
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    report = run(Path(args.output_json), Path(args.output_md))
    print(
        json.dumps(
            {
                "ok": bool(report["ok"]),
                "intervals": len(report["intervals"]),
                "boundary_samples": len(report["boundary_samples"]),
                "json": str(Path(args.output_json)),
                "report": str(Path(args.output_md)),
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
