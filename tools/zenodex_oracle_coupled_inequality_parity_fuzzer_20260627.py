#!/usr/bin/env python3
"""Fuzz coupled inequality certificates against the pointwise oracle verifier."""

from __future__ import annotations

import argparse
import json
import random
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT / "tools"))

from zenodex_oracle_coupled_inequality_certificate_20260627 import build_certificate  # noqa: E402
from zenodex_oracle_economic_security import (  # noqa: E402
    BPS_SCALE,
    MAX_AMOUNT,
    MAX_COUNT,
    MAX_MARGIN_BPS,
    sample_envelope,
    verify_economic_security_envelope,
)


OUT_DIR = REPO_ROOT / "generated" / "zenodex_oracle_coupled_inequality_parity_fuzzer_20260627"
REPORT_PATH = REPO_ROOT / "docs" / "research" / "ZENODEX_ORACLE_COUPLED_INEQUALITY_PARITY_FUZZER_20260627.md"
DEFAULT_SEED = 20260627
DEFAULT_RANDOM_CASES = 512

INT_FIELDS: tuple[str, ...] = (
    "notional_value_e8",
    "max_extractable_value_e8",
    "attack_cost_floor_e8",
    "required_attack_margin_bps",
    "reporter_count",
    "reporter_reward_budget_e8",
    "reporter_reward_per_report_e8",
    "honest_reporter_cost_e8",
    "honest_reporter_risk_premium_e8",
    "reporter_bond_required_e8",
    "slash_fraction_bps",
    "expected_cheat_gain_e8",
    "deterrence_margin_bps",
    "dispute_reward_e8",
    "dispute_budget_e8",
    "fee_paid_e8",
    "reporter_fee_share_e8",
    "treasury_fee_share_e8",
    "burn_fee_share_e8",
)

FIELD_MAXIMUMS: dict[str, int] = {
    "required_attack_margin_bps": MAX_MARGIN_BPS,
    "reporter_count": MAX_COUNT,
    "slash_fraction_bps": BPS_SCALE,
    "deterrence_margin_bps": MAX_MARGIN_BPS,
}


@dataclass(frozen=True)
class FuzzCase:
    case_id: str
    envelope: Mapping[str, Any]
    family: str


def _max_for_field(field: str) -> int:
    return FIELD_MAXIMUMS.get(field, MAX_AMOUNT)


def _single_field_domain_cases() -> list[FuzzCase]:
    base = sample_envelope()
    cases = [FuzzCase("sample_accepts", dict(base), "baseline")]
    for field in INT_FIELDS:
        maximum = _max_for_field(field)
        lower_valid = 1 if field == "reporter_count" else 0
        for label, value in (
            ("bool", True),
            ("below_min", lower_valid - 1),
            ("at_min", lower_valid),
            ("above_max", maximum + 1),
        ):
            env = dict(base)
            env[field] = value
            cases.append(FuzzCase(f"{field}_{label}", env, "single_field_domain"))
    return cases


def _metadata_domain_cases() -> list[FuzzCase]:
    base = sample_envelope()
    cases: list[FuzzCase] = []
    for case_id, assignment in (
        ("schema_mismatch", {"schema": "zenodex.oracle.economic_security_envelope.v0"}),
        ("query_id_not_hash", {"query_id": "not-a-hash"}),
        ("consumer_module_bad_token", {"consumer_module": "ZenoDEX Perps"}),
        ("action_kind_bad_token", {"action_kind": ""}),
        ("unknown_field_hidden_mint", {"hidden_mint": 1}),
    ):
        env = dict(base)
        env.update(assignment)
        cases.append(FuzzCase(case_id, env, "metadata_domain"))
    return cases


def _random_valid_amount(field: str, rng: random.Random) -> int:
    if field == "reporter_count":
        return rng.randint(1, 12)
    if field == "slash_fraction_bps":
        return rng.randint(0, BPS_SCALE)
    if field in {"required_attack_margin_bps", "deterrence_margin_bps"}:
        return rng.randint(0, 30_000)
    choices = (
        0,
        1,
        10,
        10_000,
        1_000_000,
        25_000_000,
        50_000_000,
        100_000_000,
        50_000_000_000,
        75_000_000_000,
        250_000_000_000,
        1_000_000_000_000,
    )
    return int(rng.choice(choices))


def _random_economic_cases(*, seed: int, count: int) -> list[FuzzCase]:
    rng = random.Random(seed)
    cases: list[FuzzCase] = []
    for idx in range(count):
        env = sample_envelope()
        for field in INT_FIELDS:
            env[field] = _random_valid_amount(field, rng)
        cases.append(FuzzCase(f"random_economic_{idx:04d}", env, "random_economic"))
    return cases


def _cases(*, seed: int, random_cases: int) -> list[FuzzCase]:
    return [
        *_single_field_domain_cases(),
        *_metadata_domain_cases(),
        *_random_economic_cases(seed=seed, count=random_cases),
    ]


def _evaluate_case(case: FuzzCase) -> dict[str, Any]:
    certificate = build_certificate(case.envelope)
    verifier = verify_economic_security_envelope(case.envelope).to_json_obj()
    certificate_errors = set(certificate["domain_errors"] + certificate["failed_rule_errors"])
    verifier_errors = set(verifier["errors"])
    ok_match = bool(certificate["certificate_ok"]) is bool(verifier["ok"])
    errors_match = certificate_errors == verifier_errors
    return {
        "case_id": case.case_id,
        "family": case.family,
        "ok": ok_match and errors_match and bool(certificate["parity_ok"]),
        "certificate_ok": bool(certificate["certificate_ok"]),
        "verifier_ok": bool(verifier["ok"]),
        "parity_ok": bool(certificate["parity_ok"]),
        "certificate_errors": sorted(certificate_errors),
        "verifier_errors": sorted(verifier_errors),
        "ok_match": ok_match,
        "errors_match": errors_match,
    }


def run_fuzzer(*, seed: int = DEFAULT_SEED, random_cases: int = DEFAULT_RANDOM_CASES) -> dict[str, Any]:
    rows = [_evaluate_case(case) for case in _cases(seed=seed, random_cases=random_cases)]
    mismatches = [row for row in rows if not row["ok"]]
    accepted = sum(1 for row in rows if row["certificate_ok"])
    rejected = len(rows) - accepted
    error_coverage = sorted({error for row in rows for error in row["verifier_errors"]})
    by_family: dict[str, dict[str, int]] = {}
    for row in rows:
        family = row["family"]
        stats = by_family.setdefault(family, {"cases": 0, "accepted": 0, "rejected": 0, "mismatches": 0})
        stats["cases"] += 1
        stats["accepted"] += int(row["certificate_ok"])
        stats["rejected"] += int(not row["certificate_ok"])
        stats["mismatches"] += int(not row["ok"])
    return {
        "schema": "zenodex.oracle.coupled_inequality_parity_fuzzer_report.v1",
        "ok": not mismatches,
        "seed": seed,
        "random_cases": random_cases,
        "case_count": len(rows),
        "accepted_count": accepted,
        "rejected_count": rejected,
        "mismatch_count": len(mismatches),
        "mismatches": mismatches[:25],
        "error_coverage": error_coverage,
        "by_family": by_family,
        "non_claims": [
            "The fuzzer is bounded and deterministic; it is not exhaustive over the full integer domain.",
            "The pointwise verifier remains authoritative.",
            "The fuzzer checks parity of accept/reject and reject-reason sets, not oracle truth.",
        ],
        "replay_command": (
            "python3 tools/zenodex_oracle_coupled_inequality_parity_fuzzer_20260627.py "
            f"--seed {seed} --random-cases {random_cases}"
        ),
    }


def _write_markdown(report: Mapping[str, Any], output: Path) -> None:
    lines: list[str] = []
    lines.append("# Zeno Oracle Coupled Inequality Parity Fuzzer - 2026-06-27")
    lines.append("")
    lines.append("## Executive Result")
    lines.append("")
    lines.append(
        "This bounded deterministic fuzzer compares the coupled inequality certificate against the pointwise oracle economic-security verifier."
    )
    lines.append(
        f"Cases: `{report['case_count']}`. Accepted: `{report['accepted_count']}`. Rejected: `{report['rejected_count']}`. Mismatches: `{report['mismatch_count']}`. Overall: `ok={report['ok']}`."
    )
    lines.append("")
    lines.append("Authority boundary: the fuzzer is evidence for certificate/verifier parity; it does not authorize oracle updates.")
    lines.append("")
    lines.append("## Case Families")
    lines.append("")
    lines.append("| family | cases | accepted | rejected | mismatches |")
    lines.append("| --- | ---: | ---: | ---: | ---: |")
    for family, stats in sorted(report["by_family"].items()):
        lines.append(
            f"| `{family}` | `{stats['cases']}` | `{stats['accepted']}` | `{stats['rejected']}` | `{stats['mismatches']}` |"
        )
    lines.append("")
    lines.append("## Error Coverage")
    lines.append("")
    for error in report["error_coverage"]:
        lines.append(f"- `{error}`")
    lines.append("")
    lines.append("## Non-Claims")
    lines.append("")
    for item in report["non_claims"]:
        lines.append(f"- {item}")
    lines.append("")
    lines.append("## Replay")
    lines.append("")
    lines.append("```bash")
    lines.append(str(report["replay_command"]))
    lines.append("```")
    lines.append("")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text("\n".join(lines), encoding="utf-8")


def run(output_json: Path, output_md: Path, *, seed: int, random_cases: int) -> dict[str, Any]:
    report = run_fuzzer(seed=seed, random_cases=random_cases)
    output_json.parent.mkdir(parents=True, exist_ok=True)
    output_json.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    _write_markdown(report, output_md)
    return report


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed", type=int, default=DEFAULT_SEED)
    parser.add_argument("--random-cases", type=int, default=DEFAULT_RANDOM_CASES)
    parser.add_argument("--output-json", default=str(OUT_DIR / "report.json"))
    parser.add_argument("--output-md", default=str(REPORT_PATH))
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    report = run(
        Path(args.output_json),
        Path(args.output_md),
        seed=int(args.seed),
        random_cases=int(args.random_cases),
    )
    print(
        json.dumps(
            {
                "ok": report["ok"],
                "case_count": report["case_count"],
                "mismatch_count": report["mismatch_count"],
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
