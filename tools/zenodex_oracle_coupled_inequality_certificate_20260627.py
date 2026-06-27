#!/usr/bin/env python3
"""Build coupled inequality certificates for Zeno Oracle economic envelopes."""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT / "tools"))

from zenodex_oracle_economic_security import (  # noqa: E402
    BPS_SCALE,
    ENVELOPE_KEYS,
    ENVELOPE_SCHEMA,
    MAX_AMOUNT,
    MAX_COUNT,
    MAX_MARGIN_BPS,
    SHA256_RE,
    TOKEN_RE,
    sample_envelope,
    verify_economic_security_envelope,
)


OUT_DIR = REPO_ROOT / "generated" / "zenodex_oracle_coupled_inequality_certificate_20260627"
REPORT_PATH = REPO_ROOT / "docs" / "research" / "ZENODEX_ORACLE_COUPLED_INEQUALITY_CERTIFICATE_20260627.md"
IntRuleFn = Callable[[Mapping[str, int]], bool]


@dataclass(frozen=True)
class InequalityRule:
    rule_id: str
    verifier_error: str
    expression: str
    rationale: str
    check: IntRuleFn


@dataclass(frozen=True)
class CertificateCase:
    case_id: str
    assignments: dict[str, int]
    expected_ok: bool
    expected_failed_rules: tuple[str, ...]
    expected_verifier_errors: tuple[str, ...]


def _ceil_div(numer: int, denom: int) -> int:
    if denom <= 0:
        raise ValueError("denom must be positive")
    return (numer + denom - 1) // denom


def _strict_int_fields(envelope: Mapping[str, Any]) -> dict[str, int]:
    values: dict[str, int] = {}
    for key, value in envelope.items():
        if isinstance(value, int) and not isinstance(value, bool):
            values[key] = int(value)
    return values


def _rules() -> tuple[InequalityRule, ...]:
    return (
        InequalityRule(
            "notional_covers_extractable",
            "extractable_value_exceeds_notional",
            "max_extractable_value_e8 <= notional_value_e8",
            "notional must bound the declared extractable value",
            lambda e: e["max_extractable_value_e8"] <= e["notional_value_e8"],
        ),
        InequalityRule(
            "cheat_gain_covers_extractable",
            "expected_cheat_gain_exceeds_extractable_value",
            "expected_cheat_gain_e8 <= max_extractable_value_e8",
            "expected cheat gain must not exceed the declared extractable value",
            lambda e: e["expected_cheat_gain_e8"] <= e["max_extractable_value_e8"],
        ),
        InequalityRule(
            "attack_cost_margin",
            "attack_cost_floor_below_required_margin",
            "attack_cost_floor_e8 * 10000 >= max_extractable_value_e8 * (10000 + required_attack_margin_bps)",
            "integer multiplication exactly matches the verifier's ceil-div attack-cost requirement",
            lambda e: e["attack_cost_floor_e8"] * BPS_SCALE
            >= e["max_extractable_value_e8"] * (BPS_SCALE + e["required_attack_margin_bps"]),
        ),
        InequalityRule(
            "reporter_reward_floor",
            "reporter_reward_below_honest_cost_plus_risk",
            "reporter_reward_per_report_e8 >= honest_reporter_cost_e8 + honest_reporter_risk_premium_e8",
            "per-report reward must cover honest reporting cost plus risk premium",
            lambda e: e["reporter_reward_per_report_e8"]
            >= e["honest_reporter_cost_e8"] + e["honest_reporter_risk_premium_e8"],
        ),
        InequalityRule(
            "reporter_reward_budget",
            "reporter_reward_budget_exceeded",
            "reporter_reward_per_report_e8 * reporter_count <= reporter_reward_budget_e8",
            "total reporter reward must fit the declared reward budget",
            lambda e: e["reporter_reward_per_report_e8"] * e["reporter_count"]
            <= e["reporter_reward_budget_e8"],
        ),
        InequalityRule(
            "slash_deterrence",
            "slash_deterrence_below_required_margin",
            "(reporter_bond_required_e8 * slash_fraction_bps) // 10000 >= ceil(expected_cheat_gain_e8 * (10000 + deterrence_margin_bps) / 10000)",
            "floor slash amount must cover the verifier's ceil-div deterrence requirement",
            lambda e: (e["reporter_bond_required_e8"] * e["slash_fraction_bps"]) // BPS_SCALE
            >= _ceil_div(e["expected_cheat_gain_e8"] * (BPS_SCALE + e["deterrence_margin_bps"]), BPS_SCALE),
        ),
        InequalityRule(
            "dispute_reward_budget",
            "dispute_reward_budget_exceeded",
            "dispute_reward_e8 <= dispute_budget_e8",
            "dispute reward must fit the declared dispute budget",
            lambda e: e["dispute_reward_e8"] <= e["dispute_budget_e8"],
        ),
        InequalityRule(
            "fee_share_budget",
            "fee_shares_exceed_fee_paid",
            "reporter_fee_share_e8 + treasury_fee_share_e8 + burn_fee_share_e8 <= fee_paid_e8",
            "fee shares must fit the fee paid",
            lambda e: e["reporter_fee_share_e8"] + e["treasury_fee_share_e8"] + e["burn_fee_share_e8"]
            <= e["fee_paid_e8"],
        ),
    )


def _domain_errors(envelope: Mapping[str, Any]) -> list[str]:
    errors: list[str] = []
    _unknown_field_errors(envelope, errors)
    if envelope.get("schema") != ENVELOPE_SCHEMA:
        errors.append("economic_security_schema_mismatch")
    _hash_error(envelope, "query_id", errors)
    _token_error(envelope, "consumer_module", errors)
    _token_error(envelope, "action_kind", errors)
    int_bounds: dict[str, tuple[int, int]] = {
        "notional_value_e8": (0, MAX_AMOUNT),
        "max_extractable_value_e8": (0, MAX_AMOUNT),
        "attack_cost_floor_e8": (0, MAX_AMOUNT),
        "required_attack_margin_bps": (0, MAX_MARGIN_BPS),
        "reporter_count": (1, MAX_COUNT),
        "reporter_reward_budget_e8": (0, MAX_AMOUNT),
        "reporter_reward_per_report_e8": (0, MAX_AMOUNT),
        "honest_reporter_cost_e8": (0, MAX_AMOUNT),
        "honest_reporter_risk_premium_e8": (0, MAX_AMOUNT),
        "reporter_bond_required_e8": (0, MAX_AMOUNT),
        "slash_fraction_bps": (0, BPS_SCALE),
        "expected_cheat_gain_e8": (0, MAX_AMOUNT),
        "deterrence_margin_bps": (0, MAX_MARGIN_BPS),
        "dispute_reward_e8": (0, MAX_AMOUNT),
        "dispute_budget_e8": (0, MAX_AMOUNT),
        "fee_paid_e8": (0, MAX_AMOUNT),
        "reporter_fee_share_e8": (0, MAX_AMOUNT),
        "treasury_fee_share_e8": (0, MAX_AMOUNT),
        "burn_fee_share_e8": (0, MAX_AMOUNT),
    }
    for field, (lower, upper) in int_bounds.items():
        value = envelope.get(field)
        if not isinstance(value, int) or isinstance(value, bool) or value < lower or value > upper:
            errors.append(f"{field}_must_be_int_between_{lower}_and_{upper}")
    return errors


def _unknown_field_errors(envelope: Mapping[str, Any], errors: list[str]) -> None:
    for key in envelope.keys():
        if not isinstance(key, str):
            errors.append("economic_security_field_must_be_string")
        elif key not in ENVELOPE_KEYS:
            errors.append(f"unknown_economic_security_field:{key}")


def _hash_error(envelope: Mapping[str, Any], field: str, errors: list[str]) -> None:
    value = envelope.get(field)
    if not isinstance(value, str) or not SHA256_RE.match(value):
        errors.append(f"{field}_must_be_sha256")


def _token_error(envelope: Mapping[str, Any], field: str, errors: list[str]) -> None:
    value = envelope.get(field)
    if not isinstance(value, str) or not TOKEN_RE.match(value):
        errors.append(f"{field}_must_be_token")


def build_certificate(envelope: Mapping[str, Any]) -> dict[str, Any]:
    numeric = _strict_int_fields(envelope)
    domain_errors = _domain_errors(envelope)
    rule_rows: list[dict[str, Any]] = []
    for rule in _rules():
        try:
            holds = True if domain_errors else bool(rule.check(numeric))
        except KeyError:
            holds = False
        rule_rows.append(
            {
                "rule_id": rule.rule_id,
                "verifier_error": rule.verifier_error,
                "expression": rule.expression,
                "rationale": rule.rationale,
                "holds": holds,
            }
        )
    verifier_result = verify_economic_security_envelope(envelope).to_json_obj()
    failed_rule_errors = [row["verifier_error"] for row in rule_rows if not row["holds"]]
    certificate_ok = not domain_errors and not failed_rule_errors
    verifier_errors = list(verifier_result["errors"])
    return {
        "schema": "zenodex.oracle.coupled_inequality_certificate.v1",
        "certificate_ok": certificate_ok,
        "verifier_ok": bool(verifier_result["ok"]),
        "parity_ok": certificate_ok is bool(verifier_result["ok"])
        and set(domain_errors + failed_rule_errors) == set(verifier_errors),
        "domain_errors": domain_errors,
        "failed_rule_errors": failed_rule_errors,
        "verifier_errors": verifier_errors,
        "verifier_result": verifier_result,
        "rules": rule_rows,
    }


def _case_catalog() -> tuple[CertificateCase, ...]:
    return (
        CertificateCase("sample_accepts", {}, True, tuple(), tuple()),
        CertificateCase(
            "attack_margin_counterexample_now_rejected",
            {"max_extractable_value_e8": 62_500_000_000, "required_attack_margin_bps": 5_000},
            False,
            ("attack_cost_floor_below_required_margin",),
            ("attack_cost_floor_below_required_margin",),
        ),
        CertificateCase(
            "reporter_reward_counterexample_now_rejected",
            {"reporter_reward_per_report_e8": 40_000_000, "reporter_count": 4},
            False,
            ("reporter_reward_budget_exceeded",),
            ("reporter_reward_budget_exceeded",),
        ),
        CertificateCase(
            "slash_counterexample_now_rejected",
            {"reporter_bond_required_e8": 120_000_000_000, "slash_fraction_bps": 2_400},
            False,
            ("slash_deterrence_below_required_margin",),
            ("slash_deterrence_below_required_margin",),
        ),
        CertificateCase(
            "fee_share_budget_rejects",
            {"burn_fee_share_e8": 30_000_001},
            False,
            ("fee_shares_exceed_fee_paid",),
            ("fee_shares_exceed_fee_paid",),
        ),
    )


def run_cases() -> dict[str, Any]:
    base = sample_envelope()
    cases: list[dict[str, Any]] = []
    for case in _case_catalog():
        envelope = dict(base)
        envelope.update(case.assignments)
        certificate = build_certificate(envelope)
        expected_errors_match = set(certificate["failed_rule_errors"]) == set(case.expected_failed_rules)
        verifier_errors_match = set(certificate["verifier_errors"]) == set(case.expected_verifier_errors)
        cases.append(
            {
                "case_id": case.case_id,
                "assignments": case.assignments,
                "expected_ok": case.expected_ok,
                "certificate_ok": certificate["certificate_ok"],
                "verifier_ok": certificate["verifier_ok"],
                "parity_ok": certificate["parity_ok"],
                "expected_errors_match": expected_errors_match,
                "verifier_errors_match": verifier_errors_match,
                "failed_rule_errors": certificate["failed_rule_errors"],
                "verifier_errors": certificate["verifier_errors"],
            }
        )
    return {
        "schema": "zenodex.oracle.coupled_inequality_certificate_report.v1",
        "ok": all(
            row["certificate_ok"] is row["expected_ok"]
            and row["verifier_ok"] is row["expected_ok"]
            and row["parity_ok"]
            and row["expected_errors_match"]
            and row["verifier_errors_match"]
            for row in cases
        ),
        "case_count": len(cases),
        "rule_count": len(_rules()),
        "cases": cases,
        "rules": [
            {
                "rule_id": rule.rule_id,
                "verifier_error": rule.verifier_error,
                "expression": rule.expression,
                "rationale": rule.rationale,
            }
            for rule in _rules()
        ],
        "non_claims": [
            "The certificate mirrors the current pointwise economic-security verifier; it does not estimate MEV or market truth.",
            "The certificate does not authorize oracle updates.",
            "The certificate is a coupled inequality checker, not a maximal polytope enumerator.",
        ],
        "replay_command": "python3 tools/zenodex_oracle_coupled_inequality_certificate_20260627.py",
    }


def _write_markdown(report: Mapping[str, Any], output: Path) -> None:
    lines: list[str] = []
    lines.append("# Zeno Oracle Coupled Inequality Certificate - 2026-06-27")
    lines.append("")
    lines.append("## Executive Result")
    lines.append("")
    lines.append(
        "This artifact replaces the refuted Cartesian-box interpretation with a coupled inequality certificate that mirrors the pointwise oracle economic-security verifier."
    )
    lines.append(
        f"Rules checked: `{report['rule_count']}`. Replay cases: `{report['case_count']}`. Overall status: `ok={report['ok']}`."
    )
    lines.append("")
    lines.append("Authority boundary: the certificate is advisory evidence; the pointwise verifier remains authoritative.")
    lines.append("")
    lines.append("## Rules")
    lines.append("")
    lines.append("| rule | verifier error | expression |")
    lines.append("| --- | --- | --- |")
    for row in report["rules"]:
        lines.append(f"| `{row['rule_id']}` | `{row['verifier_error']}` | `{row['expression']}` |")
    lines.append("")
    lines.append("## Replay Cases")
    lines.append("")
    lines.append("| case | certificate ok | verifier ok | failed rules |")
    lines.append("| --- | --- | --- | --- |")
    for row in report["cases"]:
        failed = ", ".join(f"`{err}`" for err in row["failed_rule_errors"]) or "none"
        lines.append(f"| `{row['case_id']}` | `{row['certificate_ok']}` | `{row['verifier_ok']}` | {failed} |")
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


def run(output_json: Path, output_md: Path) -> dict[str, Any]:
    report = run_cases()
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
                "ok": report["ok"],
                "case_count": report["case_count"],
                "rule_count": report["rule_count"],
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
