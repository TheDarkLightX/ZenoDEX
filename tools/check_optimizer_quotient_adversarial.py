#!/usr/bin/env python3
"""Adversarial replay for optimizer quotient route certificates."""

from __future__ import annotations

import argparse
import copy
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping, Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from tools.zenodex_tau_optimizer_quotient_breakthrough_20260627 import (  # noqa: E402
    ASSET_A,
    ASSET_B,
    ASSET_C,
    MAX_ROUTE_LABELS,
    _canonical_json_bytes,
    _pool,
    _route_label_payloads,
    _run_tau_cases,
    build_quotient_certificate,
    enumerate_route_labels,
    route_cases,
    verify_quotient_certificate,
)


OUT_DIR = REPO_ROOT / "generated" / "zenodex_optimizer_quotient_adversarial_20260628"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = REPO_ROOT / "docs" / "research" / "ZENODEX_OPTIMIZER_QUOTIENT_ADVERSARIAL_20260628.md"


@dataclass(frozen=True)
class AdversarialRouteCase:
    case_id: str
    pools: tuple[Any, ...]
    amount_out: int
    family: str
    note: str


def _sorted_pools(*pools: Any) -> tuple[Any, ...]:
    return tuple(sorted(pools, key=lambda pool: pool.pool_id))


def _wide_pools() -> tuple[Any, ...]:
    return _sorted_pools(
        _pool("wide_ab0", ASSET_A, ASSET_B, 4_400, 1_800, 30),
        _pool("wide_ab1", ASSET_A, ASSET_B, 5_300, 2_100, 30),
        _pool("wide_ab2", ASSET_A, ASSET_B, 6_100, 2_450, 35),
        _pool("wide_ab3", ASSET_A, ASSET_B, 7_200, 2_950, 45),
        _pool("wide_ac0", ASSET_A, ASSET_C, 4_700, 3_100, 30),
        _pool("wide_cb0", ASSET_C, ASSET_B, 4_900, 2_800, 30),
    )


def _twohop_pools() -> tuple[Any, ...]:
    return _sorted_pools(
        _pool("twohop_ab_low_fee", ASSET_A, ASSET_B, 3_800, 1_260, 15),
        _pool("twohop_ab_deep_fee", ASSET_A, ASSET_B, 7_000, 2_020, 60),
        _pool("twohop_ab_mid", ASSET_A, ASSET_B, 5_600, 1_800, 25),
        _pool("twohop_ac_deep", ASSET_A, ASSET_C, 6_500, 4_600, 30),
        _pool("twohop_ac_thin", ASSET_A, ASSET_C, 2_400, 2_100, 20),
        _pool("twohop_cb_deep", ASSET_C, ASSET_B, 6_800, 4_200, 30),
        _pool("twohop_cb_fee", ASSET_C, ASSET_B, 4_500, 3_400, 80),
    )


def _sparse_pools() -> tuple[Any, ...]:
    return _sorted_pools(
        _pool("sparse_x", ASSET_A, ASSET_B, 3_000, 1_000, 30),
        _pool("sparse_y", ASSET_A, ASSET_B, 3_500, 1_200, 90),
    )


def _asymmetric_pools() -> tuple[Any, ...]:
    return _sorted_pools(
        _pool("asym_low_fee", ASSET_A, ASSET_B, 900, 900, 5),
        _pool("asym_deep_fee", ASSET_A, ASSET_B, 12_000, 2_500, 100),
        _pool("asym_balanced", ASSET_A, ASSET_B, 5_000, 5_000, 30),
        _pool("asym_ac", ASSET_A, ASSET_C, 10_000, 3_000, 20),
        _pool("asym_cb", ASSET_C, ASSET_B, 4_000, 7_000, 15),
    )


def adversarial_route_cases() -> tuple[AdversarialRouteCase, ...]:
    rows: list[AdversarialRouteCase] = []
    for base in route_cases():
        rows.append(
            AdversarialRouteCase(
                case_id=f"original_{base.case_id}",
                pools=base.pools,
                amount_out=int(base.amount_out),
                family="original_showcase",
                note=base.note,
            )
        )
    for amount_out in (12, 24, 36, 42):
        rows.append(
            AdversarialRouteCase(
                case_id=f"wide_split_amount{amount_out}",
                pools=_wide_pools(),
                amount_out=amount_out,
                family="split_heavy_near_cap",
                note="Four direct pools create many parallel split labels under the 256-label cap.",
            )
        )
    for amount_out in (18, 33, 48, 60):
        rows.append(
            AdversarialRouteCase(
                case_id=f"twohop_winner_amount{amount_out}",
                pools=_twohop_pools(),
                amount_out=amount_out,
                family="twohop_winner",
                note="Two-hop candidates beat direct routes while split labels remain present.",
            )
        )
    for amount_out in (7, 19, 31):
        rows.append(
            AdversarialRouteCase(
                case_id=f"sparse_direct_amount{amount_out}",
                pools=_sparse_pools(),
                amount_out=amount_out,
                family="sparse_direct",
                note="Small direct-only domains stress low-compression and tie-surface boundaries.",
            )
        )
    for amount_out in (20, 50, 70):
        rows.append(
            AdversarialRouteCase(
                case_id=f"asymmetric_amount{amount_out}",
                pools=_asymmetric_pools(),
                amount_out=amount_out,
                family="asymmetric_reserves",
                note="Asymmetric reserve and fee structure changes the selected representative as amount grows.",
            )
        )
    return tuple(rows)


def _case_row(case: AdversarialRouteCase) -> dict[str, Any]:
    labels = enumerate_route_labels(case.pools, asset_in=ASSET_A, asset_out=ASSET_B, amount_out=int(case.amount_out))
    if not labels:
        raise ValueError(f"{case.case_id}: empty route domain")
    certificate = build_quotient_certificate(labels)
    verification = verify_quotient_certificate(certificate, labels)
    full_domain_bytes = len(_canonical_json_bytes(_route_label_payloads(labels)))
    certificate_bytes = len(_canonical_json_bytes(certificate))
    best = min(labels, key=lambda label: label.objective_key)
    worst = max(labels, key=lambda label: label.objective_key)
    compression_ratio = full_domain_bytes / certificate_bytes if certificate_bytes else None
    label_count = len(labels)
    return {
        "case_id": case.case_id,
        "family": case.family,
        "note": case.note,
        "ok": bool(verification["ok"]) and label_count <= MAX_ROUTE_LABELS and certificate_bytes < full_domain_bytes,
        "amount_out": int(case.amount_out),
        "label_count": label_count,
        "selected_route_id": str(certificate["selected_route_id"]),
        "best_route_id": best.route_id,
        "best_amount_in": int(best.route.amount_in),
        "worst_amount_in": int(worst.route.amount_in),
        "full_domain_bytes": full_domain_bytes,
        "quotient_certificate_bytes": certificate_bytes,
        "compression_ratio": compression_ratio,
        "failed_flags": verification["failed_flags"],
        "certificate": certificate,
    }


def _mutation_checks(case: AdversarialRouteCase) -> list[dict[str, Any]]:
    labels = enumerate_route_labels(case.pools, asset_in=ASSET_A, asset_out=ASSET_B, amount_out=int(case.amount_out))
    certificate = build_quotient_certificate(labels)
    worst = max(labels, key=lambda label: label.objective_key)
    mutations: list[tuple[str, dict[str, Any], str]] = []

    bad_hash = copy.deepcopy(certificate)
    bad_hash["domain_hash"] = "0" * 64
    mutations.append(("bad_domain_hash", bad_hash, "domain hash must bind the recomputed route-label domain"))

    bad_selected = copy.deepcopy(certificate)
    bad_selected["selected_route_id"] = worst.route_id
    mutations.append(("bad_selected_route", bad_selected, "selected representative must be the canonical minimum"))

    bad_objective = copy.deepcopy(certificate)
    bad_objective["selected_objective_key"] = [0, [], str(certificate["selected_route_id"])]
    mutations.append(("bad_selected_objective_key", bad_objective, "objective key must replay exactly"))

    bad_label_count = copy.deepcopy(certificate)
    bad_label_count["label_count"] = int(certificate["label_count"]) - 1
    mutations.append(("bad_label_count", bad_label_count, "label count must cover the full route domain"))

    bad_pruned_count = copy.deepcopy(certificate)
    bad_pruned_count["pruned_count"] = int(certificate["pruned_count"]) - 1
    mutations.append(("bad_pruned_count", bad_pruned_count, "pruned count must equal all omitted labels"))

    rows: list[dict[str, Any]] = []
    for mutation_id, mutated, rationale in mutations:
        verification = verify_quotient_certificate(mutated, labels)
        rows.append(
            {
                "mutation_id": mutation_id,
                "accepted": bool(verification["ok"]),
                "failed_flags": verification["failed_flags"],
                "rationale": rationale,
            }
        )
    if len(adversarial_route_cases()) > 1:
        other = adversarial_route_cases()[1]
        other_labels = enumerate_route_labels(
            other.pools,
            asset_in=ASSET_A,
            asset_out=ASSET_B,
            amount_out=int(other.amount_out),
        )
        transplanted = verify_quotient_certificate(certificate, other_labels)
        rows.append(
            {
                "mutation_id": "cross_domain_transplant",
                "accepted": bool(transplanted["ok"]),
                "failed_flags": transplanted["failed_flags"],
                "rationale": "certificate from one domain must not verify against another domain",
            }
        )
    return rows


def build_report() -> dict[str, Any]:
    case_rows = [_case_row(case) for case in adversarial_route_cases()]
    tau = _run_tau_cases()
    mutation_rows = _mutation_checks(adversarial_route_cases()[3])
    ratios = [float(row["compression_ratio"]) for row in case_rows if row["compression_ratio"] is not None]
    families = sorted({str(row["family"]) for row in case_rows})
    selected_prefixes = sorted({str(row["selected_route_id"]).split(":", 1)[0] for row in case_rows})
    ok = (
        all(bool(row["ok"]) for row in case_rows)
        and bool(tau.get("ok"))
        and all(not bool(row["accepted"]) for row in mutation_rows)
        and len(families) >= 4
        and {"direct", "twohop"}.issubset(set(selected_prefixes))
    )
    return {
        "schema": "zenodex.optimizer_quotient_adversarial_report.v1",
        "date": "2026-06-28",
        "ok": bool(ok),
        "case_count": len(case_rows),
        "families": families,
        "selected_route_prefixes": selected_prefixes,
        "min_label_count": min(int(row["label_count"]) for row in case_rows),
        "max_label_count": max(int(row["label_count"]) for row in case_rows),
        "min_compression_ratio": min(ratios) if ratios else None,
        "max_compression_ratio": max(ratios) if ratios else None,
        "tau": tau,
        "mutation_checks": mutation_rows,
        "cases": case_rows,
        "claim": (
            "The optimizer_quotient_certificate_v1 host-projected Tau envelope remains valid across a "
            "deterministic adversarial route-domain corpus covering original, split-heavy, two-hop-winner, "
            "sparse-direct, and asymmetric-reserve cases, while preserving bounded domain replay, mutation "
            "rejection, proof compression, and no-authority boundaries."
        ),
        "non_claims": [
            "The corpus is bounded to direct, two-hop, and two-way parallel exact-out route labels.",
            "The quotient certificate is only sound with host recomputation of the full route-label domain.",
            "Tau does not compute route labels, hashes, objective keys, CPMM arithmetic, DP states, or settlement.",
        ],
        "replay_command": "python3 tools/check_optimizer_quotient_adversarial.py",
    }


def _fmt_ratio(value: float | None) -> str:
    return "n/a" if value is None else f"{float(value):.2f}x"


def _write_markdown(report: Mapping[str, Any]) -> None:
    lines = [
        "# ZenoDEX Optimizer Quotient Adversarial Corpus - 2026-06-28",
        "",
        "## Executive Result",
        "",
        str(report["claim"]),
        "",
        f"- Cases: `{report['case_count']}`",
        f"- Families: `{', '.join(report['families'])}`",
        f"- Selected route prefixes: `{', '.join(report['selected_route_prefixes'])}`",
        f"- Label count range: `{report['min_label_count']}` to `{report['max_label_count']}`",
        f"- Compression range: `{_fmt_ratio(report['min_compression_ratio'])}` to `{_fmt_ratio(report['max_compression_ratio'])}`",
        f"- Tau replay ok: `{report['tau']['ok']}`",
        "",
        "## Case Table",
        "",
        "| case | family | labels | full bytes | cert bytes | compression | selected |",
        "| --- | --- | ---: | ---: | ---: | ---: | --- |",
    ]
    for row in report["cases"]:
        lines.append(
            f"| `{row['case_id']}` | `{row['family']}` | `{row['label_count']}` | "
            f"`{row['full_domain_bytes']}` | `{row['quotient_certificate_bytes']}` | "
            f"`{_fmt_ratio(row['compression_ratio'])}` | `{row['selected_route_id']}` |"
        )
    lines.extend(
        [
            "",
            "## Mutation Checks",
            "",
            "| mutation | accepted | failed flags |",
            "| --- | --- | --- |",
        ]
    )
    for row in report["mutation_checks"]:
        failed = ", ".join(f"`{flag}`" for flag in row["failed_flags"]) or "none"
        lines.append(f"| `{row['mutation_id']}` | `{row['accepted']}` | {failed} |")
    lines.extend(
        [
            "",
            "## Tau Boundary",
            "",
            "`src/tau_specs/recommended/optimizer_quotient_certificate_v1.tau` remains a host-projected proof-surface gate. Host code owns route-domain enumeration, hashes, objective keys, arithmetic replay, and winner selection.",
            "",
            "## Non-Claims",
            "",
        ]
    )
    for item in report["non_claims"]:
        lines.append(f"- {item}")
    lines.extend(["", "## Replay", "", "```bash", str(report["replay_command"]), "```", ""])
    REPORT_MD.parent.mkdir(parents=True, exist_ok=True)
    REPORT_MD.write_text("\n".join(lines), encoding="utf-8")


def run(output_json: Path = REPORT_JSON) -> dict[str, Any]:
    report = build_report()
    output_json.parent.mkdir(parents=True, exist_ok=True)
    output_json.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    _write_markdown(report)
    return report


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-json", default=str(REPORT_JSON))
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    report = run(Path(args.output_json))
    print(
        json.dumps(
            {
                "ok": report["ok"],
                "case_count": report["case_count"],
                "max_label_count": report["max_label_count"],
                "min_compression_ratio": report["min_compression_ratio"],
                "max_compression_ratio": report["max_compression_ratio"],
                "tau_ok": report["tau"]["ok"],
                "report": str(REPORT_MD),
                "json": str(Path(args.output_json)),
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
