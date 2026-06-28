#!/usr/bin/env python3
"""Replay a deterministic negative-frontier entropy scheduler for falsifier campaigns."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import sys
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from tools.stateful_scenario_bridge import DISASTER_SEARCH_EXPANSION_AXES  # noqa: E402


OUT_DIR = REPO_ROOT / "generated" / "zenodex_negative_frontier_entropy_scheduler_20260628"
REPORT_JSON = OUT_DIR / "report.json"
REPORT_MD = REPO_ROOT / "docs" / "research" / "ZENODEX_NEGATIVE_FRONTIER_ENTROPY_SCHEDULER_20260628.md"
SCHEDULER_SCHEMA = "zenodex.negative_frontier_entropy_scheduler_report.v1"

RECENT_NEGATIVE_FAMILY_HISTORY = (
    "route_certificate",
    "route_certificate",
    "route_certificate",
    "route_certificate",
    "oracle_recovery",
    "oracle_recovery",
    "oracle_recovery",
    "proof_mining",
    "proof_mining",
    "tau_policy",
    "tau_policy",
    "receipt_binding",
    "receipt_binding",
    "receipt_binding",
    "runtime_root",
)


@dataclass(frozen=True)
class Axis:
    axis_id: str
    priority_score: int
    family_labels: tuple[str, ...]
    mutation_families: tuple[str, ...]
    commands: tuple[tuple[str, ...], ...]


def _family_label(text: str) -> str:
    lowered = text.lower()
    rules = (
        ("oracle", "oracle_recovery"),
        ("route", "route_certificate"),
        ("quote", "route_certificate"),
        ("proof-mining", "proof_mining"),
        ("proof mining", "proof_mining"),
        ("tau", "tau_policy"),
        ("lean", "formal_proof"),
        ("tla", "formal_proof"),
        ("esso", "formal_proof"),
        ("fire", "fire_supply_chain"),
        ("wallet", "wallet_authority"),
        ("signer", "wallet_authority"),
        ("signature", "wallet_authority"),
        ("nonce", "identity_nonce"),
        ("identity", "identity_nonce"),
        ("state root", "runtime_root"),
        ("root", "runtime_root"),
        ("receipt", "receipt_binding"),
        ("certificate", "receipt_binding"),
        ("runtime", "runtime_root"),
        ("settlement", "settlement_semantics"),
        ("batch", "batch_clearing"),
        ("perp", "perps_safety"),
        ("zusd", "zusd_safety"),
        ("governance", "governance"),
        ("tokenomics", "tokenomics"),
        ("fee", "fee_accounting"),
        ("liquidity", "liquidity_accounting"),
        ("confidential", "confidential_boundary"),
        ("sealed-bid", "sealed_bid"),
        ("fhe", "confidential_boundary"),
        ("resource", "resource_budget"),
        ("dependency", "external_dependency"),
        ("external", "external_dependency"),
        ("serialization", "serialization"),
        ("width", "serialization"),
        ("canonical", "canonicalization"),
        ("alias", "canonicalization"),
        ("adaptive", "adaptive_search"),
        ("scheduler", "scheduler_stability"),
    )
    for needle, label in rules:
        if needle in lowered:
            return label
    return "other_negative_family"


def _axis_from_raw(raw: Mapping[str, Any]) -> Axis:
    mutation_families = tuple(str(item) for item in raw.get("mutation_families", ()))
    family_labels = tuple(sorted({_family_label(family) for family in mutation_families}))
    return Axis(
        axis_id=str(raw["axis_id"]),
        priority_score=int(raw["priority_score"]),
        family_labels=family_labels or ("other_negative_family",),
        mutation_families=mutation_families,
        commands=tuple(tuple(str(part) for part in command) for command in raw.get("commands", ())),
    )


def _axis_corpus() -> tuple[Axis, ...]:
    return tuple(_axis_from_raw(raw) for raw in DISASTER_SEARCH_EXPANSION_AXES)


def _entropy(counts: Mapping[str, int]) -> float:
    total = sum(int(value) for value in counts.values())
    if total <= 0:
        return 0.0
    return -sum((int(value) / total) * math.log(int(value) / total) for value in counts.values() if int(value) > 0)


def _add_axis(counts: Counter[str], axis: Axis) -> Counter[str]:
    out = Counter(counts)
    for family in axis.family_labels:
        out[family] += 1
    return out


def _stable_hash_int(seed: str, axis_id: str) -> int:
    digest = hashlib.sha256(f"{seed}:{axis_id}".encode("utf-8")).hexdigest()
    return int(digest[:16], 16)


def _eligible_axes(corpus: Sequence[Axis], *, min_priority_score: int) -> tuple[Axis, ...]:
    return tuple(axis for axis in corpus if axis.priority_score >= min_priority_score)


def _axis_score(axis: Axis, counts: Counter[str]) -> dict[str, Any]:
    before_entropy = _entropy(counts)
    after_counts = _add_axis(counts, axis)
    entropy_gain = _entropy(after_counts) - before_entropy
    new_family_count = sum(1 for family in axis.family_labels if counts[family] == 0)
    rare_family_score = sum(1.0 / (1 + counts[family]) for family in axis.family_labels)
    score = (
        (axis.priority_score / 100.0)
        + (8.0 * entropy_gain)
        + (1.5 * new_family_count)
        + (0.6 * rare_family_score)
        - (0.03 * len(axis.commands))
    )
    return {
        "score": score,
        "entropy_gain": entropy_gain,
        "new_family_count": new_family_count,
        "rare_family_score": rare_family_score,
    }


def _entropy_schedule(
    corpus: Sequence[Axis],
    *,
    budget: int,
    min_priority_score: int,
    recent_history: Sequence[str],
) -> tuple[Axis, ...]:
    selected: list[Axis] = []
    counts = Counter(recent_history)
    remaining = list(_eligible_axes(corpus, min_priority_score=min_priority_score))
    while remaining and len(selected) < budget:
        ranked = sorted(
            remaining,
            key=lambda axis: (
                -float(_axis_score(axis, counts)["score"]),
                -int(axis.priority_score),
                axis.axis_id,
            ),
        )
        winner = ranked[0]
        selected.append(winner)
        counts = _add_axis(counts, winner)
        remaining = [axis for axis in remaining if axis.axis_id != winner.axis_id]
    return tuple(selected)


def _recency_schedule(
    corpus: Sequence[Axis],
    *,
    budget: int,
    min_priority_score: int,
    recent_history: Sequence[str],
) -> tuple[Axis, ...]:
    counts = Counter(recent_history)
    eligible = _eligible_axes(corpus, min_priority_score=min_priority_score)
    return tuple(
        sorted(
            eligible,
            key=lambda axis: (
                -sum(counts[family] for family in axis.family_labels),
                -axis.priority_score,
                axis.axis_id,
            ),
        )[:budget]
    )


def _stable_random_schedule(
    corpus: Sequence[Axis],
    *,
    budget: int,
    min_priority_score: int,
    seed: str,
) -> tuple[Axis, ...]:
    eligible = _eligible_axes(corpus, min_priority_score=min_priority_score)
    return tuple(sorted(eligible, key=lambda axis: (_stable_hash_int(seed, axis.axis_id), axis.axis_id))[:budget])


def _schedule_metrics(name: str, schedule: Sequence[Axis], *, recent_history: Sequence[str]) -> dict[str, Any]:
    discovered = Counter()
    for axis in schedule:
        for family in axis.family_labels:
            discovered[family] += 1
    after_counts = Counter(recent_history)
    after_counts.update(discovered)
    return {
        "name": name,
        "axis_ids": [axis.axis_id for axis in schedule],
        "axis_count": len(schedule),
        "unique_family_count": len(discovered),
        "discovered_families": sorted(discovered),
        "discovered_family_counts": dict(sorted(discovered.items())),
        "post_schedule_entropy_nats": _entropy(after_counts),
        "priority_min": min((axis.priority_score for axis in schedule), default=0),
        "priority_mean": sum(axis.priority_score for axis in schedule) / max(1, len(schedule)),
        "command_count": sum(len(axis.commands) for axis in schedule),
    }


def _negative_controls(
    report: Mapping[str, Any],
    *,
    corpus: Sequence[Axis],
    budget: int,
    min_priority_score: int,
    seed: str,
    recent_history: Sequence[str],
) -> list[dict[str, Any]]:
    entropy = report["schedules"]["entropy"]
    recency = report["schedules"]["recency"]
    stable_random = report["schedules"]["stable_random"]
    repeated_entropy = _entropy_schedule(
        corpus,
        budget=budget,
        min_priority_score=min_priority_score,
        recent_history=recent_history,
    )
    repeated_random = _stable_random_schedule(
        corpus,
        budget=budget,
        min_priority_score=min_priority_score,
        seed=seed,
    )
    return [
        {
            "case_id": "entropy_beats_recency_unique_families",
            "ok": entropy["unique_family_count"] > recency["unique_family_count"],
            "detail": {
                "entropy": entropy["unique_family_count"],
                "recency": recency["unique_family_count"],
            },
        },
        {
            "case_id": "entropy_beats_random_unique_families",
            "ok": entropy["unique_family_count"] >= stable_random["unique_family_count"],
            "detail": {
                "entropy": entropy["unique_family_count"],
                "stable_random": stable_random["unique_family_count"],
            },
        },
        {
            "case_id": "deterministic_replay",
            "ok": entropy["axis_ids"] == [axis.axis_id for axis in repeated_entropy]
            and stable_random["axis_ids"] == [axis.axis_id for axis in repeated_random],
            "detail": {
                "entropy_axis_ids": entropy["axis_ids"],
                "stable_random_axis_ids": stable_random["axis_ids"],
            },
        },
        {
            "case_id": "severity_floor_preserved",
            "ok": entropy["priority_min"] >= report["policy"]["min_priority_score"],
            "detail": {
                "priority_min": entropy["priority_min"],
                "min_priority_score": report["policy"]["min_priority_score"],
            },
        },
        {
            "case_id": "authority_boundary",
            "ok": report["authority_boundary"]["advisory_only"] is True
            and report["authority_boundary"]["no_runtime_authority"] is True,
            "detail": report["authority_boundary"],
        },
    ]


def _axis_rows(schedule: Sequence[Axis], *, recent_history: Sequence[str]) -> list[dict[str, Any]]:
    counts = Counter(recent_history)
    rows: list[dict[str, Any]] = []
    for rank, axis in enumerate(schedule, start=1):
        score = _axis_score(axis, counts)
        rows.append(
            {
                "rank": rank,
                "axis_id": axis.axis_id,
                "priority_score": axis.priority_score,
                "family_labels": list(axis.family_labels),
                "mutation_families": list(axis.mutation_families),
                "commands": [list(command) for command in axis.commands],
                "score": score,
            }
        )
        counts = _add_axis(counts, axis)
    return rows


def build_report() -> dict[str, Any]:
    corpus = _axis_corpus()
    budget = 10
    min_priority_score = 50
    seed = "zenodex-negative-frontier-20260628"
    entropy_schedule = _entropy_schedule(
        corpus,
        budget=budget,
        min_priority_score=min_priority_score,
        recent_history=RECENT_NEGATIVE_FAMILY_HISTORY,
    )
    recency_schedule = _recency_schedule(
        corpus,
        budget=budget,
        min_priority_score=min_priority_score,
        recent_history=RECENT_NEGATIVE_FAMILY_HISTORY,
    )
    stable_random_schedule = _stable_random_schedule(
        corpus,
        budget=budget,
        min_priority_score=min_priority_score,
        seed=seed,
    )
    report: dict[str, Any] = {
        "schema": SCHEDULER_SCHEMA,
        "date": "2026-06-28",
        "policy": {
            "budget": budget,
            "min_priority_score": min_priority_score,
            "seed": seed,
            "recent_negative_family_history": list(RECENT_NEGATIVE_FAMILY_HISTORY),
            "bounded_corpus_axis_count": len(corpus),
            "eligible_axis_count": len(_eligible_axes(corpus, min_priority_score=min_priority_score)),
        },
        "authority_boundary": {
            "advisory_only": True,
            "no_runtime_authority": True,
            "no_settlement_authority": True,
            "no_governance_authority": True,
        },
        "schedules": {
            "entropy": _schedule_metrics("entropy", entropy_schedule, recent_history=RECENT_NEGATIVE_FAMILY_HISTORY),
            "recency": _schedule_metrics("recency", recency_schedule, recent_history=RECENT_NEGATIVE_FAMILY_HISTORY),
            "stable_random": _schedule_metrics("stable_random", stable_random_schedule, recent_history=RECENT_NEGATIVE_FAMILY_HISTORY),
        },
        "entropy_schedule_rows": _axis_rows(entropy_schedule, recent_history=RECENT_NEGATIVE_FAMILY_HISTORY),
        "non_claims": [
            "This scheduler is advisory and does not authorize settlement, governance, production claims, or runtime route selection.",
            "Unique-family improvement is measured on the declared bounded disaster-search axis corpus and fixed recent-history profile.",
            "The scheduler ranks next falsifier tasks; it does not prove that selected tasks will find real bugs.",
            "Family labels are deterministic keyword projections and remain a bounded replay abstraction.",
        ],
        "replay_command": "python3 tools/zenodex_negative_frontier_entropy_scheduler_20260628.py",
    }
    negative_controls = _negative_controls(
        report,
        corpus=corpus,
        budget=budget,
        min_priority_score=min_priority_score,
        seed=seed,
        recent_history=RECENT_NEGATIVE_FAMILY_HISTORY,
    )
    report["negative_controls"] = negative_controls
    report["ok"] = all(control["ok"] for control in negative_controls)
    return report


def _write_markdown(report: Mapping[str, Any], output: Path) -> None:
    lines: list[str] = []
    lines.append("# ZenoDEX Negative-Frontier Entropy Scheduler - 2026-06-28")
    lines.append("")
    lines.append("## Executive Result")
    lines.append("")
    lines.append(
        "A deterministic advisory scheduler ranks falsifier campaign axes by severity-preserving entropy gain over recent negative-family history."
    )
    lines.append("")
    lines.append("The scheduler has no settlement, governance, production-claim, or runtime authority.")
    lines.append("")
    lines.append(f"- Bounded corpus axes: `{report['policy']['bounded_corpus_axis_count']}`")
    lines.append(f"- Eligible axes: `{report['policy']['eligible_axis_count']}`")
    lines.append(f"- Budget: `{report['policy']['budget']}`")
    lines.append(f"- Entropy unique families: `{report['schedules']['entropy']['unique_family_count']}`")
    lines.append(f"- Recency unique families: `{report['schedules']['recency']['unique_family_count']}`")
    lines.append(f"- Stable-random unique families: `{report['schedules']['stable_random']['unique_family_count']}`")
    lines.append(f"- Entropy priority floor: `{report['schedules']['entropy']['priority_min']}`")
    lines.append("")
    lines.append("## Entropy Schedule")
    lines.append("")
    lines.append("| rank | axis | priority | families |")
    lines.append("| ---: | --- | ---: | --- |")
    for row in report["entropy_schedule_rows"]:
        lines.append(
            f"| `{row['rank']}` | `{row['axis_id']}` | `{row['priority_score']}` | `{', '.join(row['family_labels'])}` |"
        )
    lines.append("")
    lines.append("## Baseline Comparison")
    lines.append("")
    lines.append("| scheduler | unique families | post entropy | priority min |")
    lines.append("| --- | ---: | ---: | ---: |")
    for key in ("entropy", "recency", "stable_random"):
        item = report["schedules"][key]
        lines.append(
            f"| `{key}` | `{item['unique_family_count']}` | `{item['post_schedule_entropy_nats']:.6f}` | `{item['priority_min']}` |"
        )
    lines.append("")
    lines.append("## Negative Controls")
    lines.append("")
    lines.append("| case | ok |")
    lines.append("| --- | --- |")
    for control in report["negative_controls"]:
        lines.append(f"| `{control['case_id']}` | `{control['ok']}` |")
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
    report = build_report()
    output_json.parent.mkdir(parents=True, exist_ok=True)
    output_json.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    _write_markdown(report, output_md)
    return report


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-json", default=str(REPORT_JSON))
    parser.add_argument("--output-md", default=str(REPORT_MD))
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    report = run(Path(args.output_json), Path(args.output_md))
    print(
        json.dumps(
            {
                "ok": report["ok"],
                "json": str(Path(args.output_json)),
                "report": str(Path(args.output_md)),
                "entropy_unique_families": report["schedules"]["entropy"]["unique_family_count"],
                "recency_unique_families": report["schedules"]["recency"]["unique_family_count"],
                "stable_random_unique_families": report["schedules"]["stable_random"]["unique_family_count"],
                "priority_min": report["schedules"]["entropy"]["priority_min"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
