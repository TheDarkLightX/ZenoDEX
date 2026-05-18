#!/usr/bin/env python3
"""Sweep top-k and checked-stop audit rates over a UPBA v2 energy dataset."""

from __future__ import annotations

import argparse
import json
import sys
from collections import defaultdict
from hashlib import sha256
from pathlib import Path
from statistics import mean
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.energy.upba_v2_energy_model import LinearEnergyModel, load_linear_model

DEFAULT_TOP_KS = (1, 2, 3, 5, 10, 25)
DEFAULT_MODES = ("hand", "learned", "hybrid", "random")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dataset", type=Path, required=True)
    parser.add_argument("--model", type=Path)
    parser.add_argument("--modes", default=",".join(DEFAULT_MODES))
    parser.add_argument("--top-ks", default=",".join(str(value) for value in DEFAULT_TOP_KS))
    parser.add_argument("--seed", type=int, default=20260517)
    parser.add_argument("--max-batches", type=int)
    parser.add_argument("--output-json", type=Path)
    parser.add_argument("--output-markdown", type=Path)
    args = parser.parse_args()

    modes = _parse_csv(args.modes)
    top_ks = _parse_int_csv(args.top_ks, name="--top-ks")
    if not modes:
        raise SystemExit("--modes must contain at least one mode")
    unknown_modes = sorted(set(modes) - set(DEFAULT_MODES))
    if unknown_modes:
        raise SystemExit(f"unknown mode(s): {', '.join(unknown_modes)}")
    if not top_ks or any(value <= 0 for value in top_ks):
        raise SystemExit("--top-ks must contain positive integers")
    if any(mode in {"learned", "hybrid"} for mode in modes):
        if args.model is None:
            raise SystemExit("--model is required for learned or hybrid mode")
        model = load_linear_model(args.model)
    else:
        model = None

    rows = _load_rows(args.dataset, max_batches=args.max_batches)
    report = sweep_rows(
        rows,
        model=model,
        modes=tuple(modes),
        top_ks=tuple(sorted(set(top_ks))),
        seed=args.seed,
        dataset_path=args.dataset,
    )
    encoded = json.dumps(report, indent=2, sort_keys=True)
    if args.output_json is not None:
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(encoded + "\n", encoding="utf-8")
    if args.output_markdown is not None:
        args.output_markdown.parent.mkdir(parents=True, exist_ok=True)
        args.output_markdown.write_text(_markdown_report(report), encoding="utf-8")
    print(encoded)
    return 0


def sweep_rows(
    rows: list[dict[str, Any]],
    *,
    model: LinearEnergyModel | None,
    modes: tuple[str, ...] = DEFAULT_MODES,
    top_ks: tuple[int, ...] = DEFAULT_TOP_KS,
    seed: int = 20260517,
    dataset_path: Path | None = None,
) -> dict[str, Any]:
    by_batch: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        by_batch[str(row["batch_id"])].append(row)

    mode_reports = {
        mode: _sweep_mode(
            batches=by_batch,
            mode=mode,
            model=model,
            top_ks=top_ks,
            seed=seed,
        )
        for mode in modes
    }
    return {
        "schema": "zenodex/energy/upba_v2_topk_sweep/v1",
        "dataset": str(dataset_path) if dataset_path is not None else None,
        "rows": len(rows),
        "batches_total": len(by_batch),
        "top_ks": list(top_ks),
        "modes": mode_reports,
    }


def _sweep_mode(
    *,
    batches: dict[str, list[dict[str, Any]]],
    mode: str,
    model: LinearEnergyModel | None,
    top_ks: tuple[int, ...],
    seed: int,
) -> dict[str, Any]:
    batches_with_winner = 0
    candidate_counts: list[int] = []
    winner_positions: list[int] = []
    objective_winner_positions: list[int] = []
    objective_argmax_class_sizes: list[int] = []
    permutation_violations = 0
    topk_hits = {k: 0 for k in top_ks}
    objective_topk_hits = {k: 0 for k in top_ks}
    checked_stop_hits = {k: 0 for k in top_ks}
    checked_stop_at_winner_hits = 0
    checked_stop_at_objective_winner_hits = 0

    for batch_rows in batches.values():
        winner_rows = [row for row in batch_rows if row["label"]["is_winner"]]
        if not winner_rows:
            continue
        batches_with_winner += 1
        winner = winner_rows[0]
        ordered = _ordered_rows(batch_rows, mode=mode, model=model, seed=seed)
        candidate_counts.append(len(ordered))
        if sorted(row["candidate_hash"] for row in ordered) != sorted(
            row["candidate_hash"] for row in batch_rows
        ):
            permutation_violations += 1

        winner_index = next(
            index
            for index, row in enumerate(ordered, start=1)
            if row["candidate_hash"] == winner["candidate_hash"]
        )
        objective_winner_index = next(
            index
            for index, row in enumerate(ordered, start=1)
            if _objective_equivalent_rows(row, winner)
        )
        winner_positions.append(winner_index)
        objective_winner_positions.append(objective_winner_index)
        objective_argmax_class_sizes.append(
            sum(1 for row in batch_rows if _objective_equivalent_rows(row, winner))
        )
        checked_to_winner = ordered[:winner_index]
        suffix_after_winner = ordered[winner_index:]
        if _checked_stop_holds(winner, checked_to_winner, suffix_after_winner):
            checked_stop_at_winner_hits += 1
        checked_to_objective_winner = ordered[:objective_winner_index]
        suffix_after_objective_winner = ordered[objective_winner_index:]
        objective_winner = checked_to_objective_winner[-1]
        if _checked_stop_holds(
            objective_winner,
            checked_to_objective_winner,
            suffix_after_objective_winner,
        ):
            checked_stop_at_objective_winner_hits += 1

        for k in top_ks:
            clamped = min(k, len(ordered))
            if winner_index <= clamped:
                topk_hits[k] += 1
            if objective_winner_index <= clamped:
                objective_topk_hits[k] += 1
            checked = ordered[:clamped]
            suffix = ordered[clamped:]
            best_checked = _best_valid_row(checked)
            if best_checked is not None and _checked_stop_holds(best_checked, checked, suffix):
                checked_stop_hits[k] += 1

    return {
        "batches": batches_with_winner,
        "candidate_count_mean": mean(candidate_counts) if candidate_counts else 0,
        "mean_winner_position": mean(winner_positions) if winner_positions else 0,
        "mean_objective_winner_position": mean(objective_winner_positions)
        if objective_winner_positions
        else 0,
        "p95_winner_position": _percentile(winner_positions, 0.95),
        "p99_winner_position": _percentile(winner_positions, 0.99),
        "p95_objective_winner_position": _percentile(objective_winner_positions, 0.95),
        "p99_objective_winner_position": _percentile(objective_winner_positions, 0.99),
        "objective_tie_batch_count": sum(
            1 for value in objective_argmax_class_sizes if value > 1
        ),
        "objective_tie_batch_rate": _ratio(
            sum(1 for value in objective_argmax_class_sizes if value > 1),
            batches_with_winner,
        ),
        "objective_argmax_class_size_mean": mean(objective_argmax_class_sizes)
        if objective_argmax_class_sizes
        else 0,
        "permutation_violation_count": permutation_violations,
        "checked_stop_at_winner_rate": _ratio(checked_stop_at_winner_hits, batches_with_winner),
        "checked_stop_at_objective_winner_rate": _ratio(
            checked_stop_at_objective_winner_hits,
            batches_with_winner,
        ),
        "top_k": {
            str(k): {
                "top_k_recall": _ratio(topk_hits[k], batches_with_winner),
                "objective_top_k_recall": _ratio(
                    objective_topk_hits[k],
                    batches_with_winner,
                ),
                "checked_stop_top_k_rate": _ratio(checked_stop_hits[k], batches_with_winner),
                "false_exclusion_rate": 1.0 - _ratio(topk_hits[k], batches_with_winner),
                "objective_false_exclusion_rate": 1.0
                - _ratio(objective_topk_hits[k], batches_with_winner),
            }
            for k in top_ks
        },
    }


def _ordered_rows(
    rows: list[dict[str, Any]],
    *,
    mode: str,
    model: LinearEnergyModel | None,
    seed: int,
) -> list[dict[str, Any]]:
    if mode == "random":
        return sorted(
            rows,
            key=lambda row: sha256(
                f"{seed}:{row['batch_id']}:{row['candidate_hash']}".encode("utf-8")
            ).hexdigest(),
        )
    if mode == "hand":
        return sorted(rows, key=lambda row: (float(row["label"]["hand_energy"]), str(row["candidate_hash"])))
    if model is None:
        raise ValueError(f"{mode} mode requires a model")
    if mode == "learned":
        return sorted(rows, key=lambda row: (_model_energy(model, row), str(row["candidate_hash"])))
    if mode == "hybrid":
        return sorted(
            rows,
            key=lambda row: (
                _hard_barrier_from_row(row),
                _model_energy(model, row),
                str(row["candidate_hash"]),
            ),
        )
    raise ValueError(f"unknown mode: {mode}")


def _checked_stop_holds(
    winner: dict[str, Any],
    checked: list[dict[str, Any]],
    suffix: list[dict[str, Any]],
) -> bool:
    if not winner["label"]["valid"]:
        return False
    if all(row["candidate_hash"] != winner["candidate_hash"] for row in checked):
        return False
    return all(_row_cannot_beat(winner, row) for row in (*checked, *suffix))


def _row_cannot_beat(winner: dict[str, Any], other: dict[str, Any]) -> bool:
    if not other["label"]["valid"]:
        return True
    winner_score = _objective_score(winner)
    other_score = _objective_score(other)
    if other_score[0] < winner_score[0]:
        return True
    return other_score[0] == winner_score[0] and other_score[1] <= winner_score[1]


def _best_valid_row(rows: list[dict[str, Any]]) -> dict[str, Any] | None:
    valid = [row for row in rows if row["label"]["valid"]]
    if not valid:
        return None
    return max(valid, key=lambda row: (*_objective_score(row), str(row["candidate_hash"])))


def _objective_score(row: dict[str, Any]) -> tuple[int, int]:
    return (
        int(row["label"]["objective_volume"]),
        int(row["label"]["objective_surplus"]),
    )


def _objective_equivalent_rows(left: dict[str, Any], right: dict[str, Any]) -> bool:
    return bool(left["label"]["valid"]) and bool(right["label"]["valid"]) and (
        _objective_score(left) == _objective_score(right)
    )


def _model_energy(model: LinearEnergyModel, row: dict[str, Any]) -> float:
    return model.energy([float(value) for value in row["features"]])


def _hard_barrier_from_row(row: dict[str, Any]) -> float:
    features = {
        str(name): float(value)
        for name, value in zip(row["feature_names"], row["features"], strict=True)
    }

    def present(name: str) -> int:
        return 1 if features.get(name, 0.0) > 0.0 else 0

    return (
        1_000_000.0
        * (
            present("candidate_balance_violation_count_norm")
            + present("candidate_limit_violation_count_norm")
            + present("candidate_negative_reserve_flag")
            + present("candidate_invariant_violation_flag")
        )
        + 100_000.0
        * (
            present("candidate_noncanonical_fill_vector_flag")
            + present("candidate_schema_policy_mismatch_flag")
            + present("candidate_price_objective_violation_flag")
            + present("candidate_output_mismatch_count_norm")
            + present("candidate_fill_coverage_violation_flag")
            + present("candidate_duplicate_fill_id_flag")
            + present("candidate_unknown_fill_id_count_norm")
            + present("candidate_executed_input_over_amount_count_norm")
            + present("candidate_output_without_input_count_norm")
        )
        + 50_000.0 * present("candidate_price_ratio_unreduced_flag")
        + 10_000.0 * present("candidate_zero_net_input_count_norm")
    )


def _load_rows(path: Path, *, max_batches: int | None = None) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    seen_batches: set[str] = set()
    with path.open("r", encoding="utf-8") as handle:
        for line in handle:
            if not line.strip():
                continue
            row = json.loads(line)
            batch_id = str(row["batch_id"])
            if max_batches is not None and batch_id not in seen_batches and len(seen_batches) >= max_batches:
                break
            seen_batches.add(batch_id)
            rows.append(row)
    return rows


def _markdown_report(report: dict[str, Any]) -> str:
    lines = [
        "# ZenoEnergy Top-k Sweep",
        "",
        "```text",
        f"dataset: {report['dataset']}",
        f"rows: {report['rows']}",
        f"batches_total: {report['batches_total']}",
        f"top_ks: {', '.join(str(k) for k in report['top_ks'])}",
        "```",
        "",
        "| mode | k | top_k_recall | obj_top_k_recall | checked_stop_top_k | false_exclusion | obj_false_exclusion | mean_winner_pos | mean_obj_pos | p99_winner_pos | perm_violations |",
        "| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |",
    ]
    for mode, mode_report in report["modes"].items():
        for k in report["top_ks"]:
            metrics = mode_report["top_k"][str(k)]
            lines.append(
                "| "
                + " | ".join(
                    (
                        mode,
                        str(k),
                        _fmt(metrics["top_k_recall"]),
                        _fmt(metrics["objective_top_k_recall"]),
                        _fmt(metrics["checked_stop_top_k_rate"]),
                        _fmt(metrics["false_exclusion_rate"]),
                        _fmt(metrics["objective_false_exclusion_rate"]),
                        _fmt(mode_report["mean_winner_position"]),
                        _fmt(mode_report["mean_objective_winner_position"]),
                        str(mode_report["p99_winner_position"]),
                        str(mode_report["permutation_violation_count"]),
                    )
                )
                + " |"
            )
    lines.append("")
    lines.append("`checked_stop_top_k` is an offline audit over verified suffix labels.")
    lines.append("`obj_*` metrics treat tied valid volume/surplus maxima as one objective class.")
    return "\n".join(lines) + "\n"


def _parse_csv(value: str) -> list[str]:
    return [part.strip() for part in value.split(",") if part.strip()]


def _parse_int_csv(value: str, *, name: str) -> list[int]:
    out: list[int] = []
    for part in value.split(","):
        stripped = part.strip()
        if not stripped:
            continue
        try:
            out.append(int(stripped))
        except ValueError as exc:
            raise SystemExit(f"{name} contains a non-integer value: {stripped}") from exc
    return out


def _ratio(numerator: int, denominator: int) -> float:
    return 0.0 if denominator == 0 else numerator / denominator


def _percentile(values: list[int], fraction: float) -> int:
    if not values:
        return 0
    ordered = sorted(values)
    index = min(len(ordered) - 1, int(round((len(ordered) - 1) * fraction)))
    return ordered[index]


def _fmt(value: object) -> str:
    return f"{float(value):.3f}"


if __name__ == "__main__":
    raise SystemExit(main())
