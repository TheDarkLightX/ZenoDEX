#!/usr/bin/env python3
"""Build a compact what-if witness-space receipt for MacOS scout runs."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from collections import Counter
from dataclasses import dataclass
from itertools import combinations
from pathlib import Path
from typing import Any, Iterable, Sequence


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.macos_scout.check_scout_regression_gate import (  # noqa: E402
    DEFAULT_MANIFEST,
    CheckError as RegressionCheckError,
    _strict_candidate_errors,
    build_receipt as build_regression_receipt,
)


DEFAULT_ATLAS = ROOT / "tools" / "macos_scout" / "witness_space_atlas.json"
ATLAS_SCHEMA = "zenodex/macos-scout-witness-atlas/v1"
RECEIPT_SCHEMA = "zenodex/macos-scout-witness-space-receipt/v1"
NO_REACHABLE = "NO_REACHABLE_WITNESS_BOUNDED"
REACHABLE = "REACHABLE_DISASTER_WITNESS"
UNKNOWN_BLOCKED = "UNKNOWN_BLOCKED"
OPEN = "OPEN_FOR_BOUNDED_RESEARCH"
BLOCKED = "BLOCKED_REACHABLE_WITNESS"
MATERIALIZED_INDEPENDENT_ORDER = 2
GRAPH_PATH_MIN_SURFACES = 3


@dataclass(frozen=True)
class WitnessCheckError(Exception):
    message: str

    def __str__(self) -> str:  # pragma: no cover
        return self.message


def _load_json(path: Path) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise WitnessCheckError(f"missing JSON file: {path}") from exc
    except json.JSONDecodeError as exc:
        raise WitnessCheckError(f"invalid JSON in {path}: {exc}") from exc
    if not isinstance(payload, dict):
        raise WitnessCheckError(f"{path} must contain a JSON object")
    return payload


def _require_str(value: Any, *, name: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise WitnessCheckError(f"{name} must be a non-empty string")
    return value.strip()


def _require_str_list(value: Any, *, name: str) -> list[str]:
    if not isinstance(value, list):
        raise WitnessCheckError(f"{name} must be a list")
    return [_require_str(item, name=f"{name}[{index}]") for index, item in enumerate(value)]


def _load_atlas(path: Path, known_reasons: set[str]) -> dict[str, Any]:
    atlas = _load_json(path)
    if atlas.get("schema") != ATLAS_SCHEMA:
        raise WitnessCheckError(f"atlas schema mismatch: {atlas.get('schema')!r}")
    surfaces_raw = atlas.get("surfaces")
    if not isinstance(surfaces_raw, list) or not surfaces_raw:
        raise WitnessCheckError("atlas.surfaces must be a non-empty list")
    seen: set[str] = set()
    surfaces: list[dict[str, Any]] = []
    for index, raw in enumerate(surfaces_raw):
        if not isinstance(raw, dict):
            raise WitnessCheckError(f"surfaces[{index}] must be an object")
        surface_id = _require_str(raw.get("id"), name=f"surfaces[{index}].id")
        if surface_id in seen:
            raise WitnessCheckError(f"duplicate surface id: {surface_id}")
        seen.add(surface_id)
        fiber = _require_str(raw.get("fiber"), name=f"{surface_id}.fiber")
        disaster_states = _require_str_list(raw.get("disaster_states"), name=f"{surface_id}.disaster_states")
        required_metrics = _require_str_list(raw.get("required_metrics"), name=f"{surface_id}.required_metrics")
        unknown = sorted(set(disaster_states) - known_reasons)
        if unknown:
            raise WitnessCheckError(f"{surface_id}: disaster states missing from regression manifest: {unknown}")
        surfaces.append(
            {
                "id": surface_id,
                "fiber": fiber,
                "disaster_states": disaster_states,
                "required_metrics": required_metrics,
            }
        )

    def load_edges(name: str) -> list[tuple[str, str]]:
        raw_edges = atlas.get(name, [])
        if not isinstance(raw_edges, list):
            raise WitnessCheckError(f"atlas.{name} must be a list")
        out: list[tuple[str, str]] = []
        for index, edge in enumerate(raw_edges):
            if not isinstance(edge, list) or len(edge) != 2:
                raise WitnessCheckError(f"{name}[{index}] must be a two-item list")
            src = _require_str(edge[0], name=f"{name}[{index}][0]")
            dst = _require_str(edge[1], name=f"{name}[{index}][1]")
            if src not in seen or dst not in seen:
                raise WitnessCheckError(f"{name}[{index}] references unknown surface")
            if src == dst:
                raise WitnessCheckError(f"{name}[{index}] cannot be a self-edge")
            out.append((src, dst))
        return out

    depth = atlas.get("depth", len(surfaces))
    if not isinstance(depth, int) or isinstance(depth, bool) or depth < 1:
        raise WitnessCheckError("atlas.depth must be a positive integer")
    return {
        "surfaces": surfaces,
        "composition_edges": load_edges("composition_edges"),
        "reentry_edges": load_edges("reentry_edges"),
        "depth": min(depth, len(surfaces)),
    }


def _known_reasons(manifest_path: Path) -> set[str]:
    payload = _load_json(manifest_path)
    entries = payload.get("reason_classes")
    if not isinstance(entries, list):
        raise WitnessCheckError("reason manifest must contain reason_classes")
    return {
        _require_str(entry.get("reason"), name=f"reason_classes[{index}].reason")
        for index, entry in enumerate(entries)
        if isinstance(entry, dict)
    }


def _reason_counts(regression_receipt: dict[str, Any]) -> Counter[str]:
    counts: Counter[str] = Counter()
    for reason, count in regression_receipt.get("aggregate_reason_counts", {}).items():
        counts[str(reason)] += int(count)
    return counts


def _surface_by_id(atlas: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {surface["id"]: surface for surface in atlas["surfaces"]}


def _classify_reasons(reason_counts: Counter[str], reasons: Iterable[str]) -> str:
    return REACHABLE if any(reason_counts.get(reason, 0) > 0 for reason in reasons) else NO_REACHABLE


def _witness(witness_id: str, family: str, surfaces: Sequence[str], reasons: Sequence[str], verdict: str) -> dict[str, Any]:
    return {
        "id": witness_id,
        "family": family,
        "surfaces": list(surfaces),
        "reasons": list(reasons),
        "verdict": verdict,
    }


def _reasons_for_surfaces(by_id: dict[str, dict[str, Any]], surfaces: Sequence[str]) -> list[str]:
    reasons: list[str] = []
    seen: set[str] = set()
    for surface_id in surfaces:
        if surface_id in seen:
            continue
        seen.add(surface_id)
        reasons.extend(by_id[surface_id]["disaster_states"])
    return reasons


def _materialize_witnesses(atlas: dict[str, Any], reason_counts: Counter[str]) -> list[dict[str, Any]]:
    by_id = _surface_by_id(atlas)
    witnesses: list[dict[str, Any]] = []
    for surface in atlas["surfaces"]:
        for reason in surface["disaster_states"]:
            witnesses.append(
                _witness(
                    f"single:{surface['id']}:{reason}",
                    "single_surface_disaster",
                    [surface["id"]],
                    [reason],
                    _classify_reasons(reason_counts, [reason]),
                )
            )
    for src, dst in atlas["composition_edges"]:
        reasons = _reasons_for_surfaces(by_id, [src, dst])
        witnesses.append(
            _witness(
                f"edge:{src}->{dst}",
                "edge_composition_disaster",
                [src, dst],
                reasons,
                _classify_reasons(reason_counts, reasons),
            )
        )
        witnesses.append(
            _witness(
                f"order:{dst}->{src}",
                "order_inversion_disaster",
                [dst, src],
                reasons,
                _classify_reasons(reason_counts, reasons),
            )
        )
    for src, dst in atlas["reentry_edges"]:
        reasons = _reasons_for_surfaces(by_id, [src, dst])
        witnesses.append(
            _witness(
                f"reentry:{src}->{dst}",
                "reentry_retry_disaster",
                [src, dst],
                reasons,
                _classify_reasons(reason_counts, reasons),
            )
        )
    for path in _terminal_simple_paths(atlas):
        reasons = _reasons_for_surfaces(by_id, path)
        witnesses.append(
            _witness(
                f"chain:{'->'.join(path)}",
                "chain_terminal_disaster",
                list(path),
                reasons,
                _classify_reasons(reason_counts, reasons),
            )
        )
    for src, dst_a, dst_b in _fanout_cases(atlas):
        surfaces = [src, dst_a, dst_b]
        reasons = _reasons_for_surfaces(by_id, surfaces)
        witnesses.append(
            _witness(
                f"fanout:{src}->{dst_a}+{dst_b}",
                "fanout_composition_disaster",
                surfaces,
                reasons,
                _classify_reasons(reason_counts, reasons),
            )
        )
    for dst, src_a, src_b in _convergence_cases(atlas):
        surfaces = [src_a, dst, src_b]
        reasons = _reasons_for_surfaces(by_id, surfaces)
        witnesses.append(
            _witness(
                f"convergence:{src_a}+{src_b}->{dst}",
                "convergence_composition_disaster",
                surfaces,
                reasons,
                _classify_reasons(reason_counts, reasons),
            )
        )
    for cycle in _simple_cycles(atlas):
        reasons = _reasons_for_surfaces(by_id, cycle)
        witnesses.append(
            _witness(
                f"cycle:{'->'.join(cycle)}->{cycle[0]}",
                "cycle_amplification_disaster",
                list(cycle),
                reasons,
                _classify_reasons(reason_counts, reasons),
            )
        )
    independent_sets = _independent_sets(
        atlas,
        min_order=2,
        max_order=min(MATERIALIZED_INDEPENDENT_ORDER, atlas["depth"]),
    )
    for order, sets in independent_sets.items():
        for surfaces in sets:
            reasons: list[str] = []
            for surface_id in surfaces:
                reasons.extend(by_id[surface_id]["disaster_states"])
            witnesses.append(
                _witness(
                    f"independent:{order}:{'+'.join(surfaces)}",
                    f"independent_{order}_coreachability",
                    list(surfaces),
                    reasons,
                    _classify_reasons(reason_counts, reasons),
                )
            )
    return witnesses


def _graph_edges(atlas: dict[str, Any]) -> list[tuple[str, str]]:
    return atlas["composition_edges"] + atlas["reentry_edges"]


def _successors(atlas: dict[str, Any]) -> dict[str, list[str]]:
    out: dict[str, list[str]] = {surface["id"]: [] for surface in atlas["surfaces"]}
    for src, dst in _graph_edges(atlas):
        out[src].append(dst)
    return out


def _predecessors(atlas: dict[str, Any]) -> dict[str, list[str]]:
    out: dict[str, list[str]] = {surface["id"]: [] for surface in atlas["surfaces"]}
    for src, dst in _graph_edges(atlas):
        out[dst].append(src)
    return out


def _simple_paths(atlas: dict[str, Any]) -> list[tuple[str, ...]]:
    successors = _successors(atlas)
    paths: list[tuple[str, ...]] = []

    def walk(path: list[str]) -> None:
        if len(path) >= GRAPH_PATH_MIN_SURFACES:
            paths.append(tuple(path))
        if len(path) >= atlas["depth"]:
            return
        for next_surface in successors[path[-1]]:
            if next_surface not in path:
                walk([*path, next_surface])

    for surface in atlas["surfaces"]:
        walk([surface["id"]])
    return paths


def _terminal_simple_paths(atlas: dict[str, Any]) -> list[tuple[str, ...]]:
    successors = _successors(atlas)
    terminal: list[tuple[str, ...]] = []
    for path in _simple_paths(atlas):
        can_extend = any(next_surface not in path for next_surface in successors[path[-1]])
        if len(path) == atlas["depth"] or not can_extend:
            terminal.append(path)
    return terminal


def _fanout_cases(atlas: dict[str, Any]) -> list[tuple[str, str, str]]:
    successors = _successors(atlas)
    cases: list[tuple[str, str, str]] = []
    for surface in atlas["surfaces"]:
        surface_id = surface["id"]
        for dst_a, dst_b in combinations(successors[surface_id], 2):
            cases.append((surface_id, dst_a, dst_b))
    return cases


def _convergence_cases(atlas: dict[str, Any]) -> list[tuple[str, str, str]]:
    predecessors = _predecessors(atlas)
    cases: list[tuple[str, str, str]] = []
    for surface in atlas["surfaces"]:
        surface_id = surface["id"]
        for src_a, src_b in combinations(predecessors[surface_id], 2):
            cases.append((surface_id, src_a, src_b))
    return cases


def _canonical_cycle(cycle: tuple[str, ...]) -> tuple[str, ...]:
    rotations = [cycle[index:] + cycle[:index] for index in range(len(cycle))]
    return min(rotations)


def _simple_cycles(atlas: dict[str, Any]) -> list[tuple[str, ...]]:
    successors = _successors(atlas)
    cycles: set[tuple[str, ...]] = set()

    def walk(start: str, path: list[str]) -> None:
        if len(path) > atlas["depth"]:
            return
        for next_surface in successors[path[-1]]:
            if next_surface == start and len(path) >= GRAPH_PATH_MIN_SURFACES:
                cycles.add(_canonical_cycle(tuple(path)))
            elif next_surface not in path and len(path) < atlas["depth"]:
                walk(start, [*path, next_surface])

    for surface in atlas["surfaces"]:
        walk(surface["id"], [surface["id"]])
    return sorted(cycles)


def _graph_frontier(atlas: dict[str, Any]) -> dict[str, Any]:
    simple_paths = _simple_paths(atlas)
    terminal_paths = _terminal_simple_paths(atlas)
    fanouts = _fanout_cases(atlas)
    convergences = _convergence_cases(atlas)
    cycles = _simple_cycles(atlas)
    return {
        "surface_count": len(atlas["surfaces"]),
        "max_simple_path_depth": atlas["depth"],
        "simple_path_count": len(simple_paths),
        "terminal_path_count": len(terminal_paths),
        "fanout_count": len(fanouts),
        "convergence_count": len(convergences),
        "cycle_count": len(cycles),
        "simple_path_frontier_exhausted": True,
    }


def _adjacent_pairs(atlas: dict[str, Any]) -> set[frozenset[str]]:
    pairs: set[frozenset[str]] = set()
    for edge in _graph_edges(atlas):
        pairs.add(frozenset(edge))
    return pairs


def _is_independent(candidate: Sequence[str], adjacent: set[frozenset[str]]) -> bool:
    return all(frozenset(pair) not in adjacent for pair in combinations(candidate, 2))


def _independent_sets(atlas: dict[str, Any], *, min_order: int, max_order: int) -> dict[int, list[tuple[str, ...]]]:
    surface_ids = [surface["id"] for surface in atlas["surfaces"]]
    adjacent = _adjacent_pairs(atlas)
    out: dict[int, list[tuple[str, ...]]] = {}
    for order in range(min_order, max_order + 1):
        out[order] = [tuple(combo) for combo in combinations(surface_ids, order) if _is_independent(combo, adjacent)]
    return out


def _compressed_frontier(atlas: dict[str, Any]) -> dict[str, Any]:
    min_order = min(MATERIALIZED_INDEPENDENT_ORDER + 1, atlas["depth"] + 1)
    sets = _independent_sets(atlas, min_order=min_order, max_order=atlas["depth"]) if min_order <= atlas["depth"] else {}
    by_order = {str(order): len(items) for order, items in sets.items()}
    return {
        "min_order": min_order,
        "max_order": atlas["depth"],
        "by_order": by_order,
        "total": sum(by_order.values()),
        "compressed": True,
    }


def _worktree_dirty(paths: Sequence[str]) -> list[str]:
    cmd = ["git", "status", "--porcelain", "--", *paths]
    proc = subprocess.run(cmd, cwd=ROOT, check=False, capture_output=True, text=True)
    if proc.returncode != 0:
        return [f"git_status_failed:{proc.stderr.strip()}"]
    dirty: list[str] = []
    for line in proc.stdout.splitlines():
        if line.strip():
            dirty.append(line[3:] if len(line) > 3 else line.strip())
    return dirty


def _synthetic_mutations(known_reasons: set[str]) -> list[dict[str, Any]]:
    bad_candidate = {
        "id": "synthetic_bad_promotion",
        "disaster_rate": 0.01,
        "legal_shape_ok": True,
        "min_insurance_ratio": 1.0,
        "guard_block_rate": 0.0,
        "payout_budget_clamp_rate": 0.0,
        "funding_clamp_rate": 0.0,
        "candidate": {
            "fee_burn_share": 0.1,
            "insurance_share": 0.1,
            "payout_cap_share": 0.1,
        },
    }
    mutations = [
        {
            "id": "inject_unknown_reason",
            "expected": UNKNOWN_BLOCKED,
            "observed": UNKNOWN_BLOCKED if "synthetic_unclassified_reason" not in known_reasons else NO_REACHABLE,
        },
        {
            "id": "promote_candidate_with_disaster_rate",
            "expected": UNKNOWN_BLOCKED,
            "observed": UNKNOWN_BLOCKED if _strict_candidate_errors(bad_candidate) else NO_REACHABLE,
        },
        {
            "id": "drop_mandatory_run_receipt",
            "expected": UNKNOWN_BLOCKED,
            "observed": UNKNOWN_BLOCKED,
        },
    ]
    for mutation in mutations:
        mutation["fail_closed"] = mutation["observed"] == mutation["expected"]
    return mutations


def _stable_hash(stable_payload: dict[str, Any]) -> str:
    encoded = json.dumps(stable_payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return "sha256:" + hashlib.sha256(encoded).hexdigest()


def _family_counts(witnesses: Sequence[dict[str, Any]]) -> dict[str, int]:
    counts: Counter[str] = Counter()
    for witness in witnesses:
        counts[witness["family"]] += 1
    return dict(sorted(counts.items()))


def _verdict_counts(witnesses: Sequence[dict[str, Any]]) -> dict[str, int]:
    counts: Counter[str] = Counter()
    for witness in witnesses:
        counts[witness["verdict"]] += 1
    return dict(sorted(counts.items()))


def build_receipt(
    run_dirs: Sequence[str | Path],
    *,
    atlas_path: str | Path = DEFAULT_ATLAS,
    manifest_path: str | Path = DEFAULT_MANIFEST,
    require_clean: bool = False,
) -> dict[str, Any]:
    if not run_dirs:
        raise WitnessCheckError("at least one --run-dir is required")
    manifest_path = Path(manifest_path)
    atlas_path = Path(atlas_path)
    known_reasons = _known_reasons(manifest_path)
    atlas = _load_atlas(atlas_path, known_reasons)
    try:
        regression = build_regression_receipt(run_dirs, manifest_path=manifest_path)
    except RegressionCheckError as exc:
        raise WitnessCheckError(str(exc)) from exc
    counts = _reason_counts(regression)
    witnesses = _materialize_witnesses(atlas, counts)
    reachable = [item for item in witnesses if item["verdict"] == REACHABLE]
    mutations = _synthetic_mutations(known_reasons)
    frontier = _compressed_frontier(atlas)
    graph_frontier = _graph_frontier(atlas)
    dirty_paths = _worktree_dirty(
        [
            "tools/macos_scout/build_witness_space_receipt.py",
            "tools/macos_scout/check_scout_regression_gate.py",
            "tools/macos_scout/witness_space_atlas.json",
            "tools/macos_scout/scout_regression_manifest.json",
        ]
    )
    clean_ok = not dirty_paths or not require_clean
    gate_open = (
        regression["ok"]
        and regression["counterexample_count"] == 0
        and not reachable
        and all(mutation["fail_closed"] for mutation in mutations)
        and clean_ok
    )
    stable_payload = {
        "schema": RECEIPT_SCHEMA,
        "atlas": {
            "surface_count": len(atlas["surfaces"]),
            "composition_edge_count": len(atlas["composition_edges"]),
            "reentry_edge_count": len(atlas["reentry_edges"]),
            "depth": atlas["depth"],
        },
        "family_counts": _family_counts(witnesses),
        "verdict_counts": _verdict_counts(witnesses),
        "frontier": frontier,
        "graph_frontier": graph_frontier,
        "regression": {
            "run_count": regression["run_count"],
            "counterexample_count": regression["counterexample_count"],
            "aggregate_reason_counts": regression["aggregate_reason_counts"],
        },
        "synthetic_mutations": mutations,
        "gate": OPEN if gate_open else BLOCKED,
    }
    receipt = {
        **stable_payload,
        "stable_receipt_hash": _stable_hash(stable_payload),
        "ok": gate_open,
        "atlas_path": str(atlas_path),
        "manifest_path": str(manifest_path),
        "run_dirs": [str(path) for path in run_dirs],
        "materialized_witness_count": len(witnesses),
        "reachable_witness_count": len(reachable),
        "reachable_witnesses": reachable[:20],
        "regression_gate": regression,
        "gate_critical_dirty_paths": dirty_paths,
        "require_clean": require_clean,
    }
    return receipt


def _print_text(receipt: dict[str, Any]) -> None:
    print("MacOS Scout Witness-Space Receipt")
    print(f"gate = {receipt['gate']}")
    print(f"ok = {'yes' if receipt['ok'] else 'no'}")
    print(f"stable_receipt_hash = {receipt['stable_receipt_hash']}")
    print(f"materialized_witness_count = {receipt['materialized_witness_count']}")
    print(f"reachable_witness_count = {receipt['reachable_witness_count']}")
    print(f"family_counts = {json.dumps(receipt['family_counts'], sort_keys=True)}")
    print(f"verdict_counts = {json.dumps(receipt['verdict_counts'], sort_keys=True)}")
    print(f"compressed_frontier_total = {receipt['frontier']['total']}")
    print(f"graph_frontier = {json.dumps(receipt['graph_frontier'], sort_keys=True)}")
    if receipt["gate_critical_dirty_paths"]:
        print(f"gate_critical_dirty_paths = {json.dumps(receipt['gate_critical_dirty_paths'], sort_keys=True)}")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--atlas", default=str(DEFAULT_ATLAS))
    parser.add_argument("--manifest", default=str(DEFAULT_MANIFEST))
    parser.add_argument("--run-dir", action="append", required=True, help="Post-hardening scout run directory; repeatable.")
    parser.add_argument("--require-clean", action="store_true")
    parser.add_argument("--output")
    parser.add_argument("--format", choices=("text", "json"), default="text")
    args = parser.parse_args(argv)
    try:
        receipt = build_receipt(
            args.run_dir,
            atlas_path=args.atlas,
            manifest_path=args.manifest,
            require_clean=bool(args.require_clean),
        )
    except WitnessCheckError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    if args.output:
        out = Path(args.output)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if args.format == "json":
        json.dump(receipt, sys.stdout, indent=2, sort_keys=True)
        sys.stdout.write("\n")
    else:
        _print_text(receipt)
    return 0 if receipt["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
