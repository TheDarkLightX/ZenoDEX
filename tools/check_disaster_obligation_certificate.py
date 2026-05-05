#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from itertools import combinations
from pathlib import Path
from typing import Any, Iterable, Mapping


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MANIFEST = REPO_ROOT / "tools" / "disaster_obligation_certificate_manifest.json"


class CertificateError(RuntimeError):
    pass


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise CertificateError(message)


def _as_dict(obj: Any, *, ctx: str) -> Mapping[str, Any]:
    _require(isinstance(obj, dict), f"{ctx}: expected object")
    return obj


def _as_list(obj: Any, *, ctx: str) -> list[Any]:
    _require(isinstance(obj, list), f"{ctx}: expected list")
    return obj


def _load_json(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception as exc:
        raise CertificateError(f"failed to read JSON {path}: {exc}") from exc


def _sorted_unique_strings(raw: Iterable[Any], *, ctx: str) -> tuple[str, ...]:
    values: list[str] = []
    for item in raw:
        _require(isinstance(item, str) and item, f"{ctx}: expected non-empty string item")
        values.append(item)
    return tuple(sorted(set(values)))


def _ordered_unique_strings(raw: Iterable[Any], *, ctx: str) -> tuple[str, ...]:
    values: list[str] = []
    seen: set[str] = set()
    for item in raw:
        _require(isinstance(item, str) and item, f"{ctx}: expected non-empty string item")
        _require(item not in seen, f"{ctx}: duplicate item {item!r}")
        seen.add(item)
        values.append(item)
    return tuple(values)


def _parse_named_sets(entries: Any, *, value_key: str, ctx: str) -> dict[str, tuple[str, ...]]:
    parsed: dict[str, tuple[str, ...]] = {}
    for index, raw_entry in enumerate(_as_list(entries, ctx=ctx)):
        entry = _as_dict(raw_entry, ctx=f"{ctx}[{index}]")
        name = entry.get("name")
        _require(isinstance(name, str) and name, f"{ctx}[{index}].name: expected non-empty string")
        _require(name not in parsed, f"{ctx}: duplicate name {name!r}")
        parsed[name] = _sorted_unique_strings(
            _as_list(entry.get(value_key), ctx=f"{ctx}[{index}].{value_key}"),
            ctx=f"{ctx}[{index}].{value_key}",
        )
        _require(parsed[name], f"{ctx}[{index}].{value_key}: empty set")
    return parsed


def _quotient_classes(axes: Mapping[str, tuple[str, ...]]) -> list[dict[str, Any]]:
    grouped: dict[tuple[str, ...], list[str]] = {}
    for name, obligations in axes.items():
        grouped.setdefault(obligations, []).append(name)
    classes: list[dict[str, Any]] = []
    for index, (obligations, names) in enumerate(sorted(grouped.items(), key=lambda item: item[0]), start=1):
        classes.append(
            {
                "class_id": f"Q{index:02d}",
                "obligations": list(obligations),
                "axes": sorted(names),
            }
        )
    return classes


def _strict_subset(left: Iterable[str], right: Iterable[str]) -> bool:
    return set(left) < set(right)


def _maximal_antichain(classes: list[dict[str, Any]]) -> list[dict[str, Any]]:
    return [
        qclass
        for qclass in classes
        if not any(_strict_subset(qclass["obligations"], other["obligations"]) for other in classes)
    ]


def _dominated_classes(classes: list[dict[str, Any]]) -> list[dict[str, Any]]:
    dominated: list[dict[str, Any]] = []
    for qclass in classes:
        dominators = [
            other["class_id"]
            for other in classes
            if _strict_subset(qclass["obligations"], other["obligations"])
        ]
        if dominators:
            dominated.append(
                {
                    "class_id": qclass["class_id"],
                    "obligations": qclass["obligations"],
                    "dominated_by": dominators,
                }
            )
    return dominated


def _guard_union(selected: Iterable[str], guards: Mapping[str, tuple[str, ...]]) -> set[str]:
    covered: set[str] = set()
    for guard_name in selected:
        _require(guard_name in guards, f"selected guard {guard_name!r} is not defined")
        covered.update(guards[guard_name])
    return covered


def _required_obligations(classes: list[dict[str, Any]]) -> tuple[str, ...]:
    return tuple(sorted({ob for qclass in classes for ob in qclass["obligations"]}))


def _minimal_guard_sets(classes: list[dict[str, Any]], guards: Mapping[str, tuple[str, ...]]) -> list[list[str]]:
    guard_names = tuple(guards.keys())
    for width in range(1, len(guard_names) + 1):
        winners: list[list[str]] = []
        for selected in combinations(guard_names, width):
            covered = _guard_union(selected, guards)
            if all(set(qclass["obligations"]).issubset(covered) for qclass in classes):
                winners.append(list(selected))
        if winners:
            return winners
    return []


def _classify_candidate(
    obligations: tuple[str, ...],
    classes: list[dict[str, Any]],
    obligation_universe: Iterable[str],
) -> tuple[str, list[str], list[str]]:
    signature = set(obligations)
    missing = sorted(signature - set(obligation_universe))
    if missing:
        return "new_atom_required", [], missing

    exact = [qclass["class_id"] for qclass in classes if set(qclass["obligations"]) == signature]
    if exact:
        return "existing_class", exact, []

    dominators = [qclass["class_id"] for qclass in classes if signature < set(qclass["obligations"])]
    if dominators:
        return "dominated_by_existing_class", dominators, []

    dominated = [qclass["class_id"] for qclass in classes if set(qclass["obligations"]) < signature]
    if dominated:
        return "new_dominating_class_existing_atoms", dominated, []

    return "new_incomparable_class_existing_atoms", [], []


def evaluate_manifest(manifest: Mapping[str, Any]) -> dict[str, Any]:
    _require(int(manifest.get("manifest_version", -1)) == 1, "manifest_version mismatch")
    _require(manifest.get("schema") == "zenodex/disaster_obligation_certificate/v1", "schema mismatch")

    axes = _parse_named_sets(manifest.get("axes"), value_key="obligations", ctx="axes")
    guards = _parse_named_sets(manifest.get("guards"), value_key="covers", ctx="guards")
    selected = _ordered_unique_strings(
        _as_list(manifest.get("selected_guard_set"), ctx="selected_guard_set"),
        ctx="selected_guard_set",
    )

    classes = _quotient_classes(axes)
    antichain = _maximal_antichain(classes)
    dominated = _dominated_classes(classes)
    required = _required_obligations(antichain)
    selected_covered = _guard_union(selected, guards)
    selected_covers_required = set(required).issubset(selected_covered)

    all_guard_names = tuple(guards.keys())
    private_witnesses: list[dict[str, Any]] = []
    for index, raw_witness in enumerate(_as_list(manifest.get("private_witnesses"), ctx="private_witnesses")):
        witness = _as_dict(raw_witness, ctx=f"private_witnesses[{index}]")
        guard_name = witness.get("guard_name")
        obligation = witness.get("private_obligation")
        _require(isinstance(guard_name, str) and guard_name in guards, f"private_witnesses[{index}].guard_name is not defined")
        _require(isinstance(obligation, str) and obligation, f"private_witnesses[{index}].private_obligation is invalid")
        covering_guards = [name for name in all_guard_names if obligation in guards[name]]
        required_by = [qclass["class_id"] for qclass in classes if obligation in qclass["obligations"]]
        valid = (
            guard_name in selected
            and obligation in required
            and covering_guards == [guard_name]
            and bool(required_by)
        )
        private_witnesses.append(
            {
                "guard_name": guard_name,
                "private_obligation": obligation,
                "covering_guards": covering_guards,
                "required_by_class_ids": required_by,
                "valid": valid,
            }
        )

    witness_guard_set = {w["guard_name"] for w in private_witnesses if w["valid"]}
    selected_guards_all_forced = witness_guard_set == set(selected)
    exhaustive_minimal = _minimal_guard_sets(antichain, guards)

    obligation_universe = _required_obligations(classes)
    candidate_results: list[dict[str, Any]] = []
    for index, raw_probe in enumerate(_as_list(manifest.get("candidate_probes", []), ctx="candidate_probes")):
        probe = _as_dict(raw_probe, ctx=f"candidate_probes[{index}]")
        name = probe.get("name")
        _require(isinstance(name, str) and name, f"candidate_probes[{index}].name invalid")
        obligations = _sorted_unique_strings(
            _as_list(probe.get("obligations"), ctx=f"candidate_probes[{index}].obligations"),
            ctx=f"candidate_probes[{index}].obligations",
        )
        classification, matched, missing = _classify_candidate(obligations, classes, obligation_universe)
        expected = probe.get("expected_classification")
        candidate_results.append(
            {
                "name": name,
                "obligations": list(obligations),
                "classification": classification,
                "matched_class_ids": matched,
                "missing_obligations": missing,
                "expected_classification": expected,
                "classification_matches_expected": expected is None or classification == expected,
            }
        )

    result = {
        "ok": True,
        "axis_count": len(axes),
        "quotient_class_count": len(classes),
        "antichain_class_count": len(antichain),
        "dominated_class_count": len(dominated),
        "required_obligation_count": len(required),
        "guard_count": len(guards),
        "selected_guard_count": len(selected),
        "private_witness_count": len(private_witnesses),
        "compression_ratio_axis_to_antichain": f"{len(axes)}:{len(antichain)}",
        "selected_guard_set": list(selected),
        "required_obligations": list(required),
        "quotient_classes": classes,
        "antichain_class_ids": [qclass["class_id"] for qclass in antichain],
        "dominated_classes": dominated,
        "selected_guard_set_covers_required_obligations": selected_covers_required,
        "selected_guards_all_forced": selected_guards_all_forced,
        "private_certificate_proves_subset_minimality": bool(selected_covers_required and selected_guards_all_forced),
        "private_certificate_proves_cardinality_optimality": bool(selected_covers_required and selected_guards_all_forced),
        "private_witnesses": private_witnesses,
        "exhaustive_minimal_guard_sets": exhaustive_minimal,
        "exhaustive_search_agrees_with_private_certificate": exhaustive_minimal == [list(selected)] and selected_covers_required and selected_guards_all_forced,
        "candidate_probes": candidate_results,
    }
    return result


def check_result_against_manifest(result: Mapping[str, Any], manifest: Mapping[str, Any]) -> None:
    expected = _as_dict(manifest.get("expected"), ctx="expected")
    for key, expected_value in expected.items():
        _require(result.get(key) == expected_value, f"{key} mismatch: {result.get(key)!r} != {expected_value!r}")

    bad_witnesses = [w for w in result["private_witnesses"] if not w["valid"]]
    _require(not bad_witnesses, f"invalid private witnesses: {bad_witnesses!r}")

    bad_probes = [p for p in result["candidate_probes"] if not p["classification_matches_expected"]]
    _require(not bad_probes, f"candidate probe classification mismatch: {bad_probes!r}")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Check the ZenoDEX disaster-obligation minimizer certificate.")
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--report", type=Path, default=None, help="Optional JSON report output path")
    args = parser.parse_args(argv)

    manifest = _as_dict(_load_json(args.manifest.resolve()), ctx=str(args.manifest))
    result = evaluate_manifest(manifest)
    if args.report is not None:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    check_result_against_manifest(result, manifest)

    print(
        "ok: "
        f"axes={result['axis_count']} "
        f"quotient={result['quotient_class_count']} "
        f"antichain={result['antichain_class_count']} "
        f"selected_guards={result['selected_guard_count']} "
        f"private_witnesses={result['private_witness_count']}"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except CertificateError as exc:
        print(f"error: {exc}", file=sys.stderr)
        raise SystemExit(1)
