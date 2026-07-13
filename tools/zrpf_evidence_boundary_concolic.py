#!/usr/bin/env python3
"""Build a bounded offline path atlas for the ZRPF evidence checkers.

This tool is a deterministic bug-discovery sidecar. It does not verify RISC0
receipt seals, prove checker correctness, or authorize an evidence claim.
"""

from __future__ import annotations

import argparse
import copy
import functools
import hashlib
import heapq
import importlib
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Callable, Sequence

ROOT_DIR = Path(__file__).resolve().parents[1]
if str(ROOT_DIR) not in sys.path:
    sys.path.insert(0, str(ROOT_DIR))

adapter_checker = importlib.import_module(
    "tools.check_zrpf_v1_spot_adapter_temporary_evidence"
)
tree_checker = importlib.import_module(
    "tools.check_zrpf_v3_structural_tree_temporary_evidence"
)
v4_checker = importlib.import_module(
    "tools.check_zrpf_v4_spot_value_leaf_local_evidence"
)


MAX_DEPTH = 2
MAX_FRONTIER = 64

MutationFn = Callable[[dict[str, Any]], None]


@dataclass(frozen=True)
class Mutation:
    name: str
    apply_in_place: MutationFn


@dataclass(frozen=True)
class Target:
    name: str
    checker: Any
    mutations: tuple[Mutation, ...]
    minimum_unique_paths: int


@dataclass(frozen=True)
class BoundaryCase:
    mutation: str
    depth: int
    outcome_label: str
    path_id: str
    path_length: int


@dataclass(frozen=True)
class BoundaryTargetReport:
    target: str
    valid_seed_accepted: bool
    mutated_states_explored: int
    mutated_states_cleanly_rejected: int
    all_mutated_states_rejected: bool
    max_depth_reached: int
    unique_outcome_count: int
    unique_path_count: int
    minimum_unique_paths: int
    minimum_unique_paths_met: bool
    trace_files: tuple[str, ...]
    cases: tuple[BoundaryCase, ...]


def _set_path(document: dict[str, Any], path: tuple[Any, ...], value: Any) -> None:
    cursor: Any = document
    for part in path[:-1]:
        cursor = cursor[part]
    cursor[path[-1]] = value


def _add_unknown_adapter_field(document: dict[str, Any]) -> None:
    document["adapter"]["receipt"]["unreviewed_authority"] = True


def _add_unknown_tree_field(document: dict[str, Any]) -> None:
    document["nodes"][6]["receipt"]["unreviewed_authority"] = True


ADAPTER_MUTATIONS = (
    Mutation("unknown_nested_field", _add_unknown_adapter_field),
    Mutation(
        "claim_overpromotion",
        lambda document: _set_path(document, ("claims", "release_backed"), True),
    ),
    Mutation(
        "source_path_escape",
        lambda document: _set_path(
            document,
            ("evidence_build_sources", "files", 0, "path"),
            "../escape.rs",
        ),
    ),
    Mutation(
        "source_hash_drift",
        lambda document: _set_path(
            document,
            ("evidence_build_sources", "files", 0, "sha256"),
            "00" * 32,
        ),
    ),
    Mutation(
        "image_word_mismatch",
        lambda document: _set_path(
            document,
            ("adapter", "image_id_words", 0),
            0,
        ),
    ),
    Mutation(
        "negative_control_drift",
        lambda document: _set_path(
            document,
            ("negative_controls", 0, "passed"),
            False,
        ),
    ),
)


TREE_MUTATIONS = (
    Mutation("unknown_nested_field", _add_unknown_tree_field),
    Mutation(
        "claim_overpromotion",
        lambda document: _set_path(document, ("claims", "release_backed"), True),
    ),
    Mutation(
        "source_path_escape",
        lambda document: _set_path(
            document,
            ("verification_sources", "files", 0, "path"),
            "../escape.rs",
        ),
    ),
    Mutation(
        "source_hash_drift",
        lambda document: _set_path(
            document,
            ("guest_build_sources", "files", 0, "sha256"),
            "00" * 32,
        ),
    ),
    Mutation(
        "image_word_mismatch",
        lambda document: _set_path(
            document,
            ("programs", 1, "image_id_words", 0),
            0,
        ),
    ),
    Mutation(
        "negative_control_drift",
        lambda document: _set_path(
            document,
            ("negative_controls", 0, "passed"),
            False,
        ),
    ),
    Mutation(
        "topology_partition_gap",
        lambda document: _set_path(
            document,
            ("nodes", 5, "topology", "partition_start"),
            3,
        ),
    ),
    Mutation(
        "topology_count_mismatch",
        lambda document: _set_path(
            document,
            ("nodes", 6, "topology", "leaf_count"),
            5,
        ),
    ),
    Mutation(
        "cross_field_parent_mismatch",
        lambda document: _set_path(
            document,
            ("nodes", 0, "parent_id"),
            "l1-right",
        ),
    ),
)


def _add_unknown_v4_program_field(document: dict[str, Any]) -> None:
    document["program"]["unreviewed_authority"] = True


V4_MUTATIONS = (
    Mutation("unknown_nested_field", _add_unknown_v4_program_field),
    Mutation(
        "claim_overpromotion",
        lambda document: _set_path(
            document,
            ("claims", "manifest_authorizes_production"),
            True,
        ),
    ),
    Mutation(
        "boolean_integer_substitution",
        lambda document: _set_path(
            document,
            ("claims", "manifest_authorizes_settlement"),
            0,
        ),
    ),
    Mutation(
        "proof_source_tree_drift",
        lambda document: _set_path(
            document,
            ("proof_generation_source", "tree"),
            "00" * 20,
        ),
    ),
    Mutation(
        "verifier_source_commit_drift",
        lambda document: _set_path(
            document,
            ("native_replay_verifier", "source_commit"),
            "00" * 20,
        ),
    ),
    Mutation(
        "verifier_binary_hash_drift",
        lambda document: _set_path(
            document,
            ("native_replay_verifier", "recorded_executable_sha256"),
            "00" * 32,
        ),
    ),
    Mutation(
        "receipt_hash_drift",
        lambda document: _set_path(
            document,
            ("artifacts", 0, "sha256"),
            "00" * 32,
        ),
    ),
    Mutation(
        "journal_hash_drift",
        lambda document: _set_path(
            document,
            ("artifacts", 1, "journal_sha256"),
            "00" * 32,
        ),
    ),
    Mutation(
        "mutation_index_drift",
        lambda document: _set_path(
            document,
            ("mutation_control", "seal_word_index"),
            2,
        ),
    ),
    Mutation(
        "supporting_path_escape",
        lambda document: _set_path(
            document,
            ("native_replay", "supporting_inputs", 0, "path"),
            "../source.json",
        ),
    ),
    Mutation(
        "positive_report_hash_drift",
        lambda document: _set_path(
            document,
            ("native_replay", "expected_positive_report", "sha256"),
            "00" * 32,
        ),
    ),
    Mutation(
        "dev_mode_policy_disabled",
        lambda document: _set_path(
            document,
            ("native_replay", "dev_mode_environment_must_reject"),
            False,
        ),
    ),
    Mutation(
        "dev_mode_report_hash_drift",
        lambda document: _set_path(
            document,
            ("native_replay", "expected_dev_mode_reject_report", "sha256"),
            "00" * 32,
        ),
    ),
)


TARGETS = (
    Target(
        name="v1_spot_adapter_evidence",
        checker=adapter_checker,
        mutations=ADAPTER_MUTATIONS,
        minimum_unique_paths=6,
    ),
    Target(
        name="v3_structural_tree_evidence",
        checker=tree_checker,
        mutations=TREE_MUTATIONS,
        minimum_unique_paths=9,
    ),
    Target(
        name="v4_spot_value_leaf_evidence",
        checker=v4_checker,
        mutations=V4_MUTATIONS,
        minimum_unique_paths=10,
    ),
)
TARGET_INDEX = {target.name: target for target in TARGETS}


def _canonical_signature(document: dict[str, Any]) -> str:
    encoded = json.dumps(
        document,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _semantic_outcome(report: dict[str, Any]) -> str:
    if report.get("ok") is True:
        return "ok"
    errors = report.get("errors")
    if not isinstance(errors, list) or any(not isinstance(error, str) for error in errors):
        return "invalid_report"
    meaningful = [
        error
        for error in errors
        if "manifest canonical SHA-256" not in error
    ]
    selected = meaningful if meaningful else errors
    return "reject:" + "|".join(selected)


def _trace_validation(
    target: Target,
    document: dict[str, Any],
) -> tuple[str, str, int, bool]:
    trace_paths = {
        str(Path(target.checker.__file__).resolve()): Path(target.checker.__file__).name,
        str(Path(target.checker.support.__file__).resolve()): Path(
            target.checker.support.__file__
        ).name,
    }
    lines: list[str] = []
    last_location: str | None = None

    def tracer(frame, event, _arg):
        nonlocal last_location
        if event == "line":
            traced_name = trace_paths.get(frame.f_code.co_filename)
            if traced_name is not None:
                location = f"{traced_name}:{frame.f_lineno}"
                if location != last_location:
                    lines.append(location)
                    last_location = location
        return tracer

    previous = sys.gettrace()
    try:
        sys.settrace(tracer)
        report = target.checker.validate_manifest(document)
    except Exception as exc:  # pragma: no cover - a regression test fails on this path
        outcome = f"exception:{type(exc).__name__}"
        clean_reject = False
    else:
        outcome = _semantic_outcome(report)
        clean_reject = report.get("ok") is False and outcome.startswith("reject:")
    finally:
        sys.settrace(previous)

    path_id = hashlib.sha256("\n".join(lines).encode("utf-8")).hexdigest()[:16]
    return outcome, path_id, len(lines), clean_reject


def _load_valid_seed(target: Target) -> dict[str, Any]:
    document, errors = target.checker.load_manifest()
    if errors or not isinstance(document, dict):
        raise RuntimeError(f"{target.name} valid seed failed to load")
    return document


def _with_cached_source_hashes(target: Target):
    """Cache immutable source bytes during one offline atlas exploration."""

    support = target.checker.support
    original = support.sha256_file
    cached = functools.lru_cache(maxsize=None)(original)
    support.sha256_file = cached
    return support, original, cached


def explore_target(
    name: str,
    *,
    max_depth: int = MAX_DEPTH,
    max_frontier: int = MAX_FRONTIER,
) -> BoundaryTargetReport:
    if max_depth < 0 or max_depth > MAX_DEPTH:
        raise ValueError(f"max_depth must be between 0 and {MAX_DEPTH}")
    if max_frontier < 1 or max_frontier > MAX_FRONTIER:
        raise ValueError(f"max_frontier must be between 1 and {MAX_FRONTIER}")

    target = TARGET_INDEX[name]
    seed = _load_valid_seed(target)
    support, original_sha256_file, cached_sha256_file = _with_cached_source_hashes(target)
    try:
        # This untraced validation both establishes the valid seed and primes the
        # source-file digest cache. Atlas paths then measure validation branches,
        # rather than repeated byte-reading loops over the same immutable files.
        baseline_report = target.checker.validate_manifest(seed)
        valid_seed_accepted = baseline_report.get("ok") is True

        frontier: list[tuple[int, int, int, str, dict[str, Any]]] = [
            (0, 0, 0, "valid_seed", copy.deepcopy(seed))
        ]
        seen_documents = {_canonical_signature(seed)}
        seen_pairs: set[tuple[str, str]] = set()
        seen_outcomes: set[str] = set()
        seen_paths: set[str] = set()
        cases: list[BoundaryCase] = []
        explored = 0
        mutated_explored = 0
        mutated_rejected = 0
        maximum_depth = 0
        schedule_sequence = 1

        while frontier and explored < max_frontier:
            depth, _priority, _sequence, mutation_name, document = heapq.heappop(
                frontier
            )
            explored += 1
            maximum_depth = max(maximum_depth, depth)
            outcome, path_id, path_length, clean_reject = _trace_validation(
                target,
                document,
            )
            if depth > 0:
                mutated_explored += 1
                mutated_rejected += int(clean_reject)

            pair = (outcome, path_id)
            if pair not in seen_pairs:
                seen_pairs.add(pair)
                seen_outcomes.add(outcome)
                seen_paths.add(path_id)
                cases.append(
                    BoundaryCase(
                        mutation=mutation_name,
                        depth=depth,
                        outcome_label=outcome,
                        path_id=path_id,
                        path_length=path_length,
                    )
                )

            if depth >= max_depth:
                continue
            for order, mutation in enumerate(target.mutations):
                candidate = copy.deepcopy(document)
                mutation.apply_in_place(candidate)
                signature = _canonical_signature(candidate)
                if signature in seen_documents:
                    continue
                seen_documents.add(signature)
                next_name = (
                    mutation.name
                    if mutation_name == "valid_seed"
                    else f"{mutation_name}->{mutation.name}"
                )
                heapq.heappush(
                    frontier,
                    (
                        depth + 1,
                        -path_length,
                        schedule_sequence + order,
                        next_name,
                        candidate,
                    ),
                )
            schedule_sequence += len(target.mutations)
    finally:
        support.sha256_file = original_sha256_file
        cached_sha256_file.cache_clear()

    unique_path_count = len(seen_paths)
    minimum_met = unique_path_count >= target.minimum_unique_paths
    cases.sort(
        key=lambda case: (
            case.outcome_label,
            case.depth,
            case.mutation,
            case.path_id,
        )
    )
    return BoundaryTargetReport(
        target=target.name,
        valid_seed_accepted=valid_seed_accepted,
        mutated_states_explored=mutated_explored,
        mutated_states_cleanly_rejected=mutated_rejected,
        all_mutated_states_rejected=(
            mutated_explored > 0 and mutated_explored == mutated_rejected
        ),
        max_depth_reached=maximum_depth,
        unique_outcome_count=len(seen_outcomes),
        unique_path_count=unique_path_count,
        minimum_unique_paths=target.minimum_unique_paths,
        minimum_unique_paths_met=minimum_met,
        trace_files=tuple(
            sorted(
                {
                    Path(target.checker.__file__).name,
                    Path(target.checker.support.__file__).name,
                }
            )
        ),
        cases=tuple(cases),
    )


def explore_all_targets() -> tuple[BoundaryTargetReport, ...]:
    return tuple(explore_target(target.name) for target in TARGETS)


def _reports_json(reports: Sequence[BoundaryTargetReport]) -> dict[str, Any]:
    return {
        "schema": "zenodex/zrpf-evidence-boundary-concolic/v1",
        "authority": "offline_discovery_only",
        "python_verifies_risc0_seal": False,
        "correctness_proof": False,
        "reports": [asdict(report) for report in reports],
    }


def _report_passes(report: BoundaryTargetReport) -> bool:
    return (
        report.valid_seed_accepted
        and report.all_mutated_states_rejected
        and report.max_depth_reached == MAX_DEPTH
        and report.minimum_unique_paths_met
    )


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--target",
        choices=("all",) + tuple(sorted(TARGET_INDEX)),
        default="all",
    )
    parser.add_argument("--format", choices=("json", "text"), default="json")
    args = parser.parse_args(list(argv) if argv is not None else None)

    reports = (
        explore_all_targets()
        if args.target == "all"
        else (explore_target(args.target),)
    )
    if args.format == "json":
        print(json.dumps(_reports_json(reports), sort_keys=True, indent=2))
    else:
        for report in reports:
            print(
                f"[{report.target}] paths={report.unique_path_count} "
                f"mutants={report.mutated_states_cleanly_rejected}/"
                f"{report.mutated_states_explored} depth={report.max_depth_reached}"
            )
    return 0 if all(_report_passes(report) for report in reports) else 1


if __name__ == "__main__":
    raise SystemExit(main())
