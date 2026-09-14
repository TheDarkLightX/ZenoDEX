"""Replay and time the global checker against its pinned pre-simplification source.

Run from the checkout: python -m tools.benchmark_global_refinement_v2
Requires repository history and the development test environment. Multi-receipt
fixtures exercise the generic relation, not a qualified economic epoch. Timing
is observational and never an acceptance threshold or throughput claim.
"""

import cProfile
import hashlib
import json
import statistics
import subprocess
import sys
import time
import types
from dataclasses import replace
from pathlib import Path

from src.core import global_economic_state_effect_refinement_v2 as current
from src.core.global_economic_state_v2 import ReplayStateV2
from tests.core.test_global_economic_state_effect_refinement_v2 import _asset_transfer_candidate

BASELINE = "1fcb00c857a05cc8088464b027b1759d7785b71c"
SOURCE = "src/core/global_economic_state_effect_refinement_v2.py"


def _baseline() -> tuple[types.ModuleType, str]:
    source = subprocess.check_output(["git", "show", f"{BASELINE}:{SOURCE}"])
    module = types.ModuleType("src.core._global_refiner_benchmark_baseline")
    module.__package__ = "src.core"
    sys.modules[module.__name__] = module
    exec(compile(source, f"{BASELINE}:{SOURCE}", "exec"), module.__dict__)
    return module, hashlib.sha256(source).hexdigest()


def _candidate(count: int) -> current.GlobalEconomicStateEffectRefinementCandidateV2:
    candidate = _asset_transfer_candidate()
    occurrences = tuple(
        sorted(
            (replace(candidate.consumed_occurrences[0], nonce=i + 1) for i in range(count)),
            key=lambda row: row.occurrence_id,
        )
    )
    replay = tuple(
        sorted(
            (ReplayStateV2(row.replay_id, row.occurrence_id) for row in occurrences),
            key=lambda row: row.replay_id,
        )
    )
    return replace(
        candidate,
        _post_state=replace(candidate.post_state, replay_state=replay),
        _effect_plan=replace(
            candidate.effect_plan,
            occurrence_consumptions=tuple(row.occurrence_id for row in occurrences),
        ),
        _consumed_occurrences=occurrences,
    )


def _convert(
    module: types.ModuleType, candidate: current.GlobalEconomicStateEffectRefinementCandidateV2
):
    return module.GlobalEconomicStateEffectRefinementCandidateV2(
        candidate.pre_state,
        candidate.post_state,
        candidate.effect_plan,
        candidate.consumed_occurrences,
        candidate.terminal_plan,
        candidate.oracle_plan,
    )


def _observe(module: types.ModuleType, candidate) -> tuple[str, ...]:
    try:
        result = module.refine_global_economic_state_effects_v2(candidate)
    except (ValueError, TypeError) as error:
        return ("reject", type(error).__name__, str(error))
    return ("accept", result.refinement_root, result.production_authority)


def _measure(module: types.ModuleType, candidate) -> dict[str, object]:
    times = []
    for _ in range(7):
        start = time.perf_counter_ns()
        module.refine_global_economic_state_effects_v2(candidate)
        times.append(time.perf_counter_ns() - start)
    profile = cProfile.Profile()
    profile.runcall(module.refine_global_economic_state_effects_v2, candidate)
    copies = sum(
        row.callcount
        for row in profile.getstats()
        if getattr(row.code, "co_name", None) == "snapshot_global_economic_state_v2"
    )
    return {"median_ns": int(statistics.median(times)), "samples_ns": times, "state_copies": copies}


def main() -> None:
    baseline, source_hash = _baseline()
    results, cases = [], 0
    for count in (1, 8, 64):
        candidate = _candidate(count)
        invalid = (
            replace(
                candidate,
                _post_state=replace(candidate.post_state, height=candidate.post_state.height + 1),
            ),
            replace(candidate, _post_state=replace(candidate.post_state, replay_state=())),
            replace(
                candidate,
                _post_state=replace(
                    candidate.post_state, writer_epoch=candidate.post_state.writer_epoch + 1
                ),
            ),
            replace(candidate, _consumed_occurrences=()),
        )
        for index, item in enumerate((candidate, *invalid)):
            before = _observe(baseline, _convert(baseline, item))
            after = _observe(current, item)
            if before != after or before[0] != ("accept" if index == 0 else "reject"):
                raise ValueError(f"refinement parity/control mismatch at {count}:{index}")
            cases += 1
        results.append(
            {
                "occurrences": count,
                "before": _measure(baseline, _convert(baseline, candidate)),
                "after": _measure(current, candidate),
            }
        )
    print(
        json.dumps(
            {
                "schema": "zenodex/global-refinement-comparison/v1",
                "baseline": BASELINE,
                "baseline_source_sha256": source_hash,
                "candidate_source_sha256": hashlib.sha256(Path(SOURCE).read_bytes()).hexdigest(),
                "parity_cases": cases,
                "results": results,
                "claim": "Bounded exact acceptance/root and typed rejection/message parity; local timing only. No release authority.",
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
