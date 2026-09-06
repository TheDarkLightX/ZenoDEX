"""Render source-pinned evidence for the adjacent-swap suffix-cache candidate.

Replay: ``python3 -B -m experiments.v3_adjacent_swap_cache_v1.render_evidence``

Rendering records source and test bytes.  It does not execute the focused test
suite, establish a complexity theorem, or qualify a production release.
"""

from experiments.v3_completion_followup_v1.render_evidence import _render

CHANGED_PATHS = (
    "src/core/batch_clearing_mci_ordering.py",
    "src/core/batch_clearing_ordering.py",
)

CHANGED_TEST_PATHS = ("tests/core/test_batch_clearing_refinement_cache_v1.py",)

DEPENDENCY_PATHS = (
    # Exact simulator and its curve/quote dispatch.
    "src/core/batch_clearing_ab_order.py",
    "src/kernels/python/settlement_swap_runtime_v1.py",
    "src/core/amm_dispatch.py",
    # Settlement dispatcher and the complete settlement/commitment encoders.
    "src/core/batch_clearing.py",
    "src/core/batch_clearing_compute.py",
    "src/core/batch_clearing_single_pool.py",
    "src/core/settlement.py",
    "src/integration/dex_engine.py",
    "src/integration/operations.py",
    "src/state/canonical.py",
    "src/state/intents.py",
    "src/state/pools.py",
    "src/state/balances.py",
)

REFERENCE_PATHS = (
    "tests/core/test_batch_clearing.py",
    "tests/core/test_batch_clearing_b_refinement.py",
    "tests/core/test_batch_clearing_properties.py",
    "tests/core/test_batch_clearing_global_refinement.py",
)

ARTIFACT_PATHS = (
    "docs/research/ZENODEX_ADJACENT_SWAP_CACHE_20260906.md",
    "experiments/v3_adjacent_swap_cache_v1/render_evidence.py",
)


def main() -> None:
    _render(
        "adjacent-swap-cache",
        CHANGED_PATHS + DEPENDENCY_PATHS + REFERENCE_PATHS + ARTIFACT_PATHS,
        CHANGED_TEST_PATHS,
        claim=(
            "Under a fixed pure deterministic integer simulator premise, the adjacent-swap "
            "cache returns the same intent objects and strict (A, B) scan result as the "
            "unchanged generic evaluator. Exact post-pair reserve equality permits suffix "
            "reuse; unequal reserves trigger full suffix resimulation, and accepted swaps "
            "update the cache coherently. The result is finite source-bound evidence."
        ),
        invariant="V3-ADJACENT-SWAP-SUFFIX-CACHE-PARITY",
        families=["differential", "property", "stateful"],
        bounds=[
            "fixed intent/pool inputs with ordinary integer contributions and exact (int, int) reserve tuples",
            "pure deterministic partial simulator with input-dependent exception parity and no real-simulator totality claim",
            "finite hand-built catalogue plus 120 seeded random batches and all catalogue permutations",
            "exact post-pair reserve equality for reuse and unequal-reserve full suffix resimulation",
            "accepted-swap cache update compared with a fresh rebuild",
            "left-to-right adjacent scan, strict lexicographic (A, B) improvement, and unchanged tie/order handling",
            "hand-computed stale-suffix mutant that changes the refined ordering",
            "complete recursive Settlement object, serialization, metadata, event, fill-reason, and commitment parity",
            "worst-case O(n^2) simulator calls per pass with unchanged pass count",
            "nested intent mutation oracle separates caller preservation from the simulator premise",
        ],
        rejection_reason=(
            "The refiner returns a fresh list while preserving intent object identity and caller "
            "inputs. Pure simulator exceptions retain exact type, arguments and message in both "
            "paths. The cache is a local ordering computation with no economic write port."
        ),
        change_kind="refactor",
        nonclaims=[
            "The finite tests do not prove an O(n) pass bound, universal near-linear behavior, optimality, or production throughput/latency.",
            "Generic evaluator callbacks remain on the generic path; no callback semantics are cached.",
            "No default, cap, rounding, wire, policy, settlement, or tie-break behavior is changed by this candidate.",
            "No Lean theorem or universal Python/Rust/compiler refinement is supplied for the cache.",
            "The worker reported 140 passes for its broader focused command, while the local final rerun here is 55 passed; root's prior 50-new plus 16-old result and any broader root gate are separate evidence.",
            "The source-level production candidate remains closed for release qualification; native builds, deployment, and live throughput are outside this packet.",
        ],
        created_date="2026-09-06",
    )


if __name__ == "__main__":
    main()
