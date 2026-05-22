from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from src.core.split_routing import PoolXY


@dataclass(frozen=True)
class SplitRoutingLaneCase:
    pool0: PoolXY
    pool1: PoolXY
    amount_in: int
    expected: tuple[int, int]

    def to_json(self) -> dict[str, Any]:
        return {
            "pool0": {"x": int(self.pool0.x), "y": int(self.pool0.y), "fee_bps": int(self.pool0.fee_bps)},
            "pool1": {"x": int(self.pool1.x), "y": int(self.pool1.y), "fee_bps": int(self.pool1.fee_bps)},
            "amount_in": int(self.amount_in),
            "expected": {"amount_out": int(self.expected[0]), "split_a": int(self.expected[1])},
        }


DGSTR_CURATED_CASES: tuple[SplitRoutingLaneCase, ...] = (
    SplitRoutingLaneCase(PoolXY(x=125, y=153, fee_bps=119), PoolXY(x=125, y=140, fee_bps=150), 6055, (281, 3100)),
    SplitRoutingLaneCase(PoolXY(x=177, y=199, fee_bps=157), PoolXY(x=176, y=50, fee_bps=159), 4622, (232, 2804)),
    SplitRoutingLaneCase(PoolXY(x=60, y=142, fee_bps=59), PoolXY(x=173, y=85, fee_bps=127), 4537, (217, 1654)),
    SplitRoutingLaneCase(PoolXY(x=124, y=140, fee_bps=48), PoolXY(x=197, y=206, fee_bps=33), 7934, (332, 2784)),
    SplitRoutingLaneCase(PoolXY(x=172, y=72, fee_bps=3), PoolXY(x=163, y=104, fee_bps=95), 9596, (170, 3958)),
    SplitRoutingLaneCase(PoolXY(x=85, y=143, fee_bps=44), PoolXY(x=194, y=27, fee_bps=32), 6371, (164, 2968)),
    SplitRoutingLaneCase(PoolXY(x=66, y=71, fee_bps=36), PoolXY(x=215, y=149, fee_bps=114), 5994, (210, 1502)),
)


STIMULI_BANK: tuple[dict[str, Any], ...] = (
    {
        "stimulus_id": "control.quasi_concavity",
        "family": "physics_control",
        "prompt": "Assume the continuous relaxation is quasi-concave. Can you replace dense enumeration with shrinking interval refinement and then project back to integers?",
        "design_shift": "Prefer interval-shrinking search over uniform grids.",
    },
    {
        "stimulus_id": "ds.cache_semantics",
        "family": "data_structure",
        "prompt": "If repeated quote calls dominate cost, which probe pattern reduces recomputation while preserving deterministic tie-breaks?",
        "design_shift": "Bias toward cached sparse probes plus bounded rescue scans.",
    },
    {
        "stimulus_id": "market.adversarial_plateau",
        "family": "adversarial_game",
        "prompt": "Assume integer rounding creates disconnected equal-output plateaus. How do you recover canonical leftmost ties without paying full-span cost?",
        "design_shift": "Separate quality search from canonical leftward rescue.",
    },
)


LANE_SPEC: dict[str, Any] = {
    "lane_id": "split_routing_exact_in_dgstr",
    "title": "DGSTR Split Routing",
    "representation": "integer split search over two CPMM pools",
    "abstraction_level": "bounded exact-in routing oracle with deterministic tie-break",
    "goal": "reduce exact-in split quote calls without changing bounded exact outputs on the declared easy manifold",
    "obligations": [
        "deterministic smallest-a tie-break among equal maxima",
        "no output regression on the curated corpus",
        "measurable quote-call reduction versus baseline_canon16",
    ],
    "invariants": [
        "exact_in objective is maximize total output",
        "feasible splits are integer a in [0, D] with both pool quotes valid",
        "ties are resolved by the smallest feasible split a",
    ],
    "baseline_families": [
        {
            "name": "baseline_canon16",
            "why": "current low-cost production baseline for easy regimes",
            "failure_mode": "wide disconnected maxima still force many quote calls",
        },
        {
            "name": "dense24/dense32",
            "why": "high-coverage fallback for hard regimes",
            "failure_mode": "quote-call cost scales poorly on deep-liquidity intervals",
        },
    ],
    "reformulation_axes": [
        "interval shrinking instead of uniform grid coverage",
        "cached sparse probes instead of repeated dense scans",
        "separate optimality search from canonical tie rescue",
    ],
    "performance_descriptors": {
        "asymptotic_profile": "O(log D + k * window)",
        "invariant_family": ["deterministic_canonicalization", "bounded_exact_match"],
        "failure_envelope": ["disconnected_plateaus", "hard high-pressure regimes"],
        "certificate_shape": ["bruteforce_corpus", "quote_call_budget"],
    },
    "stimulus_ids": [
        "control.quasi_concavity",
        "ds.cache_semantics",
        "market.adversarial_plateau",
    ],
    "hypotheses": [
        {
            "hypothesis_id": "split_dgstr_v1",
            "mechanism_change": "Add dgstr_v1: discrete ternary refinement plus bounded rescue scans for exact-in split routing.",
            "representation_shift_used": "reduce",
            "expected_metric_delta": [0, 1, 2, 3, 1],
            "null_hypothesis": "dgstr_v1 fails exact-match obligations on the curated corpus or does not materially reduce quote calls.",
            "falsification_recipe": "dgstr_exact_match",
            "support_recipe": "dgstr_eval_count",
            "formal_obligations": [
                "match brute-force outputs on the declared corpus",
                "preserve leftmost split tie-break on the declared corpus",
                "stay deterministic under identical inputs",
            ],
            "risk_modes": ["disconnected global plateaus", "hard stress manifolds outside the declared corpus"],
            "status": "proposed",
        },
        {
            "hypothesis_id": "split_adaptive_v7",
            "mechanism_change": "Route easy regimes to dgstr_v1 while preserving adaptive_v6 dense24/dense32 tiers for known hard manifolds.",
            "representation_shift_used": "restrict",
            "expected_metric_delta": [1, 1, 2, 2, 2],
            "null_hypothesis": "adaptive_v7 misroutes hard regimes or the dgstr easy-path does not preserve bounded exactness on the declared corpus.",
            "falsification_recipe": "dgstr_exact_match",
            "support_recipe": "dgstr_eval_count",
            "formal_obligations": [
                "keep dense32 escalation on the known hard witness family",
                "map the easy manifold to dgstr_v1 deterministically",
            ],
            "risk_modes": ["threshold drift", "overextending the easy manifold"],
            "status": "proposed",
        },
    ],
}


def lane_packet() -> dict[str, Any]:
    return {
        **LANE_SPEC,
        "stimuli": [stim for stim in STIMULI_BANK if stim["stimulus_id"] in set(LANE_SPEC["stimulus_ids"])],
        "curated_corpus": [case.to_json() for case in DGSTR_CURATED_CASES],
    }
