from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from tools.morph_route_exact_out_2hop_value_miner import Route2HopValueCase


@dataclass(frozen=True)
class ExactOutLaneCase:
    x_ab: int
    y_ab: int
    fee_ab: int
    x_ac: int
    y_ac: int
    fee_ac: int
    x_cb: int
    y_cb: int
    fee_cb: int
    amount_out: int
    direct_in: int
    twohop_in: int

    def to_json(self) -> dict[str, Any]:
        return {
            "direct_pool": {"x": int(self.x_ab), "y": int(self.y_ab), "fee_bps": int(self.fee_ab)},
            "first_hop": {"x": int(self.x_ac), "y": int(self.y_ac), "fee_bps": int(self.fee_ac)},
            "second_hop": {"x": int(self.x_cb), "y": int(self.y_cb), "fee_bps": int(self.fee_cb)},
            "amount_out": int(self.amount_out),
            "expected": {"direct_in": int(self.direct_in), "twohop_in": int(self.twohop_in)},
        }

    def to_route_case(self) -> Route2HopValueCase:
        return Route2HopValueCase(
            x_ab=int(self.x_ab),
            y_ab=int(self.y_ab),
            fee_ab=int(self.fee_ab),
            x_ac=int(self.x_ac),
            y_ac=int(self.y_ac),
            fee_ac=int(self.fee_ac),
            x_cb=int(self.x_cb),
            y_cb=int(self.y_cb),
            fee_cb=int(self.fee_cb),
            amount_out=int(self.amount_out),
        )


EXACT_OUT_CURATED_CASES: tuple[ExactOutLaneCase, ...] = (
    ExactOutLaneCase(
        x_ab=2,
        y_ab=2,
        fee_ab=0,
        x_ac=1,
        y_ac=2,
        fee_ac=0,
        x_cb=1,
        y_cb=2,
        fee_cb=0,
        amount_out=1,
        direct_in=2,
        twohop_in=1,
    ),
)


STIMULI_BANK: tuple[dict[str, Any], ...] = (
    {
        "stimulus_id": "graph.path_relaxation",
        "family": "online_offline_dual",
        "prompt": "Treat exact-out routing as backward demand propagation over a graph. Which path relaxations expose regimes where an intermediate asset strictly lowers input cost?",
        "design_shift": "Prefer graph/path reasoning over single-pool local comparison.",
    },
    {
        "stimulus_id": "market.fragmented_liquidity",
        "family": "market_analogy",
        "prompt": "Assume direct liquidity is shallow but two adjacent markets are deeper. What minimal witness proves the topology itself is valuable before any heuristic optimization?",
        "design_shift": "Mine topology-value witnesses before optimizing router heuristics.",
    },
    {
        "stimulus_id": "certificate.cross_checker",
        "family": "dual_certificate",
        "prompt": "Require both kernel replay and a second independent arithmetic checker. Which exact-out witness survives both?",
        "design_shift": "Promote only cross-checked topology gains.",
    },
)


LANE_SPEC: dict[str, Any] = {
    "lane_id": "exact_out_multihop_value",
    "title": "Exact-Out Multihop Value",
    "representation": "2-hop exact-out topology witness over CPMM pools",
    "abstraction_level": "evidence-first lane proving multihop value exists before faster router work",
    "goal": "establish replayable evidence that 2-hop exact-out routing can beat direct exact-out routing",
    "obligations": [
        "witness survives Python kernel replay",
        "witness survives independent Z3 arithmetic replay",
        "direct and 2-hop costs remain deterministic",
    ],
    "invariants": [
        "exact-out objective minimizes input amount",
        "same target output amount across direct and 2-hop comparisons",
        "two-hop witness must strictly lower input cost than direct",
    ],
    "baseline_families": [
        {
            "name": "direct_only_exact_out",
            "why": "simplest routing posture and the null market design",
            "failure_mode": "misses fragmented-liquidity topologies where intermediate assets reduce input cost",
        }
    ],
    "reformulation_axes": [
        "topology witness mining before heuristic optimization",
        "graph/path framing instead of direct-pool framing",
        "dual-checker certification instead of single-model confidence",
    ],
    "performance_descriptors": {
        "asymptotic_profile": "witness lane only; no new router runtime",
        "invariant_family": ["exact_out_min_input", "topology_value", "cross_checker_replay"],
        "failure_envelope": ["no_direct_pool", "amount_out beyond feasible reserves"],
        "certificate_shape": ["python_kernel_replay", "z3_replay"],
    },
    "stimulus_ids": [
        "graph.path_relaxation",
        "market.fragmented_liquidity",
        "certificate.cross_checker",
    ],
    "hypotheses": [
        {
            "hypothesis_id": "exact_out_multihop_value",
            "mechanism_change": "Promote exact-out multihop routing as a real value surface because a replayable 2-hop witness beats direct exact-out cost.",
            "representation_shift_used": "reduce",
            "expected_metric_delta": [1, 1, 2, 0, 1],
            "null_hypothesis": "No replayable 2-hop exact-out witness strictly improves on direct routing under independent checkers.",
            "falsification_recipe": "route_exact_out_2hop_value",
            "support_recipe": "route_exact_out_2hop_value",
            "formal_obligations": [
                "2-hop witness survives Python kernel replay",
                "2-hop witness survives Z3 replay",
                "twohop_in < direct_in",
            ],
            "risk_modes": ["witness is too narrow", "router heuristics still underexplored"],
            "status": "proposed",
        }
    ],
}


def lane_packet() -> dict[str, Any]:
    return {
        **LANE_SPEC,
        "stimuli": [stim for stim in STIMULI_BANK if stim["stimulus_id"] in set(LANE_SPEC["stimulus_ids"])],
        "curated_corpus": [case.to_json() for case in EXACT_OUT_CURATED_CASES],
    }
