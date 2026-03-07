from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from src.core.liquidity import create_pool
from src.state.balances import BalanceTable
from src.state.intents import Intent, IntentKind
from src.state.pools import PoolState

PK = "0x" + "11" * 48
ASSET0 = "0x" + "01" * 32
ASSET1 = "0x" + "02" * 32


def _iid(n: int) -> str:
    return "0x" + f"{n:064x}"


@dataclass(frozen=True)
class BatchOrderingIntentCase:
    amount_in: int
    min_amount_out: int

    def to_json(self) -> dict[str, int]:
        return {
            "amount_in": int(self.amount_in),
            "min_amount_out": int(self.min_amount_out),
        }


@dataclass(frozen=True)
class BatchOrderingLaneCase:
    reserve0: int
    reserve1: int
    fee_bps: int
    intents: tuple[BatchOrderingIntentCase, ...]
    expected_ab: tuple[int, int]
    baseline_ab: tuple[int, int]

    def to_json(self) -> dict[str, Any]:
        return {
            "pool": {
                "reserve0": int(self.reserve0),
                "reserve1": int(self.reserve1),
                "fee_bps": int(self.fee_bps),
            },
            "intents": [it.to_json() for it in self.intents],
            "expected_ab": {"A": int(self.expected_ab[0]), "B": int(self.expected_ab[1])},
            "baseline_ab": {"A": int(self.baseline_ab[0]), "B": int(self.baseline_ab[1])},
        }


BATCH_MCI_CURATED_CASES: tuple[BatchOrderingLaneCase, ...] = (
    BatchOrderingLaneCase(
        reserve0=2_066_116,
        reserve1=2_565_724,
        fee_bps=121,
        intents=(
            BatchOrderingIntentCase(118_086, 10_046),
            BatchOrderingIntentCase(70_257, 20_012),
            BatchOrderingIntentCase(54_698, 45_308),
            BatchOrderingIntentCase(42_047, 41_305),
        ),
        expected_ab=(285_088, 190_962),
        baseline_ab=(285_088, 190_961),
    ),
    BatchOrderingLaneCase(
        reserve0=1_978_397,
        reserve1=2_077_705,
        fee_bps=41,
        intents=(
            BatchOrderingIntentCase(103_374, 103_765),
            BatchOrderingIntentCase(33_675, 16_951),
            BatchOrderingIntentCase(72_283, 11_257),
            BatchOrderingIntentCase(83_611, 76_839),
        ),
        expected_ab=(189_569, 75_928),
        baseline_ab=(189_569, 75_927),
    ),
    BatchOrderingLaneCase(
        reserve0=1_136_828,
        reserve1=1_191_769,
        fee_bps=66,
        intents=(
            BatchOrderingIntentCase(91_547, 6_129),
            BatchOrderingIntentCase(25_050, 3_514),
            BatchOrderingIntentCase(85_268, 9_114),
            BatchOrderingIntentCase(40_813, 19),
        ),
        expected_ab=(242_678, 189_655),
        baseline_ab=(242_678, 189_654),
    ),
    BatchOrderingLaneCase(
        reserve0=1_577_866,
        reserve1=2_041_354,
        fee_bps=63,
        intents=(
            BatchOrderingIntentCase(114_661, 75_340),
            BatchOrderingIntentCase(45_828, 56_113),
            BatchOrderingIntentCase(89_707, 74_402),
            BatchOrderingIntentCase(32_274, 26_941),
        ),
        expected_ab=(282_470, 75_403),
        baseline_ab=(282_470, 75_402),
    ),
    BatchOrderingLaneCase(
        reserve0=1_817_447,
        reserve1=737_460,
        fee_bps=21,
        intents=(
            BatchOrderingIntentCase(44_224, 3_566),
            BatchOrderingIntentCase(117_142, 24_776),
            BatchOrderingIntentCase(115_003, 35_054),
            BatchOrderingIntentCase(94_454, 28_501),
        ),
        expected_ab=(370_823, 32_838),
        baseline_ab=(370_823, 32_837),
    ),
    BatchOrderingLaneCase(
        reserve0=569_729,
        reserve1=2_927_207,
        fee_bps=38,
        intents=(
            BatchOrderingIntentCase(69_881, 225_148),
            BatchOrderingIntentCase(21_697, 72_999),
            BatchOrderingIntentCase(59_969, 228_610),
            BatchOrderingIntentCase(99_132, 413_878),
        ),
        expected_ab=(169_013, 28_587),
        baseline_ab=(151_547, 86_290),
    ),
    BatchOrderingLaneCase(
        reserve0=2_778_074,
        reserve1=2_754_870,
        fee_bps=65,
        intents=(
            BatchOrderingIntentCase(120_363, 15_000),
            BatchOrderingIntentCase(30_843, 25_105),
            BatchOrderingIntentCase(83_802, 44_887),
            BatchOrderingIntentCase(102_227, 55_278),
        ),
        expected_ab=(337_235, 156_144),
        baseline_ab=(337_235, 156_143),
    ),
)


STIMULI_BANK: tuple[dict[str, Any], ...] = (
    {
        "stimulus_id": "sched.insertion_frontier",
        "family": "scheduling",
        "prompt": "If local greedy priority gets trapped, can insertion over the whole partial schedule recover higher-quality AB frontiers before final refinement?",
        "design_shift": "Promote whole-order insertion scoring over single-step marginal picks.",
    },
    {
        "stimulus_id": "ds.partial_order_cache",
        "family": "data_structure",
        "prompt": "Treat each partial ordering as a state with a measurable frontier. Which insertion rule preserves deterministic tie-breaks while reducing search collapse?",
        "design_shift": "Use partial-order scoring instead of purely local swap choice.",
    },
    {
        "stimulus_id": "market.failure_envelope",
        "family": "adversarial_game",
        "prompt": "Assume tight-slippage intents can bait a slippage-first greedy pass into a locally stable but globally inferior B profile. What deterministic seed breaks that trap?",
        "design_shift": "Seed the global pass with a different representation of contribution.",
    },
)


LANE_SPEC: dict[str, Any] = {
    "lane_id": "batch_ordering_mci_ab",
    "title": "MCI Batch Ordering",
    "representation": "incremental insertion ordering for same-direction exact-in batch clearing",
    "abstraction_level": "bounded heuristic seed plus existing global AB refinement",
    "goal": "improve heuristic batch ordering quality versus greedy_ab_global without changing default settlement semantics",
    "obligations": [
        "recover bounded-optimal (A,B) on the curated witness family",
        "strictly improve over greedy_ab_global on the curated witness family",
        "remain deterministic under identical inputs",
    ],
    "invariants": [
        "primary objective A: maximize executed input volume",
        "secondary objective B: maximize total surplus when A ties",
        "same-direction exact-in only; mixed direction falls back fail-closed",
    ],
    "baseline_families": [
        {
            "name": "greedy_ab_global",
            "why": "current strongest heuristic production family for unbounded-n batches",
            "failure_mode": "greedy slippage seed can trap the later global pass on B-suboptimal plateaus",
        },
        {
            "name": "optimal_ab_bounded",
            "why": "bounded oracle for exact evaluation and witness mining",
            "failure_mode": "factorial cost prevents use outside bounded regimes",
        },
    ],
    "reformulation_axes": [
        "incremental insertion instead of local greedy picks",
        "full-order scoring at each insertion step",
        "reuse existing deterministic global refinement after a stronger seed",
    ],
    "performance_descriptors": {
        "asymptotic_profile": "O(n^4) bounded heuristic seed + O(n^3) global refinement",
        "invariant_family": ["ab_objective", "deterministic_tiebreak", "bounded_fallback"],
        "failure_envelope": ["mixed_direction_batches", "very_large_batches_above_cap"],
        "certificate_shape": ["bounded_bruteforce_match", "baseline_gap_witnesses"],
    },
    "stimulus_ids": [
        "sched.insertion_frontier",
        "ds.partial_order_cache",
        "market.failure_envelope",
    ],
    "hypotheses": [
        {
            "hypothesis_id": "batch_mci_ab_global",
            "mechanism_change": "Seed AB global refinement with marginal-contribution insertion instead of slippage-first greedy ordering.",
            "representation_shift_used": "heuristic",
            "expected_metric_delta": [1, 0, 3, -1, 2],
            "null_hypothesis": "The MCI seed does not recover bounded-optimal AB on the curated corpus or fails to beat greedy_ab_global there.",
            "falsification_recipe": "batch_mci_vs_bruteforce",
            "support_recipe": "batch_mci_vs_greedy",
            "formal_obligations": [
                "same-direction exact-in guard is preserved",
                "bounded curated corpus matches optimal AB",
                "deterministic ordering result for fixed inputs",
            ],
            "risk_modes": ["n above MCI cap", "cases where greedy seed remains better than insertion seed"],
            "status": "proposed",
        }
    ],
}


def build_case_pool_and_intents(case: BatchOrderingLaneCase) -> tuple[PoolState, list[Intent]]:
    _pool_id, pool, _lp = create_pool(
        asset0=ASSET0,
        asset1=ASSET1,
        amount0=int(case.reserve0),
        amount1=int(case.reserve1),
        fee_bps=int(case.fee_bps),
        creator_pubkey=PK,
        created_at=0,
    )
    intents: list[Intent] = []
    for idx, row in enumerate(case.intents):
        sender = "0x" + f"{idx + 1:02x}" * 48
        intents.append(
            Intent(
                module="TauSwap",
                version="0.1",
                kind=IntentKind.SWAP_EXACT_IN,
                intent_id=_iid(idx),
                sender_pubkey=sender,
                deadline=9_999_999_999,
                fields={
                    "pool_id": pool.pool_id,
                    "asset_in": ASSET0,
                    "asset_out": ASSET1,
                    "amount_in": int(row.amount_in),
                    "min_amount_out": int(row.min_amount_out),
                },
            )
        )
    return pool, intents


def build_case_balances(case: BatchOrderingLaneCase) -> BalanceTable:
    balances = BalanceTable()
    for idx, row in enumerate(case.intents):
        sender = "0x" + f"{idx + 1:02x}" * 48
        balances.set(sender, ASSET0, int(row.amount_in) + 1_000_000)
        balances.set(sender, ASSET1, 1_000_000)
    return balances


def lane_packet() -> dict[str, Any]:
    return {
        **LANE_SPEC,
        "stimuli": [stim for stim in STIMULI_BANK if stim["stimulus_id"] in set(LANE_SPEC["stimulus_ids"])],
        "curated_corpus": [case.to_json() for case in BATCH_MCI_CURATED_CASES],
    }
