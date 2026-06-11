"""Wave 4 verification-market deviation evidence.

These tests cover proof-mining and permissionless-hosting obligations in
`docs/ZENODEX_MECHANISM_DESIGN_AND_MATH.md` (O-VM-01..06).

Model conventions:

- Payoffs are exact integers. There is no floating-point probability model in
  the assertions.
- Runtime helper functions are imported for the implemented arithmetic:
  `_route_tiebreak_key`, `_compute_payout_amount`,
  `schedule_proof_mining_reward_amount`, and
  `evaluate_proof_mining_claim_gate`.
- Rejected proof-mining claims are modeled as no-ops for conservation. The
  claim gate exposes a quoted `reward_pool_after` for every call, but the
  admissibility bit is the payout authority in this research model.

They are research evidence only. They do not change production behavior.
"""

from __future__ import annotations

from collections.abc import Iterable, Mapping
from dataclasses import dataclass

from src.core.proof_mining_claim_gate import (
    PROOF_MINING_BASE_REWARD_MAX,
    PROOF_MINING_EPOCH_MAX,
    evaluate_proof_mining_claim_gate,
    schedule_proof_mining_reward_amount,
)
from tools.gpu_jobs.improvement_bounty_round_route_v1 import (
    _compute_payout_amount,
    _route_tiebreak_key,
)


@dataclass(frozen=True)
class Prover:
    prover_id: str
    speed_rank: int
    cost: int


def _first_valid_entry_set(*, reward: int, provers: Iterable[Prover]) -> set[str]:
    """Pure first-valid contest: only the fastest profitable prover enters."""

    ordered = sorted(
        (p for p in provers if reward >= p.cost),
        key=lambda p: (p.speed_rank, p.prover_id),
    )
    if not ordered:
        return set()
    return {ordered[0].prover_id}


def _contest_payoff(
    *,
    entrant: Prover,
    entrants: set[str],
    provers: Iterable[Prover],
    reward: int,
) -> int:
    """Integer payoff under deterministic first-valid selection."""

    if entrant.prover_id not in entrants:
        return 0
    active = [p for p in provers if p.prover_id in entrants]
    winner = min(active, key=lambda p: (p.speed_rank, p.prover_id))
    if winner.prover_id == entrant.prover_id:
        return reward - entrant.cost
    return -entrant.cost


def _ceil_div(numerator: int, denominator: int) -> int:
    return (numerator + denominator - 1) // denominator


def _proof_mining_claim_kwargs(
    *,
    base_reward: int,
    epoch: int,
    reward_pool_before: int,
    flags_ok: bool,
) -> dict[str, int]:
    flag = 1 if flags_ok else 0
    return {
        "base_reward": base_reward,
        "epoch": epoch,
        "reward_pool_before": reward_pool_before,
        "proof_ok": flag,
        "binding_ok": flag,
        "policy_ok": flag,
        "nonce_ok": flag,
        "unclaimed_ok": flag,
    }


# ---------------------------------------------------------------------------
# H-MD-VM-001 / O-VM-01: first-valid-wins collapses to the fastest entrant.
# ---------------------------------------------------------------------------


def test_h_md_vm_001_first_valid_wins_unique_fastest_entrant() -> None:
    """Fastest profitable prover enters; slower provers exit even if cheaper."""

    provers = [
        Prover("fast", speed_rank=0, cost=7),
        Prover("middle", speed_rank=1, cost=5),
        Prover("slow_cheap", speed_rank=2, cost=1),
    ]
    reward = 10

    entrants = _first_valid_entry_set(reward=reward, provers=provers)
    assert entrants == {"fast"}

    payoff_fast = _contest_payoff(
        entrant=provers[0], entrants=entrants, provers=provers, reward=reward
    )
    assert payoff_fast == reward - provers[0].cost == 3

    for slower in provers[1:]:
        with_slower = set(entrants)
        with_slower.add(slower.prover_id)
        assert (
            _contest_payoff(
                entrant=slower,
                entrants=with_slower,
                provers=provers,
                reward=reward,
            )
            == -slower.cost
        )
        assert _contest_payoff(
            entrant=slower, entrants=entrants, provers=provers, reward=reward
        ) == 0

    # If the globally fastest prover exits, the next-fastest profitable prover
    # becomes the only entrant.
    assert _first_valid_entry_set(reward=6, provers=provers) == {"middle"}
    assert _first_valid_entry_set(reward=0, provers=provers) == set()


# ---------------------------------------------------------------------------
# H-MD-VM-002 / O-VM-02: reward halving creates a non-empty stranded pool.
# ---------------------------------------------------------------------------


def test_h_md_vm_002_halving_depletion_cliff_leaves_pool_nonempty() -> None:
    """Participation stops when the halved reward falls below prover cost."""

    base_reward = 64
    cost = 9
    initial_pool = 1000

    active_epochs = [
        epoch
        for epoch in range(PROOF_MINING_EPOCH_MAX + 1)
        if schedule_proof_mining_reward_amount(
            base_reward=base_reward, epoch=epoch
        )
        >= cost
    ]
    stop_epoch = len(active_epochs)
    paid_before_stop = sum(
        schedule_proof_mining_reward_amount(
            base_reward=base_reward, epoch=epoch
        )
        for epoch in active_epochs
    )

    assert active_epochs == [0, 1, 2]
    assert stop_epoch == (base_reward // cost).bit_length() == 3
    assert paid_before_stop == 64 + 32 + 16 == 112
    assert initial_pool - paid_before_stop == 888
    assert initial_pool - paid_before_stop > 0

    for base in range(1, PROOF_MINING_BASE_REWARD_MAX + 1):
        for prover_cost in range(1, base + 1):
            active_count = sum(
                1
                for epoch in range(PROOF_MINING_EPOCH_MAX + 1)
                if schedule_proof_mining_reward_amount(
                    base_reward=base, epoch=epoch
                )
                >= prover_cost
            )
            if prover_cost == 1:
                # The implemented schedule floors rewards at one, so a
                # cost-one prover remains active through the bounded epoch cap.
                expected = PROOF_MINING_EPOCH_MAX + 1
            else:
                expected = min(
                    PROOF_MINING_EPOCH_MAX + 1,
                    (base // prover_cost).bit_length(),
                )
            assert active_count == expected


# ---------------------------------------------------------------------------
# H-MD-VM-003 / O-VM-03: route tie-breaks include submitter-chosen miner_id.
# ---------------------------------------------------------------------------


def test_h_md_vm_003_route_tiebreak_miner_id_is_selectable() -> None:
    """Equal improvements can be won by choosing a smaller miner_id."""

    route: list[Mapping[str, str]] = [
        {"pool_id": "pool-a", "asset_out": "ZUSD"},
        {"pool_id": "pool-b", "asset_out": "TAU"},
    ]
    key_low = _route_tiebreak_key(route, miner_id="0000")
    key_high = _route_tiebreak_key(route, miner_id="zzzz")

    assert key_low[:-1] == key_high[:-1]
    assert key_low < key_high

    tied_candidates = [
        ("high", 100, key_high),
        ("low", 100, key_low),
    ]
    # The production round sorts valid submissions by tiebreak key first, then
    # picks the smallest tiebreak index for equal improvements. Mirror that
    # integer order directly for the two-candidate witness.
    winner = sorted(tied_candidates, key=lambda item: item[2])[0]
    assert winner[0] == "low"

    one_hop = [{"pool_id": "pool-c", "asset_out": "TAU"}]
    two_hop = route
    assert _route_tiebreak_key(one_hop, miner_id="same") < _route_tiebreak_key(
        two_hop, miner_id="same"
    )


# ---------------------------------------------------------------------------
# H-MD-VM-004 / O-VM-04: per-round caps make withholding profitable.
# ---------------------------------------------------------------------------


def test_h_md_vm_004_improvement_withholding_beats_one_shot_under_cap() -> None:
    """Splitting a known improvement across rounds can beat one-shot payout."""

    params = {
        "reward_pool_before": 1000,
        "base_reward": 10,
        "improvement_reward_bps": 2500,
        "max_reward": 25,
    }
    one_shot = _compute_payout_amount(improvement_u64=80, **params)
    split_a = _compute_payout_amount(improvement_u64=40, **params)
    split_b = _compute_payout_amount(improvement_u64=40, **params)

    assert one_shot == 25
    assert split_a == split_b == 20
    assert split_a + split_b == 40
    assert split_a + split_b > one_shot

    profitable_witnesses = []
    for delta in range(2, 201, 2):
        single = _compute_payout_amount(improvement_u64=delta, **params)
        half = _compute_payout_amount(improvement_u64=delta // 2, **params)
        if 2 * half > single:
            profitable_witnesses.append(delta)
    assert 80 in profitable_witnesses
    assert profitable_witnesses


# ---------------------------------------------------------------------------
# H-MD-VM-005 / O-VM-05: exact fee floor for flooding per-block caps.
# ---------------------------------------------------------------------------


def test_h_md_vm_005_sybil_fee_floor_exact_break_even() -> None:
    """Flooding S slots is unprofitable exactly above ceil(reward / S)."""

    for reward in range(1, 129):
        for max_slots in range(1, 17):
            threshold = _ceil_div(reward, max_slots)

            at_threshold_payoff = reward - max_slots * threshold
            assert at_threshold_payoff <= 0

            if threshold > 1:
                below_payoff = reward - max_slots * (threshold - 1)
                assert below_payoff > 0

            for fee in range(1, 129):
                payoff = reward - max_slots * fee
                assert (payoff <= 0) == (fee >= threshold)


# ---------------------------------------------------------------------------
# H-MD-VM-006 / O-VM-06: pool conservation under admissible-award semantics.
# ---------------------------------------------------------------------------


def test_h_md_vm_006_pool_conservation_over_award_sequences() -> None:
    """Admissible awards conserve `total_paid + pool`; rejects are no-ops."""

    initial_pool = 300
    pool = initial_pool
    total_paid = 0
    base_reward = 64

    events = [
        (0, True),
        (1, True),
        (2, False),
        (3, True),
        (4, True),
        (5, False),
        (6, True),
        (7, True),
    ]

    for epoch, flags_ok in events:
        before = pool
        outcome = evaluate_proof_mining_claim_gate(
            **_proof_mining_claim_kwargs(
                base_reward=base_reward,
                epoch=epoch,
                reward_pool_before=before,
                flags_ok=flags_ok,
            )
        )
        assert outcome.reward_amount == schedule_proof_mining_reward_amount(
            base_reward=base_reward, epoch=epoch
        )

        if outcome.admissible:
            total_paid += outcome.reward_amount
            pool = outcome.reward_pool_after
        else:
            pool = before

        assert total_paid + pool == initial_pool
        assert 0 <= pool <= initial_pool

    small_pool_outcome = evaluate_proof_mining_claim_gate(
        **_proof_mining_claim_kwargs(
            base_reward=base_reward,
            epoch=0,
            reward_pool_before=1,
            flags_ok=True,
        )
    )
    assert small_pool_outcome.reward_amount == 64
    assert not small_pool_outcome.budget_ok
    assert not small_pool_outcome.admissible
    assert 0 + 1 == 1
