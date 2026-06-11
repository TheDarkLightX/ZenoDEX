"""Wave 3 price-mediated cross-account cascade evidence (O-PT-04 / H-MD-PT-004).

Research evidence only. This module does not change production behavior and
does not claim a production multi-account perps runtime exists on this branch.

Model boundary (read before citing):

- **Real, production-bound:** every per-account state transition runs through
  the real `src/core/perp_v2/engine.py` `step` dispatcher: keeper liquidation
  (`PARTIAL_LIQUIDATE` with the real eligibility gate, penalty arithmetic, and
  margin-restoration invariant), price publication, settlement (the real
  `settle_price` clamp to `index +/- ceil(index * max_oracle_move_bps / 10^4)`,
  real PnL realization, real settle-time forced close), the circuit breaker,
  and epoch advance. Threshold predictions use the real pure helpers
  (`maint_margin_req`, `pnl_quote`, `settle_price`, `is_liquidatable`).
- **Modeled cross-account assumption:** the cross-account coupling. The inspected core is
  a single-account kernel; this module instantiates one real kernel state per
  account, shares one mark price across them, and supplies the price-impact
  channel as an explicit parameter: closing `q` base units moves the next
  clearing price down by `floor(q * P / depth_base)` (one-sided linear book of
  depth `depth_base` base units). Inventory closed by settle-time forced
  closes is unwound on the book in the following epoch (carryover). Production
  has no such book; conclusions about impact are conclusions about the model.

Cascade definitions used throughout:

- A **seed** is an account already liquidatable at the initial shared state.
- A **victim** is an account force-closed during the run that was not a seed.
- Cascade depth `K` = number of victims. `K = 0` means the seed liquidation
  did not propagate.

Settled findings (exact integers, replayable):

1. The per-epoch realized settlement decline is clamped by the real
   `settle_price` rule to exactly `ceil(index * max_oracle_move_bps / 10^4)`
   regardless of how violent the modeled crash is, and the real circuit
   breaker activates (position increases become guard-illegal).
2. `K = 0` has an exact one-unit collateral threshold: a non-seed account
   survives iff its post-PnL collateral at the seed-impacted settle price is
   at least its maintenance requirement at that price (strict `<` in the real
   `is_liquidatable`).
3. The keeper's `fraction_bps` choice is a cascade trigger lever: from one
   initial state, the auto-minimum policy yields `K = 0` while the maximal
   `fraction_bps = 10^4` policy yields `K = 1` and strictly larger total
   penalty extraction. This composes O-PT-05 with the cascade channel.
4. Strict progress bounds depth: every cascading epoch force-closes at least
   one new account, so `K <= n - (number of seeds)`; a 4-account chain witness
   meets the bound with equality (`K = 3`).
5. `K` is weakly decreasing in book depth over the swept grid (deeper book,
   shallower cascade), with the clamp + breaker engaging at shallow depths.
6. The real `guard_settle_epoch` fails closed (rejects) when post-PnL
   collateral would go negative: the kernel has no bad-debt socialization
   path, and insurance in this core only *receives* penalties
   (`fee_income`); nothing in the inspected core spends insurance to absorb
   cascade losses automatically, so insurance does not appear in the
   measured bound.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from src.core.perp_v2.engine import step
from src.core.perp_v2.guards import guard_set_position, guard_settle_epoch
from src.core.perp_v2.math import (
    BPS_SCALE,
    is_liquidatable,
    maint_margin_req,
    pnl_quote,
    settle_price,
)
from src.core.perp_v2.types import Action, ActionParams, EpochPhase, PerpState

PRICE_E8 = 100_000_000
POSITION = 100_000
MAX_MOVE_BPS = 500  # PerpState default, asserted in tests


def _account(
    position_base: int,
    collateral_quote: int,
    *,
    now_epoch: int = 1,
    index_e8: int = PRICE_E8,
) -> PerpState:
    return PerpState(
        now_epoch=now_epoch,
        epoch_phase=EpochPhase.OPEN,
        oracle_seen=True,
        oracle_last_update_epoch=now_epoch - 1,
        index_price_e8=index_e8,
        position_base=position_base,
        entry_price_e8=0 if position_base == 0 else index_e8,
        collateral_quote=collateral_quote,
        min_notional_for_bounty=0,
        max_position_abs=1_000_000,
    )


def _model_clearing(index_e8: int, closed_base: int, depth_base: int) -> int:
    """Linear one-sided book impact; the explicitly non-production model piece."""
    return max(1, index_e8 - (closed_base * index_e8) // depth_base)


@dataclass
class CascadeRun:
    states: list[PerpState]
    seeds: set[int]
    victims: set[int]
    liquidation_epochs: list[int] = field(default_factory=list)
    epochs_run: int = 0
    total_penalty_quote: int = 0
    total_closed_base: int = 0
    final_index_e8: int = 0
    breaker_ever: bool = False

    @property
    def depth_k(self) -> int:
        return len(self.victims)


def run_cascade(
    initial: list[PerpState],
    *,
    depth_base: int,
    keeper_fraction_bps: int,
    max_epochs: int = 16,
) -> CascadeRun:
    """Drive the bounded cascade model with real per-account engine steps."""
    states = list(initial)
    index = states[0].index_price_e8
    assert all(s.index_price_e8 == index for s in states)
    seeds = {
        i
        for i, s in enumerate(states)
        if is_liquidatable(
            s.position_base,
            s.collateral_quote,
            index,
            s.maintenance_margin_bps,
            s.depeg_buffer_bps,
        )
    }
    run = CascadeRun(states=states, seeds=seeds, victims=set())
    liquidated: set[int] = set(seeds)
    carryover_settle_closed = 0

    for _ in range(max_epochs):
        run.epochs_run += 1
        epoch = states[0].now_epoch
        events = 0
        q = carryover_settle_closed
        carryover_settle_closed = 0

        # Keeper pass: real PARTIAL_LIQUIDATE on every eligible account.
        for i, s in enumerate(states):
            result = step(
                s,
                ActionParams(
                    action=Action.PARTIAL_LIQUIDATE,
                    fraction_bps=keeper_fraction_bps,
                    auth_ok=True,
                ),
            )
            if not result.accepted:
                continue
            assert result.state is not None
            closed = abs(s.position_base) - abs(result.state.position_base)
            run.total_penalty_quote += (
                s.collateral_quote - result.state.collateral_quote
            )
            run.total_closed_base += closed
            q += closed
            states[i] = result.state
            if i not in liquidated:
                liquidated.add(i)
                if i not in seeds:
                    run.victims.add(i)
            events += 1

        clearing = _model_clearing(index, q, depth_base)

        # Settlement pass: real publish + settle (clamp, PnL, forced close).
        for i, s in enumerate(states):
            pub = step(
                s,
                ActionParams(
                    action=Action.PUBLISH_CLEARING_PRICE, price_e8=clearing
                ),
            )
            assert pub.accepted, pub.rejection
            assert pub.state is not None
            settled = step(pub.state, ActionParams(action=Action.SETTLE_EPOCH))
            assert settled.accepted, settled.rejection
            ns = settled.state
            assert ns is not None
            if ns.liquidated_this_step:
                closed = abs(s.position_base)
                carryover_settle_closed += closed
                run.total_closed_base += closed
                pnl = pnl_quote(s.position_base, ns.index_price_e8, index)
                run.total_penalty_quote += (
                    s.collateral_quote + pnl - ns.collateral_quote
                )
                if i not in liquidated:
                    liquidated.add(i)
                    if i not in seeds:
                        run.victims.add(i)
                events += 1
            states[i] = ns

        new_index = states[0].index_price_e8
        assert all(t.index_price_e8 == new_index for t in states)
        run.breaker_ever = run.breaker_ever or any(
            t.breaker_active for t in states
        )
        index = new_index
        if events:
            run.liquidation_epochs.append(epoch)

        advanced = [
            step(t, ActionParams(action=Action.ADVANCE_EPOCH, delta=1))
            for t in states
        ]
        assert all(a.accepted for a in advanced)
        states = [a.state for a in advanced if a.state is not None]
        assert len(states) == len(initial)
        run.states = states

        if events == 0:
            break

    # Strict progress: liquidated accounts never exceed the population.
    assert len(liquidated) <= len(states)
    run.final_index_e8 = index
    return run


# ---------------------------------------------------------------------------
# Finding 1: the real settle clamp bounds per-epoch realized decline exactly.
# ---------------------------------------------------------------------------


def test_settle_clamp_bounds_per_epoch_decline_and_breaker_goes_reduce_only() -> None:
    """A modeled crash to clearing price 1 realizes exactly the clamped move."""

    account = _account(POSITION, 50_000)
    assert account.max_oracle_move_bps == MAX_MOVE_BPS

    def crash_epoch(state: PerpState, expected_sp: int) -> PerpState:
        pub = step(
            state,
            ActionParams(action=Action.PUBLISH_CLEARING_PRICE, price_e8=1),
        )
        assert pub.accepted and pub.state is not None
        settled = step(pub.state, ActionParams(action=Action.SETTLE_EPOCH))
        assert settled.accepted and settled.state is not None
        assert settled.state.index_price_e8 == expected_sp
        assert not settled.state.liquidated_this_step
        adv = step(
            settled.state, ActionParams(action=Action.ADVANCE_EPOCH, delta=1)
        )
        assert adv.accepted and adv.state is not None
        return adv.state

    clamp_1 = -(-PRICE_E8 * MAX_MOVE_BPS // BPS_SCALE)  # ceil division
    assert clamp_1 == 5_000_000
    state = crash_epoch(account, PRICE_E8 - clamp_1)
    assert state.index_price_e8 == 95_000_000
    assert state.breaker_active

    clamp_2 = -(-95_000_000 * MAX_MOVE_BPS // BPS_SCALE)
    assert clamp_2 == 4_750_000
    state = crash_epoch(state, 95_000_000 - clamp_2)
    assert state.index_price_e8 == 90_250_000
    assert state.collateral_quote == 50_000 - 5_000 - 4_750

    # Breaker active: increasing the position is guard-illegal, reducing is not.
    increase = ActionParams(
        action=Action.SET_POSITION, new_position_base=2 * POSITION, auth_ok=True
    )
    reduce = ActionParams(
        action=Action.SET_POSITION, new_position_base=POSITION // 2, auth_ok=True
    )
    assert not guard_set_position(state, increase)
    assert guard_set_position(state, reduce)


# ---------------------------------------------------------------------------
# Finding 2: K = 0 has an exact one-unit collateral threshold.
# ---------------------------------------------------------------------------


def test_k0_one_unit_threshold_at_seed_impacted_settle_price() -> None:
    """B survives at the helper-predicted threshold and falls one unit below."""

    depth_base = 4_000_000
    clearing = _model_clearing(PRICE_E8, POSITION, depth_base)
    assert clearing == 97_500_000
    sp1 = settle_price(clearing, PRICE_E8, MAX_MOVE_BPS, True)
    assert sp1 == 97_500_000  # 250 bps move, inside the clamp
    loss = -pnl_quote(POSITION, sp1, PRICE_E8)
    maint = maint_margin_req(POSITION, sp1, 500, 100)
    assert loss == 2_500
    assert maint == 5_850
    threshold = maint + loss
    assert threshold == 8_350

    for coll_b, expected_k in ((threshold, 0), (threshold - 1, 1)):
        seed = _account(POSITION, 5_900)
        victim = _account(POSITION, coll_b)
        run = run_cascade(
            [seed, victim],
            depth_base=depth_base,
            keeper_fraction_bps=BPS_SCALE,
        )
        assert run.seeds == {0}
        assert run.depth_k == expected_k
        assert run.epochs_run < 16
        if expected_k == 1:
            assert run.victims == {1}
            assert run.states[1].position_base == 0
        else:
            assert run.states[1].position_base == POSITION
            assert run.final_index_e8 == sp1  # fixed point after the seed epoch


# ---------------------------------------------------------------------------
# Finding 3: keeper fraction_bps choice flips K from 0 to 1 (O-PT-05 composed).
# ---------------------------------------------------------------------------


def test_fraction_bps_choice_is_a_cascade_trigger_lever() -> None:
    """Auto-minimum keeps the victim solvent; max fraction force-closes it."""

    def fresh_accounts() -> list[PerpState]:
        return [_account(POSITION, 5_999), _account(POSITION, 8_349)]

    auto = run_cascade(
        fresh_accounts(), depth_base=4_000_000, keeper_fraction_bps=0
    )
    assert auto.seeds == {0}
    assert auto.depth_k == 0
    # Auto-minimum closes 1 bp of the seed: 10 base units, zero penalty.
    assert auto.total_closed_base == 10
    assert auto.total_penalty_quote == 0
    assert auto.states[1].position_base == POSITION

    full = run_cascade(
        fresh_accounts(), depth_base=4_000_000, keeper_fraction_bps=BPS_SCALE
    )
    assert full.seeds == {0}
    assert full.depth_k == 1
    assert full.victims == {1}
    assert full.states[1].position_base == 0
    # Seed full-close penalty 500 plus the victim's settle penalty 487.
    assert full.total_penalty_quote == 987
    assert full.total_closed_base == 2 * POSITION

    assert full.total_penalty_quote > auto.total_penalty_quote
    assert full.total_closed_base > auto.total_closed_base


# ---------------------------------------------------------------------------
# Finding 4: strict progress, tight 4-account chain (K = n - 1).
# ---------------------------------------------------------------------------


def _chain_accounts() -> list[PerpState]:
    return [
        _account(POSITION, 5_900),   # seed
        _account(POSITION, 8_000),   # falls at the seed epoch's settlement
        _account(POSITION, 10_000),  # falls one epoch later
        _account(POSITION, 12_000),  # falls one epoch after that
    ]


def test_chain_witness_meets_strict_progress_bound_with_equality() -> None:
    run = run_cascade(
        _chain_accounts(), depth_base=4_000_000, keeper_fraction_bps=BPS_SCALE
    )
    assert run.seeds == {0}
    assert run.victims == {1, 2, 3}
    assert run.depth_k == 3  # == n - seeds, the strict-progress bound, tight
    assert run.liquidation_epochs == [1, 2, 3]
    assert run.epochs_run == 4
    # Exact price path: 250 bps modeled impact per cascading epoch, unclamped.
    assert run.final_index_e8 == 90_368_790
    assert not run.breaker_ever
    assert all(s.position_base == 0 for s in run.states)


# ---------------------------------------------------------------------------
# Finding 5: K is weakly decreasing in book depth; clamp engages when shallow.
# ---------------------------------------------------------------------------


def test_cascade_depth_is_weakly_decreasing_in_book_depth() -> None:
    depths = [1_000_000, 2_000_000, 4_000_000, 8_000_000]
    runs = [
        run_cascade(
            _chain_accounts(), depth_base=d, keeper_fraction_bps=BPS_SCALE
        )
        for d in depths
    ]
    ks = [r.depth_k for r in runs]
    assert ks == [3, 3, 3, 0]
    assert all(a >= b for a, b in zip(ks, ks[1:]))
    # The production clamp/breaker engages exactly at the shallow depths.
    assert [r.breaker_ever for r in runs] == [True, True, False, False]
    # Shallow depths compress the chain into fewer epochs via the clamp.
    assert runs[0].liquidation_epochs == [1, 2]
    assert runs[2].liquidation_epochs == [1, 2, 3]


def test_k0_threshold_tracks_real_helpers_across_depths() -> None:
    """The K = 0 boundary equals maint(sp1) + loss(sp1) at every swept depth."""

    for depth_base in (1_000_000, 2_000_000, 4_000_000, 8_000_000):
        clearing = _model_clearing(PRICE_E8, POSITION, depth_base)
        sp1 = settle_price(clearing, PRICE_E8, MAX_MOVE_BPS, True)
        loss = -pnl_quote(POSITION, sp1, PRICE_E8)
        maint = maint_margin_req(POSITION, sp1, 500, 100)
        threshold = maint + loss
        assert threshold > maint_margin_req(POSITION, PRICE_E8, 500, 100)

        assert not is_liquidatable(POSITION, threshold - loss, sp1, 500, 100)
        assert is_liquidatable(POSITION, threshold - 1 - loss, sp1, 500, 100)

        for coll_b, expected_k in ((threshold, 0), (threshold - 1, 1)):
            run = run_cascade(
                [_account(POSITION, 5_900), _account(POSITION, coll_b)],
                depth_base=depth_base,
                keeper_fraction_bps=BPS_SCALE,
            )
            assert run.depth_k == expected_k, (depth_base, coll_b)


# ---------------------------------------------------------------------------
# Finding 6: settlement fails closed on negative post-PnL collateral.
# ---------------------------------------------------------------------------


def test_settle_guard_fails_closed_instead_of_socializing_bad_debt() -> None:
    """Direct real-guard boundary: post-PnL collateral < 0 rejects settlement."""

    def published_state(collateral: int) -> PerpState:
        return PerpState(
            now_epoch=1,
            epoch_phase=EpochPhase.PRICE_PUBLISHED,
            clearing_price_seen=True,
            clearing_price_epoch=1,
            clearing_price_e8=94_000_000,
            oracle_seen=True,
            oracle_last_update_epoch=0,
            index_price_e8=PRICE_E8,
            position_base=POSITION,
            entry_price_e8=PRICE_E8,
            collateral_quote=collateral,
            min_notional_for_bounty=0,
            max_position_abs=1_000_000,
        )

    # 600 bps requested move clamps to 500 bps: sp = 95_000_000, loss 5_000.
    sp = settle_price(94_000_000, PRICE_E8, MAX_MOVE_BPS, True)
    assert sp == 95_000_000
    assert -pnl_quote(POSITION, sp, PRICE_E8) == 5_000

    params = ActionParams(action=Action.SETTLE_EPOCH)
    assert guard_settle_epoch(published_state(5_000), params)
    assert not guard_settle_epoch(published_state(4_999), params)
