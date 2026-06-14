# [TESTER] v1
"""
Wave-3 settlement-boundary airtightness (charter docs/ZENODEX_MECHANISM_DESIGN_AND_MATH.md
section 10, O-PT-02 / H-MD-PT-002). A bounded verification through the REAL perp_v2
engine (src/core/perp_v2/engine.py step), guards, and reducers.

O-PT-02 set out to VERIFY (not assume) that "no reachable PRICE_PUBLISHED action
sequence changes position_base conditioned on the published clearing price"
(threat: free-look / settlement avoidance on the clearing price). Verifying it
yields a SPLIT result:

  SUPPORTED (in-phase airtightness): no action that KEEPS the phase
  PRICE_PUBLISHED changes position_base. The only updates that write position_base
  are apply_set_position, apply_partial_liquidate (both dispatched behind guards
  that require OPEN phase) and apply_settle_epoch (which transitions to SETTLED,
  i.e. exits the phase). So no phase-preserving action repositions, and the
  phase-exit settle_epoch carries no trader-chosen position parameter.

  FALSIFIED (unconditional claim): the boundary is NOT airtight against a
  phase-EXIT. guard_advance_epoch (guards.py:34) checks ONLY the epoch bound — no
  phase, no auth, no prior-settlement requirement — and apply_advance_epoch resets
  the phase to OPEN at the next epoch WITHOUT settling. So the reachable sequence
  publish -> advance_epoch -> set_position changes position_base, and more
  pointedly lets a trader SKIP an unfavorable settlement (a concrete avoided loss).

Net verdict: PARTIALLY_FALSIFIED — airtightness holds within the phase but is
CONDITIONAL on settle-before-advance lifecycle discipline that the pure-core guard
does not enforce (analogous to the O-PT-01 scheduler scope). SEVERITY BOUND
(verified): the bypass is NOT live-exploitable. The engine shell
(apply_perp_ops -> perp_runtime_risk_gate, src/core/perp_runtime_risk_gate.py:180)
explicitly REJECTS advance_epoch before settlement with
"cannot advance epoch before settling current epoch" — demonstrated end to end in
test_h_md_pt_002_engine_shell_blocks_the_advance_bypass. So the settle-before-
advance invariant lives in the SHELL/runtime-risk-gate, and the permissive
guard_advance_epoch is a pure-core DEFENSE-IN-DEPTH gap only (the core relies on
the shell to enforce it). Research evidence only; a candidate remedy (also gate
advance_epoch on SETTLED in the pure core, for defense in depth) is UNTESTED and
not claimed.
"""

from __future__ import annotations

from dataclasses import replace

from src.core.perp_v2.engine import step
from src.core.perp_v2.state import initial_state
from src.core.perp_v2.types import Action, ActionParams, EpochPhase

_INDEX = 100_000_000
_POS = 1_000


def _open_with_position(position: int = _POS, **kw):
    """A valid OPEN state with a position and a fresh oracle (last < now so a
    later PRICE_PUBLISHED state can also legally settle)."""
    base = replace(
        initial_state(),
        now_epoch=5,
        epoch_phase=EpochPhase.OPEN,
        oracle_seen=True,
        oracle_last_update_epoch=4,
        max_oracle_staleness_epochs=100,
        index_price_e8=_INDEX,
        collateral_quote=1_000_000,
        position_base=position,
        entry_price_e8=_INDEX,
        max_position_abs=10**9,
        funding_cap_bps=100,
    )
    return replace(base, **kw) if kw else base


def _reach_price_published(position: int = _POS, price_e8: int = _INDEX, **kw):
    """Reach PRICE_PUBLISHED by the REAL publish action (reachable by construction)."""
    opn = _open_with_position(position, **kw)
    pub = step(opn, ActionParams(
        action=Action.PUBLISH_CLEARING_PRICE, price_e8=price_e8, auth_ok=True))
    assert pub.accepted, pub.rejection
    assert pub.state.epoch_phase == EpochPhase.PRICE_PUBLISHED
    assert pub.state.position_base == position           # publish doesn't touch position
    return opn, pub.state


def _param_trials(act: Action):
    """A broad param sweep covering every position-relevant target plus the
    params other actions consume (incl. advance delta)."""
    trials = [ActionParams(action=act, auth_ok=True)]
    for npb in (0, 500, 999, 1000, 1001, 2000, -1000, -2000):
        trials.append(ActionParams(action=act, new_position_base=npb, auth_ok=True))
    for rate in (0, 100, -100, 101):
        trials.append(ActionParams(action=act, new_rate_bps=rate, auth_ok=True))
    for frac in (0, 1, 5000, 10000):
        trials.append(ActionParams(action=act, fraction_bps=frac, auth_ok=True))
    for amt in (0, 1, 12345):
        trials.append(ActionParams(action=act, amount=amt, auth_ok=True))
    for cl in (0, 1, 100):
        trials.append(ActionParams(action=act, claim_amount=cl, auth_ok=True))
    for px in (1, _INDEX, 105_000_000):
        trials.append(ActionParams(action=act, price_e8=px, auth_ok=True))
    for d in (0, 1, 2):
        trials.append(ActionParams(action=act, delta=d, auth_ok=True))
    return trials


def test_h_md_pt_002_set_position_rejected_in_phase_accepted_in_open() -> None:
    """Non-vacuity + phase-specificity: the position-CHOOSING action set_position
    is guard-REJECTED in PRICE_PUBLISHED for every target (open more, reduce,
    close, flip sign), while the SAME targets are guard-ACCEPTED and effective in
    OPEN. So the in-phase restriction is real, not a dead action."""
    opn, pp = _reach_price_published()
    for npb in (0, 500, 999, 1001, 2000, -1000, -2000):
        params = ActionParams(action=Action.SET_POSITION, new_position_base=npb, auth_ok=True)
        r_pp = step(pp, params)
        assert not r_pp.accepted, (npb, "unexpectedly accepted in PRICE_PUBLISHED")
        assert r_pp.rejection == "guard"
        r_open = step(opn, params)
        assert r_open.accepted, (npb, r_open.rejection)
        assert r_open.state.position_base == npb         # OPEN genuinely repositions


def test_h_md_pt_002_phase_preserving_actions_preserve_position() -> None:
    """In-phase airtightness (SUPPORTED part): over a broad action x param sweep
    from SEVERAL reachable in-phase states, EVERY accepted transition that keeps
    the phase PRICE_PUBLISHED leaves position_base unchanged. (Structural reason:
    the only position-writing updates are set_position/partial_liquidate — both
    OPEN-gated — and settle_epoch, which exits to SETTLED.) Multiple base states
    are swept so reachable successors like apply_insurance_claim (legal only after
    insurance is funded) are covered too."""
    _opn, pp = _reach_price_published()
    # Reachable in-phase successor states (still PRICE_PUBLISHED).
    funded = step(pp, ActionParams(action=Action.DEPOSIT_INSURANCE, amount=50_000, auth_ok=True))
    funded_after = step(pp, ActionParams(action=Action.APPLY_FUNDING, new_rate_bps=100, auth_ok=True))
    bases = [pp]
    for r in (funded, funded_after):
        if r.accepted and r.state.epoch_phase == EpochPhase.PRICE_PUBLISHED:
            bases.append(r.state)

    checked = 0
    for s in bases:
        for act in Action:
            for params in _param_trials(act):
                r = step(s, params)
                if r.accepted and r.state.epoch_phase == EpochPhase.PRICE_PUBLISHED:
                    assert r.state.position_base == s.position_base, (act.value, params)
                    checked += 1
    assert checked > 0                                    # the invariant was actually exercised


def test_h_md_pt_002_multistep_in_phase_sequence_preserves_position() -> None:
    """The inductive closure as a real engine trace: a multi-step sequence of legal
    in-phase actions stays in PRICE_PUBLISHED and preserves position end to end."""
    _opn, pp = _reach_price_published()
    s = pp
    for params in [
        ActionParams(action=Action.DEPOSIT_INSURANCE, amount=10_000, auth_ok=True),
        ActionParams(action=Action.APPLY_FUNDING, new_rate_bps=100, auth_ok=True),
        ActionParams(action=Action.APPLY_INSURANCE_CLAIM, claim_amount=1, auth_ok=True),
        ActionParams(action=Action.DEPOSIT_INSURANCE, amount=5_000, auth_ok=True),
    ]:
        r = step(s, params)
        if not r.accepted:
            continue                                      # only the legal ones advance the trace
        assert r.state.epoch_phase == EpochPhase.PRICE_PUBLISHED
        assert r.state.position_base == _POS
        s = r.state
    assert s.position_base == _POS


def test_h_md_pt_002_settle_exit_has_no_trader_position_choice() -> None:
    """The phase-EXIT settle_epoch is not a free-look: it carries no position
    parameter. Different new_position_base values yield the IDENTICAL settled
    state, and a non-liquidatable settlement preserves the position exactly (the
    only position mutation settle can make is the deterministic zero-on-liquidation
    from the published price). So settlement cannot realize a chosen position."""
    _opn, pp = _reach_price_published()
    r_a = step(pp, ActionParams(action=Action.SETTLE_EPOCH, new_position_base=7777, auth_ok=True))
    r_b = step(pp, ActionParams(action=Action.SETTLE_EPOCH, new_position_base=0, auth_ok=True))
    assert r_a.accepted and r_b.accepted, (r_a.rejection, r_b.rejection)
    assert r_a.state == r_b.state                         # settle ignores the position param
    assert r_a.state.epoch_phase == EpochPhase.SETTLED    # it exits PRICE_PUBLISHED
    assert r_a.state.position_base == _POS                # preserved (non-liquidatable here)


def test_h_md_pt_002_advance_epoch_reachable_settlement_bypass_falsifies_unconditional() -> None:
    """FALSIFYING counterexample (the reason the verdict is PARTIALLY_FALSIFIED):
    the boundary is NOT airtight against a phase-EXIT. guard_advance_epoch checks
    only the epoch bound (no phase, no auth, no prior-settlement), and
    apply_advance_epoch resets to OPEN at the next epoch WITHOUT settling. So a
    long facing an unfavorable published clearing price can ADVANCE past settlement
    (skipping the loss), reach OPEN, and reposition — a reachable settlement
    bypass, quantified here as an avoided loss."""
    # Underwater-on-settlement long: params satisfy max_oracle_move<=maint+depeg<=initial.
    opn, pp = _reach_price_published(
        position=1_000_000, price_e8=95_000_000,        # 5% adverse clearing print
        collateral_quote=10_000_000, initial_margin_bps=1000,
        maintenance_margin_bps=500, depeg_buffer_bps=0, max_oracle_move_bps=500,
        liquidation_penalty_bps=200, min_notional_for_bounty=0,
    )

    # Honest path: settle realizes the loss.
    settled = step(pp, ActionParams(action=Action.SETTLE_EPOCH, auth_ok=True))
    assert settled.accepted, settled.rejection
    assert settled.state.epoch_phase == EpochPhase.SETTLED
    assert settled.state.collateral_quote < pp.collateral_quote   # a real loss is realized

    # Escape path: advance from PRICE_PUBLISHED is guard-legal and SKIPS settlement.
    adv = step(pp, ActionParams(action=Action.ADVANCE_EPOCH, delta=1, auth_ok=True))
    assert adv.accepted, adv.rejection
    assert adv.state.epoch_phase == EpochPhase.OPEN               # exited without settling
    assert adv.state.now_epoch == pp.now_epoch + 1
    assert adv.state.collateral_quote == pp.collateral_quote      # loss NOT realized
    assert adv.state.position_base == pp.position_base

    # ... and now reposition (close) in the new OPEN epoch.
    closed = step(adv.state, ActionParams(action=Action.SET_POSITION, new_position_base=0, auth_ok=True))
    assert closed.accepted, closed.rejection
    assert closed.state.position_base == 0                        # repositioned post-publish

    avoided = closed.state.collateral_quote - settled.state.collateral_quote
    assert avoided > 0                                            # strictly cheaper to advance
    assert avoided == pp.collateral_quote - settled.state.collateral_quote
    assert avoided == 50_000                                      # exact avoided loss on this witness


def test_h_md_pt_002_engine_shell_blocks_the_advance_bypass() -> None:
    """SEVERITY BOUND: the core-guard bypass is NOT live-exploitable. The engine
    shell (apply_perp_ops -> perp_runtime_risk_gate) REJECTS advance_epoch before
    settlement with an explicit error, and allows it only after settle_epoch. So
    the settle-before-advance invariant is enforced at the shell/runtime-risk-gate
    layer; the permissive pure-core guard_advance_epoch is a defense-in-depth gap
    only. Driven end to end through the real shell entry apply_perp_ops."""
    from src.core.dex import DexState
    from src.integration.perp_engine import PerpEngineConfig, apply_perp_ops
    from src.state.balances import BalanceTable
    from src.state.lp import LPTable

    mid = "perp:opt02-shell"
    quote = "0x" + "44" * 32
    operator = "00" * 48

    def _op(action, **kw):
        o = {"module": "TauPerp", "version": "0.1", "market_id": mid, "action": action}
        o.update(kw)
        return o

    def _apply(state, ops):
        cfg = PerpEngineConfig(operator_pubkey=operator, allow_isolated_markets=True)
        return apply_perp_ops(
            config=cfg, state=state, operations={"5": ops},
            tx_sender_pubkey=operator, block_timestamp=0)

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    state = _apply(state, [_op("init_market", quote_asset=quote)]).state
    state = _apply(state, [_op("advance_epoch", delta=1)]).state          # epoch 0 -> 1
    gs = state.perps.markets[mid].global_state
    gs["oracle_seen"] = True
    gs["oracle_last_update_epoch"] = 0                                    # last < now (=1)
    gs["index_price_e8"] = 100_000_000
    state = _apply(state, [_op("publish_clearing_price", price_e8=100_000_000)]).state
    assert int(state.perps.markets[mid].global_state.get("epoch_phase", -1)) == 1   # PRICE_PUBLISHED

    # The core bypass attempted through the SHELL: advance before settle is REJECTED.
    r_bypass = _apply(state, [_op("advance_epoch", delta=1)])
    assert not r_bypass.ok
    assert r_bypass.error == "cannot advance epoch before settling current epoch"

    # Settle first, then advance is allowed -> the enforced order is settle-before-advance.
    r_settle = _apply(state, [_op("settle_epoch")])
    assert r_settle.ok, r_settle.error
    r_adv = _apply(r_settle.state, [_op("advance_epoch", delta=1)])
    assert r_adv.ok, r_adv.error
