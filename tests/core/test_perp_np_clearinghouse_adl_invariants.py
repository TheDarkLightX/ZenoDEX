"""Tracked ADL invariant + defense-in-depth assurance for the N-party clearinghouse.

Closes a tracked-suite gap: the comprehensive ADL property tests lived only in the
git-ignored ``experiments/perp_np_clearinghouse_v1`` (per the promotion note in
``test_perp_np_clearinghouse.py``). This module brings reachable-trajectory
invariants + defense-in-depth ADL branch coverage into the tracked CI suite and
binds the runtime N-party ADL to ``lean-mathlib/Proofs/PerpADLSybilBankruptcyClosure.lean``.

Three layers:

  A. Reachable trajectories under VALID params -- the two master invariants
     (net-zero + value conservation) PLUS collateral>=0, the insurance-accounting
     identity, claims monotonicity, and a non-negative fee pool hold at EVERY
     epoch across thousands of deterministic seeded trajectories. Bad-debt is not
     observed here: the buffer ordering ``max_oracle_move <= maint+depeg <=
     initial_margin`` means a clamped price move cannot outrun the maintenance
     buffer, so from an initial-margin-funded open the liquidation step catches an
     account while its collateral is still POSITIVE (see the structural note's scope).

  B. Defense-in-depth ADL branch under buffer-VIOLATING stress params, exercised
     through the PUBLIC ``apply_settle`` path -- insurance-draw, insurance+winner-
     haircut, and full winner-haircut all restore solvency (collateral>=0,
     conservation, net-zero). These stress params violate the production buffer
     ordering, which the ``PerpClearinghouseNpMarketState`` snapshot type rejects
     (see ``test_state_type_rejects_invalid_margin_params_ordering`` in
     ``test_perp_np_clearinghouse.py``); the core ``MarketParams`` used here has no
     validator, so these params reach the settlement only via the core test path
     and exist ONLY to drive the branch that is unreachable in layer A.

  C. Lean binding -- a NARROW arithmetic-witness check (Lean is not run here): the
     2-leg offsetting witness returns the attacker to exactly its stake (zero profit,
     zero insurance draw), matching the runtime numbers to the Lean witness in
     ``adl_blocks_sybil_bankruptcy_profit`` / ``adl_treasury_draw_zero_for_offsetting_sybil``
     -- one concrete instance, not full theorem-set equivalence.

Structural note (SCOPED + bounded-empirical; NOT a closed proof). The no-insolvency
property is scoped to states reachable via ``deposit -> match``, where the matcher
enforces INITIAL margin on every open position. Across the seeded fuzzes here
(~1,500 valid-param + ~800 stress-param such trajectories, ~8k settle epochs,
funding on/off; development exploration ~10x more) ``SettleInsolvent`` was never
observed on the public ``apply_settle`` path. Argument: from an initial-margin-
funded open, underwater accounts pay zero liquidation penalty (``liq_penalty_e8``
caps it at ``max(collateral, 0) = 0``), so ``bad_debt = sum (loss - collateral)+
<= sum loss = sum gain`` (zero-sum MTM); the winner budget equals ``sum winner pnl
= sum gain >= bad_debt``. Funding is charged BETWEEN MTM and liquidation, so a
winner that pays funding has a budget capped below its pnl, but the funding it pays
is received by others (reducing their bad-debt) up to a sub-e8 dust leak, so the
bound survives -- corroborated by
``test_adl_stays_solvent_under_funding_and_bad_debt_stress``.

IMPORTANT LIMIT (surfaced by adversarial review): the snapshot type
``PerpClearinghouseNpMarketState`` validates net-zero + conservation but NOT
per-account maintenance margin, so a VALIDATED snapshot can carry open positions
below maintenance (e.g. zero collateral). Such a state is NOT deposit->match-
reachable (``check_invariants`` flags it with a ``(V) below maintenance``
violation) and settling it CAN raise ``SettleInsolvent`` -- which the integration
engine catches FAIL-CLOSED (``perp_engine`` returns
``clearinghouse_np_settle_insolvent``, no partial state). See
``test_settle_insolvent_from_below_maintenance_snapshot_is_fail_closed``. So the
no-insolvency property holds for the reachable region, NOT for arbitrary validated
snapshots.

The CORE inequality of the argument -- ``badDebt <= gain`` (the winner budget covers
the bad debt) for ANY net-zero book with non-negative collateral -- is now
MACHINE-CHECKED for arbitrary N in
``lean-mathlib/Proofs/PerpNpNoInsolvencyBudget.lean`` (theorem ``badDebt_le_gain``;
axiom-clean -- propext/Classical.choice/Quot.sound only -- and a strict
generalization of the 2-leg witness in ``PerpADLSybilBankruptcyClosure.lean`` to
any N). The runtime instantiation is bound by
``test_runtime_badDebt_le_gain_matches_lean_theorem`` below; the funding dust-leak
extension remains corroborated-not-proved. ``SettleInsolvent`` is also reachable
when ``_apply_liquidation_adl`` is called in isolation with a non-zero-sum
``pnl_map`` (the isolation test below).
"""

from __future__ import annotations

import random
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

import src.core.perp_np_clearinghouse as C  # noqa: E402
from src.core.perp_np_matching import E8, Intent  # noqa: E402

PRICE0 = 100 * E8
BPS = 10_000


def _pk(tag: str) -> str:
    return "0x" + (tag * 48)[:48].ljust(48, tag[0])


def _valid_params() -> C.MarketParams:
    """Production-shaped params: max_oracle_move (500) <= maint+depeg (600) <= initial (1000)."""
    return C.MarketParams(
        initial_margin_bps=1000, maintenance_margin_bps=500, depeg_buffer_bps=100,
        liquidation_penalty_bps=50, max_oracle_move_bps=500, funding_cap_bps=100,
        max_position_abs=1_000_000, min_notional_for_bounty_e8=100 * E8,
    )


def _stress_params() -> C.MarketParams:
    """Buffer-VIOLATING stress params (max move 4000 >> maint+depeg 600). Used ONLY to
    drive the defense-in-depth ADL branch that is unreachable under valid params.
    The snapshot type rejects this ordering; the core MarketParams has no validator."""
    return C.MarketParams(
        initial_margin_bps=1000, maintenance_margin_bps=500, depeg_buffer_bps=100,
        liquidation_penalty_bps=50, max_oracle_move_bps=4000, funding_cap_bps=100,
        max_position_abs=1_000_000, min_notional_for_bounty_e8=100 * E8,
    )


def _initial_margin_e8(base: int, price_e8: int, params: C.MarketParams) -> int:
    return abs(base) * price_e8 * params.initial_margin_bps // BPS


def _open_book(params: C.MarketParams, legs: dict[str, int], *,
               deposit_mult: float = 1.05, ins_seed: int = 0) -> C.MarketState:
    """init -> deposit (deposit_mult x each leg's initial margin) -> match. Reachable."""
    m = C.init_market(PRICE0, params=params, insurance_seed_e8=ins_seed)
    for tag, base in legs.items():
        amt = max(int(_initial_margin_e8(base, PRICE0, params) * deposit_mult), 1)
        m = C.deposit(m, _pk(tag), amt)
    m, _ = C.apply_match(m, [Intent(_pk(tag), target_base=b, nonce=1)
                             for tag, b in legs.items()])
    return m


def _hard_invariant_violations(m: C.MarketState) -> list[str]:
    """The invariants that must hold after EVERY accepted settle (empty == all hold)."""
    bad = list(C.check_invariants(m))  # (I) net-zero + (II) value conservation
    for a in m.accounts:
        if a.collateral_e8 < 0:
            bad.append(f"negative collateral {a.pubkey[:8]}={a.collateral_e8}")
    if m.insurance_e8 < 0:
        bad.append(f"negative insurance={m.insurance_e8}")
    if m.insurance_e8 != m.insurance_ext_e8 - m.claims_paid_e8:
        bad.append(f"insurance accounting {m.insurance_e8} != "
                   f"{m.insurance_ext_e8} - {m.claims_paid_e8}")
    if m.claims_paid_e8 < 0:
        bad.append(f"negative claims_paid={m.claims_paid_e8}")
    if m.fee_pool_e8 < 0:
        bad.append(f"negative fee_pool={m.fee_pool_e8}")
    return bad


def _random_balanced(rng: random.Random, n: int) -> list[int]:
    """n nonzero integer positions summing to 0 (a reachable net-zero opening book)."""
    pos = [rng.randint(-20, 20) or 1 for _ in range(n - 1)]
    pos.append(-sum(pos))
    if pos[-1] == 0:                       # avoid a zero closing leg
        pos[0] += 1
        pos[-1] = -sum(pos[:-1])
    return pos


# ---------------------------------------------------------------------------
# Layer A: reachable trajectories under VALID params -> invariants always hold
# ---------------------------------------------------------------------------
def test_trajectory_invariants_hold_under_valid_params():
    """Deterministic seeded fuzz: across many reachable multi-epoch trajectories the
    full hard-invariant set holds at every accepted settle. Asserts the fuzz is
    NON-VACUOUS by requiring it to actually exercise liquidation/ADL."""
    rng = random.Random(20260614)
    params = _valid_params()
    trajectories = 0
    settle_epochs = 0
    liquidation_epochs = 0
    insurance_draws = 0
    insolvencies = 0

    for _ in range(1500):
        n = rng.randint(2, 6)
        pos = _random_balanced(rng, n)
        ins_seed = rng.choice([0, 10 ** 9, 10 ** 12, 10 ** 15])
        legs = {f"{i:02x}": pos[i] for i in range(n)}
        m = C.init_market(PRICE0, params=params, insurance_seed_e8=ins_seed)
        for tag, base in legs.items():
            amt = max(int(_initial_margin_e8(base, PRICE0, params)
                          * rng.uniform(1.001, 3.0)), 1)
            m = C.deposit(m, _pk(tag), amt)
        try:
            m, _ = C.apply_match(m, [Intent(_pk(t), target_base=b, nonce=1)
                                     for t, b in legs.items()])
        except Exception:
            continue
        if C.net_position(m) != 0:         # matcher rationed a heavy side; skip
            continue
        trajectories += 1

        price = PRICE0
        for _ in range(rng.randint(1, 12)):
            price = max(int(price * rng.choice([1.05, 1.05, 1.05, 0.95, 1.02])), 1)
            frate = rng.choice([0, 0, 50, 100, -100])
            ins_before, claims_before = m.insurance_e8, m.claims_paid_e8
            open_before = [a.pubkey for a in m.accounts if a.position_base != 0]
            try:
                nxt = C.apply_settle(m, clearing_price_e8=price, funding_rate_bps=frate)
            except C.SettleInsolvent:
                insolvencies += 1
                break
            settle_epochs += 1
            violations = _hard_invariant_violations(nxt)
            assert not violations, f"epoch invariants violated: {violations}"
            if nxt.insurance_e8 < ins_before or nxt.claims_paid_e8 > claims_before:
                insurance_draws += 1
            closed = [pk for pk in open_before
                      if next((a.position_base for a in nxt.accounts
                               if a.pubkey == pk), 0) == 0]
            if closed:
                liquidation_epochs += 1
            m = nxt
            if not any(a.position_base for a in m.accounts):
                break

    # Non-vacuity: the fuzz must actually reach the liquidation/ADL machinery.
    assert trajectories >= 1000, f"too few reachable trajectories: {trajectories}"
    assert settle_epochs >= 3000, f"too few settle epochs: {settle_epochs}"
    assert liquidation_epochs >= 100, (
        f"fuzz never exercised liquidation/ADL ({liquidation_epochs}) -- vacuous")
    # Structural (bounded) finding: valid-param buffer ordering keeps bad-debt
    # unreachable, so no insurance draw and no insolvency ever occur here.
    assert insurance_draws == 0, (
        f"unexpected insurance draw under valid params: {insurance_draws}")
    assert insolvencies == 0, (
        f"unexpected insolvency under valid params: {insolvencies}")


def test_clean_liquidation_keeps_collateral_non_negative_valid_params():
    """A thin-margin account liquidated by a single clamped adverse move closes with
    NON-NEGATIVE collateral (no bad-debt) -- the buffer-ordering guarantee, concretely."""
    params = _valid_params()
    m = _open_book(params, {"aa": 10, "bb": -6, "cc": -4}, deposit_mult=1.02)
    # +5% (max clamp) is adverse to the shorts; thin margin -> liquidation.
    nxt = C.apply_settle(m, clearing_price_e8=PRICE0 * 105 // 100, funding_rate_bps=0)
    assert _hard_invariant_violations(nxt) == []
    assert all(a.collateral_e8 >= 0 for a in nxt.accounts)
    assert nxt.insurance_e8 == m.insurance_e8           # no insurance draw
    assert nxt.claims_paid_e8 == m.claims_paid_e8


# ---------------------------------------------------------------------------
# Layer B: defense-in-depth ADL branch (buffer-violating stress params)
# ---------------------------------------------------------------------------
def _bankrupt_shorts_scenario(ins_seed: int):
    """3-party book, thin margin, +40% move (allowed only by stress params): the
    shorts go underwater, the long wins. Returns (pre_state, post_state)."""
    params = _stress_params()
    m = _open_book(params, {"aa": 10, "bb": -6, "cc": -4},
                   deposit_mult=1.05, ins_seed=ins_seed)
    post = C.apply_settle(m, clearing_price_e8=140 * E8, funding_rate_bps=0)
    return m, post


def test_adl_insurance_draw_covers_bad_debt_no_haircut():
    """Ample insurance: bad-debt is paid entirely from insurance, the winner is NOT
    haircut, and every invariant holds."""
    pre, post = _bankrupt_shorts_scenario(ins_seed=10 ** 15)
    assert _hard_invariant_violations(post) == []
    assert all(a.collateral_e8 >= 0 for a in post.accounts)
    assert post.insurance_e8 < pre.insurance_e8                 # insurance was drawn
    drawn = pre.insurance_e8 - post.insurance_e8
    assert post.claims_paid_e8 == pre.claims_paid_e8 + drawn    # claims == draw
    # Winner (aa) keeps its full zero-sum MTM gain (no haircut): collateral grew.
    aa_pre = next(a for a in pre.accounts if a.pubkey == _pk("aa"))
    aa_post = next(a for a in post.accounts if a.pubkey == _pk("aa"))
    assert aa_post.collateral_e8 > aa_pre.collateral_e8
    assert C.net_position(post) == 0


def test_adl_winner_haircut_when_insurance_insufficient():
    """Tiny insurance: insurance drains to zero, then the winner is haircut for the
    residual; solvency is still fully restored."""
    pre, post = _bankrupt_shorts_scenario(ins_seed=10 ** 6)
    assert _hard_invariant_violations(post) == []
    assert all(a.collateral_e8 >= 0 for a in post.accounts)
    assert post.insurance_e8 == 0                               # fully drained
    assert post.claims_paid_e8 == pre.claims_paid_e8 + 10 ** 6  # drew the whole seed
    assert C.net_position(post) == 0


def test_adl_full_winner_haircut_zero_insurance():
    """Zero insurance: the winner-haircut alone covers the bad-debt. With zero-sum MTM
    the winner's gain always suffices, so no SettleInsolvent. Conservation pins the
    winner's final collateral to the conserved total (insurance/fee untouched)."""
    pre, post = _bankrupt_shorts_scenario(ins_seed=0)
    assert _hard_invariant_violations(post) == []
    assert all(a.collateral_e8 >= 0 for a in post.accounts)
    assert post.insurance_e8 == 0 and post.claims_paid_e8 == 0  # no insurance involved
    # Insurance + fee untouched => total collateral is conserved across the settle.
    assert C.total_collateral_e8(post) == C.total_collateral_e8(pre)
    assert C.net_position(post) == 0


def test_adl_zero_sum_mtm_keeps_public_settle_solvent_across_insurance_levels():
    """Corroborates the structural argument over a sweep of insurance levels (from 0
    to ample) for a fixed bankruptcy scenario: the winner budget covers the residual
    at every level, so none triggers SettleInsolvent. Bounded check, not a proof."""
    for ins_seed in (0, 1, 10 ** 3, 10 ** 6, 10 ** 9, 10 ** 12, 10 ** 15):
        _, post = _bankrupt_shorts_scenario(ins_seed=ins_seed)
        assert _hard_invariant_violations(post) == [], f"ins_seed={ins_seed}"
        assert all(a.collateral_e8 >= 0 for a in post.accounts), f"ins_seed={ins_seed}"


def test_adl_stays_solvent_under_funding_and_bad_debt_stress():
    """The subtlest part of the public-path solvency guarantee: funding is charged
    BEFORE liquidation, so a winner that PAYS funding has a reduced haircut budget.
    But funding paid by winners is received by others (reducing bad-debt) modulo a
    sub-e8 dust leak to the fee pool, so the winner budget still covers the residual.
    Seeded stress fuzz (buffer-violating params, big swings, funding ON) confirms no
    SettleInsolvent and that all invariants hold -- AND that the bad-debt/insurance
    ADL branch is actually exercised (non-vacuity via the insurance-draw counter)."""
    rng = random.Random(99)
    params = _stress_params()
    tested = 0
    insurance_draws = 0
    for _ in range(800):
        n = rng.randint(2, 5)
        pos = _random_balanced(rng, n)
        ins_seed = rng.choice([0, 1, 10 ** 6, 10 ** 9, 10 ** 12])
        legs = {f"{i:02x}": pos[i] for i in range(n)}
        m = C.init_market(PRICE0, params=params, insurance_seed_e8=ins_seed)
        for tag, base in legs.items():
            amt = max(int(_initial_margin_e8(base, PRICE0, params)
                          * rng.uniform(1.0, 1.3)), 1)
            m = C.deposit(m, _pk(tag), amt)
        try:
            m, _ = C.apply_match(m, [Intent(_pk(t), target_base=b, nonce=1)
                                     for t, b in legs.items()])
        except Exception:
            continue
        if C.net_position(m) != 0:
            continue
        tested += 1
        price = PRICE0
        for _ in range(rng.randint(1, 6)):
            price = max(int(price * rng.choice([1.40, 1.40, 0.60, 1.25])), 1)
            frate = rng.choice([100, -100, 50, -50, 0])
            ins_before = m.insurance_e8
            try:
                nxt = C.apply_settle(m, clearing_price_e8=price, funding_rate_bps=frate)
            except C.SettleInsolvent:
                pytest.fail("SettleInsolvent reached on the public path under "
                            "funding+bad-debt -- winner budget failed to cover residual")
            assert _hard_invariant_violations(nxt) == []
            if nxt.insurance_e8 < ins_before:
                insurance_draws += 1
            m = nxt
            if not any(a.position_base for a in m.accounts):
                break
    assert tested >= 400, f"too few stress trajectories: {tested}"
    assert insurance_draws >= 100, (
        f"bad-debt/insurance ADL branch not exercised ({insurance_draws}) -- vacuous")


def test_settle_insolvent_from_below_maintenance_snapshot_is_fail_closed():
    """Adversarial-review counterexample (turned into a positive artifact): the
    snapshot validator checks net-zero + conservation but NOT per-account maintenance
    margin, so a state with open positions BELOW maintenance (here: zero collateral)
    is constructible even with VALID margin params. It is NOT deposit->match-reachable
    -- ``check_invariants`` flags it with a ``(V) below maintenance`` violation -- and
    settling it raises ``SettleInsolvent``. The raise is FAIL-CLOSED: ``apply_settle``
    is a total function that raises before returning any state, so no partial state
    escapes (the integration engine maps this to ``clearinghouse_np_settle_insolvent``).
    This bounds the structural no-insolvency claim to the reachable region."""
    # Valid margin params (ordering holds): the counterexample is NOT about misconfig.
    m = C.MarketState(
        index_price_e8=PRICE0, params=_valid_params(),
        accounts=(
            C.Account(pubkey=_pk("aa"), position_base=1, entry_price_e8=PRICE0, collateral_e8=0),
            C.Account(pubkey=_pk("bb"), position_base=-1, entry_price_e8=PRICE0, collateral_e8=0),
        ),
    )
    # The input is net-zero + conserved but OUTSIDE the deposit->match-reachable region:
    assert C.net_position(m) == 0
    violations = C.check_invariants(m)
    assert any("below maintenance" in v for v in violations), violations
    # Public-path settle of this validated-but-unreachable state is fail-closed.
    with pytest.raises(C.SettleInsolvent):
        C.apply_settle(m, clearing_price_e8=105 * E8, funding_rate_bps=0)


def test_settle_insolvent_isolation_path_is_fail_closed_no_op():
    """``SettleInsolvent`` is also reachable by calling ``_apply_liquidation_adl`` in
    isolation with a non-zero-sum ``pnl_map`` (bad-debt with no offsetting winner) --
    a path the zero-sum public settle does not produce from reachable states. The
    raise leaves no partial state (it raises before any mutation is returned)."""
    accts = {
        _pk("aa"): C.Account(pubkey=_pk("aa"), position_base=5,
                             entry_price_e8=PRICE0, collateral_e8=-1_000),
        _pk("bb"): C.Account(pubkey=_pk("bb"), position_base=-5,
                             entry_price_e8=PRICE0, collateral_e8=10 ** 12),
    }
    pnl_map = {_pk("aa"): -1_000, _pk("bb"): 0}   # no positive-PnL winner
    with pytest.raises(C.SettleInsolvent):
        C._apply_liquidation_adl(accts, PRICE0, pnl_map, _stress_params(),
                                 fee_pool=0, insurance=0, claims_paid=0,
                                 flagged=set())


# ---------------------------------------------------------------------------
# Layer C: bind the runtime ADL to the Lean 2-leg offsetting witness
# ---------------------------------------------------------------------------
def test_two_leg_offsetting_witness_matches_lean_adl_closure():
    """NARROW binding (one concrete arithmetic witness, NOT full theorem-set
    equivalence, and Lean is not run here): a 2-leg book with EQUAL margins, one leg
    bankrupt and the other the offsetting winner. With zero insurance the ADL haircut
    returns the attacker (both legs) to EXACTLY its combined stake -- zero profit,
    zero insurance draw -- matching the runtime numbers to the Lean witness in
    lean-mathlib/Proofs/PerpADLSybilBankruptcyClosure.lean
    (adl_blocks_sybil_bankruptcy_profit: final == 2*margin;
    adl_treasury_draw_zero_for_offsetting_sybil: zero draw). It does NOT cover funding,
    rounding, penalties, or the multi-leg pro-rata haircut -- those are exercised by
    the fuzz tests above, not by this witness."""
    params = _stress_params()
    # Equal-size legs => equal margins (the Lean witness's `margin` on both sides).
    m = _open_book(params, {"aa": 8, "bb": -8}, deposit_mult=1.0, ins_seed=0)
    aa_pre = next(a for a in m.accounts if a.pubkey == _pk("aa"))
    bb_pre = next(a for a in m.accounts if a.pubkey == _pk("bb"))
    stake = aa_pre.collateral_e8 + bb_pre.collateral_e8        # attacker's 2-leg stake
    assert aa_pre.collateral_e8 == bb_pre.collateral_e8        # equal margins

    # +40% move: bb (short) bankrupt, aa (long) the offsetting winner.
    post = C.apply_settle(m, clearing_price_e8=140 * E8, funding_rate_bps=0)
    aa_post = next(a for a in post.accounts if a.pubkey == _pk("aa"))
    bb_post = next(a for a in post.accounts if a.pubkey == _pk("bb"))

    # Lean: ADLSybilFinalCapital = 2*margin (== stake); StandardInsuranceDraw avoided.
    assert aa_post.collateral_e8 + bb_post.collateral_e8 == stake   # zero net profit
    assert bb_post.collateral_e8 == 0                              # loser zeroed
    assert post.insurance_e8 == 0 and post.claims_paid_e8 == 0     # zero treasury draw
    assert _hard_invariant_violations(post) == []
    assert C.net_position(post) == 0


def test_runtime_badDebt_le_gain_matches_lean_theorem():
    """Binds the runtime mark-to-market to the machine-checked N-party theorem
    ``badDebt_le_gain`` in lean-mathlib/Proofs/PerpNpNoInsolvencyBudget.lean: for a
    net-zero position book with non-negative collateral, the runtime's OWN PnL
    (``C.pnl_e8``) is zero-sum, and the derived bad debt = sum max(0, -(c+p)) is
    <= the winner budget gain = sum max(0, p). This is the abstract no-insolvency
    bound the ADL relies on, exercised over arbitrary N on runtime-computed PnL (so
    the Lean model's hypotheses and conclusion are checked against the live code,
    not a re-derivation). Holds for ANY price move, so we sweep wide moves."""
    rng = random.Random(4242)
    binding = 0  # cases where bad-debt is actually positive (bound actively constrains)
    for _ in range(500):
        n = rng.randint(2, 8)
        pos = _random_balanced(rng, n)
        s = max(PRICE0 * rng.randint(10, 300) // 100, 1)     # wide moves, incl. extreme
        coll = [rng.randint(0, 10 ** 11) for _ in range(n)]  # thin enough to drive bad-debt
        pnl = [C.pnl_e8(p, s, PRICE0) for p in pos]          # runtime MTM
        assert sum(pnl) == 0, "runtime MTM must be zero-sum on a net-zero book"
        bad_debt = sum(max(0, -(c + p)) for c, p in zip(coll, pnl, strict=True))
        gain = sum(max(0, p) for p in pnl)
        assert bad_debt <= gain, (
            f"Lean badDebt_le_gain refuted on runtime PnL: {bad_debt} > {gain} "
            f"(pos={pos}, coll={coll}, s={s})")
        if bad_debt > 0:
            binding += 1
    # Non-vacuity: the bound actively constrains (positive bad-debt) in many cases,
    # not just the trivial 0 <= gain.
    assert binding >= 50, f"bound never actively constrained ({binding}) -- vacuous"
    # Tight boundary (zero collateral): bad-debt == gain == total loss EXACTLY, so the
    # inequality is provably attained, not merely slack.
    tpnl = [C.pnl_e8(p, 140 * E8, PRICE0) for p in (10, -6, -4)]
    tbad = sum(max(0, -(0 + p)) for p in tpnl)
    tgain = sum(max(0, p) for p in tpnl)
    assert tbad == tgain and tbad > 0, f"tight boundary not attained: {tbad} vs {tgain}"
