#!/usr/bin/env python3
"""Research-only N-party net-zero clearinghouse reference.

EXPERIMENTAL / PENDING REVIEW — public testnet (fake value) design evidence only.
Available only behind an explicit non-production engine capability and
physically excluded from production artifacts.

This module pins the EXACT integer semantics of the design so that the Rust/Kani
crate can mirror it, the Lean proofs can abstract it, the ESSO kernel can encode
it, and the Julia sims can drive it — all against the same definitions.

Ledger convention (matches the live 2p/3p clearinghouse kernels): collateral,
fees and insurance are held in **quote-e8** (quote * 1e8). Notional and PnL are
``position_base * price_e8`` with NO division, so mark-to-market is exactly
zero-sum (DESIGN 4.6). The only floored quantities are funding (DESIGN 4.5),
liquidation penalty, and the matcher rationing (DESIGN 4.4) — each routes its
dust deterministically so conservation stays exact.

Phase-gating (OPEN -> PRICE_PUBLISHED -> SETTLED) is modelled in the ESSO kernel;
this reference focuses on the accounting math and the ADL algorithm.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Mapping, Sequence

from src.core.perp_liquidation_envelope import require_perp_liquidation_envelope_bps
from src.nonproduction.perp_np_matching import (
    BPS_SCALE,
    I128_MAX,
    Intent,
    MatchParams,
    MatchResult,
    _ration,
    match_intents,
)

# Liquidation outcome marker (fail-closed).
REJ_INSOLVENT = "REJ_INSOLVENT"


class SettleInsolvent(Exception):
    """Raised when bad debt exceeds insurance + winner profit — settle must revert."""


# --- Pure math primitives (e8 ledger) -----------------------------------------
def maint_req_e8(position_base: int, price_e8: int, maint_bps: int, depeg_bps: int) -> int:
    """Maintenance + depeg-buffer requirement (quote-e8) for an open position.

    ``ceil(|pos| * price_e8 * (maint_bps + depeg_bps) / 1e4)``.
    Plain English: the minimum collateral an open position must keep, or it is liquidated.
    """
    notional_e8 = abs(position_base) * price_e8
    num = notional_e8 * (maint_bps + depeg_bps)
    _guard(num)
    return (num + BPS_SCALE - 1) // BPS_SCALE


def settle_price_e8(clearing_e8: int, index_e8: int, max_move_bps: int) -> int:
    """Clamp the clearing price to ``index +/- ceil(index * max_move_bps / 1e4)``.

    Plain English: a single epoch's settlement price cannot jump more than the
    configured oracle-move cap away from the prior mark (gap-risk protection).
    """
    if index_e8 <= 0:
        return clearing_e8
    diff = abs(clearing_e8 - index_e8)
    if diff * BPS_SCALE > max_move_bps * index_e8:
        max_delta = (index_e8 * max_move_bps + BPS_SCALE - 1) // BPS_SCALE
        return index_e8 + max_delta if clearing_e8 > index_e8 else index_e8 - max_delta
    return clearing_e8


def pnl_e8(position_base: int, settle_e8: int, mark_e8: int) -> int:
    """Exact mark-to-market PnL (quote-e8): ``pos * (settle - mark)`` — no division.

    Plain English: the gain/loss of marking a position from the common prior price
    to the settlement price; summed over a net-zero book it is exactly 0.
    """
    val = position_base * (settle_e8 - mark_e8)
    _guard(abs(val))
    return val


def funding_num(position_base: int, index_e8: int, rate_bps: int) -> int:
    """Unsigned funding numerator ``|pos| * index_e8 * |rate|`` (before /1e4).

    Computed on UNSIGNED operands so floor == trunc and the result is identical on
    Python and Rust; the sign is applied by the caller (DESIGN 4.5).
    """
    num = abs(position_base) * index_e8 * abs(rate_bps)
    _guard(num)
    return num


def is_funding_payer(position_base: int, rate_bps: int) -> bool:
    """True if this account PAYS funding (long & positive rate, or short & negative)."""
    if position_base == 0 or rate_bps == 0:
        return False
    return (position_base > 0) == (rate_bps > 0)


def liq_penalty_e8(notional_e8: int, collateral_e8: int, penalty_bps: int,
                   min_notional_e8: int) -> int:
    """Liquidation penalty (quote-e8): 0 below the bounty floor, else
    ``floor(notional * penalty_bps / 1e4)``, capped at non-negative collateral."""
    if notional_e8 < min_notional_e8:
        return 0
    raw = (notional_e8 * penalty_bps) // BPS_SCALE
    return min(raw, max(collateral_e8, 0))


def _guard(value: int) -> None:
    if value > I128_MAX:
        raise OverflowError("operand exceeds i128 bound")


# --- State ---------------------------------------------------------------------
@dataclass(frozen=True)
class Account:
    pubkey: str
    position_base: int = 0
    entry_price_e8: int = 0
    collateral_e8: int = 0
    funding_paid_cum_e8: int = 0
    nonce: int = 0


@dataclass(frozen=True)
class MarketParams:
    initial_margin_bps: int = 1000
    maintenance_margin_bps: int = 500
    depeg_buffer_bps: int = 100
    liquidation_penalty_bps: int = 50
    max_oracle_move_bps: int = 500
    funding_cap_bps: int = 100
    max_position_abs: int = 1_000_000
    min_notional_for_bounty_e8: int = 100_000_000

    def __post_init__(self) -> None:
        _require_bps(self.initial_margin_bps, name="initial_margin_bps", allow_zero=False)
        _require_bps(self.maintenance_margin_bps, name="maintenance_margin_bps", allow_zero=False)
        _require_bps(self.depeg_buffer_bps, name="depeg_buffer_bps", allow_zero=True)
        _require_bps(self.liquidation_penalty_bps, name="liquidation_penalty_bps", allow_zero=True)
        _require_bps(self.max_oracle_move_bps, name="max_oracle_move_bps", allow_zero=False)
        _require_bps(self.funding_cap_bps, name="funding_cap_bps", allow_zero=False)
        if not isinstance(self.max_position_abs, int) or isinstance(self.max_position_abs, bool):
            raise ValueError("max_position_abs must be an int")
        if self.max_position_abs <= 0:
            raise ValueError("max_position_abs out of range")
        if not isinstance(self.min_notional_for_bounty_e8, int) or isinstance(self.min_notional_for_bounty_e8, bool):
            raise ValueError("min_notional_for_bounty_e8 must be an int")
        if self.min_notional_for_bounty_e8 < 0:
            raise ValueError("min_notional_for_bounty_e8 must be non-negative")
        require_perp_liquidation_envelope_bps(
            initial_margin_bps=self.initial_margin_bps,
            maintenance_margin_bps=self.maintenance_margin_bps,
            depeg_buffer_bps=self.depeg_buffer_bps,
            max_oracle_move_bps=self.max_oracle_move_bps,
            liquidation_penalty_bps=self.liquidation_penalty_bps,
        )

    def match_params(self) -> MatchParams:
        return MatchParams(self.initial_margin_bps, self.max_position_abs)


def _require_bps(value: object, *, name: str, allow_zero: bool) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValueError(f"{name} must be an int")
    minimum = 0 if allow_zero else 1
    if not (minimum <= int(value) <= BPS_SCALE):
        raise ValueError(f"{name} out of range")
    return int(value)


@dataclass(frozen=True)
class MarketState:
    index_price_e8: int                       # the common current mark
    params: MarketParams
    accounts: tuple[Account, ...] = ()
    now_epoch: int = 0
    fee_pool_e8: int = 0
    insurance_e8: int = 0                      # current insurance balance
    insurance_ext_e8: int = 0                  # cumulative external seed + top-ups (I_ext)
    claims_paid_e8: int = 0
    net_deposited_e8: int = 0                  # D: cumulative trader deposits

    def by_pubkey(self) -> dict[str, Account]:
        return {a.pubkey: a for a in self.accounts}

    def with_accounts(self, accts: Mapping[str, Account]) -> "MarketState":
        ordered = tuple(accts[k] for k in sorted(accts))
        return replace(self, accounts=ordered)


# --- Constructors / simple transitions ----------------------------------------
def init_market(index_price_e8: int, params: MarketParams | None = None,
                insurance_seed_e8: int = 0) -> MarketState:
    if index_price_e8 <= 0:
        raise ValueError("index_price_e8 must be positive")
    if insurance_seed_e8 < 0:
        raise ValueError("insurance seed must be non-negative")
    p = params or MarketParams()
    return MarketState(
        index_price_e8=index_price_e8,
        params=p,
        insurance_e8=insurance_seed_e8,
        insurance_ext_e8=insurance_seed_e8,
    )


def deposit(state: MarketState, pubkey: str, amount_e8: int) -> MarketState:
    """Join (if new) and credit collateral. Trader deposit -> D and Sigma collateral both += amount."""
    if amount_e8 < 0:
        raise ValueError("deposit must be non-negative")
    accts = state.by_pubkey()
    a = accts.get(pubkey, Account(pubkey=pubkey))
    accts[pubkey] = replace(a, collateral_e8=a.collateral_e8 + amount_e8)
    new_state = state.with_accounts(accts)
    return replace(new_state, net_deposited_e8=state.net_deposited_e8 + amount_e8)


def withdraw(state: MarketState, pubkey: str, amount_e8: int) -> MarketState:
    """Withdraw collateral. Fail-closed (raises) unless `amount <= collateral` (collateral stays
    >= 0) and -- if the account is open -- the remaining collateral still meets maintenance margin.
    The withdrawal is bounded ONLY by the account's own collateral: a winner's collateral is
    legitimately theirs even when an insurance payout funded part of it (the insurance fund exists
    precisely to make winners whole when a counterparty defaults), so it must be withdrawable.
    `net_deposited` (cumulative deposits) may therefore go negative -- it stays >= -claims_paid since
    `net_deposited + claims_paid = Σ collateral + fee_pool >= 0`. Mirrors the ESSO `withdraw_i` guard.
    (Bounding by `net_deposited` instead would TRAP insurance-funded profit -- a bug a cross-model
    review caught.)"""
    if amount_e8 < 0:
        raise ValueError("withdraw must be non-negative")
    accts = state.by_pubkey()
    a = accts.get(pubkey)
    if a is None or amount_e8 > a.collateral_e8:
        raise ValueError("withdraw exceeds collateral")
    remaining = a.collateral_e8 - amount_e8
    if a.position_base != 0:
        req = maint_req_e8(a.position_base, state.index_price_e8,
                           state.params.maintenance_margin_bps, state.params.depeg_buffer_bps)
        if remaining < req:
            raise ValueError("withdraw would breach maintenance margin")
    accts[pubkey] = replace(a, collateral_e8=remaining)
    new_state = state.with_accounts(accts)
    return replace(new_state, net_deposited_e8=state.net_deposited_e8 - amount_e8)


def seed_insurance(state: MarketState, amount_e8: int) -> MarketState:
    if amount_e8 < 0:
        raise ValueError("insurance seed must be non-negative")
    return replace(state, insurance_e8=state.insurance_e8 + amount_e8,
                   insurance_ext_e8=state.insurance_ext_e8 + amount_e8)


# --- Matching step: open/modify positions at the current mark ------------------
def apply_match(state: MarketState, intents: Sequence[Intent]) -> tuple[MarketState, MatchResult]:
    """Run the matcher at the current mark; opened positions enter at ``index_price_e8``.

    Entry is set to the common mark so that the next mark-to-market is exactly
    zero-sum across the book (DESIGN 4.6 / inv_entry_matches_price_when_open).
    """
    accts = state.by_pubkey()
    result = match_intents(
        intents,
        current_positions={pk: a.position_base for pk, a in accts.items()},
        collaterals={pk: a.collateral_e8 for pk, a in accts.items()},
        last_nonces={pk: a.nonce for pk, a in accts.items()},
        clearing_price_e8=state.index_price_e8,
        now_epoch=state.now_epoch,
        params=state.params.match_params(),
    )
    for pk, delta in result.deltas.items():
        a = accts.get(pk, Account(pubkey=pk))
        new_pos = a.position_base + delta
        accts[pk] = replace(
            a,
            position_base=new_pos,
            entry_price_e8=state.index_price_e8 if new_pos != 0 else 0,
        )
    # advance each acting account's nonce to the chosen intent's nonce
    for r in result.receipts:
        if r.status == "filled":
            receipt_account = accts.get(r.pubkey)
            if receipt_account is not None and r.nonce > receipt_account.nonce:
                accts[r.pubkey] = replace(receipt_account, nonce=r.nonce)
    return state.with_accounts(accts), result


# --- Settlement step: MTM -> funding -> liquidation/ADL ------------------------
def apply_settle(state: MarketState, clearing_price_e8: int,
                 funding_rate_bps: int) -> MarketState:
    """Mark-to-market, apply funding, then liquidate + auto-deleverage.

    Raises ``SettleInsolvent`` (fail-closed, no partial state) when bad debt
    exceeds insurance + winner profit. Otherwise the two master invariants hold.
    """
    p = state.params
    if abs(funding_rate_bps) > p.funding_cap_bps:
        raise ValueError("funding rate exceeds cap")

    mark = state.index_price_e8
    s = settle_price_e8(clearing_price_e8, mark, p.max_oracle_move_bps)
    accts = state.by_pubkey()

    # 1) Mark-to-market (exact, zero-sum): mark every open position from the COMMON prior
    #    mark `mark` (= prior index) to `s`. PnL is measured from this common mark, NOT from
    #    each account's `entry_price_e8` (entry is re-marked to `s` here and only checked by
    #    the `entry`-invariant); using the common mark is what makes Σ PnL = (s-mark)·Σpos = 0.
    pnl_map: dict[str, int] = {}
    for pk, a in list(accts.items()):
        pl = pnl_e8(a.position_base, s, mark)
        pnl_map[pk] = pl
        accts[pk] = replace(a, collateral_e8=a.collateral_e8 + pl,
                            entry_price_e8=s if a.position_base != 0 else 0)

    fee_pool = state.fee_pool_e8

    # 2) Funding at the new mark `s`: payers pay ceil, payees receive floor, dust -> fee pool.
    accts, fee_pool, flagged = _apply_funding(accts, s, funding_rate_bps, fee_pool)

    # 3) Liquidation + ADL.
    accts, fee_pool, insurance, claims_paid = _apply_liquidation_adl(
        accts, s, pnl_map, p, fee_pool, state.insurance_e8, state.claims_paid_e8, flagged
    )

    new_state = replace(
        state,
        index_price_e8=s,
        now_epoch=state.now_epoch + 1,
        fee_pool_e8=fee_pool,
        insurance_e8=insurance,
        claims_paid_e8=claims_paid,
    ).with_accounts(accts)
    return new_state


def _apply_funding(accts: dict[str, Account], index_e8: int, rate_bps: int,
                   fee_pool: int) -> tuple[dict[str, Account], int, set[str]]:
    if rate_bps == 0:
        return accts, fee_pool, set()

    coll = {pk: a.collateral_e8 for pk, a in accts.items()}
    payers: list[tuple[str, int]] = []   # (pubkey, ceil magnitude owed)
    payees: list[tuple[str, int]] = []   # (pubkey, floor magnitude owed)
    for pk, a in accts.items():
        if a.position_base == 0:
            continue
        num = funding_num(a.position_base, index_e8, rate_bps)
        if is_funding_payer(a.position_base, rate_bps):
            payers.append((pk, (num + BPS_SCALE - 1) // BPS_SCALE))   # ceil
        else:
            payees.append((pk, num // BPS_SCALE))                     # floor

    # Charge payers, clamped to NON-NEGATIVE available collateral; record shortfall
    # flags. A payer whose collateral is already negative (a within-clamp adverse MTM
    # ran before funding) pays 0 and is flagged for liquidation -- never a negative
    # "payment" (which would create value and break the rationing precondition).
    collected = 0
    flagged: set[str] = set()
    paid_by: dict[str, int] = {}
    for pk, owed in payers:
        pay = min(owed, max(coll[pk], 0))
        coll[pk] -= pay
        collected += pay
        paid_by[pk] = pay
        if pay < owed:
            flagged.add(pk)

    total_owed = sum(m for _, m in payees)
    credited: dict[str, int] = {}
    if total_owed <= collected:
        for pk, owed in payees:
            coll[pk] += owed
            credited[pk] = owed
        fee_pool += collected - total_owed            # R_f in [0, N-1], swept to fee pool
    else:
        # Collection short (clamped payers): reduce payee credits pro-rata, R_f = 0.
        weights = [(i, m) for i, (_, m) in enumerate(payees) if m > 0]
        alloc = _ration(weights, collected)
        for i, (pk, _) in enumerate(payees):
            c = alloc.get(i, 0)
            coll[pk] += c
            credited[pk] = c

    out = {}
    for pk, a in accts.items():
        delta = credited.get(pk, 0) - paid_by.get(pk, 0)   # signed funding received(+)/paid(-)
        out[pk] = replace(a, collateral_e8=coll[pk],
                          funding_paid_cum_e8=a.funding_paid_cum_e8 - delta)
    return out, fee_pool, flagged


def _apply_liquidation_adl(accts: dict[str, Account], s: int, pnl_map: Mapping[str, int],
                           params: MarketParams, fee_pool: int, insurance: int,
                           claims_paid: int,
                           flagged: set[str]) -> tuple[dict[str, Account], int, int, int]:
    new = dict(accts)

    def liquidatable(a: Account) -> bool:
        if a.position_base == 0:
            return False
        req = maint_req_e8(a.position_base, s, params.maintenance_margin_bps, params.depeg_buffer_bps)
        return a.collateral_e8 < req or a.pubkey in flagged

    L = sorted(pk for pk, a in new.items() if liquidatable(a))
    if not L:
        return new, fee_pool, insurance, claims_paid

    # Penalties -> fee pool; tally bad debt (collateral driven below 0 by losses).
    total_penalty = 0
    for pk in L:
        a = new[pk]
        notional_e8 = abs(a.position_base) * s
        pen = liq_penalty_e8(notional_e8, a.collateral_e8, params.liquidation_penalty_bps,
                             params.min_notional_for_bounty_e8)
        new[pk] = replace(a, collateral_e8=a.collateral_e8 - pen)
        total_penalty += pen
    fee_pool += total_penalty

    bad_debt = sum(-new[pk].collateral_e8 for pk in L if new[pk].collateral_e8 < 0)

    # Insurance first, then haircut winners' realized profit; else fail-closed.
    d_ins = min(bad_debt, insurance)
    residual = bad_debt - d_ins
    # Haircut capacity is capped at each winner's CURRENT collateral as well as its
    # realized profit, so the haircut can never push a winner negative (guarantees
    # c_a >= 0 unconditionally, DESIGN 4.7(iii)). On the reachable apply_settle path MTM
    # has already credited the profit into collateral, so collateral >= profit and the
    # cap is a no-op; it only bites when _apply_liquidation_adl is called in isolation.
    winners = sorted(((pk, min(pnl_map.get(pk, 0), new[pk].collateral_e8)) for pk in new
                      if pk not in L and pnl_map.get(pk, 0) > 0 and new[pk].collateral_e8 > 0),
                     key=lambda t: (-t[1], t[0]))
    budget = sum(p for _, p in winners)
    if residual > budget:
        raise SettleInsolvent(
            f"bad_debt={bad_debt} > insurance({insurance}) + winner_profit({budget})")

    insurance -= d_ins
    claims_paid += d_ins

    # Lift underwater accounts to exactly 0 (funded by d_ins + haircut residual).
    for pk in L:
        if new[pk].collateral_e8 < 0:
            new[pk] = replace(new[pk], collateral_e8=0)
    if residual > 0:
        weights = [(i, p) for i, (_, p) in enumerate(winners)]
        hc = _ration(weights, residual)
        for i, (pk, _) in enumerate(winners):
            h = hc.get(i, 0)
            if h:
                new[pk] = replace(new[pk], collateral_e8=new[pk].collateral_e8 - h)

    # Close liquidated positions; ADL the opposite side to restore Sigma position = 0.
    net_liq = sum(new[pk].position_base for pk in L)
    for pk in L:
        new[pk] = replace(new[pk], position_base=0, entry_price_e8=0)

    if net_liq != 0:
        want_short_side = net_liq > 0   # net long closed -> deleverage shorts
        candidates = [pk for pk, a in new.items()
                      if pk not in L and a.position_base != 0
                      and (a.position_base < 0) == want_short_side]
        candidates.sort(key=lambda pk: (-pnl_map.get(pk, 0), pk))
        remaining = abs(net_liq)
        step = 1 if net_liq > 0 else -1   # add toward 0 for shorts; subtract for longs
        for pk in candidates:
            if remaining == 0:
                break
            a = new[pk]
            take = min(abs(a.position_base), remaining)
            new_pos = a.position_base + step * take
            new[pk] = replace(a, position_base=new_pos,
                              entry_price_e8=s if new_pos != 0 else 0)
            remaining -= take
        if remaining != 0:  # guaranteed unreachable by Sigma position = 0 before close
            raise AssertionError("ADL could not rebalance — net-zero precondition violated")

    return new, fee_pool, insurance, claims_paid


# --- Full epoch in the SAFE order (settle then match) --------------------------
def run_epoch(state: MarketState, clearing_price_e8: int, funding_rate_bps: int,
              intents: Sequence[Intent]) -> tuple[MarketState, MatchResult]:
    """One epoch in the order a cross-model review (Gemini/Agy) showed is necessary to avoid a
    'free look': settle the EXISTING book at the newly published price FIRST (MTM -> funding ->
    liquidation/ADL), THEN match the new intents at the freshly-settled mark.

    Because new entrants fill at the current price `s` (entering with zero mark-to-market PnL for
    the epoch), a faster actor cannot match at a stale prior mark and harvest the about-to-be-
    published move. Matching at `s` also preserves the exact zero-sum property: the next epoch marks
    every position (old survivors re-marked to `s`, new entrants entered at `s`) from the common
    mark `s`. The reverse order (match-then-settle) is the free-look-vulnerable sequence."""
    settled = apply_settle(state, clearing_price_e8, funding_rate_bps)   # old book marked at s; index->s
    return apply_match(settled, intents)                                 # new intents matched at s


# --- Invariant checkers --------------------------------------------------------
def net_position(state: MarketState) -> int:
    return sum(a.position_base for a in state.accounts)


def total_collateral_e8(state: MarketState) -> int:
    return sum(a.collateral_e8 for a in state.accounts)


def check_invariants(state: MarketState, *, require_margin: bool = True) -> list[str]:
    """Return a list of invariant violations (empty == all hold)."""
    v: list[str] = []
    p = state.params

    # (I) net-zero positions
    if net_position(state) != 0:
        v.append(f"(I) net position {net_position(state)} != 0")

    # (II'') combined value conservation: D + I_ext == Sigma collateral + F + I
    lhs = state.net_deposited_e8 + state.insurance_ext_e8
    rhs = total_collateral_e8(state) + state.fee_pool_e8 + state.insurance_e8
    if lhs != rhs:
        v.append(f"(II) conservation {lhs} != {rhs}")

    # (IV) insurance ledger
    if state.insurance_e8 != state.insurance_ext_e8 - state.claims_paid_e8:
        v.append("(IV) insurance != I_ext - claims_paid")
    if state.insurance_e8 < 0:
        v.append("(IV) insurance balance negative")

    # collateral non-negative
    for a in state.accounts:
        if a.collateral_e8 < 0:
            v.append(f"(coll>=0) {a.pubkey} collateral {a.collateral_e8} < 0")

    # (III) solvency
    solv = sum(min(a.collateral_e8, 0) for a in state.accounts) + state.insurance_e8 + state.fee_pool_e8
    if solv < 0:
        v.append(f"(III) solvency {solv} < 0")

    # (V) maintenance margin for open positions (post-settle)
    if require_margin:
        for a in state.accounts:
            if a.position_base != 0:
                req = maint_req_e8(a.position_base, state.index_price_e8,
                                   p.maintenance_margin_bps, p.depeg_buffer_bps)
                if a.collateral_e8 < req:
                    v.append(f"(V) {a.pubkey} below maintenance: {a.collateral_e8} < {req}")
            # (VI) position bound
            if abs(a.position_base) > p.max_position_abs:
                v.append(f"(VI) {a.pubkey} position {a.position_base} exceeds bound")
            # entry-matches-mark when open
            if a.position_base != 0 and a.entry_price_e8 != state.index_price_e8:
                v.append(f"(entry) {a.pubkey} entry {a.entry_price_e8} != mark {state.index_price_e8}")

    return v
