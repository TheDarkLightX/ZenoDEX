#!/usr/bin/env python3
"""Research-only net-zero batch matcher for the N-party perps clearinghouse.

EXPERIMENTAL / PENDING REVIEW — public testnet (fake value) design evidence only.
This module is available only behind an explicit non-production engine
capability and is physically excluded from production artifacts.

Single source of truth for matcher semantics (DESIGN.md sections 4.4 / 4.4b). The
Rust/Kani crate mirrors ``ration_net_zero`` / ``_ration``; the Lean proofs abstract
the net-zero property (``Sum delta = 0``).

Design rules followed (CBC core style):
  - pure functions, immutable inputs, explicit outputs;
  - checked integer arithmetic only (no floats anywhere);
  - stable reject codes; reject-is-no-op (a rejected intent never mutates state);
  - deterministic: canonical pubkey order + largest-remainder tie-break by index.

The matcher decides QUANTITY only. All fills execute at the published clearing
price (no price discovery). Funding, mark-to-market, liquidation and ADL live in
``perp_np_core.py``.
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from typing import Mapping, Sequence

# --- Stable reject codes (consensus behaviour; tested for precedence) ----------
REJ_EXPIRED = "REJ_EXPIRED"          # expiry_epoch < now_epoch
REJ_BAD_NONCE = "REJ_BAD_NONCE"      # nonce not strictly above the account's last
REJ_SUPERSEDED = "REJ_SUPERSEDED"    # another intent from the same account has a higher valid nonce
REJ_DUP_NONCE = "REJ_DUP_NONCE"      # >1 intent from the same account shares a nonce (operator could pick)
REJ_POS_BOUND = "REJ_POS_BOUND"      # |target_base| > max_position_abs
REJ_MARGIN = "REJ_MARGIN"            # intended target fails initial margin given collateral
REJ_PRICE = "REJ_PRICE"              # clearing price outside the intent's limit
REJ_OVERFLOW = "REJ_OVERFLOW"        # an operand exceeds the documented i128-safe bound
REJ_INVARIANT = "REJ_INVARIANT"      # post-match invariant violation (should be unreachable)

# Documented arithmetic bound for parity with the Rust i128 port. Notional and
# margin products must stay within this; anything larger is rejected, not wrapped.
I128_MAX = (1 << 127) - 1

E8 = 100_000_000          # price scale (quote-per-base * 1e8)
BPS_SCALE = 10_000        # basis-point scale


def _require_plain_int(value: object, *, name: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise TypeError(f"{name} must be an int")
    return int(value)


def _account_int(table: Mapping[str, int], pubkey: str, default: int, *, name: str) -> int:
    value = table.get(pubkey, default)
    return _require_plain_int(value, name=f"{name}[{pubkey}]")


# --- Pure focal functions (mirrored 1:1 by the Rust/Kani crate) ----------------
def _ration(weights: Sequence[tuple[int, int]], volume: int) -> dict[int, int]:
    """Distribute ``volume`` units across weighted claimants by largest remainder.

    ``weights`` is a list of ``(index, w)`` with ``w > 0`` and ``H = sum(w) >= volume >= 0``.
    Returns ``{index: alloc}`` with ``sum(alloc) == volume`` and ``0 <= alloc <= w``.

    Floor each share, then hand the leftover units one-each to the largest
    remainders, breaking ties by ascending index (the index encodes canonical
    pubkey order, so the result is identical on every node).
    """
    total = 0
    for _, w in weights:
        if w <= 0:
            raise ValueError("ration weights must be positive")
        total += w
    if total == 0:
        return {}
    if volume < 0 or volume > total:
        raise ValueError("volume must satisfy 0 <= volume <= sum(weights)")

    base: dict[int, int] = {}
    remainders: list[tuple[int, int]] = []  # (remainder_numerator, index)
    allocated = 0
    for idx, w in weights:
        # base = floor(w * volume / total); rem = w*volume - base*total in [0, total)
        prod = w * volume
        if prod > I128_MAX:
            raise OverflowError("ration product exceeds i128 bound")
        b = prod // total
        base[idx] = b
        allocated += b
        remainders.append((prod - b * total, idx))

    leftover = volume - allocated  # 0 <= leftover < len(weights)
    if leftover:
        # Largest remainder first; ascending index breaks ties deterministically.
        remainders.sort(key=lambda t: (-t[0], t[1]))
        for k in range(leftover):
            base[remainders[k][1]] += 1
    return base


def ration_net_zero(desired: Sequence[int]) -> list[int]:
    """Match desired position deltas into executed deltas with ``sum == 0`` exactly.

    Buyers (``d > 0``) are matched against sellers (``d < 0``) up to the smaller
    side's total volume ``V = min(buy_total, sell_total)``; the lighter side fills
    fully and the heavier side is rationed (largest remainder). Each executed
    ``delta[i]`` keeps the sign of ``desired[i]`` and ``|delta[i]| <= |desired[i]|``.
    """
    buys = [(i, d) for i, d in enumerate(desired) if d > 0]
    sells = [(i, -d) for i, d in enumerate(desired) if d < 0]
    buy_total = sum(w for _, w in buys)
    sell_total = sum(w for _, w in sells)
    volume = min(buy_total, sell_total)

    out = [0] * len(desired)
    if volume == 0:
        return out
    for idx, alloc in _ration(buys, volume).items():
        out[idx] = alloc
    for idx, alloc in _ration(sells, volume).items():
        out[idx] = -alloc
    return out


# --- Margin helper -------------------------------------------------------------
def initial_margin_req_e8(target_base: int, price_e8: int, initial_margin_bps: int) -> int:
    """Initial-margin requirement (quote-e8) to hold ``target_base`` at ``price_e8``.

    On the e8 ledger collateral is ``quote * 1e8`` and notional is ``|target| * price_e8``
    (already quote-e8 — no division by E8), so the requirement is
    ``ceil(|target| * price_e8 * initial_margin_bps / 1e4)``.
    Plain English: the up-front collateral a position of this size must post.
    """
    notional_e8 = abs(target_base) * price_e8
    num = notional_e8 * initial_margin_bps
    if num > I128_MAX:
        raise OverflowError("margin product exceeds i128 bound")
    return (num + BPS_SCALE - 1) // BPS_SCALE


# --- Intent + result types -----------------------------------------------------
@dataclass(frozen=True)
class Intent:
    """A single-signed position intent. ``limit_price_e8 == 0`` => no price gate."""

    pubkey: str
    target_base: int
    limit_price_e8: int = 0
    min_fill_base: int = 0
    expiry_epoch: int = 1 << 62
    nonce: int = 0


@dataclass(frozen=True)
class IntentReceipt:
    pubkey: str
    nonce: int
    status: str          # "filled" | "rejected"
    delta: int = 0       # executed signed delta (0 if unfilled/rejected)
    reject_code: str | None = None


@dataclass(frozen=True)
class MatchParams:
    initial_margin_bps: int
    max_position_abs: int

    def __post_init__(self) -> None:
        if not isinstance(self.initial_margin_bps, int) or isinstance(self.initial_margin_bps, bool):
            raise ValueError("initial_margin_bps must be an int")
        if not (0 < self.initial_margin_bps <= BPS_SCALE):
            raise ValueError("initial_margin_bps out of range")
        if not isinstance(self.max_position_abs, int) or isinstance(self.max_position_abs, bool):
            raise ValueError("max_position_abs must be an int")
        if self.max_position_abs <= 0:
            raise ValueError("max_position_abs out of range")


@dataclass(frozen=True)
class MatchResult:
    deltas: dict[str, int]               # pubkey -> executed signed delta (only non-trivial entries)
    receipts: tuple[IntentReceipt, ...]  # canonical (pubkey-sorted) order
    clearing_price_e8: int
    now_epoch: int

    @property
    def net(self) -> int:
        return sum(self.deltas.values())


ReceiptKey = tuple[str, int]
Survivor = tuple[Intent, int]


@dataclass(frozen=True)
class _MatchContext:
    current_positions: Mapping[str, int]
    collaterals: Mapping[str, int]
    last_nonces: Mapping[str, int]
    clearing_price_e8: int
    now_epoch: int
    params: MatchParams


@dataclass(frozen=True)
class _IntentValidationContext:
    current: int
    collateral: int
    last_nonce: int
    price_e8: int
    now_epoch: int
    params: MatchParams


@dataclass(frozen=True)
class _RationResult:
    deltas: Sequence[int]
    revoked: set[str]


# --- Full matcher pipeline (tested by pytest; not the Kani target) -------------
def match_intents(
    intents: Sequence[Intent],
    current_positions: Mapping[str, int],
    collaterals: Mapping[str, int],
    last_nonces: Mapping[str, int],
    clearing_price_e8: int,
    now_epoch: int,
    params: MatchParams,
) -> MatchResult:
    """Deterministic net-zero match of single-signed intents at the clearing price.

    Pipeline (DESIGN.md 4.4b): canonical order -> per-intent validation ->
    price gate -> ration_net_zero -> min-fill revocation -> overflow/post-match
    re-check. Every rejection is a stable code; rejected intents do not move state.
    Output ``net`` is exactly 0.
    """
    price_e8 = _require_plain_int(clearing_price_e8, name="clearing_price_e8")
    epoch = _require_plain_int(now_epoch, name="now_epoch")
    if price_e8 <= 0:
        raise ValueError("clearing_price_e8 must be positive")

    ctx = _MatchContext(
        current_positions=current_positions,
        collaterals=collaterals,
        last_nonces=last_nonces,
        clearing_price_e8=price_e8,
        now_epoch=epoch,
        params=params,
    )
    survivors, receipts = _select_survivors_by_account(intents=intents, ctx=ctx)
    rationed = _apply_min_fill_revocation(survivors=survivors)
    out_deltas = _finalize_match_receipts(
        ctx=ctx,
        survivors=survivors,
        rationed=rationed,
        receipts=receipts,
    )

    ordered_receipts = tuple(receipts[k] for k in sorted(receipts))
    result = MatchResult(out_deltas, ordered_receipts, clearing_price_e8, now_epoch)
    if result.net != 0:  # defence in depth; ration_net_zero guarantees this
        raise AssertionError("matcher produced non-zero net")
    return result


def _group_intents_by_pubkey(intents: Sequence[Intent]) -> dict[str, list[Intent]]:
    ordered = sorted(intents, key=lambda it: (it.pubkey, it.nonce))
    by_pubkey: dict[str, list[Intent]] = {}
    for it in ordered:
        by_pubkey.setdefault(it.pubkey, []).append(it)
    return by_pubkey


def _nonce_counts(intents: Sequence[Intent]) -> dict[int, int]:
    counts: dict[int, int] = {}
    for it in intents:
        counts[it.nonce] = counts.get(it.nonce, 0) + 1
    return counts


def _select_survivors_by_account(
    *,
    intents: Sequence[Intent],
    ctx: _MatchContext,
) -> tuple[list[Survivor], dict[ReceiptKey, IntentReceipt]]:
    # Per account, the HIGHEST-NONCE valid intent wins. Invalid higher-nonce
    # intents keep their own reject code and do not cancel lower valid intents.
    by_pubkey = _group_intents_by_pubkey(intents)
    receipts: dict[ReceiptKey, IntentReceipt] = {}
    survivors: list[Survivor] = []
    for pubkey in sorted(by_pubkey):
        chosen = _select_account_survivor(
            pubkey=pubkey,
            account_intents=by_pubkey[pubkey],
            ctx=ctx,
            receipts=receipts,
        )
        if chosen is not None:
            survivors.append(chosen)
    return survivors, receipts


def _select_account_survivor(
    *,
    pubkey: str,
    account_intents: Sequence[Intent],
    ctx: _MatchContext,
    receipts: dict[ReceiptKey, IntentReceipt],
) -> Survivor | None:
    cur = _account_int(ctx.current_positions, pubkey, 0, name="current_positions")
    coll = _account_int(ctx.collaterals, pubkey, 0, name="collaterals")
    last_nonce = _account_int(ctx.last_nonces, pubkey, -1, name="last_nonces")
    validation = _IntentValidationContext(
        current=cur,
        collateral=coll,
        last_nonce=last_nonce,
        price_e8=ctx.clearing_price_e8,
        now_epoch=ctx.now_epoch,
        params=ctx.params,
    )
    nonce_counts = _nonce_counts(account_intents)
    chosen_it: Intent | None = None
    for it in account_intents:  # ascending nonce
        if nonce_counts[it.nonce] > 1:
            receipts[_rkey(it)] = IntentReceipt(
                it.pubkey,
                it.nonce,
                "rejected",
                reject_code=REJ_DUP_NONCE,
            )
            continue
        code = _validate_intent(it, validation)
        if code is not None:
            receipts[_rkey(it)] = IntentReceipt(it.pubkey, it.nonce, "rejected", reject_code=code)
            continue
        if chosen_it is not None:
            receipts[_rkey(chosen_it)] = IntentReceipt(
                chosen_it.pubkey,
                chosen_it.nonce,
                "rejected",
                reject_code=REJ_SUPERSEDED,
            )
        chosen_it = it
    if chosen_it is None:
        return None
    return chosen_it, chosen_it.target_base - cur


def _apply_min_fill_revocation(
    *, survivors: Sequence[Survivor]
) -> _RationResult:
    # Monotone loop: each pass can only add revoked pubkeys, so it terminates
    # after at most len(survivors) revocations.
    revoked: set[str] = set()
    while True:
        desired = [d if it.pubkey not in revoked else 0 for it, d in survivors]
        deltas = ration_net_zero(desired)
        newly_revoked = _collect_min_fill_revocations(
            survivors=survivors,
            deltas=deltas,
            revoked=revoked,
        )
        if not newly_revoked:
            return _RationResult(deltas=deltas, revoked=revoked)


def _collect_min_fill_revocations(
    *,
    survivors: Sequence[Survivor],
    deltas: Sequence[int],
    revoked: set[str],
) -> bool:
    newly_revoked = False
    for (it, _), delta in zip(survivors, deltas, strict=True):
        if it.pubkey in revoked:
            continue
        if 0 < abs(delta) < it.min_fill_base:
            revoked.add(it.pubkey)
            newly_revoked = True
    return newly_revoked


def _finalize_match_receipts(
    *,
    ctx: _MatchContext,
    survivors: Sequence[Survivor],
    rationed: _RationResult,
    receipts: dict[ReceiptKey, IntentReceipt],
) -> dict[str, int]:
    out_deltas: dict[str, int] = {}
    for (it, _d), delta in zip(survivors, rationed.deltas, strict=True):
        if it.pubkey in rationed.revoked:
            receipts[_rkey(it)] = IntentReceipt(it.pubkey, it.nonce, "filled", delta=0)
            continue
        cur_pos = _account_int(ctx.current_positions, it.pubkey, 0, name="current_positions")
        new_pos = cur_pos + delta
        coll = _account_int(ctx.collaterals, it.pubkey, 0, name="collaterals")
        # Only RISK-INCREASING fills (grow same-side exposure or cross zero to the other side)
        # must satisfy initial margin. A pure same-side reduction never needs more margin than
        # already legally held, so it must NOT be dropped -- dropping it would unpair its
        # counterparty and break net-zero. For risk-increasing fills |delta| <= |desired| and the
        # target already passed validation, so this branch is unreachable -> fail-closed if it fires.
        if (_increases_risk(cur_pos, new_pos)
                and coll < initial_margin_req_e8(
                    new_pos,
                    ctx.clearing_price_e8,
                    ctx.params.initial_margin_bps,
                )):
            receipts[_rkey(it)] = IntentReceipt(it.pubkey, it.nonce, "rejected",
                                                reject_code=REJ_INVARIANT)
            continue
        receipts[_rkey(it)] = IntentReceipt(it.pubkey, it.nonce, "filled", delta=delta)
        if delta != 0:
            out_deltas[it.pubkey] = delta
    return out_deltas


def _rkey(it: Intent) -> tuple[str, int]:
    return (it.pubkey, it.nonce)


def _increases_risk(current: int, target: int) -> bool:
    """True if moving from `current` to `target` takes on NEW directional risk that requires
    initial margin: either it grows same-side exposure (|target| > |current|) or it crosses zero
    to the opposite side (current * target < 0). A pure same-side reduction returns False."""
    return current * target < 0 or abs(target) > abs(current)


def _validate_intent_basic_rejects(it: Intent, ctx: _IntentValidationContext) -> str | None:
    if it.expiry_epoch < ctx.now_epoch:
        return REJ_EXPIRED
    if it.nonce <= ctx.last_nonce:
        return REJ_BAD_NONCE
    if abs(it.target_base) > ctx.params.max_position_abs:
        return REJ_POS_BOUND
    if abs(it.target_base) * ctx.price_e8 > I128_MAX:
        return REJ_OVERFLOW
    return None


def _validate_intent_initial_margin(it: Intent, ctx: _IntentValidationContext) -> str | None:
    if not _increases_risk(ctx.current, it.target_base):
        return None
    if ctx.collateral < initial_margin_req_e8(
        it.target_base,
        ctx.price_e8,
        ctx.params.initial_margin_bps,
    ):
        return REJ_MARGIN
    return None


def _limit_price_violated(*, desired: int, price_e8: int, limit_price_e8: int) -> bool:
    if desired > 0:
        return price_e8 > limit_price_e8  # buyer wants p_c <= limit
    return price_e8 < limit_price_e8  # seller wants p_c >= limit


def _validate_intent_limit_price(it: Intent, ctx: _IntentValidationContext) -> str | None:
    desired = it.target_base - ctx.current
    if it.limit_price_e8 == 0:
        return None
    if desired == 0:
        return None
    if _limit_price_violated(
        desired=desired,
        price_e8=ctx.price_e8,
        limit_price_e8=it.limit_price_e8,
    ):
        return REJ_PRICE
    return None


def _validate_intent(it: Intent, ctx: _IntentValidationContext) -> str | None:
    """Return a reject code, or None if the intent may participate. Precedence order
    matches the listing (expiry -> nonce -> bound -> overflow -> margin -> price)."""
    # Initial-margin gate applies whenever the target takes on NEW directional risk: either it
    # grows the same-side exposure (|target| > |current|) OR it CROSSES ZERO to the other side
    # (current * target < 0) -- a flip like long 10 -> short 9 is new short risk, not de-risking,
    # so it must post initial margin (cross-model review caught this zero-crossing bypass). A pure
    # same-side reduction (|target| <= |current|, no sign flip) is always allowed.
    for check in (
        _validate_intent_basic_rejects,
        _validate_intent_initial_margin,
        _validate_intent_limit_price,
    ):
        code = check(it, ctx)
        if code is not None:
            return code
    return None


# --- Deterministic self-test CLI ----------------------------------------------
def _selftest() -> dict:
    try:
        from src.nonproduction.perp_np_matching_selftest import run_perp_np_matching_selftest
    except ModuleNotFoundError as exc:
        if exc.name != "src":
            raise
        from pathlib import Path

        sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
        from src.nonproduction.perp_np_matching_selftest import run_perp_np_matching_selftest

    return run_perp_np_matching_selftest()


def main(argv: Sequence[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description="Pure net-zero perps matcher self-test.")
    ap.add_argument("--test", action="store_true", help="run the deterministic self-test")
    ap.add_argument("--json", action="store_true", help="emit JSON to stdout")
    args = ap.parse_args(argv)

    if not args.test:
        ap.print_help(file=sys.stderr)
        return 2

    result = _selftest()
    if args.json:
        print(json.dumps(result))
    else:
        status = "PASS" if result["ok"] else "FAIL"
        print(f"[{status}] checked={result['checked']} failures={len(result['failures'])}",
              file=sys.stderr)
        for f in result["failures"][:20]:
            print(f"  - {f}", file=sys.stderr)
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
