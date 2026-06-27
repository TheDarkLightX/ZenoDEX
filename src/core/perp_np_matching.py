#!/usr/bin/env python3
"""Pure deterministic net-zero batch matcher for the N-party perps clearinghouse.

EXPERIMENTAL / PENDING REVIEW — public testnet (fake value) design evidence only.
This module is NOT wired into any consensus path. See README.md and DESIGN.md.

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
from typing import Iterable, Mapping, Sequence

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


@dataclass(frozen=True)
class MatchResult:
    deltas: dict[str, int]               # pubkey -> executed signed delta (only non-trivial entries)
    receipts: tuple[IntentReceipt, ...]  # canonical (pubkey-sorted) order
    clearing_price_e8: int
    now_epoch: int

    @property
    def net(self) -> int:
        return sum(self.deltas.values())


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
    if clearing_price_e8 <= 0:
        raise ValueError("clearing_price_e8 must be positive")

    receipts: dict[str, IntentReceipt] = {}

    # 1) Canonical order: sort by pubkey bytes, then nonce (highest last so it wins).
    ordered = sorted(intents, key=lambda it: (it.pubkey, it.nonce))

    # 2+3) Per account, the HIGHEST-NONCE *VALID* intent wins. Each account's intents are
    #     validated first (ascending nonce); an invalid higher-nonce intent gets its OWN
    #     reject code (REJ_EXPIRED/REJ_BAD_NONCE/REJ_MARGIN/...) and must NOT cancel a valid
    #     lower-nonce intent. A valid intent that loses to a higher valid one is SUPERSEDED.
    by_pubkey: dict[str, list[Intent]] = {}
    for it in ordered:
        by_pubkey.setdefault(it.pubkey, []).append(it)

    survivors: list[tuple[Intent, int]] = []  # (intent, desired_delta)
    for pk in sorted(by_pubkey):
        cur = int(current_positions.get(pk, 0))
        coll = int(collaterals.get(pk, 0))
        last_nonce = int(last_nonces.get(pk, -1))
        # Reject ALL intents sharing a nonce within this batch: otherwise the operator could
        # choose which same-nonce intent executes by ordering them (front-running / discretion).
        nonce_counts: dict[int, int] = {}
        for it in by_pubkey[pk]:
            nonce_counts[it.nonce] = nonce_counts.get(it.nonce, 0) + 1
        chosen_it: Intent | None = None
        for it in by_pubkey[pk]:  # ascending nonce
            if nonce_counts[it.nonce] > 1:
                receipts[_rkey(it)] = IntentReceipt(it.pubkey, it.nonce, "rejected",
                                                    reject_code=REJ_DUP_NONCE)
                continue
            code = _validate_intent(it, cur, coll, last_nonce, clearing_price_e8, now_epoch, params)
            if code is not None:
                receipts[_rkey(it)] = IntentReceipt(it.pubkey, it.nonce, "rejected", reject_code=code)
                continue
            if chosen_it is not None:  # a valid lower-nonce intent is superseded by this one
                receipts[_rkey(chosen_it)] = IntentReceipt(chosen_it.pubkey, chosen_it.nonce,
                                                           "rejected", reject_code=REJ_SUPERSEDED)
            chosen_it = it
        if chosen_it is not None:
            survivors.append((chosen_it, chosen_it.target_base - cur))

    # 4) ration_net_zero + 5) min-fill revocation loop (monotone -> terminates).
    revoked: set[str] = set()
    while True:
        desired = [d if it.pubkey not in revoked else 0 for it, d in survivors]
        deltas = ration_net_zero(desired)
        newly_revoked = False
        for (it, _), delta in zip(survivors, deltas):
            if it.pubkey in revoked:
                continue
            if 0 < abs(delta) < it.min_fill_base:
                revoked.add(it.pubkey)
                newly_revoked = True
        if not newly_revoked:
            break

    # 6/7) Overflow + post-match invariant re-check; build receipts.
    out_deltas: dict[str, int] = {}
    for (it, d), delta in zip(survivors, deltas):
        if it.pubkey in revoked:
            receipts[_rkey(it)] = IntentReceipt(it.pubkey, it.nonce, "filled", delta=0)
            continue
        cur_pos = int(current_positions.get(it.pubkey, 0))
        new_pos = cur_pos + delta
        coll = int(collaterals.get(it.pubkey, 0))
        # Only RISK-INCREASING fills (grow same-side exposure or cross zero to the other side)
        # must satisfy initial margin. A pure same-side reduction never needs more margin than
        # already legally held, so it must NOT be dropped -- dropping it would unpair its
        # counterparty and break net-zero. For risk-increasing fills |delta| <= |desired| and the
        # target already passed validation, so this branch is unreachable -> fail-closed if it fires.
        if (_increases_risk(cur_pos, new_pos)
                and coll < initial_margin_req_e8(new_pos, clearing_price_e8, params.initial_margin_bps)):
            receipts[_rkey(it)] = IntentReceipt(it.pubkey, it.nonce, "rejected",
                                                reject_code=REJ_INVARIANT)
            continue
        receipts[_rkey(it)] = IntentReceipt(it.pubkey, it.nonce, "filled", delta=delta)
        if delta != 0:
            out_deltas[it.pubkey] = delta

    ordered_receipts = tuple(receipts[k] for k in sorted(receipts))
    result = MatchResult(out_deltas, ordered_receipts, clearing_price_e8, now_epoch)
    if result.net != 0:  # defence in depth; ration_net_zero guarantees this
        raise AssertionError("matcher produced non-zero net")
    return result


def _rkey(it: Intent) -> tuple[str, int]:
    return (it.pubkey, it.nonce)


def _increases_risk(current: int, target: int) -> bool:
    """True if moving from `current` to `target` takes on NEW directional risk that requires
    initial margin: either it grows same-side exposure (|target| > |current|) or it crosses zero
    to the opposite side (current * target < 0). A pure same-side reduction returns False."""
    return current * target < 0 or abs(target) > abs(current)


def _validate_intent(
    it: Intent,
    current: int,
    collateral: int,
    last_nonce: int,
    price_e8: int,
    now_epoch: int,
    params: MatchParams,
) -> str | None:
    """Return a reject code, or None if the intent may participate. Precedence order
    matches the listing (expiry -> nonce -> bound -> overflow -> margin -> price)."""
    if it.expiry_epoch < now_epoch:
        return REJ_EXPIRED
    if it.nonce <= last_nonce:
        return REJ_BAD_NONCE
    if abs(it.target_base) > params.max_position_abs:
        return REJ_POS_BOUND
    if abs(it.target_base) * price_e8 > I128_MAX:
        return REJ_OVERFLOW
    # Initial-margin gate applies whenever the target takes on NEW directional risk: either it
    # grows the same-side exposure (|target| > |current|) OR it CROSSES ZERO to the other side
    # (current * target < 0) -- a flip like long 10 -> short 9 is new short risk, not de-risking,
    # so it must post initial margin (cross-model review caught this zero-crossing bypass). A pure
    # same-side reduction (|target| <= |current|, no sign flip) is always allowed.
    if (_increases_risk(current, it.target_base)
            and collateral < initial_margin_req_e8(it.target_base, price_e8, params.initial_margin_bps)):
        return REJ_MARGIN
    desired = it.target_base - current
    if it.limit_price_e8 != 0 and desired != 0:
        if desired > 0 and price_e8 > it.limit_price_e8:   # buyer wants p_c <= limit
            return REJ_PRICE
        if desired < 0 and price_e8 < it.limit_price_e8:   # seller wants p_c >= limit
            return REJ_PRICE
    return None


# --- Deterministic self-test CLI ----------------------------------------------
def _selftest_ration_cases() -> Iterable[list[int]]:
    """Yield a replay-stable ration corpus without importing an RNG in core code."""
    for case in (
        [],
        [0, 0],
        [5, -5],
        [1, 1, 1, -2],     # classic remainder case: buys 3 vs sell 2
        [3, -1, -1, -1],
        [7, -3, -4],
        [100, -1, -1, -1, -1],
        [-10, 4, 4, 4],
        [1000000, -999999, -1],
        [2, 2, 2, -3],     # heavy buys 6 vs sell 3 -> ration to (1,1,1)
    ):
        yield list(case)

    # Arithmetic mixer over all allowed lengths. This replaces the former fixed
    # seed RNG corpus while keeping broad sign, zero, tie, and imbalance coverage.
    for n in range(9):
        for seed in range(2048):
            desired: list[int] = []
            for idx in range(n):
                mixed = seed * 37 + idx * 17 + n * 11 + (seed >> (idx % 5))
                value = mixed % 101 - 50
                if (seed + 3 * idx + n) % 23 == 0:
                    value = 0
                desired.append(value)
            yield desired


def _selftest() -> dict:
    """Deterministic battery: assert net-zero, sign-consistency, |delta|<=|desired|."""
    failures: list[str] = []
    checked = 0

    def check_ration(desired: list[int]) -> None:
        nonlocal checked
        out = ration_net_zero(desired)
        checked += 1
        if sum(out) != 0:
            failures.append(f"net!=0 for {desired} -> {out}")
        for d, o in zip(desired, out):
            if d >= 0 and not (0 <= o <= d):
                failures.append(f"sign/bound for d={d} o={o}")
            if d < 0 and not (d <= o <= 0):
                failures.append(f"sign/bound for d={d} o={o}")
        # matched volume == min(buy,sell)
        b = sum(d for d in desired if d > 0)
        s = -sum(d for d in desired if d < 0)
        if sum(o for o in out if o > 0) != min(b, s):
            failures.append(f"volume mismatch for {desired}")

    for desired in _selftest_ration_cases():
        check_ration(desired)

    # End-to-end match_intents: net-zero + min-fill respected.
    params = MatchParams(initial_margin_bps=1000, max_position_abs=1_000_000)
    price = 100 * E8
    intents = [
        Intent("aa", target_base=10, min_fill_base=0, nonce=1),
        Intent("bb", target_base=-3, min_fill_base=0, nonce=1),
        Intent("cc", target_base=-3, min_fill_base=5, nonce=1),  # only 3-ish available -> revoked
    ]
    colls = {"aa": 10 * params.initial_margin_bps * price // BPS_SCALE // E8 * E8 + 10**18,
             "bb": 10**18, "cc": 10**18}
    res = match_intents(intents, {}, colls, {}, price, now_epoch=1, params=params)
    checked += 1
    if res.net != 0:
        failures.append("match_intents net!=0")
    for r in res.receipts:
        if r.status == "filled" and 0 < abs(r.delta) < _min_fill(intents, r.pubkey):
            failures.append(f"min-fill violated for {r.pubkey}: {r.delta}")

    return {"ok": not failures, "checked": checked, "failures": failures}


def _min_fill(intents: Sequence[Intent], pubkey: str) -> int:
    for it in intents:
        if it.pubkey == pubkey:
            return it.min_fill_base
    return 0


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
