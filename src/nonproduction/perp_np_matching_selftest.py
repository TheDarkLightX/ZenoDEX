"""Research-only deterministic self-tests for the N-party perps matcher."""

from __future__ import annotations

from typing import Sequence

from src.nonproduction.perp_np_matching import (
    BPS_SCALE,
    E8,
    Intent,
    MatchParams,
    match_intents,
    ration_net_zero,
)


def run_perp_np_matching_selftest() -> dict:
    """Deterministic battery: assert net-zero, sign-consistency, |delta|<=|desired|."""
    ration_checked, failures = _run_ration_selftest()
    match_failures = _run_match_intents_selftest()
    failures.extend(match_failures)
    checked = ration_checked + 1
    return {"ok": not failures, "checked": checked, "failures": failures}


def _run_ration_selftest() -> tuple[int, list[str]]:
    failures: list[str] = []
    checked = 0
    for handpicked in _handpicked_ration_cases():
        failures.extend(_check_ration_case(handpicked))
        checked += 1
    for generated in _deterministic_ration_cases(case_count=20000):
        failures.extend(_check_ration_case(generated))
        checked += 1
    return checked, failures


def _handpicked_ration_cases() -> tuple[tuple[int, ...], ...]:
    return (
        (),
        (0, 0),
        (5, -5),
        (1, 1, 1, -2),  # classic remainder case: buys 3 vs sell 2
        (3, -1, -1, -1),
        (7, -3, -4),
        (100, -1, -1, -1, -1),
        (-10, 4, 4, 4),
        (1000000, -999999, -1),
        (2, 2, 2, -3),  # heavy buys 6 vs sell 3 -> ration to (1,1,1)
    )


def _next_deterministic_int(*, state: int, lo: int, hi: int) -> tuple[int, int]:
    if lo > hi:
        raise ValueError("lo must be <= hi")
    next_state = (6364136223846793005 * state + 1442695040888963407) % (1 << 64)
    return next_state, lo + (next_state % (hi - lo + 1))


def _deterministic_ration_cases(*, case_count: int) -> list[list[int]]:
    cases: list[list[int]] = []
    stream_state = 20260601
    for _ in range(case_count):
        stream_state, n = _next_deterministic_int(state=stream_state, lo=0, hi=8)
        desired: list[int] = []
        for _ in range(n):
            stream_state, value = _next_deterministic_int(
                state=stream_state,
                lo=-50,
                hi=50,
            )
            desired.append(value)
        cases.append(desired)
    return cases


def _check_ration_case(desired: Sequence[int]) -> list[str]:
    failures: list[str] = []
    out = ration_net_zero(desired)
    if sum(out) != 0:
        failures.append(f"net!=0 for {desired} -> {out}")
    for d, o in zip(desired, out, strict=True):
        if d >= 0 and not (0 <= o <= d):
            failures.append(f"sign/bound for d={d} o={o}")
        if d < 0 and not (d <= o <= 0):
            failures.append(f"sign/bound for d={d} o={o}")
    buy_volume = sum(d for d in desired if d > 0)
    sell_volume = -sum(d for d in desired if d < 0)
    if sum(o for o in out if o > 0) != min(buy_volume, sell_volume):
        failures.append(f"volume mismatch for {desired}")
    return failures


def _run_match_intents_selftest() -> list[str]:
    failures: list[str] = []
    params = MatchParams(initial_margin_bps=1000, max_position_abs=1_000_000)
    price = 100 * E8
    intents = [
        Intent("aa", target_base=10, min_fill_base=0, nonce=1),
        Intent("bb", target_base=-3, min_fill_base=0, nonce=1),
        Intent("cc", target_base=-3, min_fill_base=5, nonce=1),  # only 3-ish available -> revoked
    ]
    colls = {
        "aa": 10 * params.initial_margin_bps * price // BPS_SCALE // E8 * E8 + 10**18,
        "bb": 10**18,
        "cc": 10**18,
    }
    res = match_intents(intents, {}, colls, {}, price, now_epoch=1, params=params)
    if res.net != 0:
        failures.append("match_intents net!=0")
    for r in res.receipts:
        if r.status == "filled" and 0 < abs(r.delta) < _min_fill(intents, r.pubkey):
            failures.append(f"min-fill violated for {r.pubkey}: {r.delta}")
    return failures


def _min_fill(intents: Sequence[Intent], pubkey: str) -> int:
    for it in intents:
        if it.pubkey == pubkey:
            return it.min_fill_base
    return 0
