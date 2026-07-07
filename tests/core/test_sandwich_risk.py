from __future__ import annotations

import random

import pytest

from src.core import sandwich_risk as sandwich_risk_module
from src.core.cpmm import swap_exact_in
from src.core.sandwich_risk import (
    SandwichRisk,
    attacker_amount_in_cutoff_upper_bound_cpmm_exact_in,
    max_sandwich_profit_exact_in_cpmm_bounded,
    max_sandwich_profit_exact_in_cpmm_front_output_quotient_bounded,
    sandwich_profit_exact_in_cpmm,
)


def _reference_max_profit(
    *,
    reserve_in: int,
    reserve_out: int,
    fee_bps: int,
    victim_amount_in: int,
    victim_min_out: int,
    cap: int,
) -> tuple[int, bool]:
    best = 0
    victim_executes_at_cap = False
    for a in range(0, cap + 1):
        p = sandwich_profit_exact_in_cpmm(
            reserve_in=reserve_in,
            reserve_out=reserve_out,
            fee_bps=fee_bps,
            victim_amount_in=victim_amount_in,
            victim_min_out=victim_min_out,
            attacker_amount_in=a,
        )
        if p is None:
            continue
        if a == cap:
            victim_executes_at_cap = True
        if p > best:
            best = int(p)
    return int(best), bool(victim_executes_at_cap)


def test_known_profitable_sandwich_case_is_detected() -> None:
    # Empirically-mined small witness:
    # x=y=1000, fee=0, victim_in=50, min_out=46 => max profit 1 at attacker_in ~18.
    res: SandwichRisk = max_sandwich_profit_exact_in_cpmm_bounded(
        reserve_in=1000,
        reserve_out=1000,
        fee_bps=0,
        victim_amount_in=50,
        victim_min_out=46,
        max_attacker_amount_in=2000,
    )
    assert res.status == "ok"
    assert res.max_profit == 1
    assert 0 < res.attacker_amount_in <= res.scanned_max_attacker_amount_in


def test_integer_rounding_requires_interior_sandwich_scan() -> None:
    # Minimized fee-free counterexample to a boundary-only shortcut:
    # the largest feasible attacker input is 3 with profit 0, while a=2 profits 1.
    fee_free = max_sandwich_profit_exact_in_cpmm_bounded(
        reserve_in=4,
        reserve_out=4,
        fee_bps=0,
        victim_amount_in=4,
        victim_min_out=1,
        max_attacker_amount_in=20,
    )
    assert fee_free.status == "ok"
    assert fee_free.max_profit == 1
    assert fee_free.attacker_amount_in == 2

    # The same failure mode survives positive fees; floors make profit a step
    # function, so the feasible boundary is not enough to certify the optimum.
    fee_positive = max_sandwich_profit_exact_in_cpmm_bounded(
        reserve_in=5,
        reserve_out=5,
        fee_bps=30,
        victim_amount_in=8,
        victim_min_out=1,
        max_attacker_amount_in=30,
    )
    assert fee_positive.status == "ok"
    assert fee_positive.max_profit == 1
    assert fee_positive.attacker_amount_in == 5


def test_front_output_quotient_matches_exhaustive_sandwich_scan_witnesses() -> None:
    for reserve, victim_in, fee_bps, min_out, cap in (
        (4, 4, 0, 1, 20),
        (5, 8, 30, 1, 30),
        (1000, 50, 0, 46, 2000),
    ):
        exhaustive = max_sandwich_profit_exact_in_cpmm_bounded(
            reserve_in=reserve,
            reserve_out=reserve,
            fee_bps=fee_bps,
            victim_amount_in=victim_in,
            victim_min_out=min_out,
            max_attacker_amount_in=cap,
        )
        quotient = max_sandwich_profit_exact_in_cpmm_front_output_quotient_bounded(
            reserve_in=reserve,
            reserve_out=reserve,
            fee_bps=fee_bps,
            victim_amount_in=victim_in,
            victim_min_out=min_out,
            max_attacker_amount_in=cap,
        )
        assert quotient == exhaustive


def test_front_output_quotient_falls_back_when_output_atoms_are_expensive(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def reject_representative_lookup(**_: object) -> int:
        raise AssertionError("quotient representative lookup should not run")

    monkeypatch.setattr(
        sandwich_risk_module,
        "_first_attacker_amount_in_for_front_output_atom",
        reject_representative_lookup,
    )
    exhaustive = max_sandwich_profit_exact_in_cpmm_bounded(
        reserve_in=2,
        reserve_out=1000,
        fee_bps=0,
        victim_amount_in=1,
        victim_min_out=1,
        max_attacker_amount_in=50,
    )
    quotient = max_sandwich_profit_exact_in_cpmm_front_output_quotient_bounded(
        reserve_in=2,
        reserve_out=1000,
        fee_bps=0,
        victim_amount_in=1,
        victim_min_out=1,
        max_attacker_amount_in=50,
    )
    assert quotient == exhaustive


def test_bounded_search_matches_reference_scan() -> None:
    rng = random.Random(7)
    for _ in range(200):
        reserve_in = rng.randint(100, 3000)
        reserve_out = rng.randint(100, 3000)
        fee_bps = rng.randint(0, 300)
        victim_amount_in = rng.randint(1, max(1, reserve_in // 3))

        try:
            victim_out_iso, _ = swap_exact_in(reserve_in, reserve_out, victim_amount_in, fee_bps)
        except Exception:
            continue

        # Keep min_out moderately tight so the feasible attacker range is unlikely to exceed the cap.
        slip_bps = rng.choice([0, 10, 50, 100, 200, 500])
        victim_min_out = int(victim_out_iso) * (10_000 - int(slip_bps)) // 10_000
        cap = 2500

        ref_best, ref_exec_at_cap = _reference_max_profit(
            reserve_in=reserve_in,
            reserve_out=reserve_out,
            fee_bps=fee_bps,
            victim_amount_in=victim_amount_in,
            victim_min_out=victim_min_out,
            cap=cap,
        )
        out = max_sandwich_profit_exact_in_cpmm_bounded(
            reserve_in=reserve_in,
            reserve_out=reserve_out,
            fee_bps=fee_bps,
            victim_amount_in=victim_amount_in,
            victim_min_out=victim_min_out,
            max_attacker_amount_in=cap,
        )

        assert out.max_profit == ref_best
        cutoff = attacker_amount_in_cutoff_upper_bound_cpmm_exact_in(
            reserve_in=reserve_in,
            reserve_out=reserve_out,
            fee_bps=fee_bps,
            victim_amount_in=victim_amount_in,
            victim_min_out=victim_min_out,
        )
        if cutoff is None:
            covered_all = False
            feasible_max = cap
        else:
            feasible_max = max(0, int(cutoff) - 1)
            covered_all = bool(int(cap) >= int(feasible_max))

        assert out.scanned_max_attacker_amount_in == min(int(cap), int(feasible_max))
        assert out.status == ("ok" if covered_all else "inconclusive")


def test_victim_output_monotone_non_increasing_in_attacker_size_when_defined() -> None:
    rng = random.Random(0)
    for _ in range(200):
        reserve_in = rng.randint(100, 2000)
        reserve_out = rng.randint(100, 2000)
        fee_bps = rng.randint(0, 200)
        victim_amount_in = rng.randint(1, max(1, reserve_in // 2))

        # Choose a nontrivial min_out.
        try:
            victim_out_iso, _ = swap_exact_in(reserve_in, reserve_out, victim_amount_in, fee_bps)
        except Exception:
            continue
        if victim_out_iso <= 1:
            continue
        victim_min_out = int(victim_out_iso) - 1

        prev = None
        for a in range(1, 200):
            # Compute victim_out under attacker size a, skipping undefined points.
            p = sandwich_profit_exact_in_cpmm(
                reserve_in=reserve_in,
                reserve_out=reserve_out,
                fee_bps=fee_bps,
                victim_amount_in=victim_amount_in,
                victim_min_out=victim_min_out,
                attacker_amount_in=a,
            )
            if p is None:
                continue

            # Recompute victim output directly (profit doesn't expose it).
            # This keeps the monotonicity test self-contained and explicit.
            att_out, (x1, y1) = swap_exact_in(reserve_in, reserve_out, a, fee_bps)
            v_out, _ = swap_exact_in(x1, y1, victim_amount_in, fee_bps)

            if prev is not None:
                assert int(v_out) <= int(prev)
            prev = int(v_out)


def test_analytic_cutoff_is_sound_on_small_random_cases() -> None:
    """If the analytic cutoff says the victim must revert at/after a, it must."""
    rng = random.Random(123)
    for _ in range(300):
        reserve_in = rng.randint(50, 2000)
        reserve_out = rng.randint(50, 2000)
        fee_bps = rng.randint(0, 200)
        victim_amount_in = rng.randint(1, max(1, reserve_in // 2))

        try:
            victim_out_iso, _ = swap_exact_in(reserve_in, reserve_out, victim_amount_in, fee_bps)
        except Exception:
            continue
        if victim_out_iso <= 1:
            continue

        # Tight min_out so the cutoff is often small enough to check directly.
        victim_min_out = int(victim_out_iso) - 1
        cutoff = attacker_amount_in_cutoff_upper_bound_cpmm_exact_in(
            reserve_in=reserve_in,
            reserve_out=reserve_out,
            fee_bps=fee_bps,
            victim_amount_in=victim_amount_in,
            victim_min_out=victim_min_out,
        )
        assert cutoff is not None
        if cutoff <= 0 or cutoff > 5000:
            continue

        # Compute victim output at attacker size = cutoff and ensure it reverts.
        try:
            _, (x1, y1) = swap_exact_in(reserve_in, reserve_out, int(cutoff), fee_bps)
        except Exception:
            # If the attacker swap is itself invalid (e.g. fee consumes the input),
            # the cutoff is vacuously sound for sandwich feasibility.
            continue
        try:
            v_out, _ = swap_exact_in(x1, y1, victim_amount_in, fee_bps)
        except Exception:
            # Zero output or other invalid trade implies the victim cannot execute
            # for any positive min_out.
            continue
        assert int(v_out) < int(victim_min_out)


@pytest.mark.parametrize(
    "victim_min_out,expected_status,expected_scanned_max,reason",
    [
        # BVA around the isolated victim output for this witness.
        # With reserves=1000/1000, fee=0, victim_in=50 => isolated_out=47.
        (46, "ok", 36, "just-below isolated output: victim executes; cutoff implies feasible_max=36"),
        (47, "ok", 13, "exactly at isolated output: tighter cutoff implies feasible_max=13"),
        (48, "victim_reverts", 2000, "just-above isolated output: victim cannot execute even at attacker=0"),
    ],
    ids=lambda x: str(x),
)
def test_sandwich_risk_bva_victim_min_out_boundary(
    victim_min_out: int,
    expected_status: str,
    expected_scanned_max: int,
    reason: str,
) -> None:
    _ = reason
    res = max_sandwich_profit_exact_in_cpmm_bounded(
        reserve_in=1000,
        reserve_out=1000,
        fee_bps=0,
        victim_amount_in=50,
        victim_min_out=int(victim_min_out),
        max_attacker_amount_in=2000,
    )
    assert res.status == str(expected_status)
    assert res.scanned_max_attacker_amount_in == int(expected_scanned_max)


@pytest.mark.parametrize(
    "cap,expected_status,expected_scanned_max,reason",
    [
        # BVA around the "coverage" boundary for the known profitable witness:
        # victim_min_out=46 => cutoff=37 => feasible_max=36.
        (35, "inconclusive", 35, "just-below feasible_max: bounded scan may miss feasible attackers"),
        (36, "ok", 36, "exactly at feasible_max: scan covers all feasible attackers"),
        (37, "ok", 36, "just-above feasible_max: still only need scan up to feasible_max"),
    ],
    ids=lambda x: str(x),
)
def test_sandwich_risk_bva_cap_boundary(
    cap: int,
    expected_status: str,
    expected_scanned_max: int,
    reason: str,
) -> None:
    _ = reason
    res = max_sandwich_profit_exact_in_cpmm_bounded(
        reserve_in=1000,
        reserve_out=1000,
        fee_bps=0,
        victim_amount_in=50,
        victim_min_out=46,
        max_attacker_amount_in=int(cap),
    )
    assert res.status == str(expected_status)
    assert res.scanned_max_attacker_amount_in == int(expected_scanned_max)


@pytest.mark.parametrize(
    "cap,should_raise,reason",
    [
        (-1, True, "just-below min (invalid): cap must be non-negative"),
        (0, False, "exactly at min: scan only attacker=0"),
        (1, False, "just-above min"),
    ],
    ids=lambda x: str(x),
)
def test_sandwich_risk_bva_cap_validation(cap: int, should_raise: bool, reason: str) -> None:
    _ = reason
    if should_raise:
        with pytest.raises(ValueError):
            max_sandwich_profit_exact_in_cpmm_bounded(
                reserve_in=1000,
                reserve_out=1000,
                fee_bps=0,
                victim_amount_in=50,
                victim_min_out=46,
                max_attacker_amount_in=int(cap),
            )
        return
    out = max_sandwich_profit_exact_in_cpmm_bounded(
        reserve_in=1000,
        reserve_out=1000,
        fee_bps=0,
        victim_amount_in=50,
        victim_min_out=46,
        max_attacker_amount_in=int(cap),
    )
    assert out.scanned_max_attacker_amount_in == int(cap)


@pytest.mark.parametrize(
    "victim_min_out,expected_cutoff,reason",
    [
        (-1, None, "special: negative min_out implies cutoff not applicable (treated as <=0)"),
        (0, None, "boundary: min_out==0 implies unbounded feasibility (no cutoff)"),
        (1, 48951, "just-above 0: cutoff becomes large but finite"),
    ],
    ids=lambda x: str(x),
)
def test_cutoff_bva_min_out_zero_boundary(
    victim_min_out: int, expected_cutoff: int | None, reason: str
) -> None:
    _ = reason
    cut = attacker_amount_in_cutoff_upper_bound_cpmm_exact_in(
        reserve_in=1000,
        reserve_out=1000,
        fee_bps=0,
        victim_amount_in=50,
        victim_min_out=int(victim_min_out),
    )
    assert cut == expected_cutoff
