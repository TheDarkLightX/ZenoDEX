"""Tests for the VOPR-style deterministic simulation core.

Run: PYTHONPATH=. pytest experiments/dst_vopr_v1/test_vopr.py
"""

from __future__ import annotations

from vopr import simulate


def test_simulate_is_deterministic():
    # The VOPR/FoundationDB property: a run is a pure function of the seed.
    for s in (1, 7, 42, 100):
        a, b = simulate(s), simulate(s)
        assert a.op_log == b.op_log
        assert a.final_root == b.final_root
        assert a.crashes == b.crashes and a.fallbacks == b.fallbacks
        assert a.anomalies == b.anomalies


def test_no_seed_adopts_corrupt_state():
    # The REAL system (commitment-verified recovery) never adopts a torn/corrupt
    # snapshot: across 120 seeded runs, zero invariant violations. (Also covers the
    # non-vacuity check below in one pass.)
    results = [simulate(s, verify_commitment=True) for s in range(120)]
    for s, r in enumerate(results):
        assert r.anomalies == [], s
    # non-vacuous: the sweep genuinely exercised crashes AND fail-closed fallbacks.
    assert sum(r.crashes for r in results) > 0 and sum(r.fallbacks for r in results) > 0


def test_planted_bug_is_caught_and_reproducible():
    # Plant a bug (trust the disk blindly); under corruption it adopts a non-committed
    # state. The same invariant CATCHES it, the seed REPRODUCES it exactly, and the
    # real (verify-on) system is clean for that very seed.
    bug_seed = next(
        (s for s in range(300) if simulate(s, verify_commitment=False).anomalies), None
    )
    assert bug_seed is not None, "expected the planted bug to adopt corruption on some seed"
    r1 = simulate(bug_seed, verify_commitment=False)
    r2 = simulate(bug_seed, verify_commitment=False)
    assert r1.anomalies == r2.anomalies and r1.anomalies  # reproducible + non-empty
    assert simulate(bug_seed, verify_commitment=True).anomalies == []  # real system robust, same seed
