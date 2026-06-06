# [TESTER] v1
"""Tests for the TAU-CONSTITUTION v1 re-runner (Python mirror + env-gated Tau).

ALWAYS-GREEN deterministic core (no Tau binary needed). The env-gated
differential against the real Tau binary is SKIPPED in this environment.
"""

from __future__ import annotations

import os

import pytest

import src.integration.tau_constitution_rerunner as rerunner
from src.core.tau_constitution import (
    SettlementSurface,
    ConstitutionReceiptBody,
    constitution_policy_hash,
    get_entry,
    make_constitution_receipt,
)
from src.integration.tau_constitution_rerunner import (
    SpotSwapExactInWitness,
    TAU_CONSTITUTION_TAU_TESTS_ENV,
    build_witness_step,
    mirror_swap_exact_in_verdict,
    rerun_spot_swap_exact_in_python,
    spot_swap_witness_hash,
    tau_constitution_tau_enabled,
    verify_constitution,
    witness_from_spot_fill,
)
from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps
from src.integration.tau_witness import (
    SWAP_EXACT_IN_V1,
    build_swap_exact_in_v1_step,
)

_ONE = "0x" + "01" * 32
_TWO = "0x" + "02" * 32


def _witness(**overrides) -> SpotSwapExactInWitness:
    base = dict(
        reserve_in=1000,
        reserve_out=2000,
        amount_in=100,
        fee_bps=30,
        min_amount_out=1,
        amount_out=180,
        new_reserve_in=1100,
        new_reserve_out=1820,
    )
    base.update(overrides)
    return SpotSwapExactInWitness(**base)


# ---------------------------------------------------------------------------
# Python mirror: accept path
# ---------------------------------------------------------------------------


def test_mirror_valid_swap_accepts():
    assert rerun_spot_swap_exact_in_python(_witness()) == 1


# ---------------------------------------------------------------------------
# Python mirror: each reject path (stable verdict 0)
# ---------------------------------------------------------------------------


def test_mirror_reserve_in_transition_mismatch_rejects():
    # new_reserve_in != reserve_in + amount_in
    assert rerun_spot_swap_exact_in_python(_witness(new_reserve_in=1101)) == 0


def test_mirror_reserve_out_transition_mismatch_rejects():
    # 2000 - 180 = 1820; 1819 is wrong
    assert rerun_spot_swap_exact_in_python(_witness(new_reserve_out=1819)) == 0


def test_mirror_slippage_violation_rejects():
    # amount_out (180) < min_amount_out (181)
    assert rerun_spot_swap_exact_in_python(_witness(min_amount_out=181)) == 0


def test_mirror_amount_out_zero_rejects():
    # amount_out must be positive; new_reserve_out then = reserve_out
    assert rerun_spot_swap_exact_in_python(
        _witness(amount_out=0, new_reserve_out=2000)
    ) == 0


def test_mirror_reserve_out_lt_amount_out_rejects():
    # reserve_out (100) < amount_out (180) violates value_gte_32(reserve_out, amount_out)
    assert rerun_spot_swap_exact_in_python(
        _witness(reserve_out=100, amount_out=180, new_reserve_out=0)
    ) == 0


def test_mirror_fee_bps_out_of_range_rejects():
    # fee_bps=10001 is out of [0, 10000]. build_swap_exact_in_v1_step itself
    # rejects >10000, so assert the witness builder fails closed (range guard).
    with pytest.raises(ValueError):
        build_swap_exact_in_v1_step(
            reserve_in=1000, reserve_out=2000, amount_in=100, fee_bps=10001,
            min_amount_out=1, amount_out=180, new_reserve_in=1100, new_reserve_out=1820,
        )


def test_mirror_fee_bps_out_of_range_via_raw_step_rejects():
    # If a raw step bypasses the builder with fee_bps in bv[16] but > 10000,
    # the mirror's fee_bps_valid check rejects it.
    step = build_swap_exact_in_v1_step(
        reserve_in=1000, reserve_out=2000, amount_in=100, fee_bps=10000,
        min_amount_out=1, amount_out=180, new_reserve_in=1100, new_reserve_out=1820,
    )
    step["i7"] = 10001  # forge fee_bps out of [0, 10000] but inside bv[16]
    assert mirror_swap_exact_in_verdict(step) == 0


# ---------------------------------------------------------------------------
# Python mirror: boundary values
# ---------------------------------------------------------------------------


def test_mirror_amount_out_equals_min_amount_out_accepts():
    assert rerun_spot_swap_exact_in_python(_witness(min_amount_out=180)) == 1


def test_mirror_amount_out_equals_reserve_out_accepts():
    # amount_out == reserve_out (drains pool to 0); value_gte_32 allows equality
    assert rerun_spot_swap_exact_in_python(
        _witness(reserve_out=180, amount_out=180, new_reserve_out=0)
    ) == 1


def test_mirror_fee_bps_zero_accepts():
    assert rerun_spot_swap_exact_in_python(_witness(fee_bps=0)) == 1


def test_mirror_fee_bps_max_accepts():
    assert rerun_spot_swap_exact_in_python(_witness(fee_bps=10000)) == 1


# ---------------------------------------------------------------------------
# LIMB-EXACT divergence anchors (derived from swap_exact_in_v1.tau lines 33-35)
#
# These exercise the no-carry / no-borrow limb semantics. A naive full-integer
# mirror (a + b, a - b on the whole value) would return 1 here; the spec returns
# 0. Verdicts hand-derived from add_32 / sub_32 in the spec text (not Tau-binary
# confirmed here; the differential confirms them where the binary works).
# ---------------------------------------------------------------------------


def test_mirror_low_limb_carry_rejects():
    # reserve_in=65535 -> (hi=0, lo=65535); amount_in=1 -> (0,1);
    # new_reserve_in=65536 -> (1,0). add_32 low limb: sum_lo=0, 0>=65535 is FALSE.
    step = build_swap_exact_in_v1_step(
        reserve_in=65535, reserve_out=2000, amount_in=1, fee_bps=30,
        min_amount_out=1, amount_out=180, new_reserve_in=65536, new_reserve_out=1820,
    )
    assert mirror_swap_exact_in_verdict(step) == 0


def test_mirror_low_limb_borrow_rejects():
    # reserve_out=65536 -> (1,0); amount_out=1 -> (0,1). sub_32 low limb:
    # a_lo(0) >= b_lo(1) is FALSE.
    step = build_swap_exact_in_v1_step(
        reserve_in=1000, reserve_out=65536, amount_in=100, fee_bps=30,
        min_amount_out=1, amount_out=1, new_reserve_in=1100, new_reserve_out=65535,
    )
    assert mirror_swap_exact_in_verdict(step) == 0


def test_mirror_no_carry_high_limb_accepts():
    # A transition where both limbs are well-behaved across the 16-bit boundary
    # on the HIGH limb only (no low-limb carry): reserve_in=0x00010000 (65536),
    # amount_in=0x00010000 -> new=0x00020000. lo limbs all 0, hi 1+1=2 (no wrap).
    step = build_swap_exact_in_v1_step(
        reserve_in=65536, reserve_out=2000, amount_in=65536, fee_bps=30,
        min_amount_out=1, amount_out=180, new_reserve_in=131072, new_reserve_out=1820,
    )
    assert mirror_swap_exact_in_verdict(step) == 1


# ---------------------------------------------------------------------------
# FAITHFULNESS ANCHOR: pin the mirror to hand-checked tau_trace_cases verdicts
# (swap_exact_in constraint family). No live binary needed.
# ---------------------------------------------------------------------------


def test_mirror_matches_hand_checked_proof_gate_pass_values():
    # Values from tau_trace_cases.swap_exact_in_proof_gate_v1_pass (o1=1). The
    # proof-gate adds flags on top of the same bounds/slippage/transition checks
    # that swap_exact_in_v1 decides, so the underlying constraint verdict is 1.
    step = build_swap_exact_in_v1_step(
        reserve_in=1000, reserve_out=2000, amount_in=100, fee_bps=30,
        min_amount_out=1, amount_out=180, new_reserve_in=1100, new_reserve_out=1820,
    )
    assert mirror_swap_exact_in_verdict(step) == 1


def test_mirror_matches_hand_checked_bad_reserve_out_values():
    # tau_trace_cases.swap_exact_in_proof_gate_v1_fail_bad_reserve_out (o1=0):
    # new_reserve_out=1819 != 2000-180.
    step = build_swap_exact_in_v1_step(
        reserve_in=1000, reserve_out=2000, amount_in=100, fee_bps=30,
        min_amount_out=1, amount_out=180, new_reserve_in=1100, new_reserve_out=1819,
    )
    assert mirror_swap_exact_in_verdict(step) == 0


# ---------------------------------------------------------------------------
# Witness reconstruction from a settled Fill
# ---------------------------------------------------------------------------


def test_witness_from_fill_derives_post_state_reserves():
    w = witness_from_spot_fill(
        reserve_in_before=1000, reserve_out_before=2000,
        amount_in_filled=100, amount_out_filled=180,
        fee_bps=30, min_amount_out=1,
    )
    assert w.new_reserve_in == 1100
    assert w.new_reserve_out == 1820
    assert rerun_spot_swap_exact_in_python(w) == 1


# ---------------------------------------------------------------------------
# verify_constitution: full client reproduction
# ---------------------------------------------------------------------------


def _receipt(verdict: int, *, witness=None, policy_hash=None, surface_id=None):
    """Build a receipt bound to ``witness`` (default: the canonical valid swap).

    ``witness_hash`` is the REAL hash of the bound witness, so verification only
    passes when the supplied witness IS this settlement's witness.
    """
    entry = get_entry(SettlementSurface.SPOT_SWAP_EXACT_IN)
    w = witness if witness is not None else _witness()
    body = ConstitutionReceiptBody(
        surface_id=surface_id if surface_id is not None else entry.surface_id,
        policy_id=entry.spec_id,
        policy_hash=policy_hash if policy_hash is not None else constitution_policy_hash(entry),
        gate_output=entry.gate_output,
        claimed_verdict=verdict,
        pre_state_root=_ONE,
        post_state_root=_TWO if verdict == 1 else _ONE,
        witness_hash=spot_swap_witness_hash(w),
        accepted=(verdict == 1),
        rejection_code="" if verdict == 1 else "admission_failed",
    )
    return make_constitution_receipt(body)


def test_verify_accepts_real_settlement():
    w = _witness()
    receipt = _receipt(1, witness=w)
    result = verify_constitution(receipt, w, use_tau=False)
    assert result.ok and result.code == "ok"
    assert result.mirror_verdict == 1
    assert result.used_tau is False


def test_verify_default_requires_tau_authority(monkeypatch):
    w = _witness()
    receipt = _receipt(1, witness=w)

    def _unavailable(*args, **kwargs):
        raise RuntimeError("tau unavailable in test")

    monkeypatch.setattr(rerunner, "rerun_spot_swap_exact_in_tau", _unavailable)
    result = verify_constitution(receipt, w)

    assert not result.ok and result.code == "tau_unavailable"
    assert result.mirror_verdict == 1


# TEETH (a): tampered policy_hash caught BEFORE re-running.
def test_verify_rejects_tampered_policy_hash():
    w = _witness()
    receipt = _receipt(1, witness=w, policy_hash="0x" + "ab" * 32)
    result = verify_constitution(receipt, w, use_tau=False)
    assert not result.ok and result.code == "policy_hash_mismatch"


# TEETH (b): substituted witness (different swap) => witness_hash_mismatch.
def test_verify_rejects_substituted_witness():
    # Receipt is bound to the canonical valid swap, but a DIFFERENT
    # admission-valid swap (also verdict 1) is supplied. Without witness_hash
    # enforcement this would sail through; with it, the data binding rejects it.
    receipt = _receipt(1, witness=_witness())
    other_valid = _witness(amount_in=200, new_reserve_in=1200)  # different, still valid
    assert rerun_spot_swap_exact_in_python(other_valid) == 1  # genuinely valid
    result = verify_constitution(receipt, other_valid, use_tau=False)
    assert not result.ok and result.code == "witness_hash_mismatch"


# TEETH (c): tampered post-state (off-by-one) bound into receipt but claimed
# verdict 1 => mirror re-derives 0 => verdict_mismatch.
def test_verify_rejects_tampered_settlement_post_state():
    tampered = _witness(new_reserve_out=1819)  # admission-invalid
    # Bind the receipt to the tampered witness (so witness_hash matches) but
    # dishonestly claim verdict 1.
    receipt = _receipt(1, witness=tampered)
    result = verify_constitution(receipt, tampered, use_tau=False)
    assert not result.ok and result.code == "verdict_mismatch"
    assert result.mirror_verdict == 0


def test_verify_accepts_claimed_zero_when_admission_fails():
    # A settlement that genuinely fails admission, with a receipt honestly
    # claiming verdict 0, verifies (the client reproduces the 0).
    bad = _witness(new_reserve_out=1819)  # admission-invalid
    receipt = _receipt(0, witness=bad)
    result = verify_constitution(receipt, bad, use_tau=False)
    assert result.ok and result.code == "ok"
    assert result.mirror_verdict == 0


# TEETH (d): the REVERSE of (c) — a genuinely VALID settlement with a receipt that
# dishonestly claims verdict 0 (reject) => mirror re-derives 1 => verdict_mismatch.
# Proves the genuine-vs-echo check is SYMMETRIC, not a one-sided "catch dishonest
# accept" tautology (a pure echo of the claimed verdict would wrongly pass this).
def test_verify_rejects_claimed_reject_on_valid_settlement():
    valid = _witness()  # genuinely admission-valid
    assert rerun_spot_swap_exact_in_python(valid) == 1  # sanity: mirror says valid
    receipt = _receipt(0, witness=valid)  # dishonestly claims verdict 0 (reject)
    result = verify_constitution(receipt, valid, use_tau=False)
    assert not result.ok and result.code == "verdict_mismatch"
    assert result.mirror_verdict == 1


def test_verify_rejects_malformed_receipt():
    result = verify_constitution({"schema": "wrong"}, _witness(), use_tau=False)
    assert not result.ok and result.code == "schema"


def test_verify_rejects_surface_mismatch():
    # surface_id in body does not match the surface we re-run under.
    w = _witness()
    receipt = _receipt(1, witness=w, surface_id="add_liquidity")
    result = verify_constitution(receipt, w, use_tau=False)
    assert not result.ok and result.code == "surface_mismatch"


def test_verify_rejects_policy_id_mismatch():
    # policy_id names a rule other than the registered governing spec. Even
    # though policy_hash still binds the real spec_id, the human-visible
    # policy_id lie is rejected fail-closed.
    entry = get_entry(SettlementSurface.SPOT_SWAP_EXACT_IN)
    w = _witness()
    body = ConstitutionReceiptBody(
        surface_id=entry.surface_id,
        policy_id="swap_exact_in_fee_proof_gate_v1",  # different rule name
        policy_hash=constitution_policy_hash(entry),
        gate_output=entry.gate_output,
        claimed_verdict=1,
        pre_state_root=_ONE,
        post_state_root=_TWO,
        witness_hash=spot_swap_witness_hash(w),
        accepted=True,
    )
    receipt = make_constitution_receipt(body)
    result = verify_constitution(receipt, w, use_tau=False)
    assert not result.ok and result.code == "policy_id_mismatch"


def test_verify_witness_out_of_domain_fails_closed():
    # A witness whose derived post-state leaves u32 range fails closed with a
    # stable code, not an exception. The receipt is bound to this same
    # out-of-domain witness (so witness_hash matches), and re-running it raises
    # ValueError in split_u32 -> witness_out_of_domain.
    over = SpotSwapExactInWitness(
        reserve_in=1000, reserve_out=100, amount_in=100, fee_bps=30,
        min_amount_out=1, amount_out=200, new_reserve_in=1100, new_reserve_out=-100,
    )
    receipt = _receipt(1, witness=over)
    result = verify_constitution(receipt, over, use_tau=False)
    assert not result.ok and result.code == "witness_out_of_domain"


# ---------------------------------------------------------------------------
# Registry-only surfaces: re-run attempt fails closed (rerunner_not_wired_v1)
# ---------------------------------------------------------------------------


def test_verify_registry_only_surface_not_wired():
    entry = get_entry(SettlementSurface.ADD_LIQUIDITY)
    body = ConstitutionReceiptBody(
        surface_id=entry.surface_id,
        policy_id=entry.spec_id,
        policy_hash=constitution_policy_hash(entry),
        gate_output=entry.gate_output,
        claimed_verdict=1,
        pre_state_root=_ONE,
        post_state_root=_TWO,
        witness_hash=_ONE,
        accepted=True,
    )
    receipt = make_constitution_receipt(body)
    result = verify_constitution(
        receipt, _witness(), surface=SettlementSurface.ADD_LIQUIDITY, use_tau=False
    )
    assert not result.ok and result.code == "rerunner_not_wired_v1"


# ---------------------------------------------------------------------------
# HONEST SCOPE: the rule decides ADMISSION, not pricing.
# ---------------------------------------------------------------------------


def test_honest_scope_admission_valid_but_wrong_price_still_passes():
    """A demonstrably mispriced-but-admission-consistent swap still verifies.

    fee_bps is range-checked but never used in a pricing formula. A swap that
    gives out an absurdly generous amount_out (way more than any CPMM/fee curve
    would allow) but keeps the reserve transition internally consistent passes
    the admission rule. This documents that the re-run reproduces "obeyed the
    admission rule", NOT "was priced correctly".
    """
    # reserve_in=1000, reserve_out=2000, amount_in=1 (tiny in) but amount_out=1000
    # (half the pool out) — economically nonsense, but transition-consistent:
    # new_reserve_in = 1001, new_reserve_out = 1000.
    mispriced = SpotSwapExactInWitness(
        reserve_in=1000, reserve_out=2000, amount_in=1, fee_bps=30,
        min_amount_out=1, amount_out=1000, new_reserve_in=1001, new_reserve_out=1000,
    )
    assert rerun_spot_swap_exact_in_python(mispriced) == 1


# ---------------------------------------------------------------------------
# ENV-GATED differential: Python mirror == Tau o1 over a batch.
# SKIPPED unless TAU_CONSTITUTION_TAU_TESTS=1 and a working binary is present.
# In this environment the bundled binary times out, so this is reported SKIPPED.
# ---------------------------------------------------------------------------


def test_tau_differential_mirror_equals_binary():
    if os.environ.get(TAU_CONSTITUTION_TAU_TESTS_ENV) != "1":
        pytest.skip(
            f"set {TAU_CONSTITUTION_TAU_TESTS_ENV}=1 to run the Tau differential "
            "(the bundled binary times out in this environment)"
        )
    tau_bin = find_tau_bin()
    if not tau_bin:
        pytest.skip("tau binary not found")

    # A batch covering accept, slippage-fail, reserve-mismatch, carry, borrow.
    witnesses = [
        _witness(),  # valid -> 1
        _witness(min_amount_out=181),  # slippage -> 0
        _witness(new_reserve_out=1819),  # reserve_out mismatch -> 0
        SpotSwapExactInWitness(  # carry -> 0
            reserve_in=65535, reserve_out=2000, amount_in=1, fee_bps=30,
            min_amount_out=1, amount_out=180, new_reserve_in=65536, new_reserve_out=1820,
        ),
        SpotSwapExactInWitness(  # borrow -> 0
            reserve_in=1000, reserve_out=65536, amount_in=100, fee_bps=30,
            min_amount_out=1, amount_out=1, new_reserve_in=1100, new_reserve_out=65535,
        ),
    ]
    steps = [build_witness_step(w) for w in witnesses]
    outputs = run_tau_spec_steps(tau_bin, SWAP_EXACT_IN_V1.path, steps, timeout_s=60.0)

    failures = []
    for idx, w in enumerate(witnesses):
        mirror = mirror_swap_exact_in_verdict(steps[idx])
        tau = outputs.get(idx, {}).get("o1")
        if mirror != tau:
            failures.append(f"step[{idx}]: mirror={mirror} tau={tau}")
    assert not failures, "mirror/Tau disagreement:\n" + "\n".join(failures)


def test_tau_enabled_is_false_in_this_env():
    # Documents that the differential is SKIPPED here: without the env flag set,
    # tau_constitution_tau_enabled() is False even though a binary may exist.
    if os.environ.get(TAU_CONSTITUTION_TAU_TESTS_ENV) == "1":
        pytest.skip("env flag set; tau path may be enabled")
    assert tau_constitution_tau_enabled() is False
