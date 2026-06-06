"""TAU-CONSTITUTION v1 re-runner — the client's independent reproduction.

Given a settlement's ``(pre_state, intent, post_state)`` and a constitution
receipt, this module lets a client re-execute the GOVERNING RULE and confirm the
verdict the ledger claimed, instead of trusting an opaque solver's assertion.

Two paths run against the SAME registered spec:

  (a) PYTHON MIRROR (always available, deterministic). A pure integer
      re-derivation of ``swap_exact_in_constraints`` from
      ``swap_exact_in_v1.tau``. Its ONLY credibility is a differential test
      against the Tau binary; it is explicitly a FALLBACK, not the authority.

  (b) TAU BINARY (production authority). Loads the spec whose RAW bytes hash to
      the receipt's ``policy_hash`` (refuses on mismatch — fail closed), feeds
      the witness to the Tau runner, and confirms the gate output equals the
      claimed verdict. Tests gate the live binary behind
      ``TAU_CONSTITUTION_TAU_TESTS`` because the bundled binary times out in this
      environment; production verification requires Tau unless a caller
      explicitly asks for mirror-only checking via ``use_tau=False``.

LIMB-EXACT MIRROR (load-bearing correctness). The governing spec encodes the
32-bit reserve transition as two independent 16-bit limbs with NO cross-limb
carry/borrow:

    add_32: sum_lo = (a_lo + b_lo) mod 2^16  AND  sum_lo >= a_lo  AND  sum_lo >= b_lo
            sum_hi = (a_hi + b_hi) mod 2^16  AND  sum_hi >= a_hi  AND  sum_hi >= b_hi
    sub_32: a_hi >= b_hi  AND  a_lo >= b_lo  AND  diff_lo = a_lo - b_lo  AND  diff_hi = a_hi - b_hi

A naive full-integer mirror (``a + b``) would diverge from the spec on any swap
whose low 16-bit limb carries (add) or borrows (subtract). The mirror below
reproduces the limb semantics verbatim so the client's re-derivation matches the
literal rule, not an idealized version of it.

HONEST SCOPE: the rule decides ADMISSION (bounds + slippage + reserve-transition
consistency), NOT pricing. ``fee_bps`` is range-checked but never used in a
pricing formula. A re-run reproduces "your trade obeyed the admission rule",
NOT "your trade was priced correctly".
"""

from __future__ import annotations

import os
from dataclasses import dataclass
from typing import Any, Mapping, Optional

from ..core.tau_constitution import (
    ConstitutionEntry,
    SettlementSurface,
    constitution_policy_hash,
    get_entry,
)
from .tau_runner import find_tau_bin, run_tau_spec_steps, split_u32
from .tau_witness import build_swap_exact_in_v1_step
from .zeno_ledger_v0 import hash_v0

_MASK16 = 0xFFFF
_U32_MAX = 0xFFFFFFFF

TAU_CONSTITUTION_TAU_TESTS_ENV = "TAU_CONSTITUTION_TAU_TESTS"
TAU_CONSTITUTION_WITNESS_HASH_DOMAIN = "tau_constitution_witness_v1"


# ---------------------------------------------------------------------------
# Typed witness (the reconstructed (pre_state, intent, post_state) tuple)
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class SpotSwapExactInWitness:
    """The eight logical u32s that the spot constitution judges.

    Reconstructed from a settled Fill: ``new_reserve_in = reserve_in +
    amount_in``, ``new_reserve_out = reserve_out - amount_out`` are the post-state
    reserves; ``fee_bps`` and ``min_amount_out`` come from the intent.
    """

    reserve_in: int
    reserve_out: int
    amount_in: int
    fee_bps: int
    min_amount_out: int
    amount_out: int
    new_reserve_in: int
    new_reserve_out: int


def _check_u32(name: str, v: int) -> int:
    if not isinstance(v, int) or isinstance(v, bool) or v < 0 or v > _U32_MAX:
        raise ValueError(f"{name} out of u32 range: {v!r}")
    return int(v)


def witness_from_spot_fill(
    *,
    reserve_in_before: int,
    reserve_out_before: int,
    amount_in_filled: int,
    amount_out_filled: int,
    fee_bps: int,
    min_amount_out: int,
) -> SpotSwapExactInWitness:
    """Reconstruct the witness from settled spot-swap Fill + intent fields.

    Post-state reserves are derived exactly as the rule expects them:
    ``new_reserve_in = reserve_in + amount_in`` and
    ``new_reserve_out = reserve_out - amount_out`` (full-integer derivation; the
    LIMB constraints are what the rule then checks). If the derived post-state
    leaves u32 range, the caller's ``verify_constitution`` reports
    ``witness_out_of_domain`` (fail closed).
    """
    reserve_in = _check_u32("reserve_in", reserve_in_before)
    reserve_out = _check_u32("reserve_out", reserve_out_before)
    amount_in = _check_u32("amount_in", amount_in_filled)
    amount_out = _check_u32("amount_out", amount_out_filled)
    if not isinstance(fee_bps, int) or isinstance(fee_bps, bool):
        raise ValueError(f"fee_bps must be an int: {fee_bps!r}")
    if not isinstance(min_amount_out, int) or isinstance(min_amount_out, bool):
        raise ValueError(f"min_amount_out must be an int: {min_amount_out!r}")

    # Derive post-state reserves. These may leave u32 range; build_..._step will
    # range-check them, surfacing as witness_out_of_domain in verify_constitution.
    new_reserve_in = reserve_in + amount_in
    new_reserve_out = reserve_out - amount_out
    return SpotSwapExactInWitness(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_in=amount_in,
        fee_bps=int(fee_bps),
        min_amount_out=int(min_amount_out),
        amount_out=amount_out,
        new_reserve_in=new_reserve_in,
        new_reserve_out=new_reserve_out,
    )


def build_witness_step(witness: SpotSwapExactInWitness) -> dict[str, int]:
    """Encode the witness into the i1..i15 stream via the registered builder.

    Uses the SAME ``build_swap_exact_in_v1_step`` that the Tau binary path feeds,
    so the Python mirror and the Tau path judge an identical input dict. Raises
    ValueError (caught upstream as ``witness_out_of_domain``) if any field is out
    of range.
    """
    if not isinstance(witness, SpotSwapExactInWitness):
        raise TypeError("witness must be a SpotSwapExactInWitness")
    return build_swap_exact_in_v1_step(
        reserve_in=witness.reserve_in,
        reserve_out=witness.reserve_out,
        amount_in=witness.amount_in,
        fee_bps=witness.fee_bps,
        min_amount_out=witness.min_amount_out,
        amount_out=witness.amount_out,
        new_reserve_in=witness.new_reserve_in,
        new_reserve_out=witness.new_reserve_out,
    )


def spot_swap_witness_hash(witness: SpotSwapExactInWitness) -> str:
    """Canonical, domain-separated hash of the eight logical witness fields.

    Binds a re-run to a SPECIFIC settlement: ``verify_constitution`` confirms
    ``spot_swap_witness_hash(witness) == receipt.witness_hash`` so that a verdict-1
    receipt cannot be satisfied by substituting a *different* admission-valid
    swap. Reuses ``hash_v0`` (no new hash primitive). ``new_reserve_*`` are
    included even though they are derived, so a tampered post-state changes the
    witness hash regardless of whether it also flips the verdict.
    """
    if not isinstance(witness, SpotSwapExactInWitness):
        raise TypeError("witness must be a SpotSwapExactInWitness")
    return hash_v0(
        TAU_CONSTITUTION_WITNESS_HASH_DOMAIN,
        {
            "schema": "zenodex/tau_constitution_witness/v1",
            "reserve_in": int(witness.reserve_in),
            "reserve_out": int(witness.reserve_out),
            "amount_in": int(witness.amount_in),
            "fee_bps": int(witness.fee_bps),
            "min_amount_out": int(witness.min_amount_out),
            "amount_out": int(witness.amount_out),
            "new_reserve_in": int(witness.new_reserve_in),
            "new_reserve_out": int(witness.new_reserve_out),
        },
    )


# ---------------------------------------------------------------------------
# (a) Python mirror — LIMB-EXACT reproduction of swap_exact_in_constraints
# ---------------------------------------------------------------------------
#
# Each helper mirrors a named predicate in swap_exact_in_v1.tau (lines 26-37).
# All inputs are bv[16] limbs (0..65535). Boolean returns map to the spec's
# `<->` between o1=1 and the constraint conjunction.


def _fee_bps_valid(fee: int) -> bool:
    # fee_bps_valid: (fee >= 0x0000) && (fee <= 0x2710). 0x2710 = 10000.
    return 0 <= fee <= 10_000


def _is_positive_32(hi: int, lo: int) -> bool:
    # is_positive_32: (hi > 0) || (hi == 0 && lo > 0).
    return hi > 0 or (hi == 0 and lo > 0)


def _value_gte_32(hi1: int, lo1: int, hi2: int, lo2: int) -> bool:
    # value_gte_32: (hi1 > hi2) || (hi1 == hi2 && lo1 >= lo2).
    return (hi1 > hi2) or (hi1 == hi2 and lo1 >= lo2)


def _add_32(
    a_hi: int, a_lo: int, b_hi: int, b_lo: int, sum_hi: int, sum_lo: int
) -> bool:
    # add_32 (NO cross-limb carry; 16-bit modular sum + no-wrap guards):
    #   sum_lo == (a_lo + b_lo) mod 2^16  &&  sum_lo >= a_lo  &&  sum_lo >= b_lo
    #   sum_hi == (a_hi + b_hi) mod 2^16  &&  sum_hi >= a_hi  &&  sum_hi >= b_hi
    lo_ok = (
        sum_lo == ((a_lo + b_lo) & _MASK16)
        and sum_lo >= a_lo
        and sum_lo >= b_lo
    )
    hi_ok = (
        sum_hi == ((a_hi + b_hi) & _MASK16)
        and sum_hi >= a_hi
        and sum_hi >= b_hi
    )
    return lo_ok and hi_ok


def _sub_32(
    a_hi: int, a_lo: int, b_hi: int, b_lo: int, diff_hi: int, diff_lo: int
) -> bool:
    # sub_32 (NO cross-limb borrow; per-limb a >= b):
    #   a_hi >= b_hi  &&  a_lo >= b_lo  &&  diff_lo == a_lo - b_lo  &&  diff_hi == a_hi - b_hi
    return (
        a_hi >= b_hi
        and a_lo >= b_lo
        and diff_lo == ((a_lo - b_lo) & _MASK16)
        and diff_hi == ((a_hi - b_hi) & _MASK16)
    )


def mirror_swap_exact_in_verdict(step: Mapping[str, int]) -> int:
    """Re-derive the o1 verdict of ``swap_exact_in_v1.tau`` from an i1..i15 dict.

    LIMB-EXACT: reproduces ``swap_exact_in_constraints`` (spec line 37) over the
    16-bit limbs verbatim. Returns 1 if the admission rule holds, else 0.

    Mirror of the spec conjunction (in order):
      is_positive_32(reserve_in) && is_positive_32(reserve_out)
      && is_positive_32(amount_in) && fee_bps_valid(fee_bps)
      && is_positive_32(amount_out)
      && value_gte_32(reserve_out, amount_out)        # reserve_out >= amount_out
      && value_gte_32(amount_out, min_amount_out)      # slippage
      && add_32(reserve_in, amount_in -> new_reserve_in)
      && sub_32(reserve_out, amount_out -> new_reserve_out)
    """
    # i1..i15 limb stream (see build_swap_exact_in_v1_step / spec stream map).
    rin_hi, rin_lo = step["i1"], step["i2"]
    rout_hi, rout_lo = step["i3"], step["i4"]
    ain_hi, ain_lo = step["i5"], step["i6"]
    fee_bps = step["i7"]
    min_hi, min_lo = step["i8"], step["i9"]
    aout_hi, aout_lo = step["i10"], step["i11"]
    new_rin_hi, new_rin_lo = step["i12"], step["i13"]
    new_rout_hi, new_rout_lo = step["i14"], step["i15"]

    for name, v in (
        ("i1", rin_hi), ("i2", rin_lo), ("i3", rout_hi), ("i4", rout_lo),
        ("i5", ain_hi), ("i6", ain_lo), ("i8", min_hi), ("i9", min_lo),
        ("i10", aout_hi), ("i11", aout_lo), ("i12", new_rin_hi), ("i13", new_rin_lo),
        ("i14", new_rout_hi), ("i15", new_rout_lo),
    ):
        if not isinstance(v, int) or isinstance(v, bool) or v < 0 or v > _MASK16:
            raise ValueError(f"{name} out of bv[16] range: {v!r}")
    if not isinstance(fee_bps, int) or isinstance(fee_bps, bool) or fee_bps < 0 or fee_bps > _MASK16:
        raise ValueError(f"i7 (fee_bps) out of bv[16] range: {fee_bps!r}")

    ok = (
        _is_positive_32(rin_hi, rin_lo)
        and _is_positive_32(rout_hi, rout_lo)
        and _is_positive_32(ain_hi, ain_lo)
        and _fee_bps_valid(fee_bps)
        and _is_positive_32(aout_hi, aout_lo)
        and _value_gte_32(rout_hi, rout_lo, aout_hi, aout_lo)
        and _value_gte_32(aout_hi, aout_lo, min_hi, min_lo)
        and _add_32(rin_hi, rin_lo, ain_hi, ain_lo, new_rin_hi, new_rin_lo)
        and _sub_32(rout_hi, rout_lo, aout_hi, aout_lo, new_rout_hi, new_rout_lo)
    )
    return 1 if ok else 0


def rerun_spot_swap_exact_in_python(witness: SpotSwapExactInWitness) -> int:
    """Re-run the spot constitution via the LIMB-EXACT Python mirror (fallback).

    NOTE: This is a deterministic fallback whose ONLY credibility is the
    env-gated differential against the Tau binary. It is NOT the authority.
    """
    step = build_witness_step(witness)
    return mirror_swap_exact_in_verdict(step)


# ---------------------------------------------------------------------------
# (b) Tau binary — production authority, env-gated
# ---------------------------------------------------------------------------


def tau_constitution_tau_enabled() -> bool:
    """True only when both the env flag is set AND a tau binary is found."""
    if os.environ.get(TAU_CONSTITUTION_TAU_TESTS_ENV) != "1":
        return False
    return find_tau_bin() is not None


def rerun_spot_swap_exact_in_tau(
    entry: ConstitutionEntry,
    witness: SpotSwapExactInWitness,
    *,
    expected_policy_hash: Optional[str] = None,
    timeout_s: float = 30.0,
) -> int:
    """Re-run the spot constitution via the Tau binary (production authority).

    Fail closed: if ``expected_policy_hash`` is provided and the entry's
    raw-bytes policy_hash does not match it, raise before running anything.
    Returns the gate output (0|1). Caller must have confirmed availability via
    :func:`tau_constitution_tau_enabled` (this raises if no binary is found).
    """
    if not isinstance(entry, ConstitutionEntry):
        raise TypeError("entry must be a ConstitutionEntry")
    if expected_policy_hash is not None:
        if constitution_policy_hash(entry) != expected_policy_hash:
            raise ValueError("policy_hash_mismatch")
    tau_bin = find_tau_bin()
    if not tau_bin:
        raise RuntimeError("tau binary not available")
    step = build_witness_step(witness)
    outputs = run_tau_spec_steps(tau_bin, entry.spec_path, [step], timeout_s=timeout_s)
    got = outputs.get(0, {})
    verdict = got.get(entry.gate_output)
    if verdict not in (0, 1):
        raise RuntimeError(f"tau returned non-boolean verdict: {verdict!r}")
    return int(verdict)


# ---------------------------------------------------------------------------
# Top-level: verify_constitution — the client's independent reproduction
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ConstitutionVerification:
    """Result of a constitution re-run. ``ok`` is the gate; ``code`` is stable."""

    ok: bool
    code: str
    mirror_verdict: Optional[int] = None
    tau_verdict: Optional[int] = None
    used_tau: bool = False


def verify_constitution(
    receipt: Mapping[str, Any],
    witness: SpotSwapExactInWitness,
    *,
    surface: SettlementSurface = SettlementSurface.SPOT_SWAP_EXACT_IN,
    use_tau: Optional[bool] = None,
    tau_timeout_s: float = 30.0,
) -> ConstitutionVerification:
    """Independently reproduce the judgement bound into ``receipt``.

    Steps (fail closed at each):
      1. The receipt envelope must be well-formed and hash-bound.
      2. ``policy_hash`` in the receipt must equal the registered spec's
         raw-bytes policy_hash (else ``policy_hash_mismatch``) — checked BEFORE
         re-running anything. A settlement is inseparable from its rule.
      3. The surface must be wired E2E (else ``rerunner_not_wired_v1``).
      4. Re-derive the verdict from ``(pre_state, intent, post_state)`` via the
         governing rule: Python mirror always; Tau binary when enabled. If the
         witness leaves u32 range, ``witness_out_of_domain``.
      5. The re-derived verdict must equal the receipt's ``claimed_verdict``
         (else ``verdict_mismatch``).

    The client reproduces the judgement; it does not trust the ledger's
    assertion of it.
    """
    # 1. Envelope well-formed + hash-bound.
    from ..core.tau_constitution import verify_constitution_receipt

    ok, code = verify_constitution_receipt(receipt)
    if not ok:
        return ConstitutionVerification(ok=False, code=code)

    body = receipt["body"]
    claimed_verdict = int(body["claimed_verdict"])

    # 3 (resolve entry; may be registry-only). Catch unknown surfaces fail-closed.
    try:
        entry = get_entry(surface)
    except Exception:
        return ConstitutionVerification(ok=False, code="unknown_surface")

    # Receipt's surface_id must match the surface we are re-running under.
    if body.get("surface_id") != entry.surface_id:
        return ConstitutionVerification(ok=False, code="surface_mismatch")

    # Receipt's policy_id must name the registered governing spec. policy_hash
    # already binds the real spec_id, but a divergent human-visible policy_id is
    # itself a lie about which rule judged the trade — reject it fail-closed.
    if body.get("policy_id") != entry.spec_id:
        return ConstitutionVerification(ok=False, code="policy_id_mismatch")

    # 2. policy_hash must match the registered spec's raw-bytes hash. Checked
    #    BEFORE re-running anything (fail closed on an altered/unknown rule).
    try:
        registered_hash = constitution_policy_hash(entry)
    except Exception:
        return ConstitutionVerification(ok=False, code="registry_error")
    if body.get("policy_hash") != registered_hash:
        return ConstitutionVerification(ok=False, code="policy_hash_mismatch")
    if body.get("gate_output") != entry.gate_output:
        return ConstitutionVerification(ok=False, code="gate_output_mismatch")

    if not entry.wired_e2e:
        return ConstitutionVerification(ok=False, code="rerunner_not_wired_v1")

    # 2b. The supplied witness must BE the receipt's witness. Without this, a
    #     verdict-1 receipt could be satisfied by substituting any other
    #     admission-valid swap. Checked BEFORE re-running anything (fail closed
    #     on wrong data, just as on a wrong rule).
    if spot_swap_witness_hash(witness) != body.get("witness_hash"):
        return ConstitutionVerification(ok=False, code="witness_hash_mismatch")

    # 4. Re-derive the verdict via the governing rule.
    try:
        mirror_verdict = rerun_spot_swap_exact_in_python(witness)
    except ValueError:
        # Out-of-domain witness (e.g. derived reserve overflows u32).
        return ConstitutionVerification(ok=False, code="witness_out_of_domain")

    tau_verdict: Optional[int] = None
    used_tau = False
    # Production default: require the Tau authority. Mirror-only verification is
    # available for deterministic local tests, but it must be an explicit caller
    # choice so clients do not accidentally treat the fallback as authoritative.
    want_tau = True if use_tau is None else bool(use_tau)
    if want_tau:
        try:
            tau_verdict = rerun_spot_swap_exact_in_tau(
                entry,
                witness,
                expected_policy_hash=body.get("policy_hash"),
                timeout_s=tau_timeout_s,
            )
        except Exception:
            # Tau is the authority; if it was requested but failed, fail closed.
            return ConstitutionVerification(
                ok=False,
                code="tau_unavailable",
                mirror_verdict=mirror_verdict,
            )
        used_tau = True
        if tau_verdict != mirror_verdict:
            # The fallback disagrees with the authority: refuse, do not silently
            # trust the mirror.
            return ConstitutionVerification(
                ok=False,
                code="mirror_tau_disagreement",
                mirror_verdict=mirror_verdict,
                tau_verdict=tau_verdict,
                used_tau=True,
            )

    derived_verdict = tau_verdict if used_tau else mirror_verdict

    # 5. The re-derived verdict must match the receipt's claim.
    if derived_verdict != claimed_verdict:
        return ConstitutionVerification(
            ok=False,
            code="verdict_mismatch",
            mirror_verdict=mirror_verdict,
            tau_verdict=tau_verdict,
            used_tau=used_tau,
        )

    return ConstitutionVerification(
        ok=True,
        code="ok",
        mirror_verdict=mirror_verdict,
        tau_verdict=tau_verdict,
        used_tau=used_tau,
    )
