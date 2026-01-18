"""
Tau witness builders (pure, no IO).

These helpers turn Python integers into the exact input streams expected by
selected Tau specs (hi/lo limbs, etc.).
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Dict

from .tau_runner import split_u32


PROJECT_ROOT = Path(__file__).resolve().parents[2]
TAU_SPECS_DIR = PROJECT_ROOT / "src" / "tau_specs"
RECOMMENDED_SPECS_DIR = PROJECT_ROOT / "src" / "tau_specs" / "recommended"

TAU_WITNESS_SCHEMA_VERSION = 1


@dataclass(frozen=True)
class TauSpecRef:
    spec_id: str
    path: Path
    gate_output: str


def _u16(name: str, v: int) -> int:
    if not isinstance(v, int) or isinstance(v, bool) or v < 0 or v > 0xFFFF:
        raise ValueError(f"{name} out of u16 range: {v!r}")
    return int(v)


def _u32(name: str, v: int) -> tuple[int, int]:
    if not isinstance(v, int) or isinstance(v, bool) or v < 0 or v > 0xFFFFFFFF:
        raise ValueError(f"{name} out of u32 range: {v!r}")
    return split_u32(int(v))


def _bv32(name: str, v: int) -> int:
    if not isinstance(v, int) or isinstance(v, bool) or v < 0 or v > 0xFFFFFFFF:
        raise ValueError(f"{name} out of bv[32] range: {v!r}")
    return int(v)


def _u64(name: str, v: int) -> int:
    if not isinstance(v, int) or isinstance(v, bool) or v < 0 or v > 0xFFFFFFFFFFFFFFFF:
        raise ValueError(f"{name} out of u64 range: {v!r}")
    return int(v)


def _sbf(name: str, v: int) -> int:
    if v not in (0, 1):
        raise ValueError(f"{name} must be 0 or 1, got {v!r}")
    return int(v)


CPMM_V1 = TauSpecRef(
    spec_id="cpmm_v1",
    path=RECOMMENDED_SPECS_DIR / "cpmm_v1.tau",
    gate_output="o1",
)

NONCE_REPLAY_GUARD_V1 = TauSpecRef(
    spec_id="nonce_replay_guard_v1",
    path=RECOMMENDED_SPECS_DIR / "nonce_replay_guard_v1.tau",
    gate_output="o4",
)

INTENT_EXPIRY_GUARD_V1 = TauSpecRef(
    spec_id="intent_expiry_guard_v1",
    path=RECOMMENDED_SPECS_DIR / "intent_expiry_guard_v1.tau",
    gate_output="o4",
)

TOKEN_ARCHETYPE_SOULBOUND_V2 = TauSpecRef(
    spec_id="token_archetype_soulbound_v2",
    path=RECOMMENDED_SPECS_DIR / "token_archetype_soulbound_v2.tau",
    gate_output="o4",
)

TOKEN_ARCHETYPE_LOCK_WEIGHTED_REWARDS_32_V1 = TauSpecRef(
    spec_id="token_archetype_lock_weighted_rewards_32_v1",
    path=RECOMMENDED_SPECS_DIR / "token_archetype_lock_weighted_rewards_32_v1.tau",
    gate_output="o3",
)

TOKEN_ARCHETYPE_LOCK_WEIGHTED_REWARDS_32_V2 = TauSpecRef(
    spec_id="token_archetype_lock_weighted_rewards_32_v2",
    path=RECOMMENDED_SPECS_DIR / "token_archetype_lock_weighted_rewards_32_v2.tau",
    gate_output="o3",
)

TOKEN_ARCHETYPE_VESTING_CLIFF_32_V1 = TauSpecRef(
    spec_id="token_archetype_vesting_cliff_32_v1",
    path=RECOMMENDED_SPECS_DIR / "token_archetype_vesting_cliff_32_v1.tau",
    gate_output="o3",
)

TOKEN_ARCHETYPE_VESTING_CLIFF_32_V2 = TauSpecRef(
    spec_id="token_archetype_vesting_cliff_32_v2",
    path=RECOMMENDED_SPECS_DIR / "token_archetype_vesting_cliff_32_v2.tau",
    gate_output="o3",
)

SWAP_EXACT_IN_V4 = TauSpecRef(
    spec_id="swap_exact_in_v4",
    path=TAU_SPECS_DIR / "swap_exact_in_v4.tau",
    gate_output="o1",
)

SWAP_EXACT_OUT_V4 = TauSpecRef(
    spec_id="swap_exact_out_v4",
    path=TAU_SPECS_DIR / "swap_exact_out_v4.tau",
    gate_output="o1",
)

SWAP_EXACT_IN_V3 = TauSpecRef(
    spec_id="swap_exact_in_v3",
    path=TAU_SPECS_DIR / "swap_exact_in_v3.tau",
    gate_output="o1",
)

SWAP_EXACT_OUT_V3 = TauSpecRef(
    spec_id="swap_exact_out_v3",
    path=TAU_SPECS_DIR / "swap_exact_out_v3.tau",
    gate_output="o1",
)

SWAP_EXACT_IN_V1 = TauSpecRef(
    spec_id="swap_exact_in_v1",
    path=RECOMMENDED_SPECS_DIR / "swap_exact_in_v1.tau",
    gate_output="o1",
)

SWAP_EXACT_OUT_V1 = TauSpecRef(
    spec_id="swap_exact_out_v1",
    path=RECOMMENDED_SPECS_DIR / "swap_exact_out_v1.tau",
    gate_output="o1",
)

SWAP_EXACT_IN_PROOF_GATE_V1 = TauSpecRef(
    spec_id="swap_exact_in_proof_gate_v1",
    path=RECOMMENDED_SPECS_DIR / "swap_exact_in_proof_gate_v1.tau",
    gate_output="o1",
)

SWAP_EXACT_OUT_PROOF_GATE_V1 = TauSpecRef(
    spec_id="swap_exact_out_proof_gate_v1",
    path=RECOMMENDED_SPECS_DIR / "swap_exact_out_proof_gate_v1.tau",
    gate_output="o1",
)

SETTLEMENT_V1 = TauSpecRef(
    spec_id="settlement_v1",
    path=TAU_SPECS_DIR / "settlement_v1.tau",
    gate_output="o7",
)

SETTLEMENT_V1_PROOF_GATE = TauSpecRef(
    spec_id="settlement_v1_proof_gate",
    path=RECOMMENDED_SPECS_DIR / "settlement_v1_proof_gate.tau",
    gate_output="o7",
)

TOKEN_COMPOSITE_V1 = TauSpecRef(
    spec_id="token_composite_v1",
    path=TAU_SPECS_DIR / "token_composite_v1.tau",
    gate_output="o4",
)

TOKEN_COMPOSITE_V2 = TauSpecRef(
    spec_id="token_composite_v2",
    path=RECOMMENDED_SPECS_DIR / "token_composite_v2.tau",
    gate_output="o4",
)

BALANCE_SAFETY_V1 = TauSpecRef(
    spec_id="balance_safety_v1",
    path=TAU_SPECS_DIR / "balance_safety_v1.tau",
    gate_output="o1",
)

BALANCE_TRANSITION_V1 = TauSpecRef(
    spec_id="balance_transition_v1",
    path=RECOMMENDED_SPECS_DIR / "balance_transition_v1.tau",
    gate_output="o1",
)

BATCHING_V1 = TauSpecRef(
    spec_id="batching_v1",
    path=TAU_SPECS_DIR / "batching_v1.tau",
    gate_output="o1",
)

BATCHING_V1_4 = TauSpecRef(
    spec_id="batching_v1_4",
    path=TAU_SPECS_DIR / "batching_v1_4.tau",
    gate_output="o1",
)

BATCH_CANONICAL_V1_4 = TauSpecRef(
    spec_id="batch_canonical_v1_4",
    path=TAU_SPECS_DIR / "batch_canonical_v1_4.tau",
    gate_output="o1",
)

TOKENOMICS_BUYBACK_BURN_V1 = TauSpecRef(
    spec_id="tokenomics_buyback_burn_v1",
    path=TAU_SPECS_DIR / "tokenomics_buyback_burn_v1.tau",
    gate_output="o1",
)

TOKENOMICS_BUYBACK_BURN_V2 = TauSpecRef(
    spec_id="tokenomics_buyback_burn_v2",
    path=RECOMMENDED_SPECS_DIR / "tokenomics_buyback_burn_v2.tau",
    gate_output="o1",
)

PROTOCOL_TOKEN_V1 = TauSpecRef(
    spec_id="protocol_token_v1",
    path=RECOMMENDED_SPECS_DIR / "protocol_token_v1.tau",
    gate_output="o1",
)

PROTOCOL_TOKEN_V2 = TauSpecRef(
    spec_id="protocol_token_v2",
    path=RECOMMENDED_SPECS_DIR / "protocol_token_v2.tau",
    gate_output="o1",
)

PROTOCOL_TOKEN_V3 = TauSpecRef(
    spec_id="protocol_token_v3",
    path=RECOMMENDED_SPECS_DIR / "protocol_token_v3.tau",
    gate_output="o1",
)

TDEX_BUYBACK_PULSEX_V1 = TauSpecRef(
    spec_id="tdex_buyback_pulsex_v1",
    path=TAU_SPECS_DIR / "tdex_buyback_pulsex_v1.tau",
    gate_output="o4",
)

TDEX_BUYBACK_FLOOR_V1 = TauSpecRef(
    spec_id="tdex_buyback_floor_v1",
    path=TAU_SPECS_DIR / "tdex_buyback_floor_v1.tau",
    gate_output="o4",
)

TDEX_BUYBACK_FLOOR_FIXEDPOINT_V1 = TauSpecRef(
    spec_id="tdex_buyback_floor_fixedpoint_v1",
    path=TAU_SPECS_DIR / "tdex_buyback_floor_fixedpoint_v1.tau",
    gate_output="o5",
)

TDEX_BUYBACK_FLOOR_V2 = TauSpecRef(
    spec_id="tdex_buyback_floor_v2",
    path=RECOMMENDED_SPECS_DIR / "tdex_buyback_floor_v2.tau",
    gate_output="o4",
)

TDEX_BUYBACK_FLOOR_FIXEDPOINT_V2 = TauSpecRef(
    spec_id="tdex_buyback_floor_fixedpoint_v2",
    path=RECOMMENDED_SPECS_DIR / "tdex_buyback_floor_fixedpoint_v2.tau",
    gate_output="o5",
)

TDEX_FEE_REBATE_V1 = TauSpecRef(
    spec_id="tdex_fee_rebate_v1",
    path=TAU_SPECS_DIR / "tdex_fee_rebate_v1.tau",
    gate_output="o3",
)

TDEX_LOCK_WEIGHT_V1 = TauSpecRef(
    spec_id="tdex_lock_weight_v1",
    path=TAU_SPECS_DIR / "tdex_lock_weight_v1.tau",
    gate_output="o4",
)

GOVERNANCE_TIMELOCK_V1 = TauSpecRef(
    spec_id="governance_timelock_v1",
    path=TAU_SPECS_DIR / "governance_timelock_v1.tau",
    gate_output="o4",
)

REVISION_POLICY_V1 = TauSpecRef(
    spec_id="revision_policy_v1",
    path=RECOMMENDED_SPECS_DIR / "revision_policy_v1.tau",
    gate_output="o10",
)

REVISION_POLICY_V2 = TauSpecRef(
    spec_id="revision_policy_v2",
    path=RECOMMENDED_SPECS_DIR / "revision_policy_v2.tau",
    gate_output="o10",
)

PARAMETER_REGISTRY_V1 = TauSpecRef(
    spec_id="parameter_registry_v1",
    path=TAU_SPECS_DIR / "parameter_registry_v1.tau",
    gate_output="o1",
)

PARAMETER_REGISTRY_V2 = TauSpecRef(
    spec_id="parameter_registry_v2",
    path=RECOMMENDED_SPECS_DIR / "parameter_registry_v2.tau",
    gate_output="o1",
)

SETTLEMENT_V2_BUYBACK = TauSpecRef(
    spec_id="settlement_v2_buyback",
    path=TAU_SPECS_DIR / "settlement_v2_buyback.tau",
    gate_output="o8",
)

SETTLEMENT_V3_BUYBACK_FLOOR = TauSpecRef(
    spec_id="settlement_v3_buyback_floor",
    path=TAU_SPECS_DIR / "settlement_v3_buyback_floor.tau",
    gate_output="o8",
)

SETTLEMENT_V4_BUYBACK_FLOOR_REBATE_LOCK = TauSpecRef(
    spec_id="settlement_v4_buyback_floor_rebate_lock",
    path=RECOMMENDED_SPECS_DIR / "settlement_v4_buyback_floor_rebate_lock.tau",
    gate_output="o11",
)

SETTLEMENT_V2_BUYBACK_PROOF_GATE = TauSpecRef(
    spec_id="settlement_v2_buyback_proof_gate",
    path=RECOMMENDED_SPECS_DIR / "settlement_v2_buyback_proof_gate.tau",
    gate_output="o8",
)

SETTLEMENT_V3_BUYBACK_FLOOR_PROOF_GATE = TauSpecRef(
    spec_id="settlement_v3_buyback_floor_proof_gate",
    path=RECOMMENDED_SPECS_DIR / "settlement_v3_buyback_floor_proof_gate.tau",
    gate_output="o8",
)

SETTLEMENT_V4_BUYBACK_FLOOR_REBATE_LOCK_PROOF_GATE = TauSpecRef(
    spec_id="settlement_v4_buyback_floor_rebate_lock_proof_gate",
    path=RECOMMENDED_SPECS_DIR / "settlement_v4_buyback_floor_rebate_lock_proof_gate.tau",
    gate_output="o11",
)


def build_token_composite_v1_step(
    *,
    feature_flags: int,
    current_supply: int,
    transfer_amount: int,
    burn_rate_bps: int,
    explicit_floor: int,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/token_composite_v1.tau`.

    All inputs are bv[16], so we bound to 0..65535 here.
    """
    for name, v in (
        ("feature_flags", feature_flags),
        ("current_supply", current_supply),
        ("transfer_amount", transfer_amount),
        ("burn_rate_bps", burn_rate_bps),
        ("explicit_floor", explicit_floor),
    ):
        if not isinstance(v, int) or isinstance(v, bool) or v < 0 or v > 0xFFFF:
            raise ValueError(f"{name} out of u16 range: {v!r}")
    return {
        "i1": int(feature_flags),
        "i2": int(current_supply),
        "i3": int(transfer_amount),
        "i4": int(burn_rate_bps),
        "i5": int(explicit_floor),
    }


def build_token_composite_v2_step(
    *,
    burn_allowed: int,
    never_zero_guaranteed: int,
    feature_config_valid: int,
    proof_ok: int = 1,
    binding_ok: int = 1,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/token_composite_v2.tau`.
    """
    return {
        "i1": _sbf("burn_allowed", burn_allowed),
        "i2": _sbf("never_zero_guaranteed", never_zero_guaranteed),
        "i3": _sbf("feature_config_valid", feature_config_valid),
        "i4": _sbf("proof_ok", proof_ok),
        "i5": _sbf("binding_ok", binding_ok),
    }


def build_settlement_v1_step(
    *,
    # canonical ids
    a: int,
    b: int,
    c: int,
    d: int,
    # price series (pp, p, curr) for no_sandwich + stability
    price_pp: int,
    price_prev: int,
    price_curr: int,
    # cpmm fields
    cpmm_rx: int,
    cpmm_ry: int,
    cpmm_net: int,
    cpmm_out: int,
    # balance transition (32-bit hi/lo)
    bal_before: int,
    delta: int,
    bal_after: int,
    # protocol token transition (32-bit hi/lo), with one-hot action flags
    tok_from: int,
    tok_to: int,
    tok_supply: int,
    tok_amount: int,
    tok_from2: int,
    tok_to2: int,
    tok_supply2: int,
    do_transfer: int,
    do_mint: int,
    do_burn: int,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/settlement_v1.tau`.

    This spec uses bv[16] streams heavily. 32-bit quantities are represented as
    (hi16, lo16) limbs.
    """
    def u16(name: str, v: int) -> int:
        if not isinstance(v, int) or isinstance(v, bool) or v < 0 or v > 0xFFFF:
            raise ValueError(f"{name} out of u16 range: {v!r}")
        return int(v)

    def u32(name: str, v: int) -> tuple[int, int]:
        if not isinstance(v, int) or isinstance(v, bool) or v < 0 or v > 0xFFFFFFFF:
            raise ValueError(f"{name} out of u32 range: {v!r}")
        return split_u32(int(v))

    # canonical/order + price/cpmm are u16
    a16, b16, c16, d16 = (u16("a", a), u16("b", b), u16("c", c), u16("d", d))
    pp16, prev16, curr16 = (u16("price_pp", price_pp), u16("price_prev", price_prev), u16("price_curr", price_curr))
    rx16, ry16, net16, out16 = (u16("cpmm_rx", cpmm_rx), u16("cpmm_ry", cpmm_ry), u16("cpmm_net", cpmm_net), u16("cpmm_out", cpmm_out))

    # balance limbs
    bal0_hi, bal0_lo = u32("bal_before", bal_before)
    d_hi, d_lo = u32("delta", delta)
    bal1_hi, bal1_lo = u32("bal_after", bal_after)

    # token limbs
    f_hi, f_lo = u32("tok_from", tok_from)
    t_hi, t_lo = u32("tok_to", tok_to)
    s_hi, s_lo = u32("tok_supply", tok_supply)
    a_hi, a_lo = u32("tok_amount", tok_amount)
    f2_hi, f2_lo = u32("tok_from2", tok_from2)
    t2_hi, t2_lo = u32("tok_to2", tok_to2)
    s2_hi, s2_lo = u32("tok_supply2", tok_supply2)

    # action flags are sbf but we pass as ints (0/1)
    for name, v in (("do_transfer", do_transfer), ("do_mint", do_mint), ("do_burn", do_burn)):
        if v not in (0, 1):
            raise ValueError(f"{name} must be 0 or 1, got {v!r}")

    return {
        # ids
        "i1": a16,
        "i2": b16,
        "i3": c16,
        "i4": d16,
        # price series
        "i5": pp16,
        "i6": prev16,
        "i7": curr16,
        # cpmm
        "i8": rx16,
        "i9": ry16,
        "i10": net16,
        "i11": out16,
        # balance 32-bit transition
        "i12": int(bal0_hi),
        "i13": int(bal0_lo),
        "i14": int(d_hi),
        "i15": int(d_lo),
        "i16": int(bal1_hi),
        "i17": int(bal1_lo),
        # token transition 32-bit limbs
        "i18": int(f_hi),
        "i19": int(f_lo),
        "i20": int(t_hi),
        "i21": int(t_lo),
        "i22": int(s_hi),
        "i23": int(s_lo),
        "i24": int(a_hi),
        "i25": int(a_lo),
        "i26": int(f2_hi),
        "i27": int(f2_lo),
        "i28": int(t2_hi),
        "i29": int(t2_lo),
        "i30": int(s2_hi),
        "i31": int(s2_lo),
        # action flags (sbf)
        "i32": int(do_transfer),
        "i33": int(do_mint),
        "i34": int(do_burn),
    }


def build_settlement_v1_proof_gate_step(
    *,
    # canonical ids
    a: int,
    b: int,
    c: int,
    d: int,
    # price series for no_sandwich + stability
    price_pp: int,
    price_prev: int,
    price_curr: int,
    # externally verified component flags
    cpmm_ok: int = 1,
    balance_ok: int = 1,
    token_ok: int = 1,
    proof_ok: int = 1,
    binding_ok: int = 1,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/settlement_v1_proof_gate.tau`.
    """
    return {
        "i1": _u16("a", a),
        "i2": _u16("b", b),
        "i3": _u16("c", c),
        "i4": _u16("d", d),
        "i5": _u16("price_pp", price_pp),
        "i6": _u16("price_prev", price_prev),
        "i7": _u16("price_curr", price_curr),
        "i8": _sbf("cpmm_ok", cpmm_ok),
        "i9": _sbf("balance_ok", balance_ok),
        "i10": _sbf("token_ok", token_ok),
        "i11": _sbf("proof_ok", proof_ok),
        "i12": _sbf("binding_ok", binding_ok),
    }


def build_settlement_v2_buyback_proof_gate_step(
    *,
    # canonical ids
    a: int,
    b: int,
    c: int,
    d: int,
    # price series for no_sandwich + stability
    price_pp: int,
    price_prev: int,
    price_curr: int,
    # externally verified component flags
    cpmm_ok: int = 1,
    balance_ok: int = 1,
    token_ok: int = 1,
    buyback_ok: int = 1,
    proof_ok: int = 1,
    binding_ok: int = 1,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/settlement_v2_buyback_proof_gate.tau`.
    """
    return {
        "i1": _u16("a", a),
        "i2": _u16("b", b),
        "i3": _u16("c", c),
        "i4": _u16("d", d),
        "i5": _u16("price_pp", price_pp),
        "i6": _u16("price_prev", price_prev),
        "i7": _u16("price_curr", price_curr),
        "i8": _sbf("cpmm_ok", cpmm_ok),
        "i9": _sbf("balance_ok", balance_ok),
        "i10": _sbf("token_ok", token_ok),
        "i11": _sbf("buyback_ok", buyback_ok),
        "i12": _sbf("proof_ok", proof_ok),
        "i13": _sbf("binding_ok", binding_ok),
    }


def build_settlement_v3_buyback_floor_proof_gate_step(
    *,
    # canonical ids
    a: int,
    b: int,
    c: int,
    d: int,
    # price series for no_sandwich + stability
    price_pp: int,
    price_prev: int,
    price_curr: int,
    # externally verified component flags
    cpmm_ok: int = 1,
    balance_ok: int = 1,
    token_ok: int = 1,
    buyback_ok: int = 1,
    proof_ok: int = 1,
    binding_ok: int = 1,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/settlement_v3_buyback_floor_proof_gate.tau`.
    """
    return {
        "i1": _u16("a", a),
        "i2": _u16("b", b),
        "i3": _u16("c", c),
        "i4": _u16("d", d),
        "i5": _u16("price_pp", price_pp),
        "i6": _u16("price_prev", price_prev),
        "i7": _u16("price_curr", price_curr),
        "i8": _sbf("cpmm_ok", cpmm_ok),
        "i9": _sbf("balance_ok", balance_ok),
        "i10": _sbf("token_ok", token_ok),
        "i11": _sbf("buyback_ok", buyback_ok),
        "i12": _sbf("proof_ok", proof_ok),
        "i13": _sbf("binding_ok", binding_ok),
    }


def build_settlement_v4_buyback_floor_rebate_lock_proof_gate_step(
    *,
    # canonical ids
    a: int,
    b: int,
    c: int,
    d: int,
    # price series for no_sandwich + stability
    price_pp: int,
    price_prev: int,
    price_curr: int,
    # externally verified component flags
    cpmm_ok: int = 1,
    balance_ok: int = 1,
    token_ok: int = 1,
    buyback_floor_ok: int = 1,
    buyback_floor_fixedpoint_ok: int = 1,
    rebate_ok: int = 1,
    lock_weight_ok: int = 1,
    proof_ok: int = 1,
    binding_ok: int = 1,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/settlement_v4_buyback_floor_rebate_lock_proof_gate.tau`.
    """
    return {
        "i1": _u16("a", a),
        "i2": _u16("b", b),
        "i3": _u16("c", c),
        "i4": _u16("d", d),
        "i5": _u16("price_pp", price_pp),
        "i6": _u16("price_prev", price_prev),
        "i7": _u16("price_curr", price_curr),
        "i8": _sbf("cpmm_ok", cpmm_ok),
        "i9": _sbf("balance_ok", balance_ok),
        "i10": _sbf("token_ok", token_ok),
        "i11": _sbf("buyback_floor_ok", buyback_floor_ok),
        "i12": _sbf("buyback_floor_fixedpoint_ok", buyback_floor_fixedpoint_ok),
        "i13": _sbf("rebate_ok", rebate_ok),
        "i14": _sbf("lock_weight_ok", lock_weight_ok),
        "i15": _sbf("proof_ok", proof_ok),
        "i16": _sbf("binding_ok", binding_ok),
    }


def build_nonce_replay_guard_v1_step(
    *,
    intent_nonce: int,
    last_used_nonce: int,
    expected_nonce: int,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/nonce_replay_guard_v1.tau`.
    """
    for name, v in (
        ("intent_nonce", intent_nonce),
        ("last_used_nonce", last_used_nonce),
        ("expected_nonce", expected_nonce),
    ):
        if not isinstance(v, int) or isinstance(v, bool) or v < 0 or v > 0xFFFFFFFF:
            raise ValueError(f"{name} out of u32 range: {v!r}")
    return {"i1": int(intent_nonce), "i2": int(last_used_nonce), "i3": int(expected_nonce)}


def build_intent_expiry_guard_v1_step(
    *,
    intent_deadline: int,
    current_timestamp: int,
    min_validity_period: int,
    max_validity_period: int,
    intent_created: int,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/intent_expiry_guard_v1.tau`.
    """
    for name, v in (
        ("intent_deadline", intent_deadline),
        ("current_timestamp", current_timestamp),
        ("min_validity_period", min_validity_period),
        ("max_validity_period", max_validity_period),
        ("intent_created", intent_created),
    ):
        if not isinstance(v, int) or isinstance(v, bool) or v < 0 or v > 0xFFFFFFFF:
            raise ValueError(f"{name} out of u32 range: {v!r}")
    return {
        "i1": int(intent_deadline),
        "i2": int(current_timestamp),
        "i3": int(min_validity_period),
        "i4": int(max_validity_period),
        "i5": int(intent_created),
    }


def build_token_archetype_soulbound_v2_step(
    *,
    from_id: int,
    to_id: int,
    issuer_id: int,
    do_transfer: int,
    do_mint: int,
    do_burn: int,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/token_archetype_soulbound_v2.tau`.
    """
    for name, v in (("from_id", from_id), ("to_id", to_id), ("issuer_id", issuer_id)):
        if not isinstance(v, int) or isinstance(v, bool) or v < 0 or v > 0xFFFF:
            raise ValueError(f"{name} out of u16 range: {v!r}")
    return {
        "i1": int(from_id),
        "i2": int(to_id),
        "i3": int(issuer_id),
        "i4": _sbf("do_transfer", do_transfer),
        "i5": _sbf("do_mint", do_mint),
        "i6": _sbf("do_burn", do_burn),
    }


def build_token_archetype_lock_weighted_rewards_32_v1_step(
    *,
    stake_amount: int,
    lock_weight_bps: int,
    reward_amount: int,
    reward_cap: int,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/token_archetype_lock_weighted_rewards_32_v1.tau`.
    """
    for name, v in (
        ("stake_amount", stake_amount),
        ("lock_weight_bps", lock_weight_bps),
        ("reward_amount", reward_amount),
        ("reward_cap", reward_cap),
    ):
        if not isinstance(v, int) or isinstance(v, bool) or v < 0 or v > 0xFFFFFFFF:
            raise ValueError(f"{name} out of u32 range: {v!r}")
    return {"i1": int(stake_amount), "i2": int(lock_weight_bps), "i3": int(reward_amount), "i4": int(reward_cap)}


def build_token_archetype_lock_weighted_rewards_32_v2_step(
    *,
    stake_amount: int,
    lock_weight_bps: int,
    reward_amount: int,
    reward_cap: int,
    proof_ok: int = 1,
    binding_ok: int = 1,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/token_archetype_lock_weighted_rewards_32_v2.tau`.
    """
    for name, v in (
        ("stake_amount", stake_amount),
        ("lock_weight_bps", lock_weight_bps),
        ("reward_amount", reward_amount),
        ("reward_cap", reward_cap),
    ):
        if not isinstance(v, int) or isinstance(v, bool) or v < 0 or v > 0xFFFF:
            raise ValueError(f"{name} out of u16 range: {v!r}")
    return {
        "i1": int(stake_amount),
        "i2": int(lock_weight_bps),
        "i3": int(reward_amount),
        "i4": int(reward_cap),
        "i5": _sbf("proof_ok", proof_ok),
        "i6": _sbf("binding_ok", binding_ok),
    }


def build_token_archetype_vesting_cliff_32_v1_step(
    *,
    total_allocation: int,
    vested_amount: int,
    claim_amount: int,
    cliff_reached: int,
    claim_cap_amount: int,
    max_claim_bps: int,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/token_archetype_vesting_cliff_32_v1.tau`.
    """
    for name, v in (
        ("total_allocation", total_allocation),
        ("vested_amount", vested_amount),
        ("claim_amount", claim_amount),
        ("claim_cap_amount", claim_cap_amount),
        ("max_claim_bps", max_claim_bps),
    ):
        if not isinstance(v, int) or isinstance(v, bool) or v < 0 or v > 0xFFFFFFFF:
            raise ValueError(f"{name} out of u32 range: {v!r}")
    return {
        "i1": int(total_allocation),
        "i2": int(vested_amount),
        "i3": int(claim_amount),
        "i4": _sbf("cliff_reached", cliff_reached),
        "i5": int(claim_cap_amount),
        "i6": int(max_claim_bps),
    }


def build_token_archetype_vesting_cliff_32_v2_step(
    *,
    total_allocation: int,
    vested_amount: int,
    claim_amount: int,
    cliff_reached: int,
    claim_cap_amount: int,
    max_claim_bps: int,
    proof_ok: int = 1,
    binding_ok: int = 1,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/token_archetype_vesting_cliff_32_v2.tau`.
    """
    for name, v in (
        ("total_allocation", total_allocation),
        ("vested_amount", vested_amount),
        ("claim_amount", claim_amount),
        ("claim_cap_amount", claim_cap_amount),
        ("max_claim_bps", max_claim_bps),
    ):
        if not isinstance(v, int) or isinstance(v, bool) or v < 0 or v > 0xFFFF:
            raise ValueError(f"{name} out of u16 range: {v!r}")
    return {
        "i1": int(total_allocation),
        "i2": int(vested_amount),
        "i3": int(claim_amount),
        "i4": _sbf("cliff_reached", cliff_reached),
        "i5": int(claim_cap_amount),
        "i6": int(max_claim_bps),
        "i7": _sbf("proof_ok", proof_ok),
        "i8": _sbf("binding_ok", binding_ok),
    }


def build_cpmm_v1_step(
    *,
    reserve_in: int,
    reserve_out: int,
    amount_in: int,
    fee_bps: int,
    amount_out: int,
) -> Dict[str, int]:
    rin_hi, rin_lo = split_u32(reserve_in)
    rout_hi, rout_lo = split_u32(reserve_out)
    ain_hi, ain_lo = split_u32(amount_in)
    aout_hi, aout_lo = split_u32(amount_out)

    if not isinstance(fee_bps, int) or isinstance(fee_bps, bool) or not (0 <= fee_bps <= 10_000):
        raise ValueError(f"fee_bps out of range: {fee_bps}")

    return {
        "i1": rin_hi,
        "i2": rin_lo,
        "i3": rout_hi,
        "i4": rout_lo,
        "i5": ain_hi,
        "i6": ain_lo,
        "i7": int(fee_bps),
        "i8": aout_hi,
        "i9": aout_lo,
    }


def build_balance_safety_v1_step(*, balance_before: int, delta_add: int, delta_sub: int) -> Dict[str, int]:
    bal_hi, bal_lo = _u32("balance_before", balance_before)
    add_hi, add_lo = _u32("delta_add", delta_add)
    sub_hi, sub_lo = _u32("delta_sub", delta_sub)
    return {
        "i1": bal_hi,
        "i2": bal_lo,
        "i3": add_hi,
        "i4": add_lo,
        "i5": sub_hi,
        "i6": sub_lo,
    }


def build_balance_transition_v1_step(
    *,
    balance_before: int,
    delta_add: int,
    delta_sub: int,
    balance_mid: int,
    balance_after: int,
) -> Dict[str, int]:
    b0_hi, b0_lo = _u32("balance_before", balance_before)
    add_hi, add_lo = _u32("delta_add", delta_add)
    sub_hi, sub_lo = _u32("delta_sub", delta_sub)
    mid_hi, mid_lo = _u32("balance_mid", balance_mid)
    b1_hi, b1_lo = _u32("balance_after", balance_after)
    return {
        "i1": b0_hi,
        "i2": b0_lo,
        "i3": add_hi,
        "i4": add_lo,
        "i5": sub_hi,
        "i6": sub_lo,
        "i7": mid_hi,
        "i8": mid_lo,
        "i9": b1_hi,
        "i10": b1_lo,
    }


def build_batching_v1_step(
    *,
    intent_a_id: int,
    intent_b_id: int,
    executed_first_id: int,
    executed_second_id: int,
) -> Dict[str, int]:
    return {
        "i1": _u64("intent_a_id", intent_a_id),
        "i2": _u64("intent_b_id", intent_b_id),
        "i3": _u64("executed_first_id", executed_first_id),
        "i4": _u64("executed_second_id", executed_second_id),
    }


def build_batching_v1_4_step(
    *,
    intent_id_0: int,
    intent_id_1: int,
    intent_id_2: int,
    intent_id_3: int,
    executed_id_0: int,
    executed_id_1: int,
    executed_id_2: int,
    executed_id_3: int,
) -> Dict[str, int]:
    return {
        "i1": _u64("intent_id_0", intent_id_0),
        "i2": _u64("intent_id_1", intent_id_1),
        "i3": _u64("intent_id_2", intent_id_2),
        "i4": _u64("intent_id_3", intent_id_3),
        "i5": _u64("executed_id_0", executed_id_0),
        "i6": _u64("executed_id_1", executed_id_1),
        "i7": _u64("executed_id_2", executed_id_2),
        "i8": _u64("executed_id_3", executed_id_3),
    }


def build_batch_canonical_v1_4_step(
    *,
    intent_id_0: int,
    intent_id_1: int,
    intent_id_2: int,
    intent_id_3: int,
) -> Dict[str, int]:
    return {
        "i1": _u64("intent_id_0", intent_id_0),
        "i2": _u64("intent_id_1", intent_id_1),
        "i3": _u64("intent_id_2", intent_id_2),
        "i4": _u64("intent_id_3", intent_id_3),
    }


def build_protocol_token_v1_step(
    *,
    from_before: int,
    to_before: int,
    supply_before: int,
    amount: int,
    from_after: int,
    to_after: int,
    supply_after: int,
    do_transfer: int,
    do_mint: int,
    do_burn: int,
) -> Dict[str, int]:
    f0_hi, f0_lo = _u32("from_before", from_before)
    t0_hi, t0_lo = _u32("to_before", to_before)
    s0_hi, s0_lo = _u32("supply_before", supply_before)
    a_hi, a_lo = _u32("amount", amount)
    f1_hi, f1_lo = _u32("from_after", from_after)
    t1_hi, t1_lo = _u32("to_after", to_after)
    s1_hi, s1_lo = _u32("supply_after", supply_after)
    return {
        "i1": f0_hi,
        "i2": f0_lo,
        "i3": t0_hi,
        "i4": t0_lo,
        "i5": s0_hi,
        "i6": s0_lo,
        "i7": a_hi,
        "i8": a_lo,
        "i9": f1_hi,
        "i10": f1_lo,
        "i11": t1_hi,
        "i12": t1_lo,
        "i13": s1_hi,
        "i14": s1_lo,
        "i15": _sbf("do_transfer", do_transfer),
        "i16": _sbf("do_mint", do_mint),
        "i17": _sbf("do_burn", do_burn),
    }


def build_protocol_token_v2_step(
    *,
    from_before: int,
    to_before: int,
    supply_before: int,
    amount: int,
    from_after: int,
    to_after: int,
    supply_after: int,
    do_transfer: int,
    do_mint: int,
    do_burn: int,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/protocol_token_v2.tau`.

    v2 uses bv[32] but requires values <= 0xFFFF for non-wrapping addition.
    """
    for name, v in (
        ("from_before", from_before),
        ("to_before", to_before),
        ("supply_before", supply_before),
        ("amount", amount),
        ("from_after", from_after),
        ("to_after", to_after),
        ("supply_after", supply_after),
    ):
        if not isinstance(v, int) or isinstance(v, bool) or v < 0 or v > 0xFFFF:
            raise ValueError(f"{name} out of v2 safe-range (0..65535): {v!r}")
    return {
        "i1": int(from_before),
        "i2": int(to_before),
        "i3": int(supply_before),
        "i4": int(amount),
        "i5": int(from_after),
        "i6": int(to_after),
        "i7": int(supply_after),
        "i8": _sbf("do_transfer", do_transfer),
        "i9": _sbf("do_mint", do_mint),
        "i10": _sbf("do_burn", do_burn),
    }


def build_protocol_token_v3_step(
    *,
    from_before: int,
    to_before: int,
    supply_before: int,
    amount: int,
    from_after: int,
    to_after: int,
    supply_after: int,
    do_transfer: int,
    do_mint: int,
    do_burn: int,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/protocol_token_v3.tau` (bv[16]).
    """
    for name, v in (
        ("from_before", from_before),
        ("to_before", to_before),
        ("supply_before", supply_before),
        ("amount", amount),
        ("from_after", from_after),
        ("to_after", to_after),
        ("supply_after", supply_after),
    ):
        if not isinstance(v, int) or isinstance(v, bool) or v < 0 or v > 0xFFFF:
            raise ValueError(f"{name} out of u16 range: {v!r}")
    return {
        "i1": int(from_before),
        "i2": int(to_before),
        "i3": int(supply_before),
        "i4": int(amount),
        "i5": int(from_after),
        "i6": int(to_after),
        "i7": int(supply_after),
        "i8": _sbf("do_transfer", do_transfer),
        "i9": _sbf("do_mint", do_mint),
        "i10": _sbf("do_burn", do_burn),
    }


def build_tokenomics_buyback_burn_v1_step(
    *,
    fee_total: int,
    fee_to_lp: int,
    fee_to_treasury: int,
    fee_to_burn: int,
    buyback_triggered: int,
    burn_amount: int,
    burn_limit: int,
) -> Dict[str, int]:
    ft_hi, ft_lo = _u32("fee_total", fee_total)
    lp_hi, lp_lo = _u32("fee_to_lp", fee_to_lp)
    tr_hi, tr_lo = _u32("fee_to_treasury", fee_to_treasury)
    burn_hi, burn_lo = _u32("fee_to_burn", fee_to_burn)

    fee_to_lp_u32 = (int(lp_hi) << 16) + int(lp_lo)
    fee_to_treasury_u32 = (int(tr_hi) << 16) + int(tr_lo)
    fee_to_burn_u32 = (int(burn_hi) << 16) + int(burn_lo)

    lpt_hi, lpt_lo = _u32("fee_lp_treasury", fee_to_lp_u32 + fee_to_treasury_u32)
    sum_hi, sum_lo = _u32("fee_sum", (fee_to_lp_u32 + fee_to_treasury_u32) + fee_to_burn_u32)
    ba_hi, ba_lo = _u32("burn_amount", burn_amount)
    lim_hi, lim_lo = _u32("burn_limit", burn_limit)
    return {
        "i1": ft_hi,
        "i2": ft_lo,
        "i3": lp_hi,
        "i4": lp_lo,
        "i5": tr_hi,
        "i6": tr_lo,
        "i7": burn_hi,
        "i8": burn_lo,
        "i9": lpt_hi,
        "i10": lpt_lo,
        "i11": sum_hi,
        "i12": sum_lo,
        "i13": _sbf("buyback_triggered", buyback_triggered),
        "i14": ba_hi,
        "i15": ba_lo,
        "i16": lim_hi,
        "i17": lim_lo,
    }


def build_tokenomics_buyback_burn_v2_step(
    *,
    fee_total: int,
    fee_to_lp: int,
    fee_to_treasury: int,
    fee_to_burn: int,
    buyback_triggered: int,
    burn_amount: int,
    burn_limit: int,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/tokenomics_buyback_burn_v2.tau`.

    Note: v2 uses bv[32] streams, but requires values <= 0xFFFF for non-wrapping addition.
    """
    for name, v in (
        ("fee_total", fee_total),
        ("fee_to_lp", fee_to_lp),
        ("fee_to_treasury", fee_to_treasury),
        ("fee_to_burn", fee_to_burn),
        ("burn_amount", burn_amount),
        ("burn_limit", burn_limit),
    ):
        if not isinstance(v, int) or isinstance(v, bool) or v < 0 or v > 0xFFFF:
            raise ValueError(f"{name} out of v2 safe-range (0..65535): {v!r}")
    return {
        "i1": int(fee_total),
        "i2": int(fee_to_lp),
        "i3": int(fee_to_treasury),
        "i4": int(fee_to_burn),
        "i5": _sbf("buyback_triggered", buyback_triggered),
        "i6": int(burn_amount),
        "i7": int(burn_limit),
    }


def build_tdex_buyback_pulsex_v1_step(
    *,
    trade_amount: int,
    fee_charged: int,
    buyback_amount: int,
    burned_amount: int,
) -> Dict[str, int]:
    return {
        "i1": _u16("trade_amount", trade_amount),
        "i2": _u16("fee_charged", fee_charged),
        "i3": _u16("buyback_amount", buyback_amount),
        "i4": _u16("burned_amount", burned_amount),
    }


def build_tdex_buyback_floor_v1_step(
    *,
    trade_amount: int,
    fee_charged: int,
    buyback_amount: int,
    burned_amount: int,
    supply_before: int,
    supply_after: int,
    supply_floor: int,
) -> Dict[str, int]:
    s0_hi, s0_lo = _u32("supply_before", supply_before)
    s1_hi, s1_lo = _u32("supply_after", supply_after)
    f_hi, f_lo = _u32("supply_floor", supply_floor)
    return {
        "i1": _u16("trade_amount", trade_amount),
        "i2": _u16("fee_charged", fee_charged),
        "i3": _u16("buyback_amount", buyback_amount),
        "i4": _u16("burned_amount", burned_amount),
        "i5": s0_hi,
        "i6": s0_lo,
        "i7": s1_hi,
        "i8": s1_lo,
        "i9": f_hi,
        "i10": f_lo,
    }


def build_tdex_buyback_floor_fixedpoint_v1_step(
    *,
    trade_amount: int,
    fee_charged: int,
    buyback_amount: int,
    burned_amount: int,
    supply_before: int,
    supply_after: int,
    supply_floor: int,
    unit_scale: int,
) -> Dict[str, int]:
    step = build_tdex_buyback_floor_v1_step(
        trade_amount=trade_amount,
        fee_charged=fee_charged,
        buyback_amount=buyback_amount,
        burned_amount=burned_amount,
        supply_before=supply_before,
        supply_after=supply_after,
        supply_floor=supply_floor,
    )
    step["i11"] = _u16("unit_scale", unit_scale)
    return step


def build_tdex_buyback_floor_v2_step(
    *,
    trade_amount: int,
    fee_charged: int,
    buyback_amount: int,
    burned_amount: int,
    supply_before: int,
    supply_after: int,
    supply_floor: int,
    fee_rate_ok: int = 1,
    buyback_share_ok: int = 1,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/tdex_buyback_floor_v2.tau`.
    """
    return {
        "i1": _bv32("trade_amount", trade_amount),
        "i2": _bv32("fee_charged", fee_charged),
        "i3": _bv32("buyback_amount", buyback_amount),
        "i4": _bv32("burned_amount", burned_amount),
        "i5": _bv32("supply_before", supply_before),
        "i6": _bv32("supply_after", supply_after),
        "i7": _bv32("supply_floor", supply_floor),
        "i8": _sbf("fee_rate_ok", fee_rate_ok),
        "i9": _sbf("buyback_share_ok", buyback_share_ok),
    }


def build_tdex_buyback_floor_fixedpoint_v2_step(
    *,
    trade_amount: int,
    fee_charged: int,
    buyback_amount: int,
    burned_amount: int,
    supply_before: int,
    supply_after: int,
    supply_floor: int,
    unit_scale: int,
    fee_rate_ok: int = 1,
    buyback_share_ok: int = 1,
    unit_ok: int = 1,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/tdex_buyback_floor_fixedpoint_v2.tau`.
    """
    return {
        "i1": _bv32("trade_amount", trade_amount),
        "i2": _bv32("fee_charged", fee_charged),
        "i3": _bv32("buyback_amount", buyback_amount),
        "i4": _bv32("burned_amount", burned_amount),
        "i5": _bv32("supply_before", supply_before),
        "i6": _bv32("supply_after", supply_after),
        "i7": _bv32("supply_floor", supply_floor),
        "i8": _bv32("unit_scale", unit_scale),
        "i9": _sbf("fee_rate_ok", fee_rate_ok),
        "i10": _sbf("buyback_share_ok", buyback_share_ok),
        "i11": _sbf("unit_ok", unit_ok),
    }


def build_tdex_fee_rebate_v1_step(
    *,
    trade_fee: int,
    rebate_rate_bps: int,
    rebate_amount: int,
    rebate_cap: int,
) -> Dict[str, int]:
    return {
        "i1": _u16("trade_fee", trade_fee),
        "i2": _u16("rebate_rate_bps", rebate_rate_bps),
        "i3": _u16("rebate_amount", rebate_amount),
        "i4": _u16("rebate_cap", rebate_cap),
    }


def build_tdex_lock_weight_v1_step(
    *,
    lock_days: int,
    stake_amount: int,
    tier1_days: int,
    tier2_days: int,
    weight_t1: int,
    weight_t2: int,
    weight_t3: int,
    weight_claimed: int,
    weighted_stake: int,
) -> Dict[str, int]:
    return {
        "i1": _u16("lock_days", lock_days),
        "i2": _u16("stake_amount", stake_amount),
        "i3": _u16("tier1_days", tier1_days),
        "i4": _u16("tier2_days", tier2_days),
        "i5": _u16("weight_t1", weight_t1),
        "i6": _u16("weight_t2", weight_t2),
        "i7": _u16("weight_t3", weight_t3),
        "i8": _u16("weight_claimed", weight_claimed),
        "i9": _u16("weighted_stake", weighted_stake),
    }


def build_governance_timelock_v1_step(
    *,
    proposal_ts: int,
    current_ts: int,
    min_delay: int,
    exec_req: int,
) -> Dict[str, int]:
    return {
        "i1": _u16("proposal_ts", proposal_ts),
        "i2": _u16("current_ts", current_ts),
        "i3": _u16("min_delay", min_delay),
        "i4": _sbf("exec_req", exec_req),
    }


def build_parameter_registry_v1_step(
    *,
    exec_req: int,
    revision_ok: int,
    fee_curr: int,
    fee_next: int,
    buyback_curr: int,
    buyback_next: int,
    rebate_curr: int,
    rebate_next: int,
    floor_curr: int,
    floor_next: int,
    unit_curr: int,
    unit_next: int,
    tier1_curr: int,
    tier1_next: int,
    tier2_curr: int,
    tier2_next: int,
    weight1_curr: int,
    weight1_next: int,
    weight2_curr: int,
    weight2_next: int,
    weight3_curr: int,
    weight3_next: int,
) -> Dict[str, int]:
    f0_hi, f0_lo = _u32("floor_curr", floor_curr)
    f1_hi, f1_lo = _u32("floor_next", floor_next)
    return {
        "i1": _sbf("exec_req", exec_req),
        "i2": _sbf("revision_ok", revision_ok),
        "i3": _u16("fee_curr", fee_curr),
        "i4": _u16("fee_next", fee_next),
        "i5": _u16("buyback_curr", buyback_curr),
        "i6": _u16("buyback_next", buyback_next),
        "i7": _u16("rebate_curr", rebate_curr),
        "i8": _u16("rebate_next", rebate_next),
        "i9": f0_hi,
        "i10": f0_lo,
        "i11": f1_hi,
        "i12": f1_lo,
        "i13": _u16("unit_curr", unit_curr),
        "i14": _u16("unit_next", unit_next),
        "i15": _u16("tier1_curr", tier1_curr),
        "i16": _u16("tier1_next", tier1_next),
        "i17": _u16("tier2_curr", tier2_curr),
        "i18": _u16("tier2_next", tier2_next),
        "i19": _u16("weight1_curr", weight1_curr),
        "i20": _u16("weight1_next", weight1_next),
        "i21": _u16("weight2_curr", weight2_curr),
        "i22": _u16("weight2_next", weight2_next),
        "i23": _u16("weight3_curr", weight3_curr),
        "i24": _u16("weight3_next", weight3_next),
    }


def build_parameter_registry_v2_step(
    *,
    exec_req: int,
    revision_ok: int,
    fee_applied: int,
    buyback_applied: int,
    rebate_applied: int,
    floor_applied: int,
    unit_applied: int,
    tier1_applied: int,
    tier2_applied: int,
    weight1_applied: int,
    weight2_applied: int,
    weight3_applied: int,
    proof_ok: int = 1,
    binding_ok: int = 1,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/parameter_registry_v2.tau`.
    """
    floor_hi, floor_lo = _u32("floor_applied", floor_applied)
    return {
        "i1": _sbf("exec_req", exec_req),
        "i2": _sbf("revision_ok", revision_ok),
        "i3": _u16("fee_applied", fee_applied),
        "i4": _u16("buyback_applied", buyback_applied),
        "i5": _u16("rebate_applied", rebate_applied),
        "i6": floor_hi,
        "i7": floor_lo,
        "i8": _u16("unit_applied", unit_applied),
        "i9": _u16("tier1_applied", tier1_applied),
        "i10": _u16("tier2_applied", tier2_applied),
        "i11": _u16("weight1_applied", weight1_applied),
        "i12": _u16("weight2_applied", weight2_applied),
        "i13": _u16("weight3_applied", weight3_applied),
        "i14": _sbf("proof_ok", proof_ok),
        "i15": _sbf("binding_ok", binding_ok),
    }


def build_revision_policy_v1_step(
    *,
    # governance
    approved: int,
    exec_req: int,
    proposal_ts: int,
    current_ts: int,
    min_delay: int,
    # fee
    fee_curr: int,
    fee_next: int,
    fee_min: int,
    fee_max: int,
    fee_step: int,
    # buyback
    buyback_curr: int,
    buyback_next: int,
    buyback_min: int,
    buyback_max: int,
    buyback_step: int,
    # rebate
    rebate_curr: int,
    rebate_next: int,
    rebate_min: int,
    rebate_max: int,
    rebate_step: int,
    # floor (u32)
    floor_curr: int,
    floor_next: int,
    floor_min: int,
    floor_max: int,
    floor_step: int,
    # unit
    unit_curr: int,
    unit_next: int,
    unit_min: int,
    unit_max: int,
    unit_step: int,
    # tiers
    tier1_curr: int,
    tier1_next: int,
    tier1_min: int,
    tier1_max: int,
    tier1_step: int,
    tier2_curr: int,
    tier2_next: int,
    tier2_min: int,
    tier2_max: int,
    tier2_step: int,
    # weights
    weight1_curr: int,
    weight1_next: int,
    weight1_min: int,
    weight1_max: int,
    weight1_step: int,
    weight2_curr: int,
    weight2_next: int,
    weight2_min: int,
    weight2_max: int,
    weight2_step: int,
    weight3_curr: int,
    weight3_next: int,
    weight3_min: int,
    weight3_max: int,
    weight3_step: int,
) -> Dict[str, int]:
    fc_hi, fc_lo = _u32("floor_curr", floor_curr)
    fn_hi, fn_lo = _u32("floor_next", floor_next)
    fmin_hi, fmin_lo = _u32("floor_min", floor_min)
    fmax_hi, fmax_lo = _u32("floor_max", floor_max)
    fstep_hi, fstep_lo = _u32("floor_step", floor_step)

    return {
        # governance
        "i1": _sbf("approved", approved),
        "i2": _sbf("exec_req", exec_req),
        "i3": _u16("proposal_ts", proposal_ts),
        "i4": _u16("current_ts", current_ts),
        "i5": _u16("min_delay", min_delay),
        # fee
        "i6": _u16("fee_curr", fee_curr),
        "i7": _u16("fee_next", fee_next),
        "i8": _u16("fee_min", fee_min),
        "i9": _u16("fee_max", fee_max),
        "i10": _u16("fee_step", fee_step),
        # buyback
        "i11": _u16("buyback_curr", buyback_curr),
        "i12": _u16("buyback_next", buyback_next),
        "i13": _u16("buyback_min", buyback_min),
        "i14": _u16("buyback_max", buyback_max),
        "i15": _u16("buyback_step", buyback_step),
        # rebate
        "i16": _u16("rebate_curr", rebate_curr),
        "i17": _u16("rebate_next", rebate_next),
        "i18": _u16("rebate_min", rebate_min),
        "i19": _u16("rebate_max", rebate_max),
        "i20": _u16("rebate_step", rebate_step),
        # floor
        "i21": fc_hi,
        "i22": fc_lo,
        "i23": fn_hi,
        "i24": fn_lo,
        "i25": fmin_hi,
        "i26": fmin_lo,
        "i27": fmax_hi,
        "i28": fmax_lo,
        "i29": fstep_hi,
        "i30": fstep_lo,
        # unit
        "i31": _u16("unit_curr", unit_curr),
        "i32": _u16("unit_next", unit_next),
        "i33": _u16("unit_min", unit_min),
        "i34": _u16("unit_max", unit_max),
        "i35": _u16("unit_step", unit_step),
        # tiers
        "i36": _u16("tier1_curr", tier1_curr),
        "i37": _u16("tier1_next", tier1_next),
        "i38": _u16("tier1_min", tier1_min),
        "i39": _u16("tier1_max", tier1_max),
        "i40": _u16("tier1_step", tier1_step),
        "i41": _u16("tier2_curr", tier2_curr),
        "i42": _u16("tier2_next", tier2_next),
        "i43": _u16("tier2_min", tier2_min),
        "i44": _u16("tier2_max", tier2_max),
        "i45": _u16("tier2_step", tier2_step),
        # weights
        "i46": _u16("weight1_curr", weight1_curr),
        "i47": _u16("weight1_next", weight1_next),
        "i48": _u16("weight1_min", weight1_min),
        "i49": _u16("weight1_max", weight1_max),
        "i50": _u16("weight1_step", weight1_step),
        "i51": _u16("weight2_curr", weight2_curr),
        "i52": _u16("weight2_next", weight2_next),
        "i53": _u16("weight2_min", weight2_min),
        "i54": _u16("weight2_max", weight2_max),
        "i55": _u16("weight2_step", weight2_step),
        "i56": _u16("weight3_curr", weight3_curr),
        "i57": _u16("weight3_next", weight3_next),
        "i58": _u16("weight3_min", weight3_min),
        "i59": _u16("weight3_max", weight3_max),
        "i60": _u16("weight3_step", weight3_step),
    }


def build_revision_policy_v2_step(
    *,
    approved: int,
    exec_req: int,
    governance_ok: int,
    revision_ok: int,
    proof_ok: int = 1,
    binding_ok: int = 1,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/revision_policy_v2.tau`.
    """
    return {
        "i1": _sbf("approved", approved),
        "i2": _sbf("exec_req", exec_req),
        "i3": _sbf("governance_ok", governance_ok),
        "i4": _sbf("revision_ok", revision_ok),
        "i5": _sbf("proof_ok", proof_ok),
        "i6": _sbf("binding_ok", binding_ok),
    }


def build_settlement_v2_buyback_step(
    *,
    settlement_v1_step: Dict[str, int],
    trade_amount: int,
    fee_charged: int,
    buyback_amount: int,
    burned_amount: int,
) -> Dict[str, int]:
    step = dict(settlement_v1_step)
    step["i35"] = _u16("trade_amount", trade_amount)
    step["i36"] = _u16("fee_charged", fee_charged)
    step["i37"] = _u16("buyback_amount", buyback_amount)
    step["i38"] = _u16("burned_amount", burned_amount)
    return step


def build_settlement_v3_buyback_floor_step(*, settlement_v2_step: Dict[str, int], supply_floor: int) -> Dict[str, int]:
    step = dict(settlement_v2_step)
    floor_hi, floor_lo = _u32("supply_floor", supply_floor)
    step["i39"] = floor_hi
    step["i40"] = floor_lo
    return step


def build_settlement_v4_buyback_floor_rebate_lock_step(
    *,
    settlement_v3_step: Dict[str, int],
    unit_scale: int,
    rebate_rate_bps: int,
    rebate_amount: int,
    rebate_cap: int,
    lock_days: int,
    stake_amount: int,
    tier1_days: int,
    tier2_days: int,
    weight_t1: int,
    weight_t2: int,
    weight_t3: int,
    weight_claimed: int,
    weighted_stake: int,
) -> Dict[str, int]:
    step = dict(settlement_v3_step)
    step["i41"] = _u16("unit_scale", unit_scale)
    step["i42"] = _u16("rebate_rate_bps", rebate_rate_bps)
    step["i43"] = _u16("rebate_amount", rebate_amount)
    step["i44"] = _u16("rebate_cap", rebate_cap)
    step["i45"] = _u16("lock_days", lock_days)
    step["i46"] = _u16("stake_amount", stake_amount)
    step["i47"] = _u16("tier1_days", tier1_days)
    step["i48"] = _u16("tier2_days", tier2_days)
    step["i49"] = _u16("weight_t1", weight_t1)
    step["i50"] = _u16("weight_t2", weight_t2)
    step["i51"] = _u16("weight_t3", weight_t3)
    step["i52"] = _u16("weight_claimed", weight_claimed)
    step["i53"] = _u16("weighted_stake", weighted_stake)
    return step


def build_swap_exact_in_v1_step(
    *,
    reserve_in: int,
    reserve_out: int,
    amount_in: int,
    fee_bps: int,
    min_amount_out: int,
    amount_out: int,
    new_reserve_in: int,
    new_reserve_out: int,
) -> Dict[str, int]:
    rin_hi, rin_lo = split_u32(reserve_in)
    rout_hi, rout_lo = split_u32(reserve_out)
    ain_hi, ain_lo = split_u32(amount_in)
    min_hi, min_lo = split_u32(min_amount_out)
    aout_hi, aout_lo = split_u32(amount_out)
    new_rin_hi, new_rin_lo = split_u32(new_reserve_in)
    new_rout_hi, new_rout_lo = split_u32(new_reserve_out)

    if not isinstance(fee_bps, int) or isinstance(fee_bps, bool) or not (0 <= fee_bps <= 10_000):
        raise ValueError(f"fee_bps out of range: {fee_bps}")

    return {
        "i1": rin_hi,
        "i2": rin_lo,
        "i3": rout_hi,
        "i4": rout_lo,
        "i5": ain_hi,
        "i6": ain_lo,
        "i7": int(fee_bps),
        "i8": min_hi,
        "i9": min_lo,
        "i10": aout_hi,
        "i11": aout_lo,
        "i12": new_rin_hi,
        "i13": new_rin_lo,
        "i14": new_rout_hi,
        "i15": new_rout_lo,
    }


def build_swap_exact_in_v4_step(
    *,
    reserve_in: int,
    reserve_out: int,
    amount_in: int,
    fee_bps: int,
    min_amount_out: int,
    amount_out: int,
    new_reserve_in: int,
    new_reserve_out: int,
) -> Dict[str, int]:
    # v4 is bv[32]-native (no hi/lo limbs).
    if not isinstance(fee_bps, int) or isinstance(fee_bps, bool) or not (0 <= fee_bps <= 10_000):
        raise ValueError(f"fee_bps out of range: {fee_bps}")
    return {
        "i1": int(reserve_in),
        "i2": int(reserve_out),
        "i3": int(amount_in),
        "i4": int(fee_bps),
        "i5": int(min_amount_out),
        "i6": int(amount_out),
        "i7": int(new_reserve_in),
        "i8": int(new_reserve_out),
    }


def build_swap_exact_in_proof_gate_v1_step(
    *,
    reserve_in: int,
    reserve_out: int,
    amount_in: int,
    fee_bps: int,
    min_amount_out: int,
    amount_out: int,
    new_reserve_in: int,
    new_reserve_out: int,
    proof_ok: int = 1,
    binding_ok: int = 1,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/swap_exact_in_proof_gate_v1.tau`.
    """
    step = build_swap_exact_in_v4_step(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_in=amount_in,
        fee_bps=fee_bps,
        min_amount_out=min_amount_out,
        amount_out=amount_out,
        new_reserve_in=new_reserve_in,
        new_reserve_out=new_reserve_out,
    )
    step["i9"] = _sbf("proof_ok", proof_ok)
    step["i10"] = _sbf("binding_ok", binding_ok)
    return step


def build_swap_exact_in_v3_step(
    *,
    reserve_in: int,
    reserve_out: int,
    amount_in: int,
    fee_bps: int,
    min_amount_out: int,
    amount_out: int,
    new_reserve_in: int,
    new_reserve_out: int,
    k_old: int,
    k_new: int,
) -> Dict[str, int]:
    # v3 is bv[32] inputs plus precomputed bv[64] k values.
    if not isinstance(fee_bps, int) or isinstance(fee_bps, bool) or not (0 <= fee_bps <= 10_000):
        raise ValueError(f"fee_bps out of range: {fee_bps}")
    for name, v in (("k_old", k_old), ("k_new", k_new)):
        if not isinstance(v, int) or isinstance(v, bool) or v < 0 or v > 0xFFFFFFFFFFFFFFFF:
            raise ValueError(f"{name} out of u64 range: {v!r}")
    return {
        "i1": int(reserve_in),
        "i2": int(reserve_out),
        "i3": int(amount_in),
        "i4": int(fee_bps),
        "i5": int(min_amount_out),
        "i6": int(amount_out),
        "i7": int(new_reserve_in),
        "i8": int(new_reserve_out),
        "i9": int(k_old),
        "i10": int(k_new),
    }


def build_swap_exact_out_v1_step(
    *,
    reserve_in: int,
    reserve_out: int,
    amount_out: int,
    fee_bps: int,
    max_amount_in: int,
    amount_in: int,
    new_reserve_in: int,
    new_reserve_out: int,
) -> Dict[str, int]:
    rin_hi, rin_lo = split_u32(reserve_in)
    rout_hi, rout_lo = split_u32(reserve_out)
    aout_hi, aout_lo = split_u32(amount_out)
    max_hi, max_lo = split_u32(max_amount_in)
    ain_hi, ain_lo = split_u32(amount_in)
    new_rin_hi, new_rin_lo = split_u32(new_reserve_in)
    new_rout_hi, new_rout_lo = split_u32(new_reserve_out)

    if not isinstance(fee_bps, int) or isinstance(fee_bps, bool) or not (0 <= fee_bps <= 10_000):
        raise ValueError(f"fee_bps out of range: {fee_bps}")

    return {
        "i1": rin_hi,
        "i2": rin_lo,
        "i3": rout_hi,
        "i4": rout_lo,
        "i5": aout_hi,
        "i6": aout_lo,
        "i7": int(fee_bps),
        "i8": max_hi,
        "i9": max_lo,
        "i10": ain_hi,
        "i11": ain_lo,
        "i12": new_rin_hi,
        "i13": new_rin_lo,
        "i14": new_rout_hi,
        "i15": new_rout_lo,
    }


def build_swap_exact_out_v4_step(
    *,
    reserve_in: int,
    reserve_out: int,
    amount_out: int,
    fee_bps: int,
    max_amount_in: int,
    amount_in: int,
    new_reserve_in: int,
    new_reserve_out: int,
) -> Dict[str, int]:
    # v4 is bv[32]-native (no hi/lo limbs).
    if not isinstance(fee_bps, int) or isinstance(fee_bps, bool) or not (0 <= fee_bps <= 10_000):
        raise ValueError(f"fee_bps out of range: {fee_bps}")
    return {
        "i1": int(reserve_in),
        "i2": int(reserve_out),
        "i3": int(amount_out),
        "i4": int(fee_bps),
        "i5": int(max_amount_in),
        "i6": int(amount_in),
        "i7": int(new_reserve_in),
        "i8": int(new_reserve_out),
    }


def build_swap_exact_out_proof_gate_v1_step(
    *,
    reserve_in: int,
    reserve_out: int,
    amount_out: int,
    fee_bps: int,
    max_amount_in: int,
    amount_in: int,
    new_reserve_in: int,
    new_reserve_out: int,
    proof_ok: int = 1,
    binding_ok: int = 1,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/swap_exact_out_proof_gate_v1.tau`.
    """
    step = build_swap_exact_out_v4_step(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_out=amount_out,
        fee_bps=fee_bps,
        max_amount_in=max_amount_in,
        amount_in=amount_in,
        new_reserve_in=new_reserve_in,
        new_reserve_out=new_reserve_out,
    )
    step["i9"] = _sbf("proof_ok", proof_ok)
    step["i10"] = _sbf("binding_ok", binding_ok)
    return step


def build_swap_exact_out_v3_step(
    *,
    reserve_in: int,
    reserve_out: int,
    amount_out: int,
    fee_bps: int,
    max_amount_in: int,
    amount_in: int,
    new_reserve_in: int,
    new_reserve_out: int,
    k_old: int,
    k_new: int,
) -> Dict[str, int]:
    # v3 is bv[32] inputs plus precomputed bv[64] k values.
    if not isinstance(fee_bps, int) or isinstance(fee_bps, bool) or not (0 <= fee_bps <= 10_000):
        raise ValueError(f"fee_bps out of range: {fee_bps}")
    for name, v in (("k_old", k_old), ("k_new", k_new)):
        if not isinstance(v, int) or isinstance(v, bool) or v < 0 or v > 0xFFFFFFFFFFFFFFFF:
            raise ValueError(f"{name} out of u64 range: {v!r}")
    return {
        "i1": int(reserve_in),
        "i2": int(reserve_out),
        "i3": int(amount_out),
        "i4": int(fee_bps),
        "i5": int(max_amount_in),
        "i6": int(amount_in),
        "i7": int(new_reserve_in),
        "i8": int(new_reserve_out),
        "i9": int(k_old),
        "i10": int(k_new),
    }
