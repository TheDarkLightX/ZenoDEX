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


CPMM_V1 = TauSpecRef(
    spec_id="cpmm_v1",
    path=RECOMMENDED_SPECS_DIR / "cpmm_v1.tau",
    gate_output="o1",
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
