#!/usr/bin/env python3
"""Intent lattice + equivalence harness for Tau specs.

Runs two kinds of assurance checks for selected specs:
1) Trace comparison: Tau spec output vs Python model output on random traces.
2) Z3 equivalence: Spec logic (hi/lo) vs model logic (combined 32-bit), plus intent checks.

If z3-solver is not installed, Z3 checks are skipped.
"""
from __future__ import annotations

import argparse
import random
import re
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Dict, List, Tuple, Optional

ROOT = Path(__file__).resolve().parents[1]

sys.path.insert(0, str(ROOT))

try:
    from tests.tau import check_formal_completeness as cfc
except Exception:
    cfc = None

try:
    import z3  # type: ignore
    HAS_Z3 = True
except Exception:
    HAS_Z3 = False


# ---------- Helpers ----------

def combine32(hi: int, lo: int) -> int:
    return ((hi & 0xFFFF) << 16) | (lo & 0xFFFF)


def split32(val: int) -> Tuple[int, int]:
    return ((val >> 16) & 0xFFFF, val & 0xFFFF)


def add32(a: int, b: int) -> int:
    return (a + b) & 0xFFFFFFFF


def sub32(a: int, b: int) -> int:
    return (a - b) & 0xFFFFFFFF


def unsigned_gt(a: int, b: int) -> bool:
    return a > b


def unsigned_gte(a: int, b: int) -> bool:
    return a >= b


def bv16(val: int) -> int:
    return val & 0xFFFF


def bv16_add(a: int, b: int) -> int:
    return (a + b) & 0xFFFF


def bv16_sub(a: int, b: int) -> int:
    return (a - b) & 0xFFFF


def bv16_mul(a: int, b: int) -> int:
    return (a * b) & 0xFFFF


# ---------- Models ----------


def model_cpmm(inputs: Dict[str, int]) -> int:
    rin = combine32(inputs["i1"], inputs["i2"])
    rout = combine32(inputs["i3"], inputs["i4"])
    ain = combine32(inputs["i5"], inputs["i6"])
    fee = inputs["i7"]
    aout = combine32(inputs["i8"], inputs["i9"])
    ok = (
        rin > 0
        and rout > 0
        and ain > 0
        and 0 <= fee <= 10000
        and aout > 0
        and rout >= aout
    )
    return 1 if ok else 0


def model_swap_exact_in(inputs: Dict[str, int]) -> int:
    rin = combine32(inputs["i1"], inputs["i2"])
    rout = combine32(inputs["i3"], inputs["i4"])
    ain = combine32(inputs["i5"], inputs["i6"])
    fee = inputs["i7"]
    min_out = combine32(inputs["i8"], inputs["i9"])
    aout = combine32(inputs["i10"], inputs["i11"])
    new_rin = combine32(inputs["i12"], inputs["i13"])
    new_rout = combine32(inputs["i14"], inputs["i15"])
    ok = (
        rin > 0
        and rout > 0
        and ain > 0
        and 0 <= fee <= 10000
        and aout > 0
        and rout >= aout
        and aout >= min_out
        and new_rin == add32(rin, ain)
        and new_rout == sub32(rout, aout)
    )
    return 1 if ok else 0


def model_swap_exact_out(inputs: Dict[str, int]) -> int:
    rin = combine32(inputs["i1"], inputs["i2"])
    rout = combine32(inputs["i3"], inputs["i4"])
    aout = combine32(inputs["i5"], inputs["i6"])
    fee = inputs["i7"]
    max_in = combine32(inputs["i8"], inputs["i9"])
    ain = combine32(inputs["i10"], inputs["i11"])
    new_rin = combine32(inputs["i12"], inputs["i13"])
    new_rout = combine32(inputs["i14"], inputs["i15"])
    ok = (
        rin > 0
        and rout > 0
        and aout > 0
        and rout > aout
        and 0 <= fee <= 10000
        and ain > 0
        and max_in >= ain
        and new_rin == add32(rin, ain)
        and new_rout == sub32(rout, aout)
    )
    return 1 if ok else 0


def model_protocol_token(inputs: Dict[str, int]) -> int:
    f_before = combine32(inputs["i1"], inputs["i2"])
    t_before = combine32(inputs["i3"], inputs["i4"])
    s_before = combine32(inputs["i5"], inputs["i6"])
    amt = combine32(inputs["i7"], inputs["i8"])
    f_after = combine32(inputs["i9"], inputs["i10"])
    t_after = combine32(inputs["i11"], inputs["i12"])
    s_after = combine32(inputs["i13"], inputs["i14"])
    do_xfer = inputs["i15"] == 1
    do_mint = inputs["i16"] == 1
    do_burn = inputs["i17"] == 1
    one_hot = sum([do_xfer, do_mint, do_burn]) == 1
    amt_pos = amt > 0

    transfer = (
        amt_pos
        and f_after == sub32(f_before, amt)
        and t_after == add32(t_before, amt)
        and s_after == s_before
    )
    mint = (
        amt_pos
        and f_after == f_before
        and t_after == add32(t_before, amt)
        and s_after == add32(s_before, amt)
    )
    burn = (
        amt_pos
        and f_after == sub32(f_before, amt)
        and t_after == t_before
        and s_after == sub32(s_before, amt)
    )
    ok = one_hot and ((do_xfer and transfer) or (do_mint and mint) or (do_burn and burn))
    return 1 if ok else 0


def model_batch_canonical(inputs: Dict[str, int]) -> int:
    ids = [inputs["i1"], inputs["i2"], inputs["i3"], inputs["i4"]]
    ok = ids[0] < ids[1] < ids[2] < ids[3]
    return 1 if ok else 0


def model_batching_v1_4(inputs: Dict[str, int]) -> int:
    intent_ids = [inputs["i1"], inputs["i2"], inputs["i3"], inputs["i4"]]
    executed = [inputs["i5"], inputs["i6"], inputs["i7"], inputs["i8"]]
    all_distinct = len(set(intent_ids)) == 4
    members = all(x in intent_ids for x in executed)
    strictly_inc = executed[0] < executed[1] < executed[2] < executed[3]
    ok = all_distinct and members and strictly_inc
    return 1 if ok else 0


def model_settlement_v4(inputs: Dict[str, int]) -> int:
    # Canonical ordering
    canonical_ok = inputs["i1"] < inputs["i2"] < inputs["i3"] < inputs["i4"]

    # Anti-sandwich (using prevprev/prev/curr inputs)
    pprev = bv16(inputs["i5"])
    prev = bv16(inputs["i6"])
    curr = bv16(inputs["i7"])
    no_sandwich_ok = ((pprev <= prev <= curr) or (pprev >= prev >= curr))

    # Stability
    if curr >= prev:
        stable_ok = bv16_sub(curr, prev) < 0x0032
    else:
        stable_ok = bv16_sub(prev, curr) < 0x0032

    # CPMM
    rx = bv16(inputs["i8"])
    ry = bv16(inputs["i9"])
    net = bv16(inputs["i10"])
    out = bv16(inputs["i11"])
    cpmm_lhs = bv16_mul(out, bv16_add(rx, net))
    cpmm_rhs = bv16_mul(net, ry)
    cpmm_ok = cpmm_lhs <= cpmm_rhs

    # Balance transition (32-bit)
    bal_before = combine32(inputs["i12"], inputs["i13"])
    delta = combine32(inputs["i14"], inputs["i15"])
    bal_after = combine32(inputs["i16"], inputs["i17"])
    balance_ok = bal_after == sub32(bal_before, delta)

    # Protocol token transition
    tok_inputs = {
        "i1": inputs["i18"],
        "i2": inputs["i19"],
        "i3": inputs["i20"],
        "i4": inputs["i21"],
        "i5": inputs["i22"],
        "i6": inputs["i23"],
        "i7": inputs["i24"],
        "i8": inputs["i25"],
        "i9": inputs["i26"],
        "i10": inputs["i27"],
        "i11": inputs["i28"],
        "i12": inputs["i29"],
        "i13": inputs["i30"],
        "i14": inputs["i31"],
        "i15": inputs["i32"],
        "i16": inputs["i33"],
        "i17": inputs["i34"],
    }
    token_ok = model_protocol_token(tok_inputs) == 1

    # Buyback/burn floor
    trade_amount = bv16(inputs["i35"])
    fee = bv16(inputs["i36"])
    buyback = bv16(inputs["i37"])
    burned = bv16(inputs["i38"])
    floor = combine32(inputs["i39"], inputs["i40"])
    supply_before = combine32(inputs["i22"], inputs["i23"])
    supply_after = combine32(inputs["i30"], inputs["i31"])

    fee_rate_ok = (bv16_mul(fee, 0x2710) >= bv16_mul(trade_amount, 0x001D)) and (
        bv16_mul(fee, 0x2710) <= bv16_add(bv16_mul(trade_amount, 0x001D), 0x270F)
    )
    buyback_share_ok = (bv16_mul(buyback, 0x0064) >= bv16_mul(fee, 0x0015)) and (
        bv16_mul(buyback, 0x0064) <= bv16_add(bv16_mul(fee, 0x0015), 0x0063)
    )
    floor_reached = supply_before <= floor
    if floor_reached:
        burn_floor_ok = (burned == 0) and (supply_after == supply_before)
    else:
        expected_after = sub32(supply_before, burned)
        burn_floor_ok = (burned == buyback) and (supply_after == expected_after) and (supply_after >= floor)

    o7 = fee_rate_ok and buyback_share_ok and burn_floor_ok

    scale = bv16(inputs["i41"])
    unit_ok = (
        scale != 0
        and (trade_amount % scale == 0)
        and (fee % scale == 0)
        and (buyback % scale == 0)
        and (burned % scale == 0)
    )
    o8 = o7 and unit_ok

    # Rebate
    rebate_rate = bv16(inputs["i42"])
    rebate = bv16(inputs["i43"])
    rebate_cap = bv16(inputs["i44"])
    rebate_rate_ok = (bv16_mul(rebate, 0x2710) >= bv16_mul(fee, rebate_rate)) and (
        bv16_mul(rebate, 0x2710) <= bv16_add(bv16_mul(fee, rebate_rate), 0x270F)
    )
    rebate_cap_ok = (rebate <= rebate_cap) and (rebate <= fee)
    o9 = rebate_rate_ok and rebate_cap_ok

    # Lock weighting
    lock_days = bv16(inputs["i45"])
    stake = bv16(inputs["i46"])
    t1 = bv16(inputs["i47"])
    t2 = bv16(inputs["i48"])
    w1 = bv16(inputs["i49"])
    w2 = bv16(inputs["i50"])
    w3 = bv16(inputs["i51"])
    w_claimed = bv16(inputs["i52"])
    weighted_stake = bv16(inputs["i53"])

    thresholds_ok = t1 < t2
    if lock_days < t1:
        weight_ok = w_claimed == w1
    elif lock_days < t2:
        weight_ok = w_claimed == w2
    else:
        weight_ok = w_claimed == w3
    weighted_stake_ok = weighted_stake == bv16_mul(stake, w_claimed)
    o10 = thresholds_ok and weight_ok and weighted_stake_ok

    settlement_ok = canonical_ok and no_sandwich_ok and stable_ok and cpmm_ok and balance_ok and token_ok and o8 and o9 and o10
    return 1 if settlement_ok else 0


# ---------- Intent lattice (selected specs) ----------


def intent_protocol_token_no_underflow(inputs: Dict[str, int]) -> bool:
    f_before = combine32(inputs["i1"], inputs["i2"])
    s_before = combine32(inputs["i5"], inputs["i6"])
    amt = combine32(inputs["i7"], inputs["i8"])
    do_xfer = inputs["i15"] == 1
    do_burn = inputs["i17"] == 1
    ok = True
    if do_xfer:
        ok = ok and (f_before >= amt)
    if do_burn:
        ok = ok and (f_before >= amt) and (s_before >= amt)
    return ok


def intent_swap_exact_in_bounds(inputs: Dict[str, int]) -> bool:
    rout = combine32(inputs["i3"], inputs["i4"])
    aout = combine32(inputs["i10"], inputs["i11"])
    min_out = combine32(inputs["i8"], inputs["i9"])
    return (rout >= aout) and (aout >= min_out)


def intent_swap_exact_out_bounds(inputs: Dict[str, int]) -> bool:
    rout = combine32(inputs["i3"], inputs["i4"])
    aout = combine32(inputs["i5"], inputs["i6"])
    max_in = combine32(inputs["i8"], inputs["i9"])
    ain = combine32(inputs["i10"], inputs["i11"])
    return (rout > aout) and (max_in >= ain)


# ---------- Z3 encoding ----------


def bv16(name: str):
    return z3.BitVec(name, 16)


def bv32(name: str):
    return z3.BitVec(name, 32)


def bv64(name: str):
    return z3.BitVec(name, 64)


def b2bv16(b):
    return z3.If(b, z3.BitVecVal(1, 16), z3.BitVecVal(0, 16))


def b2bv32(b):
    return z3.If(b, z3.BitVecVal(1, 32), z3.BitVecVal(0, 32))


def z3_add32(a_hi, a_lo, b_hi, b_lo):
    sum_lo = a_lo + b_lo
    carry = z3.ULT(sum_lo, a_lo)
    sum_hi = a_hi + b_hi + b2bv16(carry)
    return sum_hi, sum_lo


def z3_sub32(a_hi, a_lo, b_hi, b_lo):
    diff_lo = a_lo - b_lo
    borrow = z3.ULT(a_lo, b_lo)
    diff_hi = a_hi - b_hi - b2bv16(borrow)
    return diff_hi, diff_lo


def z3_value_gte(hi1, lo1, hi2, lo2):
    return z3.Or(z3.UGT(hi1, hi2), z3.And(hi1 == hi2, z3.UGE(lo1, lo2)))


def z3_value_gt(hi1, lo1, hi2, lo2):
    return z3.Or(z3.UGT(hi1, hi2), z3.And(hi1 == hi2, z3.UGT(lo1, lo2)))


def z3_ge_32(hi1, lo1, hi2, lo2):
    return z3_value_gte(hi1, lo1, hi2, lo2)


def z3_le_32(hi1, lo1, hi2, lo2):
    return z3_value_gte(hi2, lo2, hi1, lo1)


def z3_is_positive(hi, lo):
    return z3.Or(z3.UGT(hi, z3.BitVecVal(0, 16)), z3.And(hi == z3.BitVecVal(0, 16), z3.UGT(lo, z3.BitVecVal(0, 16))))


def z3_fee_ok(fee):
    return z3.And(z3.UGE(fee, z3.BitVecVal(0, 16)), z3.ULE(fee, z3.BitVecVal(10000, 16)))


def z3_combine32(hi, lo):
    return z3.ZeroExt(16, hi) << 16 | z3.ZeroExt(16, lo)


def z3_cpmm_spec(vars):
    i1, i2, i3, i4, i5, i6, i7, i8, i9 = vars
    return z3.And(
        z3_is_positive(i1, i2),
        z3_is_positive(i3, i4),
        z3_is_positive(i5, i6),
        z3_fee_ok(i7),
        z3_is_positive(i8, i9),
        z3_value_gte(i3, i4, i8, i9),
    )


def z3_cpmm_model(vars):
    i1, i2, i3, i4, i5, i6, i7, i8, i9 = vars
    rin = z3_combine32(i1, i2)
    rout = z3_combine32(i3, i4)
    ain = z3_combine32(i5, i6)
    aout = z3_combine32(i8, i9)
    return z3.And(
        z3.UGT(rin, z3.BitVecVal(0, 32)),
        z3.UGT(rout, z3.BitVecVal(0, 32)),
        z3.UGT(ain, z3.BitVecVal(0, 32)),
        z3.UGE(i7, z3.BitVecVal(0, 16)),
        z3.ULE(i7, z3.BitVecVal(10000, 16)),
        z3.UGT(aout, z3.BitVecVal(0, 32)),
        z3.UGE(rout, aout),
    )


def z3_swap_exact_in_spec(vars):
    (i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15) = vars
    sum_hi, sum_lo = z3_add32(i1, i2, i5, i6)
    diff_hi, diff_lo = z3_sub32(i3, i4, i10, i11)
    return z3.And(
        z3_is_positive(i1, i2),
        z3_is_positive(i3, i4),
        z3_is_positive(i5, i6),
        z3_fee_ok(i7),
        z3_is_positive(i10, i11),
        z3_value_gte(i3, i4, i10, i11),
        z3_value_gte(i10, i11, i8, i9),
        i12 == sum_hi,
        i13 == sum_lo,
        i14 == diff_hi,
        i15 == diff_lo,
    )


def z3_swap_exact_in_model(vars):
    (i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15) = vars
    rin = z3_combine32(i1, i2)
    rout = z3_combine32(i3, i4)
    ain = z3_combine32(i5, i6)
    min_out = z3_combine32(i8, i9)
    aout = z3_combine32(i10, i11)
    new_rin = z3_combine32(i12, i13)
    new_rout = z3_combine32(i14, i15)
    return z3.And(
        z3.UGT(rin, z3.BitVecVal(0, 32)),
        z3.UGT(rout, z3.BitVecVal(0, 32)),
        z3.UGT(ain, z3.BitVecVal(0, 32)),
        z3.UGE(i7, z3.BitVecVal(0, 16)),
        z3.ULE(i7, z3.BitVecVal(10000, 16)),
        z3.UGT(aout, z3.BitVecVal(0, 32)),
        z3.UGE(rout, aout),
        z3.UGE(aout, min_out),
        new_rin == rin + ain,
        new_rout == rout - aout,
    )


def z3_swap_exact_out_spec(vars):
    (i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15) = vars
    sum_hi, sum_lo = z3_add32(i1, i2, i10, i11)
    diff_hi, diff_lo = z3_sub32(i3, i4, i5, i6)
    return z3.And(
        z3_is_positive(i1, i2),
        z3_is_positive(i3, i4),
        z3_is_positive(i5, i6),
        z3_value_gt(i3, i4, i5, i6),
        z3_fee_ok(i7),
        z3_is_positive(i10, i11),
        z3_value_gte(i8, i9, i10, i11),
        i12 == sum_hi,
        i13 == sum_lo,
        i14 == diff_hi,
        i15 == diff_lo,
    )


def z3_swap_exact_out_model(vars):
    (i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15) = vars
    rin = z3_combine32(i1, i2)
    rout = z3_combine32(i3, i4)
    aout = z3_combine32(i5, i6)
    max_in = z3_combine32(i8, i9)
    ain = z3_combine32(i10, i11)
    new_rin = z3_combine32(i12, i13)
    new_rout = z3_combine32(i14, i15)
    return z3.And(
        z3.UGT(rin, z3.BitVecVal(0, 32)),
        z3.UGT(rout, z3.BitVecVal(0, 32)),
        z3.UGT(aout, z3.BitVecVal(0, 32)),
        z3.UGT(rout, aout),
        z3.UGE(i7, z3.BitVecVal(0, 16)),
        z3.ULE(i7, z3.BitVecVal(10000, 16)),
        z3.UGT(ain, z3.BitVecVal(0, 32)),
        z3.UGE(max_in, ain),
        new_rin == rin + ain,
        new_rout == rout - aout,
    )


def z3_protocol_token_spec(vars):
    (i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16, i17) = vars
    one_hot = z3.Or(
        z3.And(i15 == z3.BitVecVal(1, 1), i16 == z3.BitVecVal(0, 1), i17 == z3.BitVecVal(0, 1)),
        z3.And(i15 == z3.BitVecVal(0, 1), i16 == z3.BitVecVal(1, 1), i17 == z3.BitVecVal(0, 1)),
        z3.And(i15 == z3.BitVecVal(0, 1), i16 == z3.BitVecVal(0, 1), i17 == z3.BitVecVal(1, 1)),
    )
    amt_pos = z3_is_positive(i7, i8)
    # transfer
    t_hi, t_lo = z3_sub32(i1, i2, i7, i8)
    t2_hi, t2_lo = z3_add32(i3, i4, i7, i8)
    transfer_valid = z3.And(
        amt_pos,
        i9 == t_hi,
        i10 == t_lo,
        i11 == t2_hi,
        i12 == t2_lo,
        i13 == i5,
        i14 == i6,
    )
    # mint
    m_hi, m_lo = z3_add32(i3, i4, i7, i8)
    s_hi, s_lo = z3_add32(i5, i6, i7, i8)
    mint_valid = z3.And(
        amt_pos,
        i9 == i1,
        i10 == i2,
        i11 == m_hi,
        i12 == m_lo,
        i13 == s_hi,
        i14 == s_lo,
    )
    # burn
    b_hi, b_lo = z3_sub32(i1, i2, i7, i8)
    s2_hi, s2_lo = z3_sub32(i5, i6, i7, i8)
    burn_valid = z3.And(
        amt_pos,
        i9 == b_hi,
        i10 == b_lo,
        i11 == i3,
        i12 == i4,
        i13 == s2_hi,
        i14 == s2_lo,
    )
    return z3.And(one_hot, z3.Or(z3.And(i15 == z3.BitVecVal(1, 1), transfer_valid), z3.And(i16 == z3.BitVecVal(1, 1), mint_valid), z3.And(i17 == z3.BitVecVal(1, 1), burn_valid)))


def z3_protocol_token_model(vars):
    (i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16, i17) = vars
    f_before = z3_combine32(i1, i2)
    t_before = z3_combine32(i3, i4)
    s_before = z3_combine32(i5, i6)
    amt = z3_combine32(i7, i8)
    f_after = z3_combine32(i9, i10)
    t_after = z3_combine32(i11, i12)
    s_after = z3_combine32(i13, i14)

    do_xfer = i15 == z3.BitVecVal(1, 1)
    do_mint = i16 == z3.BitVecVal(1, 1)
    do_burn = i17 == z3.BitVecVal(1, 1)
    one_hot = z3.Or(
        z3.And(do_xfer, z3.Not(do_mint), z3.Not(do_burn)),
        z3.And(do_mint, z3.Not(do_xfer), z3.Not(do_burn)),
        z3.And(do_burn, z3.Not(do_xfer), z3.Not(do_mint)),
    )
    amt_pos = z3.UGT(amt, z3.BitVecVal(0, 32))

    transfer = z3.And(
        amt_pos,
        f_after == f_before - amt,
        t_after == t_before + amt,
        s_after == s_before,
    )
    mint = z3.And(
        amt_pos,
        f_after == f_before,
        t_after == t_before + amt,
        s_after == s_before + amt,
    )
    burn = z3.And(
        amt_pos,
        f_after == f_before - amt,
        t_after == t_before,
        s_after == s_before - amt,
    )
    return z3.And(one_hot, z3.Or(z3.And(do_xfer, transfer), z3.And(do_mint, mint), z3.And(do_burn, burn)))


def z3_batch_canonical_spec(vars):
    i1, i2, i3, i4 = vars
    return z3.And(z3.ULT(i1, i2), z3.ULT(i2, i3), z3.ULT(i3, i4))


def z3_batch_canonical_model(vars):
    i1, i2, i3, i4 = vars
    return z3.And(z3.ULT(i1, i2), z3.ULT(i2, i3), z3.ULT(i3, i4))


def z3_batching_v1_4_spec(vars):
    i1, i2, i3, i4, i5, i6, i7, i8 = vars
    all_distinct = z3.And(i1 != i2, i1 != i3, i1 != i4, i2 != i3, i2 != i4, i3 != i4)
    member_5 = z3.Or(i5 == i1, i5 == i2, i5 == i3, i5 == i4)
    member_6 = z3.Or(i6 == i1, i6 == i2, i6 == i3, i6 == i4)
    member_7 = z3.Or(i7 == i1, i7 == i2, i7 == i3, i7 == i4)
    member_8 = z3.Or(i8 == i1, i8 == i2, i8 == i3, i8 == i4)
    strictly_inc = z3.And(z3.ULT(i5, i6), z3.ULT(i6, i7), z3.ULT(i7, i8))
    return z3.And(all_distinct, member_5, member_6, member_7, member_8, strictly_inc)


def z3_batching_v1_4_model(vars):
    return z3_batching_v1_4_spec(vars)


def z3_settlement_v4_spec(vars):
    # vars are i1..i53 (all bv16 except i32..i34 are bv1)
    (i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11,
     i12, i13, i14, i15, i16, i17,
     i18, i19, i20, i21, i22, i23, i24, i25, i26, i27, i28, i29, i30, i31,
     i32, i33, i34,
     i35, i36, i37, i38, i39, i40, i41, i42, i43, i44, i45, i46, i47, i48,
     i49, i50, i51, i52, i53) = vars

    canonical_ok = z3.And(z3.ULT(i1, i2), z3.ULT(i2, i3), z3.ULT(i3, i4))
    no_sandwich_ok = z3.Or(z3.And(z3.ULE(i5, i6), z3.ULE(i6, i7)), z3.And(z3.UGE(i5, i6), z3.UGE(i6, i7)))
    stable_ok = z3.Or(
        z3.And(z3.UGE(i7, i6), z3.ULT(i7 - i6, z3.BitVecVal(0x0032, 16))),
        z3.And(z3.ULT(i7, i6), z3.ULT(i6 - i7, z3.BitVecVal(0x0032, 16))),
    )
    cpmm_ok = z3.ULE(i11 * (i8 + i10), i10 * i9)

    # Balance transition (hi/lo)
    bal_hi, bal_lo = z3_sub32(i12, i13, i14, i15)
    balance_ok = z3.And(i16 == bal_hi, i17 == bal_lo)

    # Token transition (hi/lo)
    token_vars = (i18, i19, i20, i21, i22, i23, i24, i25, i26, i27, i28, i29, i30, i31, i32, i33, i34)
    token_ok = z3_protocol_token_spec(token_vars)

    # Fee + buyback + burn floor
    fee_rate_ok = z3.And(
        z3.UGE(i36 * z3.BitVecVal(0x2710, 16), i35 * z3.BitVecVal(0x001D, 16)),
        z3.ULE(i36 * z3.BitVecVal(0x2710, 16), (i35 * z3.BitVecVal(0x001D, 16)) + z3.BitVecVal(0x270F, 16)),
    )
    buyback_share_ok = z3.And(
        z3.UGE(i37 * z3.BitVecVal(0x0064, 16), i36 * z3.BitVecVal(0x0015, 16)),
        z3.ULE(i37 * z3.BitVecVal(0x0064, 16), (i36 * z3.BitVecVal(0x0015, 16)) + z3.BitVecVal(0x0063, 16)),
    )
    floor_reached = z3_le_32(i22, i23, i39, i40)
    supply_eq = z3.And(i30 == i22, i31 == i23)
    burn_sub_hi, burn_sub_lo = z3_sub32(i22, i23, z3.BitVecVal(0, 16), i38)
    burn_floor_ok = z3.Or(
        z3.And(floor_reached, i38 == z3.BitVecVal(0, 16), supply_eq),
        z3.And(
            z3.Not(floor_reached),
            i38 == i37,
            i30 == burn_sub_hi,
            i31 == burn_sub_lo,
            z3_ge_32(i30, i31, i39, i40),
        ),
    )
    o7 = z3.And(fee_rate_ok, buyback_share_ok, burn_floor_ok)
    unit_ok = z3.And(
        i41 != z3.BitVecVal(0, 16),
        z3.URem(i35, i41) == z3.BitVecVal(0, 16),
        z3.URem(i36, i41) == z3.BitVecVal(0, 16),
        z3.URem(i37, i41) == z3.BitVecVal(0, 16),
        z3.URem(i38, i41) == z3.BitVecVal(0, 16),
    )
    o8 = z3.And(o7, unit_ok)

    # Rebate
    rebate_rate_ok = z3.And(
        z3.UGE(i43 * z3.BitVecVal(0x2710, 16), i36 * i42),
        z3.ULE(i43 * z3.BitVecVal(0x2710, 16), (i36 * i42) + z3.BitVecVal(0x270F, 16)),
    )
    rebate_cap_ok = z3.And(z3.ULE(i43, i44), z3.ULE(i43, i36))
    o9 = z3.And(rebate_rate_ok, rebate_cap_ok)

    # Lock weighting
    thresholds_ok = z3.ULT(i47, i48)
    weight_tier_ok = z3.Or(
        z3.And(z3.ULT(i45, i47), i52 == i49),
        z3.And(z3.UGE(i45, i47), z3.ULT(i45, i48), i52 == i50),
        z3.And(z3.UGE(i45, i48), i52 == i51),
    )
    weighted_stake_ok = i53 == i46 * i52
    o10 = z3.And(thresholds_ok, weight_tier_ok, weighted_stake_ok)

    return z3.And(canonical_ok, no_sandwich_ok, stable_ok, cpmm_ok, balance_ok, token_ok, o8, o9, o10)


def z3_settlement_v4_model(vars):
    (i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11,
     i12, i13, i14, i15, i16, i17,
     i18, i19, i20, i21, i22, i23, i24, i25, i26, i27, i28, i29, i30, i31,
     i32, i33, i34,
     i35, i36, i37, i38, i39, i40, i41, i42, i43, i44, i45, i46, i47, i48,
     i49, i50, i51, i52, i53) = vars

    canonical_ok = z3.And(z3.ULT(i1, i2), z3.ULT(i2, i3), z3.ULT(i3, i4))
    no_sandwich_ok = z3.Or(z3.And(z3.ULE(i5, i6), z3.ULE(i6, i7)), z3.And(z3.UGE(i5, i6), z3.UGE(i6, i7)))
    stable_ok = z3.Or(
        z3.And(z3.UGE(i7, i6), z3.ULT(i7 - i6, z3.BitVecVal(0x0032, 16))),
        z3.And(z3.ULT(i7, i6), z3.ULT(i6 - i7, z3.BitVecVal(0x0032, 16))),
    )
    cpmm_ok = z3.ULE(i11 * (i8 + i10), i10 * i9)

    # Balance transition (32-bit)
    bal_before = z3_combine32(i12, i13)
    delta = z3_combine32(i14, i15)
    bal_after = z3_combine32(i16, i17)
    balance_ok = bal_after == bal_before - delta

    # Token transition (32-bit)
    token_vars = (i18, i19, i20, i21, i22, i23, i24, i25, i26, i27, i28, i29, i30, i31, i32, i33, i34)
    token_ok = z3_protocol_token_model(token_vars)

    fee_rate_ok = z3.And(
        z3.UGE(i36 * z3.BitVecVal(0x2710, 16), i35 * z3.BitVecVal(0x001D, 16)),
        z3.ULE(i36 * z3.BitVecVal(0x2710, 16), (i35 * z3.BitVecVal(0x001D, 16)) + z3.BitVecVal(0x270F, 16)),
    )
    buyback_share_ok = z3.And(
        z3.UGE(i37 * z3.BitVecVal(0x0064, 16), i36 * z3.BitVecVal(0x0015, 16)),
        z3.ULE(i37 * z3.BitVecVal(0x0064, 16), (i36 * z3.BitVecVal(0x0015, 16)) + z3.BitVecVal(0x0063, 16)),
    )
    supply_before = z3_combine32(i22, i23)
    supply_after = z3_combine32(i30, i31)
    floor = z3_combine32(i39, i40)
    floor_reached = z3.ULE(supply_before, floor)
    burned = z3.ZeroExt(16, i38)
    burn_floor_ok = z3.Or(
        z3.And(floor_reached, i38 == z3.BitVecVal(0, 16), supply_after == supply_before),
        z3.And(z3.Not(floor_reached), i38 == i37, supply_after == supply_before - burned, z3.UGE(supply_after, floor)),
    )
    o7 = z3.And(fee_rate_ok, buyback_share_ok, burn_floor_ok)
    unit_ok = z3.And(
        i41 != z3.BitVecVal(0, 16),
        z3.URem(i35, i41) == z3.BitVecVal(0, 16),
        z3.URem(i36, i41) == z3.BitVecVal(0, 16),
        z3.URem(i37, i41) == z3.BitVecVal(0, 16),
        z3.URem(i38, i41) == z3.BitVecVal(0, 16),
    )
    o8 = z3.And(o7, unit_ok)

    rebate_rate_ok = z3.And(
        z3.UGE(i43 * z3.BitVecVal(0x2710, 16), i36 * i42),
        z3.ULE(i43 * z3.BitVecVal(0x2710, 16), (i36 * i42) + z3.BitVecVal(0x270F, 16)),
    )
    rebate_cap_ok = z3.And(z3.ULE(i43, i44), z3.ULE(i43, i36))
    o9 = z3.And(rebate_rate_ok, rebate_cap_ok)

    thresholds_ok = z3.ULT(i47, i48)
    weight_tier_ok = z3.Or(
        z3.And(z3.ULT(i45, i47), i52 == i49),
        z3.And(z3.UGE(i45, i47), z3.ULT(i45, i48), i52 == i50),
        z3.And(z3.UGE(i45, i48), i52 == i51),
    )
    weighted_stake_ok = i53 == i46 * i52
    o10 = z3.And(thresholds_ok, weight_tier_ok, weighted_stake_ok)

    return z3.And(canonical_ok, no_sandwich_ok, stable_ok, cpmm_ok, balance_ok, token_ok, o8, o9, o10)


def z3_intent_protocol_token_no_underflow(vars):
    (i1, i2, _, _, i5, i6, i7, i8, *rest) = vars
    f_before = z3_combine32(i1, i2)
    s_before = z3_combine32(i5, i6)
    amt = z3_combine32(i7, i8)
    i15, i16, i17 = rest[-3:]
    do_xfer = i15 == z3.BitVecVal(1, 1)
    do_burn = i17 == z3.BitVecVal(1, 1)
    return z3.And(
        z3.Implies(do_xfer, z3.UGE(f_before, amt)),
        z3.Implies(do_burn, z3.And(z3.UGE(f_before, amt), z3.UGE(s_before, amt))),
    )


@dataclass
class SpecHarness:
    name: str
    path: Path
    inputs: List[str]
    model: Callable[[Dict[str, int]], int]
    intents: List[Tuple[str, Callable[[Dict[str, int]], bool]]]
    z3_spec: Callable
    z3_model: Callable
    z3_intents: List[Tuple[str, Callable]]
    input_widths: Optional[Dict[str, int]] = None
    output: str = "o1"
    trace_enabled: bool = True


def build_harnesses() -> Dict[str, SpecHarness]:
    base = ROOT / "src" / "tau_specs"
    recommended = base / "recommended"
    return {
        "cpmm_v1": SpecHarness(
            name="cpmm_v1",
            path=base / "cpmm_v1.tau",
            inputs=[f"i{n}" for n in range(1, 10)],
            model=model_cpmm,
            intents=[],
            z3_spec=z3_cpmm_spec,
            z3_model=z3_cpmm_model,
            z3_intents=[],
        ),
        "swap_exact_in_v1": SpecHarness(
            name="swap_exact_in_v1",
            path=base / "swap_exact_in_v1.tau",
            inputs=[f"i{n}" for n in range(1, 16)],
            model=model_swap_exact_in,
            intents=[("bounds", intent_swap_exact_in_bounds)],
            z3_spec=z3_swap_exact_in_spec,
            z3_model=z3_swap_exact_in_model,
            z3_intents=[],
        ),
        "swap_exact_out_v1": SpecHarness(
            name="swap_exact_out_v1",
            path=base / "swap_exact_out_v1.tau",
            inputs=[f"i{n}" for n in range(1, 16)],
            model=model_swap_exact_out,
            intents=[("bounds", intent_swap_exact_out_bounds)],
            z3_spec=z3_swap_exact_out_spec,
            z3_model=z3_swap_exact_out_model,
            z3_intents=[],
        ),
        "protocol_token_v1": SpecHarness(
            name="protocol_token_v1",
            path=base / "protocol_token_v1.tau",
            inputs=[f"i{n}" for n in range(1, 18)],
            model=model_protocol_token,
            intents=[("no_underflow", intent_protocol_token_no_underflow)],
            z3_spec=z3_protocol_token_spec,
            z3_model=z3_protocol_token_model,
            z3_intents=[("no_underflow", z3_intent_protocol_token_no_underflow)],
            input_widths={"i15": 1, "i16": 1, "i17": 1},
        ),
        "batch_canonical_v1_4": SpecHarness(
            name="batch_canonical_v1_4",
            path=recommended / "batch_canonical_v1_4.tau",
            inputs=[f"i{n}" for n in range(1, 5)],
            model=model_batch_canonical,
            intents=[],
            z3_spec=z3_batch_canonical_spec,
            z3_model=z3_batch_canonical_model,
            z3_intents=[],
            input_widths={f"i{n}": 64 for n in range(1, 5)},
        ),
        "batching_v1_4": SpecHarness(
            name="batching_v1_4",
            path=recommended / "batching_v1_4.tau",
            inputs=[f"i{n}" for n in range(1, 9)],
            model=model_batching_v1_4,
            intents=[],
            z3_spec=z3_batching_v1_4_spec,
            z3_model=z3_batching_v1_4_model,
            z3_intents=[],
            input_widths={f"i{n}": 64 for n in range(1, 9)},
        ),
        "settlement_v4_buyback_floor_rebate_lock": SpecHarness(
            name="settlement_v4_buyback_floor_rebate_lock",
            path=recommended / "settlement_v4_buyback_floor_rebate_lock.tau",
            inputs=[f"i{n}" for n in range(1, 54)],
            model=model_settlement_v4,
            intents=[],
            z3_spec=z3_settlement_v4_spec,
            z3_model=z3_settlement_v4_model,
            z3_intents=[],
            input_widths={
                **{f"i{n}": 16 for n in range(1, 54)},
                "i32": 1,
                "i33": 1,
                "i34": 1,
            },
            output="o11",
            trace_enabled=False,
        ),
    }


def random_input(spec: SpecHarness) -> Dict[str, int]:
    values: Dict[str, int] = {}
    for name in spec.inputs:
        idx = int(name[1:])
        width = 16
        if spec.input_widths and name in spec.input_widths:
            width = spec.input_widths[name]
        if width == 1:
            values[name] = random.randint(0, 1)
            continue
        if width == 64:
            values[name] = random.getrandbits(64)
            continue
        # fee bps inputs (i7) for swaps, cpmm
        if spec.name in ("cpmm_v1", "swap_exact_in_v1", "swap_exact_out_v1") and idx == 7:
            values[name] = random.randint(0, 10000)
            continue
        values[name] = random.randint(0, 0xFFFF)
    return values


def deterministic_vectors(spec: SpecHarness) -> List[Dict[str, int]]:
    vectors: List[Dict[str, int]] = []
    if spec.name == "swap_exact_in_v1":
        def case(rin, rout, ain, fee, min_out, aout, new_rin, new_rout):
            rin_hi, rin_lo = split32(rin)
            rout_hi, rout_lo = split32(rout)
            ain_hi, ain_lo = split32(ain)
            min_hi, min_lo = split32(min_out)
            aout_hi, aout_lo = split32(aout)
            new_rin_hi, new_rin_lo = split32(new_rin)
            new_rout_hi, new_rout_lo = split32(new_rout)
            return {
                "i1": rin_hi, "i2": rin_lo,
                "i3": rout_hi, "i4": rout_lo,
                "i5": ain_hi, "i6": ain_lo,
                "i7": fee,
                "i8": min_hi, "i9": min_lo,
                "i10": aout_hi, "i11": aout_lo,
                "i12": new_rin_hi, "i13": new_rin_lo,
                "i14": new_rout_hi, "i15": new_rout_lo,
            }
        vectors.append(case(1000, 2000, 100, 30, 50, 60, 1100, 1940))
        vectors.append(case(1000, 2000, 100, 30, 70, 60, 1100, 1940))  # min_out too high
        vectors.append(case(1000, 2000, 100, 30, 50, 60, 1200, 1940))  # bad new reserve
        vectors.append(case(1000, 2000, 100, 30, 50, 2100, 1100, 1900))  # out too large

    if spec.name == "swap_exact_out_v1":
        def case(rin, rout, aout, fee, max_in, ain, new_rin, new_rout):
            rin_hi, rin_lo = split32(rin)
            rout_hi, rout_lo = split32(rout)
            aout_hi, aout_lo = split32(aout)
            max_hi, max_lo = split32(max_in)
            ain_hi, ain_lo = split32(ain)
            new_rin_hi, new_rin_lo = split32(new_rin)
            new_rout_hi, new_rout_lo = split32(new_rout)
            return {
                "i1": rin_hi, "i2": rin_lo,
                "i3": rout_hi, "i4": rout_lo,
                "i5": aout_hi, "i6": aout_lo,
                "i7": fee,
                "i8": max_hi, "i9": max_lo,
                "i10": ain_hi, "i11": ain_lo,
                "i12": new_rin_hi, "i13": new_rin_lo,
                "i14": new_rout_hi, "i15": new_rout_lo,
            }
        vectors.append(case(5000, 8000, 400, 30, 600, 550, 5550, 7600))
        vectors.append(case(5000, 8000, 400, 30, 500, 550, 5550, 7600))  # max_in too low
        vectors.append(case(5000, 8000, 9000, 30, 10000, 550, 5550, 7000))  # out too large
        vectors.append(case(5000, 8000, 400, 30, 600, 550, 5600, 7600))  # bad new reserve

    if spec.name == "protocol_token_v1":
        def case(f_before, t_before, s_before, amt, f_after, t_after, s_after, do_tr, do_m, do_b):
            f_hi, f_lo = split32(f_before)
            t_hi, t_lo = split32(t_before)
            s_hi, s_lo = split32(s_before)
            a_hi, a_lo = split32(amt)
            f2_hi, f2_lo = split32(f_after)
            t2_hi, t2_lo = split32(t_after)
            s2_hi, s2_lo = split32(s_after)
            return {
                "i1": f_hi, "i2": f_lo,
                "i3": t_hi, "i4": t_lo,
                "i5": s_hi, "i6": s_lo,
                "i7": a_hi, "i8": a_lo,
                "i9": f2_hi, "i10": f2_lo,
                "i11": t2_hi, "i12": t2_lo,
                "i13": s2_hi, "i14": s2_lo,
                "i15": do_tr, "i16": do_m, "i17": do_b,
            }
        vectors.append(case(1000, 2000, 10000, 250, 750, 2250, 10000, 1, 0, 0))
        vectors.append(case(1000, 2000, 10000, 250, 1000, 2250, 10250, 0, 1, 0))
        vectors.append(case(1000, 2000, 10000, 250, 750, 2000, 9750, 0, 0, 1))
        vectors.append(case(1000, 2000, 10000, 250, 750, 2250, 10000, 1, 1, 0))  # one_hot violated
        vectors.append(case(1000, 2000, 10000, 0, 1000, 2000, 10000, 1, 0, 0))  # zero amount

    return vectors


def run_trace(spec: SpecHarness, traces: int, seed: int, timeout: int, deterministic: bool) -> Tuple[int, List[str]]:
    failures: List[str] = []
    if cfc is None:
        return 0, ["check_formal_completeness module not available"]
    try:
        tau_bin = cfc.find_tau_bin()
    except Exception as exc:
        return 0, [f"Tau binary not found: {exc}"]

    inputs: List[Dict[str, int]] = []
    if deterministic:
        inputs.extend(deterministic_vectors(spec))
    random.seed(seed)
    inputs.extend(random_input(spec) for _ in range(traces))
    if not inputs:
        return 0, []
    spec_text = spec.path.read_text()
    stream_indices = sorted({int(m.group(1)) for m in re.finditer(r"\bi(\d+)\[", spec_text)})
    normalized = normalize_spec_text(spec.path.read_text())
    with tempfile.TemporaryDirectory() as tmpdir:
        tmp_path = Path(tmpdir) / f"{spec.name}_normalized.tau"
        tmp_path.write_text(normalized)
        outputs_by_step, trace_errors = cfc.run_tau_spec_trace(tau_bin, tmp_path, inputs, stream_indices, timeout=timeout)
    if trace_errors:
        return 0, trace_errors

    mismatches = 0
    for step, step_inputs in enumerate(inputs):
        expected = spec.model(step_inputs)
        got = outputs_by_step.get(step, {}).get(spec.output)
        if got is None:
            failures.append(f"step {step}: missing {spec.output}")
            mismatches += 1
            continue
        if int(got) != int(expected):
            failures.append(f"step {step}: expected o1={expected} got {got}")
            mismatches += 1
    return mismatches, failures


def normalize_spec_text(text: str) -> str:
    """Strip comments, remove `set charvar`, and collapse multi-line always blocks."""
    lines: List[str] = []
    raw = text.splitlines()
    i = 0
    while i < len(raw):
        line = raw[i]
        stripped = line.strip()
        if stripped.startswith("#"):
            i += 1
            continue
        if stripped.startswith("set charvar"):
            i += 1
            continue
        if stripped.startswith("always"):
            expr_parts: List[str] = []
            tail = stripped[len("always"):].strip()
            if tail:
                expr_parts.append(tail)
            i += 1
            while i < len(raw):
                nxt = raw[i].strip()
                if nxt.startswith("#"):
                    i += 1
                    continue
                expr_parts.append(nxt)
                if nxt.endswith("."):
                    break
                i += 1
            joined = " ".join(expr_parts)
            if joined.endswith("."):
                joined = joined[:-1]
            lines.append(f"always {joined}.")
            i += 1
            continue
        if stripped:
            lines.append(stripped)
        i += 1
    return "\n".join(lines) + "\n"
def run_intent_traces(spec: SpecHarness, traces: int, seed: int) -> List[str]:
    random.seed(seed + 1337)
    failures: List[str] = []
    for i in range(traces):
        inp = random_input(spec)
        ok = spec.model(inp) == 1
        for name, intent in spec.intents:
            if ok and not intent(inp):
                failures.append(f"trace {i}: intent {name} violated under spec_ok")
                break
    return failures


def run_z3_equiv(spec: SpecHarness) -> List[str]:
    if not HAS_Z3:
        return ["z3-solver not installed; skipping Z3 checks"]
    errors: List[str] = []

    # Build variable list
    vars = []
    for name in spec.inputs:
        width = 16
        if spec.input_widths and name in spec.input_widths:
            width = spec.input_widths[name]
        if width == 1:
            vars.append(z3.BitVec(name, 1))
        elif width == 64:
            vars.append(z3.BitVec(name, 64))
        else:
            vars.append(z3.BitVec(name, 16))

    spec_ok = spec.z3_spec(vars)
    model_ok = spec.z3_model(vars)

    solver = z3.Solver()
    solver.add(spec_ok != model_ok)
    if solver.check() == z3.sat:
        errors.append(f"equivalence failed: counterexample exists for {spec.name}")

    for name, intent in spec.z3_intents:
        solver = z3.Solver()
        solver.add(spec_ok)
        solver.add(z3.Not(intent(vars)))
        if solver.check() == z3.sat:
            errors.append(f"intent '{name}' not implied by spec {spec.name}")

    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description="Intent lattice + equivalence harness")
    parser.add_argument("--spec", default="all", help="Spec name or 'all'")
    parser.add_argument("--traces", type=int, default=50, help="Random trace count")
    parser.add_argument("--seed", type=int, default=7, help="Random seed")
    parser.add_argument("--mode", choices=["trace", "z3", "both"], default="both")
    parser.add_argument("--timeout", type=int, default=10, help="Tau spec-mode timeout per run (seconds)")
    parser.add_argument("--deterministic", action="store_true", help="Include deterministic trace vectors when available")
    args = parser.parse_args()

    harnesses = build_harnesses()
    specs = list(harnesses.values()) if args.spec == "all" else [harnesses[args.spec]]

    failed = False
    for spec in specs:
        print(f"\n== {spec.name} ==")
        if args.mode in ("trace", "both"):
            if not spec.trace_enabled:
                print("Trace compare: skipped (trace disabled for this spec)")
            else:
                mismatches, errors = run_trace(spec, args.traces, args.seed, args.timeout, args.deterministic)
                if errors:
                    print("Trace errors:")
                    for e in errors[:10]:
                        print("  -", e)
                    failed = True
                else:
                    total_steps = args.traces + (len(deterministic_vectors(spec)) if args.deterministic else 0)
                    print(f"Trace compare: {total_steps} steps, mismatches={mismatches}")
                intent_failures = run_intent_traces(spec, args.traces, args.seed)
                if intent_failures:
                    print("Intent violations (trace):")
                    for e in intent_failures[:5]:
                        print("  -", e)
                    failed = True

        if args.mode in ("z3", "both"):
            z3_errors = run_z3_equiv(spec)
            if z3_errors:
                print("Z3 checks:")
                for e in z3_errors:
                    print("  -", e)
                # If z3 not installed, don't fail
                if not (len(z3_errors) == 1 and "not installed" in z3_errors[0]):
                    failed = True
            else:
                print("Z3 equivalence: ok")

    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
