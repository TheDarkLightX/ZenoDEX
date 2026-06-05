"""Native semantic mirrors for Tau registry specs that exceed Tau trace budgets.

This module is intentionally small and allowlist-based. It exists for registry
coverage of AMM Tau specs whose formulas are accepted by Tau syntax checks but
are too expensive for the current Tau trace runner. Runtime promotion still
belongs to the supported-runtime-subset gate.
"""

from __future__ import annotations

from collections.abc import Mapping

U32_MOD = 1 << 32
U64_MOD = 1 << 64
U32_MAX = U32_MOD - 1
U16_MAX = (1 << 16) - 1
MIN_LP_LOCK = 1000


def native_mirror_supported_spec_ids() -> frozenset[str]:
    return frozenset(_MIRRORS)


def run_native_tau_mirror(spec_id: str, steps: list[dict[str, int]]) -> dict[int, dict[str, int]]:
    if spec_id not in _MIRRORS:
        raise ValueError(f"unsupported native Tau mirror: {spec_id}")
    mirror = _MIRRORS[spec_id]
    outputs: dict[int, dict[str, int]] = {}
    for idx, step in enumerate(steps):
        outputs[idx] = {"o1": int(bool(mirror(_require_int_step(step))))}
    return outputs


def _require_int_step(step: Mapping[str, object]) -> dict[str, int]:
    out: dict[str, int] = {}
    for key, value in step.items():
        if not isinstance(key, str) or not key.startswith("i"):
            raise ValueError(f"invalid Tau input key: {key!r}")
        if not isinstance(value, int) or isinstance(value, bool):
            raise ValueError(f"{key} must be an integer")
        out[key] = int(value)
    return out


def _u32(value: int) -> int:
    return int(value) % U32_MOD


def _u64(value: int) -> int:
    return int(value) % U64_MOD


def _sbf(value: int) -> int:
    return int(value)


def _add32(a: int, b: int) -> int:
    return _u32(_u32(a) + _u32(b))


def _sub32(a: int, b: int) -> int:
    return _u32(_u32(a) - _u32(b))


def _mul32(a: int, b: int) -> int:
    return _u32(_u32(a) * _u32(b))


def _add64(a: int, b: int) -> int:
    return _u64(_u64(a) + _u64(b))


def _sub64(a: int, b: int) -> int:
    return _u64(_u64(a) - _u64(b))


def _mul64(a: int, b: int) -> int:
    return _u64(_u64(a) * _u64(b))


def _i(step: Mapping[str, int], name: str) -> int:
    if name not in step:
        raise ValueError(f"missing Tau input {name}")
    return step[name]


def _bv16(step: Mapping[str, int], name: str) -> int:
    value = _i(step, name)
    if not 0 <= value <= U16_MAX:
        raise ValueError(f"{name} must be a bv[16] integer")
    return value


def _swap_exact_in_v4(step: Mapping[str, int]) -> bool:
    i1 = _u32(_i(step, "i1"))
    i2 = _u32(_i(step, "i2"))
    i3 = _u32(_i(step, "i3"))
    i4 = _u32(_i(step, "i4"))
    i5 = _u32(_i(step, "i5"))
    i6 = _u32(_i(step, "i6"))
    i7 = _u32(_i(step, "i7"))
    i8 = _u32(_i(step, "i8"))
    return (
        i1 > 0
        and i2 > 0
        and i3 > 0
        and i6 > 0
        and i4 <= 10_000
        and i6 < i2
        and i6 >= i5
        and i7 == _add32(i1, i3)
        and i8 == _sub32(i2, i6)
        and i1 <= 0xFFFF
        and i2 <= 0xFFFF
        and i3 <= 0xFFFF
        and i6 <= 0xFFFF
        and i7 <= 0xFFFF
        and i8 <= 0xFFFF
        and _mul32(i7, i8) >= _mul32(i1, i2)
    )


def _swap_exact_out_v4(step: Mapping[str, int]) -> bool:
    i1 = _u32(_i(step, "i1"))
    i2 = _u32(_i(step, "i2"))
    i3 = _u32(_i(step, "i3"))
    i4 = _u32(_i(step, "i4"))
    i5 = _u32(_i(step, "i5"))
    i6 = _u32(_i(step, "i6"))
    i7 = _u32(_i(step, "i7"))
    i8 = _u32(_i(step, "i8"))
    return (
        i1 > 0
        and i2 > 0
        and i3 > 0
        and i6 > 0
        and i4 <= 10_000
        and i3 < i2
        and i6 <= i5
        and i7 == _add32(i1, i6)
        and i8 == _sub32(i2, i3)
        and i1 <= 0xFFFF
        and i2 <= 0xFFFF
        and i6 <= 0xFFFF
        and i3 <= 0xFFFF
        and i7 <= 0xFFFF
        and i8 <= 0xFFFF
        and _mul32(i7, i8) >= _mul32(i1, i2)
    )


def _swap_exact_in_v3(step: Mapping[str, int]) -> bool:
    i1 = _u32(_i(step, "i1"))
    i2 = _u32(_i(step, "i2"))
    i3 = _u32(_i(step, "i3"))
    i4 = _u32(_i(step, "i4"))
    i5 = _u32(_i(step, "i5"))
    i6 = _u32(_i(step, "i6"))
    i7 = _u32(_i(step, "i7"))
    i8 = _u32(_i(step, "i8"))
    i9 = _u64(_i(step, "i9"))
    i10 = _u64(_i(step, "i10"))
    return (
        i1 > 0
        and i2 > 0
        and i3 > 0
        and i4 <= 10_000
        and i6 > 0
        and i6 < i2
        and i6 >= i5
        and i7 == _add32(i1, i3)
        and i8 == _sub32(i2, i6)
        and i10 >= i9
    )


def _swap_exact_out_v3(step: Mapping[str, int]) -> bool:
    i1 = _u32(_i(step, "i1"))
    i2 = _u32(_i(step, "i2"))
    i3 = _u32(_i(step, "i3"))
    i4 = _u32(_i(step, "i4"))
    i5 = _u32(_i(step, "i5"))
    i6 = _u32(_i(step, "i6"))
    i7 = _u32(_i(step, "i7"))
    i8 = _u32(_i(step, "i8"))
    i9 = _u64(_i(step, "i9"))
    i10 = _u64(_i(step, "i10"))
    return (
        i1 > 0
        and i2 > 0
        and i3 > 0
        and i4 <= 10_000
        and i3 < i2
        and i6 > 0
        and i6 <= i5
        and i7 == _add32(i1, i6)
        and i8 == _sub32(i2, i3)
        and i10 >= i9
    )


def _swap_exact_in_fee_proof_gate_v1(step: Mapping[str, int]) -> bool:
    i1 = _u32(_i(step, "i1"))
    i2 = _u32(_i(step, "i2"))
    i3 = _u32(_i(step, "i3"))
    i4 = _u32(_i(step, "i4"))
    i5 = _u32(_i(step, "i5"))
    i6 = _u32(_i(step, "i6"))
    i7 = _u32(_i(step, "i7"))
    i8 = _u32(_i(step, "i8"))
    i9 = _u32(_i(step, "i9"))
    return (
        _sbf(_i(step, "i10")) == 1
        and _sbf(_i(step, "i11")) == 1
        and _sbf(_i(step, "i12")) == 1
        and i1 > 0
        and i2 > 0
        and i3 > 0
        and i6 > 0
        and i4 <= 10_000
        and i9 < i3
        and i6 < i2
        and i6 >= i5
        and i7 == _add32(i1, i3)
        and i7 >= i1
        and i8 == _sub32(i2, i6)
    )


def _swap_exact_out_fee_proof_gate_v1(step: Mapping[str, int]) -> bool:
    i1 = _u32(_i(step, "i1"))
    i2 = _u32(_i(step, "i2"))
    i3 = _u32(_i(step, "i3"))
    i4 = _u32(_i(step, "i4"))
    i5 = _u32(_i(step, "i5"))
    i6 = _u32(_i(step, "i6"))
    i7 = _u32(_i(step, "i7"))
    i8 = _u32(_i(step, "i8"))
    i9 = _u32(_i(step, "i9"))
    return (
        _sbf(_i(step, "i10")) == 1
        and _sbf(_i(step, "i11")) == 1
        and _sbf(_i(step, "i12")) == 1
        and i1 > 0
        and i2 > 0
        and i3 > 0
        and i6 > 0
        and i4 <= 10_000
        and i3 < i2
        and i6 <= i5
        and i9 < i6
        and i7 == _add32(i1, i6)
        and i7 >= i1
        and i8 == _sub32(i2, i3)
    )


def _swap_exact_in_protocol_fee_apply_v1(step: Mapping[str, int]) -> bool:
    i1 = _u32(_i(step, "i1"))
    i2 = _u32(_i(step, "i2"))
    i3 = _u32(_i(step, "i3"))
    i4 = _u32(_i(step, "i4"))
    i5 = _u32(_i(step, "i5"))
    i6 = _u32(_i(step, "i6"))
    i7 = _u32(_i(step, "i7"))
    i8 = _u32(_i(step, "i8"))
    i9 = _u32(_i(step, "i9"))
    i10 = _u32(_i(step, "i10"))
    tmp = _add32(i1, i3)
    return (
        _sbf(_i(step, "i11")) == 1
        and _sbf(_i(step, "i12")) == 1
        and _sbf(_i(step, "i13")) == 1
        and _sbf(_i(step, "i14")) == 1
        and i1 > 0
        and i2 > 0
        and i3 > 0
        and i6 > 0
        and i4 <= 10_000
        and i9 < i3
        and i10 <= i9
        and i6 < i2
        and i6 >= i5
        and tmp >= i1
        and tmp >= i10
        and i7 == _sub32(tmp, i10)
        and i8 == _sub32(i2, i6)
    )


def _swap_exact_out_protocol_fee_apply_v1(step: Mapping[str, int]) -> bool:
    i1 = _u32(_i(step, "i1"))
    i2 = _u32(_i(step, "i2"))
    i3 = _u32(_i(step, "i3"))
    i4 = _u32(_i(step, "i4"))
    i5 = _u32(_i(step, "i5"))
    i6 = _u32(_i(step, "i6"))
    i7 = _u32(_i(step, "i7"))
    i8 = _u32(_i(step, "i8"))
    i9 = _u32(_i(step, "i9"))
    i10 = _u32(_i(step, "i10"))
    tmp = _add32(i1, i6)
    return (
        _sbf(_i(step, "i11")) == 1
        and _sbf(_i(step, "i12")) == 1
        and _sbf(_i(step, "i13")) == 1
        and _sbf(_i(step, "i14")) == 1
        and i1 > 0
        and i2 > 0
        and i3 > 0
        and i3 < i2
        and i6 > 0
        and i4 <= 10_000
        and i6 <= i5
        and i9 < i6
        and i10 <= i9
        and tmp >= i1
        and tmp >= i10
        and i7 == _sub32(tmp, i10)
        and i8 == _sub32(i2, i3)
    )


def _add_liquidity_ratio_guard_v1(step: Mapping[str, int]) -> bool:
    i1 = _u32(_i(step, "i1"))
    i2 = _u32(_i(step, "i2"))
    i3 = _u32(_i(step, "i3"))
    i4 = _u32(_i(step, "i4"))
    i5 = _u32(_i(step, "i5"))
    i6 = _u32(_i(step, "i6"))
    i7 = _u32(_i(step, "i7"))
    i8 = _u32(_i(step, "i8"))
    empty_pool = i1 == 0 or i2 == 0
    full_use_no_refund = i5 == i3 and i6 == i4 and i7 == 0 and i8 == 0
    return (
        _sbf(_i(step, "i9")) == 1
        and _sbf(_i(step, "i10")) == 1
        and i3 > 0
        and i4 > 0
        and i5 > 0
        and i6 > 0
        and i5 <= i3
        and i6 <= i4
        and i7 == _sub32(i3, i5)
        and i8 == _sub32(i4, i6)
        and ((not empty_pool) or full_use_no_refund)
    )


def _create_pool_apply_proof_gate_v1(step: Mapping[str, int]) -> bool:
    i1 = _u32(_i(step, "i1"))
    i2 = _u32(_i(step, "i2"))
    i3 = _u32(_i(step, "i3"))
    i4 = _u32(_i(step, "i4"))
    i5 = _u32(_i(step, "i5"))
    i6 = _u32(_i(step, "i6"))
    i7 = _u32(_i(step, "i7"))
    i8 = _u32(_i(step, "i8"))
    i9 = _u32(_i(step, "i9"))
    i10 = _u32(_i(step, "i10"))
    return (
        _sbf(_i(step, "i11")) == 1
        and _sbf(_i(step, "i12")) == 1
        and i1 == 0
        and i2 == 0
        and i3 == 0
        and i4 > 0
        and i5 > 0
        and i6 <= 10_000
        and i7 > 0
        and i8 == i4
        and i9 == i5
        and i10 == _add32(i7, MIN_LP_LOCK)
        and i10 > MIN_LP_LOCK
    )


def _create_pool_initial_sqrt_guard_v1(step: Mapping[str, int]) -> bool:
    i1 = _u64(_i(step, "i1"))
    i2 = _u64(_i(step, "i2"))
    i3 = _u64(_i(step, "i3"))
    i4 = _u64(_i(step, "i4"))
    product = _mul64(i1, i2)
    square = _mul64(i3, i3)
    residual = _sub64(product, square)
    next_gap = _add64(_mul64(i3, 2), 1)
    return (
        i1 <= U32_MAX
        and i2 <= U32_MAX
        and i3 <= U32_MAX
        and i4 <= U32_MAX
        and i1 > 0
        and i2 > 0
        and square <= product
        and residual < next_gap
        and i3 > MIN_LP_LOCK
        and i4 == _sub64(i3, MIN_LP_LOCK)
        and i4 > 0
    )


def _add_liquidity_apply_v1(step: Mapping[str, int]) -> bool:
    i1 = _u32(_i(step, "i1"))
    i2 = _u32(_i(step, "i2"))
    i3 = _u32(_i(step, "i3"))
    i4 = _u32(_i(step, "i4"))
    i5 = _u32(_i(step, "i5"))
    i6 = _u32(_i(step, "i6"))
    i7 = _u32(_i(step, "i7"))
    i8 = _u32(_i(step, "i8"))
    i9 = _u32(_i(step, "i9"))
    return (
        _sbf(_i(step, "i10")) == 1
        and _sbf(_i(step, "i11")) == 1
        and i1 > 0
        and i2 > 0
        and i3 > 0
        and i4 > 0
        and i5 > 0
        and i6 > 0
        and i7 == _add32(i1, i4)
        and i7 >= i1
        and i8 == _add32(i2, i5)
        and i8 >= i2
        and i9 == _add32(i3, i6)
        and i9 >= i3
    )


def _remove_liquidity_apply_v1(step: Mapping[str, int]) -> bool:
    i1 = _u32(_i(step, "i1"))
    i2 = _u32(_i(step, "i2"))
    i3 = _u32(_i(step, "i3"))
    i4 = _u32(_i(step, "i4"))
    i5 = _u32(_i(step, "i5"))
    i6 = _u32(_i(step, "i6"))
    i7 = _u32(_i(step, "i7"))
    i8 = _u32(_i(step, "i8"))
    i9 = _u32(_i(step, "i9"))
    return (
        _sbf(_i(step, "i10")) == 1
        and _sbf(_i(step, "i11")) == 1
        and i1 > 0
        and i2 > 0
        and i3 > 0
        and i4 > 0
        and i4 <= i3
        and i5 <= i1
        and i6 <= i2
        and i7 == _sub32(i1, i5)
        and i7 <= i1
        and i8 == _sub32(i2, i6)
        and i8 <= i2
        and i9 == _sub32(i3, i4)
        and i9 <= i3
    )


def _multi_predicate(step: Mapping[str, int]) -> bool:
    # REVIEW [B -> A-]: these legacy mirrors replace noisy Tau interpreter
    # traces for bv[16] specs. The first version compared raw Python integers,
    # so an out-of-range registry vector could be accepted by the mirror even
    # though it is not a well-formed bv[16] trace. Guarding the boundary keeps the
    # native mirror fail-closed and makes future trace expansion safer.
    return 0 <= _bv16(step, "i1") <= 0x2710 and _bv16(step, "i2") > 0


def _u32_pair_nonzero(hi: int, lo: int) -> bool:
    return hi > 0 or (hi == 0 and lo > 0)


def _u32_pair_nonnegative(hi: int, lo: int) -> bool:
    return hi > 0 or (hi == 0 and lo >= 0)


def _u32_pair_ge(lhs_hi: int, lhs_lo: int, rhs_hi: int, rhs_lo: int) -> bool:
    return lhs_hi > rhs_hi or (lhs_hi == rhs_hi and lhs_lo >= rhs_lo)


def _cpmm_basic(step: Mapping[str, int]) -> bool:
    return (
        _u32_pair_nonzero(_bv16(step, "i1"), _bv16(step, "i2"))
        and _u32_pair_nonzero(_bv16(step, "i3"), _bv16(step, "i4"))
        and _u32_pair_nonzero(_bv16(step, "i5"), _bv16(step, "i6"))
        and 0 <= _bv16(step, "i7") <= 0x2710
        and _u32_pair_nonzero(_bv16(step, "i8"), _bv16(step, "i9"))
        and _u32_pair_ge(_bv16(step, "i3"), _bv16(step, "i4"), _bv16(step, "i8"), _bv16(step, "i9"))
    )


def _balance_safety(step: Mapping[str, int]) -> bool:
    return (
        _u32_pair_nonnegative(_bv16(step, "i1"), _bv16(step, "i2"))
        and _u32_pair_nonnegative(_bv16(step, "i3"), _bv16(step, "i4"))
        and _u32_pair_nonnegative(_bv16(step, "i5"), _bv16(step, "i6"))
    )


_MIRRORS = {
    "multi_predicate": _multi_predicate,
    "cpmm_basic": _cpmm_basic,
    "balance_safety": _balance_safety,
    "dex_complete": _cpmm_basic,
    "swap_exact_in_v4": _swap_exact_in_v4,
    "swap_exact_out_v4": _swap_exact_out_v4,
    "swap_exact_in_v3": _swap_exact_in_v3,
    "swap_exact_out_v3": _swap_exact_out_v3,
    "swap_exact_in_fee_proof_gate_v1": _swap_exact_in_fee_proof_gate_v1,
    "swap_exact_out_fee_proof_gate_v1": _swap_exact_out_fee_proof_gate_v1,
    "swap_exact_in_protocol_fee_apply_v1": _swap_exact_in_protocol_fee_apply_v1,
    "swap_exact_out_protocol_fee_apply_v1": _swap_exact_out_protocol_fee_apply_v1,
    "add_liquidity_ratio_guard_v1": _add_liquidity_ratio_guard_v1,
    "create_pool_apply_proof_gate_v1": _create_pool_apply_proof_gate_v1,
    "create_pool_initial_sqrt_guard_v1": _create_pool_initial_sqrt_guard_v1,
    "add_liquidity_apply_v1": _add_liquidity_apply_v1,
    "remove_liquidity_apply_v1": _remove_liquidity_apply_v1,
}
