from __future__ import annotations

from tools.bva.spec import IntDomain, Scenario

from src.core.cpmm_u256_safety import analyze_cpmm_exact_in_u256_overflows
from src.core.fixed_width import U256_MAX


def _label(out) -> str:
    flags = []
    if out.fee_mul_overflow_naive:
        flags.append("fee_mul_overflow_naive")
    if out.fee_mul_overflow_decomposed:
        flags.append("fee_mul_overflow_decomposed")
    if out.denom_add_overflow:
        flags.append("denom_add_overflow")
    if out.numerator_mul_overflow:
        flags.append("numerator_mul_overflow")
    return "|".join(flags) if flags else "ok"


SCENARIO = Scenario(
    name="cpmm_u256_overflow_flags_exact_in",
    fn=lambda reserve_in, reserve_out, amount_in, fee_bps: analyze_cpmm_exact_in_u256_overflows(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_in=amount_in,
        fee_bps=fee_bps,
    ),
    domains={
        # Very wide ranges, but the miner is budgeted and uses specials heavily.
        "reserve_in": IntDomain(
            min_value=0,
            max_value=U256_MAX,
            specials=(1, (1 << 128) - 1, 1 << 128, (1 << 128) + 1, U256_MAX),
        ),
        "reserve_out": IntDomain(
            min_value=0,
            max_value=U256_MAX,
            specials=(1, (1 << 128) - 1, 1 << 128, (1 << 128) + 1, U256_MAX),
        ),
        "amount_in": IntDomain(
            min_value=0,
            max_value=U256_MAX,
            specials=(0, 1, 2, (1 << 128) - 1, 1 << 128, (1 << 128) + 1, U256_MAX),
        ),
        "fee_bps": IntDomain(
            min_value=0,
            max_value=10_000,
            specials=(0, 1, 30, 100, 10_000),
            include_bool=True,
        ),
    },
    label_fn=_label,
    seed=0,
    max_contexts=8,
    samples_per_context=64,
    random_contexts=8,
    random_context_budget=128,
)

