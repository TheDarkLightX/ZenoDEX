"""Production-safe CPMM settlement swap helpers.

These helpers mirror the semantics pinned down by the bounded settlement
witness kernels:

- ``src/kernels/dex/settlement_swap_apply_witness_v1.yaml``
- ``src/kernels/dex/settlement_swap_exact_out_apply_witness_v1.yaml``

Unlike the native shell adapters for those witnesses, this module is intended
for runtime use in the functional core, so it uses the full consensus domain
bounds rather than the tiny verifier-friendly state ranges.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from .cpmm_swap_v8 import swap_exact_in as _kernel_swap_exact_in_v8
from .cpmm_swap_v8 import swap_exact_out as _kernel_swap_exact_out_v8

BPS_DENOM = 10_000
# Keep these aligned with ``src/core/domain_limits.py`` and the authoritative
# kernel domains. This module stays self-contained to avoid a circular import
# through ``src.core.__init__``.
DEX_POOL_RESERVE_MAX = 3_000_000_000
DEX_SWAP_AMOUNT_MAX = 3_000_000_000
CPMM_EXACT_OUT_MAX_OVERDELIVERY_GAP_BPS_DEFAULT = 200
CPMM_SETTLEMENT_SURFACE = "cpmm_settlement"
_U128_MAX = (1 << 128) - 1


@dataclass(frozen=True)
class SettlementSwapExactInQuote:
    amount_in: int
    amount_out: int
    fee_paid: int
    protocol_fee_paid: int
    lp_fee_paid: int
    net_in: int
    reserve_in_before: int
    reserve_out_before: int
    reserve_in_after: int
    reserve_out_after: int
    k_before: int
    k_after: int


@dataclass(frozen=True)
class SettlementSwapExactOutQuote:
    amount_in: int
    amount_out: int
    amount_out_quote: int
    overdelivery_gap: int
    gap_bps: int
    fee_paid: int
    protocol_fee_paid: int
    lp_fee_paid: int
    net_in_actual: int
    reserve_in_before: int
    reserve_out_before: int
    reserve_in_after: int
    reserve_out_after: int
    k_before: int
    k_after: int


def _gap_bps(*, overdelivery_gap: int, amount_out: int) -> int:
    return ((overdelivery_gap * BPS_DENOM) + amount_out - 1) // amount_out


def _require_int_range(
    name: str,
    value: object,
    *,
    minimum: int | None = None,
    maximum: int | None = None,
) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    value_int = int(value)
    if minimum is not None and value_int < minimum:
        raise ValueError(f"{name} must be >= {minimum}: {value_int}")
    if maximum is not None and value_int > maximum:
        raise ValueError(f"{name} exceeds kernel domain max {maximum}: {value_int}")
    return value_int


def _quote_error_code(msg: str) -> str:
    if "swap would exceed reserve_in domain max" in msg:
        return "reserve_domain_exceeded"
    if msg.startswith("reserve_in ") or msg.startswith("reserve_out "):
        return "reserve_out_of_domain"
    if msg.startswith("amount_in ") or msg.startswith("amount_out must be >= 1") or (
        msg.startswith("amount_out") and "kernel domain max" in msg
    ):
        return "invalid_amount"
    if "net_in must be positive" in msg or "amount_out is zero" in msg:
        return "trade_too_small"
    if "cannot drain full reserve_out" in msg:
        return "amount_out_ge_reserve"
    if "cannot compute with 100% fee" in msg:
        return "fee_full"
    if "overdelivery gap exceeds bps policy" in msg:
        return "overdelivery_gap"
    if "Invariant violation" in msg:
        return "invariant_violation"
    return f"unmapped:{msg}"


def _pool_doc(*, reserve_in: int, reserve_out: int, fee_bps: int) -> dict[str, Any]:
    return {
        "initialized": True,
        "reserve0": reserve_in,
        "reserve1": reserve_out,
        "fee_bps": fee_bps,
    }


def _exact_in_quote_doc(q: SettlementSwapExactInQuote) -> dict[str, Any]:
    return {
        "accept": True,
        "reason": "ok",
        "quote": {
            "amount_in": q.amount_in,
            "amount_out": q.amount_out,
            "fee_paid": q.fee_paid,
            "protocol_fee_paid": q.protocol_fee_paid,
            "lp_fee_paid": q.lp_fee_paid,
            "net_in": q.net_in,
            "reserve_in_before": q.reserve_in_before,
            "reserve_out_before": q.reserve_out_before,
            "reserve_in_after": q.reserve_in_after,
            "reserve_out_after": q.reserve_out_after,
            "k_before": q.k_before,
            "k_after": q.k_after,
        },
    }


def _exact_out_quote_doc(q: SettlementSwapExactOutQuote) -> dict[str, Any]:
    return {
        "accept": True,
        "reason": "ok",
        "quote": {
            "amount_in": q.amount_in,
            "amount_out": q.amount_out,
            "amount_out_quote": q.amount_out_quote,
            "overdelivery_gap": q.overdelivery_gap,
            "gap_bps": q.gap_bps,
            "fee_paid": q.fee_paid,
            "protocol_fee_paid": q.protocol_fee_paid,
            "lp_fee_paid": q.lp_fee_paid,
            "net_in_actual": q.net_in_actual,
            "reserve_in_before": q.reserve_in_before,
            "reserve_out_before": q.reserve_out_before,
            "reserve_in_after": q.reserve_in_after,
            "reserve_out_after": q.reserve_out_after,
            "k_before": q.k_before,
            "k_after": q.k_after,
        },
    }


def _reject_doc(exc: Exception) -> dict[str, Any]:
    return {"accept": False, "reason": _quote_error_code(str(exc))}


def _docs_agree(left: dict[str, Any], right: dict[str, Any]) -> bool:
    if bool(left.get("accept")) != bool(right.get("accept")):
        return False
    if left.get("reason") != right.get("reason"):
        return False
    if not left.get("accept"):
        return True
    return left.get("quote") == right.get("quote")


def _rust_exact_in_doc(*, reserve_in: int, reserve_out: int, amount_in: int, fee_bps: int) -> dict[str, Any]:
    from src.runtime.rust_invoker import cpmm_op

    out = cpmm_op(
        pool=_pool_doc(reserve_in=reserve_in, reserve_out=reserve_out, fee_bps=fee_bps),
        tx={
            "kind": "swap_exact_in",
            "zero_for_one": True,
            "amount_in": amount_in,
            "min_amount_out": 0,
        },
    )
    if not out["accept"]:
        return {"accept": False, "reason": str(out["reject_reason"])}
    receipt = out["receipt"]
    if not isinstance(receipt, dict):
        raise ValueError("malformed accepted CPMM Rust output")
    amount_out = int(receipt["amount_out"])
    fee_paid = int(receipt["fee_total"])
    reserve_in_after = int(receipt["new_reserve0"])
    reserve_out_after = int(receipt["new_reserve1"])
    quote = SettlementSwapExactInQuote(
        amount_in=int(receipt["amount_in"]),
        amount_out=amount_out,
        fee_paid=fee_paid,
        protocol_fee_paid=0,
        lp_fee_paid=fee_paid,
        net_in=int(receipt["amount_in"]) - fee_paid,
        reserve_in_before=reserve_in,
        reserve_out_before=reserve_out,
        reserve_in_after=reserve_in_after,
        reserve_out_after=reserve_out_after,
        k_before=reserve_in * reserve_out,
        k_after=reserve_in_after * reserve_out_after,
    )
    return _exact_in_quote_doc(quote)


def _rust_exact_out_doc(
    *,
    reserve_in: int,
    reserve_out: int,
    amount_out: int,
    fee_bps: int,
    max_overdelivery_gap_bps: int,
) -> dict[str, Any]:
    from src.runtime.rust_invoker import cpmm_op

    out = cpmm_op(
        pool=_pool_doc(reserve_in=reserve_in, reserve_out=reserve_out, fee_bps=fee_bps),
        tx={
            "kind": "swap_exact_out",
            "zero_for_one": True,
            "amount_out": amount_out,
            "max_amount_in": _U128_MAX,
            "max_overdelivery_gap_bps": max_overdelivery_gap_bps,
        },
    )
    if not out["accept"]:
        return {"accept": False, "reason": str(out["reject_reason"])}
    receipt = out["receipt"]
    if not isinstance(receipt, dict):
        raise ValueError("malformed accepted CPMM Rust output")
    amount_in = int(receipt["amount_in"])
    fee_paid = int(receipt["fee_total"])
    reserve_in_after = int(receipt["new_reserve0"])
    reserve_out_after = int(receipt["new_reserve1"])
    quote = SettlementSwapExactOutQuote(
        amount_in=amount_in,
        amount_out=int(receipt["amount_out"]),
        amount_out_quote=int(receipt["amount_out_quote"]),
        overdelivery_gap=int(receipt["overdelivery_gap"]),
        gap_bps=int(receipt["gap_bps"]),
        fee_paid=fee_paid,
        protocol_fee_paid=0,
        lp_fee_paid=fee_paid,
        net_in_actual=amount_in - fee_paid,
        reserve_in_before=reserve_in,
        reserve_out_before=reserve_out,
        reserve_in_after=reserve_in_after,
        reserve_out_after=reserve_out_after,
        k_before=reserve_in * reserve_out,
        k_after=reserve_in_after * reserve_out_after,
    )
    return _exact_out_quote_doc(quote)


def _quote_cpmm_swap_exact_in_python(
    *,
    reserve_in: int,
    reserve_out: int,
    amount_in: int,
    fee_bps: int,
    protocol_fee_share_bps: int = 0,
) -> SettlementSwapExactInQuote:
    """Return a kernel-backed exact-in settlement quote plus post-state."""
    reserve_in = _require_int_range("reserve_in", reserve_in, minimum=1, maximum=DEX_POOL_RESERVE_MAX)
    reserve_out = _require_int_range("reserve_out", reserve_out, minimum=1, maximum=DEX_POOL_RESERVE_MAX)
    amount_in = _require_int_range("amount_in", amount_in, minimum=1, maximum=DEX_SWAP_AMOUNT_MAX)
    fee_bps = _require_int_range("fee_bps", fee_bps, minimum=0, maximum=BPS_DENOM)
    protocol_fee_share_bps = _require_int_range(
        "protocol_fee_share_bps",
        protocol_fee_share_bps,
        minimum=0,
        maximum=BPS_DENOM,
    )
    if reserve_in + amount_in > DEX_POOL_RESERVE_MAX:
        raise ValueError(
            f"swap would exceed reserve_in domain max {DEX_POOL_RESERVE_MAX}: "
            f"{reserve_in} + {amount_in}"
        )

    res = _kernel_swap_exact_in_v8(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_in=amount_in,
        fee_bps=fee_bps,
        protocol_fee_share_bps=protocol_fee_share_bps,
    )
    if res.k_after < res.k_before:
        raise ValueError(f"Invariant violation: new_k ({res.k_after}) < old_k ({res.k_before})")

    return SettlementSwapExactInQuote(
        amount_in=int(amount_in),
        amount_out=int(res.amount_out),
        fee_paid=int(res.fee_total),
        protocol_fee_paid=int(res.protocol_fee),
        lp_fee_paid=int(res.lp_fee),
        net_in=int(res.net_in),
        reserve_in_before=int(reserve_in),
        reserve_out_before=int(reserve_out),
        reserve_in_after=int(res.new_reserve_in),
        reserve_out_after=int(res.new_reserve_out),
        k_before=int(res.k_before),
        k_after=int(res.k_after),
    )


def quote_cpmm_swap_exact_in_for_ordering_simulation(
    *,
    reserve_in: int,
    reserve_out: int,
    amount_in: int,
    fee_bps: int,
) -> SettlementSwapExactInQuote:
    """Return a deterministic, side-effect-free CPMM exact-in quote for ordering simulation.

    Design by contract:
    - Precondition: callers provide candidate reserves, amount, and fee in the
      same integer domains accepted by ``quote_cpmm_swap_exact_in``.
    - Invariant: ordering exploration is pure arithmetic and never crosses the
      external Rust subprocess boundary.
    - Postcondition: accepted quotes are byte-identical to the Python authority
      quote used for Rust differential checks.
    """

    return _quote_cpmm_swap_exact_in_python(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_in=amount_in,
        fee_bps=fee_bps,
    )


def quote_cpmm_swap_exact_out_for_ordering_simulation(
    *,
    reserve_in: int,
    reserve_out: int,
    amount_out: int,
    fee_bps: int,
) -> SettlementSwapExactOutQuote:
    """Return a deterministic, side-effect-free CPMM exact-out quote for ordering simulation."""

    return _quote_cpmm_swap_exact_out_python(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_out=amount_out,
        fee_bps=fee_bps,
    )


def quote_cpmm_swap_exact_in(
    *,
    reserve_in: int,
    reserve_out: int,
    amount_in: int,
    fee_bps: int,
    protocol_fee_share_bps: int = 0,
) -> SettlementSwapExactInQuote:
    from src.runtime.authority import AuthorityMode, active_mode, decide

    mode = active_mode(CPMM_SETTLEMENT_SURFACE)
    if mode is AuthorityMode.PYTHON_AUTHORITY or int(protocol_fee_share_bps) != 0:
        return _quote_cpmm_swap_exact_in_python(
            reserve_in=reserve_in,
            reserve_out=reserve_out,
            amount_in=amount_in,
            fee_bps=fee_bps,
            protocol_fee_share_bps=protocol_fee_share_bps,
        )

    def python_doc() -> dict[str, Any]:
        try:
            return _exact_in_quote_doc(
                _quote_cpmm_swap_exact_in_python(
                    reserve_in=reserve_in,
                    reserve_out=reserve_out,
                    amount_in=amount_in,
                    fee_bps=fee_bps,
                    protocol_fee_share_bps=protocol_fee_share_bps,
                )
            )
        except (TypeError, ValueError) as exc:
            return _reject_doc(exc)

    decision = decide(
        CPMM_SETTLEMENT_SURFACE,
        mode,
        python_fn=python_doc,
        rust_fn=lambda: _rust_exact_in_doc(
            reserve_in=reserve_in,
            reserve_out=reserve_out,
            amount_in=amount_in,
            fee_bps=fee_bps,
        ),
        compare=_docs_agree,
    )
    doc = decision.result
    if not doc["accept"]:
        return _quote_cpmm_swap_exact_in_python(
            reserve_in=reserve_in,
            reserve_out=reserve_out,
            amount_in=amount_in,
            fee_bps=fee_bps,
            protocol_fee_share_bps=protocol_fee_share_bps,
        )
    q = doc["quote"]
    return SettlementSwapExactInQuote(**q)


def _quote_cpmm_swap_exact_out_python(
    *,
    reserve_in: int,
    reserve_out: int,
    amount_out: int,
    fee_bps: int,
    max_overdelivery_gap_bps: int = CPMM_EXACT_OUT_MAX_OVERDELIVERY_GAP_BPS_DEFAULT,
    protocol_fee_share_bps: int = 0,
) -> SettlementSwapExactOutQuote:
    """Return a kernel-backed exact-out settlement quote plus post-state."""
    reserve_in = _require_int_range("reserve_in", reserve_in, minimum=1, maximum=DEX_POOL_RESERVE_MAX)
    reserve_out = _require_int_range("reserve_out", reserve_out, minimum=1, maximum=DEX_POOL_RESERVE_MAX)
    amount_out = _require_int_range("amount_out", amount_out, minimum=1, maximum=DEX_SWAP_AMOUNT_MAX)
    fee_bps = _require_int_range("fee_bps", fee_bps, minimum=0, maximum=BPS_DENOM)
    max_overdelivery_gap_bps = _require_int_range(
        "max_overdelivery_gap_bps",
        max_overdelivery_gap_bps,
        minimum=0,
        maximum=BPS_DENOM,
    )
    protocol_fee_share_bps = _require_int_range(
        "protocol_fee_share_bps",
        protocol_fee_share_bps,
        minimum=0,
        maximum=BPS_DENOM,
    )

    res = _kernel_swap_exact_out_v8(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_out=amount_out,
        fee_bps=fee_bps,
        protocol_fee_share_bps=protocol_fee_share_bps,
    )
    if res.new_reserve_in > DEX_POOL_RESERVE_MAX:
        raise ValueError(
            f"swap would exceed reserve_in domain max {DEX_POOL_RESERVE_MAX}: "
            f"{reserve_in} + {res.amount_in}"
        )
    gap_bps = _gap_bps(overdelivery_gap=int(res.overdelivery_gap), amount_out=amount_out)
    if gap_bps > max_overdelivery_gap_bps:
        raise ValueError(
            f"overdelivery gap exceeds bps policy: gap_bps={gap_bps} > {max_overdelivery_gap_bps}"
        )
    if res.k_after < res.k_before:
        raise ValueError(f"Invariant violation: new_k ({res.k_after}) < old_k ({res.k_before})")

    return SettlementSwapExactOutQuote(
        amount_in=int(res.amount_in),
        amount_out=int(res.amount_out),
        amount_out_quote=int(res.amount_out_quote),
        overdelivery_gap=int(res.overdelivery_gap),
        gap_bps=int(gap_bps),
        fee_paid=int(res.fee_total),
        protocol_fee_paid=int(res.protocol_fee),
        lp_fee_paid=int(res.lp_fee),
        net_in_actual=int(res.net_in),
        reserve_in_before=int(reserve_in),
        reserve_out_before=int(reserve_out),
        reserve_in_after=int(res.new_reserve_in),
        reserve_out_after=int(res.new_reserve_out),
        k_before=int(res.k_before),
        k_after=int(res.k_after),
    )


def quote_cpmm_swap_exact_out(
    *,
    reserve_in: int,
    reserve_out: int,
    amount_out: int,
    fee_bps: int,
    max_overdelivery_gap_bps: int = CPMM_EXACT_OUT_MAX_OVERDELIVERY_GAP_BPS_DEFAULT,
    protocol_fee_share_bps: int = 0,
) -> SettlementSwapExactOutQuote:
    from src.runtime.authority import AuthorityMode, active_mode, decide

    mode = active_mode(CPMM_SETTLEMENT_SURFACE)
    if mode is AuthorityMode.PYTHON_AUTHORITY or int(protocol_fee_share_bps) != 0:
        return _quote_cpmm_swap_exact_out_python(
            reserve_in=reserve_in,
            reserve_out=reserve_out,
            amount_out=amount_out,
            fee_bps=fee_bps,
            max_overdelivery_gap_bps=max_overdelivery_gap_bps,
            protocol_fee_share_bps=protocol_fee_share_bps,
        )

    def python_doc() -> dict[str, Any]:
        try:
            return _exact_out_quote_doc(
                _quote_cpmm_swap_exact_out_python(
                    reserve_in=reserve_in,
                    reserve_out=reserve_out,
                    amount_out=amount_out,
                    fee_bps=fee_bps,
                    max_overdelivery_gap_bps=max_overdelivery_gap_bps,
                    protocol_fee_share_bps=protocol_fee_share_bps,
                )
            )
        except (TypeError, ValueError) as exc:
            return _reject_doc(exc)

    decision = decide(
        CPMM_SETTLEMENT_SURFACE,
        mode,
        python_fn=python_doc,
        rust_fn=lambda: _rust_exact_out_doc(
            reserve_in=reserve_in,
            reserve_out=reserve_out,
            amount_out=amount_out,
            fee_bps=fee_bps,
            max_overdelivery_gap_bps=max_overdelivery_gap_bps,
        ),
        compare=_docs_agree,
    )
    doc = decision.result
    if not doc["accept"]:
        return _quote_cpmm_swap_exact_out_python(
            reserve_in=reserve_in,
            reserve_out=reserve_out,
            amount_out=amount_out,
            fee_bps=fee_bps,
            max_overdelivery_gap_bps=max_overdelivery_gap_bps,
            protocol_fee_share_bps=protocol_fee_share_bps,
        )
    q = doc["quote"]
    return SettlementSwapExactOutQuote(**q)
