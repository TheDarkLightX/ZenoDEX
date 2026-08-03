"""Pure zUSD-kernel replay for authenticated borrowing-fee occurrences."""

from __future__ import annotations

from typing import NamedTuple

from .zusd import ZUSDCommand, ZUSDState, ZUSDStepResult, _step_python
from .zusd_authenticated_borrow_fee_occurrence_values_v1 import (
    ZUSDAuthenticatedBorrowFeeOccurrenceRejectCodeV1,
    ZUSDAuthenticatedBorrowFeeOccurrenceRejectV1,
)


class _KernelValuesV1(NamedTuple):
    post_state: ZUSDState
    fee_e8: int
    fee_bps: int
    debt_delta_e8: int


def _reject_v1(
    code: ZUSDAuthenticatedBorrowFeeOccurrenceRejectCodeV1,
    *path: str,
) -> ZUSDAuthenticatedBorrowFeeOccurrenceRejectV1:
    return ZUSDAuthenticatedBorrowFeeOccurrenceRejectV1(code, tuple(path))


def _accepted_effects_v1(
    result: ZUSDStepResult,
    principal_e8: int,
) -> tuple[int, int, int] | ZUSDAuthenticatedBorrowFeeOccurrenceRejectV1:
    expected_fields = {
        "event",
        "principal_e8",
        "mint_fee_e8",
        "mint_fee_bps",
        "debt_delta_e8",
    }
    if set(result.effects) != expected_fields or result.effects.get("event") != "zusd_minted":
        return _reject_v1(
            ZUSDAuthenticatedBorrowFeeOccurrenceRejectCodeV1.MALFORMED_KERNEL_ACCEPT,
            "kernel",
            "effects",
        )
    principal = result.effects.get("principal_e8")
    fee = result.effects.get("mint_fee_e8")
    fee_bps = result.effects.get("mint_fee_bps")
    debt_delta = result.effects.get("debt_delta_e8")
    if (
        type(principal) is not int
        or type(fee) is not int
        or type(fee_bps) is not int
        or type(debt_delta) is not int
        or principal != principal_e8
    ):
        return _reject_v1(
            ZUSDAuthenticatedBorrowFeeOccurrenceRejectCodeV1.MALFORMED_KERNEL_ACCEPT,
            "kernel",
            "effects",
        )
    if fee == 0:
        return _reject_v1(
            ZUSDAuthenticatedBorrowFeeOccurrenceRejectCodeV1.ZERO_FEE,
            "kernel",
            "effects",
            "mint_fee_e8",
        )
    return fee, fee_bps, debt_delta


def _economic_delta_matches_v1(
    *,
    pre_state: ZUSDState,
    post_state: ZUSDState,
    principal_e8: int,
    values: tuple[int, int, int],
) -> bool:
    fee, _, debt_delta = values
    return (
        debt_delta == principal_e8 + fee
        and post_state.debt_e8 - pre_state.debt_e8 == debt_delta
        and post_state.free_debt_e8 - pre_state.free_debt_e8 == debt_delta
        and post_state.protocol_revenue_zusd_cum_e8 - pre_state.protocol_revenue_zusd_cum_e8 == fee
    )


def _derive_kernel_values_v1(
    *,
    pre_state: ZUSDState,
    principal_e8: int,
) -> _KernelValuesV1 | ZUSDAuthenticatedBorrowFeeOccurrenceRejectV1:
    result = _step_python(
        pre_state,
        ZUSDCommand(tag="mint_zusd", args={"amount_e8": principal_e8}),
    )
    if type(result.ok) is not bool or not result.ok:
        return _reject_v1(
            ZUSDAuthenticatedBorrowFeeOccurrenceRejectCodeV1.KERNEL_REJECTED,
            "kernel",
            result.error or "unknown",
        )
    if type(result.state) is not ZUSDState or type(result.effects) is not dict:
        return _reject_v1(
            ZUSDAuthenticatedBorrowFeeOccurrenceRejectCodeV1.MALFORMED_KERNEL_ACCEPT,
            "kernel",
        )
    values = _accepted_effects_v1(result, principal_e8)
    if type(values) is ZUSDAuthenticatedBorrowFeeOccurrenceRejectV1:
        return values
    if not _economic_delta_matches_v1(
        pre_state=pre_state,
        post_state=result.state,
        principal_e8=principal_e8,
        values=values,
    ):
        return _reject_v1(
            ZUSDAuthenticatedBorrowFeeOccurrenceRejectCodeV1.ECONOMIC_DELTA_MISMATCH,
            "kernel",
            "post_state",
        )
    fee, fee_bps, debt_delta = values
    return _KernelValuesV1(result.state, fee, fee_bps, debt_delta)


__all__ = ()
