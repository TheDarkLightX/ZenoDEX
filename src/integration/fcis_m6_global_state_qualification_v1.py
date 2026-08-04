"""Fail-closed qualification boundary for M6 application-content receipts."""

from __future__ import annotations

from typing import cast

from ..core.fcis_m6_global_state_projection_v1 import (
    M6GlobalStateProjectionRejectCodeV1,
    M6GlobalStateProjectionRejectV1,
)
from .fcis_m6_projection_receipts_v1 import (
    M6ProjectionContentParityReceiptV1,
    is_verified_projection_content_parity_v1,
)


def require_authoritative_global_state_projection_v1(
    parity: object,
) -> M6GlobalStateProjectionRejectV1:
    """Reject until content, global state, and authority are all closed."""

    if not is_verified_projection_content_parity_v1(parity):
        return M6GlobalStateProjectionRejectV1(
            M6GlobalStateProjectionRejectCodeV1.INVALID_SOURCE,
            ("qualification",),
        )
    receipt = cast(M6ProjectionContentParityReceiptV1, parity)
    return M6GlobalStateProjectionRejectV1(
        M6GlobalStateProjectionRejectCodeV1.INCOMPLETE_GLOBAL_STATE,
        ("qualification", "content_only_receipt"),
        missing_components=receipt.coverage.missing_components,
        global_gaps=receipt.global_gaps,
        unmet_obligations=receipt.unmet_authority_obligations,
    )


__all__ = ("require_authoritative_global_state_projection_v1",)
