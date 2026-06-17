from __future__ import annotations

import pytest

from src.integration.api_server_dex_dispatch import DexRequestContext
from src.integration.dex_dispatch_receipt_handlers import _handle_impact_preview


def _ctx() -> DexRequestContext:
    return DexRequestContext(server=object(), cors_origin=None, raw_body=None)


@pytest.mark.parametrize(
    "field",
    (
        "reserve_in",
        "reserve_out",
        "amount_in",
        "fee_bps",
        "pending_volume_same_direction",
        "confidence_bps",
    ),
)
def test_impact_preview_handler_rejects_bool_numeric_fields(field: str) -> None:
    payload = {
        "reserve_in": 1_000,
        "reserve_out": 1_000,
        "amount_in": 10,
        "fee_bps": 0,
        "pending_volume_same_direction": 0,
        "confidence_bps": 9_500,
    }
    payload[field] = True

    with pytest.raises(ValueError, match=f"{field} must be an int"):
        _handle_impact_preview(payload, _ctx())
