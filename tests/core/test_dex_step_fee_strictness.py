from __future__ import annotations

import pytest

from src.core.settlement import Fill, FillAction


def test_fill_rejects_bool_fee_metadata_at_construction() -> None:
    intent_id = "0x" + "01" * 32
    with pytest.raises(TypeError, match="fill.fee_paid must be a non-negative int"):
        Fill(
            intent_id=intent_id,
            action=FillAction.FILL,
            fee_paid=False,
        )
