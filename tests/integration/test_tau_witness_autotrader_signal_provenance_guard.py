from __future__ import annotations

import pytest

from src.integration.tau_witness import (
    AUTOTRADER_SIGNAL_PROVENANCE_GUARD_V1,
    build_autotrader_signal_provenance_guard_v1_step,
)


def test_build_autotrader_signal_provenance_guard_v1_step() -> None:
    step = build_autotrader_signal_provenance_guard_v1_step(
        source_kind_code=1,
        trust_tier_code=2,
        quote_receipt_present=1,
        quote_receipt_verified=1,
        quote_epoch_present=1,
        binding_ok=1,
        auth_ok=1,
        source_available=1,
        require_quote_receipts=1,
    )
    assert AUTOTRADER_SIGNAL_PROVENANCE_GUARD_V1.spec_id == "autotrader_signal_provenance_guard_v1"
    assert step == {
        "i1": 1,
        "i2": 2,
        "i3": 1,
        "i4": 1,
        "i5": 1,
        "i6": 1,
        "i7": 1,
        "i8": 1,
        "i9": 1,
    }


def test_build_autotrader_signal_provenance_guard_v1_step_rejects_bad_bools() -> None:
    with pytest.raises(ValueError, match="quote_receipt_present must be 0 or 1"):
        build_autotrader_signal_provenance_guard_v1_step(
            source_kind_code=1,
            trust_tier_code=2,
            quote_receipt_present=2,
            quote_receipt_verified=1,
            quote_epoch_present=1,
            binding_ok=1,
            auth_ok=1,
            source_available=1,
            require_quote_receipts=1,
        )
