from __future__ import annotations

import pytest

from src.integration.tau_witness import (
    AUTOTRADER_SUBMIT_BUNDLE_GUARD_V1,
    build_autotrader_submit_bundle_guard_v1_step,
)


def test_build_autotrader_submit_bundle_guard_v1_step() -> None:
    step = build_autotrader_submit_bundle_guard_v1_step(
        emit_requested=1,
        signed_intents_present=1,
        signatures_present=1,
        signatures_verify=1,
        sender_binding_ok=1,
        quote_receipts_present=1,
        operations_roundtrip_ok=1,
        tx_requested=1,
        tx_payload_ok=1,
    )
    assert AUTOTRADER_SUBMIT_BUNDLE_GUARD_V1.spec_id == "autotrader_submit_bundle_guard_v1"
    assert step == {
        "i1": 1,
        "i2": 1,
        "i3": 1,
        "i4": 1,
        "i5": 1,
        "i6": 1,
        "i7": 1,
        "i8": 1,
        "i9": 1,
    }


def test_build_autotrader_submit_bundle_guard_v1_step_rejects_bad_bools() -> None:
    with pytest.raises(ValueError, match="tx_payload_ok must be 0 or 1"):
        build_autotrader_submit_bundle_guard_v1_step(
            emit_requested=1,
            signed_intents_present=1,
            signatures_present=1,
            signatures_verify=1,
            sender_binding_ok=1,
            quote_receipts_present=1,
            operations_roundtrip_ok=1,
            tx_requested=1,
            tx_payload_ok=2,
        )
