from __future__ import annotations

import pytest

from src.integration.tau_witness import (
    AUTOTRADER_TX_ENVELOPE_GUARD_V1,
    build_autotrader_tx_envelope_guard_v1_step,
)


def test_build_autotrader_tx_envelope_guard_v1_step() -> None:
    step = build_autotrader_tx_envelope_guard_v1_step(
        tx_requested=1,
        sequence_present=1,
        expiration_present=1,
        sequence_valid=1,
        expiration_valid=1,
        fee_limit_valid=1,
        intent_stream_present=1,
        settlement_stream_absent=1,
        extra_custom_streams_absent=1,
    )
    assert AUTOTRADER_TX_ENVELOPE_GUARD_V1.spec_id == "autotrader_tx_envelope_guard_v1"
    assert step["i9"] == 1


def test_build_autotrader_tx_envelope_guard_v1_step_rejects_bad_bools() -> None:
    with pytest.raises(ValueError, match="tx_requested must be 0 or 1"):
        build_autotrader_tx_envelope_guard_v1_step(
            tx_requested=2,
            sequence_present=1,
            expiration_present=1,
            sequence_valid=1,
            expiration_valid=1,
            fee_limit_valid=1,
            intent_stream_present=1,
            settlement_stream_absent=1,
            extra_custom_streams_absent=1,
        )
