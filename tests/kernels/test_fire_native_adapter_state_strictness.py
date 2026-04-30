from __future__ import annotations

import pytest


def test_burn_boost_call_native_adapter_reset_rejects_string_integer_state() -> None:
    from src.fire.runtime.burn_boost_call_v1_native_adapter import make_adapter

    adapter = make_adapter(ir={"schema": "fake"})

    with pytest.raises(TypeError, match="artifact_lower must be an int"):
        adapter.reset(
            state={
                "artifact_lower": "0",
                "artifact_upper": 30,
                "cap_index": 3,
                "holder_delta": 0,
                "holder_posted": 0,
                "n_notional": 10,
                "phase": "Compiled",
                "source_upper": 9,
                "strike_index": 4,
                "witness_final": 0,
                "writer_delta": 0,
                "writer_posted": 0,
            }
        )


def test_fee_note_native_adapter_reset_rejects_bool_integer_state() -> None:
    from src.fire.runtime.fee_note_v1_native_adapter import make_adapter

    adapter = make_adapter(ir={"schema": "fake"})

    with pytest.raises(TypeError, match="artifact_lower must be an int"):
        adapter.reset(
            state={
                "artifact_lower": False,
                "artifact_upper": 20,
                "cap_index": 7,
                "holder_delta": 0,
                "holder_posted": 0,
                "n_notional": 10,
                "phase": "Compiled",
                "source_upper": 2,
                "witness_final": 0,
                "writer_delta": 0,
                "writer_posted": 0,
            }
        )


def test_lp_loss_cover_native_adapter_reset_rejects_non_string_phase() -> None:
    from src.fire.runtime.lp_loss_cover_v1_native_adapter import make_adapter

    adapter = make_adapter(ir={"schema": "fake"})

    with pytest.raises(TypeError, match="phase must be a non-empty string"):
        adapter.reset(
            state={
                "artifact_lower": 0,
                "artifact_upper": 50,
                "cap_amount": 5,
                "deductible": 2,
                "hodl_lower": 10,
                "hodl_upper": 20,
                "holder_delta": 0,
                "holder_posted": 0,
                "lpv_lower": 7,
                "lpv_upper": 12,
                "n_notional": 10,
                "phase": 0,
                "witness_hodl_final": 0,
                "witness_lpv_final": 0,
                "writer_delta": 0,
                "writer_posted": 0,
            }
        )
