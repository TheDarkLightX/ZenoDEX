from __future__ import annotations

import pytest

from src.integration.tau_witness import (
    AUTOTRADER_EMIT_FINALIZE_V1,
    build_autotrader_emit_finalize_v1_step,
)


def test_build_autotrader_emit_finalize_v1_step() -> None:
    step = build_autotrader_emit_finalize_v1_step(
        emit_requested=1,
        system_compose_ok=1,
        submit_bundle_ok=1,
    )
    assert AUTOTRADER_EMIT_FINALIZE_V1.spec_id == "autotrader_emit_finalize_v1"
    assert step == {"i1": 1, "i2": 1, "i3": 1}


def test_build_autotrader_emit_finalize_v1_step_rejects_bad_bools() -> None:
    with pytest.raises(ValueError, match="submit_bundle_ok must be 0 or 1"):
        build_autotrader_emit_finalize_v1_step(
            emit_requested=1,
            system_compose_ok=1,
            submit_bundle_ok=2,
        )
