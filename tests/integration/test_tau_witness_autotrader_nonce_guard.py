from __future__ import annotations

import pytest

from src.integration.tau_witness import (
    AUTOTRADER_NONCE_GUARD_V1,
    build_autotrader_nonce_guard_v1_step,
)


def test_build_autotrader_nonce_guard_v1_step() -> None:
    step = build_autotrader_nonce_guard_v1_step(intent_nonce=9, last_used_nonce=8, expected_nonce=9)
    assert AUTOTRADER_NONCE_GUARD_V1.spec_id == "autotrader_nonce_guard_v1"
    assert step == {"i1": 9, "i2": 8, "i3": 9}


def test_build_autotrader_nonce_guard_v1_step_rejects_bad_ranges() -> None:
    with pytest.raises(ValueError, match=r"intent_nonce out of bv\[32\] range"):
        build_autotrader_nonce_guard_v1_step(intent_nonce=-1, last_used_nonce=8, expected_nonce=9)
