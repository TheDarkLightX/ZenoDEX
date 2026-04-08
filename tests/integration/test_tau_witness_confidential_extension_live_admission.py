from __future__ import annotations

import pytest

from src.integration.tau_witness import (
    CONFIDENTIAL_EXTENSION_LIVE_ADMISSION_V1,
    build_confidential_extension_live_admission_v1_step,
)


def test_build_confidential_extension_live_admission_v1_step() -> None:
    step = build_confidential_extension_live_admission_v1_step(
        do_execute=1,
        receipt_verified=1,
        policy_digest_match=1,
        request_unused=1,
    )
    assert CONFIDENTIAL_EXTENSION_LIVE_ADMISSION_V1.spec_id == "confidential_extension_live_admission_v1"
    assert step == {"i1": 1, "i2": 1, "i3": 1, "i4": 1}


def test_build_confidential_extension_live_admission_v1_step_rejects_bad_flags() -> None:
    with pytest.raises(ValueError, match="do_execute must be 0 or 1"):
        build_confidential_extension_live_admission_v1_step(
            do_execute=2,
            receipt_verified=1,
            policy_digest_match=1,
            request_unused=1,
        )
