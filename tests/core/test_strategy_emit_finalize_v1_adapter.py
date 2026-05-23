from __future__ import annotations

import pytest

from src.kernels.python.strategy_emit_finalize_v1_adapter import check_strategy_emit_finalize


def test_check_strategy_emit_finalize_accepts_valid_emit() -> None:
    result = check_strategy_emit_finalize(
        emit_requested=True,
        system_compose_ok=True,
        submit_bundle_ok=True,
    )
    assert result.ok is True
    assert result.error is None


def test_check_strategy_emit_finalize_accepts_non_emit_state() -> None:
    result = check_strategy_emit_finalize(
        emit_requested=False,
        system_compose_ok=False,
        submit_bundle_ok=False,
    )
    assert result.ok is True
    assert result.error is None


@pytest.mark.parametrize(
    ("system_compose_ok", "submit_bundle_ok", "error"),
    [
        (False, True, "emit_finalize_system_compose_rejected"),
        (True, False, "emit_finalize_submit_bundle_rejected"),
    ],
)
def test_check_strategy_emit_finalize_rejects_invalid_inputs(
    system_compose_ok: bool,
    submit_bundle_ok: bool,
    error: str,
) -> None:
    result = check_strategy_emit_finalize(
        emit_requested=True,
        system_compose_ok=system_compose_ok,
        submit_bundle_ok=submit_bundle_ok,
    )
    assert result.ok is False
    assert result.error == error


def test_check_strategy_emit_finalize_rejects_bad_types() -> None:
    with pytest.raises(TypeError, match="emit_requested must be a bool"):
        check_strategy_emit_finalize(
            emit_requested=1,
            system_compose_ok=True,
            submit_bundle_ok=True,
        )
