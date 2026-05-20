from __future__ import annotations

import pytest

from src.kernels.python.strategy_tx_envelope_guard_v1_adapter import check_strategy_tx_envelope


def test_strategy_tx_envelope_guard_accepts_no_tx_and_scoped_tx() -> None:
    no_tx = check_strategy_tx_envelope(
        tx_requested=False,
        sequence_number=None,
        expiration_time=None,
        fee_limit="0",
        operations={},
    )
    assert no_tx.ok is True
    assert no_tx.error is None

    tx = check_strategy_tx_envelope(
        tx_requested=True,
        sequence_number=9,
        expiration_time=999,
        fee_limit="0",
        operations={"2": [{"intent_id": "iid.1"}]},
    )
    assert tx.ok is True
    assert tx.error is None


@pytest.mark.parametrize(
    ("kwargs", "error"),
    [
        (
            {
                "tx_requested": True,
                "sequence_number": 9,
                "expiration_time": None,
                "fee_limit": "0",
                "operations": {"2": [{"intent_id": "iid.1"}]},
            },
            "tx_envelope_pairing_rejected",
        ),
        (
            {
                "tx_requested": True,
                "sequence_number": -1,
                "expiration_time": 999,
                "fee_limit": "0",
                "operations": {"2": [{"intent_id": "iid.1"}]},
            },
            "tx_envelope_sequence_rejected",
        ),
        (
            {
                "tx_requested": True,
                "sequence_number": 9,
                "expiration_time": 0,
                "fee_limit": "0",
                "operations": {"2": [{"intent_id": "iid.1"}]},
            },
            "tx_envelope_expiration_rejected",
        ),
        (
            {
                "tx_requested": True,
                "sequence_number": 9,
                "expiration_time": 999,
                "fee_limit": "00",
                "operations": {"2": [{"intent_id": "iid.1"}]},
            },
            "tx_envelope_fee_limit_rejected",
        ),
        (
            {
                "tx_requested": True,
                "sequence_number": 9,
                "expiration_time": 999,
                "fee_limit": "0",
                "operations": {"2": [{"intent_id": "iid.1"}], "3": {}},
            },
            "tx_envelope_stream_scope_rejected",
        ),
    ],
)
def test_strategy_tx_envelope_guard_rejects_invalid_inputs(
    kwargs: dict[str, object],
    error: str,
) -> None:
    result = check_strategy_tx_envelope(**kwargs)
    assert result.ok is False
    assert result.error == error


def test_strategy_tx_envelope_guard_rejects_bad_types() -> None:
    with pytest.raises(TypeError, match="tx_requested must be a bool"):
        check_strategy_tx_envelope(
            tx_requested=1,
            sequence_number=None,
            expiration_time=None,
            fee_limit="0",
            operations={},
        )
    with pytest.raises(TypeError, match="operations must be a mapping"):
        check_strategy_tx_envelope(
            tx_requested=True,
            sequence_number=1,
            expiration_time=2,
            fee_limit="0",
            operations=[],
        )
    with pytest.raises(TypeError, match="operations keys must be strings"):
        check_strategy_tx_envelope(
            tx_requested=True,
            sequence_number=1,
            expiration_time=2,
            fee_limit="0",
            operations={2: []},
        )


@pytest.mark.parametrize(
    ("fee_limit", "ok", "error"),
    [
        (True, False, "tx_envelope_fee_limit_rejected"),
        (7, True, None),
        ([], False, "tx_envelope_fee_limit_rejected"),
        ("", False, "tx_envelope_fee_limit_rejected"),
    ],
)
def test_strategy_tx_envelope_guard_covers_fee_limit_shapes(
    fee_limit: object,
    ok: bool,
    error: str | None,
) -> None:
    result = check_strategy_tx_envelope(
        tx_requested=True,
        sequence_number=9,
        expiration_time=999,
        fee_limit=fee_limit,
        operations={"2": [{"intent_id": "iid.1"}]},
    )
    assert result.ok is ok
    assert result.error == error
