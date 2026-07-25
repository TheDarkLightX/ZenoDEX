from __future__ import annotations

from dataclasses import fields as dataclass_fields

import pytest

from src.core.settlement import (
    BalanceDelta,
    Fill,
    FillAction,
    LPDelta,
    ReserveDelta,
    Settlement,
)
from src.core.settlement_schema import (
    MAX_SETTLEMENT_AMOUNT_V1,
    MAX_SETTLEMENT_DELTA_COMPONENT_V1,
)
from src.core.settlement_snapshots import (
    OwnedBalanceDeltaV1,
    OwnedFillV1,
    OwnedLPDeltaV1,
    OwnedReserveDeltaV1,
    OwnedSettlementV1,
    canonical_owned_settlement_bytes_v1,
    snapshot_settlement,
)
from src.integration.operations import create_settlement_operation
from src.state.canonical import canonical_json_bytes
from src.state.snapshot_combinators import AdmitCode
from src.state.state_snapshots import StateAdmissionError

INTENT_ID = "0x" + "33" * 32


def _settlement() -> Settlement:
    return Settlement(
        module="TauSwap",
        version="0.1",
        batch_ref="batch-1",
        included_intents=[(INTENT_ID, FillAction.FILL)],
        fills=[
            Fill(
                INTENT_ID,
                FillAction.FILL,
                amount_in_filled=1,
                amount_out_filled=1,
                fee_paid=0,
                protocol_fee_paid=0,
                reserve_in_before=10,
                reserve_out_before=10,
            )
        ],
        balance_deltas=[BalanceDelta("alice", "A", 1, 0)],
        reserve_deltas=[ReserveDelta("pool", "A", 0, 1)],
        lp_deltas=[LPDelta("alice", "pool", 1, 0)],
        events=[{"kind": "fill", "payload": {"n": 1}}],
    )


def test_fcis_t_478_016_settlement_snapshot_detaches_every_source_alias() -> None:
    source = _settlement()
    owned = snapshot_settlement(source)
    before = canonical_owned_settlement_bytes_v1(owned)

    source.included_intents.append(("0x" + "44" * 32, FillAction.REJECT))
    source.fills[0].amount_in_filled = 99
    source.balance_deltas[0].delta_add = 99
    source.reserve_deltas.clear()
    source.lp_deltas.clear()
    assert source.events is not None
    source.events[0]["kind"] = "mutated"

    assert type(owned) is OwnedSettlementV1
    assert canonical_owned_settlement_bytes_v1(owned) == before


def test_fcis_t_478_017_foreign_subclasses_and_corrupted_owned_values_reject() -> None:
    class SettlementSubclass(Settlement):
        pass

    source = _settlement()
    subclass = SettlementSubclass(**vars(source))
    with pytest.raises(StateAdmissionError) as settlement_reject:
        snapshot_settlement(subclass)  # type: ignore[arg-type]
    assert settlement_reject.value.code is AdmitCode.WRONG_EXACT_TYPE

    class FillSubclass(Fill):
        pass

    source.fills[0] = FillSubclass(**vars(source.fills[0]))
    with pytest.raises(StateAdmissionError) as fill_reject:
        snapshot_settlement(source)
    assert fill_reject.value.code is AdmitCode.WRONG_EXACT_TYPE

    owned = snapshot_settlement(_settlement())
    object.__setattr__(owned, "module", "foreign")
    with pytest.raises(StateAdmissionError) as owned_reject:
        snapshot_settlement(owned)
    assert owned_reject.value.code is AdmitCode.NONCANONICAL_SCALAR


@pytest.mark.parametrize(
    ("field_name", "value", "expected_code"),
    (
        ("amount_in_filled", True, AdmitCode.WRONG_EXACT_TYPE),
        ("amount_in_filled", -1, AdmitCode.OUT_OF_RANGE),
        (
            "amount_in_filled",
            MAX_SETTLEMENT_AMOUNT_V1 + 1,
            AdmitCode.OUT_OF_RANGE,
        ),
    ),
)
def test_fcis_t_478_018_fill_scalars_have_exact_bounds(
    field_name: str,
    value: object,
    expected_code: AdmitCode,
) -> None:
    source = _settlement()
    setattr(source.fills[0], field_name, value)

    with pytest.raises(StateAdmissionError) as captured:
        snapshot_settlement(source)

    assert captured.value.code is expected_code


def test_fcis_t_478_018_delta_scalars_have_exact_aggregate_bound() -> None:
    source = _settlement()
    source.balance_deltas[0].delta_add = MAX_SETTLEMENT_DELTA_COMPONENT_V1 + 1

    with pytest.raises(StateAdmissionError) as captured:
        snapshot_settlement(source)

    assert captured.value.code is AdmitCode.OUT_OF_RANGE


def test_fcis_t_478_019_owned_records_contain_protocol_fields_only() -> None:
    assert tuple(field.name for field in dataclass_fields(OwnedFillV1)) == tuple(
        field.name for field in dataclass_fields(Fill)
    )
    assert tuple(field.name for field in dataclass_fields(OwnedBalanceDeltaV1)) == tuple(
        field.name for field in dataclass_fields(BalanceDelta)
    )
    assert tuple(field.name for field in dataclass_fields(OwnedReserveDeltaV1)) == tuple(
        field.name for field in dataclass_fields(ReserveDelta)
    )
    assert tuple(field.name for field in dataclass_fields(OwnedLPDeltaV1)) == tuple(
        field.name for field in dataclass_fields(LPDelta)
    )
    assert tuple(field.name for field in dataclass_fields(OwnedSettlementV1)) == tuple(
        field.name for field in dataclass_fields(Settlement)
    )


def test_fcis_t_478_020_events_use_bounded_owned_json() -> None:
    source = _settlement()
    assert source.events is not None
    source.events[0]["oversized"] = "x" * 4_097

    with pytest.raises(StateAdmissionError) as captured:
        snapshot_settlement(source)

    assert captured.value.code is AdmitCode.BYTE_LIMIT


def test_fcis_t_478_020_omitted_events_have_one_owned_representation() -> None:
    omitted = _settlement()
    omitted.events = None
    assert snapshot_settlement(omitted).events is None

    present_but_empty = _settlement()
    present_but_empty.events = []
    with pytest.raises(StateAdmissionError) as captured:
        snapshot_settlement(present_but_empty)
    assert captured.value.code is AdmitCode.ITEM_LIMIT


def test_fcis_t_478_024_settlement_bytes_match_mounted_operation_projection() -> None:
    source = _settlement()
    owned = snapshot_settlement(source)

    assert canonical_owned_settlement_bytes_v1(owned) == canonical_json_bytes(
        create_settlement_operation(source)["3"]
    )
