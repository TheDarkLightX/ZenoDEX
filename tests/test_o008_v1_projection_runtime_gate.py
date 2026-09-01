"""Runtime binding of the V1 terminal and outbox projections (O-008 replay gate).

The O-008 admission core scans the pinned source bytes; this gate binds the
*imported* classes: field order from ``dataclasses.fields``, canonical keys from a
live ``to_canonical`` call, unknown-field rejection at construction, frozen
instances, the class objects' defining module, and the state containers' element
annotations. It is executed only under ``--replay`` and reported NOT_RUN
otherwise. Authority: NONE.
"""

from __future__ import annotations

import dataclasses
import inspect
from pathlib import Path

import pytest

from src.core import global_settlement_types_v1 as types_v1
from src.core.global_settlement_types_v1 import (
    GlobalEconomicStateV1,
    LaneIdV1,
    OutboxStateV1,
    OutboxStatusV1,
    TerminalObligationStatusV1,
    TerminalObligationV1,
)

ROOT = Path(__file__).resolve().parents[1]
TYPES_PATH = "src/core/global_settlement_types_v1.py"
TERMINAL_FIELDS = ("obligation_id", "lane_id", "claimant", "asset", "amount_atoms", "status")
OUTBOX_FIELDS = ("effect_id", "destination_id", "payload_hash", "commit_id", "status")
ROOT_HEX = "0x" + "1" * 64


def _terminal() -> TerminalObligationV1:
    return TerminalObligationV1("terminal-1", LaneIdV1.ASSET_TRANSFER, "alice", "USD", 1, TerminalObligationStatusV1.OPEN)


def _outbox() -> OutboxStateV1:
    return OutboxStateV1(ROOT_HEX, "dest-1", ROOT_HEX, ROOT_HEX, OutboxStatusV1.PENDING)


def test_terminal_record_runtime_fields_and_canonical_keys_are_exact() -> None:
    assert tuple(f.name for f in dataclasses.fields(TerminalObligationV1)) == TERMINAL_FIELDS
    assert tuple(_terminal().to_canonical()) == TERMINAL_FIELDS


def test_outbox_record_runtime_fields_and_canonical_keys_are_exact() -> None:
    assert tuple(f.name for f in dataclasses.fields(OutboxStateV1)) == OUTBOX_FIELDS
    assert tuple(_outbox().to_canonical()) == OUTBOX_FIELDS


@pytest.mark.parametrize("extra", ["liability_domain", "custody_principal"])
def test_terminal_record_rejects_unknown_fields_at_construction(extra: str) -> None:
    with pytest.raises(TypeError):
        TerminalObligationV1(
            "terminal-1", LaneIdV1.ASSET_TRANSFER, "alice", "USD", 1, TerminalObligationStatusV1.OPEN, **{extra: "x"}
        )


@pytest.mark.parametrize("extra", ["asset", "amount_atoms"])
def test_outbox_record_rejects_unknown_fields_at_construction(extra: str) -> None:
    with pytest.raises(TypeError):
        OutboxStateV1(ROOT_HEX, "dest-1", ROOT_HEX, ROOT_HEX, OutboxStatusV1.PENDING, **{extra: 1})


def test_records_are_frozen_slots_classes_defined_in_the_pinned_module() -> None:
    for cls, instance in ((TerminalObligationV1, _terminal()), (OutboxStateV1, _outbox())):
        assert cls.__module__ == types_v1.__name__
        assert Path(inspect.getsourcefile(cls) or "").resolve() == (ROOT / TYPES_PATH).resolve()
        assert cls.__dataclass_params__.frozen is True
        assert not hasattr(instance, "__dict__")
        with pytest.raises(dataclasses.FrozenInstanceError):
            setattr(instance, dataclasses.fields(cls)[0].name, "mutated")


def test_state_containers_hold_exactly_the_record_types() -> None:
    annotations = {f.name: f.type for f in dataclasses.fields(GlobalEconomicStateV1)}
    assert annotations["terminal_obligations"] == "tuple[TerminalObligationV1, ...]"
    assert annotations["outbox"] == "tuple[OutboxStateV1, ...]"
    assert types_v1.TerminalObligationV1 is TerminalObligationV1
    assert types_v1.OutboxStateV1 is OutboxStateV1
