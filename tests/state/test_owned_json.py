from __future__ import annotations

import pytest

from src.state.owned_collections import OwnedMapV1
from src.state.owned_json import project_owned_json, snapshot_owned_json
from src.state.snapshot_combinators import AdmitCode
from src.state.state_snapshots import StateAdmissionError


def test_fcis_t_478_001_owned_json_accepts_exact_closed_values() -> None:
    source = {"b": [None, True, 7, "text"], "a": {"nested": -1}}

    owned = snapshot_owned_json(source)

    assert type(owned) is OwnedMapV1
    assert tuple(owned) == ("a", "b")
    assert project_owned_json(owned) == {
        "a": {"nested": -1},
        "b": [None, True, 7, "text"],
    }


@pytest.mark.parametrize(
    "source",
    (
        1.0,
        b"bytes",
        bytearray(b"bytes"),
        {1, 2},
        frozenset((1, 2)),
    ),
)
def test_fcis_t_478_002_owned_json_rejects_foreign_exact_types(source: object) -> None:
    with pytest.raises(StateAdmissionError) as captured:
        snapshot_owned_json(source)  # type: ignore[arg-type]

    assert captured.value.code is AdmitCode.WRONG_EXACT_TYPE


def test_fcis_t_478_003_owned_json_rejects_cycles_and_string_overflow() -> None:
    cycle: list[object] = []
    cycle.append(cycle)
    with pytest.raises(StateAdmissionError) as cycle_reject:
        snapshot_owned_json(cycle)  # type: ignore[arg-type]
    assert cycle_reject.value.code is AdmitCode.CYCLE

    with pytest.raises(StateAdmissionError) as string_reject:
        snapshot_owned_json("x" * 4_097)
    assert string_reject.value.code is AdmitCode.BYTE_LIMIT


def test_fcis_t_478_006_projection_and_source_mutation_cannot_change_owned_json() -> None:
    nested = [1, 2]
    source = {"nested": nested}
    owned = snapshot_owned_json(source)
    projection = project_owned_json(owned)

    nested.append(3)
    source["extra"] = 4
    assert isinstance(projection, dict)
    projection["extra"] = 5

    assert project_owned_json(owned) == {"nested": [1, 2]}
