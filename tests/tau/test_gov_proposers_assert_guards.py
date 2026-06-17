from __future__ import annotations

import pytest

from src.tau_specs.governance import gov_proposers
from src.tau_specs.governance.gov_proposers import energy_propose, layered_q_propose


def test_layered_q_propose_rejects_malformed_snapshot_without_assert(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(
        gov_proposers,
        "_snapshot_layered_table",
        lambda _artifact: {"regime": [], "actions": {}},
    )

    with pytest.raises(TypeError, match="plain dict regime/actions"):
        layered_q_propose((1,), (2,), {}, curr=10)


def test_energy_propose_rejects_malformed_targets_snapshot_without_assert(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(
        gov_proposers,
        "_snapshot_energy_model",
        lambda _artifact: {"targets": [], "w_track": 1, "w_move": 1},
    )

    with pytest.raises(TypeError, match="snapshot targets must be a plain dict"):
        energy_propose((1,), {}, curr=10, lo=0, hi=20, step=1)


def test_energy_propose_rejects_malformed_weight_snapshot_without_assert(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(
        gov_proposers,
        "_snapshot_energy_model",
        lambda _artifact: {"targets": {"1": 10}, "w_track": True, "w_move": 1},
    )

    with pytest.raises(TypeError, match="snapshot weights must be plain ints"):
        energy_propose((1,), {}, curr=10, lo=0, hi=20, step=1)
