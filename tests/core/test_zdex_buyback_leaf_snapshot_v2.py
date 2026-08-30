"""Ownership and shape evidence for the buyback successor leaf adapter."""

from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.global_settlement_types_v1 import LaneIdV1, LaneWriteV1
from src.core.zdex_buyback_leaf_snapshot_v2 import (
    ZDEXSpotBuybackLeafSnapshotV2,
    ZDEXTokenomicsBuybackLeafSnapshotV2,
    snapshot_zdex_spot_buyback_leaf_v2,
    snapshot_zdex_tokenomics_buyback_leaf_v2,
)
from tests.core.test_zdex_tokenomics_buyback_transition_v2 import (
    _accepted as _tokenomics_accepted,
)
from tests.core.test_zdex_tokenomics_buyback_transition_v2 import (
    _candidate as _tokenomics_candidate,
)
from tests.core.test_zdex_tokenomics_buyback_transition_v2 import (
    _spot_accepted,
)


def test_snapshot_adapter_owns_exact_validated_leaf_outputs() -> None:
    # Arrange.
    candidate = _tokenomics_candidate()
    spot = _spot_accepted(candidate.intent_input)
    tokenomics = _tokenomics_accepted(candidate)

    # Act.
    spot_snapshot = snapshot_zdex_spot_buyback_leaf_v2(spot)
    tokenomics_snapshot = snapshot_zdex_tokenomics_buyback_leaf_v2(tokenomics)

    # Assert.
    assert type(spot_snapshot) is ZDEXSpotBuybackLeafSnapshotV2
    assert type(tokenomics_snapshot) is ZDEXTokenomicsBuybackLeafSnapshotV2
    assert spot_snapshot.journal is not spot.journal
    assert spot_snapshot.journal.context is not spot.journal.context
    assert spot_snapshot.journal.context.coordinates is not spot.journal.context.coordinates
    assert spot_snapshot.effects is not spot.effects
    assert tokenomics_snapshot.journal is not tokenomics.journal
    assert tokenomics_snapshot.effects is not tokenomics.effects
    assert spot_snapshot.journal_root == spot.journal.journal_root
    assert tokenomics_snapshot.journal_root == tokenomics.journal.journal_root
    assert spot_snapshot.effect_plan_root == spot.effects.effect_plan_root
    assert tokenomics_snapshot.effect_plan_root == tokenomics.effects.effect_plan_root


def test_snapshot_adapter_survives_retained_source_mutation() -> None:
    # Arrange.
    candidate = _tokenomics_candidate()
    spot = _spot_accepted(candidate.intent_input)
    tokenomics = _tokenomics_accepted(candidate)
    spot_snapshot = snapshot_zdex_spot_buyback_leaf_v2(spot)
    tokenomics_snapshot = snapshot_zdex_tokenomics_buyback_leaf_v2(tokenomics)
    stable = (
        spot_snapshot.snapshot_root,
        tokenomics_snapshot.snapshot_root,
    )

    # Act.
    object.__setattr__(
        spot.journal.context.coordinates,
        "quote_port_root",
        "0x" + "a1" * 32,
    )
    object.__setattr__(
        tokenomics.journal,
        "quote_port_root",
        "0x" + "a2" * 32,
    )

    # Assert.
    assert (spot_snapshot.snapshot_root, tokenomics_snapshot.snapshot_root) == stable
    spot_snapshot.validate()
    tokenomics_snapshot.validate()


def test_snapshot_adapter_rejects_stale_accepted_wrapper() -> None:
    # Arrange.
    candidate = _tokenomics_candidate()
    spot = _spot_accepted(candidate.intent_input)
    object.__setattr__(
        spot.journal.context.coordinates,
        "quote_port_root",
        "0x" + "a3" * 32,
    )

    # Act / Assert.
    with pytest.raises((TypeError, ValueError)):
        snapshot_zdex_spot_buyback_leaf_v2(spot)


def test_snapshot_shape_rejects_wrong_lane_write() -> None:
    # Arrange.
    candidate = _tokenomics_candidate()
    spot = snapshot_zdex_spot_buyback_leaf_v2(_spot_accepted(candidate.intent_input))
    write = spot.effects.lane_writes[0]
    wrong_effects = replace(
        spot.effects,
        lane_writes=(
            LaneWriteV1(LaneIdV1.ZDEX_TOKENOMICS, write.pre_root, write.post_root),
        ),
    )

    # Act / Assert.
    with pytest.raises(ValueError, match="Spot lane write"):
        ZDEXSpotBuybackLeafSnapshotV2(spot.journal, wrong_effects)


def test_tokenomics_snapshot_requires_one_same_occurrence_consumption() -> None:
    # Arrange.
    tokenomics = snapshot_zdex_tokenomics_buyback_leaf_v2(
        _tokenomics_accepted(_tokenomics_candidate())
    )
    missing = replace(tokenomics.effects, occurrence_consumptions=())
    rebound_journal = replace(
        tokenomics.journal,
        effect_plan_root=missing.effect_plan_root,
    )

    # Act / Assert.
    with pytest.raises(ValueError, match="one occurrence consumption"):
        ZDEXTokenomicsBuybackLeafSnapshotV2(rebound_journal, missing)


def test_snapshot_adapter_requires_exact_accepted_types() -> None:
    with pytest.raises(TypeError, match="exact accepted result"):
        snapshot_zdex_spot_buyback_leaf_v2(object())
    with pytest.raises(TypeError, match="exact accepted result"):
        snapshot_zdex_tokenomics_buyback_leaf_v2(object())
