"""Invariant and mutation evidence for the external monotonic-anchor statement."""

from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.global_economic_monotonic_anchor_v1 import (
    GlobalEconomicMonotonicAnchorV1,
    decode_global_economic_monotonic_anchor_v1,
    require_global_economic_epoch_anchor_successor_v1,
    require_global_economic_monotonic_anchor_can_advance_v1,
)


def _root(index: int) -> str:
    return "0x" + f"{index:064x}"


def _anchor(*, anchor_sequence: int = 0, publication_sequence: int = 0):
    return GlobalEconomicMonotonicAnchorV1(
        anchor_namespace_root=_root(1),
        anchor_sequence=anchor_sequence,
        previous_anchor_root=(
            _root(0) if anchor_sequence == 0 else _root(20 + anchor_sequence)
        ),
        authority_root=_root(2),
        authority_generation=0,
        activation_id=_root(3),
        chain_id="tau-testnet",
        deployment_root=_root(4),
        epoch_store_root=_root(5),
        profile_root=_root(6),
        writer_epoch=7,
        publication_id=_root(3) if publication_sequence == 0 else _root(30),
        publication_sequence=publication_sequence,
        height=10 + publication_sequence,
        state_root=_root(8 + publication_sequence),
        commit_id=_root(0) if publication_sequence == 0 else _root(31),
        certificate_root=_root(9 + publication_sequence),
    )


def test_anchor_canonical_roundtrip_owns_the_complete_coordinates() -> None:
    # Arrange
    anchor = _anchor()

    # Act
    decoded = decode_global_economic_monotonic_anchor_v1(anchor.canonical_bytes)

    # Assert
    assert decoded == anchor
    assert decoded.anchor_root == anchor.anchor_root


@pytest.mark.parametrize(
    "field",
    (
        "anchor_namespace_root",
        "authority_root",
        "activation_id",
        "deployment_root",
        "epoch_store_root",
        "profile_root",
    ),
)
def test_epoch_anchor_successor_kills_every_root_binding_mutant(field: str) -> None:
    # Arrange: one exact adjacent epoch-anchor transition.
    current = _anchor()
    successor = replace(
        _anchor(anchor_sequence=1, publication_sequence=1),
        previous_anchor_root=current.anchor_root,
    )
    require_global_economic_epoch_anchor_successor_v1(current, successor)

    # Act / Assert: changing any bound root cannot remain an epoch successor.
    with pytest.raises(ValueError):
        require_global_economic_epoch_anchor_successor_v1(
            current,
            replace(successor, **{field: _root(60)}),
        )


@pytest.mark.parametrize(
    ("field", "value"),
    (
        ("anchor_sequence", True),
        ("authority_generation", False),
        ("writer_epoch", True),
        ("publication_sequence", False),
        ("height", True),
    ),
)
def test_anchor_rejects_boolean_integer_aliases(field: str, value: object) -> None:
    with pytest.raises(TypeError, match="exact integer"):
        replace(_anchor(), **{field: value})


def test_epoch_anchor_successor_rejects_skip_replay_and_wrong_previous_root() -> None:
    # Arrange
    current = _anchor()
    successor = replace(
        _anchor(anchor_sequence=1, publication_sequence=1),
        previous_anchor_root=current.anchor_root,
    )

    # Act / Assert
    with pytest.raises(ValueError, match="anchor sequence"):
        require_global_economic_epoch_anchor_successor_v1(
            current,
            replace(successor, anchor_sequence=2),
        )
    with pytest.raises(ValueError, match="publication sequence"):
        require_global_economic_epoch_anchor_successor_v1(
            current,
            replace(successor, publication_sequence=2),
        )
    with pytest.raises(ValueError, match="previous root"):
        require_global_economic_epoch_anchor_successor_v1(
            current,
            replace(successor, previous_anchor_root=_root(62)),
        )


def test_anchor_u64_boundaries_reject_overflow_and_forbid_successor_at_maximum() -> None:
    maximum = (1 << 64) - 1
    current = replace(
        _anchor(anchor_sequence=maximum, publication_sequence=0),
        previous_anchor_root=_root(63),
    )

    with pytest.raises(ValueError, match="cannot advance"):
        require_global_economic_epoch_anchor_successor_v1(current, current)
    with pytest.raises(ValueError, match="height cannot advance"):
        require_global_economic_monotonic_anchor_can_advance_v1(
            replace(_anchor(), height=maximum)
        )
    with pytest.raises(ValueError, match="unsigned 64-bit"):
        replace(_anchor(), anchor_sequence=maximum + 1)
