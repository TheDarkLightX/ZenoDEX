"""Adversarial structural-integrity tests for closed FCIS owned maps."""

from __future__ import annotations

from types import MappingProxyType
from typing import Callable, cast

import pytest

# The inherited package initializer has a direct state-first import cycle.
# Normal package initialization remains the supported test path for this slice.
import src.core as _core_package  # noqa: F401
from src.state.lp import LPTable
from src.state.lp_duration_transitions import (
    LPDurationEventV1,
    LPDurationTransitionCodeV1,
    LPDurationTransitionOkV1,
    LPDurationTransitionRejectV1,
    apply_lp_position_events_v1,
)
from src.state.owned_collections import OwnedMapV1, owned_map_structure_is_exact_v1
from src.state.state_snapshot_values import CommittedLPTableV1
from src.state.state_snapshots import snapshot_lp_table


def _exact_lp() -> CommittedLPTableV1:
    source = LPTable()
    source.set("owner", "pool", 1_000)
    source.set_last_mint_timestamp("owner", "pool", 100)
    return snapshot_lp_table(source)


def _balance_map(state: CommittedLPTableV1) -> OwnedMapV1[tuple[str, str], int]:
    return cast(
        OwnedMapV1[tuple[str, str], int],
        object.__getattribute__(state, "_balances"),
    )


def _replace_index_with_plain_dict(owned: OwnedMapV1[tuple[str, str], int]) -> None:
    object.__setattr__(owned, "_index", dict(owned.entries))


def _add_hidden_index_entry(owned: OwnedMapV1[tuple[str, str], int]) -> None:
    index = dict(owned.entries)
    index[("hidden", "pool")] = 7
    object.__setattr__(owned, "_index", MappingProxyType(index))


def _remove_index_entry(owned: OwnedMapV1[tuple[str, str], int]) -> None:
    object.__setattr__(owned, "_index", MappingProxyType({}))


def _replace_index_value(owned: OwnedMapV1[tuple[str, str], int]) -> None:
    key, value = owned.entries[0]
    replacement = int(str(value))
    assert replacement == value and replacement is not value
    object.__setattr__(owned, "_index", MappingProxyType({key: replacement}))


def _replace_index_key_identity(owned: OwnedMapV1[tuple[str, str], int]) -> None:
    key, value = owned.entries[0]
    replacement_key = tuple([*key])
    assert replacement_key == key and replacement_key is not key
    object.__setattr__(owned, "_index", MappingProxyType({replacement_key: value}))


def _remove_canonical_entry(owned: OwnedMapV1[tuple[str, str], int]) -> None:
    object.__setattr__(owned, "_entries", ())


def _replace_entries_with_list(owned: OwnedMapV1[tuple[str, str], int]) -> None:
    object.__setattr__(owned, "_entries", list(owned.entries))


def _replace_entry_with_non_pair(owned: OwnedMapV1[tuple[str, str], int]) -> None:
    key, value = owned.entries[0]
    object.__setattr__(owned, "_entries", ((key, value, 0),))


def _replace_revision_with_non_string(owned: OwnedMapV1[tuple[str, str], int]) -> None:
    object.__setattr__(owned, "_schema_revision", 1)


@pytest.mark.parametrize(
    "corrupt",
    (
        _replace_index_with_plain_dict,
        _add_hidden_index_entry,
        _remove_index_entry,
        _replace_index_value,
        _replace_index_key_identity,
        _remove_canonical_entry,
        _replace_entries_with_list,
        _replace_entry_with_non_pair,
        _replace_revision_with_non_string,
    ),
)
def test_owned_map_integrity_rejects_hostile_structure_without_reconstruction(
    corrupt: Callable[[OwnedMapV1[tuple[str, str], int]], None],
) -> None:
    state = _exact_lp()
    owned = _balance_map(state)
    assert owned_map_structure_is_exact_v1(owned) is True

    corrupt(owned)

    assert owned_map_structure_is_exact_v1(owned) is False
    with pytest.raises(TypeError):
        state.__post_init__()


def test_committed_lp_revalidation_rejects_wrong_exact_schema_metadata() -> None:
    state = _exact_lp()
    owned = _balance_map(state)
    object.__setattr__(owned, "_schema_id", "zenodex/lp/wrong")

    assert owned_map_structure_is_exact_v1(owned) is True
    with pytest.raises(TypeError, match="schema metadata mismatch"):
        state.__post_init__()


def test_committed_lp_revalidation_rejects_coherently_corrupted_domain_entries() -> None:
    state = _exact_lp()
    owned = _balance_map(state)
    _key, value = owned.entries[0]
    invalid_key = (True, "pool")
    object.__setattr__(owned, "_entries", ((invalid_key, value),))
    object.__setattr__(
        owned,
        "_index",
        MappingProxyType({invalid_key: value}),
    )

    assert owned_map_structure_is_exact_v1(owned) is True
    with pytest.raises(TypeError):
        state.__post_init__()

    result = apply_lp_position_events_v1(
        state,
        (),
        now=500,
        policy=None,
    )
    assert type(result) is LPDurationTransitionRejectV1
    assert result.code is LPDurationTransitionCodeV1.INVALID_PRESTATE


def test_exact_lp_noop_retains_the_original_validated_prestate() -> None:
    state = _exact_lp()

    result = apply_lp_position_events_v1(
        state,
        (),
        now=500,
        policy=None,
    )

    assert type(result) is LPDurationTransitionOkV1
    assert result.state is state
    assert result.patch is None


def test_exact_lp_transition_preserves_the_existing_result_contract() -> None:
    state = _exact_lp()

    result = apply_lp_position_events_v1(
        state,
        (LPDurationEventV1(("owner", "pool"), 25, 0),),
        now=500,
        policy=None,
    )

    assert type(result) is LPDurationTransitionOkV1
    assert result.patch is not None
    assert result.state.get("owner", "pool") == 1_025
    assert result.state.get_last_mint_timestamp("owner", "pool") == 500
    assert state.get("owner", "pool") == 1_000
    assert state.get_last_mint_timestamp("owner", "pool") == 100


def test_exact_lp_rejects_a_corrupted_lookup_index_before_any_candidate() -> None:
    state = _exact_lp()
    _add_hidden_index_entry(_balance_map(state))

    result = apply_lp_position_events_v1(
        state,
        (),
        now=500,
        policy=None,
    )

    assert type(result) is LPDurationTransitionRejectV1
    assert result.code is LPDurationTransitionCodeV1.INVALID_PRESTATE
    assert result.path == ("state",)
    assert not hasattr(result, "state")
    assert not hasattr(result, "patch")
