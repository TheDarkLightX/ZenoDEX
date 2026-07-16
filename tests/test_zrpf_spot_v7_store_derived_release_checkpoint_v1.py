from __future__ import annotations

import copy
import json
import pickle
from pathlib import Path
from typing import Any, cast

import pytest

from tests.test_zrpf_spot_v7_authenticated_release_selection_store_v2 import (
    _authenticated_selection,
)
from tests.test_zrpf_spot_v7_authenticated_release_state_store_v3 import (
    EVALUATION_EPOCH,
    _new_store,
    _successor_selection,
    _v2_genesis_cursor,
)
from tools import zrpf_spot_v7_store_derived_release_checkpoint_v1 as derived_v1
from tools.zrpf_spot_v7_release_state_checkpoint_v1 import (
    parse_exact_spot_v7_release_state_checkpoint_v1,
)


def test_genesis_derivation_requires_exact_store_replay_and_private_type(tmp_path: Path) -> None:
    store, _selection, _revocation, _candidate = _new_store(tmp_path)
    checkpoint = derived_v1.derive_store_release_state_checkpoint_v1(store)

    document = parse_exact_spot_v7_release_state_checkpoint_v1(checkpoint.canonical_bytes)
    assert document.database_revision == 0
    assert document.release_checkpoint_sequence == 0
    assert checkpoint.checkpoint_hash == document.release_checkpoint_hash
    assert checkpoint.store_replay_currentness_at_use_verified is False
    assert checkpoint.external_monotonic_state_anchor_verified is False
    assert checkpoint.release_authority is False
    assert checkpoint.runtime_authority is False
    assert checkpoint.settlement_authority is False
    assert checkpoint.production_authority is False
    assert type(checkpoint).__name__.startswith("_StoreDerived")

    with pytest.raises(TypeError, match="direct Store V3 replay"):
        derived_v1._StoreDerivedReleaseStateCheckpointV1()
    with pytest.raises(TypeError, match="immutable"):
        checkpoint._canonical_bytes = b"{}\n"
    with pytest.raises(TypeError, match="cannot be copied"):
        copy.copy(checkpoint)
    with pytest.raises(TypeError, match="cannot be deep-copied"):
        copy.deepcopy(checkpoint)
    with pytest.raises(TypeError, match="cannot be serialized"):
        pickle.dumps(checkpoint)


def test_selection_and_terminal_revocation_derive_one_exact_chain(tmp_path: Path) -> None:
    store, selection, revocation, _candidate = _new_store(tmp_path)
    genesis = derived_v1.derive_store_release_state_checkpoint_v1(store)

    store.commit(selection)
    selected = derived_v1.derive_store_release_state_checkpoint_v1(store)
    selected_document = parse_exact_spot_v7_release_state_checkpoint_v1(selected.canonical_bytes)
    assert selected_document.database_revision == 1
    assert selected_document.current_revocation_record_id is None
    assert selected.parent_checkpoint_hash == genesis.checkpoint_hash

    store.commit(revocation)
    revoked = derived_v1.derive_store_release_state_checkpoint_v1(store)
    revoked_document = parse_exact_spot_v7_release_state_checkpoint_v1(revoked.canonical_bytes)
    assert revoked_document.database_revision == 2
    assert revoked_document.current_revocation_record_id is not None
    assert revoked.parent_checkpoint_hash == selected.checkpoint_hash


def test_parent_provenance_cannot_be_supplied_by_a_caller(tmp_path: Path) -> None:
    store, _selection, _revocation, _candidate = _new_store(tmp_path)
    checkpoint = derived_v1.derive_store_release_state_checkpoint_v1(store)

    with pytest.raises(TypeError, match="unexpected keyword argument"):
        derived_v1.derive_store_release_state_checkpoint_v1(
            store,
            parent=checkpoint,  # type: ignore[call-arg]
        )


def test_same_identity_divergent_store_cannot_supply_parent_lineage(tmp_path: Path) -> None:
    store_a, selection_a, _revocation_a, _candidate_a = _new_store(
        tmp_path,
        name="a.sqlite3",
    )
    store_b, _selection_b, _revocation_b, _candidate_b = _new_store(
        tmp_path,
        name="b.sqlite3",
    )
    store_a.commit(selection_a)
    selected_a = derived_v1.derive_store_release_state_checkpoint_v1(store_a)

    divergent_b, _candidate, _pins = _authenticated_selection(
        cursor=_v2_genesis_cursor(),
        revision=1,
        parent_candidate_id=None,
        variant=1,
        evaluation_epoch=EVALUATION_EPOCH,
    )
    store_b.commit(divergent_b)
    selected_b = derived_v1.derive_store_release_state_checkpoint_v1(store_b)

    assert store_a.identity == store_b.identity
    assert selected_a.checkpoint_hash != selected_b.checkpoint_hash

    successor_a = _successor_selection(store_a.read_cursor(), variant=2)
    store_a.commit(successor_a)
    head_a = derived_v1.derive_store_release_state_checkpoint_v1(store_a)
    assert head_a.parent_checkpoint_hash == selected_a.checkpoint_hash
    assert head_a.parent_checkpoint_hash != selected_b.checkpoint_hash


def test_non_genesis_checkpoint_reconstructs_after_cold_restart(tmp_path: Path) -> None:
    store, selection, revocation, _candidate = _new_store(tmp_path)
    store.commit(selection)
    store.commit(revocation)
    before_restart = derived_v1.derive_store_release_state_checkpoint_v1(store)

    reopened = store.__class__(store.path, identity=store.identity)
    after_restart = derived_v1.derive_store_release_state_checkpoint_v1(reopened)

    assert after_restart.canonical_bytes == before_restart.canonical_bytes
    assert after_restart.checkpoint_hash == before_restart.checkpoint_hash
    assert after_restart.parent_checkpoint_hash == before_restart.parent_checkpoint_hash


def test_raw_document_and_internal_byte_mutation_cannot_supply_provenance(tmp_path: Path) -> None:
    store, _selection, _revocation, _candidate = _new_store(tmp_path)
    checkpoint = derived_v1.derive_store_release_state_checkpoint_v1(store)
    raw_document = parse_exact_spot_v7_release_state_checkpoint_v1(checkpoint.canonical_bytes)

    with pytest.raises(TypeError):
        cast(Any, derived_v1.derive_store_release_state_checkpoint_v1)(
            store,
            raw_document,
        )

    body = json.loads(checkpoint.canonical_bytes)
    body["release_state_root"] = "11" * 32
    object.__setattr__(
        checkpoint,
        "_canonical_bytes",
        json.dumps(body, sort_keys=True, separators=(",", ":")).encode() + b"\n",
    )
    with pytest.raises(derived_v1.StoreDerivedReleaseCheckpointRejectV1):
        _ = checkpoint.checkpoint_hash
