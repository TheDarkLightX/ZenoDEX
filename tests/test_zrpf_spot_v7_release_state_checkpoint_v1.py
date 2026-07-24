from __future__ import annotations

import hashlib
import json
from collections.abc import Callable
from dataclasses import replace

import pytest

from tools.zrpf_spot_v7_release_state_checkpoint_v1 import (
    RELEASE_STATE_CHECKPOINT_SCHEMA_V1,
    ZERO_DIGEST_HEX_V1,
    SpotV7ReleaseStateCheckpointRejectV1,
    SpotV7ReleaseStateCheckpointV1,
    build_spot_v7_release_state_checkpoint_v1,
    parse_exact_spot_v7_release_state_checkpoint_v1,
    validate_spot_v7_release_state_checkpoint_successor_v1,
)


def _root(label: str) -> str:
    return hashlib.sha256(label.encode("ascii")).hexdigest()


def _build(
    *,
    database_revision: int,
    last_evaluation_epoch: int,
    release_state_root: str,
    current_candidate_id: str | None,
    current_candidate_sha256: str | None,
    current_release_revision: int | None,
    current_select_input_id: str | None,
    current_revocation_record_id: str | None,
    parent_release_checkpoint_hash: str,
    release_checkpoint_sequence: int,
) -> bytes:
    return build_spot_v7_release_state_checkpoint_v1(
        application_id="zenodex",
        chain_id="zenodex-test-chain-v1",
        domain_id="spot-v7-test-domain",
        release_profile="zenodex_spot_v7_bounded_single_action_v1",
        store_identity_hash=_root("store-identity"),
        database_revision=database_revision,
        last_evaluation_epoch=last_evaluation_epoch,
        release_state_root=release_state_root,
        current_candidate_id=current_candidate_id,
        current_candidate_sha256=current_candidate_sha256,
        current_release_revision=current_release_revision,
        current_select_input_id=current_select_input_id,
        current_revocation_record_id=current_revocation_record_id,
        parent_release_checkpoint_hash=parent_release_checkpoint_hash,
        release_checkpoint_sequence=release_checkpoint_sequence,
    )


def _genesis_bytes() -> bytes:
    return _build(
        database_revision=0,
        last_evaluation_epoch=0,
        release_state_root=_root("release-genesis"),
        current_candidate_id=None,
        current_candidate_sha256=None,
        current_release_revision=None,
        current_select_input_id=None,
        current_revocation_record_id=None,
        parent_release_checkpoint_hash=ZERO_DIGEST_HEX_V1,
        release_checkpoint_sequence=0,
    )


def _selected_bytes(
    *,
    parent_hash: str,
    sequence: int = 1,
    database_revision: int = 1,
    evaluation_epoch: int = 10,
    candidate_label: str = "candidate-1",
    release_revision: int = 1,
) -> bytes:
    return _build(
        database_revision=database_revision,
        last_evaluation_epoch=evaluation_epoch,
        release_state_root=_root(f"release-state-{sequence}"),
        current_candidate_id=_root(candidate_label),
        current_candidate_sha256=_root(f"{candidate_label}-bytes"),
        current_release_revision=release_revision,
        current_select_input_id=_root(f"select-{sequence}"),
        current_revocation_record_id=None,
        parent_release_checkpoint_hash=parent_hash,
        release_checkpoint_sequence=sequence,
    )


def _revoked_bytes(*, parent_hash: str) -> bytes:
    return _build(
        database_revision=2,
        last_evaluation_epoch=11,
        release_state_root=_root("release-state-2"),
        current_candidate_id=_root("candidate-1"),
        current_candidate_sha256=_root("candidate-1-bytes"),
        current_release_revision=1,
        current_select_input_id=_root("select-1"),
        current_revocation_record_id=_root("revocation-1"),
        parent_release_checkpoint_hash=parent_hash,
        release_checkpoint_sequence=2,
    )


def test_genesis_round_trip_is_canonical_and_authority_false() -> None:
    raw = _genesis_bytes()
    value = parse_exact_spot_v7_release_state_checkpoint_v1(raw)

    assert raw.endswith(b"\n")
    assert value.canonical_bytes == raw
    assert value.schema == RELEASE_STATE_CHECKPOINT_SCHEMA_V1
    assert value.database_revision == 0
    assert value.release_checkpoint_sequence == 0
    assert value.parent_release_checkpoint_hash == ZERO_DIGEST_HEX_V1
    assert value.current_candidate_id is None
    assert value.external_finality_authenticated is False
    assert value.external_monotonic_state_anchor_verified is False
    assert value.hostile_same_interpreter_resistance_established is False
    assert value.release_authority is False
    assert value.runtime_authority is False
    assert value.settlement_authority is False
    assert value.production_authority is False


def test_genesis_hash_vector_is_stable() -> None:
    raw = _genesis_bytes()
    value = parse_exact_spot_v7_release_state_checkpoint_v1(raw)

    assert len(raw) == 828
    assert hashlib.sha256(raw).hexdigest() == (
        "9d3006807131b39e8850e56926208e9da807f22c47b3eaf52ea911e5b825aa10"
    )
    assert value.release_checkpoint_hash == (
        "f6340c079d94823f9dab7540629a961287aa3a7b633062a324cf79f240eb732a"
    )


def test_selected_then_revoked_successor_chain_is_exact() -> None:
    genesis = parse_exact_spot_v7_release_state_checkpoint_v1(_genesis_bytes())
    selected = parse_exact_spot_v7_release_state_checkpoint_v1(
        _selected_bytes(parent_hash=genesis.release_checkpoint_hash)
    )
    revoked = parse_exact_spot_v7_release_state_checkpoint_v1(
        _revoked_bytes(parent_hash=selected.release_checkpoint_hash)
    )

    assert validate_spot_v7_release_state_checkpoint_successor_v1(genesis, selected) is selected
    assert validate_spot_v7_release_state_checkpoint_successor_v1(selected, revoked) is revoked
    assert revoked.current_candidate_id == selected.current_candidate_id
    assert revoked.current_select_input_id == selected.current_select_input_id
    assert revoked.current_revocation_record_id == _root("revocation-1")


def test_selected_successor_advances_release_lineage() -> None:
    genesis = parse_exact_spot_v7_release_state_checkpoint_v1(_genesis_bytes())
    first = parse_exact_spot_v7_release_state_checkpoint_v1(
        _selected_bytes(parent_hash=genesis.release_checkpoint_hash)
    )
    second = parse_exact_spot_v7_release_state_checkpoint_v1(
        _selected_bytes(
            parent_hash=first.release_checkpoint_hash,
            sequence=2,
            database_revision=2,
            evaluation_epoch=12,
            candidate_label="candidate-2",
            release_revision=2,
        )
    )

    assert validate_spot_v7_release_state_checkpoint_successor_v1(first, second) is second


@pytest.mark.parametrize(
    "kwargs",
    (
        {"database_revision": True},
        {"last_evaluation_epoch": -1},
        {"store_identity_hash": "AA" * 32},
        {"release_state_root": ZERO_DIGEST_HEX_V1},
        {"application_id": ""},
        {"chain_id": "chain\nsmuggle"},
        {"release_checkpoint_sequence": 1},
    ),
)
def test_invalid_width_scope_root_or_genesis_framing_rejects(kwargs: dict[str, object]) -> None:
    values: dict[str, object] = {
        "application_id": "zenodex",
        "chain_id": "zenodex-test-chain-v1",
        "domain_id": "spot-v7-test-domain",
        "release_profile": "zenodex_spot_v7_bounded_single_action_v1",
        "store_identity_hash": _root("store-identity"),
        "database_revision": 0,
        "last_evaluation_epoch": 0,
        "release_state_root": _root("release-genesis"),
        "current_candidate_id": None,
        "current_candidate_sha256": None,
        "current_release_revision": None,
        "current_select_input_id": None,
        "current_revocation_record_id": None,
        "parent_release_checkpoint_hash": ZERO_DIGEST_HEX_V1,
        "release_checkpoint_sequence": 0,
    }
    values.update(kwargs)
    with pytest.raises(SpotV7ReleaseStateCheckpointRejectV1):
        build_spot_v7_release_state_checkpoint_v1(**values)  # type: ignore[arg-type]


@pytest.mark.parametrize(
    ("candidate_id", "candidate_sha256", "release_revision", "select_id", "revocation_id"),
    (
        (_root("candidate"), None, 1, _root("select"), None),
        (None, _root("candidate-bytes"), None, None, None),
        (_root("candidate"), _root("candidate-bytes"), None, _root("select"), None),
        (_root("candidate"), _root("candidate-bytes"), 1, None, None),
        (None, None, None, None, _root("revocation")),
    ),
)
def test_partial_state_variants_reject(
    candidate_id: str | None,
    candidate_sha256: str | None,
    release_revision: int | None,
    select_id: str | None,
    revocation_id: str | None,
) -> None:
    with pytest.raises(SpotV7ReleaseStateCheckpointRejectV1):
        _build(
            database_revision=1,
            last_evaluation_epoch=1,
            release_state_root=_root("partial"),
            current_candidate_id=candidate_id,
            current_candidate_sha256=candidate_sha256,
            current_release_revision=release_revision,
            current_select_input_id=select_id,
            current_revocation_record_id=revocation_id,
            parent_release_checkpoint_hash=_root("parent"),
            release_checkpoint_sequence=1,
        )


def test_checkpoint_sequence_must_equal_database_revision() -> None:
    with pytest.raises(SpotV7ReleaseStateCheckpointRejectV1):
        _build(
            database_revision=2,
            last_evaluation_epoch=10,
            release_state_root=_root("mismatched-revision"),
            current_candidate_id=_root("candidate"),
            current_candidate_sha256=_root("candidate-bytes"),
            current_release_revision=1,
            current_select_input_id=_root("select"),
            current_revocation_record_id=None,
            parent_release_checkpoint_hash=_root("parent"),
            release_checkpoint_sequence=1,
        )


@pytest.mark.parametrize(
    "mutator",
    (
        lambda body: body.update(extra="unknown"),
        lambda body: body.update(database_revision=1.0),
        lambda body: body.update(release_state_root="AA" * 32),
        lambda body: body.update(release_checkpoint_hash=_root("forged")),
    ),
)
def test_unknown_float_noncanonical_or_hash_substitution_rejects(
    mutator: Callable[[dict[str, object]], None],
) -> None:
    body = json.loads(_genesis_bytes())
    mutator(body)
    raw = json.dumps(body, sort_keys=True, separators=(",", ":"), allow_nan=False).encode() + b"\n"
    with pytest.raises(SpotV7ReleaseStateCheckpointRejectV1):
        parse_exact_spot_v7_release_state_checkpoint_v1(raw)


def test_duplicate_key_and_escaped_duplicate_key_reject() -> None:
    for raw in (
        b'{"schema":"a","schema":"b"}\n',
        b'{"schema":"a","sch\\u0065ma":"b"}\n',
    ):
        with pytest.raises(SpotV7ReleaseStateCheckpointRejectV1):
            parse_exact_spot_v7_release_state_checkpoint_v1(raw)


@pytest.mark.parametrize(
    "child_factory",
    (
        lambda parent: _selected_bytes(
            parent_hash=_root("wrong-parent"),
            sequence=2,
            database_revision=2,
            evaluation_epoch=11,
            candidate_label="candidate-2",
            release_revision=2,
        ),
        lambda parent: _selected_bytes(
            parent_hash=parent.release_checkpoint_hash,
            sequence=3,
            database_revision=3,
            evaluation_epoch=11,
            candidate_label="candidate-2",
            release_revision=2,
        ),
        lambda parent: _selected_bytes(
            parent_hash=parent.release_checkpoint_hash,
            sequence=2,
            database_revision=2,
            evaluation_epoch=9,
            candidate_label="candidate-2",
            release_revision=2,
        ),
        lambda parent: _selected_bytes(
            parent_hash=parent.release_checkpoint_hash,
            sequence=2,
            database_revision=2,
            evaluation_epoch=11,
            candidate_label="candidate-2",
            release_revision=3,
        ),
    ),
)
def test_fork_gap_stale_or_release_revision_skip_rejects(
    child_factory: Callable[[SpotV7ReleaseStateCheckpointV1], bytes],
) -> None:
    genesis = parse_exact_spot_v7_release_state_checkpoint_v1(_genesis_bytes())
    parent = parse_exact_spot_v7_release_state_checkpoint_v1(
        _selected_bytes(parent_hash=genesis.release_checkpoint_hash)
    )
    child = parse_exact_spot_v7_release_state_checkpoint_v1(child_factory(parent))
    with pytest.raises(SpotV7ReleaseStateCheckpointRejectV1):
        validate_spot_v7_release_state_checkpoint_successor_v1(parent, child)


def test_revocation_must_preserve_selected_candidate_and_is_terminal() -> None:
    genesis = parse_exact_spot_v7_release_state_checkpoint_v1(_genesis_bytes())
    selected = parse_exact_spot_v7_release_state_checkpoint_v1(
        _selected_bytes(parent_hash=genesis.release_checkpoint_hash)
    )
    revoked = parse_exact_spot_v7_release_state_checkpoint_v1(
        _revoked_bytes(parent_hash=selected.release_checkpoint_hash)
    )
    wrong_revocation = parse_exact_spot_v7_release_state_checkpoint_v1(
        _build(
            database_revision=2,
            last_evaluation_epoch=11,
            release_state_root=_root("wrong-revoked-state"),
            current_candidate_id=_root("different-candidate"),
            current_candidate_sha256=selected.current_candidate_sha256,
            current_release_revision=selected.current_release_revision,
            current_select_input_id=selected.current_select_input_id,
            current_revocation_record_id=_root("revocation-2"),
            parent_release_checkpoint_hash=selected.release_checkpoint_hash,
            release_checkpoint_sequence=2,
        )
    )
    with pytest.raises(SpotV7ReleaseStateCheckpointRejectV1):
        validate_spot_v7_release_state_checkpoint_successor_v1(selected, wrong_revocation)

    after_revocation = parse_exact_spot_v7_release_state_checkpoint_v1(
        _selected_bytes(
            parent_hash=revoked.release_checkpoint_hash,
            sequence=3,
            database_revision=3,
            evaluation_epoch=12,
            candidate_label="candidate-2",
            release_revision=2,
        )
    )
    with pytest.raises(SpotV7ReleaseStateCheckpointRejectV1):
        validate_spot_v7_release_state_checkpoint_successor_v1(revoked, after_revocation)


def test_nominal_checkpoint_field_substitution_cannot_enter_successor_chain() -> None:
    genesis = parse_exact_spot_v7_release_state_checkpoint_v1(_genesis_bytes())
    selected = parse_exact_spot_v7_release_state_checkpoint_v1(
        _selected_bytes(parent_hash=genesis.release_checkpoint_hash)
    )
    substituted = replace(selected, release_state_root=_root("substituted-state"))

    with pytest.raises(SpotV7ReleaseStateCheckpointRejectV1):
        validate_spot_v7_release_state_checkpoint_successor_v1(genesis, substituted)
