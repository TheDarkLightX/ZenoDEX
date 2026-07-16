from __future__ import annotations

import copy
import hashlib
import inspect
import json
import pickle
from collections.abc import Callable
from typing import Any

import pytest

from tools import zrpf_spot_v7_highest_observed_release_event_watermark_v1 as watermark
from tools.zrpf_spot_v7_release_state_checkpoint_v1 import (
    ZERO_DIGEST_HEX_V1,
    SpotV7ReleaseStateCheckpointV1,
    build_spot_v7_release_state_checkpoint_v1,
    parse_exact_spot_v7_release_state_checkpoint_v1,
)


def _root(label: str) -> str:
    return hashlib.sha256(label.encode("ascii")).hexdigest()


def _build_checkpoint(
    *,
    database_revision: int,
    evaluation_epoch: int,
    release_state_root: str,
    candidate_label: str | None,
    release_revision: int | None,
    select_label: str | None,
    revocation_label: str | None,
    parent_hash: str,
    chain_id: str = "zenodex-test-chain-v1",
) -> bytes:
    return build_spot_v7_release_state_checkpoint_v1(
        application_id="zenodex",
        chain_id=chain_id,
        domain_id="spot-v7-test-domain",
        release_profile="zenodex_spot_v7_bounded_single_action_v1",
        store_identity_hash=_root("store-identity"),
        database_revision=database_revision,
        last_evaluation_epoch=evaluation_epoch,
        release_state_root=release_state_root,
        current_candidate_id=None if candidate_label is None else _root(candidate_label),
        current_candidate_sha256=(
            None if candidate_label is None else _root(f"{candidate_label}-bytes")
        ),
        current_release_revision=release_revision,
        current_select_input_id=None if select_label is None else _root(select_label),
        current_revocation_record_id=(
            None if revocation_label is None else _root(revocation_label)
        ),
        parent_release_checkpoint_hash=parent_hash,
        release_checkpoint_sequence=database_revision,
    )


def _genesis() -> SpotV7ReleaseStateCheckpointV1:
    return parse_exact_spot_v7_release_state_checkpoint_v1(
        _build_checkpoint(
            database_revision=0,
            evaluation_epoch=0,
            release_state_root=_root("release-genesis"),
            candidate_label=None,
            release_revision=None,
            select_label=None,
            revocation_label=None,
            parent_hash=ZERO_DIGEST_HEX_V1,
        )
    )


def _selection(
    parent: SpotV7ReleaseStateCheckpointV1,
    *,
    candidate_label: str = "candidate-1",
) -> SpotV7ReleaseStateCheckpointV1:
    revision = parent.database_revision + 1
    return parse_exact_spot_v7_release_state_checkpoint_v1(
        _build_checkpoint(
            database_revision=revision,
            evaluation_epoch=10 + revision,
            release_state_root=_root(f"release-state-{revision}"),
            candidate_label=candidate_label,
            release_revision=revision,
            select_label=f"select-{revision}",
            revocation_label=None,
            parent_hash=parent.release_checkpoint_hash,
        )
    )


def _revocation(
    selected: SpotV7ReleaseStateCheckpointV1,
) -> SpotV7ReleaseStateCheckpointV1:
    revision = selected.database_revision + 1
    return parse_exact_spot_v7_release_state_checkpoint_v1(
        _build_checkpoint(
            database_revision=revision,
            evaluation_epoch=20,
            release_state_root=_root("release-state-revoked"),
            candidate_label="candidate-1",
            release_revision=selected.current_release_revision,
            select_label="select-1",
            revocation_label="revocation-1",
            parent_hash=selected.release_checkpoint_hash,
        )
    )


def _event_kind(
    checkpoint: SpotV7ReleaseStateCheckpointV1,
) -> watermark.ObservedReleaseEventKindV1:
    if checkpoint.is_genesis:
        return watermark.ObservedReleaseEventKindV1.GENESIS
    if checkpoint.is_revoked:
        return watermark.ObservedReleaseEventKindV1.REVOKE
    return watermark.ObservedReleaseEventKindV1.SELECT


def _watermark_bytes(
    *,
    finalized: SpotV7ReleaseStateCheckpointV1,
    observed: SpotV7ReleaseStateCheckpointV1,
    external_position: int = 41,
    **overrides: Any,
) -> bytes:
    values: dict[str, object] = {
        "application_id": observed.application_id,
        "chain_id": observed.chain_id,
        "domain_id": observed.domain_id,
        "release_profile": observed.release_profile,
        "store_identity_hash": observed.store_identity_hash,
        "external_backend_id": "test-external-monotonic-log-v1",
        "external_position": external_position,
        "external_backend_commitment": _root(f"external-commitment-{external_position}"),
        "external_parent_commitment": (
            ZERO_DIGEST_HEX_V1
            if external_position == 0
            else _root(f"external-parent-{external_position - 1}")
        ),
        "latest_finalized_checkpoint_hash": finalized.release_checkpoint_hash,
        "latest_finalized_database_revision": finalized.database_revision,
        "highest_observed_checkpoint_hash": observed.release_checkpoint_hash,
        "highest_observed_database_revision": observed.database_revision,
        "highest_observed_release_state_root": observed.release_state_root,
        "highest_observed_event_kind": _event_kind(observed),
        "highest_observed_select_input_id": observed.current_select_input_id,
        "highest_observed_revocation_record_id": observed.current_revocation_record_id,
    }
    values.update(overrides)
    return watermark.build_spot_v7_highest_observed_release_event_watermark_v1(
        **values  # type: ignore[arg-type]
    )


def _assess(
    *,
    local: SpotV7ReleaseStateCheckpointV1,
    finalized: SpotV7ReleaseStateCheckpointV1,
    observed: SpotV7ReleaseStateCheckpointV1,
    watermark_bytes: bytes | None = None,
) -> watermark._AuthorityNeutralReleaseCurrentnessAssessmentV1:
    return watermark.assess_exact_spot_v7_release_currentness_against_watermark_v1(
        exact_local_checkpoint_bytes=local.canonical_bytes,
        exact_finalized_checkpoint_bytes=finalized.canonical_bytes,
        exact_highest_observed_checkpoint_bytes=observed.canonical_bytes,
        exact_watermark_bytes=(
            _watermark_bytes(finalized=finalized, observed=observed)
            if watermark_bytes is None
            else watermark_bytes
        ),
    )


def test_watermark_round_trip_is_canonical_and_authority_false() -> None:
    genesis = _genesis()
    selected = _selection(genesis)
    raw = _watermark_bytes(finalized=selected, observed=selected)
    value = watermark.parse_exact_spot_v7_highest_observed_release_event_watermark_v1(raw)

    assert value.canonical_bytes == raw
    assert value.latest_finalized_checkpoint_hash == selected.release_checkpoint_hash
    assert value.highest_observed_checkpoint_hash == selected.release_checkpoint_hash
    assert value.highest_observed_event_kind is watermark.ObservedReleaseEventKindV1.SELECT
    assert value.watermark_hash != ZERO_DIGEST_HEX_V1
    assert value.external_finality_authenticated is False
    assert value.external_monotonicity_authenticated is False
    assert value.store_derived_checkpoint_provenance_verified is False
    assert value.rollback_safe_currentness_established is False
    assert value.release_authority is False
    assert value.runtime_authority is False
    assert value.settlement_authority is False
    assert value.production_authority is False


def test_watermark_hash_vector_is_stable() -> None:
    genesis = _genesis()
    selected = _selection(genesis)
    raw = _watermark_bytes(finalized=selected, observed=selected)
    value = watermark.parse_exact_spot_v7_highest_observed_release_event_watermark_v1(raw)

    assert len(raw) == 1_252
    assert hashlib.sha256(raw).hexdigest() == (
        "f4e4fe88edb2b2a89164dbbd21fa48c0506ae14767000940c5546319ea724132"
    )
    assert value.watermark_hash == (
        "c2539a47958c1b6d8435118bda87ea51599554b793794068d6a1f078db7858d9"
    )


def test_f1_pending_r2_restore_l1_remains_paused() -> None:
    genesis = _genesis()
    finalized_selection_f1 = _selection(genesis)
    pending_revocation_r2 = _revocation(finalized_selection_f1)

    result = _assess(
        local=finalized_selection_f1,
        finalized=finalized_selection_f1,
        observed=pending_revocation_r2,
    )

    assert result.disposition is watermark.ReleaseCurrentnessDispositionV1.PAUSED
    assert (
        result.relation
        is watermark.ReleaseCurrentnessRelationV1.LOCAL_MATCHES_FINALIZED_BEHIND_PENDING_REVOCATION
    )
    assert result.blocker_code == "PENDING_REVOCATION_WATERMARK_UNAUTHENTICATED"
    assert result.local_database_revision == 1
    assert result.highest_observed_database_revision == 2
    assert result.external_finality_authenticated is False
    assert result.external_monotonicity_authenticated is False
    assert result.store_derived_checkpoint_provenance_verified is False
    assert result.rollback_safe_currentness_established is False
    assert result.release_authority is False
    assert result.runtime_authority is False
    assert result.settlement_authority is False
    assert result.production_authority is False


def test_local_pending_revocation_is_paused_before_rollback() -> None:
    genesis = _genesis()
    finalized = _selection(genesis)
    revoked = _revocation(finalized)

    result = _assess(local=revoked, finalized=finalized, observed=revoked)

    assert (
        result.relation
        is watermark.ReleaseCurrentnessRelationV1.LOCAL_MATCHES_REVOKED_HIGHEST_OBSERVED
    )
    assert result.blocker_code == "REVOKED_RELEASE_WATERMARK_UNAUTHENTICATED"
    assert result.disposition is watermark.ReleaseCurrentnessDispositionV1.PAUSED


def test_matching_finalized_selection_stays_paused_without_backend_authentication() -> None:
    genesis = _genesis()
    selected = _selection(genesis)

    result = _assess(local=selected, finalized=selected, observed=selected)

    assert (
        result.relation is watermark.ReleaseCurrentnessRelationV1.LOCAL_MATCHES_FINALIZED_SELECTION
    )
    assert result.blocker_code == "EXTERNAL_WATERMARK_AND_FINALITY_AUTHENTICATION_REQUIRED"
    assert result.disposition is watermark.ReleaseCurrentnessDispositionV1.PAUSED


def test_matching_genesis_is_never_operational() -> None:
    genesis = _genesis()

    result = _assess(local=genesis, finalized=genesis, observed=genesis)

    assert result.relation is watermark.ReleaseCurrentnessRelationV1.LOCAL_MATCHES_GENESIS
    assert result.blocker_code == "GENESIS_NOT_OPERATIONAL"
    assert result.disposition is watermark.ReleaseCurrentnessDispositionV1.PAUSED


def test_matching_pending_selection_is_paused_until_finalized() -> None:
    genesis = _genesis()
    finalized = _selection(genesis)
    pending = _selection(finalized, candidate_label="candidate-2")

    result = _assess(local=pending, finalized=finalized, observed=pending)

    assert result.relation is watermark.ReleaseCurrentnessRelationV1.LOCAL_MATCHES_PENDING_SELECTION
    assert result.blocker_code == "PENDING_SELECTION_WATERMARK_UNAUTHENTICATED"

    rolled_back = _assess(local=finalized, finalized=finalized, observed=pending)
    assert (
        rolled_back.relation
        is watermark.ReleaseCurrentnessRelationV1.LOCAL_MATCHES_FINALIZED_BEHIND_PENDING_SELECTION
    )
    assert rolled_back.blocker_code == "PENDING_SELECTION_WATERMARK_UNAUTHENTICATED"


def test_local_behind_finalized_fork_and_stale_watermark_are_typed_pauses() -> None:
    genesis = _genesis()
    selected = _selection(genesis)
    successor = _selection(selected, candidate_label="candidate-2")

    behind = _assess(local=genesis, finalized=selected, observed=selected)
    assert behind.relation is watermark.ReleaseCurrentnessRelationV1.LOCAL_BEHIND_FINALIZED
    assert behind.blocker_code == "LOCAL_RELEASE_STATE_ROLLBACK_OR_INCOMPLETE"

    fork_bytes = _build_checkpoint(
        database_revision=1,
        evaluation_epoch=11,
        release_state_root=_root("fork-root"),
        candidate_label="fork-candidate",
        release_revision=1,
        select_label="fork-select",
        revocation_label=None,
        parent_hash=genesis.release_checkpoint_hash,
    )
    fork = parse_exact_spot_v7_release_state_checkpoint_v1(fork_bytes)
    forked = _assess(local=fork, finalized=selected, observed=selected)
    assert forked.relation is watermark.ReleaseCurrentnessRelationV1.LOCAL_FORK_AT_FINALIZED
    assert forked.blocker_code == "LOCAL_RELEASE_STATE_FORK"

    observed_revocation = _revocation(selected)
    observed_fork = _assess(
        local=successor,
        finalized=selected,
        observed=observed_revocation,
    )
    assert (
        observed_fork.relation
        is watermark.ReleaseCurrentnessRelationV1.LOCAL_FORK_AT_HIGHEST_OBSERVED
    )
    assert observed_fork.blocker_code == "LOCAL_RELEASE_STATE_FORK"

    stale = _assess(local=successor, finalized=selected, observed=selected)
    assert stale.relation is watermark.ReleaseCurrentnessRelationV1.LOCAL_AHEAD_OF_HIGHEST_OBSERVED
    assert stale.blocker_code == "HIGHEST_OBSERVED_WATERMARK_STALE"


def test_output_is_exact_deterministic_opaque_and_authority_false() -> None:
    genesis = _genesis()
    finalized = _selection(genesis)
    observed = _revocation(finalized)
    first = _assess(local=finalized, finalized=finalized, observed=observed)
    second = _assess(local=finalized, finalized=finalized, observed=observed)

    assert type(first).__name__.startswith("_AuthorityNeutral")
    assert first.canonical_assessment_bytes == second.canonical_assessment_bytes
    assert first.assessment_sha256 == hashlib.sha256(first.canonical_assessment_bytes).digest()
    assert len(first.canonical_assessment_bytes) == 1_876
    assert hashlib.sha256(first.canonical_assessment_bytes).hexdigest() == (
        "3562f31ad81e40d24d11e0e195583aba14aa3865b414aa403a34521a776a60e6"
    )
    document = json.loads(first.canonical_assessment_bytes)
    assert document["assessment_hash"] == (
        "8fe59c92d0a253b98d340f439b0e6acae6a5afb8ad16426d22afd474c675928e"
    )
    assert document["disposition"] == "PAUSED"
    assert document["external_finality_authenticated"] is False
    assert document["external_monotonicity_authenticated"] is False
    assert document["rollback_safe_currentness_established"] is False
    assert document["store_derived_checkpoint_provenance_verified"] is False
    assert document["release_authority"] is False
    assert document["runtime_authority"] is False
    assert document["settlement_authority"] is False
    assert document["production_authority"] is False

    with pytest.raises(TypeError, match="checked construction"):
        type(first)()
    with pytest.raises(TypeError, match="immutable"):
        first._local_database_revision = 99
    with pytest.raises(TypeError, match="explicit disposition handling"):
        bool(first)
    with pytest.raises(TypeError, match="cannot be copied"):
        copy.copy(first)
    with pytest.raises(TypeError, match="cannot be deep-copied"):
        copy.deepcopy(first)
    with pytest.raises(TypeError, match="cannot be serialized"):
        pickle.dumps(first)


@pytest.mark.parametrize(
    ("field", "replacement"),
    (
        ("_local_database_revision", 99),
        ("_blocker_code", "GENESIS_NOT_OPERATIONAL"),
        ("_relation", watermark.ReleaseCurrentnessRelationV1.LOCAL_MATCHES_GENESIS),
        ("_exact_watermark_bytes", b"{}\n"),
    ),
)
def test_same_interpreter_mutation_invalidates_every_data_projection(
    field: str,
    replacement: object,
) -> None:
    genesis = _genesis()
    finalized = _selection(genesis)
    observed = _revocation(finalized)
    result = _assess(local=finalized, finalized=finalized, observed=observed)
    object.__setattr__(result, field, replacement)

    with pytest.raises(ValueError, match="assessment was mutated"):
        _ = result.local_database_revision
    with pytest.raises(ValueError, match="assessment was mutated"):
        _ = result.canonical_assessment_bytes
    assert result.release_authority is False
    assert result.settlement_authority is False
    assert result.production_authority is False


@pytest.mark.parametrize(
    "mutator",
    (
        lambda body: body.update(extra="unknown"),
        lambda body: body.update(external_position=1.5),
        lambda body: body.update(external_position=True),
        lambda body: body.update(external_parent_commitment=ZERO_DIGEST_HEX_V1),
        lambda body: body.update(external_backend_id="bad\nbackend"),
        lambda body: body.update(highest_observed_release_state_root="AA" * 32),
        lambda body: body.update(watermark_hash=_root("forged")),
    ),
)
def test_unknown_float_invalid_token_noncanonical_or_hash_substitution_rejects(
    mutator: Callable[[dict[str, object]], None],
) -> None:
    genesis = _genesis()
    selected = _selection(genesis)
    body = json.loads(_watermark_bytes(finalized=selected, observed=selected))
    mutator(body)
    raw = json.dumps(body, sort_keys=True, separators=(",", ":"), allow_nan=False).encode() + b"\n"

    with pytest.raises(watermark.SpotV7HighestObservedReleaseEventWatermarkRejectV1):
        watermark.parse_exact_spot_v7_highest_observed_release_event_watermark_v1(raw)


def test_duplicate_escaped_duplicate_depth_and_oversize_reject() -> None:
    for raw in (
        b'{"schema":"a","schema":"b"}\n',
        b'{"schema":"a","sch\\u0065ma":"b"}\n',
        b'{"a":{"b":{"c":1}}}\n',
        b"{" + b'"x":"' + b"a" * watermark.MAX_HIGHEST_OBSERVED_WATERMARK_BYTES_V1 + b'"}\n',
    ):
        with pytest.raises(watermark.SpotV7HighestObservedReleaseEventWatermarkRejectV1):
            watermark.parse_exact_spot_v7_highest_observed_release_event_watermark_v1(raw)


def test_missing_field_and_noncanonical_document_forms_reject_exactly() -> None:
    genesis = _genesis()
    selected = _selection(genesis)
    canonical = _watermark_bytes(finalized=selected, observed=selected)
    missing = json.loads(canonical)
    del missing["chain_id"]
    missing_raw = (
        json.dumps(missing, sort_keys=True, separators=(",", ":"), allow_nan=False).encode() + b"\n"
    )

    with pytest.raises(
        watermark.SpotV7HighestObservedReleaseEventWatermarkRejectV1,
    ) as missing_error:
        watermark.parse_exact_spot_v7_highest_observed_release_event_watermark_v1(missing_raw)
    assert missing_error.value.code == "FIELD_SET_MISMATCH"

    for raw in (b" " + canonical, canonical.removesuffix(b"\n"), canonical + b"\n"):
        with pytest.raises(
            watermark.SpotV7HighestObservedReleaseEventWatermarkRejectV1,
        ) as noncanonical_error:
            watermark.parse_exact_spot_v7_highest_observed_release_event_watermark_v1(raw)
        assert noncanonical_error.value.code == "NONCANONICAL_JSON"


def test_u64_boundaries_and_event_shapes_reject_exactly() -> None:
    genesis = _genesis()
    selected = _selection(genesis)
    maximum = _watermark_bytes(
        finalized=selected,
        observed=selected,
        external_position=watermark.MAX_U64_V1,
    )
    assert (
        watermark.parse_exact_spot_v7_highest_observed_release_event_watermark_v1(
            maximum
        ).external_position
        == watermark.MAX_U64_V1
    )

    for invalid_position in (-1, watermark.MAX_U64_V1 + 1):
        with pytest.raises(
            watermark.SpotV7HighestObservedReleaseEventWatermarkRejectV1,
        ) as position_error:
            _watermark_bytes(
                finalized=selected,
                observed=selected,
                external_position=invalid_position,
            )
        assert position_error.value.code == "U64_REQUIRED"

    shape_cases: tuple[tuple[dict[str, Any], str], ...] = (
        (
            {
                "highest_observed_event_kind": watermark.ObservedReleaseEventKindV1.GENESIS,
            },
            "GENESIS_EVENT_SHAPE",
        ),
        (
            {
                "highest_observed_event_kind": watermark.ObservedReleaseEventKindV1.REVOKE,
            },
            "REVOKE_EVENT_SHAPE",
        ),
    )
    for overrides, expected_code in shape_cases:
        with pytest.raises(
            watermark.SpotV7HighestObservedReleaseEventWatermarkRejectV1,
        ) as shape_error:
            _watermark_bytes(finalized=selected, observed=selected, **overrides)
        assert shape_error.value.code == expected_code

    revoked = _revocation(selected)
    with pytest.raises(
        watermark.SpotV7HighestObservedReleaseEventWatermarkRejectV1,
    ) as revoked_shape_error:
        _watermark_bytes(
            finalized=selected,
            observed=revoked,
            highest_observed_event_kind=watermark.ObservedReleaseEventKindV1.SELECT,
        )
    assert revoked_shape_error.value.code == "SELECT_EVENT_SHAPE"


@pytest.mark.parametrize(
    "overrides",
    (
        {"latest_finalized_database_revision": 2},
        {"latest_finalized_checkpoint_hash": _root("wrong-finalized")},
        {"highest_observed_checkpoint_hash": _root("wrong-observed")},
        {"highest_observed_database_revision": 7},
        {"highest_observed_release_state_root": _root("wrong-state")},
        {"highest_observed_event_kind": watermark.ObservedReleaseEventKindV1.SELECT},
        {"highest_observed_select_input_id": _root("wrong-select")},
        {"highest_observed_revocation_record_id": _root("wrong-revocation")},
    ),
)
def test_watermark_checkpoint_binding_substitution_rejects(
    overrides: dict[str, Any],
) -> None:
    genesis = _genesis()
    finalized = _selection(genesis)
    observed = _revocation(finalized)
    with pytest.raises(watermark.SpotV7HighestObservedReleaseEventWatermarkRejectV1):
        raw = _watermark_bytes(finalized=finalized, observed=observed, **overrides)
        _assess(
            local=finalized,
            finalized=finalized,
            observed=observed,
            watermark_bytes=raw,
        )


def test_observed_checkpoint_must_equal_or_immediately_follow_finalized() -> None:
    genesis = _genesis()
    finalized = _selection(genesis)
    second = _selection(finalized, candidate_label="candidate-2")
    third = _selection(second, candidate_label="candidate-3")

    with pytest.raises(
        watermark.SpotV7HighestObservedReleaseEventWatermarkRejectV1,
        match="OBSERVED_FINALIZED_DISTANCE_UNSUPPORTED",
    ):
        _assess(local=finalized, finalized=finalized, observed=third)


def test_checkpoint_and_watermark_scope_substitution_rejects() -> None:
    genesis = _genesis()
    selected = _selection(genesis)
    wrong_local = parse_exact_spot_v7_release_state_checkpoint_v1(
        _build_checkpoint(
            database_revision=1,
            evaluation_epoch=11,
            release_state_root=_root("release-state-1"),
            candidate_label="candidate-1",
            release_revision=1,
            select_label="select-1",
            revocation_label=None,
            parent_hash=genesis.release_checkpoint_hash,
            chain_id="other-chain",
        )
    )
    with pytest.raises(
        watermark.SpotV7HighestObservedReleaseEventWatermarkRejectV1,
        match="SCOPE_MISMATCH",
    ):
        _assess(local=wrong_local, finalized=selected, observed=selected)

    wrong_watermark = _watermark_bytes(
        finalized=selected,
        observed=selected,
        chain_id="other-chain",
    )
    with pytest.raises(
        watermark.SpotV7HighestObservedReleaseEventWatermarkRejectV1,
        match="SCOPE_MISMATCH",
    ):
        _assess(
            local=selected,
            finalized=selected,
            observed=selected,
            watermark_bytes=wrong_watermark,
        )


def test_raw_watermark_has_no_authority_boolean_ingress() -> None:
    parameters = inspect.signature(
        watermark.build_spot_v7_highest_observed_release_event_watermark_v1
    ).parameters
    assessment_parameters = inspect.signature(
        watermark.assess_exact_spot_v7_release_currentness_against_watermark_v1
    ).parameters

    forbidden = {
        "verified",
        "authenticated",
        "external_monotonicity_authenticated",
        "external_finality_authenticated",
        "store_derived_checkpoint_provenance_verified",
        "rollback_safe_currentness_established",
        "release_authority",
        "runtime_authority",
        "settlement_authority",
        "production_authority",
    }
    assert forbidden.isdisjoint(parameters)
    assert forbidden.isdisjoint(assessment_parameters)
