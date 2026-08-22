"""Adversarial evidence for unmounted ordinary economic epoch durability."""

from __future__ import annotations

import json
import sqlite3
import subprocess
import sys
from collections.abc import Callable
from dataclasses import replace
from pathlib import Path

import pytest

import src.integration.global_economic_epoch_journal_v1 as journal_module
from src.core.global_economic_durable_activation_v1 import (
    DurableEconomicInitialStateBundleV1,
    prepare_durable_economic_initial_state_bundle_v1,
)
from src.core.global_settlement_types_v1 import (
    MAX_CYCLE_BUDGET_V1,
    MAX_JOURNAL_BYTES_V1,
    canonical_global_bytes_v1,
    hash_global_v1,
)
from src.integration.global_economic_commit_v1 import (
    CommitOutcomeStatusV1,
    EconomicEpochBodyAndStateV1,
)
from src.integration.global_economic_durable_epoch_v1 import (
    _BUNDLE_MAGIC_V1,
    DURABLE_ECONOMIC_EPOCH_SCHEMA_V1,
    DurableEconomicEpochBundleV1,
    DurableEconomicEpochMaterialV1,
    DurableEconomicEpochRecordV1,
    DurableEconomicPublicationHeadV1,
    _decode_payload_sections_v1,
    _payload_root_v1,
    decode_durable_economic_epoch_bundle_v1,
    prepare_durable_economic_epoch_bundle_v1,
)
from src.integration.global_economic_epoch_journal_v1 import (
    DurableEconomicEpochCasTokenV1,
    DurableEconomicEpochCommitOutcomeV1,
    DurableEconomicEpochCommitStatusV1,
    DurableEconomicEpochWriteCapabilityV1,
    GlobalEconomicEpochJournalV1,
    _create_epoch_journal_for_verified_publisher_v1,
    _DurableEconomicEpochCommitFaultV1,
    _open_epoch_journal_for_verified_publisher_v1,
    _SimulatedDurableEconomicEpochCrashV1,
)
from tests.core.test_global_settlement_abi_v1 import (
    _commit_port,
    _epoch_admission_fixture,
    _initial_state_admission,
    _profile,
    _publisher_verified_epoch,
    _RecordingReceiptVerifier,
    _state,
)


def _fixture_v1(*, receipt_bytes: bytes = b"durable-ordinary-epoch-receipt"):
    profile, route = _profile()
    pre_state = _state(profile, height=0)
    post_state = _state(profile, height=1)
    activation = prepare_durable_economic_initial_state_bundle_v1(
        _initial_state_admission(profile, pre_state),
        source_head=None,
    )
    publisher, verified, body, _, _, _ = _publisher_verified_epoch(
        profile,
        route,
        pre_state,
        post_state,
        receipt_bytes=receipt_bytes,
    )
    outcome = publisher.commit_verified_economic_epoch(
        expected_head=pre_state.state_root,
        expected_profile=profile.profile_id,
        verified_epoch=verified,
        body_and_state=body,
    )
    assert outcome.status is CommitOutcomeStatusV1.COMMITTED
    assert outcome.record is not None
    source_head = DurableEconomicPublicationHeadV1.from_activation(activation.head)
    epoch = prepare_durable_economic_epoch_bundle_v1(
        DurableEconomicEpochMaterialV1(
            source_head=source_head,
            profile=profile,
            certificate=verified.certificate,
            effect_plan=verified.effect_plan,
            body_and_state=body,
            published_epoch=outcome.record,
            receipt_bytes=receipt_bytes,
        )
    )
    return activation, source_head, epoch


def _create_writer_v1(
    path: Path,
    activation: DurableEconomicInitialStateBundleV1,
) -> tuple[GlobalEconomicEpochJournalV1, DurableEconomicEpochWriteCapabilityV1]:
    return _create_epoch_journal_for_verified_publisher_v1(path, activation)


def _open_writer_v1(
    path: Path,
) -> tuple[GlobalEconomicEpochJournalV1, DurableEconomicEpochWriteCapabilityV1]:
    return _open_epoch_journal_for_verified_publisher_v1(path)


def _commit_v1(
    journal: GlobalEconomicEpochJournalV1,
    write_capability: DurableEconomicEpochWriteCapabilityV1,
    epoch: DurableEconomicEpochBundleV1,
    cas_token: DurableEconomicEpochCasTokenV1,
) -> DurableEconomicEpochCommitOutcomeV1:
    return journal._commit_epoch_from_verified_publisher_v1(
        epoch,
        cas_token,
        write_capability,
    )


def _stored_epoch_rows_v1(path: Path) -> tuple[int, str, bytes]:
    with sqlite3.connect(path) as connection:
        count = connection.execute("SELECT COUNT(*) FROM economic_epochs").fetchone()[0]
        head_id = connection.execute(
            "SELECT publication_id FROM current_head WHERE singleton = 1"
        ).fetchone()[0]
        bundle_bytes = connection.execute(
            "SELECT bundle_bytes FROM economic_epochs WHERE publication_id = ?",
            (head_id,),
        ).fetchone()[0]
    assert type(count) is int
    assert type(head_id) is str
    assert type(bundle_bytes) is bytes
    return count, head_id, bundle_bytes


def _two_epoch_chain_v1(*, reuse_commit_id: bool = False):
    activation, _, first = _fixture_v1(receipt_bytes=b"stateful-epoch-one")
    payload = json.loads(first.payload)
    state = payload["body_and_state"]["post_state"]
    state["height"] = first.record.height + 1
    post_state_root = hash_global_v1("global-economic-state-root-v1", state)
    body = payload["body_and_state"]
    body["pre_state_root"] = first.record.post_state_root
    body_commitment = hash_global_v1(
        "global-economic-epoch-body-v1",
        {
            "pre_state_root": body["pre_state_root"],
            "post_state_root": post_state_root,
            "ordered_command_body_hashes": body["ordered_command_body_hashes"],
            "receipt_archive_root": body["receipt_archive_root"],
            "outbox": state["outbox"],
        },
    )
    certificate = payload["certificate"]
    certificate["height"] = first.record.height + 1
    certificate["pre_state_root"] = first.record.post_state_root
    certificate["post_state_root"] = post_state_root
    certificate["body_commitment"] = body_commitment
    certificate_root = hash_global_v1(
        "global-economic-epoch-certificate-v1",
        certificate,
    )
    commit_id = (
        first.record.commit_id
        if reuse_commit_id
        else hash_global_v1(
            "durable-journal-test-only-synthetic-commit-v1",
            {"source": first.record.publication_id, "certificate": certificate_root},
        )
    )
    published = payload["published_epoch"]
    published["commit_id"] = commit_id
    published["certificate_root"] = certificate_root
    published["pre_state_root"] = first.record.post_state_root
    published["post_state_root"] = post_state_root
    published["body_commitment"] = body_commitment
    payload["schema"] = DURABLE_ECONOMIC_EPOCH_SCHEMA_V1
    payload_bytes = canonical_global_bytes_v1(payload)
    second_record = DurableEconomicEpochRecordV1.build(
        sequence=first.record.sequence + 1,
        activation_id=first.record.activation_id,
        source_publication_id=first.record.publication_id,
        chain_id=first.record.chain_id,
        deployment_root=first.record.deployment_root,
        profile_root=first.record.profile_root,
        writer_epoch=first.record.writer_epoch,
        height=first.record.height + 1,
        pre_state_root=first.record.post_state_root,
        post_state_root=post_state_root,
        commit_id=commit_id,
        certificate_root=certificate_root,
        body_commitment=body_commitment,
        effect_plan_root=first.record.effect_plan_root,
        receipt_root=first.record.receipt_root,
        release_observation_root=first.record.release_observation_root,
        payload_byte_count=len(payload_bytes),
        payload_root=_payload_root_v1(payload_bytes),
        receipt_byte_count=first.record.receipt_byte_count,
    )
    second = DurableEconomicEpochBundleV1(
        second_record,
        payload_bytes,
        first.receipt_bytes,
    )
    return activation, first, second


def _fully_rehashed_epoch_v1(
    epoch: DurableEconomicEpochBundleV1,
    mutate: Callable[[dict[str, object]], None],
    *,
    declared_journal_bytes: int | None = None,
) -> bytes:
    """Apply a semantic mutant and rebuild every dependent public commitment."""

    payload = json.loads(epoch.payload)
    assert type(payload) is dict
    mutate(payload)
    body = payload["body_and_state"]
    effect_plan = payload["effect_plan"]
    certificate = payload["certificate"]
    published = payload["published_epoch"]
    assert type(body) is dict
    assert type(effect_plan) is dict
    assert type(certificate) is dict
    assert type(published) is dict
    state = body["post_state"]
    assert type(state) is dict

    post_state_root = hash_global_v1("global-economic-state-root-v1", state)
    effect_plan_root = hash_global_v1(
        "global-economic-effect-plan-v1",
        effect_plan,
    )
    body_commitment = hash_global_v1(
        "global-economic-epoch-body-v1",
        {
            "pre_state_root": body["pre_state_root"],
            "post_state_root": post_state_root,
            "ordered_command_body_hashes": body["ordered_command_body_hashes"],
            "receipt_archive_root": body["receipt_archive_root"],
            "outbox": state["outbox"],
        },
    )
    certificate["post_state_root"] = post_state_root
    certificate["effect_plan_root"] = effect_plan_root
    certificate["body_commitment"] = body_commitment
    journal = dict(certificate)
    for field in ("receipt_root", "receipt_kind", "journal_bytes", "cycle_budget"):
        del journal[field]
    actual_journal_bytes = len(canonical_global_bytes_v1(journal))
    certificate["journal_bytes"] = (
        actual_journal_bytes
        if declared_journal_bytes is None
        else declared_journal_bytes
    )
    certificate_root = hash_global_v1(
        "global-economic-epoch-certificate-v1",
        certificate,
    )
    published["certificate_root"] = certificate_root
    published["post_state_root"] = post_state_root
    published["effect_plan_root"] = effect_plan_root
    published["body_commitment"] = body_commitment

    payload_bytes = canonical_global_bytes_v1(payload)
    record_body = epoch.record.to_canonical()
    for field in ("schema", "global_settlement_abi", "publication_id"):
        del record_body[field]
    record_body.update(
        {
            "post_state_root": post_state_root,
            "certificate_root": certificate_root,
            "effect_plan_root": effect_plan_root,
            "body_commitment": body_commitment,
            "payload_byte_count": len(payload_bytes),
            "payload_root": _payload_root_v1(payload_bytes),
        }
    )
    record = DurableEconomicEpochRecordV1.build(**record_body)
    record_bytes = canonical_global_bytes_v1(record)
    return b"".join(
        (
            _BUNDLE_MAGIC_V1,
            len(record_bytes).to_bytes(4, "big"),
            record_bytes,
            len(payload_bytes).to_bytes(8, "big"),
            payload_bytes,
            len(epoch.receipt_bytes).to_bytes(8, "big"),
            epoch.receipt_bytes,
        )
    )


def _typed_two_command_epoch_v1() -> DurableEconomicEpochBundleV1:
    candidate = _epoch_admission_fixture(2)
    body = EconomicEpochBodyAndStateV1(
        pre_state_root=candidate.pre_state.state_root,
        post_state=candidate.post_state,
        ordered_command_body_hashes=candidate.ordered_command_body_hashes,
        receipt_archive_root=hash_global_v1(
            "durable-two-command-receipt-archive-v1",
            {"count": 2},
        ),
        data_availability_root=candidate.certificate.data_availability_root,
        finality_root=candidate.certificate.finality_root,
    )
    certificate = replace(
        candidate.certificate,
        body_commitment=body.body_commitment,
        journal_bytes=1,
    )
    certificate = replace(
        certificate,
        journal_bytes=len(certificate.canonical_journal_bytes),
    )
    candidate = replace(
        candidate,
        certificate=certificate,
        expected_body_commitment=body.body_commitment,
    )
    publisher = _commit_port(
        candidate.profile,
        candidate.pre_state,
        _RecordingReceiptVerifier(),
    )
    verified = publisher.verify_economic_epoch(candidate)
    outcome = publisher.commit_verified_economic_epoch(
        expected_head=candidate.pre_state.state_root,
        expected_profile=candidate.profile.profile_id,
        verified_epoch=verified,
        body_and_state=body,
    )
    assert outcome.status is CommitOutcomeStatusV1.COMMITTED
    assert outcome.record is not None
    activation = prepare_durable_economic_initial_state_bundle_v1(
        _initial_state_admission(candidate.profile, candidate.pre_state),
        source_head=None,
    )
    return prepare_durable_economic_epoch_bundle_v1(
        DurableEconomicEpochMaterialV1(
            source_head=DurableEconomicPublicationHeadV1.from_activation(
                activation.head
            ),
            profile=candidate.profile,
            certificate=verified.certificate,
            effect_plan=verified.effect_plan,
            body_and_state=body,
            published_epoch=outcome.record,
            receipt_bytes=candidate.receipt_bytes,
        )
    )


def test_given_complete_epoch_when_encoded_then_roundtrip_preserves_every_body() -> None:
    # Arrange: Alice has one publisher-admitted epoch and its exact receipt bytes.
    _, source_head, epoch = _fixture_v1()

    # Act: an independent decoder snapshots the canonical byte bundle.
    decoded = decode_durable_economic_epoch_bundle_v1(epoch.canonical_bytes)

    # Assert: the bundle and source lineage survive byte-for-byte.
    assert decoded == epoch
    assert decoded.canonical_bytes == epoch.canonical_bytes
    assert decoded.record.source_publication_id == source_head.publication_id
    assert decoded.head.state_root == epoch.record.post_state_root


def test_distinct_occurrences_may_repeat_the_same_command_body_hash() -> None:
    # Arrange: the typed two-command verifier and publisher admit repeated bodies.
    epoch = _typed_two_command_epoch_v1()

    # Act: decode the resulting complete durability bundle.
    decoded = decode_durable_economic_epoch_bundle_v1(epoch.canonical_bytes)
    sections = _decode_payload_sections_v1(decoded.payload)

    # Assert: command order and canonically sorted effect consumption both survive.
    command_hashes = sections.body["ordered_command_body_hashes"]
    occurrences = sections.certificate["ordered_occurrence_ids"]
    assert command_hashes == [command_hashes[0], command_hashes[0]]
    assert sections.effect_plan["occurrence_consumptions"] == sorted(occurrences)


def test_fully_rehashed_effect_consuming_foreign_occurrence_is_rejected() -> None:
    # Arrange: Mallory replaces only the consumed occurrence and rehashes every layer.
    _, _, epoch = _fixture_v1()

    def replace_consumption(payload: dict[str, object]) -> None:
        effect_plan = payload["effect_plan"]
        assert type(effect_plan) is dict
        consumptions = effect_plan["occurrence_consumptions"]
        assert type(consumptions) is list
        consumptions[0] = hash_global_v1("foreign-occurrence-v1", {"index": 1})

    tampered = _fully_rehashed_epoch_v1(epoch, replace_consumption)

    # Act and assert: effect consumption must equal certificate occurrence order.
    with pytest.raises(ValueError, match="occurrence consumption mismatch"):
        decode_durable_economic_epoch_bundle_v1(tampered)


@pytest.mark.parametrize("section_name", ("certificate", "effect_plan", "post_state"))
def test_fully_rehashed_foreign_inner_schema_is_rejected(section_name: str) -> None:
    # Arrange: Mallory substitutes one inner ABI marker and rehashes every layer.
    _, _, epoch = _fixture_v1()

    def replace_schema(payload: dict[str, object]) -> None:
        if section_name == "post_state":
            body = payload["body_and_state"]
            assert type(body) is dict
            section = body[section_name]
        else:
            section = payload[section_name]
        assert type(section) is dict
        section["schema"] = "zenodex/global-settlement-abi/v2"

    tampered = _fully_rehashed_epoch_v1(epoch, replace_schema)

    # Act and assert: a content-derived envelope cannot substitute the ABI family.
    with pytest.raises(ValueError, match="schema mismatch"):
        decode_durable_economic_epoch_bundle_v1(tampered)


def test_journal_byte_declaration_requires_exact_canonical_length() -> None:
    # Arrange: Mallory supplies a bounded but verifier-impossible byte declaration.
    _, _, epoch = _fixture_v1()

    def preserve_certificate(_payload: dict[str, object]) -> None:
        return

    declared = json.loads(epoch.payload)["certificate"]["journal_bytes"]
    mismatched = _fully_rehashed_epoch_v1(
        epoch,
        preserve_certificate,
        declared_journal_bytes=declared + 1,
    )
    excessive = _fully_rehashed_epoch_v1(
        epoch,
        preserve_certificate,
        declared_journal_bytes=MAX_JOURNAL_BYTES_V1 + 1,
    )

    # Act and assert: exact typed fixture passes; bounded mismatch and ceiling fail.
    assert decode_durable_economic_epoch_bundle_v1(epoch.canonical_bytes) == epoch
    with pytest.raises(ValueError, match="journal byte declaration mismatch"):
        decode_durable_economic_epoch_bundle_v1(mismatched)
    with pytest.raises(ValueError, match="proof resources exceed the ABI ceiling"):
        decode_durable_economic_epoch_bundle_v1(excessive)


def test_cycle_budget_ceiling_accepts_exact_limit_and_rejects_one_over() -> None:
    # Arrange: rebuild otherwise identical epochs at both cycle-budget neighbors.
    _, _, epoch = _fixture_v1()

    def set_cycle_budget(value: int) -> Callable[[dict[str, object]], None]:
        def mutate(payload: dict[str, object]) -> None:
            certificate = payload["certificate"]
            assert type(certificate) is dict
            certificate["cycle_budget"] = value

        return mutate

    exact = _fully_rehashed_epoch_v1(epoch, set_cycle_budget(MAX_CYCLE_BUDGET_V1))
    excessive = _fully_rehashed_epoch_v1(
        epoch,
        set_cycle_budget(MAX_CYCLE_BUDGET_V1 + 1),
    )

    # Act and assert: exact ABI maxima survive; one unit above fails closed.
    assert decode_durable_economic_epoch_bundle_v1(exact).canonical_bytes == exact
    with pytest.raises(ValueError, match="proof resources exceed the ABI ceiling"):
        decode_durable_economic_epoch_bundle_v1(excessive)


@pytest.mark.parametrize(
    "removed_field",
    (
        "balances",
        "supplies",
        "custody",
        "liabilities",
        "reserves",
        "replay_state",
        "terminal_obligations",
        "history_root",
        "outbox",
    ),
)
def test_given_valid_epoch_when_economic_state_field_is_omitted_then_rejects(
    removed_field: str,
) -> None:
    # Arrange: Mallory removes one value-bearing field and rehashes the envelope.
    _, _, epoch = _fixture_v1()
    payload = json.loads(epoch.payload)
    del payload["body_and_state"]["post_state"][removed_field]
    tampered_payload = canonical_global_bytes_v1(payload)
    record_body = epoch.record.to_canonical()
    for field in ("schema", "global_settlement_abi", "publication_id"):
        del record_body[field]
    record_body["payload_byte_count"] = len(tampered_payload)
    record_body["payload_root"] = _payload_root_v1(tampered_payload)
    tampered_record = DurableEconomicEpochRecordV1.build(**record_body)

    # Act and assert: state closure survives a fully rehashed outer envelope.
    with pytest.raises((TypeError, ValueError), match="state|payload|body|field"):
        type(epoch)(tampered_record, tampered_payload, epoch.receipt_bytes)


def test_given_activation_when_epoch_commits_then_bundle_and_head_are_atomic(
    tmp_path: Path,
) -> None:
    # Arrange: the durable journal begins from one exact activation bundle.
    activation, _, epoch = _fixture_v1()
    path = tmp_path / "economic-epochs.sqlite"
    journal, write_capability = _create_writer_v1(path, activation)
    token = journal.acquire_cas_head_token()

    # Act: publish one adjacent ordinary epoch and reopen the database.
    outcome = _commit_v1(journal, write_capability, epoch, token)
    journal.close()
    reopened = GlobalEconomicEpochJournalV1.open(path)

    # Assert: the complete body and head pointer moved in one SQLite transaction.
    assert outcome.status is DurableEconomicEpochCommitStatusV1.COMMITTED
    assert reopened.head == epoch.head
    assert _stored_epoch_rows_v1(path) == (
        1,
        epoch.record.publication_id,
        epoch.canonical_bytes,
    )
    reopened.close()


def test_journal_resolves_owned_activation_and_exact_historical_heads(
    tmp_path: Path,
) -> None:
    # Arrange: one activation and one ordinary epoch are durably published.
    activation, source_head, epoch = _fixture_v1()
    journal, write_capability = _create_writer_v1(
        tmp_path / "head-resolution.sqlite",
        activation,
    )
    _commit_v1(
        journal,
        write_capability,
        epoch,
        journal.acquire_cas_head_token(),
    )

    # Act: resolve the immutable activation and both content-addressed heads.
    owned_activation = journal.activation_bundle
    resolved_source = journal.publication_head(source_head.publication_id)
    resolved_epoch = journal.publication_head(epoch.head.publication_id)
    absent = journal.publication_head("0x" + "ff" * 32)

    # Assert: callers receive exact owned snapshots and unknown identities stay absent.
    assert owned_activation == activation
    assert owned_activation is not activation
    assert resolved_source == source_head
    assert resolved_epoch == epoch.head
    assert absent is None
    journal.close()


def test_given_lost_ack_when_exact_epoch_retries_then_no_duplicate_is_created(
    tmp_path: Path,
) -> None:
    # Arrange: a caller retains its source token after the epoch actually committed.
    activation, _, epoch = _fixture_v1()
    path = tmp_path / "lost-ack.sqlite"
    journal, write_capability = _create_writer_v1(path, activation)
    token = journal.acquire_cas_head_token()
    first = _commit_v1(journal, write_capability, epoch, token)

    # Act: retry the byte-identical epoch through the original token.
    retry = _commit_v1(journal, write_capability, epoch, token)

    # Assert: retry is typed, exact, and leaves one history row.
    assert first.status is DurableEconomicEpochCommitStatusV1.COMMITTED
    assert retry.status is DurableEconomicEpochCommitStatusV1.ALREADY_COMMITTED
    assert retry.committed_epoch == epoch.head
    assert _stored_epoch_rows_v1(path)[:2] == (1, epoch.record.publication_id)
    journal.close()


def test_given_two_epoch_history_when_first_retries_then_tip_remains_second(
    tmp_path: Path,
) -> None:
    # Arrange: two adjacent epochs commit after the first caller loses its ACK.
    activation, first_epoch, second_epoch = _two_epoch_chain_v1()
    path = tmp_path / "historical-retry.sqlite"
    journal, write_capability = _create_writer_v1(path, activation)
    first_token = journal.acquire_cas_head_token()
    _commit_v1(journal, write_capability, first_epoch, first_token)
    _commit_v1(
        journal,
        write_capability,
        second_epoch,
        journal.acquire_cas_head_token(),
    )

    # Act: retry the historical byte-identical first epoch through its source token.
    retry = _commit_v1(journal, write_capability, first_epoch, first_token)

    # Assert: original identity is returned while the durable head remains epoch two.
    assert retry.status is DurableEconomicEpochCommitStatusV1.ALREADY_COMMITTED
    assert retry.committed_epoch == first_epoch.head
    assert retry.head == second_epoch.head
    journal.close()


def test_given_adjacent_epoch_reusing_commit_id_then_replay_is_rejected(
    tmp_path: Path,
) -> None:
    # Arrange: a fully rehashed successor reuses the prior verifier commit identity.
    activation, first_epoch, duplicate_commit_epoch = _two_epoch_chain_v1(
        reuse_commit_id=True
    )
    path = tmp_path / "duplicate-commit-id.sqlite"
    journal, write_capability = _create_writer_v1(path, activation)
    _commit_v1(
        journal,
        write_capability,
        first_epoch,
        journal.acquire_cas_head_token(),
    )

    # Act and assert: durable replay identity is unique across the full history.
    with pytest.raises(ValueError, match="commit identity"):
        _commit_v1(
            journal,
            write_capability,
            duplicate_commit_epoch,
            journal.acquire_cas_head_token(),
        )
    assert journal.head == first_epoch.head
    journal.close()


def test_commit_resnapshots_epoch_after_hostile_frozen_object_mutation(
    tmp_path: Path,
) -> None:
    # Arrange: bypass frozen-dataclass guards after the bundle validated once.
    activation, _, epoch = _fixture_v1()
    path = tmp_path / "hostile-object.sqlite"
    journal, write_capability = _create_writer_v1(path, activation)
    token = journal.acquire_cas_head_token()
    object.__setattr__(epoch.record, "commit_id", "0x" + "cd" * 32)

    # Act and assert: commit re-decodes owned bytes and leaves activation unchanged.
    with pytest.raises(ValueError, match="publication id"):
        _commit_v1(journal, write_capability, epoch, token)
    assert journal.head.publication_id == activation.record.activation_id
    journal.close()


def test_given_two_valid_successors_when_one_wins_then_other_is_stale_no_effect(
    tmp_path: Path,
) -> None:
    # Arrange: two sequencers produce valid, distinct receipt-bound successors.
    activation, _, first = _fixture_v1(receipt_bytes=b"first-valid-receipt")
    alternate_activation, _, second = _fixture_v1(receipt_bytes=b"second-valid-receipt")
    assert alternate_activation == activation
    assert second.record.publication_id != first.record.publication_id
    path = tmp_path / "competing.sqlite"
    journal, write_capability = _create_writer_v1(path, activation)
    first_token = journal.acquire_cas_head_token()
    second_token = journal.acquire_cas_head_token()

    # Act: first commits; second submits from its now-stale source snapshot.
    winner = _commit_v1(journal, write_capability, first, first_token)
    loser = _commit_v1(journal, write_capability, second, second_token)

    # Assert: history contains only the winner and the loser is an exact no-op.
    assert winner.status is DurableEconomicEpochCommitStatusV1.COMMITTED
    assert loser.status is DurableEconomicEpochCommitStatusV1.STALE_HEAD
    assert loser.head == first.head
    assert _stored_epoch_rows_v1(path) == (
        1,
        first.record.publication_id,
        first.canonical_bytes,
    )
    journal.close()


def test_given_two_open_instances_when_one_commits_then_other_observes_stale(
    tmp_path: Path,
) -> None:
    # Arrange: independent shells acquire tokens against the same durable source.
    activation, _, first_epoch = _fixture_v1(receipt_bytes=b"cross-instance-first")
    _, _, second_epoch = _fixture_v1(receipt_bytes=b"cross-instance-second")
    path = tmp_path / "cross-instance.sqlite"
    first, first_write_capability = _create_writer_v1(path, activation)
    second, second_write_capability = _open_writer_v1(path)
    first_token = first.acquire_cas_head_token()
    second_token = second.acquire_cas_head_token()

    # Act: SQLite serializes the winner before the second shell validates its CAS.
    winner = _commit_v1(
        first,
        first_write_capability,
        first_epoch,
        first_token,
    )
    loser = _commit_v1(
        second,
        second_write_capability,
        second_epoch,
        second_token,
    )

    # Assert: both instances converge on one complete publication.
    assert winner.status is DurableEconomicEpochCommitStatusV1.COMMITTED
    assert loser.status is DurableEconomicEpochCommitStatusV1.STALE_HEAD
    assert loser.head == first_epoch.head
    first.close()
    second.close()


@pytest.mark.parametrize(
    ("fault", "expected_post"),
    (
        (_DurableEconomicEpochCommitFaultV1.AFTER_BEGIN, False),
        (_DurableEconomicEpochCommitFaultV1.AFTER_INSERT, False),
        (_DurableEconomicEpochCommitFaultV1.AFTER_HEAD_UPDATE_BEFORE_COMMIT, False),
        (_DurableEconomicEpochCommitFaultV1.AFTER_COMMIT_BEFORE_ACK, True),
    ),
)
def test_given_crash_boundary_when_reopened_then_store_is_exact_pre_or_post(
    tmp_path: Path,
    fault: _DurableEconomicEpochCommitFaultV1,
    expected_post: bool,
) -> None:
    # Arrange: one deterministic failure point surrounds the commit boundary.
    activation, source_head, epoch = _fixture_v1()
    path = tmp_path / f"fault-{fault.value}.sqlite"
    journal, write_capability = _create_writer_v1(path, activation)
    token = journal.acquire_cas_head_token()

    # Act: inject failure, close, and recover from the file.
    with pytest.raises(_SimulatedDurableEconomicEpochCrashV1, match=fault.value):
        journal._commit_epoch_with_fault_for_test_v1(
            epoch,
            token,
            fault,
            write_capability,
        )
    journal.close()
    reopened = GlobalEconomicEpochJournalV1.open(path)

    # Assert: recovery exposes a complete PRE or complete POST state only.
    assert reopened.head == (epoch.head if expected_post else source_head)
    if expected_post:
        reopened_writer, reopened_write_capability = _open_writer_v1(path)
        reopened.close()
        retry = _commit_v1(
            reopened_writer,
            reopened_write_capability,
            epoch,
            reopened_writer.acquire_cas_head_token(),
        )
        assert retry.status is DurableEconomicEpochCommitStatusV1.ALREADY_COMMITTED
        reopened_writer.close()
    else:
        reopened.close()


@pytest.mark.parametrize(
    ("fault", "expected_post"),
    (
        (_DurableEconomicEpochCommitFaultV1.AFTER_BEGIN, False),
        (_DurableEconomicEpochCommitFaultV1.AFTER_INSERT, False),
        (_DurableEconomicEpochCommitFaultV1.AFTER_HEAD_UPDATE_BEFORE_COMMIT, False),
        (_DurableEconomicEpochCommitFaultV1.AFTER_COMMIT_BEFORE_ACK, True),
    ),
)
def test_given_abrupt_exit_when_reopened_then_sqlite_recovers_pre_or_post(
    tmp_path: Path,
    fault: _DurableEconomicEpochCommitFaultV1,
    expected_post: bool,
) -> None:
    # Arrange: persist the base activation before handing work to a child process.
    activation, source_head, epoch = _fixture_v1()
    path = tmp_path / f"hard-exit-{fault.value}.sqlite"
    journal, _ = _create_writer_v1(path, activation)
    journal.close()
    child_program = """
import os
import sys

import src.integration.global_economic_epoch_journal_v1 as journal_module
from tests.integration.test_global_economic_epoch_journal_v1 import _fixture_v1

path = sys.argv[1]
fault = journal_module._DurableEconomicEpochCommitFaultV1(sys.argv[2])
_, _, epoch = _fixture_v1()
journal, write_capability = journal_module._open_epoch_journal_for_verified_publisher_v1(path)
token = journal.acquire_cas_head_token()
journal_module._SimulatedDurableEconomicEpochCrashV1 = lambda _message: os._exit(97)
journal._commit_epoch_with_fault_for_test_v1(epoch, token, fault, write_capability)
raise RuntimeError("hard-exit mutation unexpectedly returned")
"""

    # Act: terminate without exception unwinding or explicit rollback cleanup.
    child = subprocess.run(
        [sys.executable, "-c", child_program, str(path), fault.value],
        cwd=Path(__file__).resolve().parents[2],
        check=False,
        timeout=20,
    )

    # Assert: SQLite recovery matches the deterministic PRE/POST oracle.
    assert child.returncode == 97
    assert epoch.record.activation_id == source_head.activation_id
    with GlobalEconomicEpochJournalV1.open(path) as reopened:
        assert reopened.head == (epoch.head if expected_post else source_head)


def test_given_foreign_cas_token_when_used_then_commit_rejects_without_effect(
    tmp_path: Path,
) -> None:
    # Arrange: Mallory obtains a valid token from a different journal instance.
    activation, source_head, epoch = _fixture_v1()
    first, first_write_capability = _create_writer_v1(
        tmp_path / "first.sqlite",
        activation,
    )
    second, _ = _create_writer_v1(tmp_path / "second.sqlite", activation)
    foreign = second.acquire_cas_head_token()

    # Act and assert: token ownership rejects before any economic row is inserted.
    with pytest.raises(ValueError, match="foreign or forged"):
        _commit_v1(first, first_write_capability, epoch, foreign)
    assert first.head == source_head
    first.close()
    second.close()


def test_direct_journal_has_no_unfenced_epoch_commit_api(tmp_path: Path) -> None:
    # Arrange: Mallory can open the structural journal and form a valid bundle.
    activation, source_head, epoch = _fixture_v1()
    journal = GlobalEconomicEpochJournalV1.create(
        tmp_path / "reader-only.sqlite",
        activation,
    )
    token = journal.acquire_cas_head_token()

    # Act and assert: no public commit exists and a fabricated capability rejects.
    assert "commit_epoch" not in GlobalEconomicEpochJournalV1.__dict__
    with pytest.raises(TypeError, match="exact write capability"):
        journal._commit_epoch_from_verified_publisher_v1(
            epoch,
            token,
            object(),  # type: ignore[arg-type]
        )
    with pytest.raises(TypeError, match="publisher-minted"):
        DurableEconomicEpochWriteCapabilityV1(object(), journal)
    assert journal.head == source_head
    journal.close()


def test_private_structural_writer_remains_a_same_process_release_blocker(
    tmp_path: Path,
) -> None:
    # Arrange: same-interpreter code opens the unmounted structural journal.
    activation, _, epoch = _fixture_v1()
    journal = GlobalEconomicEpochJournalV1.create(
        tmp_path / "private-writer-blocker.sqlite",
        activation,
    )

    # Act: Python permits direct invocation of the underscore-prefixed writer.
    outcome = journal._commit_epoch_v1(
        epoch,
        journal.acquire_cas_head_token(),
        fault=None,
    )

    # Assert: preserve the counterexample until an OS-isolated writer replaces it.
    assert outcome.status is DurableEconomicEpochCommitStatusV1.COMMITTED
    assert journal.head == epoch.head
    journal.close()


def test_write_capability_is_bound_to_one_journal_instance(tmp_path: Path) -> None:
    # Arrange: two journals hold identical activations and distinct capabilities.
    activation, source_head, epoch = _fixture_v1()
    first, _ = _create_writer_v1(tmp_path / "cap-first.sqlite", activation)
    second, second_capability = _create_writer_v1(
        tmp_path / "cap-second.sqlite",
        activation,
    )

    # Act and assert: a capability cannot authorize a different journal instance.
    with pytest.raises(ValueError, match="foreign or forged"):
        _commit_v1(
            first,
            second_capability,
            epoch,
            first.acquire_cas_head_token(),
        )
    assert first.head == second.head == source_head
    first.close()
    second.close()


def test_given_extra_schema_object_when_opened_then_exact_schema_gate_rejects(
    tmp_path: Path,
) -> None:
    # Arrange: a local attacker adds an unowned trigger-capable schema surface.
    activation, _, _ = _fixture_v1()
    path = tmp_path / "schema-mutant.sqlite"
    journal, _ = _create_writer_v1(path, activation)
    journal.close()
    with sqlite3.connect(path) as connection:
        connection.execute("CREATE TABLE shadow_writer (value TEXT) STRICT")

    # Act and assert: reopening rejects the expanded schema before reading a head.
    with pytest.raises(RuntimeError, match="exact schema"):
        GlobalEconomicEpochJournalV1.open(path)


def test_given_zero_remaining_row_capacity_when_committing_then_typed_noop(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange: set the bounded journal at its exact zero-remaining-row boundary.
    activation, source_head, epoch = _fixture_v1()
    path = tmp_path / "capacity.sqlite"
    journal, write_capability = _create_writer_v1(path, activation)
    token = journal.acquire_cas_head_token()
    monkeypatch.setattr(journal_module, "_MAX_EPOCH_HISTORY_V1", 0)

    # Act: submit an otherwise valid adjacent epoch.
    outcome = _commit_v1(journal, write_capability, epoch, token)

    # Assert: capacity rejection is typed and no state, history, or head changes.
    assert outcome.status is DurableEconomicEpochCommitStatusV1.CAPACITY_EXCEEDED
    assert outcome.head == source_head
    assert journal.head == source_head
    journal.close()


def test_open_accepts_history_at_exact_byte_capacity(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange: one committed epoch consumes exactly the configured byte capacity.
    activation, _, epoch = _fixture_v1()
    path = tmp_path / "exact-byte-capacity.sqlite"
    journal, write_capability = _create_writer_v1(path, activation)
    _commit_v1(
        journal,
        write_capability,
        epoch,
        journal.acquire_cas_head_token(),
    )
    journal.close()
    monkeypatch.setattr(
        journal_module,
        "_MAX_EPOCH_STORE_BYTES_V1",
        len(epoch.canonical_bytes),
    )

    # Act: recovery validates all stored bundle bytes at the exact limit.
    reopened = GlobalEconomicEpochJournalV1.open(path)

    # Assert: equality is admitted and the complete head is retained.
    assert reopened.head == epoch.head
    reopened.close()


def test_open_rejects_history_one_byte_over_capacity(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange: the stored history exceeds the configured byte ceiling by one byte.
    activation, _, epoch = _fixture_v1()
    path = tmp_path / "one-over-byte-capacity.sqlite"
    journal, write_capability = _create_writer_v1(path, activation)
    _commit_v1(
        journal,
        write_capability,
        epoch,
        journal.acquire_cas_head_token(),
    )
    journal.close()
    monkeypatch.setattr(
        journal_module,
        "_MAX_EPOCH_STORE_BYTES_V1",
        len(epoch.canonical_bytes) - 1,
    )

    # Act and assert: open fails closed before exposing a durable head.
    with pytest.raises(ValueError, match="history exceeds byte capacity"):
        GlobalEconomicEpochJournalV1.open(path)
