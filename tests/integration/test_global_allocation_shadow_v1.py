"""Isolated committed-journal observations; all receipt verifiers are test mocks."""

from __future__ import annotations

import hashlib
import json
import sqlite3
from dataclasses import fields, replace
from pathlib import Path

import pytest

from src.core import global_accounting_allocation_certificate_v1 as cert
from src.core import global_settlement_types_v1 as types
from src.core.global_economic_durable_activation_v1 import (
    prepare_durable_economic_initial_state_bundle_v1,
)
from src.core.global_settlement_types_v1 import canonical_global_bytes_v1
from src.integration import global_allocation_shadow_v1 as shadow
from src.integration.global_economic_epoch_journal_v1 import DurableEconomicEpochCommitStatusV1
from tests.core.test_asset_transfer_receipt_admission_v1 import _admission_fixture
from tests.core.test_global_accounting_allocation_certificate_v1_golden import _witnessed
from tests.core.test_global_settlement_abi_v1 import (
    EconomicInitialStateKindV1,
    EconomicInitialStateSourceManifestV1,
    _initial_state_admission,
    _profile,
)
from tests.integration.test_global_economic_epoch_journal_v1 import (
    _commit_v1,
    _create_writer_v1,
    _fixture_v1,
)


def _committed_source(tmp_path: Path):
    activation, _, epoch = _fixture_v1()
    path = tmp_path / "economic.sqlite"
    writer, capability = _create_writer_v1(path, activation)
    try:
        outcome = _commit_v1(writer, capability, epoch, writer.acquire_cas_head_token())
        assert outcome.status is DurableEconomicEpochCommitStatusV1.COMMITTED
    finally:
        writer.close()
    return shadow.ReadOnlyAllocationSourceV1(path), activation, epoch


def test_module_and_coordinator_roots_expose_unresolved_allocation_bridge() -> None:
    """Retain the W04 counterexample; this passing discovery test closes no gate."""
    accepted, _witness, _lane_root, _prior = _admission_fixture()
    _activation, _head, epoch = _fixture_v1()
    module_root = accepted.module_journal.post_lane_root
    coordinator_root = accepted.private_port.post_state.state_root
    assert module_root == accepted.post_state.state_root
    epoch_state = json.loads(epoch.payload)["body_and_state"]["post_state"]
    assert coordinator_root == epoch_state["lane_roots"][0]["state_root"]
    assert module_root != coordinator_root


def test_committed_single_transfer_observation_uses_verified_global_allocation_relation(tmp_path: Path) -> None:
    """Given an isolated ordinary commit, bind its two stored states without rewriting roots."""
    from src.core.asset_transfer_global_allocation_v1 import (
        AssetTransferGlobalAllocationCandidateV1,
    )
    from src.core.asset_transfer_receipt_admission_v1 import (
        verify_asset_transfer_global_fragment_receipt_v1,
    )
    from src.integration.global_economic_durable_epoch_v1 import (
        DurableEconomicEpochMaterialV1,
        DurableEconomicPublicationHeadV1,
        prepare_durable_economic_epoch_bundle_v1,
    )
    from tests.core.test_asset_transfer_global_allocation_v1 import _global_allocation_fixture
    from tests.core.test_global_settlement_abi_v1 import _publisher_verified_epoch

    profile, route, occurrence, accepted, module_witness, pre, post = _global_allocation_fixture()
    activation = prepare_durable_economic_initial_state_bundle_v1(
        _initial_state_admission(profile, pre), source_head=None,
    )
    receipt_bytes = b"global-allocation-observation-mock-epoch-receipt"
    publisher, verified, body, _, _, _ = _publisher_verified_epoch(
        profile, route, pre, post, receipt_bytes=receipt_bytes,
    )
    committed = publisher.commit_verified_economic_epoch(
        expected_head=pre.state_root, expected_profile=profile.profile_id,
        verified_epoch=verified, body_and_state=body,
    )
    assert committed.record is not None
    epoch = prepare_durable_economic_epoch_bundle_v1(DurableEconomicEpochMaterialV1(
        source_head=DurableEconomicPublicationHeadV1.from_activation(activation.head),
        profile=profile, certificate=verified.certificate, effect_plan=verified.effect_plan,
        body_and_state=body, published_epoch=committed.record, receipt_bytes=receipt_bytes,
    ))
    path = tmp_path / "single-transfer.sqlite"
    writer, capability = _create_writer_v1(path, activation)
    try:
        assert _commit_v1(writer, capability, epoch, writer.acquire_cas_head_token()).status is DurableEconomicEpochCommitStatusV1.COMMITTED
    finally:
        writer.close()
    source = shadow.ReadOnlyAllocationSourceV1(path)
    before_files, before_rows = _file_family(tmp_path), _logical_rows(path)
    snapshot = source.read_snapshot()
    assert snapshot.predecessor_state == pre and snapshot.state == post
    witness = verify_asset_transfer_global_fragment_receipt_v1(
        module_witness, AssetTransferGlobalAllocationCandidateV1(
            accepted, occurrence, snapshot.predecessor_state, snapshot.state,
        ),
    )
    assert isinstance(witness, cert.VerifiedLaneAllocationFragmentV1)
    assert accepted.module_journal.post_lane_root != witness.fragment.lane_state_root
    observer = shadow.GlobalAllocationShadowObserverV1(capacity=3)
    slots = (witness, *(None for _ in types.ALL_LANE_IDS_V1[1:]))
    projected = observer.observe(source, lane_witnesses=slots)
    assert projected.status is shadow.ShadowObservationStatusV1.PROJECTED
    assert observer.observe(source, lane_witnesses=slots, expected_allocation_root=projected.allocation_root).status is shadow.ShadowObservationStatusV1.AGREES
    assert observer.observe(source, lane_witnesses=slots, expected_allocation_root="0x" + "99" * 32).status is shadow.ShadowObservationStatusV1.DIFFERS
    assert observer.observe(source).status is shadow.ShadowObservationStatusV1.MISSING_WITNESS
    assert before_files == _file_family(tmp_path) and before_rows == _logical_rows(path)
    assert source.read_snapshot().state.profile_root == profile.profile_id


def _file_family(tmp_path: Path):
    return {
        path.name: hashlib.sha256(path.read_bytes()).hexdigest()
        for path in tmp_path.iterdir()
        if path.is_file()
    }


def _logical_rows(path: Path):
    with sqlite3.connect(f"{path.as_uri()}?mode=ro", uri=True) as connection:
        return tuple(
            tuple(connection.execute(f"SELECT * FROM {table} ORDER BY 1"))
            for table in ("metadata", "economic_epochs", "current_head")
        )


def _empty_activation_source(tmp_path: Path):
    """Closed empty test profile; disabled lanes are no product-completion evidence."""
    source_manifest = EconomicInitialStateSourceManifestV1(EconomicInitialStateKindV1.GENESIS, ())
    base, _ = _profile(source_manifest=source_manifest)
    disabled = {
        "status": types.ReleaseStatusV1.RETIRED,
        "accepts_new_objects": False,
        "evidence_statuses": (types.EvidenceStatusV1.DISABLED_PROVED_NO_WRITER,),
    }
    arguments = {
        field.name: getattr(base, field.name)
        for field in fields(base)
        if field.name != "profile_id"
    }
    arguments.update(
        lane_registry=types.LaneRegistryV1(
            tuple(replace(row, **disabled) for row in base.lane_registry.releases)
        ),
        lane_coordinator_registry=types.LaneCoordinatorRegistryV1(
            tuple(replace(row, **disabled) for row in base.lane_coordinator_registry.releases)
        ),
        route_registry=types.RouteRegistryV1(()),
    )
    profile = types.EconomicProfileSnapshotV1.build(**arguments)
    state = types.GlobalEconomicStateV1(
        chain_id="zeno-test-chain",
        deployment_root="0x" + "55" * 32,
        writer_epoch=profile.authority_epoch,
        height=0,
        profile_root=profile.profile_id,
        lane_roots=tuple(
            types.LaneStateRootV1(
                row.lane_id,
                row.release_id,
                False,
                cert.REGISTERED_EMPTY_LANE_ROOTS_V1.get(row.lane_id, "0x" + "66" * 32),
            )
            for row in profile.lane_registry.releases
        ),
    )
    # Reuse the existing mock certificate recipe, then bind the prepared candidate
    # to this empty profile before any admission, encoding or store creation.
    admission = _initial_state_admission(base, state, source_manifest=source_manifest)
    certificate = replace(
        admission.certificate, profile_root=profile.profile_id, state_root=state.state_root
    )
    certificate = replace(certificate, journal_bytes=len(certificate.canonical_journal_bytes))
    activation = prepare_durable_economic_initial_state_bundle_v1(
        replace(admission, profile=profile, state=state, certificate=certificate),
        source_head=None,
    )
    path = tmp_path / "empty-activation.sqlite"
    writer, _ = _create_writer_v1(path, activation)
    writer.close()
    return shadow.ReadOnlyAllocationSourceV1(path), activation


def test_given_committed_empty_activation_when_observed_then_agreement_and_difference_are_isolated(
    tmp_path: Path,
) -> None:
    source, activation = _empty_activation_source(tmp_path)
    before_files, before_rows = _file_family(tmp_path), _logical_rows(source.path)
    snapshot = source.read_snapshot()
    expected = cert.build_registered_empty_certificate_v1(snapshot.state).allocation_root
    observer = shadow.GlobalAllocationShadowObserverV1(capacity=2)

    agrees = observer.observe(source, expected_allocation_root=expected)
    differs = observer.observe(source, expected_allocation_root="0x" + "77" * 32)
    projected = observer.observe(source)

    assert agrees.status is shadow.ShadowObservationStatusV1.AGREES
    assert differs.status is shadow.ShadowObservationStatusV1.DIFFERS
    assert differs.allocation_root == agrees.allocation_root == expected
    assert projected.status is shadow.ShadowObservationStatusV1.PROJECTED
    assert observer.diagnostics == (differs, projected)
    assert snapshot.head.publication_id == activation.record.activation_id
    assert snapshot.predecessor_head is None and snapshot.predecessor_state is None
    assert agrees.publication_id == activation.record.activation_id
    assert agrees.provenance == shadow.SHADOW_SOURCE_PROVENANCE_V1
    assert agrees.authority == "NONE"
    assert source.read_snapshot().state.profile_root == snapshot.state.profile_root
    assert _logical_rows(source.path) == before_rows
    assert _file_family(tmp_path) == before_files
    assert not hasattr(source, "_connection") and not hasattr(source, "commit")


def test_given_committed_ordinary_epoch_when_projection_lacks_lane_coverage_then_gap_is_visible(
    tmp_path: Path,
) -> None:
    source, activation, epoch = _committed_source(tmp_path)
    before_files, before_rows = _file_family(tmp_path), _logical_rows(source.path)
    snapshot = source.read_snapshot()
    _, _, _, slots = _witnessed()
    observer = shadow.GlobalAllocationShadowObserverV1()
    missing = observer.observe(source)
    refused = observer.observe(source, lane_witnesses=slots)
    assert missing.status is shadow.ShadowObservationStatusV1.MISSING_WITNESS
    assert refused.status is shadow.ShadowObservationStatusV1.PROJECTION_REJECTED
    assert refused.code == "PROJECTION_MULTIPLE_ENABLED_LANES"
    assert snapshot.head == epoch.head
    assert snapshot.predecessor_head.publication_id == activation.record.activation_id
    assert snapshot.predecessor_state.state_root == epoch.record.pre_state_root
    assert _logical_rows(source.path) == before_rows
    assert _file_family(tmp_path) == before_files


def test_given_observation_failure_when_writer_commits_then_read_lock_has_been_released(
    tmp_path: Path, monkeypatch
) -> None:
    activation, _, epoch = _fixture_v1()
    path = tmp_path / "economic.sqlite"
    writer, capability = _create_writer_v1(path, activation)
    source = shadow.ReadOnlyAllocationSourceV1(path)
    observer = shadow.GlobalAllocationShadowObserverV1()
    before = _logical_rows(path)
    try:
        with monkeypatch.context() as scoped:
            scoped.setattr(shadow, "MAX_SHADOW_STATE_ROWS_V1", 0)
            outcome = observer.observe(source)
        assert outcome.status is shadow.ShadowObservationStatusV1.RESOURCE_LIMIT
        assert _logical_rows(path) == before
        committed = _commit_v1(writer, capability, epoch, writer.acquire_cas_head_token())
        assert committed.status is DurableEconomicEpochCommitStatusV1.COMMITTED
        assert source.read_snapshot().head == epoch.head
    finally:
        writer.close()


@pytest.mark.parametrize("corruption", ("head", "schema"))
def test_given_corrupt_history_or_unknown_schema_when_observed_then_visible_invalid_source_has_no_effect(
    tmp_path: Path, corruption: str
) -> None:
    source, _, _ = _committed_source(tmp_path)
    with sqlite3.connect(source.path) as connection:
        if corruption == "head":
            connection.execute("UPDATE current_head SET publication_id = ?", ("0x" + "99" * 32,))
        else:
            connection.execute("CREATE TABLE unknown_writer (value INTEGER)")
    before_files, before_rows = _file_family(tmp_path), _logical_rows(source.path)
    outcome = shadow.GlobalAllocationShadowObserverV1().observe(source)
    assert outcome.status is shadow.ShadowObservationStatusV1.SOURCE_INVALID
    assert outcome.state_root is None and outcome.allocation_root is None
    assert _logical_rows(source.path) == before_rows
    assert _file_family(tmp_path) == before_files


def test_given_missing_source_when_observed_then_gap_is_visible_and_no_database_is_created(
    tmp_path: Path,
) -> None:
    path = tmp_path / "missing.sqlite"
    diagnostic = shadow.GlobalAllocationShadowObserverV1().observe(
        shadow.ReadOnlyAllocationSourceV1(path)
    )
    assert diagnostic.status is shadow.ShadowObservationStatusV1.SOURCE_UNAVAILABLE
    assert diagnostic.provenance == "SOURCE_NOT_OBSERVED"
    assert not path.exists()


def test_read_only_connection_disallows_writes_attach_and_pragma_reconfiguration(
    tmp_path: Path, monkeypatch
) -> None:
    source, _, _ = _committed_source(tmp_path)
    original = shadow._read_committed_snapshot_v1
    attempts = []

    def inspect(journal):
        connection = journal._connection
        for sql in (
            "DELETE FROM economic_epochs",
            "PRAGMA query_only = OFF",
            "ATTACH DATABASE ':memory:' AS attacker",
            "CREATE TABLE observer_write (value INTEGER)",
        ):
            with pytest.raises(sqlite3.DatabaseError):
                connection.execute(sql)
            attempts.append(sql)
        return original(journal)

    before = _file_family(tmp_path)
    monkeypatch.setattr(shadow, "_read_committed_snapshot_v1", inspect)
    assert source.read_snapshot().head.sequence == 1
    assert len(attempts) == 4
    assert _file_family(tmp_path) == before


def test_exact_snapshot_decoder_rejects_unknown_omitted_and_noncanonical_rows(
    tmp_path: Path,
) -> None:
    source, _, _ = _committed_source(tmp_path)
    raw = json.loads(canonical_global_bytes_v1(source.read_snapshot().state))
    assert (
        shadow.decode_shadow_state_v1(raw).to_canonical()
        == source.read_snapshot().state.to_canonical()
    )
    for changed in (
        {**raw, "unknown": 1},
        {key: value for key, value in raw.items() if key != "outbox"},
    ):
        with pytest.raises(ValueError, match="field set"):
            shadow.decode_shadow_state_v1(changed)
    lane = {**raw["lane_roots"][0], "enabled": 1}
    with pytest.raises((TypeError, ValueError)):
        shadow.decode_shadow_state_v1({**raw, "lane_roots": [lane, *raw["lane_roots"][1:]]})
    with pytest.raises(shadow._ObservationLimitV1):
        shadow.decode_shadow_state_v1(
            {**raw, "outbox": [{}] * (shadow.types.MAX_GLOBAL_OUTBOX_ROWS_V1 + 1)}
        )


def test_snapshot_header_and_predecessor_binding_rejects_each_changed_coordinate(
    tmp_path: Path,
) -> None:
    source, _, _ = _committed_source(tmp_path)
    snapshot = source.read_snapshot()
    for field, value in (
        ("chain_id", "foreign"),
        ("deployment_root", "0x" + "77" * 32),
        ("profile_root", "0x" + "77" * 32),
        ("writer_epoch", snapshot.head.writer_epoch + 1),
        ("height", snapshot.head.height + 1),
        ("state_root", "0x" + "77" * 32),
    ):
        with pytest.raises(ValueError, match="binding mismatch"):
            shadow._bind_snapshot_state_v1(snapshot.state, replace(snapshot.head, **{field: value}))
    with pytest.raises(ValueError, match="binding mismatch"):
        shadow._bind_snapshot_state_v1(snapshot.predecessor_state, snapshot.head)


def test_diagnostic_ring_capacity_is_bounded() -> None:
    for capacity in (0, shadow.MAX_SHADOW_DIAGNOSTICS_V1 + 1, True):
        with pytest.raises(ValueError, match="capacity"):
            shadow.GlobalAllocationShadowObserverV1(capacity=capacity)


def test_history_budget_rejects_before_bundle_decode(tmp_path: Path, monkeypatch) -> None:
    source, _, _ = _committed_source(tmp_path)
    before = _file_family(tmp_path)

    def unexpected_decode(_journal):
        raise AssertionError("bundle decode must not run beyond the observation budget")

    monkeypatch.setattr(shadow, "MAX_SHADOW_HISTORY_EPOCHS_V1", 0)
    monkeypatch.setattr(
        shadow.GlobalEconomicEpochJournalV1, "_read_activation_v1", unexpected_decode
    )
    diagnostic = shadow.GlobalAllocationShadowObserverV1().observe(source)
    assert diagnostic.status is shadow.ShadowObservationStatusV1.RESOURCE_LIMIT
    assert diagnostic.provenance == "SOURCE_NOT_OBSERVED"
    assert _file_family(tmp_path) == before


def test_busy_source_and_projection_exception_leave_following_reads_available(
    tmp_path: Path, monkeypatch
) -> None:
    source, _, _ = _committed_source(tmp_path)
    observer = shadow.GlobalAllocationShadowObserverV1()
    blocker = sqlite3.connect(source.path, isolation_level=None)
    try:
        blocker.execute("BEGIN EXCLUSIVE")
        busy = observer.observe(source)
        assert busy.status is shadow.ShadowObservationStatusV1.SOURCE_UNAVAILABLE
    finally:
        blocker.rollback()
        blocker.close()
    before = _file_family(tmp_path)

    def fail_after_read(*_arguments):
        raise RuntimeError("test diagnostic computation failure")

    with monkeypatch.context() as scoped:
        scoped.setattr(shadow, "_observe_allocation_v1", fail_after_read)
        failed = observer.observe(source)
    assert failed.status is shadow.ShadowObservationStatusV1.OBSERVATION_FAILED
    assert failed.state_root == source.read_snapshot().state.state_root
    assert _file_family(tmp_path) == before
