"""End-to-end CBC tests for the authority-false Spot V7 V4 store."""

from __future__ import annotations

import copy
import json
import os
import pickle
import sqlite3
from dataclasses import dataclass, replace
from pathlib import Path
from typing import Any, Callable, cast
from unittest.mock import patch

import pytest

import src.integration.zrpf_spot_v7_atomic_operational_store_v4 as store_v4_module
import tests.integration.test_zrpf_spot_v7_governed_da_prerequisite_v2 as da_test
import tests.integration.test_zrpf_spot_v7_operational_atomic_store as legacy_store_test
import tests.integration.test_zrpf_spot_v7_operational_policy_provenance as policy_v2_test
import tests.integration.test_zrpf_spot_v7_operational_policy_v3 as policy_v3_test
import tests.integration.test_zrpf_spot_v7_settlement_envelope_replay as replay_test
import tests.integration.test_zrpf_spot_v7_settlement_finality_v3 as finality_v3_test
import tests.integration.test_zrpf_spot_v7_zeno_ledger_finality_adapter as finality_v2_test
from src.integration._zrpf_spot_v7_atomic_settlement_capability import (
    _derive_capability_commitment,
)
from src.integration._zrpf_spot_v7_atomic_settlement_evidence_v4 import (
    _validate_finality_row,
)
from src.integration._zrpf_spot_v7_firecracker_authority import (
    _GovernedFirecrackerSpotV7SettlementV1,
)
from src.integration._zrpf_spot_v7_operational_capability_v2 import (
    _AuthenticatedExactCheckpointFinalityTransitionV2,
    _GovernedOperationalPolicyMaterialV2,
)
from src.integration._zrpf_spot_v7_operational_capability_v3 import (
    _bind_spot_v7_operational_commit_capability_v3,
    _SpotV7AtomicEconomicCommitCapabilityV3,
)
from src.integration._zrpf_spot_v7_operational_policy_v3 import (
    _GovernedOperationalPolicyMaterialV3,
    _GovernedSpotV7OperationalPolicyV3,
)
from src.integration._zrpf_spot_v7_settlement_durable_replay import (
    _reverify_persisted_spot_v7_settlement_replay_v2,
)
from src.integration._zrpf_spot_v7_settlement_envelope_replay import (
    SpotV7SettlementEnvelopeReplayAdapterV2,
    build_spot_v7_settlement_envelope_v1,
)
from src.integration._zrpf_spot_v7_zeno_ledger_finality_contract import (
    derive_zeno_ledger_finality_network_id_v1,
    derive_zeno_ledger_finality_protocol_id_v2,
    derive_zeno_ledger_finality_protocol_id_v3,
)
from src.integration._zrpf_spot_v7_zeno_ledger_replay_observation import (
    SpotV7ZenoLedgerReplayBoundObservationAdapterV1,
)
from src.integration.dex_engine import DexEngineConfig
from src.integration.dex_snapshot import snapshot_from_state
from src.integration.zeno_ledger_replay import (
    replay_engine_config_digest_v0,
    replay_engine_config_document_v0,
)
from src.integration.zeno_ledger_v0 import (
    build_checkpoint_v0,
    canonical_json_bytes_v0,
    dex_state_root_v0,
)
from src.integration.zrpf_spot_v7_atomic_operational_store_v4 import (
    SQLiteSpotV7AtomicOperationalStoreV4,
)
from src.integration.zrpf_spot_v7_atomic_settlement_types import (
    SpotV7AtomicSettlementDispositionV1,
    SpotV7AtomicSettlementResultV1,
    SpotV7AtomicSettlementStoreErrorV1,
    SpotV7AtomicSettlementStoreIdentityV1,
    SpotV7CellOpeningV1,
)
from src.integration.zrpf_spot_v7_governed_da_prerequisite_v2 import (
    _bind_governed_spot_v7_da_prerequisite_v2,
    _bind_governed_spot_v7_sampled_response_v1,
)
from src.integration.zrpf_spot_v7_lagged_checkpoint_beacon import (
    bind_governed_spot_v7_lagged_checkpoint_beacon_v1,
)
from src.integration.zrpf_spot_v7_zeno_ledger_finality_adapter import (
    SpotV7ZenoLedgerCheckpointFinalityAdapterV2,
    SpotV7ZenoLedgerCheckpointFinalityAdapterV3,
    ZenoLedgerCheckpointFinalityCursorV1,
    derive_zeno_ledger_external_finality_policy_hash_v2,
)

_SOURCE_EPOCH = 19
_CURRENT_EPOCH = 20
_CHAIN_ID = replay_test._CHAIN_ID

_OPERATIONAL_BLOB_MUTATIONS = {
    "sampled-evidence": (
        "SELECT exact_sampled_evidence FROM spot_v7_operational_da_v4",
        "UPDATE spot_v7_operational_da_v4 SET exact_sampled_evidence = ?",
    ),
    "source-finality-evidence": (
        "SELECT exact_source_finality_evidence FROM spot_v7_operational_da_v4",
        "UPDATE spot_v7_operational_da_v4 SET exact_source_finality_evidence = ?",
    ),
    "current-finality-evidence": (
        "SELECT exact_finality_evidence FROM spot_v7_operational_finality_v4",
        "UPDATE spot_v7_operational_finality_v4 SET exact_finality_evidence = ?",
    ),
    "replay-body": (
        "SELECT exact_body FROM spot_v7_settlement_replay_v4",
        "UPDATE spot_v7_settlement_replay_v4 SET exact_body = ?",
    ),
    "policy-source-root": (
        "SELECT beacon_source_finality_policy_root "
        "FROM spot_v7_operational_policy_v4 WHERE singleton = 1",
        "UPDATE spot_v7_operational_policy_v4 "
        "SET beacon_source_finality_policy_root = ? WHERE singleton = 1",
    ),
    "policy-cursor-sequence": (
        "SELECT current_checkpoint_sequence_be "
        "FROM spot_v7_operational_policy_v4 WHERE singleton = 1",
        "UPDATE spot_v7_operational_policy_v4 "
        "SET current_checkpoint_sequence_be = ? WHERE singleton = 1",
    ),
    "policy-cursor-hash": (
        "SELECT current_checkpoint_hash FROM spot_v7_operational_policy_v4 WHERE singleton = 1",
        "UPDATE spot_v7_operational_policy_v4 SET current_checkpoint_hash = ? WHERE singleton = 1",
    ),
}

_AUTHORITY_FLAG_SELECTS = (
    (
        "SELECT current_release_head_verified, release_authority, "
        "settlement_authority, production_authority "
        "FROM spot_v7_operational_policy_v4 WHERE singleton = 1",
        (0, 0, 0, 0),
    ),
    (
        "SELECT public_future_availability_verified, settlement_authority, "
        "production_authority FROM spot_v7_operational_da_v4",
        (0, 0, 0),
    ),
    (
        "SELECT proof_receipt_authentication_established, settlement_authority, "
        "production_authority FROM spot_v7_operational_finality_v4",
        (0, 0, 0),
    ),
    (
        "SELECT proof_receipt_authentication_established, release_authority, "
        "settlement_authority, production_authority "
        "FROM spot_v7_settlement_replay_v4",
        (0, 0, 0, 0),
    ),
)

_AUTHORITY_FLAG_ESCALATIONS = (
    "UPDATE spot_v7_operational_policy_v4 SET current_release_head_verified = 1",
    "UPDATE spot_v7_operational_policy_v4 SET release_authority = 1",
    "UPDATE spot_v7_operational_policy_v4 SET settlement_authority = 1",
    "UPDATE spot_v7_operational_policy_v4 SET production_authority = 1",
    "UPDATE spot_v7_operational_da_v4 SET public_future_availability_verified = 1",
    "UPDATE spot_v7_operational_da_v4 SET settlement_authority = 1",
    "UPDATE spot_v7_operational_da_v4 SET production_authority = 1",
    "UPDATE spot_v7_operational_finality_v4 SET proof_receipt_authentication_established = 1",
    "UPDATE spot_v7_operational_finality_v4 SET settlement_authority = 1",
    "UPDATE spot_v7_operational_finality_v4 SET production_authority = 1",
    "UPDATE spot_v7_settlement_replay_v4 SET proof_receipt_authentication_established = 1",
    "UPDATE spot_v7_settlement_replay_v4 SET release_authority = 1",
    "UPDATE spot_v7_settlement_replay_v4 SET settlement_authority = 1",
    "UPDATE spot_v7_settlement_replay_v4 SET production_authority = 1",
)


@dataclass(frozen=True, slots=True)
class _GenuineV4Fixture:
    capability: _SpotV7AtomicEconomicCommitCapabilityV3
    settlement: _GovernedFirecrackerSpotV7SettlementV1
    policy: _GovernedSpotV7OperationalPolicyV3
    identity: SpotV7AtomicSettlementStoreIdentityV1
    genesis_cells: tuple[SpotV7CellOpeningV1, ...]
    settlement_commitment: str


class _CommitFaultConnection:
    """Delegate every SQLite operation except the injected outcome boundary."""

    def __init__(
        self,
        connection: sqlite3.Connection,
        *,
        commit_before_raise: bool,
        rollback_raises: bool,
    ) -> None:
        self._connection = connection
        self._commit_before_raise = commit_before_raise
        self._rollback_raises = rollback_raises
        self.commit_calls = 0
        self.rollback_calls = 0

    @property
    def in_transaction(self) -> bool:
        return self._connection.in_transaction

    def commit(self) -> None:
        self.commit_calls += 1
        if self._commit_before_raise:
            self._connection.commit()
        raise sqlite3.OperationalError("injected commit acknowledgement failure")

    def rollback(self) -> None:
        self.rollback_calls += 1
        if self._rollback_raises:
            raise sqlite3.OperationalError("injected rollback failure")
        self._connection.rollback()

    def close(self) -> None:
        self._connection.close()

    def __getattr__(self, name: str) -> Any:
        return getattr(self._connection, name)


def _private_directory(tmp_path: Path, name: str = "private") -> Path:
    directory = tmp_path / name
    directory.mkdir(mode=0o700)
    return directory


def _proposer_index(duty: dict[str, Any]) -> int:
    proposer = duty["proposer"]
    if type(proposer) is not dict:
        raise TypeError("test proposer must be an exact dict")
    validator_id = proposer.get("validator_id")
    if validator_id == "sequencer-0":
        return 0
    if validator_id == "sequencer-1":
        return 1
    raise ValueError("test proposer is outside the two-validator fixture")


def _authenticate_source_finality_v2(
    *,
    source_policy: object,
    application_id: str,
    chain_or_domain_id: str,
    source_prior_hash: str,
    validator_set: dict[str, Any],
    finality_registry: dict[str, Any],
    config_document: dict[str, Any],
    pre_state: object,
) -> tuple[_AuthenticatedExactCheckpointFinalityTransitionV2, dict[str, Any]]:
    pre_state_root = dex_state_root_v0(pre_state)
    source_candidate = replace(
        finality_v2_test._candidate(epoch_id=_SOURCE_EPOCH),
        application_id=application_id,
        chain_or_domain_id=chain_or_domain_id,
        pre_state_root=pre_state_root,
        post_state_root=pre_state_root,
    )
    source_body = finality_v2_test._ledger_body(source_candidate)
    source_header = finality_v2_test._header(
        source_candidate,
        validator_set,
        previous_hash=source_prior_hash,
    )
    replay_observation = SpotV7ZenoLedgerReplayBoundObservationAdapterV1(
        config_document
    ).authenticate(
        header=source_header,
        body=source_body,
        pre_snapshot=snapshot_from_state(pre_state).data,
        parent_header=None,
    )
    checkpoint = build_checkpoint_v0(source_header)
    duty = finality_v2_test.build_proposer_duty_v0(
        validator_set=validator_set,
        height=_SOURCE_EPOCH,
    )
    proposer = cast(dict[str, Any], duty["proposer"])
    capability = SpotV7ZenoLedgerCheckpointFinalityAdapterV2(source_policy).authenticate(
        settlement=finality_v2_test._settlement(source_candidate),
        prior_cursor=ZenoLedgerCheckpointFinalityCursorV1(
            _SOURCE_EPOCH - 1,
            source_prior_hash,
        ),
        header=source_header,
        replay_observation=replay_observation,
        checkpoint=checkpoint,
        validator_set=validator_set,
        proposer_id=str(proposer["validator_id"]),
        proposer_key_id=str(proposer["key_id"]),
        proposer_envelope=finality_v2_test._proposer_envelope(
            str(checkpoint["header_hash"]),
            validator_set,
            height=_SOURCE_EPOCH,
            proposer_index=_proposer_index(duty),
        ),
        registry=finality_registry,
        envelopes=finality_v2_test._envelopes(str(checkpoint["header_hash"])),
    )
    return capability, source_header


def _signed_source_policy_v2(
    material: _GovernedOperationalPolicyMaterialV2,
) -> object:
    release_registry = policy_v2_test._registry()
    manifest = policy_v2_test._manifest(
        release_registry,
        material=material,
        policy_activation_epoch=0,
        registry_activation_epoch=0,
    )
    return policy_v2_test._load(
        manifest,
        release_registry,
        policy_v2_test._envelopes(manifest),
        evaluation_epoch=_SOURCE_EPOCH,
    )


def _signed_policy_v3(
    material: _GovernedOperationalPolicyMaterialV3,
) -> _GovernedSpotV7OperationalPolicyV3:
    release_registry = policy_v3_test._registry()
    manifest = policy_v3_test._manifest(release_registry, material=material)
    return policy_v3_test._load(
        manifest,
        release_registry,
        pin_material=material,
    )


def _build_genuine_v4_fixture() -> _GenuineV4Fixture:
    with (
        patch.object(finality_v2_test, "CHAIN_ID", _CHAIN_ID),
        patch.object(policy_v3_test, "CHAIN_ID", _CHAIN_ID),
        patch.object(da_test, "EPOCH_ID", _CURRENT_EPOCH),
        patch.object(da_test, "CHECKED_EPOCH", _CURRENT_EPOCH),
        patch.object(
            da_test,
            "RETENTION_THROUGH_EPOCH",
            _CURRENT_EPOCH + 15,
        ),
    ):
        finality_registry = finality_v2_test._registry()
        validator_set = finality_v2_test._validator_set()
        config_document = replay_engine_config_document_v0(DexEngineConfig(chain_id=_CHAIN_ID))
        external_finality_policy_hash = derive_zeno_ledger_external_finality_policy_hash_v2(
            chain_id=_CHAIN_ID,
            config_digest=replay_engine_config_digest_v0(config_document),
            sequencer_set_hash=str(validator_set["validator_set_hash"]),
        )
        application_id = policy_v3_test._root("application")
        chain_or_domain_id = policy_v3_test._root("domain")
        source_prior_hash = policy_v3_test._root("source-prior-18")
        source_material = replace(
            policy_v2_test._material(),
            application_id=application_id,
            chain_or_domain_id=chain_or_domain_id,
            finality_network_id=derive_zeno_ledger_finality_network_id_v1(_CHAIN_ID),
            finality_protocol_id=derive_zeno_ledger_finality_protocol_id_v2(),
            external_finality_policy_hash=external_finality_policy_hash,
            finality_verifier_set_root=str(finality_registry["registry_hash"]),
            genesis_application_checkpoint_sequence=_SOURCE_EPOCH - 1,
            genesis_application_checkpoint_hash=source_prior_hash,
        )
        source_policy = _signed_source_policy_v2(source_material)
        pre_state, _post_state = replay_test._states()
        source_finality, source_header = _authenticate_source_finality_v2(
            source_policy=source_policy,
            application_id=application_id,
            chain_or_domain_id=chain_or_domain_id,
            source_prior_hash=source_prior_hash,
            validator_set=validator_set,
            finality_registry=finality_registry,
            config_document=config_document,
            pre_state=pre_state,
        )
        source_projection = source_finality._projection
        source_checkpoint_hash = source_projection.next_application_checkpoint_hash
        base_material = replace(
            policy_v3_test._base_material(),
            finality_network_id=derive_zeno_ledger_finality_network_id_v1(_CHAIN_ID),
            finality_protocol_id=derive_zeno_ledger_finality_protocol_id_v3(),
            external_finality_policy_hash=external_finality_policy_hash,
            finality_verifier_set_root=str(finality_registry["registry_hash"]),
            genesis_application_checkpoint_sequence=_SOURCE_EPOCH,
            genesis_application_checkpoint_hash=source_checkpoint_hash,
        )
        material = policy_v3_test._material(
            base=base_material,
            source_finality=source_material,
        )
        policy = _signed_policy_v3(material)
        beacon = bind_governed_spot_v7_lagged_checkpoint_beacon_v1(
            operational_policy=policy,
            source_finality=source_finality,
            checked_epoch=_CURRENT_EPOCH,
        )
        sampled = da_test._sampled(policy, beacon)
        governed_sample = _bind_governed_spot_v7_sampled_response_v1(
            operational_policy=policy,
            governed_beacon=beacon,
            sampled_response=sampled,
        )
        data_availability = _bind_governed_spot_v7_da_prerequisite_v2(
            operational_policy=policy,
            exact_full_blob=da_test._full_blob(policy),
            governed_sampled_response=governed_sample,
        )
        da_projection = data_availability._projection_for_downstream_binding_v2()
        partial_candidate = replace(
            replay_test._candidate(),
            application_id=application_id,
            chain_or_domain_id=chain_or_domain_id,
            epoch_id=_CURRENT_EPOCH,
            data_availability_certificate_root=(da_projection.base.certificate_root),
            data_root=da_projection.base.data_root,
            exact_v7_journal_bytes=b"placeholder",
        )
        candidate = replace(
            partial_candidate,
            exact_v7_journal_bytes=replay_test._v7_journal(partial_candidate),
        )
        settlement = replay_test._settlement(candidate)
        body = finality_v3_test._body_for_chain(
            replay_test._body(
                candidate,
                build_spot_v7_settlement_envelope_v1(settlement),
            )
        )
        header = finality_v3_test._header(
            candidate=candidate,
            body=body,
            validator_set=validator_set,
            previous_hash=source_checkpoint_hash,
        )
        replay_observation = SpotV7SettlementEnvelopeReplayAdapterV2(config_document).authenticate(
            settlement=settlement,
            header=header,
            body=body,
            pre_snapshot=snapshot_from_state(pre_state).data,
            parent_header=source_header,
        )
        persisted = replay_observation._durable_replay_packet_for_history_reverification()._persisted_inputs_for_storage()
        durable_replay = _reverify_persisted_spot_v7_settlement_replay_v2(
            settlement=settlement,
            persisted=persisted,
            exact_parent_header_bytes=canonical_json_bytes_v0(source_header),
        )
        checkpoint = build_checkpoint_v0(header)
        duty = finality_v2_test.build_proposer_duty_v0(
            validator_set=validator_set,
            height=_CURRENT_EPOCH,
        )
        proposer = cast(dict[str, Any], duty["proposer"])
        finality = SpotV7ZenoLedgerCheckpointFinalityAdapterV3(policy).authenticate(
            settlement=settlement,
            prior_cursor=ZenoLedgerCheckpointFinalityCursorV1(
                _SOURCE_EPOCH,
                source_checkpoint_hash,
            ),
            settlement_replay_observation=replay_observation,
            checkpoint=checkpoint,
            validator_set=validator_set,
            proposer_id=str(proposer["validator_id"]),
            proposer_key_id=str(proposer["key_id"]),
            proposer_envelope=finality_v2_test._proposer_envelope(
                str(checkpoint["header_hash"]),
                validator_set,
                height=_CURRENT_EPOCH,
                proposer_index=_proposer_index(duty),
            ),
            registry=finality_registry,
            envelopes=finality_v2_test._envelopes(str(checkpoint["header_hash"])),
        )
        capability = _bind_spot_v7_operational_commit_capability_v3(
            settlement=settlement,
            policy=policy,
            data_availability=data_availability,
            finality=finality,
            durable_replay=durable_replay,
            exact_parent_header_bytes=canonical_json_bytes_v0(source_header),
        )
        identity = SpotV7AtomicSettlementStoreIdentityV1(
            application_id=candidate.application_id,
            chain_or_domain_id=candidate.chain_or_domain_id,
            verified_program_id=candidate.verified_program_id,
            verified_profile_id=candidate.verified_profile_id,
            verified_program_manifest_root=(candidate.verified_program_manifest_root),
            genesis_state_root=candidate.pre_state_root,
        )
        genesis_cells = tuple(
            sorted(
                (transition.pre for transition in candidate.cell_transitions),
                key=lambda opening: opening.cell_key,
            )
        )
        return _GenuineV4Fixture(
            capability=capability,
            settlement=settlement,
            policy=policy,
            identity=identity,
            genesis_cells=genesis_cells,
            settlement_commitment=_derive_capability_commitment(candidate),
        )


@pytest.fixture(scope="module")
def genuine_v4_fixture() -> _GenuineV4Fixture:
    return _build_genuine_v4_fixture()


def _resolver(
    fixture: _GenuineV4Fixture,
    calls: list[str] | None = None,
) -> Callable[[str], object]:
    def resolve(commitment: str) -> object:
        if calls is not None:
            calls.append(commitment)
        if commitment != fixture.settlement_commitment:
            raise ValueError("unknown settlement commitment")
        return fixture.settlement

    return resolve


def _store(
    tmp_path: Path,
    fixture: _GenuineV4Fixture,
    *,
    resolver: Callable[[str], object] | None = None,
    directory_name: str = "private",
) -> SQLiteSpotV7AtomicOperationalStoreV4:
    return SQLiteSpotV7AtomicOperationalStoreV4(
        _private_directory(tmp_path, directory_name) / "spot-v7-v4.sqlite3",
        identity=fixture.identity,
        genesis_cells=fixture.genesis_cells,
        governed_operational_policy=fixture.policy,
        settlement_resolver=resolver or _resolver(fixture),
    )


def _commit(
    store: SQLiteSpotV7AtomicOperationalStoreV4,
    fixture: _GenuineV4Fixture,
) -> SpotV7AtomicSettlementResultV1:
    return store._commit_operational_capability_v3(
        expected_cursor=store.read_cursor(),
        capability=fixture.capability,
    )


def _open_existing(
    path: Path,
    fixture: _GenuineV4Fixture,
    *,
    resolver: Callable[[str], object] | None = None,
) -> SQLiteSpotV7AtomicOperationalStoreV4:
    return SQLiteSpotV7AtomicOperationalStoreV4(
        path,
        identity=fixture.identity,
        genesis_cells=fixture.genesis_cells,
        governed_operational_policy=fixture.policy,
        settlement_resolver=resolver or _resolver(fixture),
    )


def _flip_first_byte(value: bytes) -> bytes:
    if not value:
        raise ValueError("test mutation target must be nonempty")
    return bytes((value[0] ^ 1,)) + value[1:]


def _tamper_operational_blob(path: Path, mutation: str) -> None:
    select_statement, update_statement = _OPERATIONAL_BLOB_MUTATIONS[mutation]
    with sqlite3.connect(path) as connection:
        row = connection.execute(select_statement).fetchone()
        if row is None or type(row[0]) is not bytes:
            raise AssertionError("test mutation target must be one stored blob")
        connection.execute(update_statement, (_flip_first_byte(row[0]),))


def test_given_genuine_prerequisites_when_v4_commits_and_reopens_then_history_replays_authority_false(
    tmp_path: Path,
    genuine_v4_fixture: _GenuineV4Fixture,
) -> None:
    calls: list[str] = []
    store = _store(
        tmp_path,
        genuine_v4_fixture,
        resolver=_resolver(genuine_v4_fixture, calls),
    )

    result = _commit(store, genuine_v4_fixture)

    assert result.disposition is SpotV7AtomicSettlementDispositionV1.COMMITTED
    assert result.settlement_authority is False
    assert result.production_authority is False
    assert store.release_authority is False
    assert store.settlement_authority is False
    assert store.production_authority is False
    assert calls == []

    reopened = SQLiteSpotV7AtomicOperationalStoreV4(
        store.path,
        identity=genuine_v4_fixture.identity,
        genesis_cells=genuine_v4_fixture.genesis_cells,
        governed_operational_policy=genuine_v4_fixture.policy,
        settlement_resolver=_resolver(genuine_v4_fixture, calls),
    )

    assert reopened.read_cursor() == result.head_cursor
    assert reopened.get_receipt(genuine_v4_fixture.settlement_commitment) == result.receipt
    assert calls == [genuine_v4_fixture.settlement_commitment] * 3
    assert reopened.release_authority is False
    assert reopened.settlement_authority is False
    assert reopened.production_authority is False


def test_given_valid_signed_finality_when_rolling_parent_differs_then_direct_replay_rejects(
    tmp_path: Path,
    genuine_v4_fixture: _GenuineV4Fixture,
) -> None:
    store = _store(tmp_path, genuine_v4_fixture)
    committed = _commit(store, genuine_v4_fixture)
    assert committed.committed is True
    with sqlite3.connect(store.path) as connection:
        connection.row_factory = sqlite3.Row
        settlement_row = connection.execute("SELECT * FROM spot_v7_settlements").fetchone()
        finality_row = connection.execute(
            "SELECT * FROM spot_v7_operational_finality_v4"
        ).fetchone()
        replay_row = connection.execute(
            "SELECT exact_projection FROM spot_v7_settlement_replay_v4"
        ).fetchone()
        assert settlement_row is not None
        assert finality_row is not None
        assert replay_row is not None and type(replay_row[0]) is bytes
        replay_projection = json.loads(replay_row[0])
        assert type(replay_projection) is dict

        finality_policy = genuine_v4_fixture.policy._base_store_policy_for_finality_v3()
        candidate = genuine_v4_fixture.settlement._candidate_for_atomic_store()
        accepted_cursor = _validate_finality_row(
            genuine_v4_fixture.policy,
            candidate=candidate,
            settlement_row=settlement_row,
            replay_projection=replay_projection,
            row=finality_row,
            prior_sequence=finality_policy.genesis_application_checkpoint_sequence,
            prior_hash=finality_policy.genesis_application_checkpoint_hash,
        )
        assert accepted_cursor[0] == _CURRENT_EPOCH

        with pytest.raises(ValueError, match="finality prior cursor mismatch"):
            _validate_finality_row(
                genuine_v4_fixture.policy,
                candidate=candidate,
                settlement_row=settlement_row,
                replay_projection=replay_projection,
                row=finality_row,
                prior_sequence=(finality_policy.genesis_application_checkpoint_sequence),
                prior_hash=policy_v3_test._root("wrong-rolling-parent"),
            )


def test_given_exact_committed_capability_when_retried_then_result_is_idempotent(
    tmp_path: Path,
    genuine_v4_fixture: _GenuineV4Fixture,
) -> None:
    store = _store(tmp_path, genuine_v4_fixture)
    initial_cursor = store.read_cursor()

    committed = store._commit_operational_capability_v3(
        expected_cursor=initial_cursor,
        capability=genuine_v4_fixture.capability,
    )
    retried = store._commit_operational_capability_v3(
        expected_cursor=initial_cursor,
        capability=genuine_v4_fixture.capability,
    )

    assert committed.disposition is SpotV7AtomicSettlementDispositionV1.COMMITTED
    assert retried.disposition is SpotV7AtomicSettlementDispositionV1.IDEMPOTENT_REPLAY
    assert retried.head_cursor == committed.head_cursor
    assert retried.receipt == committed.receipt
    assert retried.settlement_authority is False
    assert retried.production_authority is False
    assert store.read_cursor() == committed.head_cursor


def test_given_commit_and_rollback_failures_then_primary_outcome_unknown_error_survives(
    tmp_path: Path,
    genuine_v4_fixture: _GenuineV4Fixture,
) -> None:
    store = _store(tmp_path, genuine_v4_fixture)
    initial_cursor = store.read_cursor()
    proxy = _CommitFaultConnection(
        store._connect(),
        commit_before_raise=False,
        rollback_raises=True,
    )
    with patch.object(
        store_v4_module.SQLiteSpotV7AtomicOperationalStoreV4,
        "_connect",
        return_value=proxy,
    ):
        with pytest.raises(SpotV7AtomicSettlementStoreErrorV1) as captured:
            store._commit_operational_capability_v3(
                expected_cursor=initial_cursor,
                capability=genuine_v4_fixture.capability,
            )

    assert captured.value.code == ("SPOT_V7_ATOMIC_OPERATIONAL_V4_COMMIT_OUTCOME_UNKNOWN")
    assert captured.value.detail == ("commit acknowledgement failed; reconcile with an exact retry")
    assert proxy.commit_calls == 1
    assert proxy.rollback_calls == 1
    assert isinstance(captured.value.__cause__, sqlite3.OperationalError)


def test_given_commit_succeeds_before_ack_failure_then_exact_retry_is_idempotent(
    tmp_path: Path,
    genuine_v4_fixture: _GenuineV4Fixture,
) -> None:
    store = _store(tmp_path, genuine_v4_fixture)
    initial_cursor = store.read_cursor()
    proxy = _CommitFaultConnection(
        store._connect(),
        commit_before_raise=True,
        rollback_raises=False,
    )
    with patch.object(
        store_v4_module.SQLiteSpotV7AtomicOperationalStoreV4,
        "_connect",
        return_value=proxy,
    ):
        with pytest.raises(SpotV7AtomicSettlementStoreErrorV1) as captured:
            store._commit_operational_capability_v3(
                expected_cursor=initial_cursor,
                capability=genuine_v4_fixture.capability,
            )

    assert captured.value.code == ("SPOT_V7_ATOMIC_OPERATIONAL_V4_COMMIT_OUTCOME_UNKNOWN")
    assert proxy.commit_calls == 1
    assert proxy.rollback_calls == 0

    retried = store._commit_operational_capability_v3(
        expected_cursor=initial_cursor,
        capability=genuine_v4_fixture.capability,
    )
    assert retried.disposition is SpotV7AtomicSettlementDispositionV1.IDEMPOTENT_REPLAY
    assert retried.idempotent_replay is True
    assert retried.receipt is not None
    assert retried.head_cursor.revision == initial_cursor.revision + 1
    assert retried.settlement_authority is False
    assert retried.production_authority is False


def test_given_new_v4_store_then_schema_contains_no_legacy_operational_tables(
    tmp_path: Path,
    genuine_v4_fixture: _GenuineV4Fixture,
) -> None:
    store = _store(tmp_path, genuine_v4_fixture)
    with sqlite3.connect(store.path) as connection:
        observed = {
            str(row[0])
            for row in connection.execute(
                "SELECT name FROM sqlite_master WHERE type = 'table'"
            ).fetchall()
        }

    assert observed.isdisjoint(
        {
            "spot_v7_operational_policy",
            "spot_v7_operational_da",
            "spot_v7_operational_finality",
            "spot_v7_operational_policy_provenance",
        }
    )
    assert {
        "spot_v7_operational_policy_v4",
        "spot_v7_operational_da_v4",
        "spot_v7_operational_finality_v4",
        "spot_v7_settlement_replay_v4",
    } <= observed


def test_given_failed_atomic_initialization_then_no_final_database_exists_and_retry_succeeds(
    tmp_path: Path,
    genuine_v4_fixture: _GenuineV4Fixture,
) -> None:
    private = _private_directory(tmp_path)
    path = private / "spot-v7-v4.sqlite3"
    staging = private / ".spot-v7-v4.sqlite3.spot-v7-v4-initializing"
    with patch.object(
        store_v4_module,
        "_validate_complete_spot_v7_operational_history_v4",
        side_effect=ValueError("injected initialization validation failure"),
    ):
        with pytest.raises(SpotV7AtomicSettlementStoreErrorV1) as captured:
            _open_existing(path, genuine_v4_fixture)

    assert captured.value.code == "SPOT_V7_ATOMIC_OPERATIONAL_V4_OPEN_FAILED"
    assert captured.value.detail == "injected initialization validation failure"
    assert not path.exists()
    assert not staging.exists()
    assert not Path(f"{staging}-journal").exists()
    assert not Path(f"{staging}-wal").exists()
    assert not Path(f"{staging}-shm").exists()

    corrected = _open_existing(path, genuine_v4_fixture)
    assert corrected.read_cursor().revision == 0
    assert corrected.read_cursor().settlement_count == 0
    assert corrected.read_cursor().last_epoch_id is None


def test_given_valid_single_link_staging_when_final_is_absent_then_initialization_resumes(
    tmp_path: Path,
    genuine_v4_fixture: _GenuineV4Fixture,
) -> None:
    private = _private_directory(tmp_path)
    seed_path = private / "seed.sqlite3"
    seed = _open_existing(seed_path, genuine_v4_fixture)
    assert seed.read_cursor().revision == 0
    path = private / "spot-v7-v4.sqlite3"
    staging = private / ".spot-v7-v4.sqlite3.spot-v7-v4-initializing"
    seed_path.rename(staging)
    staging_info = staging.stat(follow_symlinks=False)
    staging_bytes = staging.read_bytes()
    assert not path.exists()
    assert staging_info.st_nlink == 1

    recovered = _open_existing(path, genuine_v4_fixture)

    final_info = path.stat(follow_symlinks=False)
    assert recovered.read_cursor().revision == 0
    assert path.read_bytes() == staging_bytes
    assert final_info.st_ino == staging_info.st_ino
    assert final_info.st_nlink == 1
    assert not staging.exists()


def test_given_published_two_link_initialization_when_reopened_then_only_staging_is_removed(
    tmp_path: Path,
    genuine_v4_fixture: _GenuineV4Fixture,
) -> None:
    private = _private_directory(tmp_path)
    path = private / "spot-v7-v4.sqlite3"
    store = _open_existing(path, genuine_v4_fixture)
    assert store.read_cursor().revision == 0
    staging = private / ".spot-v7-v4.sqlite3.spot-v7-v4-initializing"
    final_bytes = path.read_bytes()
    original_info = path.stat(follow_symlinks=False)
    os.link(path, staging, follow_symlinks=False)
    assert path.stat(follow_symlinks=False).st_nlink == 2
    assert staging.stat(follow_symlinks=False).st_ino == original_info.st_ino

    recovered = _open_existing(path, genuine_v4_fixture)

    recovered_info = path.stat(follow_symlinks=False)
    assert recovered.read_cursor().revision == 0
    assert path.read_bytes() == final_bytes
    assert recovered_info.st_ino == original_info.st_ino
    assert recovered_info.st_nlink == 1
    assert not staging.exists()


def test_given_result_construction_failure_then_transaction_rolls_back_before_reopen(
    tmp_path: Path,
    genuine_v4_fixture: _GenuineV4Fixture,
) -> None:
    store = _store(tmp_path, genuine_v4_fixture)
    genesis_cursor = store.read_cursor()
    with patch.object(
        store_v4_module,
        "SpotV7AtomicSettlementResultV1",
        side_effect=ValueError("injected result construction failure"),
    ):
        with pytest.raises(SpotV7AtomicSettlementStoreErrorV1) as captured:
            _commit(store, genuine_v4_fixture)

    assert captured.value.code == "SPOT_V7_ATOMIC_OPERATIONAL_V4_COMMIT_FAILED"
    assert captured.value.detail == "injected result construction failure"
    reopened = _open_existing(store.path, genuine_v4_fixture)
    assert reopened.read_cursor() == genesis_cursor
    assert reopened.read_cursor().revision == 0
    assert reopened.read_cursor().settlement_count == 0
    assert reopened.get_receipt(genuine_v4_fixture.settlement_commitment) is None

    retried = reopened._commit_operational_capability_v3(
        expected_cursor=genesis_cursor,
        capability=genuine_v4_fixture.capability,
    )
    assert retried.disposition is SpotV7AtomicSettlementDispositionV1.COMMITTED
    assert retried.head_cursor.revision == 1
    assert retried.head_cursor.settlement_count == 1
    assert reopened.read_cursor() == retried.head_cursor
    assert reopened.get_receipt(genuine_v4_fixture.settlement_commitment) == (retried.receipt)


def test_given_two_store_instances_with_same_stale_cursor_when_both_commit_then_only_one_is_new(
    tmp_path: Path,
    genuine_v4_fixture: _GenuineV4Fixture,
) -> None:
    first_store = _store(tmp_path, genuine_v4_fixture)
    second_store = _open_existing(first_store.path, genuine_v4_fixture)
    shared_stale_cursor = first_store.read_cursor()

    first = first_store._commit_operational_capability_v3(
        expected_cursor=shared_stale_cursor,
        capability=genuine_v4_fixture.capability,
    )
    second = second_store._commit_operational_capability_v3(
        expected_cursor=shared_stale_cursor,
        capability=genuine_v4_fixture.capability,
    )

    dispositions = (first.disposition, second.disposition)
    assert dispositions.count(SpotV7AtomicSettlementDispositionV1.COMMITTED) == 1
    assert dispositions.count(SpotV7AtomicSettlementDispositionV1.IDEMPOTENT_REPLAY) == 1
    assert first.head_cursor == second.head_cursor
    assert first.receipt == second.receipt
    assert first_store.read_cursor() == second_store.read_cursor()


def test_given_open_store_when_copy_serialize_or_mutate_is_attempted_then_it_rejects(
    tmp_path: Path,
    genuine_v4_fixture: _GenuineV4Fixture,
) -> None:
    store = _store(tmp_path, genuine_v4_fixture)

    with pytest.raises(TypeError, match="cannot be copied"):
        copy.copy(store)
    with pytest.raises(TypeError, match="cannot be deep-copied"):
        copy.deepcopy(store)
    with pytest.raises(TypeError, match="cannot be serialized"):
        pickle.dumps(store)
    with pytest.raises(TypeError, match="cannot be mutated"):
        store._busy_timeout_ms = 1


def test_given_committed_store_when_resolver_raises_runtime_error_then_open_returns_typed_error(
    tmp_path: Path,
    genuine_v4_fixture: _GenuineV4Fixture,
) -> None:
    store = _store(tmp_path, genuine_v4_fixture)
    committed = _commit(store, genuine_v4_fixture)
    assert committed.committed is True

    def failed_resolver(_commitment: str) -> object:
        raise RuntimeError("deterministic resolver failure")

    with pytest.raises(SpotV7AtomicSettlementStoreErrorV1) as captured:
        _open_existing(
            store.path,
            genuine_v4_fixture,
            resolver=failed_resolver,
        )

    assert captured.value.code == "SPOT_V7_ATOMIC_OPERATIONAL_V4_OPEN_FAILED"
    assert captured.value.detail == "Spot V7 V4 settlement resolver failed"


def test_given_open_store_when_same_inode_is_truncated_then_read_rejects_without_reinitializing(
    tmp_path: Path,
    genuine_v4_fixture: _GenuineV4Fixture,
) -> None:
    store = _store(tmp_path, genuine_v4_fixture)
    path = store.path
    original_inode = path.stat().st_ino
    with path.open("r+b") as database:
        database.truncate(0)
    assert path.stat().st_ino == original_inode
    assert path.stat().st_size == 0

    with pytest.raises(SpotV7AtomicSettlementStoreErrorV1) as captured:
        store.read_cursor()

    assert captured.value.code == "SPOT_V7_ATOMIC_OPERATIONAL_V4_READ_FAILED"
    assert path.stat().st_ino == original_inode
    assert path.stat().st_size == 0


def test_given_committed_store_then_sql_authority_flags_are_zero_and_cannot_escalate(
    tmp_path: Path,
    genuine_v4_fixture: _GenuineV4Fixture,
) -> None:
    store = _store(tmp_path, genuine_v4_fixture)
    committed = _commit(store, genuine_v4_fixture)
    assert committed.committed is True

    with sqlite3.connect(store.path) as connection:
        for statement, expected in _AUTHORITY_FLAG_SELECTS:
            row = connection.execute(statement).fetchone()
            assert row is not None
            assert tuple(row) == expected

    for statement in _AUTHORITY_FLAG_ESCALATIONS:
        with sqlite3.connect(store.path) as connection:
            with pytest.raises(sqlite3.IntegrityError):
                connection.execute(statement)
            connection.rollback()

    reopened = _open_existing(store.path, genuine_v4_fixture)
    assert reopened.release_authority is False
    assert reopened.settlement_authority is False
    assert reopened.production_authority is False


@pytest.mark.parametrize("mutation", tuple(_OPERATIONAL_BLOB_MUTATIONS))
def test_given_committed_store_when_operational_row_is_tampered_then_reopen_rejects(
    tmp_path: Path,
    genuine_v4_fixture: _GenuineV4Fixture,
    mutation: str,
) -> None:
    store = _store(tmp_path, genuine_v4_fixture)
    committed = _commit(store, genuine_v4_fixture)
    assert committed.committed is True
    _tamper_operational_blob(store.path, mutation)
    tampered_bytes = store.path.read_bytes()

    with pytest.raises(SpotV7AtomicSettlementStoreErrorV1) as captured:
        _open_existing(store.path, genuine_v4_fixture)

    assert captured.value.code == "SPOT_V7_ATOMIC_OPERATIONAL_V4_OPEN_FAILED"
    assert store.path.read_bytes() == tampered_bytes


def test_given_current_finality_claim_when_boolean_is_encoded_as_integer_then_reopen_rejects_claim(
    tmp_path: Path,
    genuine_v4_fixture: _GenuineV4Fixture,
) -> None:
    store = _store(tmp_path, genuine_v4_fixture)
    committed = _commit(store, genuine_v4_fixture)
    assert committed.committed is True
    with sqlite3.connect(store.path) as connection:
        row = connection.execute(
            "SELECT exact_finality_evidence FROM spot_v7_operational_finality_v4"
        ).fetchone()
        assert row is not None and type(row[0]) is bytes
        document = json.loads(row[0])
        assert type(document) is dict
        claims = document.get("claims")
        assert type(claims) is dict
        assert claims["production_authority"] is False
        claims["production_authority"] = 0
        connection.execute(
            "UPDATE spot_v7_operational_finality_v4 SET exact_finality_evidence = ?",
            (canonical_json_bytes_v0(document),),
        )

    with pytest.raises(SpotV7AtomicSettlementStoreErrorV1) as captured:
        _open_existing(store.path, genuine_v4_fixture)

    assert captured.value.code == "SPOT_V7_ATOMIC_OPERATIONAL_V4_OPEN_FAILED"
    assert "finality claim boundary mismatch" in captured.value.detail


@pytest.mark.parametrize(
    "admission_field",
    (
        "scheduled_header_admission",
        "proposer_authorship_admission",
        "live_quorum_admission",
    ),
)
def test_given_finality_admission_when_ok_boolean_is_integer_then_reopen_rejects_transcript(
    tmp_path: Path,
    genuine_v4_fixture: _GenuineV4Fixture,
    admission_field: str,
) -> None:
    store = _store(tmp_path, genuine_v4_fixture)
    committed = _commit(store, genuine_v4_fixture)
    assert committed.committed is True
    with sqlite3.connect(store.path) as connection:
        row = connection.execute(
            "SELECT exact_finality_evidence FROM spot_v7_operational_finality_v4"
        ).fetchone()
        assert row is not None and type(row[0]) is bytes
        document = json.loads(row[0])
        assert type(document) is dict
        admission = document.get(admission_field)
        assert type(admission) is dict
        assert admission["ok"] is True
        admission["ok"] = 1
        connection.execute(
            "UPDATE spot_v7_operational_finality_v4 SET exact_finality_evidence = ?",
            (canonical_json_bytes_v0(document),),
        )

    with pytest.raises(SpotV7AtomicSettlementStoreErrorV1) as captured:
        _open_existing(store.path, genuine_v4_fixture)

    assert captured.value.code == "SPOT_V7_ATOMIC_OPERATIONAL_V4_OPEN_FAILED"
    assert "finality admission transcript mismatch" in captured.value.detail


@pytest.mark.parametrize("resolver_mode", ("missing", "wrong"))
def test_given_committed_v4_when_resolver_is_missing_or_wrong_then_reopen_fails_closed(
    tmp_path: Path,
    genuine_v4_fixture: _GenuineV4Fixture,
    resolver_mode: str,
) -> None:
    store = _store(tmp_path, genuine_v4_fixture)
    committed = _commit(store, genuine_v4_fixture)
    assert committed.committed is True

    if resolver_mode == "missing":

        def rejected_resolver(_commitment: str) -> object:
            return None

    else:
        candidate = genuine_v4_fixture.settlement._candidate_for_atomic_store()
        wrong_settlement = replay_test._settlement(
            replace(
                candidate,
                authorization_nullifier=policy_v3_test._root("wrong-resolver-authorization"),
            )
        )

        def rejected_resolver(_commitment: str) -> object:
            return wrong_settlement

    with pytest.raises(SpotV7AtomicSettlementStoreErrorV1) as captured:
        SQLiteSpotV7AtomicOperationalStoreV4(
            store.path,
            identity=genuine_v4_fixture.identity,
            genesis_cells=genuine_v4_fixture.genesis_cells,
            governed_operational_policy=genuine_v4_fixture.policy,
            settlement_resolver=rejected_resolver,
        )

    assert captured.value.code == "SPOT_V7_ATOMIC_OPERATIONAL_V4_OPEN_FAILED"


@pytest.mark.parametrize("path_attack", ("deleted", "replaced"))
def test_given_open_v4_when_database_path_is_deleted_or_replaced_then_read_fails_without_recreation(
    tmp_path: Path,
    genuine_v4_fixture: _GenuineV4Fixture,
    path_attack: str,
) -> None:
    store = _store(tmp_path, genuine_v4_fixture)
    path = store.path
    original_bytes = path.read_bytes()
    path.unlink()
    if path_attack == "replaced":
        path.write_bytes(original_bytes)
        path.chmod(0o600)
        replacement_identity = path.stat().st_ino

    with pytest.raises(SpotV7AtomicSettlementStoreErrorV1) as captured:
        store.read_cursor()

    assert captured.value.code == "SPOT_V7_ATOMIC_OPERATIONAL_V4_READ_FAILED"
    if path_attack == "deleted":
        assert not path.exists()
    else:
        assert path.exists()
        assert path.stat().st_ino == replacement_identity
        assert path.read_bytes() == original_bytes


def test_given_populated_v3_database_when_opened_as_v4_then_migration_is_rejected(
    tmp_path: Path,
    genuine_v4_fixture: _GenuineV4Fixture,
) -> None:
    legacy = legacy_store_test._store(tmp_path)
    legacy_result = legacy._commit_test_only_operational_capability(
        expected_cursor=legacy.read_cursor(),
        capability=legacy_store_test._packet(),
    )
    assert legacy_result.committed is True
    before = legacy.path.read_bytes()

    with pytest.raises(SpotV7AtomicSettlementStoreErrorV1) as captured:
        SQLiteSpotV7AtomicOperationalStoreV4(
            legacy.path,
            identity=genuine_v4_fixture.identity,
            genesis_cells=genuine_v4_fixture.genesis_cells,
            governed_operational_policy=genuine_v4_fixture.policy,
            settlement_resolver=_resolver(genuine_v4_fixture),
        )

    assert captured.value.code == "SPOT_V7_ATOMIC_OPERATIONAL_V4_OPEN_FAILED"
    assert legacy.path.read_bytes() == before
