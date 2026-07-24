"""CBC tests for the unavailable Spot V7 DA/finality commit gate."""

from __future__ import annotations

import copy
import hashlib
import inspect
import pickle

import pytest

import src.integration._zrpf_spot_v7_firecracker_authority as firecracker_authority
import src.integration._zrpf_spot_v7_operational_gate as operational_gate
from src.integration._zrpf_spot_v7_atomic_settlement_capability import (
    _SpotV7SettlementCandidateInputV1,
)
from src.integration._zrpf_spot_v7_firecracker_authority import (
    _GovernedFirecrackerSpotV7SettlementV1,
)
from src.integration._zrpf_spot_v7_operational_gate import (
    SPOT_V7_OPERATIONAL_COMMIT_MISSING_CONDITIONS_V1,
    SpotV7OperationalCommitAuthorityUnavailableV1,
    SpotV7OperationalCommitMissingConditionV1,
    SpotV7OperationalGateBindingErrorV1,
    _AuthenticatedCheckpointFinalityProjectionV2,
    _AuthenticatedCheckpointFinalityTransitionV2,
    _bind_spot_v7_operational_commit_capability_v1,
    _GovernedFullBlobPolicyProjectionV1,
    _GovernedLocalFullBlobPolicySatisfactionV1,
    _GovernedOperationalPolicyProjectionV1,
    _GovernedSpotV7OperationalPolicyV1,
    _SpotV7AtomicEconomicCommitCapabilityV1,
    _validate_spot_v7_operational_gate_inputs_v1,
)
from src.integration.zrpf_spot_v7_atomic_settlement_store import (
    SQLiteSpotV7AtomicSettlementStoreV1,
)
from src.integration.zrpf_spot_v7_atomic_settlement_types import (
    SpotV7AssetEffectV1,
    SpotV7AtomicSettlementCursorV1,
    SpotV7CellKindV1,
    SpotV7CellOpeningV1,
    SpotV7CellRoleV1,
    SpotV7CellTransitionV1,
    spot_v7_cell_transitions_root_v1,
)


def _root(seed: int) -> str:
    return f"0x{seed:064x}"


def _opening(
    kind: SpotV7CellKindV1,
    subject_id: str,
    asset_id: str,
    atoms: int,
) -> SpotV7CellOpeningV1:
    return SpotV7CellOpeningV1(kind, subject_id, asset_id, atoms)


def _candidate() -> _SpotV7SettlementCandidateInputV1:
    sender = "0x" + (bytes((0x11,)) * 48).hex()
    pool = "0x" + (bytes((0x22,)) * 32).hex()
    input_asset = _root(0x33)
    output_asset = _root(0x44)
    recipient = "0x" + (bytes((0x55,)) * 48).hex()
    action = _root(0x66)
    transitions = tuple(
        sorted(
            (
                SpotV7CellTransitionV1(
                    SpotV7CellRoleV1.DEBIT,
                    _opening(
                        SpotV7CellKindV1.ACCOUNT_BALANCE,
                        sender,
                        input_asset,
                        1_000,
                    ),
                    _opening(
                        SpotV7CellKindV1.ACCOUNT_BALANCE,
                        sender,
                        input_asset,
                        900,
                    ),
                ),
                SpotV7CellTransitionV1(
                    SpotV7CellRoleV1.CREDIT,
                    _opening(
                        SpotV7CellKindV1.POOL_RESERVE,
                        pool,
                        input_asset,
                        5_000,
                    ),
                    _opening(
                        SpotV7CellKindV1.POOL_RESERVE,
                        pool,
                        input_asset,
                        5_100,
                    ),
                ),
                SpotV7CellTransitionV1(
                    SpotV7CellRoleV1.DEBIT,
                    _opening(
                        SpotV7CellKindV1.POOL_RESERVE,
                        pool,
                        output_asset,
                        8_000,
                    ),
                    _opening(
                        SpotV7CellKindV1.POOL_RESERVE,
                        pool,
                        output_asset,
                        7_940,
                    ),
                ),
                SpotV7CellTransitionV1(
                    SpotV7CellRoleV1.CREDIT,
                    _opening(
                        SpotV7CellKindV1.ACCOUNT_BALANCE,
                        recipient,
                        output_asset,
                        25,
                    ),
                    _opening(
                        SpotV7CellKindV1.ACCOUNT_BALANCE,
                        recipient,
                        output_asset,
                        85,
                    ),
                ),
            ),
            key=lambda row: row.cell_key,
        )
    )
    effects = tuple(
        sorted(
            (
                SpotV7AssetEffectV1(action, input_asset, 100),
                SpotV7AssetEffectV1(action, output_asset, 60),
            ),
            key=lambda row: (row.asset_id, row.effect_id),
        )
    )
    return _SpotV7SettlementCandidateInputV1(
        application_id=_root(1),
        chain_or_domain_id=_root(2),
        epoch_id=9,
        verified_program_id=_root(3),
        verified_profile_id=_root(4),
        verified_program_manifest_root=_root(5),
        source_child_claim_binding=_root(6),
        source_child_journal_sha256=_root(7),
        data_availability_certificate_root=_root(8),
        data_root=_root(9),
        settlement_effect_plan_commitment=_root(10),
        pre_state_root=_root(11),
        post_state_root=_root(12),
        economic_action_id=action,
        authorization_nullifier=_root(13),
        authorization_grant_spend_nullifier=_root(14),
        consumed_object_ids=(_root(15),),
        cell_transitions=transitions,
        cell_transitions_root=spot_v7_cell_transitions_root_v1(transitions),
        asset_effects=effects,
        exact_v7_receipt_bytes=b"receipt",
        exact_v7_journal_bytes=b"journal",
        exact_plan_b_bytes=b"plan",
        exact_firecracker_execution_record_bytes=b"execution",
        exact_firecracker_output_bytes=b"output",
    )


def _governed_settlement(
    candidate: _SpotV7SettlementCandidateInputV1 | None = None,
) -> _GovernedFirecrackerSpotV7SettlementV1:
    capability = object.__new__(_GovernedFirecrackerSpotV7SettlementV1)
    object.__setattr__(capability, "_candidate", candidate or _candidate())
    object.__setattr__(capability, "_runtime_execution", object())
    object.__setattr__(
        capability,
        "_seal",
        firecracker_authority._GOVERNED_BINDER_SEAL_V1,
    )
    return capability


def _policy(
    *,
    application_id: str | None = None,
    chain_or_domain_id: str | None = None,
    da_policy_root: str | None = None,
    finality_policy_root: str | None = None,
) -> _GovernedSpotV7OperationalPolicyV1:
    candidate = _candidate()
    return _GovernedSpotV7OperationalPolicyV1(
        _GovernedOperationalPolicyProjectionV1(
            application_id=application_id or candidate.application_id,
            chain_or_domain_id=chain_or_domain_id or candidate.chain_or_domain_id,
            full_blob_da_policy_root=da_policy_root or _root(21),
            checkpoint_finality_policy_root=finality_policy_root or _root(22),
        ),
        seal=operational_gate._GOVERNED_OPERATIONAL_POLICY_SEAL_V1,
    )


def _da(
    *,
    application_id: str | None = None,
    chain_or_domain_id: str | None = None,
    epoch_id: int | None = None,
    certificate_root: str | None = None,
    data_root: str | None = None,
    policy_root: str | None = None,
) -> _GovernedLocalFullBlobPolicySatisfactionV1:
    candidate = _candidate()
    certificate_epoch = candidate.epoch_id if epoch_id is None else epoch_id
    return _GovernedLocalFullBlobPolicySatisfactionV1(
        _GovernedFullBlobPolicyProjectionV1(
            application_id=application_id or candidate.application_id,
            chain_or_domain_id=chain_or_domain_id or candidate.chain_or_domain_id,
            epoch_id=certificate_epoch,
            certificate_root=certificate_root or candidate.data_availability_certificate_root,
            data_root=data_root or candidate.data_root,
            policy_root=policy_root or _root(21),
            exact_blob_sha256=_root(23),
            checked_epoch=certificate_epoch,
            retention_through_epoch=certificate_epoch + 100,
        ),
        seal=operational_gate._GOVERNED_FULL_BLOB_POLICY_SEAL_V1,
    )


def _finality(
    *,
    application_id: str | None = None,
    chain_or_domain_id: str | None = None,
    epoch_id: int | None = None,
    proof_journal_hash: str | None = None,
    post_state_root: str | None = None,
    policy_root: str | None = None,
) -> _AuthenticatedCheckpointFinalityTransitionV2:
    candidate = _candidate()
    journal_hash = "0x" + hashlib.sha256(candidate.exact_v7_journal_bytes).hexdigest()
    return _AuthenticatedCheckpointFinalityTransitionV2(
        _AuthenticatedCheckpointFinalityProjectionV2(
            application_id=application_id or candidate.application_id,
            chain_or_domain_id=chain_or_domain_id or candidate.chain_or_domain_id,
            epoch_id=candidate.epoch_id if epoch_id is None else epoch_id,
            proof_journal_hash=proof_journal_hash or journal_hash,
            post_state_root=post_state_root or candidate.post_state_root,
            policy_root=policy_root or _root(22),
            certificate_root=_root(24),
            finality_evidence_root=_root(25),
            prior_application_checkpoint_sequence=40,
            prior_application_checkpoint_hash=_root(26),
            next_application_checkpoint_sequence=41,
            next_application_checkpoint_hash=_root(27),
        ),
        seal=operational_gate._AUTHENTICATED_CHECKPOINT_FINALITY_SEAL_V2,
    )


def test_operational_frontier_names_every_unclosed_authority_condition() -> None:
    assert SPOT_V7_OPERATIONAL_COMMIT_MISSING_CONDITIONS_V1 == (
        SpotV7OperationalCommitMissingConditionV1.GOVERNED_V7_SETTLEMENT_CAPABILITY,
        SpotV7OperationalCommitMissingConditionV1.GOVERNED_OPERATIONAL_POLICY,
        SpotV7OperationalCommitMissingConditionV1.EXACT_FULL_BLOB_POLICY_CHECK,
        SpotV7OperationalCommitMissingConditionV1.AUTHENTICATED_EXTERNAL_FINALITY,
        SpotV7OperationalCommitMissingConditionV1.EXACT_CHECKPOINT_FINALITY_V2_CHECK,
    )


@pytest.mark.parametrize(
    ("component", "replacement", "code"),
    (
        ("policy_application", _root(101), "policy_application"),
        ("policy_domain", _root(102), "policy_domain"),
        ("da_application", _root(103), "da_application"),
        ("da_domain", _root(104), "da_domain"),
        ("da_epoch", 10, "da_epoch"),
        ("da_certificate", _root(105), "da_certificate_root"),
        ("da_data", _root(106), "da_data_root"),
        ("da_policy", _root(107), "da_policy_root"),
        ("finality_application", _root(108), "finality_application"),
        ("finality_domain", _root(109), "finality_domain"),
        ("finality_epoch", 10, "finality_epoch"),
        ("finality_journal", _root(110), "finality_proof_journal"),
        ("finality_post", _root(111), "finality_post_state"),
        ("finality_policy", _root(112), "finality_policy_root"),
    ),
)
def test_structure_preserving_cross_binding_mutations_reject(
    component: str,
    replacement: str | int,
    code: str,
) -> None:
    settlement = _governed_settlement()
    policy = _policy(
        application_id=(str(replacement) if component == "policy_application" else None),
        chain_or_domain_id=(str(replacement) if component == "policy_domain" else None),
    )
    da = _da(
        application_id=(str(replacement) if component == "da_application" else None),
        chain_or_domain_id=(str(replacement) if component == "da_domain" else None),
        epoch_id=(int(replacement) if component == "da_epoch" else None),
        certificate_root=(str(replacement) if component == "da_certificate" else None),
        data_root=(str(replacement) if component == "da_data" else None),
        policy_root=(str(replacement) if component == "da_policy" else None),
    )
    finality = _finality(
        application_id=(str(replacement) if component == "finality_application" else None),
        chain_or_domain_id=(str(replacement) if component == "finality_domain" else None),
        epoch_id=(int(replacement) if component == "finality_epoch" else None),
        proof_journal_hash=(str(replacement) if component == "finality_journal" else None),
        post_state_root=(str(replacement) if component == "finality_post" else None),
        policy_root=(str(replacement) if component == "finality_policy" else None),
    )

    with pytest.raises(SpotV7OperationalGateBindingErrorV1) as captured:
        _validate_spot_v7_operational_gate_inputs_v1(
            settlement=settlement,
            policy=policy,
            data_availability=da,
            finality=finality,
        )

    assert captured.value.code == code


def test_exact_cross_binding_is_checked_before_unavailable_authority_reject() -> None:
    settlement = _governed_settlement()
    candidate = _validate_spot_v7_operational_gate_inputs_v1(
        settlement=settlement,
        policy=_policy(),
        data_availability=_da(),
        finality=_finality(),
    )

    assert candidate is settlement._candidate_for_atomic_store()
    with pytest.raises(SpotV7OperationalCommitAuthorityUnavailableV1) as captured:
        _bind_spot_v7_operational_commit_capability_v1(
            settlement=settlement,
            policy=_policy(),
            data_availability=_da(),
            finality=_finality(),
        )
    assert captured.value.missing_conditions == (
        SPOT_V7_OPERATIONAL_COMMIT_MISSING_CONDITIONS_V1
    )


@pytest.mark.parametrize(
    "untrusted",
    (
        True,
        {"local_full_blob_policy_satisfied": True},
        {"external_finality_verified": True},
        {"settlement_authority": True},
        object(),
    ),
)
def test_caller_booleans_and_reports_cannot_cross_the_gate(untrusted: object) -> None:
    with pytest.raises(TypeError):
        _validate_spot_v7_operational_gate_inputs_v1(
            settlement=untrusted,
            policy=untrusted,
            data_availability=untrusted,
            finality=untrusted,
        )


def test_atomic_commit_capability_has_no_current_mint_path() -> None:
    source = inspect.getsource(_bind_spot_v7_operational_commit_capability_v1)

    assert "_validate_spot_v7_operational_gate_inputs_v1(" in source
    assert "_require_spot_v7_operational_commit_authority_available_v1()" in source
    assert "_SpotV7AtomicEconomicCommitCapabilityV1(" not in source
    forged = object.__new__(_SpotV7AtomicEconomicCommitCapabilityV1)
    for operation in (copy.copy, copy.deepcopy, pickle.dumps):
        with pytest.raises(TypeError):
            operation(forged)


def test_store_rejects_governed_v7_capability_at_operational_gate_before_sqlite() -> None:
    store = object.__new__(SQLiteSpotV7AtomicSettlementStoreV1)
    settlement = _governed_settlement()
    cursor = SpotV7AtomicSettlementCursorV1(0, _root(11), 0, 4, None)

    with pytest.raises(SpotV7OperationalCommitAuthorityUnavailableV1):
        store._commit_governed_firecracker_capability(
            expected_cursor=cursor,
            capability=settlement,
        )

    assert store.operational_commit_gate_available is False
