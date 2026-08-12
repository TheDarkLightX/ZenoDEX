from __future__ import annotations

import ast
from collections.abc import MutableMapping
from dataclasses import fields, replace
from pathlib import Path
from typing import cast

import pytest

import src.core.m6_safe_mount_transition_v1 as m6_transition
import src.core.m6_safe_mount_types_v1 as m6_types
from src.core.m6_authority_evidence_v1 import (
    _issue_m6_authority_verification_receipt_v1,
    _issue_m6_execution_context_verification_receipt_v1,
    _issue_m6_finality_verification_receipt_v1,
    verify_authenticated_execution_context_v1,
    verify_migration_evidence_v1,
    verify_tau_escrow_deposit_evidence_v1,
    verify_tau_withdrawal_ack_evidence_v1,
)
from src.core.m6_safe_mount_transition_v1 import _BUSINESS_HANDLERS
from src.core.m6_safe_mount_v1 import (
    LAUNCH_COMMANDS_V1,
    M6_RESEARCH_DISABLED_COMMANDS_V1,
    M6_RESEARCH_ENABLED_COMMANDS_V1,
    MAX_ATOMS_V1,
    MAX_DURABILITY_PROFILE_CHAIN_BLOCKS_V1,
    MAX_DURABILITY_PROFILE_JSON_BYTES_V1,
    ZERO_ROOT_V1,
    ZRPF_COMMAND_COUNT_V1,
    AcceptCandidateV1,
    AdmissionRejectReasonV1,
    AuthenticatedExecutionContextV1,
    BusinessRejectReasonV1,
    BusinessStatusV1,
    EconomicAtomKindV1,
    EconomicAtomV1,
    EscrowAtomV1,
    FinalityModeV1,
    FreshnessBoundsV1,
    GlobalCommandKindV1,
    GlobalCommandV1,
    M6ApplicationStateV1,
    M6AuthorityEvidenceV1,
    M6DurabilityProfileV1,
    M6ExecutionContextClaimsV1,
    M6PromotionSubjectV1,
    MigrationAuthorityProofV1,
    MigrationEvidenceKindV1,
    MigrationPhaseV1,
    MigrationStateV1,
    OracleContextV1,
    PublicationAtomV1,
    RejectNoCommitV1,
    TauBatchCertificateV1,
    TauEscrowDepositProofV1,
    TauFinalityBoundDepositWitnessV1,
    ValueDeltaCertificateV1,
    ValueDeltaEntryV1,
    VerifiedZenoLedgerFinalityV1,
    WithdrawalAcknowledgmentV1,
    ZenoLedgerFinalityCertificateV1,
    ZRPFBatchCandidateV1,
    admit_global_command_v1,
    canonical_bytes_v1,
    decode_global_command_v1,
    degrade_to_direct_v1,
    execute_direct_batch_v1,
    execute_zrpf_batch_v1,
    hash_v1,
    initial_application_state_v1,
    m6_chain_id_root_from_external_v1,
    ordered_root_v1,
    run_m6_transition_v1,
    validate_economic_state_v1,
    validate_state_commitments_v1,
    verify_zrpf_root_v1,
)
from src.core.m6_safe_mount_v1 import (
    verify_zeno_ledger_finality_v1 as _verify_zeno_ledger_finality_v1,
)
from src.core.m6_zrpf_v1 import (
    DirectBatchCandidateV1,
    _issue_m6_zrpf_verification_receipt_v1,
    verify_zrpf_structure_v1,
)
from src.integration.m6_commit_port_v1 import CommitStatusV1, M6CommitPortV1


def _root(value: int) -> str:
    return f"0x{value:064x}"


@pytest.fixture()
def subject() -> M6PromotionSubjectV1:
    return M6PromotionSubjectV1(
        source=_root(1),
        proof=_root(2),
        build=_root(3),
        schema=_root(4),
        deployment=_root(5),
        chain_id=_root(11),
        verifier=_root(6),
        tau_profile=_root(7),
        validator_set=_root(8),
        writer_epoch=0,
        managed_asset_policy=_root(9),
        risc0_image=_root(10),
        destination_adapter_roots=(),
    )


def _state(subject: M6PromotionSubjectV1, *, alice_atoms: int = 0) -> M6ApplicationStateV1:
    state = initial_application_state_v1(subject)
    if alice_atoms == 0:
        return state
    return replace(
        state,
        economic_atoms=(
            EconomicAtomV1(EconomicAtomKindV1.BALANCE, "alice", "A", "ledger", alice_atoms),
            EconomicAtomV1(EconomicAtomKindV1.BALANCE, "pool", "A", "ledger", 100),
            EconomicAtomV1(EconomicAtomKindV1.BALANCE, "pool", "B", "ledger", 65),
        ),
    )


def test_launch_command_registry_key_set_matches_business_handler_registry() -> None:
    """Tier 0: every declared launch command has one business-handler key."""

    expected_values = frozenset(
        {
            "spot_swap",
            "lp_add",
            "lp_remove",
            "zusd_borrow",
            "zusd_repay",
            "zusd_redeem",
            "zusd_liquidate",
            "stability_pool_deposit",
            "stability_pool_withdraw",
            "zusd_redistribute",
            "perp_open",
            "perp_close",
            "perp_funding",
            "perp_liquidate",
            "oracle_submit",
            "oracle_dispute",
            "protocol_buy_and_burn",
            "zrpf_prover_reward",
            "seller_auction_commit",
            "seller_auction_reveal",
            "seller_auction_settle",
            "seller_auction_cancel",
            "seller_auction_expire",
            "private_swap_commit",
            "private_swap_reveal",
            "private_swap_settle",
            "private_swap_cancel",
            "private_swap_expire",
            "tau_escrow_deposit",
            "tau_withdrawal",
            "tau_withdrawal_ack",
            "fallback_activate",
            "tau_rejoin",
        }
    )
    assert {kind.value for kind in GlobalCommandKindV1} == expected_values
    assert {kind.value for kind in LAUNCH_COMMANDS_V1} == expected_values
    assert set(_BUSINESS_HANDLERS) == set(LAUNCH_COMMANDS_V1)
    assert M6_RESEARCH_DISABLED_COMMANDS_V1 == frozenset(
        {
            GlobalCommandKindV1.ZUSD_LIQUIDATE,
            GlobalCommandKindV1.ZUSD_REDISTRIBUTE,
            GlobalCommandKindV1.PERP_FUNDING,
            GlobalCommandKindV1.PERP_LIQUIDATE,
            GlobalCommandKindV1.ORACLE_SUBMIT,
            GlobalCommandKindV1.ORACLE_DISPUTE,
            GlobalCommandKindV1.PROTOCOL_BUY_AND_BURN,
            GlobalCommandKindV1.ZRPF_PROVER_REWARD,
        }
    )
    assert M6_RESEARCH_DISABLED_COMMANDS_V1 <= LAUNCH_COMMANDS_V1
    assert M6_RESEARCH_ENABLED_COMMANDS_V1 == LAUNCH_COMMANDS_V1 - M6_RESEARCH_DISABLED_COMMANDS_V1
    assert not M6_RESEARCH_DISABLED_COMMANDS_V1 & M6_RESEARCH_ENABLED_COMMANDS_V1


def test_durability_profile_is_canonical_and_subject_bound(subject: M6PromotionSubjectV1) -> None:
    profile = subject.durability_profile
    assert canonical_bytes_v1(profile) == canonical_bytes_v1(profile.to_canonical())
    altered_profile = replace(profile, max_chain_blocks=profile.max_chain_blocks - 1)
    assert altered_profile.profile_root != profile.profile_root
    assert replace(subject, durability_profile=altered_profile).subject_root != subject.subject_root

    with pytest.raises(ValueError, match="must be positive"):
        M6DurabilityProfileV1(max_json_bytes=0, max_chain_blocks=1)
    M6DurabilityProfileV1(
        max_json_bytes=MAX_DURABILITY_PROFILE_JSON_BYTES_V1,
        max_chain_blocks=MAX_DURABILITY_PROFILE_CHAIN_BLOCKS_V1,
    )
    with pytest.raises(ValueError, match="profile ceiling"):
        M6DurabilityProfileV1(
            max_json_bytes=MAX_DURABILITY_PROFILE_JSON_BYTES_V1 + 1,
            max_chain_blocks=1,
        )
    with pytest.raises(ValueError, match="profile ceiling"):
        M6DurabilityProfileV1(
            max_json_bytes=1,
            max_chain_blocks=MAX_DURABILITY_PROFILE_CHAIN_BLOCKS_V1 + 1,
        )


class _TestExecutionContextVerifier:
    """Test ingress verifier; production authentication remains an external port."""

    def verify_execution_context(
        self,
        claims: M6ExecutionContextClaimsV1,
    ):
        assert claims.authentication_root
        return _issue_m6_execution_context_verification_receipt_v1(
            claims,
            attestation_root=claims.authentication_root,
        )


_TEST_EXECUTION_CONTEXT_VERIFIER = _TestExecutionContextVerifier()


class _TestZRPFReceiptVerifier:
    """Research fixture for the explicit proof-verifier adapter boundary."""

    def verify_zrpf_receipt(self, subject, batch, journal):
        return _issue_m6_zrpf_verification_receipt_v1(
            promotion_subject_root=subject.subject_root,
            profile=journal.profile,
            verifier_image=journal.verifier_image,
            journal_root=journal.journal_root,
            data_availability_root=journal.data_availability_root,
            attestation_root=hash_v1(
                "test-m6-zrpf-attestation-v1",
                {"candidate_id": batch.candidate_id, "journal_root": journal.journal_root},
            ),
        )


_TEST_ZRPF_RECEIPT_VERIFIER = _TestZRPFReceiptVerifier()


def _context(
    subject: M6PromotionSubjectV1,
    state: M6ApplicationStateV1,
    nonce: int,
    *,
    sender: str = "alice",
    ledger_height: int = 0,
    oracle_age: int = 0,
    parent_head: str | None = None,
    authority_evidence: M6AuthorityEvidenceV1 | None = None,
    freshness_bounds: FreshnessBoundsV1 | None = None,
) -> AuthenticatedExecutionContextV1:
    return verify_authenticated_execution_context_v1(
        deployment=subject.deployment,
        chain_id=subject.chain_id,
        parent_head=state.head if parent_head is None else parent_head,
        epoch=state.writer_epoch,
        sender=sender,
        nonce=nonce,
        oracle_context=OracleContextV1(
            _root(100),
            observed_height=ledger_height,
            oracle_height=max(0, ledger_height - oracle_age),
        ),
        tau_profile=subject.tau_profile,
        verifier_registry=subject.verifier,
        freshness_bounds=(
            FreshnessBoundsV1(2, 2, 2)
            if freshness_bounds is None
            else freshness_bounds
        ),
        ledger_height=ledger_height,
        authority_evidence=authority_evidence,
        verifier=_TEST_EXECUTION_CONTEXT_VERIFIER,
    )


def test_noop_execution_verifier_cannot_issue_an_authenticated_context(
    subject: M6PromotionSubjectV1,
) -> None:
    """A verifier returning no receipt must fail before a transition can run."""

    class NoOpVerifier:
        def verify_execution_context(self, claims: M6ExecutionContextClaimsV1):
            del claims
            return None

    with pytest.raises(TypeError, match="did not return a typed receipt"):
        verify_authenticated_execution_context_v1(
            deployment=subject.deployment,
            chain_id=subject.chain_id,
            parent_head=ZERO_ROOT_V1,
            epoch=0,
            sender="alice",
            nonce=1,
            oracle_context=OracleContextV1(_root(100), observed_height=0, oracle_height=0),
            tau_profile=subject.tau_profile,
            verifier_registry=subject.verifier,
            freshness_bounds=FreshnessBoundsV1(0, 0, 0),
            verifier=NoOpVerifier(),
        )


def _command(kind: GlobalCommandKindV1, sequence_nonce: int, **payload: str | int) -> GlobalCommandV1:
    return GlobalCommandV1(
        kind=kind,
        command_id=_root(1_000 + sequence_nonce),
        sender="alice",
        nonce=sequence_nonce,
        payload=payload,
    )


def _command_for(
    kind: GlobalCommandKindV1,
    sender: str,
    sequence_nonce: int,
    command_id: int,
    **payload: str | int,
) -> GlobalCommandV1:
    created_height = int(payload.pop("created_height", 0))
    return GlobalCommandV1(
        kind=kind,
        command_id=_root(command_id),
        sender=sender,
        nonce=sequence_nonce,
        payload=payload,
        created_height=created_height,
    )


def _context_for(
    subject: M6PromotionSubjectV1,
    state: M6ApplicationStateV1,
    sender: str,
    nonce: int,
    ledger_height: int,
) -> AuthenticatedExecutionContextV1:
    return _context(subject, state, nonce, sender=sender, ledger_height=ledger_height)


class _TestAuthorityVerifier:
    """AAA fixture: cryptographic/external checks are injected at this port."""

    def verify_tau_finality_bound_deposit(
        self,
        witness: TauFinalityBoundDepositWitnessV1,
        **kwargs: object,
    ):
        return self.verify_tau_escrow_deposit(witness, **kwargs)

    def verify_tau_escrow_deposit(
        self,
        proof: TauEscrowDepositProofV1,
        **kwargs: object,
    ):
        return _issue_m6_authority_verification_receipt_v1(
            kind=GlobalCommandKindV1.TAU_ESCROW_DEPOSIT,
            subject_root=cast(str, kwargs["expected_subject_root"]),
            pre_state_root=cast(str, kwargs["expected_pre_state_root"]),
            command_hash=cast(str, kwargs["expected_command_hash"]),
            evidence_root=proof.proof_root,
            attestation_root=proof.tau_finality_root,
        )

    def verify_tau_withdrawal_ack(
        self,
        acknowledgment: WithdrawalAcknowledgmentV1,
        **kwargs: object,
    ):
        return _issue_m6_authority_verification_receipt_v1(
            kind=GlobalCommandKindV1.TAU_WITHDRAWAL_ACK,
            subject_root=cast(str, kwargs["expected_subject_root"]),
            pre_state_root=cast(str, kwargs["expected_pre_state_root"]),
            command_hash=cast(str, kwargs["expected_command_hash"]),
            evidence_root=acknowledgment.acknowledgment_root,
            attestation_root=acknowledgment.tau_receipt_root,
        )

    def verify_migration(
        self,
        proof: MigrationAuthorityProofV1,
        **kwargs: object,
    ):
        return _issue_m6_authority_verification_receipt_v1(
            kind=(
                GlobalCommandKindV1.FALLBACK_ACTIVATE
                if proof.kind is MigrationEvidenceKindV1.FALLBACK_LIVENESS
                else GlobalCommandKindV1.TAU_REJOIN
            ),
            subject_root=cast(str, kwargs["expected_subject_root"]),
            pre_state_root=cast(str, kwargs["expected_pre_state_root"]),
            command_hash=cast(str, kwargs["expected_command_hash"]),
            evidence_root=hash_v1("m6-migration-authority-proof-v1", proof.to_canonical()),
            attestation_root=proof.condition_root,
        )


_TEST_AUTHORITY_VERIFIER = _TestAuthorityVerifier()


def _payload(
    command: GlobalCommandV1,
    key: str,
    default: str | int | None = None,
) -> str | int:
    value = command.payload_value(key, default)
    if value is None:
        raise ValueError(f"missing test command payload field: {key}")
    return cast(str | int, value)


def _with_deposit_evidence(
    subject: M6PromotionSubjectV1,
    state: M6ApplicationStateV1,
    command: GlobalCommandV1,
    *,
    ledger_height: int = 0,
    freshness_bounds: FreshnessBoundsV1 | None = None,
) -> AuthenticatedExecutionContextV1:
    proof = TauEscrowDepositProofV1(
        deposit_id=cast(str, _payload(command, "deposit_id")),
        tau_transaction_root=cast(str, _payload(command, "tau_transaction_root")),
        tau_finality_root=cast(str, _payload(command, "tau_finality_root")),
        tau_profile_root=cast(str, _payload(command, "tau_profile_root")),
        beneficiary=command.sender,
        asset=cast(str, _payload(command, "asset")),
        amount_atoms=cast(int, _payload(command, "amount_atoms")),
        tau_finality_height=cast(int, _payload(command, "tau_finality_height", 0)),
    )
    evidence = verify_tau_escrow_deposit_evidence_v1(
        command,
        proof,
        subject_root=subject.subject_root,
        pre_state_root=state.state_root,
        tau_profile_root=subject.tau_profile,
        verifier=_TEST_AUTHORITY_VERIFIER,
    )
    return _context(
        subject,
        state,
        command.nonce,
        sender=command.sender,
        authority_evidence=evidence,
        ledger_height=ledger_height,
        freshness_bounds=freshness_bounds,
    )


def _with_ack_evidence(
    subject: M6PromotionSubjectV1,
    state: M6ApplicationStateV1,
    command: GlobalCommandV1,
    provenance_root: str,
) -> AuthenticatedExecutionContextV1:
    acknowledgment = WithdrawalAcknowledgmentV1(
        withdrawal_id=cast(str, _payload(command, "withdrawal_id")),
        provenance_root=provenance_root,
        tau_receipt_root=cast(str, _payload(command, "tau_receipt_root")),
        acknowledged_state_root=cast(str, _payload(command, "ack_root")),
        tau_receipt_height=cast(int, _payload(command, "tau_receipt_height", 0)),
    )
    evidence = verify_tau_withdrawal_ack_evidence_v1(
        command,
        acknowledgment,
        subject_root=subject.subject_root,
        pre_state_root=state.state_root,
        expected_provenance_root=provenance_root,
        verifier=_TEST_AUTHORITY_VERIFIER,
    )
    return _context(
        subject,
        state,
        command.nonce,
        sender=command.sender,
        authority_evidence=evidence,
    )


def _with_migration_evidence(
    subject: M6PromotionSubjectV1,
    state: M6ApplicationStateV1,
    command: GlobalCommandV1,
) -> AuthenticatedExecutionContextV1:
    if command.kind is GlobalCommandKindV1.FALLBACK_ACTIVATE:
        kind = MigrationEvidenceKindV1.FALLBACK_LIVENESS
        compatible_profile_root = ZERO_ROOT_V1
    else:
        kind = MigrationEvidenceKindV1.TAU_REJOIN_CATCHUP
        compatible_profile_root = subject.tau_profile
    proof = MigrationAuthorityProofV1(
        kind=kind,
        checkpoint_root=cast(str, _payload(command, "checkpoint_root")),
        compatible_profile_root=compatible_profile_root,
        condition_root=_root(706),
        source_authority_epoch=state.migration.authority_epoch,
    )
    evidence = verify_migration_evidence_v1(
        command,
        proof,
        subject_root=subject.subject_root,
        pre_state_root=state.state_root,
        source_authority_epoch=state.migration.authority_epoch,
        tau_profile_root=subject.tau_profile,
        verifier=_TEST_AUTHORITY_VERIFIER,
    )
    return _context(
        subject,
        state,
        command.nonce,
        sender=command.sender,
        authority_evidence=evidence,
    )


_DISPATCH_PROBE_PAYLOADS_V1: dict[GlobalCommandKindV1, dict[str, str | int]] = {
    GlobalCommandKindV1.SPOT_SWAP: {
        "asset_in": "A",
        "asset_out": "B",
        "amount_in_atoms": 1,
        "amount_out_atoms": 1,
        "pool": "pool",
    },
    GlobalCommandKindV1.LP_ADD: {
        "asset": "A",
        "amount_atoms": 1,
        "pool": "pool",
        "lp_shares_atoms": 1,
    },
    GlobalCommandKindV1.LP_REMOVE: {
        "asset": "A",
        "amount_atoms": 1,
        "pool": "pool",
        "lp_shares_atoms": 1,
    },
    GlobalCommandKindV1.ZUSD_BORROW: {
        "collateral_asset": "A",
        "collateral_atoms": 1,
        "amount_atoms": 1,
        "vault_id": "vault-1",
    },
    GlobalCommandKindV1.ZUSD_REPAY: {"amount_atoms": 1, "vault_id": "vault-1"},
    GlobalCommandKindV1.ZUSD_REDEEM: {
        "amount_atoms": 1,
        "collateral_asset": "A",
        "vault_id": "vault-1",
    },
    GlobalCommandKindV1.ZUSD_LIQUIDATE: {
        "vault_id": "vault-1",
        "debtor": "bob",
        "debt_atoms": 1,
        "collateral_asset": "A",
        "collateral_atoms": 1,
    },
    GlobalCommandKindV1.STABILITY_POOL_DEPOSIT: {"amount_atoms": 1},
    GlobalCommandKindV1.STABILITY_POOL_WITHDRAW: {"amount_atoms": 1},
    GlobalCommandKindV1.ZUSD_REDISTRIBUTE: {
        "amount_atoms": 1,
        "collateral_asset": "A",
        "collateral_atoms": 1,
        "source_vault": "vault-1",
    },
    GlobalCommandKindV1.PERP_OPEN: {
        "market": "BTC",
        "margin_atoms": 1,
        "size_atoms": 1,
        "price_e8": 1,
    },
    GlobalCommandKindV1.PERP_CLOSE: {"market": "BTC", "size_atoms": 1, "pnl_atoms": 0},
    GlobalCommandKindV1.PERP_FUNDING: {"market": "BTC", "amount_atoms": 1},
    GlobalCommandKindV1.PERP_LIQUIDATE: {
        "market": "BTC",
        "margin_atoms": 1,
        "insurance_atoms": 1,
    },
    GlobalCommandKindV1.ORACLE_SUBMIT: {
        "oracle_id": "btc-usd",
        "price_e8": 1,
        "bond_atoms": 1,
    },
    GlobalCommandKindV1.ORACLE_DISPUTE: {"oracle_id": "btc-usd", "bond_atoms": 1},
    GlobalCommandKindV1.PROTOCOL_BUY_AND_BURN: {"asset": "A", "amount_atoms": 1},
    GlobalCommandKindV1.ZRPF_PROVER_REWARD: {
        "prover": "prover-1",
        "reward_asset": "A",
        "amount_atoms": 1,
    },
    GlobalCommandKindV1.SELLER_AUCTION_COMMIT: {
        "auction_id": "auction-1",
        "bond_asset": "USD",
        "bond_atoms": 1,
        "commitment": _root(801),
        "commit_height": 10,
        "reveal_deadline_height": 20,
        "settle_deadline_height": 30,
    },
    GlobalCommandKindV1.SELLER_AUCTION_REVEAL: {
        "auction_id": "auction-1",
        "inventory_asset": "ITEM",
        "quantity_atoms": 1,
        "price_e8": 1,
        "nonce": 7,
    },
    GlobalCommandKindV1.SELLER_AUCTION_SETTLE: {"auction_id": "auction-1", "clearing_price_e8": 1},
    GlobalCommandKindV1.SELLER_AUCTION_CANCEL: {"auction_id": "auction-1"},
    GlobalCommandKindV1.SELLER_AUCTION_EXPIRE: {"auction_id": "auction-1"},
    GlobalCommandKindV1.PRIVATE_SWAP_COMMIT: {
        "batch_id": "batch-1",
        "bond_asset": "USD",
        "bond_atoms": 1,
        "commitment": _root(802),
        "commit_height": 10,
        "reveal_deadline_height": 20,
        "settle_deadline_height": 30,
    },
    GlobalCommandKindV1.PRIVATE_SWAP_REVEAL: {
        "batch_id": "batch-1",
        "asset_in": "A",
        "amount_in_atoms": 1,
        "asset_out": "B",
        "amount_out_atoms": 1,
        "nonce": 7,
    },
    GlobalCommandKindV1.PRIVATE_SWAP_SETTLE: {"batch_id": "batch-1", "clearing_root": _root(803)},
    GlobalCommandKindV1.PRIVATE_SWAP_CANCEL: {"batch_id": "batch-1"},
    GlobalCommandKindV1.PRIVATE_SWAP_EXPIRE: {"batch_id": "batch-1"},
    GlobalCommandKindV1.TAU_ESCROW_DEPOSIT: {
        "deposit_id": "dispatch-probe-deposit",
        "asset": "A",
        "amount_atoms": 1,
        "tau_transaction_root": _root(804),
        "tau_finality_root": _root(805),
        "tau_profile_root": _root(806),
    },
    GlobalCommandKindV1.TAU_WITHDRAWAL: {
        "withdrawal_id": "dispatch-probe-withdrawal",
        "asset": "A",
        "amount_atoms": 1,
        "destination": "tau-alice",
    },
    GlobalCommandKindV1.TAU_WITHDRAWAL_ACK: {
        "withdrawal_id": "missing-dispatch-probe-withdrawal",
        "ack_root": _root(807),
        "tau_receipt_root": _root(808),
    },
    GlobalCommandKindV1.FALLBACK_ACTIVATE: {"checkpoint_root": _root(809)},
    GlobalCommandKindV1.TAU_REJOIN: {
        "checkpoint_root": _root(810),
        "compatible_profile_root": _root(811),
    },
}


_DISPATCH_PROBE_EXPECTED_REJECT_REASONS_V1: dict[
    GlobalCommandKindV1, BusinessRejectReasonV1
] = {
    GlobalCommandKindV1.SPOT_SWAP: BusinessRejectReasonV1.INSUFFICIENT_RESERVE,
    GlobalCommandKindV1.LP_ADD: BusinessRejectReasonV1.INSUFFICIENT_BALANCE,
    GlobalCommandKindV1.LP_REMOVE: BusinessRejectReasonV1.INVALID_AMOUNT,
    GlobalCommandKindV1.ZUSD_BORROW: BusinessRejectReasonV1.INSUFFICIENT_BALANCE,
    GlobalCommandKindV1.ZUSD_REPAY: BusinessRejectReasonV1.INSUFFICIENT_BALANCE,
    GlobalCommandKindV1.ZUSD_REDEEM: BusinessRejectReasonV1.INSUFFICIENT_BALANCE,
    GlobalCommandKindV1.ZUSD_LIQUIDATE: BusinessRejectReasonV1.UNSUPPORTED_OPERATION,
    GlobalCommandKindV1.STABILITY_POOL_DEPOSIT: BusinessRejectReasonV1.INSUFFICIENT_BALANCE,
    GlobalCommandKindV1.STABILITY_POOL_WITHDRAW: BusinessRejectReasonV1.INSUFFICIENT_BALANCE,
    GlobalCommandKindV1.ZUSD_REDISTRIBUTE: BusinessRejectReasonV1.UNSUPPORTED_OPERATION,
    GlobalCommandKindV1.PERP_OPEN: BusinessRejectReasonV1.INSUFFICIENT_BALANCE,
    GlobalCommandKindV1.PERP_CLOSE: BusinessRejectReasonV1.INVALID_AMOUNT,
    GlobalCommandKindV1.PERP_FUNDING: BusinessRejectReasonV1.UNSUPPORTED_OPERATION,
    GlobalCommandKindV1.PERP_LIQUIDATE: BusinessRejectReasonV1.UNSUPPORTED_OPERATION,
    GlobalCommandKindV1.ORACLE_SUBMIT: BusinessRejectReasonV1.UNSUPPORTED_OPERATION,
    GlobalCommandKindV1.ORACLE_DISPUTE: BusinessRejectReasonV1.UNSUPPORTED_OPERATION,
    GlobalCommandKindV1.PROTOCOL_BUY_AND_BURN: BusinessRejectReasonV1.UNSUPPORTED_OPERATION,
    GlobalCommandKindV1.ZRPF_PROVER_REWARD: BusinessRejectReasonV1.UNSUPPORTED_OPERATION,
    GlobalCommandKindV1.SELLER_AUCTION_COMMIT: BusinessRejectReasonV1.INVALID_DEADLINE,
    GlobalCommandKindV1.SELLER_AUCTION_REVEAL: BusinessRejectReasonV1.INVALID_COMMITMENT,
    GlobalCommandKindV1.SELLER_AUCTION_SETTLE: BusinessRejectReasonV1.INVALID_PHASE,
    GlobalCommandKindV1.SELLER_AUCTION_CANCEL: BusinessRejectReasonV1.INVALID_PHASE,
    GlobalCommandKindV1.SELLER_AUCTION_EXPIRE: BusinessRejectReasonV1.INVALID_PHASE,
    GlobalCommandKindV1.PRIVATE_SWAP_COMMIT: BusinessRejectReasonV1.INVALID_DEADLINE,
    GlobalCommandKindV1.PRIVATE_SWAP_REVEAL: BusinessRejectReasonV1.INVALID_COMMITMENT,
    GlobalCommandKindV1.PRIVATE_SWAP_SETTLE: BusinessRejectReasonV1.INVALID_PHASE,
    GlobalCommandKindV1.PRIVATE_SWAP_CANCEL: BusinessRejectReasonV1.INVALID_PHASE,
    GlobalCommandKindV1.PRIVATE_SWAP_EXPIRE: BusinessRejectReasonV1.INVALID_PHASE,
    GlobalCommandKindV1.TAU_ESCROW_DEPOSIT: BusinessRejectReasonV1.INVALID_ESCROW,
    GlobalCommandKindV1.TAU_WITHDRAWAL: BusinessRejectReasonV1.INSUFFICIENT_BALANCE,
    GlobalCommandKindV1.TAU_WITHDRAWAL_ACK: BusinessRejectReasonV1.INVALID_WITHDRAWAL,
    GlobalCommandKindV1.FALLBACK_ACTIVATE: BusinessRejectReasonV1.INVALID_AUTHORITY,
    GlobalCommandKindV1.TAU_REJOIN: BusinessRejectReasonV1.INVALID_AUTHORITY,
}


def _dispatch_probe_inputs_v1(
    subject: M6PromotionSubjectV1,
    kind: GlobalCommandKindV1,
) -> tuple[M6ApplicationStateV1, AuthenticatedExecutionContextV1, GlobalCommandV1]:
    """Build one admitted, no-effect business-rejection probe per command kind."""

    state = _state(subject)
    payload = dict(_DISPATCH_PROBE_PAYLOADS_V1[kind])

    if kind is GlobalCommandKindV1.TAU_ESCROW_DEPOSIT:
        payload["tau_profile_root"] = subject.tau_profile
        seed = _command(kind, 1, **payload)
        seeded = run_m6_transition_v1(
            subject,
            state,
            _with_deposit_evidence(subject, state, seed),
            seed,
        )
        assert isinstance(seeded, AcceptCandidateV1)
        assert seeded.business_status is BusinessStatusV1.ACCEPTED
        state = seeded.post_state
        command = _command(kind, 2, **payload)
        return state, _with_deposit_evidence(subject, state, command), command

    if kind is GlobalCommandKindV1.TAU_REJOIN:
        payload["checkpoint_root"] = state.state_root
        payload["compatible_profile_root"] = subject.tau_profile

    command = _command(kind, 1, **payload)
    if kind is GlobalCommandKindV1.TAU_WITHDRAWAL_ACK:
        return state, _with_ack_evidence(subject, state, command, state.state_root), command
    if kind in (GlobalCommandKindV1.FALLBACK_ACTIVATE, GlobalCommandKindV1.TAU_REJOIN):
        return state, _with_migration_evidence(subject, state, command), command
    return state, _context(subject, state, command.nonce), command


_REJECTION_STATE_ALLOWED_CHANGES_V1 = frozenset(
    {
        "head",
        "ingress_nonces",
        "history",
        "nullifiers",
        "history_root_cache",
        "nullifier_root_cache",
    }
)


def _assert_committed_rejection_contract_v1(
    state: M6ApplicationStateV1,
    context: AuthenticatedExecutionContextV1,
    command: GlobalCommandV1,
    result: object,
    expected_reason: BusinessRejectReasonV1,
) -> None:
    assert isinstance(result, AcceptCandidateV1)
    assert result.business_status is BusinessStatusV1.REJECTED_COMMITTED
    assert result.business_reject_reason is expected_reason
    assert result.context == context
    assert result.command == command
    assert result.pre_state_root == state.state_root
    assert result.post_state.head == result.post_state.state_root

    expected_nonces = {item.sender: item.last_nonce for item in state.ingress_nonces}
    expected_nonces[command.sender] = command.nonce
    assert tuple(
        (item.sender, item.last_nonce) for item in result.post_state.ingress_nonces
    ) == tuple(sorted(expected_nonces.items()))

    assert result.post_state.history[:-1] == state.history
    assert result.post_state.nullifiers[:-1] == state.nullifiers
    assert result.post_state.history[-1] == result.history_atom
    assert result.post_state.nullifiers[-1] == result.history_atom.nullifier
    assert result.history_atom.sequence == len(state.history)
    assert result.history_atom.command_hash == command.command_hash
    assert result.history_atom.sender == command.sender
    assert result.history_atom.nonce == command.nonce
    assert result.history_atom.pre_state_root == state.state_root
    assert result.history_atom.post_state_root == result.post_state.state_root
    assert result.history_atom.outcome is BusinessStatusV1.REJECTED_COMMITTED
    assert result.history_atom.nullifier == hash_v1(
        "m6-ingress-nullifier-v1",
        {
            "sender": command.sender,
            "nonce": command.nonce,
            "command_hash": command.command_hash,
            "pre_state_root": state.state_root,
        },
    )

    assert result.value_delta.command_hash == command.command_hash
    assert result.value_delta.pre_state_root == state.state_root
    assert result.value_delta.post_state_root == result.post_state.state_root
    assert result.value_delta.entries == ()
    assert result.history_atom.value_delta_root == result.value_delta.delta_root
    assert result.history_atom.outcome is result.business_status
    assert result.history_atom.business_reject_reason is result.business_reject_reason
    assert result.outbox_atoms == ()

    publication = result.publication_atom
    assert publication.pre_state_root == state.state_root
    assert publication.post_state_root == result.post_state.state_root
    assert publication.history_root == result.post_state.history_root
    assert publication.nullifier_root == result.post_state.nullifier_root
    assert publication.value_delta_root == result.value_delta.delta_root
    assert publication.outbox_root == result.post_state.outbox_root
    assert publication.writer_epoch == result.post_state.writer_epoch
    assert publication.business_status is result.business_status
    assert publication.business_reject_reason is result.business_reject_reason
    assert publication.candidate_id == hash_v1(
        "m6-candidate-id-v1",
        {
            "command_hash": command.command_hash,
            "pre_state_root": state.state_root,
            "post_state_root": result.post_state.state_root,
        },
    )

    for state_field in fields(M6ApplicationStateV1):
        if state_field.name in _REJECTION_STATE_ALLOWED_CHANGES_V1:
            continue
        assert getattr(result.post_state, state_field.name) == getattr(state, state_field.name), state_field.name
    validate_state_commitments_v1(result.post_state)


def test_dispatch_probe_tables_are_exhaustive() -> None:
    assert set(_DISPATCH_PROBE_PAYLOADS_V1) == set(GlobalCommandKindV1)
    assert set(_DISPATCH_PROBE_EXPECTED_REJECT_REASONS_V1) == set(GlobalCommandKindV1)


@pytest.mark.parametrize("kind", tuple(GlobalCommandKindV1), ids=lambda kind: kind.value)
def test_global_command_dispatch_has_exact_committed_rejection_trace(
    subject: M6PromotionSubjectV1,
    kind: GlobalCommandKindV1,
) -> None:
    """Every launch command has an exact, committed, no-effect rejection probe."""

    state, context, command = _dispatch_probe_inputs_v1(subject, kind)
    assert state.get_nonce(command.sender) == command.nonce - 1

    result = run_m6_transition_v1(subject, state, context, command)
    _assert_committed_rejection_contract_v1(
        state,
        context,
        command,
        result,
        _DISPATCH_PROBE_EXPECTED_REJECT_REASONS_V1[kind],
    )

    if kind in (
        GlobalCommandKindV1.SELLER_AUCTION_REVEAL,
        GlobalCommandKindV1.PRIVATE_SWAP_REVEAL,
    ):
        assert command.nonce == 1
        assert _payload(command, "nonce") == 7


def test_business_handler_registry_is_immutable_and_closed() -> None:
    """Architecture conformance: dispatch cannot be rewritten in process."""

    assert set(_BUSINESS_HANDLERS) == set(LAUNCH_COMMANDS_V1)
    with pytest.raises(TypeError):
        cast(dict[GlobalCommandKindV1, object], _BUSINESS_HANDLERS)[
            GlobalCommandKindV1.PROTOCOL_BUY_AND_BURN
        ] = lambda _scratch: None


def test_finality_policy_matrix_is_exhaustive_and_rebinding_safe(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Architecture/BVA: every migration edge has one frozen finality mode."""

    expected = {
        (MigrationPhaseV1.NORMAL, MigrationPhaseV1.NORMAL): FinalityModeV1.TAU_ORDERED,
        (MigrationPhaseV1.NORMAL, MigrationPhaseV1.FALLBACK): FinalityModeV1.FALLBACK_FORCED_INCLUSION,
        (MigrationPhaseV1.FALLBACK, MigrationPhaseV1.FALLBACK): FinalityModeV1.FALLBACK_FORCED_INCLUSION,
        (MigrationPhaseV1.FALLBACK, MigrationPhaseV1.NORMAL): FinalityModeV1.FALLBACK_FORCED_INCLUSION,
    }
    table = m6_transition._FINALITY_MODE_BY_MIGRATION_EDGE_V1

    # Assert: all 4 x 4 phase edges are classified, including the six
    # unreachable/research-only phases that must fail closed.
    assert dict(table) == expected
    for pre_phase in MigrationPhaseV1:
        for post_phase in MigrationPhaseV1:
            assert table.get((pre_phase, post_phase)) is expected.get((pre_phase, post_phase))

    # Act: a same-process adapter attempts to replace the policy surfaces.
    hostile_mutable_view = cast(
        MutableMapping[tuple[MigrationPhaseV1, MigrationPhaseV1], FinalityModeV1],
        table,
    )
    with pytest.raises(TypeError):
        hostile_mutable_view[(MigrationPhaseV1.NORMAL, MigrationPhaseV1.NORMAL)] = (
            FinalityModeV1.FALLBACK_FORCED_INCLUSION
        )
    monkeypatch.setattr(m6_transition, "_FINALITY_MODE_BY_MIGRATION_EDGE_V1", {})

    # Assert: the transition helper captured the original immutable table.
    for pre_phase in MigrationPhaseV1:
        for post_phase in MigrationPhaseV1:
            assert m6_transition.expected_finality_mode_v1(pre_phase, post_phase) is expected.get(
                (pre_phase, post_phase)
            )


@pytest.mark.parametrize(
    "kind",
    tuple(sorted(M6_RESEARCH_DISABLED_COMMANDS_V1, key=lambda item: item.value)),
    ids=lambda kind: kind.value,
)
def test_every_research_disabled_value_writer_is_a_typed_no_effect_failure(
    subject: M6PromotionSubjectV1,
    kind: GlobalCommandKindV1,
) -> None:
    """AAA/BVA: every incomplete authority path remains closed in the profile."""

    # Arrange: use the exhaustive well-formed dispatch probe for this command.
    state, context, command = _dispatch_probe_inputs_v1(subject, kind)

    # Act: admit the authenticated command at the exact business boundary.
    result = run_m6_transition_v1(subject, state, context, command)

    # Assert: the command consumes its ingress identity, while no economic or
    # external effect can be selected without the missing policy witness.
    _assert_committed_rejection_contract_v1(
        state,
        context,
        command,
        result,
        BusinessRejectReasonV1.UNSUPPORTED_OPERATION,
    )
    assert isinstance(result, AcceptCandidateV1)
    assert result.post_state.economic_atoms == state.economic_atoms
    assert result.post_state.outbox == state.outbox


def test_disabled_partition_precedes_rebound_handler_lookup(
    subject: M6PromotionSubjectV1,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Mutation killer: rebinding a disabled handler cannot enable it."""

    state = _state(subject)
    command = _command(
        GlobalCommandKindV1.PROTOCOL_BUY_AND_BURN,
        1,
        asset="PROTO",
        amount_atoms=1,
    )
    calls: list[str] = []

    def sentinel(_scratch: object) -> None:
        calls.append("called")

    # Mutate both policy surfaces a careless adapter might otherwise use as
    # authority.  The transition's closed partition must remain fail-closed.
    monkeypatch.setattr(m6_transition, "M6_RESEARCH_DISABLED_COMMANDS_V1", frozenset(), raising=False)
    monkeypatch.setattr(
        m6_transition,
        "_BUSINESS_HANDLERS",
        {GlobalCommandKindV1.PROTOCOL_BUY_AND_BURN: sentinel},
    )
    result = run_m6_transition_v1(subject, state, _context(subject, state, 1), command)

    assert calls == []
    assert isinstance(result, AcceptCandidateV1)
    assert result.business_status is BusinessStatusV1.REJECTED_COMMITTED
    assert result.business_reject_reason is BusinessRejectReasonV1.UNSUPPORTED_OPERATION


def test_late_business_failure_rolls_back_all_mutable_scratch_effects(
    subject: M6PromotionSubjectV1,
) -> None:
    """RIPR: a redeem fails after burns/debt changes when vault custody is absent."""

    atoms = tuple(
        sorted(
            (
                EconomicAtomV1(EconomicAtomKindV1.BALANCE, "alice", "zUSD", "ledger", 5),
                EconomicAtomV1(EconomicAtomKindV1.SUPPLY, "__supply__", "zUSD", "ledger", 5),
                EconomicAtomV1(
                    EconomicAtomKindV1.DEBT,
                    "alice",
                    "debt:rollback-vault",
                    "liability",
                    5,
                ),
            ),
            key=lambda atom: atom.key,
        )
    )
    state = replace(_state(subject), economic_atoms=atoms)
    command = _command(
        GlobalCommandKindV1.ZUSD_REDEEM,
        1,
        amount_atoms=1,
        collateral_asset="A",
        vault_id="rollback-vault",
    )

    context = _context(subject, state, 1)
    result = run_m6_transition_v1(subject, state, context, command)

    _assert_committed_rejection_contract_v1(
        state,
        context,
        command,
        result,
        BusinessRejectReasonV1.INSUFFICIENT_BALANCE,
    )


def _seller_reveal_commitment(
    auction_id: str,
    bidder: str,
    inventory_asset: str,
    quantity_atoms: int,
    price_e8: int,
    nonce: int,
) -> str:
    return hash_v1(
        "m6-seller-auction-reveal-v1",
        {
            "auction_id": auction_id,
            "bidder": bidder,
            "inventory_asset": inventory_asset,
            "quantity_atoms": quantity_atoms,
            "price_e8": price_e8,
            "nonce": nonce,
        },
    )


def _private_reveal_commitment(
    batch_id: str,
    trader: str,
    asset_in: str,
    amount_in_atoms: int,
    asset_out: str,
    amount_out_atoms: int,
    nonce: int,
) -> str:
    return hash_v1(
        "m6-private-swap-reveal-v1",
        {
            "batch_id": batch_id,
            "trader": trader,
            "asset_in": asset_in,
            "amount_in_atoms": amount_in_atoms,
            "asset_out": asset_out,
            "amount_out_atoms": amount_out_atoms,
            "nonce": nonce,
        },
    )


def test_canonical_command_round_trip_rejects_duplicate_and_float_fields() -> None:
    command = _command(
        GlobalCommandKindV1.TAU_WITHDRAWAL,
        1,
        withdrawal_id="w1",
        asset="A",
        amount_atoms=2,
        destination="tau-alice",
    )
    raw = canonical_bytes_v1(command)
    assert decode_global_command_v1(raw) == command
    with pytest.raises(ValueError, match="duplicate"):
        decode_global_command_v1(raw.replace(b'"nonce":1', b'"nonce":1,"nonce":1'))
    with pytest.raises(ValueError, match="floats"):
        decode_global_command_v1(raw.replace(b'"amount_atoms":2', b'"amount_atoms":2.0'))
    with pytest.raises(ValueError, match="unknown"):
        _command(
            GlobalCommandKindV1.TAU_WITHDRAWAL,
            1,
            withdrawal_id="w1",
            asset="A",
            amount_atoms=2,
            destination="tau-alice",
            ignored_authority_hint="mallory",
        )


def test_malformed_command_ingress_returns_no_commit_without_touching_state(
    subject: M6PromotionSubjectV1,
) -> None:
    """AAA: raw malformed input is typed before batch admission and has no nonce."""

    state = _state(subject)
    pre_state_root = state.state_root
    for raw in (b"not-json", b"{}", object()):
        result = admit_global_command_v1(raw, pre_state_root=pre_state_root)
        assert isinstance(result, RejectNoCommitV1)
        assert result.reason is AdmissionRejectReasonV1.MALFORMED_COMMAND
        assert result.pre_state_root == pre_state_root
        assert result.command_hash is None

    assert state.state_root == pre_state_root
    assert state.get_nonce("alice") == 0


def test_untyped_context_reaches_only_a_no_commit_reject(
    subject: M6PromotionSubjectV1,
) -> None:
    state = _state(subject, alice_atoms=3)
    command = _command(
        GlobalCommandKindV1.TAU_WITHDRAWAL,
        1,
        withdrawal_id="w-untyped",
        asset="A",
        amount_atoms=2,
        destination="tau-mallory",
    )
    pre_state_root = state.state_root

    result = run_m6_transition_v1(
        subject,
        state,
        cast(AuthenticatedExecutionContextV1, object()),
        command,
    )

    assert isinstance(result, RejectNoCommitV1)
    assert result.reason is AdmissionRejectReasonV1.UNAUTHENTICATED_CONTEXT
    assert result.pre_state_root == pre_state_root
    assert state.state_root == pre_state_root
    assert state.get_nonce("alice") == 0


def test_zero_economic_atoms_are_not_representable() -> None:
    with pytest.raises(ValueError, match="economic atom amount must be positive"):
        EconomicAtomV1(EconomicAtomKindV1.BALANCE, "alice", "A", "ledger", 0)


def test_ledger_allocation_api_is_nonlegal_and_preserves_the_v1_wire_projection(
    subject: M6PromotionSubjectV1,
) -> None:
    """BDD/compatibility: logical allocations avoid a legal-custody claim."""

    # Given: a new caller names the internal accounting partition explicitly.
    atom = EconomicAtomV1.from_ledger_allocation(
        kind=EconomicAtomKindV1.BALANCE,
        owner="alice",
        asset="A",
        ledger_allocation="ledger",
        amount_atoms=7,
    )
    delta = ValueDeltaEntryV1.from_ledger_allocation(
        delta_class=m6_types.ValueDeltaClassV1.INTERNAL_TRANSFER,
        owner="alice",
        asset="A",
        ledger_allocation="ledger",
        delta_atoms=-7,
    )
    legacy_atom = EconomicAtomV1(EconomicAtomKindV1.BALANCE, "alice", "A", "ledger", 7)
    legacy_delta = ValueDeltaEntryV1(
        m6_types.ValueDeltaClassV1.INTERNAL_TRANSFER,
        "alice",
        "A",
        "ledger",
        -7,
    )

    # When: it is exposed to the V1 canonical codec.
    atom_wire = atom.to_canonical()
    delta_wire = delta.to_canonical()
    state = replace(initial_application_state_v1(subject), economic_atoms=(atom,))

    # Then: public vocabulary is legal-neutral while historical V1 roots retain
    # their fixed field spelling until an explicit schema migration occurs.
    assert atom.ledger_allocation == "ledger"
    assert delta.ledger_allocation == "ledger"
    assert atom == legacy_atom
    assert delta == legacy_delta
    assert canonical_bytes_v1(atom) == canonical_bytes_v1(legacy_atom)
    assert canonical_bytes_v1(delta) == canonical_bytes_v1(legacy_delta)
    assert (
        state.get_ledger_allocation(EconomicAtomKindV1.BALANCE, "alice", "A", "ledger")
        == 7
    )
    assert state.get_atom(EconomicAtomKindV1.BALANCE, "alice", "A", "ledger") == 7
    assert atom_wire["custody"] == "ledger"
    assert delta_wire["custody"] == "ledger"
    assert "ledger_allocation" not in atom_wire
    assert "ledger_allocation" not in delta_wire


def test_command_integer_overflow_is_rejected_at_the_typed_boundary() -> None:
    with pytest.raises(ValueError, match="command argument amount_atoms exceeds"):
        _command(
            GlobalCommandKindV1.LP_ADD,
            1,
            asset="A",
            amount_atoms=MAX_ATOMS_V1 + 1,
            pool="pool",
            lp_shares_atoms=1,
        )


@pytest.mark.parametrize(
    ("pool_atoms", "expected_status", "expected_reason"),
    (
        (MAX_ATOMS_V1 - 1, BusinessStatusV1.ACCEPTED, None),
        (MAX_ATOMS_V1, BusinessStatusV1.REJECTED_COMMITTED, BusinessRejectReasonV1.INVALID_AMOUNT),
    ),
    ids=("max-minus-one-accepted", "max-overflow-committed-rejection"),
)
def test_enabled_atom_update_is_total_at_max_boundary(
    subject: M6PromotionSubjectV1,
    pool_atoms: int,
    expected_status: BusinessStatusV1,
    expected_reason: BusinessRejectReasonV1 | None,
) -> None:
    """BVA: an admitted enabled transfer never leaks an atom overflow exception."""

    state = replace(
        _state(subject, alice_atoms=1),
        economic_atoms=tuple(
            sorted(
                (
                    EconomicAtomV1(EconomicAtomKindV1.BALANCE, "alice", "A", "ledger", 1),
                    EconomicAtomV1(EconomicAtomKindV1.BALANCE, "pool", "A", "ledger", pool_atoms),
                    EconomicAtomV1(EconomicAtomKindV1.BALANCE, "pool", "B", "ledger", 65),
                ),
                key=lambda item: item.key,
            )
        ),
    )
    context = _context(subject, state, 1)
    command = _command(
        GlobalCommandKindV1.LP_ADD,
        1,
        asset="A",
        amount_atoms=1,
        pool="pool",
        lp_shares_atoms=1,
    )

    result = run_m6_transition_v1(subject, state, context, command)

    if expected_status is BusinessStatusV1.REJECTED_COMMITTED:
        assert expected_reason is not None
        _assert_committed_rejection_contract_v1(state, context, command, result, expected_reason)
    else:
        assert isinstance(result, AcceptCandidateV1)
        assert result.business_status is expected_status
        assert result.business_reject_reason is expected_reason
        assert result.post_state.get_atom(EconomicAtomKindV1.BALANCE, "pool", "A", "ledger") == MAX_ATOMS_V1


def test_spot_swap_preserves_internal_conservation_and_commits_new_state(subject: M6PromotionSubjectV1) -> None:
    state = _state(subject, alice_atoms=100)
    command = _command(
        GlobalCommandKindV1.SPOT_SWAP,
        1,
        asset_in="A",
        asset_out="B",
        amount_in_atoms=10,
        amount_out_atoms=5,
        pool="pool",
        fee_atoms=1,
    )
    result = run_m6_transition_v1(subject, state, _context(subject, state, 1), command)
    assert isinstance(result, AcceptCandidateV1)
    assert result.business_status is BusinessStatusV1.ACCEPTED
    assert result.post_state.get_nonce("alice") == 1
    assert result.post_state.get_atom(EconomicAtomKindV1.BALANCE, "alice", "A", "ledger") == 90
    assert result.post_state.get_atom(EconomicAtomKindV1.BALANCE, "alice", "B", "ledger") == 5
    assert result.value_delta.preserves_internal_conservation()
    assert result.value_delta.internal_transfer_totals() == {("A", "ledger"): 0, ("B", "ledger"): 0}


def test_spot_swap_rejects_caller_selected_output_against_pool_quote(
    subject: M6PromotionSubjectV1,
) -> None:
    state = _state(subject, alice_atoms=100)
    command = _command(
        GlobalCommandKindV1.SPOT_SWAP,
        1,
        asset_in="A",
        asset_out="B",
        amount_in_atoms=10,
        amount_out_atoms=6,
        pool="pool",
        fee_atoms=1,
    )
    result = run_m6_transition_v1(subject, state, _context(subject, state, 1), command)
    assert isinstance(result, AcceptCandidateV1)
    assert result.business_status is BusinessStatusV1.REJECTED_COMMITTED
    assert result.business_reject_reason is BusinessRejectReasonV1.INVALID_PRICE
    assert result.post_state.economic_atoms == state.economic_atoms


def test_stability_pool_withdraw_requires_the_callers_own_pool_claim(
    subject: M6PromotionSubjectV1,
) -> None:
    """AAA/RIPR: authenticated identity alone cannot drain shared custody."""

    # Arrange: the pool is funded, while Mallory has no provider claim.
    state = replace(
        initial_application_state_v1(subject),
        economic_atoms=(
            EconomicAtomV1(
                EconomicAtomKindV1.BALANCE,
                "stability_pool",
                "zUSD",
                "ledger",
                10,
            ),
        ),
    )
    command = _command_for(
        GlobalCommandKindV1.STABILITY_POOL_WITHDRAW,
        "mallory",
        1,
        1_101,
        amount_atoms=10,
    )

    # Act: submit a well-formed authenticated withdrawal.
    result = run_m6_transition_v1(
        subject,
        state,
        _context_for(subject, state, "mallory", 1, 0),
        command,
    )

    # Assert: the business rejection consumes Mallory's nonce but leaves pool
    # custody and every recipient balance unchanged.
    assert isinstance(result, AcceptCandidateV1)
    assert result.business_status is BusinessStatusV1.REJECTED_COMMITTED
    assert result.business_reject_reason is BusinessRejectReasonV1.INSUFFICIENT_BALANCE
    assert result.post_state.get_atom(EconomicAtomKindV1.BALANCE, "stability_pool", "zUSD", "ledger") == 10
    assert result.post_state.get_atom(EconomicAtomKindV1.BALANCE, "mallory", "zUSD", "ledger") == 0


def test_stability_pool_deposit_and_withdraw_round_trip_uses_claim_atom(
    subject: M6PromotionSubjectV1,
) -> None:
    """AAA/BVA: one provider can withdraw exactly its recorded claim."""

    # Arrange: Alice has one zUSD atom and no existing pool claim.
    state = replace(
        initial_application_state_v1(subject),
        economic_atoms=(
            EconomicAtomV1(EconomicAtomKindV1.BALANCE, "alice", "zUSD", "ledger", 1),
        ),
    )

    # Act: deposit one atom, then withdraw the exact boundary amount.
    deposited = run_m6_transition_v1(
        subject,
        state,
        _context(subject, state, 1),
        _command(GlobalCommandKindV1.STABILITY_POOL_DEPOSIT, 1, amount_atoms=1),
    )
    assert isinstance(deposited, AcceptCandidateV1)
    withdrawn = run_m6_transition_v1(
        subject,
        deposited.post_state,
        _context(subject, deposited.post_state, 2),
        _command(GlobalCommandKindV1.STABILITY_POOL_WITHDRAW, 2, amount_atoms=1),
    )

    # Assert: custody and claim both return to their terminal zero form.
    assert isinstance(withdrawn, AcceptCandidateV1)
    assert withdrawn.business_status is BusinessStatusV1.ACCEPTED
    assert withdrawn.post_state.get_atom(EconomicAtomKindV1.BALANCE, "alice", "zUSD", "ledger") == 1
    assert withdrawn.post_state.get_atom(EconomicAtomKindV1.BALANCE, "stability_pool", "zUSD", "ledger") == 0
    assert withdrawn.post_state.get_atom(EconomicAtomKindV1.STABILITY_POOL_SHARE, "alice", "zUSD", "stability_pool") == 0

    deposit_entries = {
        (entry.owner, entry.asset, entry.custody): entry.delta_atoms
        for entry in deposited.value_delta.entries
        if entry.delta_class.name == "LIABILITY"
    }
    withdraw_entries = {
        (entry.owner, entry.asset, entry.custody): entry.delta_atoms
        for entry in withdrawn.value_delta.entries
        if entry.delta_class.name == "LIABILITY"
    }
    assert deposit_entries[("alice", "zUSD", "stability_pool")] == 1
    assert withdraw_entries[("alice", "zUSD", "stability_pool")] == -1


def test_positionless_perp_funding_is_fail_closed_without_value_effect(
    subject: M6PromotionSubjectV1,
) -> None:
    """BDD/AAA: incomplete funding cannot strand a caller's zUSD."""

    state = replace(
        _state(subject),
        economic_atoms=(EconomicAtomV1(EconomicAtomKindV1.BALANCE, "alice", "zUSD", "ledger", 1),),
    )
    command = _command(GlobalCommandKindV1.PERP_FUNDING, 1, market="BTC", amount_atoms=1)

    result = run_m6_transition_v1(subject, state, _context(subject, state, 1), command)

    assert isinstance(result, AcceptCandidateV1)
    assert result.business_status is BusinessStatusV1.REJECTED_COMMITTED
    assert result.business_reject_reason is BusinessRejectReasonV1.UNSUPPORTED_OPERATION
    assert result.post_state.economic_atoms == state.economic_atoms


def test_zusd_borrow_rejects_amount_above_conservative_collateral_bound(
    subject: M6PromotionSubjectV1,
) -> None:
    state = replace(
        initial_application_state_v1(subject),
        economic_atoms=(EconomicAtomV1(EconomicAtomKindV1.BALANCE, "alice", "A", "ledger", 5),),
    )
    command = _command(
        GlobalCommandKindV1.ZUSD_BORROW,
        1,
        collateral_asset="A",
        collateral_atoms=1,
        amount_atoms=2,
        vault_id="v1",
    )
    result = run_m6_transition_v1(subject, state, _context(subject, state, 1), command)
    assert isinstance(result, AcceptCandidateV1)
    assert result.business_status is BusinessStatusV1.REJECTED_COMMITTED
    assert result.business_reject_reason is BusinessRejectReasonV1.INVALID_AMOUNT
    assert result.post_state.economic_atoms == state.economic_atoms


def test_zusd_redistribution_is_disabled_without_liquidation_authority(
    subject: M6PromotionSubjectV1,
) -> None:
    state = replace(
        initial_application_state_v1(subject),
        economic_atoms=tuple(
            sorted(
                (
                    EconomicAtomV1(EconomicAtomKindV1.BALANCE, "alice", "zUSD", "ledger", 3),
                    EconomicAtomV1(EconomicAtomKindV1.BALANCE, "vault:v1", "A", "ledger", 5),
                ),
                key=lambda item: item.key,
            )
        ),
    )
    command = _command(
        GlobalCommandKindV1.ZUSD_REDISTRIBUTE,
        1,
        amount_atoms=3,
        collateral_asset="A",
        collateral_atoms=2,
        source_vault="vault:v1",
    )
    result = run_m6_transition_v1(subject, state, _context(subject, state, 1), command)
    assert isinstance(result, AcceptCandidateV1)
    assert result.business_status is BusinessStatusV1.REJECTED_COMMITTED
    assert result.business_reject_reason is BusinessRejectReasonV1.UNSUPPORTED_OPERATION
    assert result.post_state.economic_atoms == state.economic_atoms


def test_zusd_redeem_rejects_collateral_release_without_matching_debt(
    subject: M6PromotionSubjectV1,
) -> None:
    # Arrange: the caller owns zUSD and the vault owns collateral, while no
    # debt atom binds those two claims.
    state = replace(
        initial_application_state_v1(subject),
        economic_atoms=tuple(
            sorted(
                (
                    EconomicAtomV1(EconomicAtomKindV1.BALANCE, "alice", "zUSD", "ledger", 5),
                    EconomicAtomV1(EconomicAtomKindV1.SUPPLY, "__supply__", "zUSD", "ledger", 5),
                    EconomicAtomV1(EconomicAtomKindV1.BALANCE, "vault:v1", "A", "ledger", 5),
                ),
                key=lambda item: item.key,
            )
        ),
    )
    command = _command(
        GlobalCommandKindV1.ZUSD_REDEEM,
        1,
        vault_id="v1",
        collateral_asset="A",
        amount_atoms=5,
    )

    # Act: attempt to redeem against custody without a debt liability.
    result = run_m6_transition_v1(subject, state, _context(subject, state, 1), command)

    # Assert: no collateral is released and no supply is burned.
    assert isinstance(result, AcceptCandidateV1)
    assert result.business_status is BusinessStatusV1.REJECTED_COMMITTED
    assert result.business_reject_reason is BusinessRejectReasonV1.INSUFFICIENT_BALANCE
    assert result.post_state.economic_atoms == state.economic_atoms


def test_zusd_redeem_closes_the_matching_debt_and_returns_vault_collateral(
    subject: M6PromotionSubjectV1,
) -> None:
    # Arrange: this is the exact borrow/redeem boundary with a one-to-one
    # conservative collateral policy.
    borrowed = run_m6_transition_v1(
        subject,
        _state(subject, alice_atoms=5),
        _context(subject, _state(subject, alice_atoms=5), 1),
        _command(
            GlobalCommandKindV1.ZUSD_BORROW,
            1,
            collateral_asset="A",
            collateral_atoms=5,
            amount_atoms=5,
            vault_id="v1",
        ),
    )
    assert isinstance(borrowed, AcceptCandidateV1)
    assert borrowed.business_status is BusinessStatusV1.ACCEPTED

    # Act: redeem exactly the outstanding debt.
    result = run_m6_transition_v1(
        subject,
        borrowed.post_state,
        _context(subject, borrowed.post_state, 2),
        _command(
            GlobalCommandKindV1.ZUSD_REDEEM,
            2,
            vault_id="v1",
            collateral_asset="A",
            amount_atoms=5,
        ),
    )

    # Assert: the monetary kernel closes debt, supply, and vault custody
    # together; no collateral is created from an unbound claim.
    assert isinstance(result, AcceptCandidateV1)
    assert result.business_status is BusinessStatusV1.ACCEPTED
    assert result.post_state.get_atom(EconomicAtomKindV1.DEBT, "alice", "debt:v1", "liability") == 0
    assert result.post_state.get_atom(EconomicAtomKindV1.SUPPLY, "__supply__", "zUSD", "ledger") == 0
    vault_owner = "vault:" + hash_v1(
        "m6-zusd-vault-owner-v1", {"vault_id": "v1", "sender": "alice"}
    )
    assert result.post_state.get_atom(EconomicAtomKindV1.BALANCE, vault_owner, "A", "ledger") == 0
    assert result.post_state.get_atom(EconomicAtomKindV1.BALANCE, "alice", "A", "ledger") == 5


@pytest.mark.parametrize("oracle_age", (0, 1, 2, 3))
def test_zusd_borrow_freshness_boundary_is_closed_and_deterministic(
    subject: M6PromotionSubjectV1,
    oracle_age: int,
) -> None:
    """BDD/BVA/AAA: risk-increasing debt creation stops exactly past max age."""

    state = _state(subject, alice_atoms=5)
    command = replace(
        _command(
            GlobalCommandKindV1.ZUSD_BORROW,
            1,
            collateral_asset="A",
            collateral_atoms=1,
            amount_atoms=1,
            vault_id="freshness-vault",
        ),
        created_height=10 + oracle_age,
    )

    result = run_m6_transition_v1(
        subject,
        state,
        _context(
            subject,
            state,
            1,
            ledger_height=10 + oracle_age,
            oracle_age=oracle_age,
        ),
        command,
    )

    if oracle_age <= 2:
        assert isinstance(result, AcceptCandidateV1)
        assert result.business_status is BusinessStatusV1.ACCEPTED
        assert result.post_state.get_atom(EconomicAtomKindV1.SUPPLY, "__supply__", "zUSD", "ledger") == 1
    else:
        assert isinstance(result, RejectNoCommitV1)
        assert result.reason is AdmissionRejectReasonV1.STALE_ORACLE_CONTEXT
        assert result.pre_state_root == state.state_root


def test_zusd_repay_remains_available_for_stale_oracle_recovery(
    subject: M6PromotionSubjectV1,
) -> None:
    """BDD/AAA: debt-reducing recovery remains possible after freshness expiry."""

    initial = _state(subject, alice_atoms=5)
    borrowed = run_m6_transition_v1(
        subject,
        initial,
        _context(subject, initial, 1),
        _command(
            GlobalCommandKindV1.ZUSD_BORROW,
            1,
            collateral_asset="A",
            collateral_atoms=1,
            amount_atoms=1,
            vault_id="recovery-vault",
        ),
    )
    assert isinstance(borrowed, AcceptCandidateV1)

    repaid = run_m6_transition_v1(
        subject,
        borrowed.post_state,
        _context(
            subject,
            borrowed.post_state,
            2,
            ledger_height=13,
            oracle_age=3,
        ),
        replace(
            _command(
                GlobalCommandKindV1.ZUSD_REPAY,
                2,
                amount_atoms=1,
                vault_id="recovery-vault",
            ),
            created_height=13,
        ),
    )

    assert isinstance(repaid, AcceptCandidateV1)
    assert repaid.business_status is BusinessStatusV1.ACCEPTED
    assert repaid.post_state.get_atom(EconomicAtomKindV1.SUPPLY, "__supply__", "zUSD", "ledger") == 0
    assert repaid.post_state.get_atom(EconomicAtomKindV1.DEBT, "alice", "debt:recovery-vault", "liability") == 0


@pytest.mark.parametrize("age", (0, 2, 3))
def test_command_freshness_boundary_is_closed_and_no_commit_is_pure(
    subject: M6PromotionSubjectV1,
    age: int,
) -> None:
    """BDD/AAA/BVA: command age is enforced at the exact profile boundary."""

    state = _state(subject)
    command = replace(
        _command(
            GlobalCommandKindV1.SELLER_AUCTION_CANCEL,
            1,
            auction_id="fresh-command",
        ),
        created_height=10,
    )
    result = run_m6_transition_v1(
        subject,
        state,
        _context(
            subject,
            state,
            1,
            ledger_height=10 + age,
            freshness_bounds=FreshnessBoundsV1(2, 2, 2),
        ),
        command,
    )

    if age <= 2:
        assert isinstance(result, AcceptCandidateV1)
        assert result.post_state.get_nonce("alice") == 1
    else:
        assert isinstance(result, RejectNoCommitV1)
        assert result.reason is AdmissionRejectReasonV1.STALE_COMMAND_CONTEXT
        assert result.pre_state_root == state.state_root
        assert state.get_nonce("alice") == 0


@pytest.mark.parametrize("age", (0, 2, 3))
def test_tau_evidence_freshness_boundary_is_closed_and_no_commit_is_pure(
    subject: M6PromotionSubjectV1,
    age: int,
) -> None:
    """BDD/AAA/BVA: stale Tau evidence cannot create internal credit."""

    state = _state(subject)
    command = _command(
        GlobalCommandKindV1.TAU_ESCROW_DEPOSIT,
        1,
        deposit_id="fresh-tau",
        asset="A",
        amount_atoms=1,
        tau_transaction_root=_root(7_201),
        tau_finality_root=_root(7_202),
        tau_profile_root=subject.tau_profile,
        tau_finality_height=10,
    )
    command = replace(command, created_height=10)
    context = _with_deposit_evidence(
        subject,
        state,
        command,
        ledger_height=10 + age,
        freshness_bounds=FreshnessBoundsV1(99, 2, 99),
    )
    result = run_m6_transition_v1(subject, state, context, command)

    if age <= 2:
        assert isinstance(result, AcceptCandidateV1)
        assert result.business_status is BusinessStatusV1.ACCEPTED
        assert result.post_state.escrows
    else:
        assert isinstance(result, RejectNoCommitV1)
        assert result.reason is AdmissionRejectReasonV1.STALE_TAU_CONTEXT
        assert result.pre_state_root == state.state_root
        assert state.get_nonce("alice") == 0


def test_authority_boundary_rejects_inconsistent_zusd_supply_and_debt(
    subject: M6PromotionSubjectV1,
) -> None:
    """RIPR/mutation: a forged monetary supply cannot enter the commit port."""

    state = replace(
        initial_application_state_v1(subject),
        economic_atoms=(EconomicAtomV1(EconomicAtomKindV1.SUPPLY, "__supply__", "zUSD", "ledger", 1),),
    )

    with pytest.raises(ValueError, match="zUSD supply/debt mismatch"):
        validate_economic_state_v1(state)
    with pytest.raises(ValueError, match="zUSD supply/debt mismatch"):
        M6CommitPortV1(subject, state, _TEST_FINALITY_VERIFIER)


@pytest.mark.parametrize("asset", ("TAU", "PROTO", "A"))
def test_authority_boundary_rejects_unbacked_non_zusd_supply(
    subject: M6PromotionSubjectV1,
    asset: str,
) -> None:
    """BDD/BVA: no non-zUSD supply enters authority without its owning kernel."""

    # Arrange: construct a typed but unsupported issuance atom at each asset
    # boundary represented by the research profile.
    state = replace(
        initial_application_state_v1(subject),
        economic_atoms=(EconomicAtomV1(EconomicAtomKindV1.SUPPLY, "__supply__", asset, "ledger", 1),),
    )

    # Act and assert: both the pure validator and the unique commit port fail
    # closed before any state can acquire economic authority.
    with pytest.raises(ValueError, match="non-zUSD supply requires a mounted issuance kernel"):
        validate_economic_state_v1(state)
    with pytest.raises(ValueError, match="non-zUSD supply requires a mounted issuance kernel"):
        M6CommitPortV1(subject, state, _TEST_FINALITY_VERIFIER)


@pytest.mark.parametrize(
    ("left_atoms", "right_atoms"),
    ((MAX_ATOMS_V1 - 1, 2), (MAX_ATOMS_V1, 1)),
)
def test_authority_boundary_rejects_aggregate_atom_overflow(
    subject: M6PromotionSubjectV1,
    left_atoms: int,
    right_atoms: int,
) -> None:
    """BVA/RIPR: individually valid rows cannot overflow an authority aggregate."""

    # Arrange: two owners share one asset/custody aggregate at its upper edge.
    state = replace(
        initial_application_state_v1(subject),
        economic_atoms=(
            EconomicAtomV1(EconomicAtomKindV1.BALANCE, "alice", "A", "ledger", left_atoms),
            EconomicAtomV1(EconomicAtomKindV1.BALANCE, "bob", "A", "ledger", right_atoms),
        ),
    )

    # Act and assert: the authority boundary rejects before commit-port creation.
    with pytest.raises(ValueError, match="economic aggregate exceeds 128-bit atom domain"):
        validate_economic_state_v1(state)
    with pytest.raises(ValueError, match="economic aggregate exceeds 128-bit atom domain"):
        M6CommitPortV1(subject, state, _TEST_FINALITY_VERIFIER)


@pytest.mark.parametrize(
    "economic_atoms",
    (
        pytest.param(
            (
                EconomicAtomV1(EconomicAtomKindV1.BALANCE, "alice", "A", "ledger", MAX_ATOMS_V1 - 1),
                EconomicAtomV1(EconomicAtomKindV1.BALANCE, "bob", "A", "ledger", 1),
            ),
            id="same_kind_asset_custody",
        ),
        pytest.param(
            (
                EconomicAtomV1(EconomicAtomKindV1.BALANCE, "alice", "A", "ledger", MAX_ATOMS_V1),
                EconomicAtomV1(EconomicAtomKindV1.BALANCE, "bob", "A", "vault", MAX_ATOMS_V1),
            ),
            id="different_custody",
        ),
        pytest.param(
            (
                EconomicAtomV1(EconomicAtomKindV1.BALANCE, "alice", "A", "ledger", MAX_ATOMS_V1),
                EconomicAtomV1(EconomicAtomKindV1.BALANCE, "bob", "B", "ledger", MAX_ATOMS_V1),
            ),
            id="different_asset",
        ),
        pytest.param(
            (
                EconomicAtomV1(EconomicAtomKindV1.REWARD, "prover", "PROTO", "reward", MAX_ATOMS_V1),
                EconomicAtomV1(
                    EconomicAtomKindV1.PROTOCOL_RESERVE,
                    "protocol",
                    "PROTO",
                    "reserve",
                    MAX_ATOMS_V1,
                ),
            ),
            id="different_kind",
        ),
    ),
)
def test_authority_boundary_accepts_exact_aggregate_max_per_partition(
    subject: M6PromotionSubjectV1,
    economic_atoms: tuple[EconomicAtomV1, ...],
) -> None:
    """BVA/RIPR: MAX is valid once per independent kind/asset/custody partition."""

    state = replace(
        initial_application_state_v1(subject),
        economic_atoms=tuple(sorted(economic_atoms, key=lambda atom: atom.key)),
    )

    validate_economic_state_v1(state)
    M6CommitPortV1(subject, state, _TEST_FINALITY_VERIFIER)


def test_economic_state_validator_closes_pool_escrow_and_reward_relations(
    subject: M6PromotionSubjectV1,
) -> None:
    """RIPR/BVA: each supported custody relation has a named terminal check."""

    pool_state = replace(
        initial_application_state_v1(subject),
        economic_atoms=(EconomicAtomV1(EconomicAtomKindV1.BALANCE, "stability_pool", "zUSD", "ledger", 1),),
    )
    with pytest.raises(ValueError, match="Stability Pool custody/claim mismatch"):
        validate_economic_state_v1(pool_state)

    escrow_state = replace(
        initial_application_state_v1(subject),
        escrows=(EscrowAtomV1("escrow-1", "alice", "A", 1, "seller_commit"),),
    )
    with pytest.raises(ValueError, match="escrow custody mismatch"):
        validate_economic_state_v1(escrow_state)

    reward_state = replace(
        initial_application_state_v1(subject),
        economic_atoms=tuple(
            sorted(
                (
                    EconomicAtomV1(EconomicAtomKindV1.REWARD, "prover", "PROTO", "reward", 2),
                    EconomicAtomV1(EconomicAtomKindV1.PROTOCOL_RESERVE, "protocol", "PROTO", "reserve", 1),
                ),
                key=lambda atom: atom.key,
            )
        ),
    )
    with pytest.raises(ValueError, match="reward/reserve mismatch"):
        validate_economic_state_v1(reward_state)


def test_zusd_vault_custody_cannot_cross_owner_when_vault_ids_collide(
    subject: M6PromotionSubjectV1,
) -> None:
    """RIPR/BVA: one shared vault label cannot authorize another owner's asset."""

    initial = replace(
        initial_application_state_v1(subject),
        economic_atoms=tuple(
            sorted(
                (
                    EconomicAtomV1(EconomicAtomKindV1.BALANCE, "alice", "A", "ledger", 1),
                    EconomicAtomV1(EconomicAtomKindV1.BALANCE, "bob", "B", "ledger", 1),
                ),
                key=lambda atom: atom.key,
            )
        ),
    )
    alice_borrow = run_m6_transition_v1(
        subject,
        initial,
        _context_for(subject, initial, "alice", 1, 0),
        _command_for(
            GlobalCommandKindV1.ZUSD_BORROW,
            "alice",
            1,
            12_001,
            collateral_asset="A",
            collateral_atoms=1,
            amount_atoms=1,
            vault_id="shared",
        ),
    )
    assert isinstance(alice_borrow, AcceptCandidateV1)
    bob_borrow = run_m6_transition_v1(
        subject,
        alice_borrow.post_state,
        _context_for(subject, alice_borrow.post_state, "bob", 1, 0),
        _command_for(
            GlobalCommandKindV1.ZUSD_BORROW,
            "bob",
            1,
            12_002,
            collateral_asset="B",
            collateral_atoms=1,
            amount_atoms=1,
            vault_id="shared",
        ),
    )
    assert isinstance(bob_borrow, AcceptCandidateV1)

    # Act: Alice tries to redeem Bob's collateral asset through the shared label.
    result = run_m6_transition_v1(
        subject,
        bob_borrow.post_state,
        _context(subject, bob_borrow.post_state, 2),
        _command(
            GlobalCommandKindV1.ZUSD_REDEEM,
            2,
            vault_id="shared",
            collateral_asset="B",
            amount_atoms=1,
        ),
    )

    # Assert: the failed attempt consumes only Alice's ingress identity.
    assert isinstance(result, AcceptCandidateV1)
    assert result.business_status is BusinessStatusV1.REJECTED_COMMITTED
    assert result.business_reject_reason is BusinessRejectReasonV1.INSUFFICIENT_BALANCE
    assert result.post_state.get_atom(EconomicAtomKindV1.BALANCE, "alice", "B", "ledger") == 0
    assert result.post_state.get_atom(EconomicAtomKindV1.BALANCE, "bob", "B", "ledger") == 0
    assert result.post_state.get_atom(EconomicAtomKindV1.DEBT, "bob", "debt:shared", "liability") == 1


def test_lp_share_identity_binds_the_deposit_asset(
    subject: M6PromotionSubjectV1,
) -> None:
    # Arrange: create one LP share against asset A.
    state = replace(
        initial_application_state_v1(subject),
        economic_atoms=tuple(
            sorted(
                (
                    EconomicAtomV1(EconomicAtomKindV1.BALANCE, "alice", "A", "ledger", 1),
                    EconomicAtomV1(EconomicAtomKindV1.BALANCE, "pool", "A", "ledger", 1),
                    EconomicAtomV1(EconomicAtomKindV1.BALANCE, "pool", "B", "ledger", 1),
                ),
                key=lambda item: item.key,
            )
        ),
    )
    added = run_m6_transition_v1(
        subject,
        state,
        _context(subject, state, 1),
        _command(GlobalCommandKindV1.LP_ADD, 1, asset="A", amount_atoms=1, pool="pool", lp_shares_atoms=1),
    )
    assert isinstance(added, AcceptCandidateV1)
    assert added.business_status is BusinessStatusV1.ACCEPTED

    # Act: cross the sharp asset boundary on removal.
    result = run_m6_transition_v1(
        subject,
        added.post_state,
        _context(subject, added.post_state, 2),
        _command(GlobalCommandKindV1.LP_REMOVE, 2, asset="B", amount_atoms=1, pool="pool", lp_shares_atoms=1),
    )

    # Assert: the A share cannot authorize a B withdrawal.
    assert isinstance(result, AcceptCandidateV1)
    assert result.business_status is BusinessStatusV1.REJECTED_COMMITTED
    assert result.business_reject_reason is BusinessRejectReasonV1.INVALID_AMOUNT
    assert result.post_state.get_atom(EconomicAtomKindV1.BALANCE, "alice", "B", "ledger") == 0


def test_perp_close_requires_the_full_tracked_position(
    subject: M6PromotionSubjectV1,
) -> None:
    # Arrange: the account has margin and a position larger than the close.
    state = replace(
        initial_application_state_v1(subject),
        economic_atoms=tuple(
            sorted(
                (
                    EconomicAtomV1(EconomicAtomKindV1.MARGIN, "alice", "BTC", "perp", 1),
                    EconomicAtomV1(EconomicAtomKindV1.POSITION, "alice", "BTC", "perp", 100),
                    EconomicAtomV1(EconomicAtomKindV1.BALANCE, "perp:BTC", "zUSD", "ledger", 1),
                ),
                key=lambda item: item.key,
            )
        ),
    )

    # Act: close only one unit while the position remains 100 units.
    result = run_m6_transition_v1(
        subject,
        state,
        _context(subject, state, 1),
        _command(GlobalCommandKindV1.PERP_CLOSE, 1, market="BTC", size_atoms=1, pnl_atoms=0),
    )

    # Assert: partial close is rejected until the lifecycle policy supplies a
    # typed partial-close settlement rule.
    assert isinstance(result, AcceptCandidateV1)
    assert result.business_status is BusinessStatusV1.REJECTED_COMMITTED
    assert result.business_reject_reason is BusinessRejectReasonV1.INVALID_AMOUNT
    assert result.post_state.economic_atoms == state.economic_atoms


def test_perp_open_and_full_close_preserve_position_price_and_margin_lifecycle(
    subject: M6PromotionSubjectV1,
) -> None:
    # Arrange: fund the perp custody through the open transition.
    state = replace(
        initial_application_state_v1(subject),
        economic_atoms=(EconomicAtomV1(EconomicAtomKindV1.BALANCE, "alice", "zUSD", "ledger", 2),),
    )
    opened = run_m6_transition_v1(
        subject,
        state,
        _context(subject, state, 1),
        _command(
            GlobalCommandKindV1.PERP_OPEN,
            1,
            market="BTC",
            margin_atoms=1,
            size_atoms=1,
            price_e8=100,
        ),
    )
    assert isinstance(opened, AcceptCandidateV1)
    assert opened.business_status is BusinessStatusV1.ACCEPTED
    assert opened.post_state.get_atom(EconomicAtomKindV1.POSITION, "alice", "BTC", "perp") == 1
    assert opened.post_state.get_atom(EconomicAtomKindV1.POSITION_ENTRY_PRICE, "alice", "BTC", "perp:e8") == 100

    # Act: close the complete tracked position with zero PnL.
    closed = run_m6_transition_v1(
        subject,
        opened.post_state,
        _context(subject, opened.post_state, 2),
        _command(GlobalCommandKindV1.PERP_CLOSE, 2, market="BTC", size_atoms=1, pnl_atoms=0),
    )

    # Assert: position, entry price, and margin all reach their terminal zero
    # representation, while the margin returns to the trader.
    assert isinstance(closed, AcceptCandidateV1)
    assert closed.business_status is BusinessStatusV1.ACCEPTED
    assert closed.post_state.get_atom(EconomicAtomKindV1.POSITION, "alice", "BTC", "perp") == 0
    assert closed.post_state.get_atom(EconomicAtomKindV1.POSITION_ENTRY_PRICE, "alice", "BTC", "perp:e8") == 0
    assert closed.post_state.get_atom(EconomicAtomKindV1.MARGIN, "alice", "BTC", "perp") == 0
    assert closed.post_state.get_atom(EconomicAtomKindV1.BALANCE, "alice", "zUSD", "ledger") == 2


def test_seller_auction_mount_binds_participants_deadlines_and_pro_rata_fill(
    subject: M6PromotionSubjectV1,
) -> None:
    state = replace(
        initial_application_state_v1(subject),
        economic_atoms=tuple(
            sorted(
                (
                    EconomicAtomV1(EconomicAtomKindV1.BALANCE, "alice", "USD", "ledger", 100),
                    EconomicAtomV1(EconomicAtomKindV1.BALANCE, "bob", "USD", "ledger", 100),
                    EconomicAtomV1(EconomicAtomKindV1.BALANCE, "auction:auction-1", "ITEM", "ledger", 3),
                ),
                key=lambda item: item.key,
            )
        ),
    )
    price = 125_000_000
    alice_nonce = 7
    bob_nonce = 8
    alice_commitment = _seller_reveal_commitment("auction-1", "alice", "ITEM", 2, price, alice_nonce)
    bob_commitment = _seller_reveal_commitment("auction-1", "bob", "ITEM", 2, price, bob_nonce)
    alice_commit = _command_for(
        GlobalCommandKindV1.SELLER_AUCTION_COMMIT,
        "alice",
        1,
        2_001,
        auction_id="auction-1",
        bond_asset="USD",
        bond_atoms=5,
        commitment=alice_commitment,
        created_height=10,
        commit_height=10,
        reveal_deadline_height=20,
        settle_deadline_height=30,
    )
    alice_committed = run_m6_transition_v1(
        subject,
        state,
        _context_for(subject, state, "alice", 1, 10),
        alice_commit,
    )
    assert isinstance(alice_committed, AcceptCandidateV1)
    state = alice_committed.post_state

    bob_commit = _command_for(
        GlobalCommandKindV1.SELLER_AUCTION_COMMIT,
        "bob",
        1,
        2_002,
        auction_id="auction-1",
        bond_asset="USD",
        bond_atoms=5,
        commitment=bob_commitment,
        created_height=10,
        commit_height=10,
        reveal_deadline_height=20,
        settle_deadline_height=30,
    )
    bob_committed = run_m6_transition_v1(
        subject,
        state,
        _context_for(subject, state, "bob", 1, 10),
        bob_commit,
    )
    assert isinstance(bob_committed, AcceptCandidateV1)
    state = bob_committed.post_state

    alice_reveal = _command_for(
        GlobalCommandKindV1.SELLER_AUCTION_REVEAL,
        "alice",
        2,
        2_003,
        auction_id="auction-1",
        inventory_asset="ITEM",
        quantity_atoms=2,
        price_e8=price,
        nonce=alice_nonce,
        created_height=15,
    )
    alice_revealed = run_m6_transition_v1(
        subject,
        state,
        _context_for(subject, state, "alice", 2, 15),
        alice_reveal,
    )
    assert isinstance(alice_revealed, AcceptCandidateV1)
    state = alice_revealed.post_state

    bob_reveal = _command_for(
        GlobalCommandKindV1.SELLER_AUCTION_REVEAL,
        "bob",
        2,
        2_004,
        auction_id="auction-1",
        inventory_asset="ITEM",
        quantity_atoms=2,
        price_e8=price,
        nonce=bob_nonce,
        created_height=15,
    )
    bob_revealed = run_m6_transition_v1(
        subject,
        state,
        _context_for(subject, state, "bob", 2, 15),
        bob_reveal,
    )
    assert isinstance(bob_revealed, AcceptCandidateV1)
    state = bob_revealed.post_state

    settle = _command_for(
        GlobalCommandKindV1.SELLER_AUCTION_SETTLE,
        "keeper",
        1,
        2_005,
        auction_id="auction-1",
        clearing_price_e8=price,
        created_height=25,
    )
    settled = run_m6_transition_v1(
        subject,
        state,
        _context_for(subject, state, "keeper", 1, 25),
        settle,
    )
    assert isinstance(settled, AcceptCandidateV1)
    assert settled.business_status is BusinessStatusV1.ACCEPTED
    final = settled.post_state
    assert final.get_atom(EconomicAtomKindV1.BALANCE, "alice", "ITEM", "ledger") == 2
    assert final.get_atom(EconomicAtomKindV1.BALANCE, "bob", "ITEM", "ledger") == 1
    assert final.get_atom(EconomicAtomKindV1.BALANCE, "auction:auction-1", "ITEM", "ledger") == 0
    assert final.get_atom(EconomicAtomKindV1.BALANCE, "alice", "USD", "ledger") == 97
    assert final.get_atom(EconomicAtomKindV1.BALANCE, "bob", "USD", "ledger") == 98
    assert final.get_atom(EconomicAtomKindV1.BALANCE, "auction:auction-1", "USD", "ledger") == 5
    assert final.get_atom(
        EconomicAtomKindV1.ROUNDING_BUCKET,
        "protocol",
        "USD",
        "protocol-rounding-e8",
    ) == 125_000_000
    assert tuple(row.phase.value for row in final.seller_auction_bids) == ("settle", "settle")
    assert tuple(row.filled_quantity_atoms for row in final.seller_auction_bids) == (2, 1)
    assert tuple(row.rounding_remainder_e8 for row in final.seller_auction_bids) == (50_000_000, 75_000_000)
    assert all(escrow.amount_atoms == 0 for escrow in final.escrows)


def test_sealed_bid_expiry_slashes_non_reveal_and_preserves_terminal_record(
    subject: M6PromotionSubjectV1,
) -> None:
    state = replace(
        initial_application_state_v1(subject),
        economic_atoms=(
            EconomicAtomV1(EconomicAtomKindV1.BALANCE, "alice", "USD", "ledger", 10),
        ),
    )
    commit = _command_for(
        GlobalCommandKindV1.SELLER_AUCTION_COMMIT,
        "alice",
        1,
        2_102,
        auction_id="auction-expire",
        bond_asset="USD",
        bond_atoms=5,
        commitment=_root(2_101),
        created_height=10,
        commit_height=10,
        reveal_deadline_height=20,
        settle_deadline_height=30,
    )
    committed = run_m6_transition_v1(subject, state, _context_for(subject, state, "alice", 1, 10), commit)
    assert isinstance(committed, AcceptCandidateV1)
    expire = _command_for(
        GlobalCommandKindV1.SELLER_AUCTION_EXPIRE,
        "keeper",
        1,
        2_103,
        auction_id="auction-expire",
        created_height=31,
    )
    expired = run_m6_transition_v1(
        subject,
        committed.post_state,
        _context_for(subject, committed.post_state, "keeper", 1, 31),
        expire,
    )
    assert isinstance(expired, AcceptCandidateV1)
    assert expired.post_state.get_atom(EconomicAtomKindV1.PROTOCOL_RESERVE, "protocol", "USD", "reserve") == 5
    assert expired.post_state.seller_auction_bids[0].phase.value == "expired"
    assert expired.post_state.escrows[0].terminal_state == "seller_expired"
    assert expired.post_state.escrows[0].amount_atoms == 0


def test_sealed_bid_commit_rejects_when_deadline_is_not_bound_to_context_height(
    subject: M6PromotionSubjectV1,
) -> None:
    state = replace(
        initial_application_state_v1(subject),
        economic_atoms=(
            EconomicAtomV1(EconomicAtomKindV1.BALANCE, "alice", "USD", "ledger", 10),
        ),
    )
    command = _command_for(
        GlobalCommandKindV1.SELLER_AUCTION_COMMIT,
        "alice",
        1,
        2_111,
        auction_id="auction-height",
        bond_asset="USD",
        bond_atoms=5,
        commitment=_root(2_112),
        commit_height=10,
        reveal_deadline_height=20,
        settle_deadline_height=30,
    )
    result = run_m6_transition_v1(subject, state, _context(subject, state, 1), command)
    assert isinstance(result, AcceptCandidateV1)
    assert result.business_status is BusinessStatusV1.REJECTED_COMMITTED
    assert result.business_reject_reason is not None
    assert result.post_state.economic_atoms == state.economic_atoms
    assert result.post_state.escrows == ()
    assert result.post_state.seller_auction_bids == ()


def test_sealed_bid_cancel_refunds_commit_escrow_before_reveal_deadline(
    subject: M6PromotionSubjectV1,
) -> None:
    state = replace(
        initial_application_state_v1(subject),
        economic_atoms=(
            EconomicAtomV1(EconomicAtomKindV1.BALANCE, "alice", "USD", "ledger", 10),
        ),
    )
    commit = _command_for(
        GlobalCommandKindV1.SELLER_AUCTION_COMMIT,
        "alice",
        1,
        2_121,
        auction_id="auction-cancel",
        bond_asset="USD",
        bond_atoms=5,
        commitment=_root(2_122),
        created_height=10,
        commit_height=10,
        reveal_deadline_height=20,
        settle_deadline_height=30,
    )
    committed = run_m6_transition_v1(subject, state, _context_for(subject, state, "alice", 1, 10), commit)
    assert isinstance(committed, AcceptCandidateV1)
    cancel = _command_for(
        GlobalCommandKindV1.SELLER_AUCTION_CANCEL,
        "alice",
        2,
        2_123,
        auction_id="auction-cancel",
        commitment=_root(2_122),
        created_height=15,
    )
    cancelled = run_m6_transition_v1(
        subject,
        committed.post_state,
        _context_for(subject, committed.post_state, "alice", 2, 15),
        cancel,
    )
    assert isinstance(cancelled, AcceptCandidateV1)
    assert cancelled.post_state.get_atom(EconomicAtomKindV1.BALANCE, "alice", "USD", "ledger") == 10
    assert cancelled.post_state.get_atom(EconomicAtomKindV1.PROTOCOL_RESERVE, "protocol", "USD", "reserve") == 0
    assert cancelled.post_state.seller_auction_bids[0].phase.value == "cancelled"
    assert cancelled.post_state.escrows[0].amount_atoms == 0


def test_sealed_bid_state_rejects_missing_lifecycle_escrow_binding(
    subject: M6PromotionSubjectV1,
) -> None:
    state = replace(
        initial_application_state_v1(subject),
        economic_atoms=(
            EconomicAtomV1(EconomicAtomKindV1.BALANCE, "alice", "USD", "ledger", 10),
        ),
    )
    commit = _command_for(
        GlobalCommandKindV1.SELLER_AUCTION_COMMIT,
        "alice",
        1,
        2_124,
        auction_id="auction-binding",
        bond_asset="USD",
        bond_atoms=5,
        commitment=_root(2_125),
        created_height=10,
        commit_height=10,
        reveal_deadline_height=20,
        settle_deadline_height=30,
    )
    committed = run_m6_transition_v1(subject, state, _context_for(subject, state, "alice", 1, 10), commit)
    assert isinstance(committed, AcceptCandidateV1)
    with pytest.raises(ValueError, match="bind to an escrow"):
        replace(committed.post_state, escrows=())


def test_private_swap_expiry_slashes_non_reveal_bond_after_settle_deadline(
    subject: M6PromotionSubjectV1,
) -> None:
    state = replace(
        initial_application_state_v1(subject),
        economic_atoms=(
            EconomicAtomV1(EconomicAtomKindV1.BALANCE, "alice", "USD", "ledger", 10),
        ),
    )
    commit = _command_for(
        GlobalCommandKindV1.PRIVATE_SWAP_COMMIT,
        "alice",
        1,
        2_131,
        batch_id="batch-expire",
        bond_asset="USD",
        bond_atoms=5,
        commitment=_root(2_132),
        created_height=10,
        commit_height=10,
        reveal_deadline_height=20,
        settle_deadline_height=30,
    )
    committed = run_m6_transition_v1(subject, state, _context_for(subject, state, "alice", 1, 10), commit)
    assert isinstance(committed, AcceptCandidateV1)
    expire = _command_for(
        GlobalCommandKindV1.PRIVATE_SWAP_EXPIRE,
        "keeper",
        1,
        2_133,
        batch_id="batch-expire",
        created_height=31,
    )
    expired = run_m6_transition_v1(
        subject,
        committed.post_state,
        _context_for(subject, committed.post_state, "keeper", 1, 31),
        expire,
    )
    assert isinstance(expired, AcceptCandidateV1)
    assert expired.post_state.get_atom(EconomicAtomKindV1.PROTOCOL_RESERVE, "protocol", "USD", "reserve") == 5
    assert expired.post_state.private_swap_participants[0].phase.value == "expired"
    assert expired.post_state.escrows[0].amount_atoms == 0


def test_private_swap_mount_requires_reciprocal_two_party_clearing_root(
    subject: M6PromotionSubjectV1,
) -> None:
    state = replace(
        initial_application_state_v1(subject),
        economic_atoms=tuple(
            sorted(
                (
                    EconomicAtomV1(EconomicAtomKindV1.BALANCE, "alice", "A", "ledger", 10),
                    EconomicAtomV1(EconomicAtomKindV1.BALANCE, "bob", "B", "ledger", 10),
                    EconomicAtomV1(EconomicAtomKindV1.BALANCE, "alice", "USD", "ledger", 5),
                    EconomicAtomV1(EconomicAtomKindV1.BALANCE, "bob", "USD", "ledger", 5),
                ),
                key=lambda item: item.key,
            )
        ),
    )
    alice_commitment = _private_reveal_commitment("batch-1", "alice", "A", 4, "B", 6, 11)
    bob_commitment = _private_reveal_commitment("batch-1", "bob", "B", 6, "A", 4, 12)
    alice_commit = _command_for(
        GlobalCommandKindV1.PRIVATE_SWAP_COMMIT,
        "alice",
        1,
        2_201,
        batch_id="batch-1",
        bond_asset="USD",
        bond_atoms=2,
        commitment=alice_commitment,
        created_height=10,
        commit_height=10,
        reveal_deadline_height=20,
        settle_deadline_height=30,
    )
    first = run_m6_transition_v1(subject, state, _context_for(subject, state, "alice", 1, 10), alice_commit)
    assert isinstance(first, AcceptCandidateV1)
    bob_commit = _command_for(
        GlobalCommandKindV1.PRIVATE_SWAP_COMMIT,
        "bob",
        1,
        2_202,
        batch_id="batch-1",
        bond_asset="USD",
        bond_atoms=2,
        commitment=bob_commitment,
        created_height=10,
        commit_height=10,
        reveal_deadline_height=20,
        settle_deadline_height=30,
    )
    second = run_m6_transition_v1(
        subject,
        first.post_state,
        _context_for(subject, first.post_state, "bob", 1, 10),
        bob_commit,
    )
    assert isinstance(second, AcceptCandidateV1)
    alice_reveal = _command_for(
        GlobalCommandKindV1.PRIVATE_SWAP_REVEAL,
        "alice",
        2,
        2_203,
        batch_id="batch-1",
        asset_in="A",
        amount_in_atoms=4,
        asset_out="B",
        amount_out_atoms=6,
        nonce=11,
        created_height=15,
    )
    third = run_m6_transition_v1(
        subject,
        second.post_state,
        _context_for(subject, second.post_state, "alice", 2, 15),
        alice_reveal,
    )
    assert isinstance(third, AcceptCandidateV1)
    bob_reveal = _command_for(
        GlobalCommandKindV1.PRIVATE_SWAP_REVEAL,
        "bob",
        2,
        2_204,
        batch_id="batch-1",
        asset_in="B",
        amount_in_atoms=6,
        asset_out="A",
        amount_out_atoms=4,
        nonce=12,
        created_height=15,
    )
    fourth = run_m6_transition_v1(
        subject,
        third.post_state,
        _context_for(subject, third.post_state, "bob", 2, 15),
        bob_reveal,
    )
    assert isinstance(fourth, AcceptCandidateV1)
    rows = fourth.post_state.private_swap_participants
    clearing_root = hash_v1(
        "m6-private-swap-clearing-v1",
        {
            "batch_id": "batch-1",
            "participants": tuple(
                {
                    "trader": row.trader,
                    "commitment": row.commitment,
                    "asset_in": row.asset_in,
                    "amount_in_atoms": row.amount_in_atoms,
                    "asset_out": row.asset_out,
                    "amount_out_atoms": row.amount_out_atoms,
                    "reveal_nonce": row.reveal_nonce,
                }
                for row in sorted(rows, key=lambda item: item.key)
            ),
        },
    )
    forged_settle = _command_for(
        GlobalCommandKindV1.PRIVATE_SWAP_SETTLE,
        "keeper",
        1,
        2_205,
        batch_id="batch-1",
        clearing_root=_root(2_299),
        created_height=25,
    )
    forged = run_m6_transition_v1(
        subject,
        fourth.post_state,
        _context_for(subject, fourth.post_state, "keeper", 1, 25),
        forged_settle,
    )
    assert isinstance(forged, AcceptCandidateV1)
    assert forged.business_status is BusinessStatusV1.REJECTED_COMMITTED
    assert forged.post_state.get_atom(EconomicAtomKindV1.BALANCE, "alice", "A", "ledger") == 10
    assert forged.post_state.get_atom(EconomicAtomKindV1.BALANCE, "bob", "B", "ledger") == 10
    assert all(row.phase.value == "reveal" for row in forged.post_state.private_swap_participants)
    settle = _command_for(
        GlobalCommandKindV1.PRIVATE_SWAP_SETTLE,
        "keeper",
        1,
        2_205,
        batch_id="batch-1",
        clearing_root=clearing_root,
        created_height=25,
    )
    settled = run_m6_transition_v1(
        subject,
        fourth.post_state,
        _context_for(subject, fourth.post_state, "keeper", 1, 25),
        settle,
    )
    assert isinstance(settled, AcceptCandidateV1)
    final = settled.post_state
    assert final.get_atom(EconomicAtomKindV1.BALANCE, "alice", "A", "ledger") == 6
    assert final.get_atom(EconomicAtomKindV1.BALANCE, "alice", "B", "ledger") == 6
    assert final.get_atom(EconomicAtomKindV1.BALANCE, "bob", "A", "ledger") == 4
    assert final.get_atom(EconomicAtomKindV1.BALANCE, "bob", "B", "ledger") == 4
    assert all(row.phase.value == "settle" for row in final.private_swap_participants)


def test_authenticated_business_reject_consumes_nonce_without_value_or_outbox_change(
    subject: M6PromotionSubjectV1,
) -> None:
    state = _state(subject, alice_atoms=1)
    command = _command(
        GlobalCommandKindV1.TAU_WITHDRAWAL,
        1,
        withdrawal_id="w1",
        asset="A",
        amount_atoms=2,
        destination="tau-alice",
    )
    result = run_m6_transition_v1(subject, state, _context(subject, state, 1), command)
    assert isinstance(result, AcceptCandidateV1)
    assert result.business_status is BusinessStatusV1.REJECTED_COMMITTED
    assert result.post_state.get_nonce("alice") == 1
    assert result.post_state.economic_atoms == state.economic_atoms
    assert result.post_state.outbox == state.outbox
    assert result.post_state.history[-1].outcome is BusinessStatusV1.REJECTED_COMMITTED


def test_context_reject_is_exact_no_op(subject: M6PromotionSubjectV1) -> None:
    state = _state(subject, alice_atoms=10)
    command = _command(
        GlobalCommandKindV1.TAU_WITHDRAWAL,
        1,
        withdrawal_id="w1",
        asset="A",
        amount_atoms=2,
        destination="tau-alice",
    )
    stale_context = _context(subject, state, 1, parent_head=_root(999))
    result = run_m6_transition_v1(subject, state, stale_context, command)
    assert isinstance(result, RejectNoCommitV1)
    assert result.reason is AdmissionRejectReasonV1.CONTEXT_PARENT_HEAD_MISMATCH
    assert result.pre_state_root == state.state_root
    assert state.get_nonce("alice") == 0


def test_context_constructor_cannot_authorize_a_tau_withdrawal_without_verifier_witness(
    subject: M6PromotionSubjectV1,
) -> None:
    """RIPR: caller-authored context data cannot reach the value-moving core."""

    state = _state(subject, alice_atoms=3)
    pre_state_root = state.state_root

    with pytest.raises(TypeError, match="verifier-created"):
        AuthenticatedExecutionContextV1(
            deployment=subject.deployment,
            chain_id=subject.chain_id,
            parent_head=state.head,
            epoch=state.writer_epoch,
            sender="alice",
            nonce=1,
            oracle_context=OracleContextV1(_root(100), observed_height=10, oracle_height=10),
            tau_profile=subject.tau_profile,
            verifier_registry=subject.verifier,
            freshness_bounds=FreshnessBoundsV1(2, 2, 2),
        )

    assert state.state_root == pre_state_root
    assert state.get_nonce("alice") == 0


def test_object_new_verifier_approval_cannot_authorize_an_authenticated_context(
    subject: M6PromotionSubjectV1,
) -> None:
    """RIPR: an uninitialized verifier marker cannot cross the context port."""

    claims = M6ExecutionContextClaimsV1(
        deployment=subject.deployment,
        chain_id=subject.chain_id,
        parent_head=ZERO_ROOT_V1,
        epoch=0,
        sender="alice",
        nonce=1,
        oracle_context=OracleContextV1(_root(100), observed_height=0, oracle_height=0),
        tau_profile=subject.tau_profile,
        verifier_registry=subject.verifier,
        freshness_bounds=FreshnessBoundsV1(0, 0, 0),
        ledger_height=0,
    )
    forged_approval = object.__new__(m6_types._M6VerifierApproval)

    with pytest.raises(TypeError, match="verifier approval"):
        AuthenticatedExecutionContextV1._from_verifier(
            claims=claims,
            verification_approval=forged_approval,
        )


def test_object_new_verifier_approval_cannot_authorize_external_evidence(
    subject: M6PromotionSubjectV1,
) -> None:
    """RIPR: the same uninitialized marker cannot mint Tau authority evidence."""

    state = _state(subject)
    command = _command(
        GlobalCommandKindV1.FALLBACK_ACTIVATE,
        1,
        checkpoint_root=state.state_root,
    )
    proof = MigrationAuthorityProofV1(
        kind=MigrationEvidenceKindV1.FALLBACK_LIVENESS,
        checkpoint_root=state.state_root,
        compatible_profile_root=ZERO_ROOT_V1,
        condition_root=_root(9_201),
        source_authority_epoch=state.migration.authority_epoch,
    )
    forged_approval = object.__new__(m6_types._M6VerifierApproval)

    with pytest.raises(TypeError, match="sealed verifier approval"):
        M6AuthorityEvidenceV1(
            forged_approval,
            GlobalCommandKindV1.FALLBACK_ACTIVATE,
            subject.subject_root,
            state.state_root,
            command.command_hash,
            proof,
        )


def test_verifier_construction_tokens_are_not_importable_from_the_value_module(
    subject: M6PromotionSubjectV1,
) -> None:
    """RIPR: private module globals cannot bypass the verifier port."""

    del subject
    assert not hasattr(m6_types, "_M6_EXECUTION_CONTEXT_WITNESS_TOKEN")
    assert not hasattr(m6_types, "_M6_AUTHORITY_EVIDENCE_TOKEN")


def test_external_authority_commands_reject_without_verifier_owned_evidence(
    subject: M6PromotionSubjectV1,
) -> None:
    """AAA/BVE: missing authority evidence is a committed business rejection."""

    # Arrange: each command starts from a clean state so the only boundary
    # under test is the absent verifier witness.
    deposit_state = _state(subject)
    deposit = _command(
        GlobalCommandKindV1.TAU_ESCROW_DEPOSIT,
        1,
        deposit_id="d-missing-evidence",
        asset="A",
        amount_atoms=3,
        tau_transaction_root=_root(701),
        tau_finality_root=_root(702),
        tau_profile_root=subject.tau_profile,
    )

    # Act: a well-formed, authenticated command reaches business evaluation.
    deposit_result = run_m6_transition_v1(
        subject,
        deposit_state,
        _context(subject, deposit_state, 1),
        deposit,
    )

    # Assert: no external credit or escrow is created, while the ingress nonce
    # still records the authenticated command.
    assert isinstance(deposit_result, AcceptCandidateV1)
    assert deposit_result.business_status is BusinessStatusV1.REJECTED_COMMITTED
    assert deposit_result.business_reject_reason is BusinessRejectReasonV1.INVALID_AUTHORITY
    assert deposit_result.post_state.escrows == deposit_state.escrows
    assert deposit_result.post_state.economic_atoms == deposit_state.economic_atoms
    assert deposit_result.post_state.get_nonce("alice") == 1

    fallback_state = _state(subject)
    fallback = _command(
        GlobalCommandKindV1.FALLBACK_ACTIVATE,
        1,
        checkpoint_root=fallback_state.state_root,
    )
    fallback_result = run_m6_transition_v1(
        subject,
        fallback_state,
        _context(subject, fallback_state, 1),
        fallback,
    )
    assert isinstance(fallback_result, AcceptCandidateV1)
    assert fallback_result.business_status is BusinessStatusV1.REJECTED_COMMITTED
    assert fallback_result.business_reject_reason is BusinessRejectReasonV1.INVALID_AUTHORITY
    assert fallback_result.post_state.migration == fallback_state.migration

    rejoin_base = _state(subject)
    rejoin_state = replace(
        rejoin_base,
        writer_epoch=1,
        migration=MigrationStateV1(
            phase=MigrationPhaseV1.FALLBACK,
            authority_epoch=1,
            previous_authority_root=_root(703),
            checkpoint_root=rejoin_base.state_root,
            quiescent=False,
        ),
    )
    rejoin = _command(
        GlobalCommandKindV1.TAU_REJOIN,
        1,
        checkpoint_root=rejoin_state.state_root,
        compatible_profile_root=subject.tau_profile,
    )
    rejoin_result = run_m6_transition_v1(
        subject,
        rejoin_state,
        _context(subject, rejoin_state, 1),
        rejoin,
    )
    assert isinstance(rejoin_result, AcceptCandidateV1)
    assert rejoin_result.business_status is BusinessStatusV1.REJECTED_COMMITTED
    assert rejoin_result.business_reject_reason is BusinessRejectReasonV1.INVALID_AUTHORITY
    assert rejoin_result.post_state.migration == rejoin_state.migration

    withdrawal_state = _state(subject, alice_atoms=10)
    withdrawal = _command(
        GlobalCommandKindV1.TAU_WITHDRAWAL,
        1,
        withdrawal_id="w-missing-ack-evidence",
        asset="A",
        amount_atoms=2,
        destination="tau-alice",
    )
    staged = run_m6_transition_v1(
        subject,
        withdrawal_state,
        _context(subject, withdrawal_state, 1),
        withdrawal,
    )
    assert isinstance(staged, AcceptCandidateV1)
    ack = _command(
        GlobalCommandKindV1.TAU_WITHDRAWAL_ACK,
        2,
        withdrawal_id="w-missing-ack-evidence",
        ack_root=_root(704),
        tau_receipt_root=_root(705),
    )
    ack_result = run_m6_transition_v1(
        subject,
        staged.post_state,
        _context(subject, staged.post_state, 2),
        ack,
    )
    assert isinstance(ack_result, AcceptCandidateV1)
    assert ack_result.business_status is BusinessStatusV1.REJECTED_COMMITTED
    assert ack_result.business_reject_reason is BusinessRejectReasonV1.INVALID_AUTHORITY
    assert ack_result.post_state.withdrawals == staged.post_state.withdrawals
    assert ack_result.post_state.acknowledgments == staged.post_state.acknowledgments


def test_tau_withdrawal_and_acknowledgment_bind_one_pending_outbox(subject: M6PromotionSubjectV1) -> None:
    state = _state(subject, alice_atoms=10)
    withdrawal = _command(
        GlobalCommandKindV1.TAU_WITHDRAWAL,
        1,
        withdrawal_id="w1",
        asset="A",
        amount_atoms=2,
        destination="tau-alice",
    )
    staged = run_m6_transition_v1(subject, state, _context(subject, state, 1), withdrawal)
    assert isinstance(staged, AcceptCandidateV1)
    assert len(staged.post_state.outbox) == 1
    assert staged.post_state.withdrawals[0].status.value == "pending"
    ack = _command(
        GlobalCommandKindV1.TAU_WITHDRAWAL_ACK,
        2,
        withdrawal_id="w1",
        ack_root=_root(777),
        tau_receipt_root=_root(778),
    )
    acknowledged = run_m6_transition_v1(
        subject,
        staged.post_state,
        _with_ack_evidence(subject, staged.post_state, ack, staged.pre_state_root),
        ack,
    )
    assert isinstance(acknowledged, AcceptCandidateV1)
    assert acknowledged.post_state.withdrawals[0].status.value == "acknowledged"
    assert acknowledged.post_state.outbox == staged.post_state.outbox
    assert acknowledged.post_state.acknowledgments[0].provenance_root == staged.pre_state_root


def test_replayed_tau_withdrawal_ack_is_a_committed_noop_for_liability_state(
    subject: M6PromotionSubjectV1,
) -> None:
    """BDD/RIPR: a second ACK cannot clear or recreate an already-settled liability."""

    state = _state(subject, alice_atoms=10)
    withdrawal = _command(
        GlobalCommandKindV1.TAU_WITHDRAWAL,
        1,
        withdrawal_id="w-replay-ack",
        asset="A",
        amount_atoms=2,
        destination="tau-alice",
    )
    staged = run_m6_transition_v1(subject, state, _context(subject, state, 1), withdrawal)
    assert isinstance(staged, AcceptCandidateV1)
    ack = _command(
        GlobalCommandKindV1.TAU_WITHDRAWAL_ACK,
        2,
        withdrawal_id="w-replay-ack",
        ack_root=_root(779),
        tau_receipt_root=_root(780),
    )
    acknowledged = run_m6_transition_v1(
        subject,
        staged.post_state,
        _with_ack_evidence(subject, staged.post_state, ack, staged.pre_state_root),
        ack,
    )
    assert isinstance(acknowledged, AcceptCandidateV1)
    replay = _command(
        GlobalCommandKindV1.TAU_WITHDRAWAL_ACK,
        3,
        withdrawal_id="w-replay-ack",
        ack_root=_root(779),
        tau_receipt_root=_root(780),
    )

    result = run_m6_transition_v1(
        subject,
        acknowledged.post_state,
        _with_ack_evidence(subject, acknowledged.post_state, replay, staged.pre_state_root),
        replay,
    )

    assert isinstance(result, AcceptCandidateV1)
    assert result.business_status is BusinessStatusV1.REJECTED_COMMITTED
    assert result.business_reject_reason is BusinessRejectReasonV1.INVALID_WITHDRAWAL
    assert result.post_state.withdrawals == acknowledged.post_state.withdrawals
    assert result.post_state.acknowledgments == acknowledged.post_state.acknowledgments
    assert result.post_state.outbox == acknowledged.post_state.outbox
    assert result.post_state.get_nonce("alice") == 3


def test_tau_withdrawal_acknowledgment_is_owned_by_requesting_account(
    subject: M6PromotionSubjectV1,
) -> None:
    state = _state(subject, alice_atoms=10)
    withdrawal = _command(
        GlobalCommandKindV1.TAU_WITHDRAWAL,
        1,
        withdrawal_id="w-owned",
        asset="A",
        amount_atoms=2,
        destination="tau-alice",
    )
    staged = run_m6_transition_v1(subject, state, _context(subject, state, 1), withdrawal)
    assert isinstance(staged, AcceptCandidateV1)
    ack = _command_for(
        GlobalCommandKindV1.TAU_WITHDRAWAL_ACK,
        "mallory",
        1,
        6_001,
        withdrawal_id="w-owned",
        ack_root=_root(777),
        tau_receipt_root=_root(778),
    )
    rejected = run_m6_transition_v1(
        subject,
        staged.post_state,
        _with_ack_evidence(subject, staged.post_state, ack, staged.pre_state_root),
        ack,
    )
    assert isinstance(rejected, AcceptCandidateV1)
    assert rejected.business_status is BusinessStatusV1.REJECTED_COMMITTED
    assert rejected.business_reject_reason is BusinessRejectReasonV1.INVALID_WITHDRAWAL
    assert rejected.post_state.withdrawals == staged.post_state.withdrawals


def test_tau_deposit_requires_profile_bound_finality_proof(subject: M6PromotionSubjectV1) -> None:
    state = _state(subject)
    deposit = _command(
        GlobalCommandKindV1.TAU_ESCROW_DEPOSIT,
        1,
        deposit_id="d1",
        asset="A",
        amount_atoms=3,
        tau_transaction_root=_root(701),
        tau_finality_root=_root(702),
        tau_profile_root=subject.tau_profile,
    )
    accepted = run_m6_transition_v1(subject, state, _with_deposit_evidence(subject, state, deposit), deposit)
    assert isinstance(accepted, AcceptCandidateV1)
    assert accepted.post_state.escrows[0].terminal_state.startswith("tau_finalized:")

    wrong_payload = {item.key: item.value for item in deposit.payload}
    wrong_payload["tau_profile_root"] = _root(703)
    wrong_profile = replace(deposit, nonce=2, payload=wrong_payload)
    rejected = run_m6_transition_v1(subject, accepted.post_state, _context(subject, accepted.post_state, 2), wrong_profile)
    assert isinstance(rejected, AcceptCandidateV1)
    assert rejected.business_status is BusinessStatusV1.REJECTED_COMMITTED
    assert rejected.post_state.escrows == accepted.post_state.escrows


def test_duplicate_tau_deposit_is_a_typed_committed_rejection(
    subject: M6PromotionSubjectV1,
) -> None:
    state = _state(subject)
    deposit = _command(
        GlobalCommandKindV1.TAU_ESCROW_DEPOSIT,
        1,
        deposit_id="d-duplicate",
        asset="A",
        amount_atoms=3,
        tau_transaction_root=_root(701),
        tau_finality_root=_root(702),
        tau_profile_root=subject.tau_profile,
    )
    accepted = run_m6_transition_v1(subject, state, _with_deposit_evidence(subject, state, deposit), deposit)
    assert isinstance(accepted, AcceptCandidateV1)
    duplicate = replace(deposit, nonce=2)
    rejected = run_m6_transition_v1(
        subject,
        accepted.post_state,
        _with_deposit_evidence(subject, accepted.post_state, duplicate),
        duplicate,
    )
    assert isinstance(rejected, AcceptCandidateV1)
    assert rejected.business_status is BusinessStatusV1.REJECTED_COMMITTED
    assert rejected.business_reject_reason is BusinessRejectReasonV1.INVALID_ESCROW
    assert rejected.post_state.escrows == accepted.post_state.escrows


def test_fallback_and_rejoin_require_current_phase_and_checkpoint_lineage(
    subject: M6PromotionSubjectV1,
) -> None:
    state = _state(subject)
    fallback = _command(
        GlobalCommandKindV1.FALLBACK_ACTIVATE,
        1,
        checkpoint_root=state.state_root,
    )
    fallback_result = run_m6_transition_v1(
        subject,
        state,
        _with_migration_evidence(subject, state, fallback),
        fallback,
    )
    assert isinstance(fallback_result, AcceptCandidateV1)
    assert fallback_result.business_status is BusinessStatusV1.ACCEPTED

    normal_rejoin = _command(
        GlobalCommandKindV1.TAU_REJOIN,
        1,
        checkpoint_root=fallback_result.post_state.state_root,
        compatible_profile_root=subject.tau_profile,
    )
    invalid_normal_rejoin = run_m6_transition_v1(
        subject,
        state,
        _context(subject, state, 1),
        normal_rejoin,
    )
    assert isinstance(invalid_normal_rejoin, AcceptCandidateV1)
    assert invalid_normal_rejoin.business_status is BusinessStatusV1.REJECTED_COMMITTED
    assert invalid_normal_rejoin.business_reject_reason is BusinessRejectReasonV1.INVALID_AUTHORITY

    unrelated_checkpoint = replace(
        fallback_result.post_state,
        migration=replace(fallback_result.post_state.migration, checkpoint_root=_root(999)),
    )
    invalid_rejoin = run_m6_transition_v1(
        subject,
        unrelated_checkpoint,
        _context(subject, unrelated_checkpoint, 2),
        replace(normal_rejoin, nonce=2),
    )
    assert isinstance(invalid_rejoin, AcceptCandidateV1)
    assert invalid_rejoin.business_status is BusinessStatusV1.REJECTED_COMMITTED
    assert invalid_rejoin.business_reject_reason is BusinessRejectReasonV1.INVALID_AUTHORITY

    valid_rejoin = replace(normal_rejoin, nonce=2, command_id=_root(7_004))
    rejoined = run_m6_transition_v1(
        subject,
        fallback_result.post_state,
        _with_migration_evidence(subject, fallback_result.post_state, valid_rejoin),
        valid_rejoin,
    )
    assert isinstance(rejoined, AcceptCandidateV1)
    assert rejoined.business_status is BusinessStatusV1.ACCEPTED
    assert rejoined.post_state.migration.phase is MigrationPhaseV1.NORMAL


def test_fallback_activation_uses_tau_free_forced_inclusion_finality(
    subject: M6PromotionSubjectV1,
) -> None:
    """BDD/AAA: the NORMAL -> FALLBACK transition can commit during Tau outage."""

    state = _state(subject)
    command = _command(
        GlobalCommandKindV1.FALLBACK_ACTIVATE,
        1,
        checkpoint_root=state.state_root,
    )
    candidate = run_m6_transition_v1(
        subject,
        state,
        _with_migration_evidence(subject, state, command),
        command,
    )
    assert isinstance(candidate, AcceptCandidateV1)
    assert candidate.post_state.migration.phase is MigrationPhaseV1.FALLBACK

    tau = _tau_certificate(subject, candidate, state.head)
    tau_finality = _finality(
        subject,
        candidate.post_state.state_root,
        candidate.publication_atom.publication_root,
        candidate.post_state.writer_epoch,
        tau,
    )
    tau_result = M6CommitPortV1(subject, state, _TEST_FINALITY_VERIFIER).publish(candidate, tau_finality, tau)
    assert tau_result.status is CommitStatusV1.FINALITY_REJECTED
    assert tau_result.state == state

    certificate = ZenoLedgerFinalityCertificateV1(
        finality_id=_root(9_101),
        candidate_head=candidate.post_state.state_root,
        publication_root=candidate.publication_atom.publication_root,
        chain_id=subject.chain_id,
        validator_set_root=subject.validator_set,
        writer_epoch=candidate.post_state.writer_epoch,
        signer_ids=("v1", "v2", "v3", "v4", "v5"),
        quorum=5,
        mode=FinalityModeV1.FALLBACK_FORCED_INCLUSION,
        signature_root=_root(9_102),
    )
    finality = verify_zeno_ledger_finality_v1(
        subject,
        candidate_head=candidate.post_state.state_root,
        publication_root=candidate.publication_atom.publication_root,
        candidate_parent_head=state.head,
        expected_command_root=ordered_root_v1(
            "m6-direct-command-root-v1", (command.command_hash,)
        ),
        expected_nonce_root=ordered_root_v1(
            "m6-direct-nonce-root-v1", (command.nonce_identity,)
        ),
        certificate=certificate,
        tau_certificate=None,
    )

    result = M6CommitPortV1(subject, state, _TEST_FINALITY_VERIFIER).publish(candidate, finality, None)

    assert result.status is CommitStatusV1.COMMITTED
    assert result.state.migration.phase is MigrationPhaseV1.FALLBACK

    rejoin = _command(
        GlobalCommandKindV1.TAU_REJOIN,
        2,
        checkpoint_root=result.state.state_root,
        compatible_profile_root=subject.tau_profile,
    )
    rejoin_candidate = run_m6_transition_v1(
        subject,
        result.state,
        _with_migration_evidence(subject, result.state, rejoin),
        rejoin,
    )
    assert isinstance(rejoin_candidate, AcceptCandidateV1)
    assert rejoin_candidate.post_state.migration.phase is MigrationPhaseV1.NORMAL

    rejoin_tau = _tau_certificate(subject, rejoin_candidate, result.state.head)
    rejoin_tau_finality = _finality(
        subject,
        rejoin_candidate.post_state.state_root,
        rejoin_candidate.publication_atom.publication_root,
        rejoin_candidate.post_state.writer_epoch,
        rejoin_tau,
    )
    rejected_rejoin = M6CommitPortV1(subject, result.state, _TEST_FINALITY_VERIFIER).publish(
        rejoin_candidate,
        rejoin_tau_finality,
        rejoin_tau,
    )
    assert rejected_rejoin.status is CommitStatusV1.FINALITY_REJECTED
    assert rejected_rejoin.state == result.state

    rejoin_certificate = ZenoLedgerFinalityCertificateV1(
        finality_id=_root(9_201),
        candidate_head=rejoin_candidate.post_state.state_root,
        publication_root=rejoin_candidate.publication_atom.publication_root,
        chain_id=subject.chain_id,
        validator_set_root=subject.validator_set,
        writer_epoch=rejoin_candidate.post_state.writer_epoch,
        signer_ids=("v1", "v2", "v3", "v4", "v5"),
        quorum=5,
        mode=FinalityModeV1.FALLBACK_FORCED_INCLUSION,
        signature_root=_root(9_202),
    )
    rejoin_finality = verify_zeno_ledger_finality_v1(
        subject,
        candidate_head=rejoin_candidate.post_state.state_root,
        publication_root=rejoin_candidate.publication_atom.publication_root,
        candidate_parent_head=result.state.head,
        expected_command_root=ordered_root_v1(
            "m6-direct-command-root-v1", (rejoin.command_hash,)
        ),
        expected_nonce_root=ordered_root_v1(
            "m6-direct-nonce-root-v1", (rejoin.nonce_identity,)
        ),
        certificate=rejoin_certificate,
        tau_certificate=None,
    )
    rejoined = M6CommitPortV1(subject, result.state, _TEST_FINALITY_VERIFIER).publish(
        rejoin_candidate,
        rejoin_finality,
        None,
    )
    assert rejoined.status is CommitStatusV1.COMMITTED
    assert rejoined.state.migration.phase is MigrationPhaseV1.NORMAL


def test_oracle_freshness_is_anchored_to_consensus_ledger_height(
    subject: M6PromotionSubjectV1,
) -> None:
    """BVA/RIPR: an old oracle cannot pass because observed height is recent."""

    state = _state(subject, alice_atoms=5)
    command = replace(
        _command(
            GlobalCommandKindV1.ZUSD_BORROW,
            1,
            collateral_asset="A",
            collateral_atoms=1,
            amount_atoms=1,
            vault_id="ledger-anchored-oracle",
        ),
        created_height=1_000,
    )
    context = verify_authenticated_execution_context_v1(
        deployment=subject.deployment,
        chain_id=subject.chain_id,
        parent_head=state.head,
        epoch=state.writer_epoch,
        sender="alice",
        nonce=1,
        oracle_context=OracleContextV1(
            _root(100), observed_height=10, oracle_height=10
        ),
        tau_profile=subject.tau_profile,
        verifier_registry=subject.verifier,
        freshness_bounds=FreshnessBoundsV1(2, 2, 2),
        ledger_height=1_000,
        verifier=_TEST_EXECUTION_CONTEXT_VERIFIER,
    )

    result = run_m6_transition_v1(subject, state, context, command)

    assert isinstance(result, RejectNoCommitV1)
    assert result.reason is AdmissionRejectReasonV1.STALE_ORACLE_CONTEXT
    assert result.pre_state_root == state.state_root
    assert state.get_nonce("alice") == 0


def test_authority_evidence_is_opaque_and_rejects_crossed_bindings(
    subject: M6PromotionSubjectV1,
) -> None:
    state = _state(subject)
    command = _command(
        GlobalCommandKindV1.TAU_ESCROW_DEPOSIT,
        1,
        deposit_id="d-opaque",
        asset="A",
        amount_atoms=3,
        tau_transaction_root=_root(7_001),
        tau_finality_root=_root(7_002),
        tau_profile_root=subject.tau_profile,
    )
    proof = TauEscrowDepositProofV1(
        deposit_id="d-opaque",
        tau_transaction_root=_root(7_001),
        tau_finality_root=_root(7_002),
        tau_profile_root=subject.tau_profile,
        beneficiary="alice",
        asset="A",
        amount_atoms=3,
    )
    evidence_context = _with_deposit_evidence(subject, state, command)

    with pytest.raises(TypeError, match="verifier-created"):
        _context(subject, state, 1, authority_evidence=proof)

    with pytest.raises(TypeError, match="sealed verifier approval"):
        from src.core.m6_safe_mount_v1 import M6AuthorityEvidenceV1

        M6AuthorityEvidenceV1(object(), GlobalCommandKindV1.TAU_ESCROW_DEPOSIT, subject.subject_root, state.state_root, command.command_hash, proof)

    other_state = replace(state, economic_atoms=(EconomicAtomV1(EconomicAtomKindV1.BALANCE, "alice", "A", "ledger", 1),))
    crossed = run_m6_transition_v1(subject, other_state, evidence_context, command)
    assert isinstance(crossed, AcceptCandidateV1)
    assert crossed.business_status is BusinessStatusV1.REJECTED_COMMITTED
    assert crossed.business_reject_reason is BusinessRejectReasonV1.INVALID_AUTHORITY
    assert crossed.post_state.economic_atoms == other_state.economic_atoms

    with pytest.raises(AttributeError, match="immutable"):
        assert evidence_context.authority_evidence is not None
        evidence_context.authority_evidence.kind = GlobalCommandKindV1.TAU_WITHDRAWAL_ACK

    altered_payload = {item.key: item.value for item in command.payload}
    altered_payload["amount_atoms"] = 4
    altered_command = replace(command, payload=altered_payload)
    crossed_command = run_m6_transition_v1(subject, state, evidence_context, altered_command)
    assert isinstance(crossed_command, AcceptCandidateV1)
    assert crossed_command.business_status is BusinessStatusV1.REJECTED_COMMITTED
    assert crossed_command.business_reject_reason is BusinessRejectReasonV1.INVALID_AUTHORITY


def test_external_verifier_rejection_does_not_issue_authority_evidence(
    subject: M6PromotionSubjectV1,
) -> None:
    class RejectingVerifier(_TestAuthorityVerifier):
        def verify_tau_escrow_deposit(self, proof: TauEscrowDepositProofV1, **_: object) -> None:
            raise ValueError("external Tau finality unavailable")

    state = _state(subject)
    command = _command(
        GlobalCommandKindV1.TAU_ESCROW_DEPOSIT,
        1,
        deposit_id="d-verifier-reject",
        asset="A",
        amount_atoms=1,
        tau_transaction_root=_root(7_011),
        tau_finality_root=_root(7_012),
        tau_profile_root=subject.tau_profile,
    )
    proof = TauEscrowDepositProofV1(
        deposit_id="d-verifier-reject",
        tau_transaction_root=_root(7_011),
        tau_finality_root=_root(7_012),
        tau_profile_root=subject.tau_profile,
        beneficiary="alice",
        asset="A",
        amount_atoms=1,
    )
    with pytest.raises(ValueError, match="finality unavailable"):
        verify_tau_escrow_deposit_evidence_v1(
            command,
            proof,
            subject_root=subject.subject_root,
            pre_state_root=state.state_root,
            tau_profile_root=subject.tau_profile,
            verifier=RejectingVerifier(),
        )


def _tau_certificate(subject: M6PromotionSubjectV1, candidate: AcceptCandidateV1, parent_head: str) -> TauBatchCertificateV1:
    hashes = (candidate.command.command_hash,)
    identities = (candidate.command.nonce_identity,)
    root = hash_v1(
        "m6-tau-batch-certificate-v1",
        {
            "batch_id": "b1",
            "tau_profile_root": subject.tau_profile,
            "chain_id": subject.chain_id,
            "ordered_command_hashes": hashes,
            "ordered_nonce_identities": identities,
            "candidate_parent_head": parent_head,
        },
    )
    return TauBatchCertificateV1(
        "b1", subject.tau_profile, subject.chain_id, hashes, identities, parent_head, root
    )


def _finality_certificate(
    subject: M6PromotionSubjectV1,
    candidate_head: str,
    publication_root: str,
    epoch: int,
    *,
    execution_receipt_root: str | None = None,
) -> ZenoLedgerFinalityCertificateV1:
    return ZenoLedgerFinalityCertificateV1(
        finality_id=_root(900),
        candidate_head=candidate_head,
        publication_root=publication_root,
        chain_id=subject.chain_id,
        validator_set_root=subject.validator_set,
        writer_epoch=epoch,
        signer_ids=("v1", "v2", "v3", "v4", "v5"),
        quorum=5,
        mode=FinalityModeV1.TAU_ORDERED,
        signature_root=_root(901),
        execution_receipt_root=execution_receipt_root,
    )


def _finality_receipt(
    subject: M6PromotionSubjectV1,
    certificate: ZenoLedgerFinalityCertificateV1,
    candidate_parent_head: str,
    *,
    expected_writer_epoch: int | None = None,
):
    return _issue_m6_finality_verification_receipt_v1(
        subject_root=subject.subject_root,
        candidate_parent_head=candidate_parent_head,
        candidate_head=certificate.candidate_head,
        publication_root=certificate.publication_root,
        expected_writer_epoch=(
            certificate.writer_epoch
            if expected_writer_epoch is None
            else expected_writer_epoch
        ),
        certificate_root=certificate.certificate_root,
        attestation_root=certificate.signature_root,
    )


class _TestFinalityVerifier:
    """Research fixture for the external finality-verifier port."""

    def verify_finality(self, subject: M6PromotionSubjectV1, **kwargs: object):
        certificate = cast(ZenoLedgerFinalityCertificateV1, kwargs["certificate"])
        return _finality_receipt(
            subject,
            certificate,
            cast(str, kwargs["candidate_parent_head"]),
            expected_writer_epoch=cast(int, kwargs["expected_writer_epoch"]),
        )


_TEST_FINALITY_VERIFIER = _TestFinalityVerifier()


def verify_zeno_ledger_finality_v1(
    subject: M6PromotionSubjectV1,
    **kwargs: object,
) -> VerifiedZenoLedgerFinalityV1:
    """Test adapter standing in for the external cryptographic verifier port."""

    certificate = cast(ZenoLedgerFinalityCertificateV1, kwargs["certificate"])
    parent_head = cast(str, kwargs["candidate_parent_head"])
    expected_epoch = cast(int, kwargs.pop("expected_writer_epoch", certificate.writer_epoch))
    receipt = kwargs.pop("verification_receipt", None)
    if receipt is None:
        receipt = _finality_receipt(
            subject,
            certificate,
            parent_head,
            expected_writer_epoch=expected_epoch,
        )
    return _verify_zeno_ledger_finality_v1(
        subject,
        expected_writer_epoch=expected_epoch,
        verification_receipt=receipt,
        **kwargs,
    )


def _finality(
    subject: M6PromotionSubjectV1,
    candidate_head: str,
    publication_root: str,
    epoch: int,
    tau_certificate: TauBatchCertificateV1,
    *,
    execution_receipt_root: str | None = None,
) -> VerifiedZenoLedgerFinalityV1:
    certificate = _finality_certificate(
        subject,
        candidate_head,
        publication_root,
        epoch,
        execution_receipt_root=execution_receipt_root,
    )
    return verify_zeno_ledger_finality_v1(
        subject,
        candidate_head=candidate_head,
        publication_root=publication_root,
        candidate_parent_head=tau_certificate.candidate_parent_head,
        expected_writer_epoch=epoch,
        expected_command_root=ordered_root_v1(
            "m6-direct-command-root-v1",
            tau_certificate.ordered_command_hashes,
        ),
        expected_nonce_root=ordered_root_v1(
            "m6-direct-nonce-root-v1",
            tau_certificate.ordered_nonce_identities,
        ),
        expected_execution_receipt_root=execution_receipt_root,
        certificate=certificate,
        tau_certificate=tau_certificate,
        verification_receipt=_finality_receipt(
            subject,
            certificate,
            tau_certificate.candidate_parent_head,
        ),
    )


def test_commit_port_requires_five_of_seven_finality_and_is_idempotent(subject: M6PromotionSubjectV1) -> None:
    state = _state(subject, alice_atoms=10)
    command = _command(
        GlobalCommandKindV1.TAU_WITHDRAWAL,
        1,
        withdrawal_id="w1",
        asset="A",
        amount_atoms=2,
        destination="tau-alice",
    )
    candidate = run_m6_transition_v1(subject, state, _context(subject, state, 1), command)
    assert isinstance(candidate, AcceptCandidateV1)
    port = M6CommitPortV1(subject, state, _TEST_FINALITY_VERIFIER)
    with pytest.raises(ValueError, match="quorum"):
        ZenoLedgerFinalityCertificateV1(
            finality_id=_root(902),
            candidate_head=candidate.post_state.state_root,
            publication_root=candidate.publication_atom.publication_root,
            chain_id=subject.chain_id,
            validator_set_root=subject.validator_set,
            writer_epoch=0,
            signer_ids=("v1", "v2", "v3", "v4"),
            quorum=5,
            mode=FinalityModeV1.TAU_ORDERED,
            signature_root=_root(903),
        )
    tau = _tau_certificate(subject, candidate, state.head)
    raw_good = _finality_certificate(
        subject,
        candidate.post_state.state_root,
        candidate.publication_atom.publication_root,
        0,
    )
    raw_result = port.publish(candidate, raw_good, tau)
    assert raw_result.status is CommitStatusV1.FINALITY_REJECTED
    assert raw_result.reason == "finality evidence must be verifier-created"
    assert raw_result.state == state
    good = _finality(
        subject,
        candidate.post_state.state_root,
        candidate.publication_atom.publication_root,
        0,
        tau,
    )
    committed = port.publish(candidate, good, tau)
    assert committed.status is CommitStatusV1.COMMITTED
    assert committed.record is not None
    assert committed.record.value_delta_root == candidate.value_delta.delta_root
    assert committed.record.outbox_atoms == candidate.outbox_atoms
    retry = port.publish(candidate, good, tau)
    assert retry.status is CommitStatusV1.ALREADY_COMMITTED
    assert retry.record == committed.record
    conflicting_certificate = replace(good.certificate, signature_root=_root(904))
    conflicting = verify_zeno_ledger_finality_v1(
        subject,
        candidate_head=candidate.post_state.state_root,
        publication_root=candidate.publication_atom.publication_root,
        candidate_parent_head=state.head,
        expected_command_root=good.expected_command_root,
        expected_nonce_root=good.expected_nonce_root,
        certificate=conflicting_certificate,
        tau_certificate=tau,
    )
    conflict = port.publish(candidate, conflicting, tau)
    assert conflict.status is CommitStatusV1.FINALITY_REJECTED


def test_commit_port_rejects_caller_only_finality_without_external_verifier(
    subject: M6PromotionSubjectV1,
) -> None:
    """RIPR: a caller-minted typed receipt cannot authorize a commit alone."""

    state = _state(subject, alice_atoms=10)
    command = _command(
        GlobalCommandKindV1.TAU_WITHDRAWAL,
        1,
        withdrawal_id="caller-only",
        asset="A",
        amount_atoms=1,
        destination="tau-alice",
    )
    candidate = run_m6_transition_v1(subject, state, _context(subject, state, 1), command)
    assert isinstance(candidate, AcceptCandidateV1)
    tau = _tau_certificate(subject, candidate, state.head)
    finality = _finality(
        subject,
        candidate.post_state.state_root,
        candidate.publication_atom.publication_root,
        0,
        tau,
    )

    result = M6CommitPortV1(subject, state).publish(candidate, finality, tau)

    assert result.status is CommitStatusV1.FINALITY_REJECTED
    assert result.reason == "external finality verifier is unavailable"
    assert result.state == state


@pytest.mark.parametrize(
    ("backend_error", "expected_reason"),
    (
        (RuntimeError("private verifier credential"), "external finality verification failed"),
        (ValueError("private verifier credential"), "external finality verification rejected"),
    ),
)
def test_commit_port_converts_finality_backend_failure_to_no_commit(
    subject: M6PromotionSubjectV1,
    backend_error: Exception,
    expected_reason: str,
) -> None:
    """RIPR: an adapter outage cannot escape or partially publish."""

    class RaisingFinalityVerifier:
        def verify_finality(self, _subject: M6PromotionSubjectV1, **_kwargs: object) -> object:
            raise backend_error

    state = _state(subject, alice_atoms=10)
    command = _command(
        GlobalCommandKindV1.TAU_WITHDRAWAL,
        1,
        withdrawal_id="backend-failure",
        asset="A",
        amount_atoms=1,
        destination="tau-alice",
    )
    candidate = run_m6_transition_v1(subject, state, _context(subject, state, 1), command)
    assert isinstance(candidate, AcceptCandidateV1)
    tau = _tau_certificate(subject, candidate, state.head)
    finality = _finality(
        subject,
        candidate.post_state.state_root,
        candidate.publication_atom.publication_root,
        0,
        tau,
    )

    result = M6CommitPortV1(subject, state, RaisingFinalityVerifier()).publish(candidate, finality, tau)

    assert result.status is CommitStatusV1.FINALITY_REJECTED
    assert result.reason == expected_reason
    assert "credential" not in result.reason
    assert result.state == state


def test_finality_verifier_rejects_foreign_chain_identity_before_publication(
    subject: M6PromotionSubjectV1,
) -> None:
    state = _state(subject, alice_atoms=10)
    command = _command(
        GlobalCommandKindV1.TAU_WITHDRAWAL,
        1,
        withdrawal_id="chain-id-withdrawal",
        asset="A",
        amount_atoms=2,
        destination="tau-alice",
    )
    candidate = run_m6_transition_v1(subject, state, _context(subject, state, 1), command)
    assert isinstance(candidate, AcceptCandidateV1)
    tau = _tau_certificate(subject, candidate, state.head)
    foreign_certificate = replace(
        _finality_certificate(
            subject,
            candidate.post_state.state_root,
            candidate.publication_atom.publication_root,
            0,
        ),
        chain_id=_root(12),
        signature_root=_root(907),
    )

    with pytest.raises(ValueError, match="chain identity"):
        verify_zeno_ledger_finality_v1(
            subject,
            candidate_head=candidate.post_state.state_root,
            publication_root=candidate.publication_atom.publication_root,
            candidate_parent_head=state.head,
            expected_command_root=ordered_root_v1(
                "m6-direct-command-root-v1",
                (command.command_hash,),
            ),
            expected_nonce_root=ordered_root_v1(
                "m6-direct-nonce-root-v1",
                (command.nonce_identity,),
            ),
            certificate=foreign_certificate,
            tau_certificate=tau,
        )

    assert M6CommitPortV1(subject, state, _TEST_FINALITY_VERIFIER).state == state


def test_transition_rejects_context_authenticated_for_foreign_chain(subject: M6PromotionSubjectV1) -> None:
    """BDD/RIPR: a verifier witness for one chain cannot enter another chain."""

    state = _state(subject, alice_atoms=10)
    command = _command(
        GlobalCommandKindV1.TAU_WITHDRAWAL,
        1,
        withdrawal_id="foreign-context-chain",
        asset="A",
        amount_atoms=2,
        destination="tau-alice",
    )
    foreign_subject = replace(subject, chain_id=_root(12))
    foreign_context = _context(foreign_subject, state, 1)

    result = run_m6_transition_v1(subject, state, foreign_context, command)

    assert isinstance(result, RejectNoCommitV1)
    assert result.reason is AdmissionRejectReasonV1.CONTEXT_CHAIN_ID_MISMATCH
    assert result.pre_state_root == state.state_root
    assert state.get_nonce("alice") == 0


def test_external_chain_identity_codec_is_deterministic_and_drift_sensitive() -> None:
    """BVA/RIPR: textual ledger identity has one explicit M6 root codec."""

    chain_id = "zeno-ledger-devnet-0"
    root = m6_chain_id_root_from_external_v1(chain_id)

    assert root == m6_chain_id_root_from_external_v1(chain_id)
    assert root != m6_chain_id_root_from_external_v1("zeno-ledger-devnet-1")
    with pytest.raises(ValueError, match="external chain id"):
        m6_chain_id_root_from_external_v1("")


def test_finality_rejects_tau_nonce_identity_swap(subject: M6PromotionSubjectV1) -> None:
    """RIPR/BVA: Tau nonce identities must match the candidate nonce root."""

    state = _state(subject, alice_atoms=10)
    command = _command(
        GlobalCommandKindV1.TAU_WITHDRAWAL,
        1,
        withdrawal_id="tau-nonce-mutant",
        asset="A",
        amount_atoms=2,
        destination="tau-alice",
    )
    candidate = run_m6_transition_v1(subject, state, _context(subject, state, 1), command)
    assert isinstance(candidate, AcceptCandidateV1)
    tau = _tau_certificate(subject, candidate, state.head)
    swapped_identities = ("mallory:999",)
    swapped_tau = replace(
        tau,
        ordered_nonce_identities=swapped_identities,
        certificate_root=hash_v1(
            "m6-tau-batch-certificate-v1",
            {
                "batch_id": tau.batch_id,
                "tau_profile_root": tau.tau_profile_root,
                "chain_id": tau.chain_id,
                "ordered_command_hashes": tau.ordered_command_hashes,
                "ordered_nonce_identities": swapped_identities,
                "candidate_parent_head": tau.candidate_parent_head,
            },
        ),
    )

    with pytest.raises(ValueError, match="nonce binding"):
        verify_zeno_ledger_finality_v1(
            subject,
            candidate_head=candidate.post_state.state_root,
            publication_root=candidate.publication_atom.publication_root,
            candidate_parent_head=state.head,
            expected_command_root=ordered_root_v1(
                "m6-direct-command-root-v1",
                (command.command_hash,),
            ),
            expected_nonce_root=ordered_root_v1(
                "m6-direct-nonce-root-v1",
                (command.nonce_identity,),
            ),
            certificate=_finality_certificate(
                subject,
                candidate.post_state.state_root,
                candidate.publication_atom.publication_root,
                state.writer_epoch,
            ),
            tau_certificate=swapped_tau,
        )


def test_commit_port_rejects_verifier_handle_with_crossed_parent_binding(
    subject: M6PromotionSubjectV1,
) -> None:
    # Arrange: use a fresh writer epoch so fallback finality is structurally
    # admissible, then bind the opaque handle to a foreign parent head.
    initial = initial_application_state_v1(subject)
    state = replace(
        initial,
        writer_epoch=1,
        migration=replace(
            initial.migration,
            phase=MigrationPhaseV1.FALLBACK,
            authority_epoch=1,
        ),
    )
    command = _command(GlobalCommandKindV1.SELLER_AUCTION_CANCEL, 1, auction_id="missing")
    candidate = run_m6_transition_v1(subject, state, _context(subject, state, 1), command)
    assert isinstance(candidate, AcceptCandidateV1)
    certificate = ZenoLedgerFinalityCertificateV1(
        finality_id=_root(905),
        candidate_head=candidate.post_state.state_root,
        publication_root=candidate.publication_atom.publication_root,
        chain_id=subject.chain_id,
        validator_set_root=subject.validator_set,
        writer_epoch=1,
        signer_ids=("v1", "v2", "v3", "v4", "v5"),
        quorum=5,
        mode=FinalityModeV1.FALLBACK_FORCED_INCLUSION,
        signature_root=_root(906),
    )
    crossed = verify_zeno_ledger_finality_v1(
        subject,
        candidate_head=candidate.post_state.state_root,
        publication_root=candidate.publication_atom.publication_root,
        candidate_parent_head=_root(999),
        expected_command_root=ordered_root_v1(
            "m6-direct-command-root-v1",
            (command.command_hash,),
        ),
        expected_nonce_root=ordered_root_v1(
            "m6-direct-nonce-root-v1",
            (command.nonce_identity,),
        ),
        certificate=certificate,
        tau_certificate=None,
    )

    # Act: attempt to publish with the verifier-created but misbound handle.
    result = M6CommitPortV1(subject, state, _TEST_FINALITY_VERIFIER).publish(candidate, crossed, None)

    # Assert: metadata binding is part of publication authority.
    assert result.status is CommitStatusV1.FINALITY_REJECTED
    assert result.reason == "finality evidence parent head mismatch"
    assert result.state == state


def test_commit_port_rejects_fallback_replay_with_mutated_nonce_root(
    subject: M6PromotionSubjectV1,
) -> None:
    """RIPR/BVA: already-committed fallback evidence remains nonce-bound."""

    initial = initial_application_state_v1(subject)
    state = replace(
        initial,
        writer_epoch=1,
        migration=replace(
            initial.migration,
            phase=MigrationPhaseV1.FALLBACK,
            authority_epoch=1,
        ),
    )
    command = _command(GlobalCommandKindV1.SELLER_AUCTION_CANCEL, 1, auction_id="missing")
    candidate = run_m6_transition_v1(subject, state, _context(subject, state, 1), command)
    assert isinstance(candidate, AcceptCandidateV1)
    certificate = ZenoLedgerFinalityCertificateV1(
        finality_id=_root(907),
        candidate_head=candidate.post_state.state_root,
        publication_root=candidate.publication_atom.publication_root,
        chain_id=subject.chain_id,
        validator_set_root=subject.validator_set,
        writer_epoch=1,
        signer_ids=("v1", "v2", "v3", "v4", "v5"),
        quorum=5,
        mode=FinalityModeV1.FALLBACK_FORCED_INCLUSION,
        signature_root=_root(908),
    )
    nonce_root = ordered_root_v1("m6-direct-nonce-root-v1", (command.nonce_identity,))
    finality = verify_zeno_ledger_finality_v1(
        subject,
        candidate_head=candidate.post_state.state_root,
        publication_root=candidate.publication_atom.publication_root,
        candidate_parent_head=state.head,
        expected_command_root=ordered_root_v1(
            "m6-direct-command-root-v1",
            (command.command_hash,),
        ),
        expected_nonce_root=nonce_root,
        certificate=certificate,
        tau_certificate=None,
    )
    port = M6CommitPortV1(subject, state, _TEST_FINALITY_VERIFIER)
    committed = port.publish(candidate, finality, None)
    assert committed.status is CommitStatusV1.COMMITTED

    mutated = verify_zeno_ledger_finality_v1(
        subject,
        candidate_head=candidate.post_state.state_root,
        publication_root=candidate.publication_atom.publication_root,
        candidate_parent_head=state.head,
        expected_command_root=finality.expected_command_root,
        expected_nonce_root=_root(909),
        certificate=certificate,
        tau_certificate=None,
    )
    replay = port.publish(candidate, mutated, None)
    assert replay.status is CommitStatusV1.FINALITY_REJECTED
    assert replay.reason == "finality evidence nonce root mismatch"


def test_fallback_finality_rejects_attached_tau_certificate(
    subject: M6PromotionSubjectV1,
) -> None:
    """BDD/BVA: fallback authority cannot carry Tau-normal-lane evidence."""

    initial = initial_application_state_v1(subject)
    state = replace(
        initial,
        writer_epoch=1,
        migration=replace(
            initial.migration,
            phase=MigrationPhaseV1.FALLBACK,
            authority_epoch=1,
        ),
    )
    command = _command(GlobalCommandKindV1.SELLER_AUCTION_CANCEL, 1, auction_id="fallback-mode")
    candidate = run_m6_transition_v1(subject, state, _context(subject, state, 1), command)
    assert isinstance(candidate, AcceptCandidateV1)
    tau = _tau_certificate(subject, candidate, state.head)
    fallback_certificate = ZenoLedgerFinalityCertificateV1(
        finality_id=_root(910),
        candidate_head=candidate.post_state.state_root,
        publication_root=candidate.publication_atom.publication_root,
        chain_id=subject.chain_id,
        validator_set_root=subject.validator_set,
        writer_epoch=1,
        signer_ids=("v1", "v2", "v3", "v4", "v5"),
        quorum=5,
        mode=FinalityModeV1.FALLBACK_FORCED_INCLUSION,
        signature_root=_root(911),
    )

    with pytest.raises(ValueError, match="fallback finality forbids"):
        verify_zeno_ledger_finality_v1(
            subject,
            candidate_head=candidate.post_state.state_root,
            publication_root=candidate.publication_atom.publication_root,
            candidate_parent_head=state.head,
            expected_command_root=ordered_root_v1(
                "m6-direct-command-root-v1",
                (command.command_hash,),
            ),
            expected_nonce_root=ordered_root_v1(
                "m6-direct-nonce-root-v1",
                (command.nonce_identity,),
            ),
            certificate=fallback_certificate,
            tau_certificate=tau,
        )


def test_commit_port_rejects_forged_candidate_body_on_already_committed_id(
    subject: M6PromotionSubjectV1,
) -> None:
    # Arrange: commit one candidate, then retain its finality evidence while
    # mutating the candidate body under the same caller-supplied identity.
    state = _state(subject, alice_atoms=10)
    command = _command(
        GlobalCommandKindV1.TAU_WITHDRAWAL,
        1,
        withdrawal_id="w1",
        asset="A",
        amount_atoms=2,
        destination="tau-alice",
    )
    candidate = run_m6_transition_v1(subject, state, _context(subject, state, 1), command)
    assert isinstance(candidate, AcceptCandidateV1)
    port = M6CommitPortV1(subject, state, _TEST_FINALITY_VERIFIER)
    tau = _tau_certificate(subject, candidate, state.head)
    finality = _finality(
        subject,
        candidate.post_state.state_root,
        candidate.publication_atom.publication_root,
        0,
        tau,
    )
    committed = port.publish(candidate, finality, tau)
    assert committed.status is CommitStatusV1.COMMITTED

    forged = replace(
        candidate,
        outbox_atoms=(),
    )

    # Act: replay the forged body with the original finality and Tau receipt.
    result = port.publish(forged, finality, tau)

    # Assert: the stored publication remains unchanged and the forged replay
    # cannot obtain an idempotent success.
    assert result.status is CommitStatusV1.FINALITY_REJECTED
    assert result.reason is not None and "replay candidate" in result.reason
    assert "outbox atoms" in result.reason
    assert port.state == committed.state


def test_commit_port_rejects_forged_history_archive_on_already_committed_id(
    subject: M6PromotionSubjectV1,
) -> None:
    state = _state(subject, alice_atoms=10)
    command = _command(
        GlobalCommandKindV1.TAU_WITHDRAWAL,
        1,
        withdrawal_id="w-history",
        asset="A",
        amount_atoms=2,
        destination="tau-alice",
    )
    candidate = run_m6_transition_v1(subject, state, _context(subject, state, 1), command)
    assert isinstance(candidate, AcceptCandidateV1)
    port = M6CommitPortV1(subject, state, _TEST_FINALITY_VERIFIER)
    tau = _tau_certificate(subject, candidate, state.head)
    finality = _finality(
        subject,
        candidate.post_state.state_root,
        candidate.publication_atom.publication_root,
        0,
        tau,
    )
    committed = port.publish(candidate, finality, tau)
    assert committed.status is CommitStatusV1.COMMITTED

    forged = replace(candidate, post_state=replace(candidate.post_state, history=()))
    result = port.publish(forged, finality, tau)

    assert result.status is CommitStatusV1.FINALITY_REJECTED
    assert result.reason is not None and "history root cache mismatch" in result.reason
    assert port.state == committed.state


def test_commit_port_finality_preserves_sealed_bid_lifecycle_rows(
    subject: M6PromotionSubjectV1,
) -> None:
    state = replace(
        initial_application_state_v1(subject),
        economic_atoms=(EconomicAtomV1(EconomicAtomKindV1.BALANCE, "alice", "USD", "ledger", 10),),
    )
    commitment = _root(5_001)
    commit = _command_for(
        GlobalCommandKindV1.SELLER_AUCTION_COMMIT,
        "alice",
        1,
        5_002,
        auction_id="auction-publication",
        bond_asset="USD",
        bond_atoms=5,
        commitment=commitment,
        created_height=10,
        commit_height=10,
        reveal_deadline_height=20,
        settle_deadline_height=30,
    )
    candidate = run_m6_transition_v1(
        subject,
        state,
        _context_for(subject, state, "alice", 1, 10),
        commit,
    )
    assert isinstance(candidate, AcceptCandidateV1)
    finality = _finality(
        subject,
        candidate.post_state.state_root,
        candidate.publication_atom.publication_root,
        0,
        _tau_certificate(subject, candidate, state.head),
    )
    result = M6CommitPortV1(subject, state, _TEST_FINALITY_VERIFIER).publish(
        candidate,
        finality,
        _tau_certificate(subject, candidate, state.head),
    )
    assert result.status is CommitStatusV1.COMMITTED
    assert result.state.seller_auction_bids == candidate.post_state.seller_auction_bids
    assert result.state.private_swap_participants == candidate.post_state.private_swap_participants
    assert result.state.state_root == candidate.post_state.state_root


def test_direct_commit_replays_the_authenticated_candidate_before_publication(
    subject: M6PromotionSubjectV1,
) -> None:
    state = _state(subject)
    command = _command(GlobalCommandKindV1.SELLER_AUCTION_CANCEL, 1, auction_id="missing")
    genuine = run_m6_transition_v1(subject, state, _context(subject, state, 1), command)
    assert isinstance(genuine, AcceptCandidateV1)
    assert genuine.business_status is BusinessStatusV1.REJECTED_COMMITTED

    forged_base = replace(
        genuine.post_state,
        economic_atoms=(EconomicAtomV1(EconomicAtomKindV1.BALANCE, "mallory", "GOLD", "ledger", 999),),
        history=(),
        nullifiers=(),
        head="0x" + "00" * 32,
        history_root_cache=None,
        nullifier_root_cache=None,
        outbox_root_cache=None,
    )
    forged_root = forged_base.state_root
    delta = ValueDeltaCertificateV1(
        command_hash=command.command_hash,
        pre_state_root=state.state_root,
        post_state_root=forged_root,
        entries=(),
        delta_root=hash_v1(
            "m6-value-delta-certificate-v1",
            {
                "command_hash": command.command_hash,
                "pre_state_root": state.state_root,
                "post_state_root": forged_root,
                "entries": (),
            },
        ),
    )
    history_atom = replace(
        genuine.history_atom,
        post_state_root=forged_root,
        value_delta_root=delta.delta_root,
    )
    forged_post_state = replace(
        forged_base,
        head=forged_root,
        history=(history_atom,),
        nullifiers=(history_atom.nullifier,),
        history_root_cache=None,
        nullifier_root_cache=None,
        outbox_root_cache=None,
    )
    candidate_id = hash_v1(
        "m6-candidate-id-v1",
        {
            "command_hash": command.command_hash,
            "pre_state_root": state.state_root,
            "post_state_root": forged_root,
        },
    )
    publication = PublicationAtomV1(
        candidate_id=candidate_id,
        pre_state_root=state.state_root,
        post_state_root=forged_root,
        history_root=forged_post_state.history_root,
        nullifier_root=forged_post_state.nullifier_root,
        value_delta_root=delta.delta_root,
        outbox_root=forged_post_state.outbox_root,
        execution_context_root=genuine.context.authentication_root,
        writer_epoch=forged_post_state.writer_epoch,
        business_status=BusinessStatusV1.REJECTED_COMMITTED,
        business_reject_reason=BusinessRejectReasonV1.INVALID_PHASE,
    )
    forged = AcceptCandidateV1(
        context=genuine.context,
        command=command,
        pre_state_root=state.state_root,
        post_state=forged_post_state,
        value_delta=delta,
        history_atom=history_atom,
        publication_atom=publication,
        outbox_atoms=(),
        business_status=BusinessStatusV1.REJECTED_COMMITTED,
        business_reject_reason=BusinessRejectReasonV1.INVALID_PHASE,
    )
    finality = _finality(
        subject,
        forged.post_state.state_root,
        forged.publication_atom.publication_root,
        0,
        _tau_certificate(subject, forged, state.head),
    )
    result = M6CommitPortV1(subject, state, _TEST_FINALITY_VERIFIER).publish(
        forged,
        finality,
        finality.tau_certificate,
    )
    assert result.status is CommitStatusV1.FINALITY_REJECTED
    assert result.state == state
    assert result.reason is not None and "replay" in result.reason


def test_lp_add_rejects_caller_minted_share_amounts(subject: M6PromotionSubjectV1) -> None:
    state = _state(subject, alice_atoms=1)
    command = _command(
        GlobalCommandKindV1.LP_ADD,
        1,
        asset="A",
        amount_atoms=1,
        pool="pool",
        lp_shares_atoms=10**30,
    )
    result = run_m6_transition_v1(subject, state, _context(subject, state, 1), command)
    assert isinstance(result, AcceptCandidateV1)
    assert result.business_status is BusinessStatusV1.REJECTED_COMMITTED
    assert result.business_reject_reason is BusinessRejectReasonV1.INVALID_AMOUNT
    assert result.post_state.get_atom(EconomicAtomKindV1.LP_SHARE, "alice", "pool", "lp") == 0
    assert result.post_state.get_atom(EconomicAtomKindV1.BALANCE, "alice", "A", "ledger") == 1


def test_perp_close_rejects_unfunded_positive_pnl(subject: M6PromotionSubjectV1) -> None:
    state = replace(
        initial_application_state_v1(subject),
        economic_atoms=tuple(
            sorted(
                (
                    EconomicAtomV1(EconomicAtomKindV1.MARGIN, "alice", "BTC", "perp", 1),
                    EconomicAtomV1(EconomicAtomKindV1.POSITION, "alice", "BTC", "perp", 1),
                    EconomicAtomV1(EconomicAtomKindV1.POSITION_ENTRY_PRICE, "alice", "BTC", "perp:e8", 100),
                ),
                key=lambda item: item.key,
            )
        ),
    )
    command = _command(GlobalCommandKindV1.PERP_CLOSE, 1, market="BTC", size_atoms=1, pnl_atoms=100)
    result = run_m6_transition_v1(subject, state, _context(subject, state, 1), command)
    assert isinstance(result, AcceptCandidateV1)
    assert result.business_status is BusinessStatusV1.REJECTED_COMMITTED
    assert result.business_reject_reason is BusinessRejectReasonV1.UNSUPPORTED_OPERATION
    assert result.post_state.get_atom(EconomicAtomKindV1.MARGIN, "alice", "BTC", "perp") == 1
    assert result.post_state.get_atom(EconomicAtomKindV1.BALANCE, "alice", "zUSD", "ledger") == 0


def test_perp_liquidation_rejects_unfunded_insurance_transfer(
    subject: M6PromotionSubjectV1,
) -> None:
    state = replace(
        initial_application_state_v1(subject),
        economic_atoms=tuple(
            sorted(
                (
                    EconomicAtomV1(EconomicAtomKindV1.MARGIN, "alice", "BTC", "perp", 1),
                    EconomicAtomV1(EconomicAtomKindV1.POSITION, "alice", "BTC", "perp", 1),
                    EconomicAtomV1(EconomicAtomKindV1.POSITION_ENTRY_PRICE, "alice", "BTC", "perp:e8", 100),
                ),
                key=lambda item: item.key,
            )
        ),
    )
    command = _command(
        GlobalCommandKindV1.PERP_LIQUIDATE,
        1,
        market="BTC",
        margin_atoms=1,
        insurance_atoms=1,
    )
    result = run_m6_transition_v1(subject, state, _context(subject, state, 1), command)
    assert isinstance(result, AcceptCandidateV1)
    assert result.business_status is BusinessStatusV1.REJECTED_COMMITTED
    assert result.business_reject_reason is BusinessRejectReasonV1.UNSUPPORTED_OPERATION
    assert result.post_state.get_atom(EconomicAtomKindV1.MARGIN, "alice", "BTC", "perp") == 1
    assert result.post_state.get_atom(EconomicAtomKindV1.INSURANCE, "insurance", "BTC", "perp") == 0


def test_perp_liquidation_rejects_partial_margin_release(
    subject: M6PromotionSubjectV1,
) -> None:
    # Arrange: a full position has two margin atoms committed to the perp
    # custody, while the command tries to release only one.
    state = replace(
        initial_application_state_v1(subject),
        economic_atoms=tuple(
            sorted(
                (
                    EconomicAtomV1(EconomicAtomKindV1.MARGIN, "alice", "BTC", "perp", 2),
                    EconomicAtomV1(EconomicAtomKindV1.POSITION, "alice", "BTC", "perp", 1),
                    EconomicAtomV1(EconomicAtomKindV1.BALANCE, "perp:BTC", "zUSD", "ledger", 1),
                ),
                key=lambda item: item.key,
            )
        ),
    )

    # Act: submit a partial liquidation at the margin boundary.
    result = run_m6_transition_v1(
        subject,
        state,
        _context(subject, state, 1),
        _command(
            GlobalCommandKindV1.PERP_LIQUIDATE,
            1,
            market="BTC",
            margin_atoms=1,
            insurance_atoms=1,
        ),
    )

    # Assert: no orphan margin remains after a rejected lifecycle transition.
    assert isinstance(result, AcceptCandidateV1)
    assert result.business_status is BusinessStatusV1.REJECTED_COMMITTED
    assert result.business_reject_reason is BusinessRejectReasonV1.UNSUPPORTED_OPERATION
    assert result.post_state.economic_atoms == state.economic_atoms


def test_oracle_submit_is_disabled_without_reporter_authority(
    subject: M6PromotionSubjectV1,
) -> None:
    # Arrange: the caller has enough balance, but no subject-bound reporter
    # registry or observation proof exists in this reference profile.
    state = replace(
        initial_application_state_v1(subject),
        economic_atoms=(EconomicAtomV1(EconomicAtomKindV1.BALANCE, "alice", "zUSD", "ledger", 2),),
    )
    command = _command(
        GlobalCommandKindV1.ORACLE_SUBMIT,
        1,
        oracle_id="btc-usd",
        price_e8=1,
        bond_atoms=1,
    )

    # Act: submit a syntactically valid observation.
    rejected = run_m6_transition_v1(subject, state, _context(subject, state, 1), command)

    # Assert: no caller-selected global price or bond movement is accepted.
    assert isinstance(rejected, AcceptCandidateV1)
    assert rejected.business_status is BusinessStatusV1.REJECTED_COMMITTED
    assert rejected.business_reject_reason is BusinessRejectReasonV1.UNSUPPORTED_OPERATION
    assert rejected.post_state.economic_atoms == state.economic_atoms


def test_oracle_dispute_is_disabled_until_adjudication_evidence_is_typed(
    subject: M6PromotionSubjectV1,
) -> None:
    # Arrange: a well-formed dispute command still lacks an adjudication
    # witness, bond ownership policy, and terminal outcome policy.
    state = replace(
        initial_application_state_v1(subject),
        economic_atoms=(EconomicAtomV1(EconomicAtomKindV1.BALANCE, "alice", "zUSD", "ledger", 1),),
    )

    # Act: submit the command at the typed boundary.
    assert GlobalCommandKindV1.ORACLE_DISPUTE in M6_RESEARCH_DISABLED_COMMANDS_V1
    assert GlobalCommandKindV1.ORACLE_DISPUTE not in M6_RESEARCH_ENABLED_COMMANDS_V1
    result = run_m6_transition_v1(
        subject,
        state,
        _context(subject, state, 1),
        _command(GlobalCommandKindV1.ORACLE_DISPUTE, 1, oracle_id="btc-usd", bond_atoms=1),
    )

    # Assert: the incomplete feature consumes its ingress nonce only after
    # canonical admission and creates no value or oracle effect.
    assert isinstance(result, AcceptCandidateV1)
    assert result.business_status is BusinessStatusV1.REJECTED_COMMITTED
    assert result.business_reject_reason is BusinessRejectReasonV1.UNSUPPORTED_OPERATION
    assert result.post_state.economic_atoms == state.economic_atoms


def test_protocol_buy_and_burn_is_disabled_until_owning_kernel_is_typed(
    subject: M6PromotionSubjectV1,
) -> None:
    """BDD/AAA: arbitrary reserve/supply mutation cannot be a launch operation.

    The M6 state has no typed protocol-asset identity, purchase execution
    evidence, or owning burn kernel.  Until those contracts exist, the command
    must commit only its ingress failure record.
    """

    # Arrange: give the untyped handler enough reserve and supply to mutate.
    state = replace(
        initial_application_state_v1(subject),
        economic_atoms=tuple(
            sorted(
                (
                    EconomicAtomV1(
                        EconomicAtomKindV1.PROTOCOL_RESERVE,
                        "protocol",
                        "PROTO",
                        "reserve",
                        10,
                    ),
                    EconomicAtomV1(
                        EconomicAtomKindV1.SUPPLY,
                        "__supply__",
                        "PROTO",
                        "ledger",
                        10,
                    ),
                ),
                key=lambda item: item.key,
            )
        ),
    )
    command = _command(
        GlobalCommandKindV1.PROTOCOL_BUY_AND_BURN,
        1,
        asset="PROTO",
        amount_atoms=1,
    )

    # Act: submit the command through the authoritative transition.
    context = _context(subject, state, 1)
    result = run_m6_transition_v1(subject, state, context, command)

    # Assert: no arbitrary reserve or supply mutation is accepted.
    _assert_committed_rejection_contract_v1(
        state,
        context,
        command,
        result,
        BusinessRejectReasonV1.UNSUPPORTED_OPERATION,
    )
    assert result.post_state.economic_atoms == state.economic_atoms
    assert GlobalCommandKindV1.PROTOCOL_BUY_AND_BURN in M6_RESEARCH_DISABLED_COMMANDS_V1
    assert GlobalCommandKindV1.PROTOCOL_BUY_AND_BURN not in M6_RESEARCH_ENABLED_COMMANDS_V1


@pytest.mark.parametrize(
    ("asset", "amount_atoms"),
    (
        ("zUSD", -1),
        ("zUSD", 0),
        ("zUSD", 1),
        ("ZDEX", 10),
        ("fee-token", MAX_ATOMS_V1),
        ("arbitrary-token", MAX_ATOMS_V1 - 1),
    ),
    ids=lambda value: str(value),
)
def test_protocol_buy_and_burn_bva_is_disabled_without_any_value_effect(
    subject: M6PromotionSubjectV1,
    asset: str,
    amount_atoms: int,
) -> None:
    """BVA: disabled commands reject across assets and amount boundaries."""

    seed_amount = max(abs(amount_atoms), 1)
    state = replace(
        initial_application_state_v1(subject),
        economic_atoms=tuple(
            sorted(
                (
                    EconomicAtomV1(
                        EconomicAtomKindV1.PROTOCOL_RESERVE,
                        "protocol",
                        asset,
                        "reserve",
                        seed_amount,
                    ),
                    EconomicAtomV1(
                        EconomicAtomKindV1.SUPPLY,
                        "__supply__",
                        asset,
                        "ledger",
                        seed_amount,
                    ),
                ),
                key=lambda item: item.key,
            )
        ),
    )
    command = _command(
        GlobalCommandKindV1.PROTOCOL_BUY_AND_BURN,
        1,
        asset=asset,
        amount_atoms=amount_atoms,
    )
    context = _context(subject, state, 1)

    result = run_m6_transition_v1(subject, state, context, command)

    _assert_committed_rejection_contract_v1(
        state,
        context,
        command,
        result,
        BusinessRejectReasonV1.UNSUPPORTED_OPERATION,
    )
    assert result.post_state.economic_atoms == state.economic_atoms


def test_protocol_buy_and_burn_overflow_is_admission_reject_and_max_is_committed_failure(
    subject: M6PromotionSubjectV1,
) -> None:
    """BVA: overflow cannot enter the batch; the valid max remains replayable."""

    state = _state(subject)
    context = _context(subject, state, 1)
    pre_state_root = state.state_root

    with pytest.raises(ValueError, match="128-bit atom domain"):
        _command(
            GlobalCommandKindV1.PROTOCOL_BUY_AND_BURN,
            1,
            asset="PROTO",
            amount_atoms=MAX_ATOMS_V1 + 1,
        )

    # The malformed boundary fails before a typed command exists and cannot
    # consume the sender's nonce or alter the state snapshot.
    assert state.state_root == pre_state_root
    assert state.get_nonce("alice") == 0

    valid_max = _command(
        GlobalCommandKindV1.PROTOCOL_BUY_AND_BURN,
        1,
        asset="PROTO",
        amount_atoms=MAX_ATOMS_V1,
    )
    result = run_m6_transition_v1(subject, state, context, valid_max)
    _assert_committed_rejection_contract_v1(
        state,
        context,
        valid_max,
        result,
        BusinessRejectReasonV1.UNSUPPORTED_OPERATION,
    )


def test_protocol_buy_and_burn_committed_failure_publishes_and_replays_once(
    subject: M6PromotionSubjectV1,
) -> None:
    """The shell persists a business failure's nonce and replay identity once."""

    state = _state(subject)
    command = _command(
        GlobalCommandKindV1.PROTOCOL_BUY_AND_BURN,
        1,
        asset="PROTO",
        amount_atoms=1,
    )
    context = _context(subject, state, 1)
    candidate = run_m6_transition_v1(subject, state, context, command)
    _assert_committed_rejection_contract_v1(
        state,
        context,
        command,
        candidate,
        BusinessRejectReasonV1.UNSUPPORTED_OPERATION,
    )
    assert isinstance(candidate, AcceptCandidateV1)

    tau = _tau_certificate(subject, candidate, state.head)
    finality = _finality(
        subject,
        candidate.post_state.state_root,
        candidate.publication_atom.publication_root,
        0,
        tau,
    )
    port = M6CommitPortV1(subject, state, _TEST_FINALITY_VERIFIER)

    committed = port.publish(candidate, finality, tau)

    assert committed.status is CommitStatusV1.COMMITTED
    assert committed.state == replace(
        candidate.post_state,
        finality_certificates=(finality.certificate,),
    )
    assert committed.state.get_nonce("alice") == 1
    assert len(committed.state.history) == len(state.history) + 1
    assert committed.state.nullifiers[-1] == candidate.history_atom.nullifier
    assert committed.record is not None
    assert committed.record.value_delta_root == candidate.value_delta.delta_root
    assert committed.record.outbox_atoms == ()

    retry = port.publish(candidate, finality, tau)

    assert retry.status is CommitStatusV1.ALREADY_COMMITTED

    # Mutating the business decision under the same candidate identity must
    # never turn a committed rejection into an idempotent success.
    with pytest.raises(ValueError, match="history business reject reason mismatch"):
        replace(candidate, business_reject_reason=BusinessRejectReasonV1.INVALID_AMOUNT)

    forged = replace(
        candidate,
        history_atom=replace(
            candidate.history_atom,
            outcome=BusinessStatusV1.ACCEPTED,
            business_reject_reason=None,
        ),
        publication_atom=replace(
            candidate.publication_atom,
            business_status=BusinessStatusV1.ACCEPTED,
            business_reject_reason=None,
        ),
        business_status=BusinessStatusV1.ACCEPTED,
        business_reject_reason=None,
    )
    forged_retry = port.publish(forged, finality, tau)
    assert forged_retry.status is CommitStatusV1.FINALITY_REJECTED
    assert forged_retry.reason is not None and "publication root" in forged_retry.reason
    assert retry.record == committed.record


def test_history_capacity_returns_typed_no_commit_without_an_exception(
    subject: M6PromotionSubjectV1,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """BVA: a full bounded archive fails before a successor is constructed."""

    # Arrange: reduce the profile capacity to one committed history atom.
    monkeypatch.setattr(m6_transition, "MAX_HISTORY_LENGTH", 1)
    state = _state(subject)
    first = run_m6_transition_v1(
        subject,
        state,
        _context(subject, state, 1),
        _command(
            GlobalCommandKindV1.PROTOCOL_BUY_AND_BURN,
            1,
            asset="PROTO",
            amount_atoms=1,
        ),
    )
    assert isinstance(first, AcceptCandidateV1)

    # Act: attempt the next authenticated command at the exact capacity edge.
    second = run_m6_transition_v1(
        subject,
        first.post_state,
        _context(subject, first.post_state, 2),
        _command(
            GlobalCommandKindV1.PROTOCOL_BUY_AND_BURN,
            2,
            asset="PROTO",
            amount_atoms=1,
        ),
    )

    # Assert: no Python capacity exception escapes and the full state remains
    # unchanged because no canonical successor can be published.
    assert isinstance(second, RejectNoCommitV1)
    assert second.reason is AdmissionRejectReasonV1.STATE_CAPACITY_EXCEEDED
    assert second.pre_state_root == first.post_state.state_root
    assert first.post_state.get_nonce("alice") == 1


def test_oracle_dispute_cannot_smuggle_a_caller_authored_outcome(
    subject: M6PromotionSubjectV1,
) -> None:
    """BDD/AAA: an outcome field is rejected before batch admission.

    The current M6 surface has no typed adjudication witness.  A caller must
    therefore be unable to turn the disabled command into a settlement by
    adding an outcome, slash, or replacement-price hint at the decode edge.
    """

    # Arrange: start from the exact canonical shape, then add the tempting
    # caller-authored adjudication result without constructing a typed command.
    command = _command(
        GlobalCommandKindV1.ORACLE_DISPUTE,
        1,
        oracle_id="btc-usd",
        bond_atoms=1,
    )
    forged = command.to_canonical()
    payload = dict(forged["payload"])
    payload["outcome"] = "upheld"
    forged["payload"] = payload

    # Act: decode the forged bytes at the untrusted boundary.
    with pytest.raises(ValueError, match="typed validation"):
        decode_global_command_v1(canonical_bytes_v1(forged))

    # Assert: no typed command exists that could consume the ingress nonce or
    # reach the business transition with a caller-selected outcome.  The same
    # nonce remains available to the valid, explicitly disabled command.
    state = _state(subject)
    accepted = run_m6_transition_v1(subject, state, _context(subject, state, 1), command)
    assert isinstance(accepted, AcceptCandidateV1)
    assert accepted.business_status is BusinessStatusV1.REJECTED_COMMITTED
    assert accepted.business_reject_reason is BusinessRejectReasonV1.UNSUPPORTED_OPERATION
    assert accepted.post_state.get_nonce("alice") == 1


def test_malformed_tau_deposit_proof_is_a_typed_committed_rejection(
    subject: M6PromotionSubjectV1,
) -> None:
    state = initial_application_state_v1(subject)
    command = _command(
        GlobalCommandKindV1.TAU_ESCROW_DEPOSIT,
        1,
        deposit_id="deposit-1",
        asset="A",
        amount_atoms=1,
        tau_transaction_root="bad-root",
        tau_finality_root=_root(702),
        tau_profile_root=subject.tau_profile,
    )
    result = run_m6_transition_v1(subject, state, _context(subject, state, 1), command)
    assert isinstance(result, AcceptCandidateV1)
    assert result.business_status is BusinessStatusV1.REJECTED_COMMITTED
    assert result.business_reject_reason is BusinessRejectReasonV1.INVALID_COMMITMENT
    assert result.post_state.escrows == ()


def _zrpf_inputs(
    subject: M6PromotionSubjectV1,
    state: M6ApplicationStateV1,
    *,
    first_withdrawal: bool = False,
) -> tuple[tuple[AuthenticatedExecutionContextV1, ...], tuple[GlobalCommandV1, ...]]:
    contexts: list[AuthenticatedExecutionContextV1] = []
    commands: list[GlobalCommandV1] = []
    current = state
    for nonce in range(1, ZRPF_COMMAND_COUNT_V1 + 1):
        if first_withdrawal and nonce == 1:
            command = _command(
                GlobalCommandKindV1.TAU_WITHDRAWAL,
                nonce,
                withdrawal_id="withdrawal-1",
                asset="A",
                amount_atoms=1,
                destination="tau-alice",
            )
        else:
            command = _command(
                GlobalCommandKindV1.SELLER_AUCTION_CANCEL,
                nonce,
                auction_id=f"auction-{nonce}",
            )
        context = _context(subject, current, nonce)
        preview = run_m6_transition_v1(subject, current, context, command)
        assert isinstance(preview, AcceptCandidateV1)
        contexts.append(context)
        commands.append(command)
        current = preview.post_state
    return tuple(contexts), tuple(commands)


def test_direct_and_zrpf_reference_paths_have_exact_state_and_root_parity(subject: M6PromotionSubjectV1) -> None:
    state = _state(subject)
    contexts, commands = _zrpf_inputs(subject, state)
    direct = execute_direct_batch_v1(subject, state, contexts, commands)
    zrpf = execute_zrpf_batch_v1(subject, state, contexts, commands)
    assert isinstance(zrpf, ZRPFBatchCandidateV1)
    verified = verify_zrpf_root_v1(
        subject,
        zrpf,
        receipt_verifier=_TEST_ZRPF_RECEIPT_VERIFIER,
    )
    assert direct.post_state.state_root == zrpf.post_state_root == verified.post_state.state_root
    assert direct.command_root == zrpf.journal.command_root
    assert direct.nonce_root == zrpf.journal.nonce_root
    assert direct.value_delta_root == zrpf.journal.value_delta_root
    assert direct.history_root == zrpf.journal.history_root
    assert direct.nullifier_root == zrpf.journal.nullifier_root == verified.post_state.nullifier_root
    assert direct.outbox_root == zrpf.journal.outbox_root
    assert direct.data_availability_root == zrpf.journal.data_availability_root


def _two_command_direct_batch(
    subject: M6PromotionSubjectV1,
    state: M6ApplicationStateV1,
) -> DirectBatchCandidateV1:
    contexts: list[AuthenticatedExecutionContextV1] = []
    commands: list[GlobalCommandV1] = []
    current = state
    for nonce in (1, 2):
        command = _command(
            GlobalCommandKindV1.SELLER_AUCTION_CANCEL,
            nonce,
            auction_id=f"direct-{nonce}",
        )
        context = _context(subject, current, nonce)
        result = run_m6_transition_v1(subject, current, context, command)
        assert isinstance(result, AcceptCandidateV1)
        contexts.append(context)
        commands.append(command)
        current = result.post_state
    return execute_direct_batch_v1(subject, state, tuple(contexts), tuple(commands))


def test_direct_batch_publication_survives_proof_capacity_degradation(
    subject: M6PromotionSubjectV1,
) -> None:
    """BDD/AAA: direct fallback uses the same commit port and durable shape."""

    state = _state(subject)
    direct = _two_command_direct_batch(subject, state)
    command_hashes = tuple(command.command_hash for command in direct.commands)
    nonce_identities = tuple(command.nonce_identity for command in direct.commands)
    tau = TauBatchCertificateV1(
        batch_id="direct-batch",
        tau_profile_root=subject.tau_profile,
        chain_id=subject.chain_id,
        ordered_command_hashes=command_hashes,
        ordered_nonce_identities=nonce_identities,
        candidate_parent_head=direct.pre_head,
        certificate_root=hash_v1(
            "m6-tau-batch-certificate-v1",
            {
                "batch_id": "direct-batch",
                "tau_profile_root": subject.tau_profile,
                "chain_id": subject.chain_id,
                "ordered_command_hashes": command_hashes,
                "ordered_nonce_identities": nonce_identities,
                "candidate_parent_head": direct.pre_head,
            },
        ),
    )
    certificate = _finality_certificate(
        subject,
        direct.post_state_root,
        direct.publication_root,
        state.writer_epoch,
    )
    finality = verify_zeno_ledger_finality_v1(
        subject,
        candidate_head=direct.post_state_root,
        publication_root=direct.publication_root,
        candidate_parent_head=direct.pre_head,
        expected_writer_epoch=state.writer_epoch,
        expected_command_root=direct.command_root,
        expected_nonce_root=direct.nonce_root,
        certificate=certificate,
        tau_certificate=tau,
    )

    port = M6CommitPortV1(subject, state, _TEST_FINALITY_VERIFIER)
    result = port.publish_direct_batch(
        direct,
        finality,
        tau,
    )

    assert result.status is CommitStatusV1.COMMITTED
    assert result.record is not None
    assert result.record.direct_batch_replay is not None
    assert len(result.record.direct_batch_replay) == 2
    assert result.record.zrpf_journal is None
    retry = port.publish_direct_batch(
        direct,
        finality,
        tau,
    )
    assert retry.status is CommitStatusV1.ALREADY_COMMITTED


def test_zrpf_root_issuance_fails_closed_without_a_proof_receipt_verifier(
    subject: M6PromotionSubjectV1,
) -> None:
    state = _state(subject)
    contexts, commands = _zrpf_inputs(subject, state)
    zrpf = execute_zrpf_batch_v1(subject, state, contexts, commands)

    with pytest.raises(ValueError, match="proof receipt verifier is unavailable"):
        verify_zrpf_root_v1(subject, zrpf)


def test_zrpf_root_rejects_a_forged_post_state_even_when_journal_roots_are_rebound(
    subject: M6PromotionSubjectV1,
) -> None:
    state = _state(subject)
    contexts, commands = _zrpf_inputs(subject, state)
    zrpf = execute_zrpf_batch_v1(subject, state, contexts, commands)
    forged_post_state = replace(
        zrpf.direct.post_state,
        economic_atoms=(EconomicAtomV1(EconomicAtomKindV1.BALANCE, "mallory", "GOLD", "ledger", 999),),
    )
    forged_direct = replace(zrpf.direct, post_state=forged_post_state)
    forged = replace(zrpf, direct=forged_direct, journal=replace(zrpf.journal, post_state_root=forged_post_state.state_root))
    with pytest.raises(ValueError, match="direct replay"):
        verify_zrpf_structure_v1(subject, forged)


def test_zrpf_commit_publishes_exact_new_outbox_atoms(subject: M6PromotionSubjectV1) -> None:
    state = _state(subject, alice_atoms=1)
    contexts, commands = _zrpf_inputs(subject, state, first_withdrawal=True)
    zrpf = execute_zrpf_batch_v1(subject, state, contexts, commands)
    verified = verify_zrpf_root_v1(
        subject,
        zrpf,
        receipt_verifier=_TEST_ZRPF_RECEIPT_VERIFIER,
    )
    command_hashes = tuple(command.command_hash for command in commands)
    nonce_identities = tuple(command.nonce_identity for command in commands)
    tau = TauBatchCertificateV1(
        batch_id="zrpf-batch-1",
        tau_profile_root=subject.tau_profile,
        chain_id=subject.chain_id,
        ordered_command_hashes=command_hashes,
        ordered_nonce_identities=nonce_identities,
        candidate_parent_head=state.head,
        certificate_root=hash_v1(
            "m6-tau-batch-certificate-v1",
            {
                "batch_id": "zrpf-batch-1",
                "tau_profile_root": subject.tau_profile,
                "chain_id": subject.chain_id,
                "ordered_command_hashes": command_hashes,
                "ordered_nonce_identities": nonce_identities,
                "candidate_parent_head": state.head,
            },
        ),
    )
    finality = _finality(
        subject,
        verified.post_state.state_root,
        verified.journal.journal_root,
        state.writer_epoch,
        tau,
        execution_receipt_root=verified.proof_receipt.receipt_root,
    )

    result = M6CommitPortV1(subject, state, _TEST_FINALITY_VERIFIER).publish_zrpf(verified, finality, tau)

    assert result.status is CommitStatusV1.COMMITTED
    assert result.record is not None
    assert result.record.outbox_atoms == (verified.post_state.outbox[0],)
    assert result.record.outbox_root == verified.post_state.outbox_root


def test_zrpf_foreign_image_is_rejected_without_a_verified_handle(subject: M6PromotionSubjectV1) -> None:
    state = _state(subject)
    contexts, commands = _zrpf_inputs(subject, state)
    zrpf = execute_zrpf_batch_v1(subject, state, contexts, commands)
    foreign = replace(zrpf, journal=replace(zrpf.journal, verifier_image=_root(999)))
    with pytest.raises(ValueError, match="verifier image"):
        verify_zrpf_structure_v1(subject, foreign)


def test_zrpf_foreign_writer_epoch_is_rejected(subject: M6PromotionSubjectV1) -> None:
    state = _state(subject)
    contexts, commands = _zrpf_inputs(subject, state)
    zrpf = execute_zrpf_batch_v1(subject, state, contexts, commands)
    foreign = replace(zrpf, journal=replace(zrpf.journal, writer_epoch=1))
    with pytest.raises(ValueError, match="writer epoch"):
        verify_zrpf_structure_v1(subject, foreign)


def test_zrpf_foreign_nullifier_root_is_rejected(subject: M6PromotionSubjectV1) -> None:
    state = _state(subject)
    contexts, commands = _zrpf_inputs(subject, state)
    zrpf = execute_zrpf_batch_v1(subject, state, contexts, commands)
    foreign = replace(zrpf, journal=replace(zrpf.journal, nullifier_root=_root(999)))
    with pytest.raises(ValueError, match="nullifier root"):
        verify_zrpf_structure_v1(subject, foreign)


def test_zrpf_context_and_command_bindings_are_rejected_when_crossed(
    subject: M6PromotionSubjectV1,
) -> None:
    state = _state(subject)
    contexts, commands = _zrpf_inputs(subject, state)
    zrpf = execute_zrpf_batch_v1(subject, state, contexts, commands)
    crossed_context = _context(
        subject,
        state,
        zrpf.direct.contexts[0].nonce,
        sender="mallory",
        ledger_height=zrpf.direct.contexts[0].ledger_height,
    )
    crossed_direct = replace(
        zrpf.direct,
        contexts=(crossed_context, *zrpf.direct.contexts[1:]),
    )
    crossed = replace(zrpf, direct=crossed_direct)
    with pytest.raises(ValueError, match="context command"):
        verify_zrpf_structure_v1(subject, crossed)


def test_direct_commit_rejects_an_outbox_projection_that_drops_a_withdrawal(
    subject: M6PromotionSubjectV1,
) -> None:
    state = _state(subject, alice_atoms=10)
    command = _command(
        GlobalCommandKindV1.TAU_WITHDRAWAL,
        1,
        withdrawal_id="w1",
        asset="A",
        amount_atoms=2,
        destination="tau-alice",
    )
    candidate = run_m6_transition_v1(subject, state, _context(subject, state, 1), command)
    assert isinstance(candidate, AcceptCandidateV1)
    dropped = replace(candidate, outbox_atoms=())
    tau = _tau_certificate(subject, candidate, state.head)
    finality = _finality(
        subject,
        candidate.post_state.state_root,
        candidate.publication_atom.publication_root,
        0,
        tau,
    )
    result = M6CommitPortV1(subject, state, _TEST_FINALITY_VERIFIER).publish(
        dropped,
        finality,
        tau,
    )
    assert result.status is CommitStatusV1.FINALITY_REJECTED
    assert result.reason is not None and "replay" in result.reason
    assert result.state == state


def test_direct_commit_rejects_a_mutated_publication_projection(
    subject: M6PromotionSubjectV1,
) -> None:
    state = _state(subject, alice_atoms=10)
    command = _command(
        GlobalCommandKindV1.TAU_WITHDRAWAL,
        1,
        withdrawal_id="w1",
        asset="A",
        amount_atoms=2,
        destination="tau-alice",
    )
    candidate = run_m6_transition_v1(subject, state, _context(subject, state, 1), command)
    assert isinstance(candidate, AcceptCandidateV1)
    corrupted = replace(
        candidate,
        publication_atom=replace(candidate.publication_atom, outbox_root=_root(999)),
    )
    tau = _tau_certificate(subject, candidate, state.head)
    finality = _finality(
        subject,
        corrupted.post_state.state_root,
        corrupted.publication_atom.publication_root,
        0,
        tau,
    )
    result = M6CommitPortV1(subject, state, _TEST_FINALITY_VERIFIER).publish(
        corrupted,
        finality,
        tau,
    )
    assert result.status is CommitStatusV1.FINALITY_REJECTED
    assert result.reason is not None and "replay" in result.reason
    assert result.state == state


def test_direct_degradation_requires_unavailable_proof_capacity(subject: M6PromotionSubjectV1) -> None:
    state = _state(subject)
    context = _context(subject, state, 1)
    command = _command(GlobalCommandKindV1.SELLER_AUCTION_CANCEL, 1, auction_id="auction-1")
    direct = degrade_to_direct_v1(
        subject,
        state,
        (context,),
        (command,),
        proof_capacity_available=False,
    )
    assert direct.post_state.ingress_nonces[0].last_nonce == 1
    with pytest.raises(ValueError, match="unavailable proof capacity"):
        degrade_to_direct_v1(
            subject,
            state,
            (context,),
            (command,),
            proof_capacity_available=True,
        )


def test_zrpf_crossed_chunks_are_rejected(subject: M6PromotionSubjectV1) -> None:
    state = _state(subject)
    contexts, commands = _zrpf_inputs(subject, state)
    zrpf = execute_zrpf_batch_v1(subject, state, contexts, commands)
    crossed = replace(zrpf, chunks=(zrpf.chunks[1], zrpf.chunks[0], *zrpf.chunks[2:]))
    with pytest.raises(ValueError, match="chunk"):
        verify_zrpf_structure_v1(subject, crossed)


def test_commit_boundary_recomputes_derived_archive_roots(subject: M6PromotionSubjectV1) -> None:
    state = _state(subject)
    corrupted = replace(state, history_root_cache=_root(999))
    with pytest.raises(ValueError, match="history root cache mismatch"):
        validate_state_commitments_v1(corrupted)


def test_zusd_redeem_cannot_create_collateral_without_vault_custody(subject: M6PromotionSubjectV1) -> None:
    state = replace(
        _state(subject),
        economic_atoms=(
            EconomicAtomV1(EconomicAtomKindV1.BALANCE, "alice", "zUSD", "ledger", 10),
            EconomicAtomV1(EconomicAtomKindV1.SUPPLY, "__supply__", "zUSD", "ledger", 10),
        ),
    )
    command = _command(
        GlobalCommandKindV1.ZUSD_REDEEM,
        1,
        vault_id="vault-1",
        collateral_asset="A",
        amount_atoms=5,
    )
    result = run_m6_transition_v1(subject, state, _context(subject, state, 1), command)
    assert isinstance(result, AcceptCandidateV1)
    assert result.business_status is BusinessStatusV1.REJECTED_COMMITTED
    assert result.post_state.get_atom(EconomicAtomKindV1.BALANCE, "alice", "A", "ledger") == 0
    assert result.post_state.get_atom(EconomicAtomKindV1.BALANCE, "alice", "zUSD", "ledger") == 10


def test_readiness_does_not_accept_self_declared_four_way_gates() -> None:
    from src.core.m6_safe_mount_types_v1 import m6_ready_v1

    statuses = {
        f"M6-R{index:02d}": {"PROVED": True, "IMPLEMENTED": True, "MOUNTED": True, "TESTED": True}
        for index in range(1, 14)
    }
    assert not m6_ready_v1(statuses)
    statuses["M6-R13"]["MOUNTED"] = False
    assert not m6_ready_v1(statuses)
    statuses["M6-R13"]["MOUNTED"] = True
    statuses["M6-R14"] = statuses.pop("M6-R13")
    assert not m6_ready_v1(statuses)


def test_research_facade_is_not_reexported_by_production_core_namespace() -> None:
    import src.core as production_core
    import src.core.m6_safe_mount_v1 as m6_facade

    assert "M6PromotionSubjectV1" not in production_core.__all__
    assert "run_m6_transition_v1" not in production_core.__all__
    assert "execute_zrpf_batch_v1" not in production_core.__all__
    assert not hasattr(m6_facade, "issue_m6_authority_verification_receipt_v1")
    assert not hasattr(m6_facade, "issue_m6_execution_context_verification_receipt_v1")
    assert not hasattr(m6_facade, "issue_m6_zrpf_verification_receipt_v1")
    assert not hasattr(m6_facade, "m6_authority_evidence_v1")
    assert not hasattr(m6_facade, "m6_safe_mount_types_v1")
    assert not hasattr(m6_facade, "m6_zrpf_v1")


def _has_legacy_tau_balance_adapter_reference_v1(tree: ast.AST) -> bool:
    """Recognize static or literal dynamic references to the legacy adapter."""

    imported_modules: set[str] = set()
    called_attributes: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            imported_modules.update(alias.name for alias in node.names)
        elif isinstance(node, ast.ImportFrom):
            imported_modules.update(
                f"{node.module}.{alias.name}" if node.module else alias.name
                for alias in node.names
            )
        elif isinstance(node, ast.Call):
            if isinstance(node.func, ast.Name):
                function_name = node.func.id
            elif isinstance(node.func, ast.Attribute):
                function_name = node.func.attr
            else:
                continue
            called_attributes.add(function_name)

            if (
                function_name in {"import_module", "__import__"}
                and node.args
                and isinstance(node.args[0], ast.Constant)
                and isinstance(node.args[0].value, str)
            ):
                imported_modules.add(node.args[0].value)
            if (
                function_name == "getattr"
                and len(node.args) >= 2
                and isinstance(node.args[1], ast.Constant)
                and isinstance(node.args[1].value, str)
            ):
                called_attributes.add(node.args[1].value)

    imports_legacy_adapter = any(
        module == "tau_testnet_dex_plugin"
        or module.endswith(".tau_testnet_dex_plugin")
        for module in imported_modules
    )
    return imports_legacy_adapter or "apply_app_tx" in called_attributes


def test_m6_authority_path_has_no_static_legacy_balance_adapter_reference() -> None:
    """MUT-M6-BACKING-001: static legacy balance ingress cannot become M6 authority."""

    # Arrange: the complete M6 core and authority-shell import boundary.
    repo_root = Path(__file__).resolve().parents[2]
    authority_paths = (
        "src/core/m6_safe_mount_types_v1.py",
        "src/core/m6_authority_evidence_v1.py",
        "src/core/m6_safe_mount_transition_v1.py",
        "src/integration/m6_authority_verifier_v1.py",
        "src/integration/m6_commit_port_v1.py",
        "src/integration/m6_durable_store_v1.py",
    )

    # Act / Assert: static importing or directly calling the legacy mapping
    # adapter would create a bypass around the finality-bound deposit witness
    # port.  Obfuscated runtime construction remains outside this narrow
    # source-level check.
    for relative_path in authority_paths:
        tree = ast.parse((repo_root / relative_path).read_text(encoding="utf-8"))
        assert not _has_legacy_tau_balance_adapter_reference_v1(tree), relative_path


def test_static_legacy_balance_adapter_detector_rejects_qualified_hostile_call() -> None:
    """Mutation control: the static no-bypass detector catches a qualified call."""

    # Arrange / Act: a plausible attempted bypass uses a module alias.
    hostile_tree = ast.parse(
        "from src.integration import tau_testnet_dex_plugin as legacy\n"
        "legacy.apply_app_tx({}, chain_balances={})\n"
    )

    # Assert: the checker mechanism itself recognizes the mutant.
    assert _has_legacy_tau_balance_adapter_reference_v1(hostile_tree)


def test_static_legacy_balance_adapter_detector_rejects_literal_dynamic_import() -> None:
    """Mutation control: literal dynamic imports cannot evade the static detector."""

    # Arrange / Act: an attempted bypass hides both import and call behind
    # standard dynamic helpers while retaining literals in source.
    hostile_tree = ast.parse(
        "from importlib import import_module\n"
        "legacy = import_module('src.integration.tau_testnet_dex_plugin')\n"
        "getattr(legacy, 'apply_app_tx')({}, chain_balances={})\n"
    )

    # Assert: literal dynamic forms still identify the forbidden adapter.
    assert _has_legacy_tau_balance_adapter_reference_v1(hostile_tree)
