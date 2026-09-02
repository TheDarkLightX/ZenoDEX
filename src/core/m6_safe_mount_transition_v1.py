"""Deterministic M6 transition reference.

The transition consumes one authenticated, typed command and one immutable
state snapshot.  Admission failures return ``RejectNoCommitV1``.  A typed
command that reaches the canonical batch and fails its business precondition
returns ``AcceptCandidateV1`` with a committed ingress nonce and replay
history, while all value effects and external outbox rows remain unchanged.
That distinction makes the nonce rule explicit and prevents a caller from
silently treating a committed failure as a no-op rejection.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass, replace
from types import MappingProxyType
from typing import Mapping

from ..state.canonical import canonical_hex_fixed_allow_0x
from .m6_safe_mount_types_v1 import (
    LAUNCH_COMMANDS_V1,
    MAX_ATOMS_V1,
    MAX_HISTORY_LENGTH,
    MAX_PRICE_E8_V1,
    MAX_SEALED_BID_PRICE_E8_V1,
    SEALED_BID_PRICE_SCALE_E8_V1,
    ZERO_ROOT_V1,
    AcceptCandidateV1,
    AdmissionRejectReasonV1,
    AuthenticatedExecutionContextV1,
    BusinessRejectReasonV1,
    BusinessStatusV1,
    CommandArgumentV1,
    EconomicAtomKindV1,
    EconomicAtomV1,
    EscrowAtomV1,
    FinalityModeV1,
    FreshnessBoundsV1,
    GlobalCommandKindV1,
    GlobalCommandV1,
    HistoryAtomV1,
    M6ApplicationStateV1,
    M6AuthorityEvidenceV1,
    M6PromotionSubjectV1,
    MigrationAuthorityProofV1,
    MigrationEvidenceKindV1,
    MigrationPhaseV1,
    MigrationStateV1,
    NonceAtomV1,
    OracleContextV1,
    OutboxAtomV1,
    PrivateSwapParticipantStateV1,
    PrivateSwapPhaseV1,
    PublicationAtomV1,
    RejectNoCommitV1,
    SellerAuctionBidStateV1,
    SellerAuctionPhaseV1,
    TauEscrowDepositProofV1,
    TauWithdrawalIntentV1,
    TauWithdrawalStatusV1,
    ValueDeltaCertificateV1,
    ValueDeltaClassV1,
    ValueDeltaEntryV1,
    WithdrawalAcknowledgmentV1,
    _M6ExecutionContextWitness,
    append_root_v1,
    hash_v1,
)

# Publication policy belongs to the deterministic core.  The commit shell may
# consume this closed decision, while it cannot choose a different finality
# mode for the same migration edge.
_FINALITY_MODE_BY_MIGRATION_EDGE_V1 = MappingProxyType(
    {
        (MigrationPhaseV1.NORMAL, MigrationPhaseV1.NORMAL): FinalityModeV1.TAU_ORDERED,
        (MigrationPhaseV1.NORMAL, MigrationPhaseV1.FALLBACK): FinalityModeV1.FALLBACK_FORCED_INCLUSION,
        (MigrationPhaseV1.FALLBACK, MigrationPhaseV1.FALLBACK): FinalityModeV1.FALLBACK_FORCED_INCLUSION,
        (MigrationPhaseV1.FALLBACK, MigrationPhaseV1.NORMAL): FinalityModeV1.FALLBACK_FORCED_INCLUSION,
    }
)


def expected_finality_mode_v1(
    pre_phase: MigrationPhaseV1,
    post_phase: MigrationPhaseV1,
    _table: Mapping[tuple[MigrationPhaseV1, MigrationPhaseV1], FinalityModeV1] = (
        _FINALITY_MODE_BY_MIGRATION_EDGE_V1
    ),
) -> FinalityModeV1 | None:
    """Return the only finality mode admitted for a migration edge."""

    return _table.get((pre_phase, post_phase))


class _BusinessFailure(Exception):
    def __init__(self, reason: BusinessRejectReasonV1) -> None:
        self.reason = reason
        super().__init__(reason.value)


@dataclass(frozen=True, slots=True)
class _AppliedBusiness:
    status: BusinessStatusV1
    reject_reason: BusinessRejectReasonV1 | None
    economic_atoms: tuple[EconomicAtomV1, ...]
    escrows: tuple[EscrowAtomV1, ...]
    withdrawals: tuple[TauWithdrawalIntentV1, ...]
    outbox: tuple[OutboxAtomV1, ...]
    acknowledgments: tuple[WithdrawalAcknowledgmentV1, ...]
    seller_auction_bids: tuple[SellerAuctionBidStateV1, ...]
    private_swap_participants: tuple[PrivateSwapParticipantStateV1, ...]
    migration: MigrationStateV1
    delta_entries: tuple[ValueDeltaEntryV1, ...]


def run_m6_transition_v1(
    subject: M6PromotionSubjectV1,
    state: M6ApplicationStateV1,
    context: AuthenticatedExecutionContextV1,
    command: GlobalCommandV1,
) -> AcceptCandidateV1 | RejectNoCommitV1:
    """Evaluate one M6 command deterministically.

    Reject precedence is type/binding, parent head, epoch/profile, sender and
    nonce, freshness, then business validation.  The first five classes are
    no-commit rejects.  Business rejection consumes exactly the authenticated
    ingress nonce and appends one history/nullifier pair with an empty value
    effect plan.  No external effect is created by a business rejection.
    """

    type_reject_reason = _require_transition_types(subject, state, context, command)
    if type_reject_reason is not None:
        return RejectNoCommitV1(
            reason=type_reject_reason,
            pre_state_root=state.state_root,
        )
    pre_state_root = state.state_root
    command_hash = command.command_hash
    admission_reason = _admission_reject_reason(subject, state, context, command)
    if admission_reason is not None:
        return RejectNoCommitV1(
            reason=admission_reason,
            pre_state_root=pre_state_root,
            command_hash=command_hash,
        )

    try:
        applied = _apply_business_command(
            state,
            command,
            pre_state_root,
            subject.subject_root,
            subject.tau_profile,
            context.ledger_height,
            context.authority_evidence,
        )
    except _BusinessFailure as failure:
        applied = _committed_business_rejection(state, failure.reason)
    return _commit_business_result(state, context, command, pre_state_root, applied)


def _committed_business_rejection(
    state: M6ApplicationStateV1,
    reason: BusinessRejectReasonV1,
) -> _AppliedBusiness:
    return _AppliedBusiness(
        status=BusinessStatusV1.REJECTED_COMMITTED,
        reject_reason=reason,
        economic_atoms=state.economic_atoms,
        escrows=state.escrows,
        withdrawals=state.withdrawals,
        outbox=state.outbox,
        acknowledgments=state.acknowledgments,
        seller_auction_bids=state.seller_auction_bids,
        private_swap_participants=state.private_swap_participants,
        migration=state.migration,
        delta_entries=(),
    )


def _commit_business_result(
    state: M6ApplicationStateV1,
    context: AuthenticatedExecutionContextV1,
    command: GlobalCommandV1,
    pre_state_root: str,
    applied: _AppliedBusiness,
) -> AcceptCandidateV1:
    provisional = _provisional_state(state, command, applied)
    post_state_root = provisional.state_root
    delta = _make_value_delta(command, pre_state_root, post_state_root, applied.delta_entries)
    nullifier = _make_nullifier(command, pre_state_root)
    history_atom = _make_history_atom(
        state,
        command,
        pre_state_root,
        post_state_root,
        applied.status,
        applied.reject_reason,
        delta,
        nullifier,
    )
    post_state = _append_committed_archives(state, provisional, history_atom, nullifier, applied.outbox)
    publication = _make_publication(
        post_state,
        command,
        pre_state_root,
        post_state_root,
        delta,
        context.authentication_root,
        applied.status,
        applied.reject_reason,
    )
    return AcceptCandidateV1(
        context=context,
        command=command,
        pre_state_root=pre_state_root,
        post_state=post_state,
        value_delta=delta,
        history_atom=history_atom,
        publication_atom=publication,
        outbox_atoms=tuple(applied.outbox[len(state.outbox) :]),
        business_status=applied.status,
        business_reject_reason=applied.reject_reason,
    )


def _provisional_state(
    state: M6ApplicationStateV1,
    command: GlobalCommandV1,
    applied: _AppliedBusiness,
) -> M6ApplicationStateV1:
    return replace(
        state,
        ingress_nonces=_with_nonce(state.ingress_nonces, command.sender, command.nonce),
        economic_atoms=applied.economic_atoms,
        escrows=applied.escrows,
        withdrawals=applied.withdrawals,
        outbox=applied.outbox,
        acknowledgments=applied.acknowledgments,
        seller_auction_bids=applied.seller_auction_bids,
        private_swap_participants=applied.private_swap_participants,
        migration=applied.migration,
        writer_epoch=applied.migration.authority_epoch,
    )


def _make_value_delta(
    command: GlobalCommandV1,
    pre_state_root: str,
    post_state_root: str,
    entries: tuple[ValueDeltaEntryV1, ...],
) -> ValueDeltaCertificateV1:
    return ValueDeltaCertificateV1(
        command_hash=command.command_hash,
        pre_state_root=pre_state_root,
        post_state_root=post_state_root,
        entries=entries,
        delta_root=hash_v1(
            "m6-value-delta-certificate-v1",
            {
                "command_hash": command.command_hash,
                "pre_state_root": pre_state_root,
                "post_state_root": post_state_root,
                "entries": entries,
            },
        ),
    )


def _make_nullifier(command: GlobalCommandV1, pre_state_root: str) -> str:
    return hash_v1(
        "m6-ingress-nullifier-v1",
        {
            "sender": command.sender,
            "nonce": command.nonce,
            "command_hash": command.command_hash,
            "pre_state_root": pre_state_root,
        },
    )


def _make_history_atom(
    state: M6ApplicationStateV1,
    command: GlobalCommandV1,
    pre_state_root: str,
    post_state_root: str,
    status: BusinessStatusV1,
    reject_reason: BusinessRejectReasonV1 | None,
    delta: ValueDeltaCertificateV1,
    nullifier: str,
) -> HistoryAtomV1:
    return HistoryAtomV1(
        sequence=len(state.history),
        command_hash=command.command_hash,
        sender=command.sender,
        nonce=command.nonce,
        pre_state_root=pre_state_root,
        post_state_root=post_state_root,
        outcome=status,
        value_delta_root=delta.delta_root,
        nullifier=nullifier,
        business_reject_reason=reject_reason,
    )


def _append_committed_archives(
    state: M6ApplicationStateV1,
    provisional: M6ApplicationStateV1,
    history_atom: HistoryAtomV1,
    nullifier: str,
    outbox: tuple[OutboxAtomV1, ...],
) -> M6ApplicationStateV1:
    history_root = append_root_v1("m6-history-root-v1", state.history_root, history_atom.history_root)
    nullifier_root = append_root_v1("m6-nullifier-root-v1", state.nullifier_root, nullifier)
    outbox_root = state.outbox_root
    for outbox_atom in outbox[len(state.outbox) :]:
        outbox_root = append_root_v1("m6-outbox-root-v1", outbox_root, outbox_atom.effect_id)
    return replace(
        provisional,
        head=provisional.state_root,
        history=state.history + (history_atom,),
        nullifiers=state.nullifiers + (nullifier,),
        history_root_cache=history_root,
        nullifier_root_cache=nullifier_root,
        outbox_root_cache=outbox_root,
    )


def _make_publication(
    post_state: M6ApplicationStateV1,
    command: GlobalCommandV1,
    pre_state_root: str,
    post_state_root: str,
    delta: ValueDeltaCertificateV1,
    execution_context_root: str,
    status: BusinessStatusV1,
    reject_reason: BusinessRejectReasonV1 | None,
) -> PublicationAtomV1:
    candidate_id = hash_v1(
        "m6-candidate-id-v1",
        {
            "command_hash": command.command_hash,
            "pre_state_root": pre_state_root,
            "post_state_root": post_state_root,
        },
    )
    return PublicationAtomV1(
        candidate_id=candidate_id,
        pre_state_root=pre_state_root,
        post_state_root=post_state_root,
        history_root=post_state.history_root,
        nullifier_root=post_state.nullifier_root,
        value_delta_root=delta.delta_root,
        outbox_root=post_state.outbox_root,
        execution_context_root=execution_context_root,
        writer_epoch=post_state.writer_epoch,
        business_status=status,
        business_reject_reason=reject_reason,
    )


def _require_transition_types(
    subject: object,
    state: object,
    context: object,
    command: object,
) -> AdmissionRejectReasonV1 | None:
    if type(subject) is not M6PromotionSubjectV1:
        raise TypeError("subject must be M6PromotionSubjectV1")
    if type(state) is not M6ApplicationStateV1:
        raise TypeError("state must be M6ApplicationStateV1")
    if type(context) is not AuthenticatedExecutionContextV1:
        return AdmissionRejectReasonV1.UNAUTHENTICATED_CONTEXT
    if not _authenticated_context_is_current_v1(context):
        return AdmissionRejectReasonV1.UNAUTHENTICATED_CONTEXT
    if type(command) is not GlobalCommandV1:
        return AdmissionRejectReasonV1.MALFORMED_COMMAND
    if type(command.payload) is not tuple or any(
        type(argument) is not CommandArgumentV1
        or type(argument.key) is not str
        or type(argument.value) not in (str, int)
        for argument in command.payload
    ):
        return AdmissionRejectReasonV1.MALFORMED_COMMAND
    return None


def _authenticated_context_is_current_v1(
    context: AuthenticatedExecutionContextV1,
) -> bool:
    """Recheck exact nested types and the witness against the current body."""

    if type(context.oracle_context) is not OracleContextV1:
        return False
    if type(context.freshness_bounds) is not FreshnessBoundsV1:
        return False
    evidence = context.authority_evidence
    if evidence is not None:
        if type(evidence) is not M6AuthorityEvidenceV1:
            return False
        expected_payload_types: dict[GlobalCommandKindV1, type[object]] = {
            GlobalCommandKindV1.TAU_ESCROW_DEPOSIT: TauEscrowDepositProofV1,
            GlobalCommandKindV1.TAU_WITHDRAWAL_ACK: WithdrawalAcknowledgmentV1,
            GlobalCommandKindV1.FALLBACK_ACTIVATE: MigrationAuthorityProofV1,
            GlobalCommandKindV1.TAU_REJOIN: MigrationAuthorityProofV1,
        }
        expected_payload_type = expected_payload_types.get(evidence.kind)
        if expected_payload_type is None or type(evidence.payload) is not expected_payload_type:
            return False
    witness = context._verification_witness
    if type(witness) is not _M6ExecutionContextWitness:
        return False
    try:
        return witness.context_root == context.authentication_root
    except (TypeError, ValueError):
        return False


def _admission_reject_reason(
    subject: M6PromotionSubjectV1,
    state: M6ApplicationStateV1,
    context: AuthenticatedExecutionContextV1,
    command: GlobalCommandV1,
) -> AdmissionRejectReasonV1 | None:
    if state.deployment != subject.deployment or context.deployment != subject.deployment:
        return AdmissionRejectReasonV1.CONTEXT_DEPLOYMENT_MISMATCH
    if context.chain_id != subject.chain_id:
        return AdmissionRejectReasonV1.CONTEXT_CHAIN_ID_MISMATCH
    if context.parent_head != state.head:
        return AdmissionRejectReasonV1.CONTEXT_PARENT_HEAD_MISMATCH
    if context.epoch != state.writer_epoch:
        return AdmissionRejectReasonV1.CONTEXT_EPOCH_MISMATCH
    if context.tau_profile != subject.tau_profile:
        return AdmissionRejectReasonV1.CONTEXT_TAU_PROFILE_MISMATCH
    if context.verifier_registry != subject.verifier:
        return AdmissionRejectReasonV1.CONTEXT_VERIFIER_MISMATCH
    if context.sender != command.sender:
        return AdmissionRejectReasonV1.SENDER_MISMATCH
    if context.nonce != command.nonce or command.nonce != state.get_nonce(command.sender) + 1:
        return AdmissionRejectReasonV1.NONCE_MISMATCH
    # A committed candidate always appends one history/nullifier pair.  Once
    # the bounded archive is full there is no valid successor that can obey
    # the nonce/history invariant, so fail at admission with a typed no-commit
    # result instead of leaking a constructor ValueError.
    if len(state.history) >= MAX_HISTORY_LENGTH:
        return AdmissionRejectReasonV1.STATE_CAPACITY_EXCEEDED
    if command.kind not in LAUNCH_COMMANDS_V1:
        return AdmissionRejectReasonV1.UNSUPPORTED_COMMAND
    if context.ledger_height < command.created_height:
        return AdmissionRejectReasonV1.STALE_COMMAND_CONTEXT
    if (
        context.ledger_height - command.created_height
        > context.freshness_bounds.max_command_age_blocks
    ):
        return AdmissionRejectReasonV1.STALE_COMMAND_CONTEXT
    if (
        command.kind in _ORACLE_SENSITIVE_COMMANDS_V1
    ):
        if context.oracle_context.observed_height > context.ledger_height:
            return AdmissionRejectReasonV1.STALE_ORACLE_CONTEXT
        if context.oracle_context.oracle_height > context.ledger_height:
            return AdmissionRejectReasonV1.STALE_ORACLE_CONTEXT
        if (
            context.ledger_height - context.oracle_context.oracle_height
            > context.freshness_bounds.max_oracle_age_blocks
        ):
            return AdmissionRejectReasonV1.STALE_ORACLE_CONTEXT
    if command.kind in {
        GlobalCommandKindV1.TAU_ESCROW_DEPOSIT,
        GlobalCommandKindV1.TAU_WITHDRAWAL_ACK,
    } and context.authority_evidence is not None:
        authority_payload = context.authority_evidence.payload
        tau_height = (
            authority_payload.tau_finality_height
            if isinstance(authority_payload, TauEscrowDepositProofV1)
            else authority_payload.tau_receipt_height
            if isinstance(authority_payload, WithdrawalAcknowledgmentV1)
            else None
        )
        if tau_height is not None:
            if context.ledger_height < tau_height:
                return AdmissionRejectReasonV1.STALE_TAU_CONTEXT
            if (
                context.ledger_height - tau_height
                > context.freshness_bounds.max_tau_age_blocks
            ):
                return AdmissionRejectReasonV1.STALE_TAU_CONTEXT
    return None


_ORACLE_SENSITIVE_COMMANDS_V1 = frozenset(
    {
        GlobalCommandKindV1.ZUSD_BORROW,
        GlobalCommandKindV1.ZUSD_REDEEM,
        GlobalCommandKindV1.ZUSD_LIQUIDATE,
        GlobalCommandKindV1.ZUSD_REDISTRIBUTE,
        GlobalCommandKindV1.PERP_OPEN,
        GlobalCommandKindV1.PERP_FUNDING,
        GlobalCommandKindV1.PERP_LIQUIDATE,
        GlobalCommandKindV1.ORACLE_SUBMIT,
        GlobalCommandKindV1.ORACLE_DISPUTE,
    }
)


def _apply_business_command(
    state: M6ApplicationStateV1,
    command: GlobalCommandV1,
    pre_state_root: str,
    subject_root: str,
    tau_profile: str,
    ledger_height: int,
    authority_evidence: M6AuthorityEvidenceV1 | None,
) -> _AppliedBusiness:
    if _is_research_disabled_command_v1(command.kind):
        # Keep this partition in the closed transition code.  The module-level
        # research metadata remains useful for reporting, yet it is mutable at
        # runtime through Python rebinding.  A disabled command must remain
        # fail-closed even if an adapter mutates that metadata and the handler
        # table in the same process.
        raise _BusinessFailure(BusinessRejectReasonV1.UNSUPPORTED_OPERATION)
    scratch = _BusinessScratch.from_state(
        state,
        command,
        pre_state_root,
        subject_root,
        tau_profile,
        ledger_height,
        authority_evidence,
    )
    handler = _BUSINESS_HANDLERS.get(command.kind)
    if handler is None:
        raise _BusinessFailure(BusinessRejectReasonV1.UNSUPPORTED_OPERATION)
    handler(scratch)
    return scratch.finish()


def _is_research_disabled_command_v1(kind: GlobalCommandKindV1) -> bool:
    """Return the closed research-only command partition.

    This deliberately does not read a mutable registry or environment value.
    A mounted deployment needs a promotion-subject-bound policy witness before
    it can enable one of these operations.
    """

    return kind in (
        GlobalCommandKindV1.ZUSD_LIQUIDATE,
        GlobalCommandKindV1.ZUSD_REDISTRIBUTE,
        GlobalCommandKindV1.PERP_FUNDING,
        GlobalCommandKindV1.PERP_LIQUIDATE,
        GlobalCommandKindV1.ORACLE_SUBMIT,
        GlobalCommandKindV1.ORACLE_DISPUTE,
        GlobalCommandKindV1.PROTOCOL_BUY_AND_BURN,
        GlobalCommandKindV1.ZRPF_PROVER_REWARD,
    )


@dataclass(slots=True)
class _BusinessScratch:
    command: GlobalCommandV1
    pre_state_root: str
    subject_root: str
    tau_profile: str
    ledger_height: int
    authority_evidence: M6AuthorityEvidenceV1 | None
    atoms: dict[tuple[str, str, str, str], int]
    deltas: dict[tuple[str, str, str, str], ValueDeltaEntryV1]
    escrows: list[EscrowAtomV1]
    withdrawals: list[TauWithdrawalIntentV1]
    outbox: list[OutboxAtomV1]
    acknowledgments: list[WithdrawalAcknowledgmentV1]
    seller_auction_bids: list[SellerAuctionBidStateV1]
    private_swap_participants: list[PrivateSwapParticipantStateV1]
    migration: MigrationStateV1

    @classmethod
    def from_state(
        cls,
        state: M6ApplicationStateV1,
        command: GlobalCommandV1,
        pre_state_root: str,
        subject_root: str,
        tau_profile: str,
        ledger_height: int,
        authority_evidence: M6AuthorityEvidenceV1 | None,
    ) -> _BusinessScratch:
        return cls(
            command=command,
            pre_state_root=pre_state_root,
            subject_root=subject_root,
            tau_profile=tau_profile,
            ledger_height=ledger_height,
            authority_evidence=authority_evidence,
            atoms={atom.key: atom.amount_atoms for atom in state.economic_atoms},
            deltas={},
            escrows=list(state.escrows),
            withdrawals=list(state.withdrawals),
            outbox=list(state.outbox),
            acknowledgments=list(state.acknowledgments),
            seller_auction_bids=list(state.seller_auction_bids),
            private_swap_participants=list(state.private_swap_participants),
            migration=state.migration,
        )

    def field(self, key: str, default: str | int | None = None) -> str | int | None:
        return self.command.payload_value(key, default)

    def text(self, key: str, default: str | None = None) -> str:
        value = self.field(key, default)
        if not isinstance(value, str) or not value:
            raise _BusinessFailure(BusinessRejectReasonV1.INVALID_ASSET)
        return value

    def root_text(self, key: str) -> str:
        value = self.text(key)
        try:
            canonical = canonical_hex_fixed_allow_0x(value, nbytes=32, name=key)
        except (TypeError, ValueError) as exc:
            raise _BusinessFailure(BusinessRejectReasonV1.INVALID_COMMITMENT) from exc
        if canonical != value or value == "0x" + "00" * 32:
            raise _BusinessFailure(BusinessRejectReasonV1.INVALID_COMMITMENT)
        return value

    def deadlines(self) -> tuple[int, int, int]:
        commit_height = self.nonnegative(self.field("commit_height"))
        reveal_deadline = self.nonnegative(self.field("reveal_deadline_height"))
        settle_deadline = self.nonnegative(self.field("settle_deadline_height"))
        if (
            commit_height != self.ledger_height
            or not commit_height < reveal_deadline < settle_deadline
        ):
            raise _BusinessFailure(BusinessRejectReasonV1.INVALID_DEADLINE)
        return commit_height, reveal_deadline, settle_deadline

    def atoms_value(self, kind: EconomicAtomKindV1, owner: str, asset: str, custody: str) -> int:
        return self.atoms.get((kind.value, owner, asset, custody), 0)

    def change_atom(
        self,
        kind: EconomicAtomKindV1,
        owner: str,
        asset: str,
        custody: str,
        delta_atoms: int,
    ) -> None:
        key = (kind.value, owner, asset, custody)
        next_value = self.atoms.get(key, 0) + delta_atoms
        if next_value < 0:
            raise _BusinessFailure(BusinessRejectReasonV1.INSUFFICIENT_BALANCE)
        if next_value > MAX_ATOMS_V1:
            raise _BusinessFailure(BusinessRejectReasonV1.INVALID_AMOUNT)
        if next_value == 0:
            self.atoms.pop(key, None)
        else:
            self.atoms[key] = next_value

    def record(
        self,
        delta_class: ValueDeltaClassV1,
        owner: str,
        asset: str,
        custody: str,
        delta_atoms: int,
    ) -> None:
        if delta_atoms == 0:
            return
        key = (delta_class.value, owner, asset, custody)
        previous = self.deltas.get(key)
        amount = delta_atoms if previous is None else previous.delta_atoms + delta_atoms
        if amount == 0:
            self.deltas.pop(key, None)
            return
        self.deltas[key] = ValueDeltaEntryV1.from_ledger_allocation(
            delta_class=delta_class,
            owner=owner,
            asset=asset,
            ledger_allocation=custody,
            delta_atoms=amount,
        )

    def debit_balance(self, owner: str, asset: str, amount_atoms: int, custody: str = "ledger") -> None:
        _positive(amount_atoms)
        self.change_atom(EconomicAtomKindV1.BALANCE, owner, asset, custody, -amount_atoms)
        self.record(ValueDeltaClassV1.INTERNAL_TRANSFER, owner, asset, custody, -amount_atoms)

    def credit_balance(self, owner: str, asset: str, amount_atoms: int, custody: str = "ledger") -> None:
        _positive(amount_atoms)
        self.change_atom(EconomicAtomKindV1.BALANCE, owner, asset, custody, amount_atoms)
        self.record(ValueDeltaClassV1.INTERNAL_TRANSFER, owner, asset, custody, amount_atoms)

    def positive(self, value: object) -> int:
        return _positive(value)

    def nonnegative(self, value: object) -> int:
        if type(value) is not int or value < 0:
            raise _BusinessFailure(BusinessRejectReasonV1.INVALID_AMOUNT)
        return int(value)

    def simple_transfer(self, asset: str, amount_atoms: int, destination: str, custody: str = "ledger") -> None:
        self.debit_balance(self.command.sender, asset, amount_atoms, custody)
        self.credit_balance(destination, asset, amount_atoms, custody)

    def move_balance(
        self,
        source: str,
        destination: str,
        asset: str,
        amount_atoms: int,
        custody: str = "ledger",
    ) -> None:
        self.debit_balance(source, asset, amount_atoms, custody)
        self.credit_balance(destination, asset, amount_atoms, custody)

    def _auction_rounding_custody(self, auction_id: str) -> str:
        # The hash keeps the derived custody key bounded even when an
        # externally supplied auction identifier reaches its type limit.
        return "auction-rounding:" + hash_v1("m6-auction-rounding-custody-v1", auction_id)

    def accrue_auction_rounding(self, auction_id: str, owner: str, asset: str, remainder_e8: int) -> None:
        if remainder_e8 == 0:
            return
        self.change_atom(
            EconomicAtomKindV1.ROUNDING_BUCKET,
            owner,
            asset,
            self._auction_rounding_custody(auction_id),
            remainder_e8,
        )

    def drain_auction_rounding(self, auction_id: str, owner: str, asset: str) -> None:
        custody = self._auction_rounding_custody(auction_id)
        remainder_e8 = self.atoms_value(EconomicAtomKindV1.ROUNDING_BUCKET, owner, asset, custody)
        if remainder_e8 == 0:
            return
        self.change_atom(EconomicAtomKindV1.ROUNDING_BUCKET, owner, asset, custody, -remainder_e8)
        # This is an accounting-unit sink, denominated in e8 fixed-point
        # residue. It is deliberately separate from token-unit reserve atoms.
        self.change_atom(
            EconomicAtomKindV1.ROUNDING_BUCKET,
            "protocol",
            asset,
            "protocol-rounding-e8",
            remainder_e8,
        )

    def refund_escrow(self, row: SellerAuctionBidStateV1 | PrivateSwapParticipantStateV1) -> None:
        escrow_owner = f"escrow:{row.escrow_id}"
        self.move_balance(escrow_owner, row.bidder if isinstance(row, SellerAuctionBidStateV1) else row.trader, row.bond_asset, row.bond_atoms)
        self.record(ValueDeltaClassV1.REFUND, escrow_owner, row.bond_asset, "ledger", -row.bond_atoms)
        self.record(
            ValueDeltaClassV1.REFUND,
            row.bidder if isinstance(row, SellerAuctionBidStateV1) else row.trader,
            row.bond_asset,
            "ledger",
            row.bond_atoms,
        )

    def slash_escrow(self, row: SellerAuctionBidStateV1 | PrivateSwapParticipantStateV1) -> None:
        escrow_owner = f"escrow:{row.escrow_id}"
        self.change_atom(EconomicAtomKindV1.BALANCE, escrow_owner, row.bond_asset, "ledger", -row.bond_atoms)
        self.change_atom(EconomicAtomKindV1.PROTOCOL_RESERVE, "protocol", row.bond_asset, "reserve", row.bond_atoms)
        self.record(ValueDeltaClassV1.SLASH, escrow_owner, row.bond_asset, "ledger", -row.bond_atoms)
        self.record(ValueDeltaClassV1.SLASH, "protocol", row.bond_asset, "reserve", row.bond_atoms)

    def close_escrow(self, escrow_id: str, terminal_state: str) -> None:
        for index, escrow in enumerate(self.escrows):
            if escrow.escrow_id == escrow_id:
                self.escrows[index] = replace(escrow, amount_atoms=0, terminal_state=terminal_state)
                return
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_ESCROW)

    def finish(self) -> _AppliedBusiness:
        return _AppliedBusiness(
            status=BusinessStatusV1.ACCEPTED,
            reject_reason=None,
            economic_atoms=_atoms_tuple(self.atoms),
            escrows=tuple(sorted(self.escrows, key=lambda item: item.escrow_id)),
            withdrawals=tuple(sorted(self.withdrawals, key=lambda item: item.withdrawal_id)),
            outbox=tuple(self.outbox),
            acknowledgments=tuple(sorted(self.acknowledgments, key=lambda item: item.withdrawal_id)),
            seller_auction_bids=tuple(sorted(self.seller_auction_bids, key=lambda item: item.key)),
            private_swap_participants=tuple(sorted(self.private_swap_participants, key=lambda item: item.key)),
            migration=self.migration,
            delta_entries=tuple(self.deltas[key] for key in sorted(self.deltas)),
        )


def _positive(value: object) -> int:
    if type(value) is not int or value <= 0:
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_AMOUNT)
    return int(value)


def _apply_spot_swap(scratch: _BusinessScratch) -> None:
    asset_in = scratch.text("asset_in")
    asset_out = scratch.text("asset_out")
    pool = scratch.text("pool")
    amount_in = scratch.positive(scratch.field("amount_in_atoms"))
    amount_out = scratch.positive(scratch.field("amount_out_atoms"))
    fee = scratch.nonnegative(scratch.field("fee_atoms", 0))
    if fee > amount_in:
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_AMOUNT)
    reserve_in = scratch.atoms_value(EconomicAtomKindV1.BALANCE, pool, asset_in, "ledger")
    reserve_out = scratch.atoms_value(EconomicAtomKindV1.BALANCE, pool, asset_out, "ledger")
    effective_input = amount_in - fee
    if reserve_in <= 0 or reserve_out <= 0 or effective_input <= 0:
        raise _BusinessFailure(BusinessRejectReasonV1.INSUFFICIENT_RESERVE)
    expected_output = (reserve_out * effective_input) // (reserve_in + effective_input)
    if expected_output <= 0 or expected_output >= reserve_out or amount_out != expected_output:
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_PRICE)
    recipient = scratch.text("recipient", scratch.command.sender)
    scratch.debit_balance(scratch.command.sender, asset_in, amount_in)
    scratch.credit_balance(pool, asset_in, amount_in - fee)
    if fee:
        scratch.credit_balance("protocol", asset_in, fee)
    scratch.debit_balance(pool, asset_out, amount_out)
    scratch.credit_balance(recipient, asset_out, amount_out)


def _apply_lp_add(scratch: _BusinessScratch) -> None:
    asset = scratch.text("asset")
    pool = scratch.text("pool")
    amount = scratch.positive(scratch.field("amount_atoms"))
    shares = scratch.positive(scratch.field("lp_shares_atoms"))
    # The complete pool-share pricing policy is not yet a typed M6 profile.
    # Until it is, equality is the conservative closed-world relation: a
    # caller cannot choose an arbitrary share minting ratio.
    if shares != amount:
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_AMOUNT)
    scratch.debit_balance(scratch.command.sender, asset, amount)
    scratch.credit_balance(pool, asset, amount)
    share_asset = _lp_share_asset(pool, asset)
    scratch.change_atom(EconomicAtomKindV1.LP_SHARE, scratch.command.sender, share_asset, "lp", shares)
    scratch.record(ValueDeltaClassV1.MINT, scratch.command.sender, share_asset, "lp", shares)


def _apply_lp_remove(scratch: _BusinessScratch) -> None:
    asset = scratch.text("asset")
    pool = scratch.text("pool")
    amount = scratch.positive(scratch.field("amount_atoms"))
    shares = scratch.positive(scratch.field("lp_shares_atoms"))
    if shares != amount:
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_AMOUNT)
    share_asset = _lp_share_asset(pool, asset)
    if scratch.atoms_value(EconomicAtomKindV1.LP_SHARE, scratch.command.sender, share_asset, "lp") < shares:
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_AMOUNT)
    scratch.change_atom(EconomicAtomKindV1.LP_SHARE, scratch.command.sender, share_asset, "lp", -shares)
    scratch.record(ValueDeltaClassV1.BURN, scratch.command.sender, share_asset, "lp", -shares)
    scratch.debit_balance(pool, asset, amount)
    scratch.credit_balance(scratch.command.sender, asset, amount)


def _lp_share_asset(pool: str, asset: str) -> str:
    """Return a bounded identity for one pool/underlying-asset share class."""

    return "lp-share:" + hash_v1(
        "m6-lp-share-identity-v1",
        {"pool": pool, "asset": asset},
    )


def _zusd_vault_owner(vault_id: str, sender: str) -> str:
    """Derive a custody identity bound to one sender and vault identifier."""

    return "vault:" + hash_v1(
        "m6-zusd-vault-owner-v1",
        {"vault_id": vault_id, "sender": sender},
    )


def _apply_zusd_borrow(scratch: _BusinessScratch) -> None:
    collateral_asset = scratch.text("collateral_asset")
    vault_id = scratch.text("vault_id")
    collateral = scratch.positive(scratch.field("collateral_atoms"))
    amount = scratch.positive(scratch.field("amount_atoms"))
    # M6 currently lacks a complete oracle/MCR policy.  Keep the reference
    # kernel conservative until that policy is a separate typed input.
    if amount > collateral:
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_AMOUNT)
    vault_owner = _zusd_vault_owner(vault_id, scratch.command.sender)
    scratch.debit_balance(scratch.command.sender, collateral_asset, collateral)
    scratch.credit_balance(scratch.command.sender, "zUSD", amount)
    scratch.change_atom(EconomicAtomKindV1.SUPPLY, "__supply__", "zUSD", "ledger", amount)
    scratch.record(ValueDeltaClassV1.MINT, "__supply__", "zUSD", "ledger", amount)
    scratch.change_atom(EconomicAtomKindV1.DEBT, scratch.command.sender, f"debt:{vault_id}", "liability", amount)
    scratch.record(ValueDeltaClassV1.LIABILITY, scratch.command.sender, f"debt:{vault_id}", "liability", amount)
    scratch.credit_balance(vault_owner, collateral_asset, collateral)


def _apply_zusd_repay(scratch: _BusinessScratch) -> None:
    vault_id = scratch.text("vault_id")
    amount = scratch.positive(scratch.field("amount_atoms"))
    debt_asset = f"debt:{vault_id}"
    if scratch.atoms_value(EconomicAtomKindV1.DEBT, scratch.command.sender, debt_asset, "liability") < amount:
        raise _BusinessFailure(BusinessRejectReasonV1.INSUFFICIENT_BALANCE)
    scratch.debit_balance(scratch.command.sender, "zUSD", amount)
    scratch.change_atom(EconomicAtomKindV1.SUPPLY, "__supply__", "zUSD", "ledger", -amount)
    scratch.record(ValueDeltaClassV1.BURN, "__supply__", "zUSD", "ledger", -amount)
    scratch.change_atom(EconomicAtomKindV1.DEBT, scratch.command.sender, debt_asset, "liability", -amount)
    scratch.record(ValueDeltaClassV1.LIABILITY, scratch.command.sender, debt_asset, "liability", -amount)


def _apply_zusd_redeem(scratch: _BusinessScratch) -> None:
    vault_id = scratch.text("vault_id")
    collateral_asset = scratch.text("collateral_asset")
    amount = scratch.positive(scratch.field("amount_atoms"))
    debt_asset = f"debt:{vault_id}"
    if scratch.atoms_value(EconomicAtomKindV1.DEBT, scratch.command.sender, debt_asset, "liability") < amount:
        raise _BusinessFailure(BusinessRejectReasonV1.INSUFFICIENT_BALANCE)
    scratch.debit_balance(scratch.command.sender, "zUSD", amount)
    scratch.change_atom(EconomicAtomKindV1.SUPPLY, "__supply__", "zUSD", "ledger", -amount)
    scratch.record(ValueDeltaClassV1.BURN, "__supply__", "zUSD", "ledger", -amount)
    scratch.change_atom(EconomicAtomKindV1.DEBT, scratch.command.sender, debt_asset, "liability", -amount)
    scratch.record(ValueDeltaClassV1.LIABILITY, scratch.command.sender, debt_asset, "liability", -amount)
    scratch.debit_balance(
        _zusd_vault_owner(vault_id, scratch.command.sender),
        collateral_asset,
        amount,
    )
    scratch.credit_balance(scratch.command.sender, collateral_asset, amount)


def _apply_zusd_liquidate(scratch: _BusinessScratch) -> None:
    vault_id = scratch.text("vault_id")
    debtor = scratch.text("debtor")
    collateral_asset = scratch.text("collateral_asset")
    debt = scratch.positive(scratch.field("debt_atoms"))
    collateral = scratch.positive(scratch.field("collateral_atoms"))
    debt_asset = f"debt:{vault_id}"
    if scratch.atoms_value(EconomicAtomKindV1.DEBT, debtor, debt_asset, "liability") < debt:
        raise _BusinessFailure(BusinessRejectReasonV1.INSUFFICIENT_BALANCE)
    scratch.debit_balance(scratch.command.sender, "zUSD", debt)
    scratch.change_atom(EconomicAtomKindV1.SUPPLY, "__supply__", "zUSD", "ledger", -debt)
    scratch.record(ValueDeltaClassV1.BURN, "__supply__", "zUSD", "ledger", -debt)
    scratch.change_atom(EconomicAtomKindV1.DEBT, debtor, debt_asset, "liability", -debt)
    scratch.record(ValueDeltaClassV1.LIABILITY, debtor, debt_asset, "liability", -debt)
    scratch.debit_balance(_zusd_vault_owner(vault_id, debtor), collateral_asset, collateral)
    scratch.credit_balance(scratch.command.sender, collateral_asset, collateral)


def _apply_stability_deposit(scratch: _BusinessScratch) -> None:
    amount = scratch.positive(scratch.field("amount_atoms"))
    scratch.simple_transfer("zUSD", amount, "stability_pool")
    # The pool balance is shared custody.  A separate claim atom makes the
    # withdrawing authority belong to the depositor instead of to any
    # authenticated caller who can name the global pool.
    scratch.change_atom(
        EconomicAtomKindV1.STABILITY_POOL_SHARE,
        scratch.command.sender,
        "zUSD",
        "stability_pool",
        amount,
    )
    scratch.record(
        ValueDeltaClassV1.LIABILITY,
        scratch.command.sender,
        "zUSD",
        "stability_pool",
        amount,
    )


def _apply_stability_withdraw(scratch: _BusinessScratch) -> None:
    amount = scratch.positive(scratch.field("amount_atoms"))
    if scratch.atoms_value(
        EconomicAtomKindV1.STABILITY_POOL_SHARE,
        scratch.command.sender,
        "zUSD",
        "stability_pool",
    ) < amount:
        raise _BusinessFailure(BusinessRejectReasonV1.INSUFFICIENT_BALANCE)
    scratch.debit_balance("stability_pool", "zUSD", amount)
    scratch.change_atom(
        EconomicAtomKindV1.STABILITY_POOL_SHARE,
        scratch.command.sender,
        "zUSD",
        "stability_pool",
        -amount,
    )
    scratch.record(
        ValueDeltaClassV1.LIABILITY,
        scratch.command.sender,
        "zUSD",
        "stability_pool",
        -amount,
    )
    scratch.credit_balance(scratch.command.sender, "zUSD", amount)


def _apply_zusd_redistribute(scratch: _BusinessScratch) -> None:
    collateral_asset = scratch.text("collateral_asset")
    source_vault = scratch.text("source_vault")
    amount = scratch.positive(scratch.field("collateral_atoms"))
    zusd_amount = scratch.positive(scratch.field("amount_atoms"))
    scratch.debit_balance(source_vault, collateral_asset, amount)
    scratch.credit_balance(scratch.command.sender, collateral_asset, amount)
    scratch.debit_balance(scratch.command.sender, "zUSD", zusd_amount)
    scratch.credit_balance(source_vault, "zUSD", zusd_amount)


def _apply_perp_open(scratch: _BusinessScratch) -> None:
    market = scratch.text("market")
    margin = scratch.positive(scratch.field("margin_atoms"))
    size = scratch.positive(scratch.field("size_atoms"))
    price = scratch.positive(scratch.field("price_e8"))
    if price > MAX_PRICE_E8_V1:
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_PRICE)
    if scratch.atoms_value(EconomicAtomKindV1.POSITION, scratch.command.sender, market, "perp"):
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_PHASE)
    scratch.simple_transfer("zUSD", margin, f"perp:{market}")
    scratch.change_atom(EconomicAtomKindV1.MARGIN, scratch.command.sender, market, "perp", margin)
    scratch.change_atom(EconomicAtomKindV1.POSITION, scratch.command.sender, market, "perp", size)
    scratch.change_atom(
        EconomicAtomKindV1.POSITION_ENTRY_PRICE,
        scratch.command.sender,
        market,
        "perp:e8",
        price,
    )
    scratch.record(ValueDeltaClassV1.LIABILITY, scratch.command.sender, f"position:{market}", "perp", size)


def _apply_perp_close(scratch: _BusinessScratch) -> None:
    market = scratch.text("market")
    size = scratch.positive(scratch.field("size_atoms"))
    pnl = scratch.field("pnl_atoms")
    if type(pnl) is not int:
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_AMOUNT)
    # A caller-authored PnL is not an execution proof.  The current reference
    # profile supports the zero-PnL close lifecycle and rejects both positive
    # and negative settlement until exit-price/oracle policy is typed and
    # subject-bound.
    if pnl != 0:
        raise _BusinessFailure(BusinessRejectReasonV1.UNSUPPORTED_OPERATION)
    position = scratch.atoms_value(EconomicAtomKindV1.POSITION, scratch.command.sender, market, "perp")
    if position != size:
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_AMOUNT)
    margin = scratch.atoms_value(EconomicAtomKindV1.MARGIN, scratch.command.sender, market, "perp")
    if margin <= 0:
        raise _BusinessFailure(BusinessRejectReasonV1.INSUFFICIENT_BALANCE)
    entry_price = scratch.atoms_value(
        EconomicAtomKindV1.POSITION_ENTRY_PRICE,
        scratch.command.sender,
        market,
        "perp:e8",
    )
    if entry_price <= 0:
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_AUTHORITY)
    scratch.change_atom(EconomicAtomKindV1.POSITION, scratch.command.sender, market, "perp", -size)
    scratch.change_atom(
        EconomicAtomKindV1.POSITION_ENTRY_PRICE,
        scratch.command.sender,
        market,
        "perp:e8",
        -entry_price,
    )
    scratch.change_atom(EconomicAtomKindV1.MARGIN, scratch.command.sender, market, "perp", -margin)
    scratch.record(ValueDeltaClassV1.LIABILITY, scratch.command.sender, f"position:{market}", "perp", -size)
    scratch.move_balance(f"perp:{market}", scratch.command.sender, "zUSD", margin)
    if pnl > 0:
        scratch.move_balance(f"perp:{market}", scratch.command.sender, "zUSD", pnl)
    elif pnl < 0:
        scratch.move_balance(scratch.command.sender, f"perp:{market}", "zUSD", -pnl)


def _apply_perp_funding(scratch: _BusinessScratch) -> None:
    scratch.simple_transfer("zUSD", scratch.positive(scratch.field("amount_atoms")), f"perp:{scratch.text('market')}")


def _apply_perp_liquidate(scratch: _BusinessScratch) -> None:
    market = scratch.text("market")
    margin = scratch.positive(scratch.field("margin_atoms"))
    insurance = scratch.positive(scratch.field("insurance_atoms"))
    position = scratch.atoms_value(EconomicAtomKindV1.POSITION, scratch.command.sender, market, "perp")
    if position <= 0:
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_AMOUNT)
    current_margin = scratch.atoms_value(EconomicAtomKindV1.MARGIN, scratch.command.sender, market, "perp")
    if current_margin != margin:
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_AMOUNT)
    entry_price = scratch.atoms_value(
        EconomicAtomKindV1.POSITION_ENTRY_PRICE,
        scratch.command.sender,
        market,
        "perp:e8",
    )
    if entry_price <= 0:
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_AUTHORITY)
    scratch.change_atom(EconomicAtomKindV1.POSITION, scratch.command.sender, market, "perp", -position)
    scratch.change_atom(
        EconomicAtomKindV1.POSITION_ENTRY_PRICE,
        scratch.command.sender,
        market,
        "perp:e8",
        -entry_price,
    )
    scratch.change_atom(EconomicAtomKindV1.MARGIN, scratch.command.sender, market, "perp", -margin)
    # Insurance is a custody claim over funded zUSD.  The previous reference
    # path created the insurance atom without debiting any source custody.
    scratch.move_balance(f"perp:{market}", "insurance", "zUSD", insurance)
    scratch.change_atom(EconomicAtomKindV1.INSURANCE, "insurance", market, "perp", insurance)
    scratch.record(ValueDeltaClassV1.LIABILITY, scratch.command.sender, f"position:{market}", "perp", -margin)


def _oracle_price_asset(oracle_id: str) -> str:
    return "oracle-price:" + hash_v1("m6-oracle-price-identity-v1", oracle_id)


def _apply_oracle_submit(scratch: _BusinessScratch) -> None:
    bond = scratch.positive(scratch.field("bond_atoms"))
    oracle_id = scratch.text("oracle_id")
    price = scratch.positive(scratch.field("price_e8"))
    if price > MAX_PRICE_E8_V1:
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_PRICE)
    scratch.simple_transfer("zUSD", bond, f"oracle:{oracle_id}")
    scratch.change_atom(EconomicAtomKindV1.ORACLE_BOND, scratch.command.sender, oracle_id, "oracle", bond)
    price_asset = _oracle_price_asset(oracle_id)
    previous_price = scratch.atoms_value(
        EconomicAtomKindV1.ORACLE_PRICE,
        "oracle",
        price_asset,
        "price-e8",
    )
    if previous_price:
        scratch.change_atom(
            EconomicAtomKindV1.ORACLE_PRICE,
            "oracle",
            price_asset,
            "price-e8",
            -previous_price,
        )
    scratch.change_atom(EconomicAtomKindV1.ORACLE_PRICE, "oracle", price_asset, "price-e8", price)


def _apply_oracle_dispute(scratch: _BusinessScratch) -> None:
    del scratch
    # Dispute adjudication needs a typed oracle observation, bond ownership,
    # deadline, and outcome policy.  Accepting this command while ignoring
    # those fields would let an authenticated sender manufacture an outcome.
    raise _BusinessFailure(BusinessRejectReasonV1.UNSUPPORTED_OPERATION)


def _apply_protocol_buy_and_burn(scratch: _BusinessScratch) -> None:
    del scratch
    # The reference state has no typed protocol-asset identity, purchase
    # evidence, or owning burn kernel.  Mutating arbitrary reserve and supply
    # atoms here would bypass that authority boundary, so this launch command
    # remains an explicit committed failure until the kernel is versioned.
    raise _BusinessFailure(BusinessRejectReasonV1.UNSUPPORTED_OPERATION)


def _apply_prover_reward(scratch: _BusinessScratch) -> None:
    asset = scratch.text("reward_asset")
    amount = scratch.positive(scratch.field("amount_atoms"))
    prover = scratch.text("prover")
    scratch.change_atom(EconomicAtomKindV1.PROTOCOL_RESERVE, "protocol", asset, "reserve", -amount)
    scratch.change_atom(EconomicAtomKindV1.REWARD, prover, asset, "reward", amount)
    scratch.record(ValueDeltaClassV1.INTERNAL_TRANSFER, "protocol", asset, "reserve", -amount)
    scratch.record(ValueDeltaClassV1.INTERNAL_TRANSFER, prover, asset, "reward", amount)


def _apply_seller_auction_commit(scratch: _BusinessScratch) -> None:
    auction_id = scratch.text("auction_id")
    asset = scratch.text("bond_asset")
    amount = scratch.positive(scratch.field("bond_atoms"))
    commitment = scratch.root_text("commitment")
    commit_height, reveal_deadline, settle_deadline = scratch.deadlines()
    existing = [row for row in scratch.seller_auction_bids if row.auction_id == auction_id]
    if any(
        row.bond_asset != asset
        or row.commit_height != commit_height
        or row.reveal_deadline_height != reveal_deadline
        or row.settle_deadline_height != settle_deadline
        for row in existing
    ):
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_DEADLINE)
    if any(row.key == (auction_id, scratch.command.sender, commitment) for row in existing):
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_COMMITMENT)
    escrow_id = hash_v1(
        "m6-seller-auction-escrow-v1",
        {"auction_id": auction_id, "bidder": scratch.command.sender, "commitment": commitment},
    )
    scratch.simple_transfer(asset, amount, f"escrow:{escrow_id}")
    scratch.escrows.append(EscrowAtomV1(escrow_id, scratch.command.sender, asset, amount, "seller_commit"))
    scratch.seller_auction_bids.append(
        SellerAuctionBidStateV1(
            auction_id=auction_id,
            bidder=scratch.command.sender,
            escrow_id=escrow_id,
            bond_asset=asset,
            bond_atoms=amount,
            commitment=commitment,
            commit_height=commit_height,
            reveal_deadline_height=reveal_deadline,
            settle_deadline_height=settle_deadline,
        )
    )


def _apply_private_swap_commit(scratch: _BusinessScratch) -> None:
    batch_id = scratch.text("batch_id")
    asset = scratch.text("bond_asset")
    amount = scratch.positive(scratch.field("bond_atoms"))
    commitment = scratch.root_text("commitment")
    commit_height, reveal_deadline, settle_deadline = scratch.deadlines()
    existing = [row for row in scratch.private_swap_participants if row.batch_id == batch_id]
    if any(
        row.bond_asset != asset
        or row.commit_height != commit_height
        or row.reveal_deadline_height != reveal_deadline
        or row.settle_deadline_height != settle_deadline
        for row in existing
    ):
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_DEADLINE)
    if any(row.key == (batch_id, scratch.command.sender, commitment) for row in existing):
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_COMMITMENT)
    escrow_id = hash_v1(
        "m6-private-swap-escrow-v1",
        {"batch_id": batch_id, "trader": scratch.command.sender, "commitment": commitment},
    )
    scratch.simple_transfer(asset, amount, f"escrow:{escrow_id}")
    scratch.escrows.append(EscrowAtomV1(escrow_id, scratch.command.sender, asset, amount, "private_swap_commit"))
    scratch.private_swap_participants.append(
        PrivateSwapParticipantStateV1(
            batch_id=batch_id,
            trader=scratch.command.sender,
            escrow_id=escrow_id,
            bond_asset=asset,
            bond_atoms=amount,
            commitment=commitment,
            commit_height=commit_height,
            reveal_deadline_height=reveal_deadline,
            settle_deadline_height=settle_deadline,
        )
    )


def _apply_seller_auction_reveal(scratch: _BusinessScratch) -> None:
    auction_id = scratch.text("auction_id")
    inventory_asset = scratch.text("inventory_asset")
    quantity = scratch.positive(scratch.field("quantity_atoms"))
    price = scratch.positive(scratch.field("price_e8"))
    nonce = scratch.positive(scratch.field("nonce"))
    if price > MAX_SEALED_BID_PRICE_E8_V1:
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_PRICE)
    commitment = hash_v1(
        "m6-seller-auction-reveal-v1",
        {
            "auction_id": auction_id,
            "bidder": scratch.command.sender,
            "inventory_asset": inventory_asset,
            "quantity_atoms": quantity,
            "price_e8": price,
            "nonce": nonce,
        },
    )
    matches = [
        (index, row)
        for index, row in enumerate(scratch.seller_auction_bids)
        if row.auction_id == auction_id
        and row.bidder == scratch.command.sender
        and row.commitment == commitment
        and row.phase is SellerAuctionPhaseV1.COMMIT
    ]
    if len(matches) != 1:
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_COMMITMENT)
    index, row = matches[0]
    if not row.commit_height < scratch.ledger_height <= row.reveal_deadline_height:
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_DEADLINE)
    if any(
        other.auction_id == auction_id
        and other.inventory_asset is not None
        and other.inventory_asset != inventory_asset
        for other in scratch.seller_auction_bids
    ):
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_ASSET)
    scratch.seller_auction_bids[index] = replace(
        row,
        inventory_asset=inventory_asset,
        quantity_atoms=quantity,
        price_e8=price,
        reveal_nonce=nonce,
        phase=SellerAuctionPhaseV1.REVEAL,
    )


def _apply_private_swap_reveal(scratch: _BusinessScratch) -> None:
    batch_id = scratch.text("batch_id")
    asset_in = scratch.text("asset_in")
    amount_in = scratch.positive(scratch.field("amount_in_atoms"))
    asset_out = scratch.text("asset_out")
    amount_out = scratch.positive(scratch.field("amount_out_atoms"))
    nonce = scratch.positive(scratch.field("nonce"))
    if asset_in == asset_out:
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_ASSET)
    commitment = hash_v1(
        "m6-private-swap-reveal-v1",
        {
            "batch_id": batch_id,
            "trader": scratch.command.sender,
            "asset_in": asset_in,
            "amount_in_atoms": amount_in,
            "asset_out": asset_out,
            "amount_out_atoms": amount_out,
            "nonce": nonce,
        },
    )
    matches = [
        (index, row)
        for index, row in enumerate(scratch.private_swap_participants)
        if row.batch_id == batch_id
        and row.trader == scratch.command.sender
        and row.commitment == commitment
        and row.phase is PrivateSwapPhaseV1.COMMIT
    ]
    if len(matches) != 1:
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_COMMITMENT)
    index, row = matches[0]
    if not row.commit_height < scratch.ledger_height <= row.reveal_deadline_height:
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_DEADLINE)
    scratch.private_swap_participants[index] = replace(
        row,
        asset_in=asset_in,
        amount_in_atoms=amount_in,
        asset_out=asset_out,
        amount_out_atoms=amount_out,
        reveal_nonce=nonce,
        phase=PrivateSwapPhaseV1.REVEAL,
    )


def _ceil_price_payment(quantity_atoms: int, price_e8: int) -> int:
    numerator = quantity_atoms * price_e8
    return (numerator + SEALED_BID_PRICE_SCALE_E8_V1 - 1) // SEALED_BID_PRICE_SCALE_E8_V1


def _seller_fill_plan(
    rows: list[SellerAuctionBidStateV1], inventory_atoms: int
) -> tuple[int, dict[tuple[str, str, str], int]]:
    revealed = [row for row in rows if row.phase is SellerAuctionPhaseV1.REVEAL]
    if not revealed or inventory_atoms <= 0:
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_PHASE)
    ordered = sorted(revealed, key=lambda row: (-int(row.price_e8 or 0), row.bidder, row.commitment))
    remaining = inventory_atoms
    fills: dict[tuple[str, str, str], int] = {}
    clearing_price = 0
    price_values = tuple(sorted({int(row.price_e8 or 0) for row in ordered}, reverse=True))
    for price in price_values:
        bucket = tuple(row for row in ordered if row.price_e8 == price)
        if remaining <= 0:
            break
        requested = sum(int(row.quantity_atoms or 0) for row in bucket)
        if requested <= remaining:
            for row in bucket:
                fills[row.key] = int(row.quantity_atoms or 0)
            remaining -= requested
            clearing_price = price
            continue
        allocated = 0
        allocations: list[tuple[int, SellerAuctionBidStateV1, int, int]] = []
        for position, row in enumerate(bucket):
            quantity = int(row.quantity_atoms or 0)
            numerator = quantity * remaining
            base = numerator // requested
            remainder = numerator % requested
            allocated += base
            allocations.append((position, row, base, remainder))
        leftover = remaining - allocated
        ranked = sorted(
            allocations,
            key=lambda item: (-item[3], item[1].bidder, item[1].commitment, item[0]),
        )
        bonus_positions = {item[0] for item in ranked[:leftover]}
        for position, row, base, _remainder in allocations:
            fill = base + (1 if position in bonus_positions else 0)
            if fill:
                fills[row.key] = fill
        clearing_price = price
        remaining = 0
    if clearing_price == 0:
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_PHASE)
    return clearing_price, fills


def _apply_seller_auction_settle(scratch: _BusinessScratch) -> None:
    auction_id = scratch.text("auction_id")
    clearing_price = scratch.positive(scratch.field("clearing_price_e8"))
    if clearing_price > MAX_SEALED_BID_PRICE_E8_V1:
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_PRICE)
    rows = [
        row for row in scratch.seller_auction_bids
        if row.auction_id == auction_id
        and row.phase in (SellerAuctionPhaseV1.COMMIT, SellerAuctionPhaseV1.REVEAL)
    ]
    if not rows:
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_PHASE)
    first = rows[0]
    if any(
        row.commit_height != first.commit_height
        or row.reveal_deadline_height != first.reveal_deadline_height
        or row.settle_deadline_height != first.settle_deadline_height
        for row in rows
    ):
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_DEADLINE)
    if not first.reveal_deadline_height < scratch.ledger_height <= first.settle_deadline_height:
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_DEADLINE)
    revealed = [row for row in rows if row.phase is SellerAuctionPhaseV1.REVEAL]
    if not revealed or any(row.inventory_asset != revealed[0].inventory_asset for row in revealed):
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_ASSET)
    inventory_asset = str(revealed[0].inventory_asset)
    inventory_owner = f"auction:{auction_id}"
    inventory_atoms = scratch.atoms_value(EconomicAtomKindV1.BALANCE, inventory_owner, inventory_asset, "ledger")
    derived_price, fills = _seller_fill_plan(rows, inventory_atoms)
    if clearing_price != derived_price:
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_PRICE)
    payment_plan: dict[tuple[str, str, str], tuple[int, int]] = {}
    for row in revealed:
        fill = fills.get(row.key, 0)
        payment = _ceil_price_payment(fill, clearing_price) if fill else 0
        # Integer payment rounding is charged to the auction custody owner;
        # the terminal row records the exact e8 remainder for its drain audit.
        rounding_remainder = (
            payment * SEALED_BID_PRICE_SCALE_E8_V1 - fill * clearing_price
            if fill
            else 0
        )
        if payment and scratch.atoms_value(EconomicAtomKindV1.BALANCE, row.bidder, row.bond_asset, "ledger") < payment:
            raise _BusinessFailure(BusinessRejectReasonV1.INSUFFICIENT_BALANCE)
        payment_plan[row.key] = (payment, rounding_remainder)
    for index, row in enumerate(scratch.seller_auction_bids):
        if row.auction_id != auction_id or row.phase not in (SellerAuctionPhaseV1.COMMIT, SellerAuctionPhaseV1.REVEAL):
            continue
        if row.phase is SellerAuctionPhaseV1.COMMIT:
            scratch.slash_escrow(row)
            scratch.close_escrow(row.escrow_id, "seller_expired_non_reveal")
            scratch.seller_auction_bids[index] = replace(row, phase=SellerAuctionPhaseV1.EXPIRED)
            continue
        fill = fills.get(row.key, 0)
        payment, rounding_remainder = payment_plan[row.key]
        if fill:
            scratch.accrue_auction_rounding(auction_id, inventory_owner, row.bond_asset, rounding_remainder)
            scratch.move_balance(inventory_owner, row.bidder, inventory_asset, fill)
            scratch.move_balance(row.bidder, inventory_owner, row.bond_asset, payment)
        scratch.refund_escrow(row)
        scratch.close_escrow(row.escrow_id, "seller_settled")
        scratch.seller_auction_bids[index] = replace(
            row,
            filled_quantity_atoms=fill,
            paid_atoms=payment,
            rounding_remainder_e8=rounding_remainder,
            phase=SellerAuctionPhaseV1.SETTLE,
        )
    scratch.drain_auction_rounding(auction_id, inventory_owner, first.bond_asset)


def _optional_commitment(scratch: _BusinessScratch) -> str | None:
    raw = scratch.field("commitment")
    if raw is None:
        return None
    if not isinstance(raw, str):
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_COMMITMENT)
    return scratch.root_text("commitment")


def _apply_seller_auction_cancel(scratch: _BusinessScratch) -> None:
    auction_id = scratch.text("auction_id")
    commitment = _optional_commitment(scratch)
    matches = [
        (index, row)
        for index, row in enumerate(scratch.seller_auction_bids)
        if row.auction_id == auction_id
        and row.bidder == scratch.command.sender
        and row.phase is SellerAuctionPhaseV1.COMMIT
        and (commitment is None or row.commitment == commitment)
    ]
    if len(matches) != 1:
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_PHASE)
    index, row = matches[0]
    if scratch.ledger_height != row.commit_height:
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_DEADLINE)
    scratch.refund_escrow(row)
    scratch.close_escrow(row.escrow_id, "seller_cancelled")
    scratch.seller_auction_bids[index] = replace(row, phase=SellerAuctionPhaseV1.CANCELLED)


def _apply_seller_auction_expire(scratch: _BusinessScratch) -> None:
    auction_id = scratch.text("auction_id")
    indexes = [
        index for index, row in enumerate(scratch.seller_auction_bids)
        if row.auction_id == auction_id
        and row.phase in (SellerAuctionPhaseV1.COMMIT, SellerAuctionPhaseV1.REVEAL)
    ]
    if not indexes:
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_PHASE)
    rows = [scratch.seller_auction_bids[index] for index in indexes]
    if any(
        row.commit_height != rows[0].commit_height
        or row.reveal_deadline_height != rows[0].reveal_deadline_height
        or row.settle_deadline_height != rows[0].settle_deadline_height
        for row in rows
    ):
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_DEADLINE)
    if scratch.ledger_height <= rows[0].settle_deadline_height:
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_DEADLINE)
    for index in indexes:
        row = scratch.seller_auction_bids[index]
        if row.phase is SellerAuctionPhaseV1.COMMIT:
            scratch.slash_escrow(row)
        else:
            scratch.refund_escrow(row)
        scratch.close_escrow(row.escrow_id, "seller_expired")
        scratch.seller_auction_bids[index] = replace(row, phase=SellerAuctionPhaseV1.EXPIRED)


def _private_clearing_root(batch_id: str, rows: list[PrivateSwapParticipantStateV1]) -> str:
    revealed = tuple(
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
    )
    return hash_v1("m6-private-swap-clearing-v1", {"batch_id": batch_id, "participants": revealed})


def _apply_private_swap_settle(scratch: _BusinessScratch) -> None:
    batch_id = scratch.text("batch_id")
    clearing_root = scratch.root_text("clearing_root")
    rows = [
        row for row in scratch.private_swap_participants
        if row.batch_id == batch_id
        and row.phase in (PrivateSwapPhaseV1.COMMIT, PrivateSwapPhaseV1.REVEAL)
    ]
    if len(rows) != 2 or any(row.phase is not PrivateSwapPhaseV1.REVEAL for row in rows):
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_PHASE)
    first = rows[0]
    if not first.reveal_deadline_height < scratch.ledger_height <= first.settle_deadline_height:
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_DEADLINE)
    if any(
        row.commit_height != first.commit_height
        or row.reveal_deadline_height != first.reveal_deadline_height
        or row.settle_deadline_height != first.settle_deadline_height
        for row in rows
    ):
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_PHASE)
    if len({row.trader for row in rows}) != 2:
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_PHASE)
    if _private_clearing_root(batch_id, rows) != clearing_root:
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_COMMITMENT)
    left, right = sorted(rows, key=lambda item: item.key)
    if not (
        left.asset_in == right.asset_out
        and left.amount_in_atoms == right.amount_out_atoms
        and right.asset_in == left.asset_out
        and right.amount_in_atoms == left.amount_out_atoms
    ):
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_AMOUNT)
    for row in rows:
        if scratch.atoms_value(EconomicAtomKindV1.BALANCE, row.trader, str(row.asset_in), "ledger") < int(row.amount_in_atoms or 0):
            raise _BusinessFailure(BusinessRejectReasonV1.INSUFFICIENT_BALANCE)
    scratch.move_balance(left.trader, right.trader, str(left.asset_in), int(left.amount_in_atoms or 0))
    scratch.move_balance(right.trader, left.trader, str(right.asset_in), int(right.amount_in_atoms or 0))
    for index, row in enumerate(scratch.private_swap_participants):
        if row.key not in {item.key for item in rows}:
            continue
        scratch.refund_escrow(row)
        scratch.close_escrow(row.escrow_id, "private_swap_settled")
        scratch.private_swap_participants[index] = replace(row, phase=PrivateSwapPhaseV1.SETTLE)


def _apply_private_swap_cancel(scratch: _BusinessScratch) -> None:
    batch_id = scratch.text("batch_id")
    commitment = _optional_commitment(scratch)
    matches = [
        (index, row)
        for index, row in enumerate(scratch.private_swap_participants)
        if row.batch_id == batch_id
        and row.trader == scratch.command.sender
        and row.phase is PrivateSwapPhaseV1.COMMIT
        and (commitment is None or row.commitment == commitment)
    ]
    if len(matches) != 1:
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_PHASE)
    index, row = matches[0]
    if scratch.ledger_height != row.commit_height:
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_DEADLINE)
    scratch.refund_escrow(row)
    scratch.close_escrow(row.escrow_id, "private_swap_cancelled")
    scratch.private_swap_participants[index] = replace(row, phase=PrivateSwapPhaseV1.CANCELLED)


def _apply_private_swap_expire(scratch: _BusinessScratch) -> None:
    batch_id = scratch.text("batch_id")
    indexes = [
        index for index, row in enumerate(scratch.private_swap_participants)
        if row.batch_id == batch_id
        and row.phase in (PrivateSwapPhaseV1.COMMIT, PrivateSwapPhaseV1.REVEAL)
    ]
    if not indexes:
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_PHASE)
    rows = [scratch.private_swap_participants[index] for index in indexes]
    if any(
        row.commit_height != rows[0].commit_height
        or row.reveal_deadline_height != rows[0].reveal_deadline_height
        or row.settle_deadline_height != rows[0].settle_deadline_height
        for row in rows
    ):
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_DEADLINE)
    if scratch.ledger_height <= rows[0].settle_deadline_height:
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_DEADLINE)
    for index in indexes:
        row = scratch.private_swap_participants[index]
        if row.phase is PrivateSwapPhaseV1.COMMIT:
            scratch.slash_escrow(row)
        else:
            scratch.refund_escrow(row)
        scratch.close_escrow(row.escrow_id, "private_swap_expired")
        scratch.private_swap_participants[index] = replace(row, phase=PrivateSwapPhaseV1.EXPIRED)


def _authority_payload(
    scratch: _BusinessScratch,
    kind: GlobalCommandKindV1,
    expected_type: type[object],
) -> object:
    evidence = scratch.authority_evidence
    if evidence is None:
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_AUTHORITY)
    if (
        evidence.kind is not kind
        or evidence.subject_root != scratch.subject_root
        or evidence.pre_state_root != scratch.pre_state_root
        or evidence.command_hash != scratch.command.command_hash
        or not isinstance(evidence.payload, expected_type)
    ):
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_AUTHORITY)
    return evidence.payload


def _apply_tau_escrow_deposit(scratch: _BusinessScratch) -> None:
    deposit_id = scratch.text("deposit_id")
    asset = scratch.text("asset")
    amount = scratch.positive(scratch.field("amount_atoms"))
    transaction_root = scratch.root_text("tau_transaction_root")
    finality_root = scratch.root_text("tau_finality_root")
    profile_root = scratch.root_text("tau_profile_root")
    finality_height_value = scratch.field("tau_finality_height", default=0)
    if not isinstance(finality_height_value, int) or isinstance(finality_height_value, bool):
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_AUTHORITY)
    finality_height = finality_height_value
    payload = _authority_payload(
        scratch,
        GlobalCommandKindV1.TAU_ESCROW_DEPOSIT,
        TauEscrowDepositProofV1,
    )
    if not isinstance(payload, TauEscrowDepositProofV1):
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_AUTHORITY)
    if (
        payload.deposit_id != deposit_id
        or payload.tau_transaction_root != transaction_root
        or payload.tau_finality_root != finality_root
        or payload.tau_profile_root != profile_root
        or payload.tau_finality_height != finality_height
        or payload.beneficiary != scratch.command.sender
        or payload.asset != asset
        or payload.amount_atoms != amount
    ):
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_AUTHORITY)
    if any(escrow.escrow_id == deposit_id for escrow in scratch.escrows):
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_ESCROW)
    proof = TauEscrowDepositProofV1(
        deposit_id=deposit_id,
        tau_transaction_root=transaction_root,
        tau_finality_root=finality_root,
        tau_profile_root=profile_root,
        beneficiary=scratch.command.sender,
        asset=asset,
        amount_atoms=amount,
        tau_finality_height=finality_height,
    )
    if proof.tau_profile_root != scratch.tau_profile:
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_ESCROW)
    scratch.escrows.append(
        EscrowAtomV1(
            deposit_id,
            scratch.command.sender,
            asset,
            amount,
            f"tau_finalized:{proof.proof_root}",
        )
    )
    scratch.change_atom(EconomicAtomKindV1.ESCROW, scratch.command.sender, asset, "tau_escrow", amount)
    scratch.record(ValueDeltaClassV1.EXTERNAL_IN, scratch.command.sender, asset, "tau_escrow", amount)


def _apply_tau_withdrawal(scratch: _BusinessScratch) -> None:
    withdrawal_id = scratch.text("withdrawal_id")
    asset = scratch.text("asset")
    destination = scratch.text("destination")
    amount = scratch.positive(scratch.field("amount_atoms"))
    if any(item.withdrawal_id == withdrawal_id for item in scratch.withdrawals):
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_WITHDRAWAL)
    scratch.debit_balance(scratch.command.sender, asset, amount)
    scratch.change_atom(EconomicAtomKindV1.WITHDRAWAL_LIABILITY, scratch.command.sender, asset, "tau", amount)
    candidate_id = hash_v1(
        "m6-withdrawal-candidate-v1",
        {"command": scratch.command.command_hash, "id": withdrawal_id},
    )
    scratch.withdrawals.append(
        TauWithdrawalIntentV1(
            withdrawal_id=withdrawal_id,
            # The internal requester owns acknowledgment authority.  The Tau
            # destination remains bound in the outbox atom.
            beneficiary=scratch.command.sender,
            asset=asset,
            amount_atoms=amount,
            source_state_root=scratch.pre_state_root,
            candidate_id=candidate_id,
        )
    )
    scratch.outbox.append(
        OutboxAtomV1(
            effect_id=withdrawal_id,
            effect_type="tau_withdrawal",
            destination=destination,
            asset=asset,
            amount_atoms=amount,
            source_state_root=scratch.pre_state_root,
        )
    )
    scratch.record(ValueDeltaClassV1.EXTERNAL_OUT, scratch.command.sender, asset, "tau", -amount)
    scratch.record(ValueDeltaClassV1.LIABILITY, scratch.command.sender, asset, "tau", amount)


def _apply_tau_withdrawal_ack(scratch: _BusinessScratch) -> None:
    withdrawal_id = scratch.text("withdrawal_id")
    ack_root = scratch.root_text("ack_root")
    receipt_root = scratch.root_text("tau_receipt_root")
    receipt_height_value = scratch.field("tau_receipt_height", default=0)
    if not isinstance(receipt_height_value, int) or isinstance(receipt_height_value, bool):
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_AUTHORITY)
    receipt_height = receipt_height_value
    payload = _authority_payload(
        scratch,
        GlobalCommandKindV1.TAU_WITHDRAWAL_ACK,
        WithdrawalAcknowledgmentV1,
    )
    if not isinstance(payload, WithdrawalAcknowledgmentV1):
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_AUTHORITY)
    index = next((i for i, item in enumerate(scratch.withdrawals) if item.withdrawal_id == withdrawal_id), None)
    if index is None or scratch.withdrawals[index].status is not TauWithdrawalStatusV1.PENDING:
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_WITHDRAWAL)
    withdrawal = scratch.withdrawals[index]
    if withdrawal.beneficiary != scratch.command.sender:
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_WITHDRAWAL)
    if (
        payload.withdrawal_id != withdrawal_id
        or payload.acknowledged_state_root != ack_root
        or payload.tau_receipt_root != receipt_root
        or payload.tau_receipt_height != receipt_height
        or payload.provenance_root != withdrawal.source_state_root
    ):
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_AUTHORITY)
    scratch.withdrawals[index] = replace(withdrawal, status=TauWithdrawalStatusV1.ACKNOWLEDGED)
    scratch.acknowledgments.append(
        WithdrawalAcknowledgmentV1(
            withdrawal_id=withdrawal_id,
            provenance_root=withdrawal.source_state_root,
            tau_receipt_root=receipt_root,
            acknowledged_state_root=ack_root,
            tau_receipt_height=receipt_height,
        )
    )
    scratch.change_atom(
        EconomicAtomKindV1.WITHDRAWAL_LIABILITY,
        withdrawal.beneficiary,
        withdrawal.asset,
        "tau",
        -withdrawal.amount_atoms,
    )
    scratch.record(
        ValueDeltaClassV1.LIABILITY,
        withdrawal.beneficiary,
        withdrawal.asset,
        "tau",
        -withdrawal.amount_atoms,
    )


def _apply_fallback_activate(scratch: _BusinessScratch) -> None:
    checkpoint = scratch.root_text("checkpoint_root")
    payload = _authority_payload(
        scratch,
        GlobalCommandKindV1.FALLBACK_ACTIVATE,
        MigrationAuthorityProofV1,
    )
    if not isinstance(payload, MigrationAuthorityProofV1):
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_AUTHORITY)
    if (
        payload.kind is not MigrationEvidenceKindV1.FALLBACK_LIVENESS
        or payload.checkpoint_root != checkpoint
        or payload.compatible_profile_root != ZERO_ROOT_V1
        or payload.source_authority_epoch != scratch.migration.authority_epoch
        or scratch.migration.phase is not MigrationPhaseV1.NORMAL
        or checkpoint != scratch.pre_state_root
    ):
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_AUTHORITY)
    scratch.migration = MigrationStateV1(
        phase=MigrationPhaseV1.FALLBACK,
        authority_epoch=scratch.migration.authority_epoch + 1,
        previous_authority_root=scratch.migration.checkpoint_root,
        checkpoint_root=checkpoint,
        quiescent=False,
    )


def _apply_tau_rejoin(scratch: _BusinessScratch) -> None:
    checkpoint = scratch.root_text("checkpoint_root")
    profile = scratch.root_text("compatible_profile_root")
    payload = _authority_payload(
        scratch,
        GlobalCommandKindV1.TAU_REJOIN,
        MigrationAuthorityProofV1,
    )
    if not isinstance(payload, MigrationAuthorityProofV1):
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_AUTHORITY)
    if (
        payload.kind is not MigrationEvidenceKindV1.TAU_REJOIN_CATCHUP
        or payload.checkpoint_root != checkpoint
        or payload.compatible_profile_root != profile
        or payload.source_authority_epoch != scratch.migration.authority_epoch
        or scratch.migration.phase is not MigrationPhaseV1.FALLBACK
        or checkpoint != scratch.pre_state_root
        or profile != scratch.tau_profile
    ):
        raise _BusinessFailure(BusinessRejectReasonV1.INVALID_AUTHORITY)
    scratch.migration = MigrationStateV1(
        phase=MigrationPhaseV1.NORMAL,
        authority_epoch=scratch.migration.authority_epoch + 1,
        previous_authority_root=scratch.migration.checkpoint_root,
        checkpoint_root=checkpoint,
        quiescent=False,
    )


_BUSINESS_HANDLERS: Mapping[GlobalCommandKindV1, Callable[[_BusinessScratch], None]] = MappingProxyType({
    GlobalCommandKindV1.SPOT_SWAP: _apply_spot_swap,
    GlobalCommandKindV1.LP_ADD: _apply_lp_add,
    GlobalCommandKindV1.LP_REMOVE: _apply_lp_remove,
    GlobalCommandKindV1.ZUSD_BORROW: _apply_zusd_borrow,
    GlobalCommandKindV1.ZUSD_REPAY: _apply_zusd_repay,
    GlobalCommandKindV1.ZUSD_REDEEM: _apply_zusd_redeem,
    GlobalCommandKindV1.ZUSD_LIQUIDATE: _apply_zusd_liquidate,
    GlobalCommandKindV1.STABILITY_POOL_DEPOSIT: _apply_stability_deposit,
    GlobalCommandKindV1.STABILITY_POOL_WITHDRAW: _apply_stability_withdraw,
    GlobalCommandKindV1.ZUSD_REDISTRIBUTE: _apply_zusd_redistribute,
    GlobalCommandKindV1.PERP_OPEN: _apply_perp_open,
    GlobalCommandKindV1.PERP_CLOSE: _apply_perp_close,
    GlobalCommandKindV1.PERP_FUNDING: _apply_perp_funding,
    GlobalCommandKindV1.PERP_LIQUIDATE: _apply_perp_liquidate,
    GlobalCommandKindV1.ORACLE_SUBMIT: _apply_oracle_submit,
    GlobalCommandKindV1.ORACLE_DISPUTE: _apply_oracle_dispute,
    GlobalCommandKindV1.PROTOCOL_BUY_AND_BURN: _apply_protocol_buy_and_burn,
    GlobalCommandKindV1.ZRPF_PROVER_REWARD: _apply_prover_reward,
    GlobalCommandKindV1.SELLER_AUCTION_COMMIT: _apply_seller_auction_commit,
    GlobalCommandKindV1.SELLER_AUCTION_REVEAL: _apply_seller_auction_reveal,
    GlobalCommandKindV1.SELLER_AUCTION_SETTLE: _apply_seller_auction_settle,
    GlobalCommandKindV1.SELLER_AUCTION_CANCEL: _apply_seller_auction_cancel,
    GlobalCommandKindV1.SELLER_AUCTION_EXPIRE: _apply_seller_auction_expire,
    GlobalCommandKindV1.PRIVATE_SWAP_COMMIT: _apply_private_swap_commit,
    GlobalCommandKindV1.PRIVATE_SWAP_REVEAL: _apply_private_swap_reveal,
    GlobalCommandKindV1.PRIVATE_SWAP_SETTLE: _apply_private_swap_settle,
    GlobalCommandKindV1.PRIVATE_SWAP_CANCEL: _apply_private_swap_cancel,
    GlobalCommandKindV1.PRIVATE_SWAP_EXPIRE: _apply_private_swap_expire,
    GlobalCommandKindV1.TAU_ESCROW_DEPOSIT: _apply_tau_escrow_deposit,
    GlobalCommandKindV1.TAU_WITHDRAWAL: _apply_tau_withdrawal,
    GlobalCommandKindV1.TAU_WITHDRAWAL_ACK: _apply_tau_withdrawal_ack,
    GlobalCommandKindV1.FALLBACK_ACTIVATE: _apply_fallback_activate,
    GlobalCommandKindV1.TAU_REJOIN: _apply_tau_rejoin,
})


def _atoms_tuple(values: Mapping[tuple[str, str, str, str], int]) -> tuple[EconomicAtomV1, ...]:
    atoms: list[EconomicAtomV1] = []
    for (kind_value, owner, asset, custody), amount in sorted(values.items()):
        if amount <= 0:
            continue
        atoms.append(
            EconomicAtomV1.from_ledger_allocation(
                kind=EconomicAtomKindV1(kind_value),
                owner=owner,
                asset=asset,
                ledger_allocation=custody,
                amount_atoms=amount,
            )
        )
    return tuple(atoms)


def _with_nonce(values: tuple[NonceAtomV1, ...], sender: str, nonce: int) -> tuple[NonceAtomV1, ...]:
    updated = {item.sender: item.last_nonce for item in values}
    updated[sender] = nonce
    return tuple(NonceAtomV1(key, updated[key]) for key in sorted(updated))


__all__ = ["expected_finality_mode_v1", "run_m6_transition_v1"]
