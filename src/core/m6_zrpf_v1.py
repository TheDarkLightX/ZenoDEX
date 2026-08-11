"""Fixed-topology ZRPF 1.0 reference path over the M6 transition.

ZRPF is represented here as candidate evidence.  It executes the same Python
reference transition as direct mode, binds every ordered command and nonce,
and verifies the 64x16 / 8x8 journal shape.  Structural checking is kept
separate from issuance of an opaque root handle: the latter requires a typed
receipt from an explicit external proof-verifier port.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Protocol

from .m6_safe_mount_transition_v1 import run_m6_transition_v1
from .m6_safe_mount_types_v1 import (
    _VERIFIED_ZRPF_TOKEN,
    _ZRPF_VERIFICATION_RECEIPT_TOKEN,
    ZRPF_COMMAND_COUNT_V1,
    ZRPF_COMMANDS_PER_LEAF_V1,
    ZRPF_LEAF_COUNT_V1,
    AcceptCandidateV1,
    AuthenticatedExecutionContextV1,
    GlobalCommandV1,
    M6ApplicationStateV1,
    M6PromotionSubjectV1,
    M6ZRPFVerificationReceiptV1,
    RejectNoCommitV1,
    VerifiedZRPFRootV1,
    ZRPFChunkStatementV1,
    ZRPFRootJournalV1,
    hash_v1,
    ordered_root_v1,
)


@dataclass(frozen=True, slots=True)
class DirectBatchCandidateV1:
    subject_root: str
    pre_head: str
    pre_state_root: str
    pre_state: M6ApplicationStateV1
    post_state: M6ApplicationStateV1
    commands: tuple[GlobalCommandV1, ...]
    contexts: tuple[AuthenticatedExecutionContextV1, ...]
    candidates: tuple[AcceptCandidateV1, ...]
    command_root: str
    nonce_root: str
    value_delta_root: str
    history_root: str
    nullifier_root: str
    outbox_root: str
    data_availability_root: str

    @property
    def post_state_root(self) -> str:
        return self.post_state.state_root

    @property
    def publication_root(self) -> str:
        return direct_batch_publication_root_v1(
            pre_head=self.pre_head,
            pre_state_root=self.pre_state_root,
            post_state_root=self.post_state_root,
            candidate_id=self.candidate_id,
            command_root=self.command_root,
            nonce_root=self.nonce_root,
            value_delta_root=self.value_delta_root,
            history_root=self.history_root,
            nullifier_root=self.nullifier_root,
            outbox_root=self.outbox_root,
            data_availability_root=self.data_availability_root,
        )

    @property
    def candidate_id(self) -> str:
        return hash_v1(
            "m6-direct-batch-candidate-v1",
            {
                "subject_root": self.subject_root,
                "pre_head": self.pre_head,
                "pre_state_root": self.pre_state_root,
                "post_state_root": self.post_state_root,
                "command_root": self.command_root,
                "nullifier_root": self.nullifier_root,
                "data_availability_root": self.data_availability_root,
            },
        )


def direct_candidate_data_availability_projection_v1(
    candidate: AcceptCandidateV1,
) -> dict[str, object]:
    """Return the bounded effect projection committed by direct/ZRPF DA.

    The full post-state is already committed by ``post_state_root``.  Retaining
    it once per command would make durable replay quadratic in batch length.
    This projection carries the command-local economic delta, history atom,
    publication atom, and newly-created external effects that the execution
    receipt must bind.
    """

    return {
        "candidate_id": candidate.candidate_id,
        "pre_state_root": candidate.pre_state_root,
        "post_state_root": candidate.post_state.state_root,
        "value_delta": candidate.value_delta,
        "history_atom": candidate.history_atom,
        "publication_atom": candidate.publication_atom,
        "outbox_atoms": candidate.outbox_atoms,
        "business_status": candidate.business_status,
        "business_reject_reason": candidate.business_reject_reason,
    }


def direct_batch_publication_root_v1(
    *,
    pre_head: str,
    pre_state_root: str,
    post_state_root: str,
    candidate_id: str,
    command_root: str,
    nonce_root: str,
    value_delta_root: str,
    history_root: str,
    nullifier_root: str,
    outbox_root: str,
    data_availability_root: str,
) -> str:
    """Hash the complete direct-batch publication projection."""

    return hash_v1(
        "m6-direct-batch-publication-v1",
        {
            "pre_head": pre_head,
            "pre_state_root": pre_state_root,
            "post_state_root": post_state_root,
            "candidate_id": candidate_id,
            "command_root": command_root,
            "nonce_root": nonce_root,
            "value_delta_root": value_delta_root,
            "history_root": history_root,
            "nullifier_root": nullifier_root,
            "outbox_root": outbox_root,
            "data_availability_root": data_availability_root,
        },
    )


@dataclass(frozen=True, slots=True)
class ZRPFBatchCandidateV1:
    direct: DirectBatchCandidateV1
    chunks: tuple[ZRPFChunkStatementV1, ...]
    journal: ZRPFRootJournalV1

    @property
    def post_state(self) -> M6ApplicationStateV1:
        return self.direct.post_state

    @property
    def post_state_root(self) -> str:
        return self.direct.post_state_root

    @property
    def candidate_id(self) -> str:
        return self.direct.candidate_id


def execute_direct_batch_v1(
    subject: M6PromotionSubjectV1,
    state: M6ApplicationStateV1,
    contexts: tuple[AuthenticatedExecutionContextV1, ...],
    commands: tuple[GlobalCommandV1, ...],
) -> DirectBatchCandidateV1:
    """Execute a canonical batch sequentially through the authoritative core."""

    if not isinstance(contexts, tuple) or not isinstance(commands, tuple):
        raise TypeError("batch contexts and commands must be tuples")
    if not commands or len(commands) != len(contexts):
        raise ValueError("batch contexts and commands must have one non-empty aligned length")
    if len(commands) > ZRPF_COMMAND_COUNT_V1:
        raise ValueError("batch exceeds the ZRPF 1.0 command capacity")
    current = state
    candidates: list[AcceptCandidateV1] = []
    for context, command in zip(contexts, commands, strict=True):
        result = run_m6_transition_v1(subject, current, context, command)
        if isinstance(result, RejectNoCommitV1):
            raise ValueError(f"canonical batch contains an admission reject: {result.reason.value}")
        candidates.append(result)
        current = result.post_state
    command_hashes = tuple(command.command_hash for command in commands)
    nonce_identities = tuple(command.nonce_identity for command in commands)
    return DirectBatchCandidateV1(
        subject_root=subject.subject_root,
        pre_head=contexts[0].parent_head,
        pre_state_root=state.state_root,
        pre_state=state,
        post_state=current,
        commands=commands,
        contexts=contexts,
        candidates=tuple(candidates),
        command_root=ordered_root_v1("m6-direct-command-root-v1", command_hashes),
        nonce_root=ordered_root_v1("m6-direct-nonce-root-v1", nonce_identities),
        value_delta_root=ordered_root_v1(
            "m6-direct-value-delta-root-v1",
            tuple(candidate.value_delta.delta_root for candidate in candidates),
        ),
        history_root=current.history_root,
        nullifier_root=current.nullifier_root,
        outbox_root=current.outbox_root,
        data_availability_root=_data_availability_root_v1(
            commands,
            contexts,
            tuple(candidates),
        ),
    )


def _data_availability_root_v1(
    commands: tuple[GlobalCommandV1, ...],
    contexts: tuple[AuthenticatedExecutionContextV1, ...],
    candidates: tuple[AcceptCandidateV1, ...],
) -> str:
    """Commit the command preimages, authenticated contexts, and full effects."""

    if len(commands) != len(contexts) or len(commands) != len(candidates):
        raise ValueError("ZRPF data availability inputs are not aligned")
    entries = tuple(
        {
            "command": command,
            "context": context,
            "candidate": direct_candidate_data_availability_projection_v1(candidate),
        }
        for command, context, candidate in zip(commands, contexts, candidates, strict=True)
    )
    return ordered_root_v1("m6-zrpf-data-availability-v1", entries)


def execute_zrpf_batch_v1(
    subject: M6PromotionSubjectV1,
    state: M6ApplicationStateV1,
    contexts: tuple[AuthenticatedExecutionContextV1, ...],
    commands: tuple[GlobalCommandV1, ...],
) -> ZRPFBatchCandidateV1:
    """Build the fixed 64-leaf, 8-aggregate ZRPF candidate journal."""

    if len(commands) != ZRPF_COMMAND_COUNT_V1:
        raise ValueError("ZRPF 1.0 requires exactly 1,024 ordered commands")
    direct = execute_direct_batch_v1(subject, state, contexts, commands)
    chunks = tuple(
        _make_chunk_statement(subject, direct, ordinal)
        for ordinal in range(ZRPF_LEAF_COUNT_V1)
    )
    aggregate_roots = tuple(
        _aggregate_root(chunks[first : first + 8], ordinal)
        for ordinal, first in enumerate(range(0, ZRPF_LEAF_COUNT_V1, 8))
    )
    journal = ZRPFRootJournalV1(
        profile="zenodex/m6-zrpf/1.0",
        promotion_subject_root=subject.subject_root,
        writer_epoch=state.writer_epoch,
        pre_state_root=direct.pre_state_root,
        post_state_root=direct.post_state_root,
        command_count=len(commands),
        chunk_statement_roots=tuple(chunk.statement_root for chunk in chunks),
        aggregate_statement_roots=aggregate_roots,
        command_root=direct.command_root,
        nonce_root=direct.nonce_root,
        value_delta_root=direct.value_delta_root,
        history_root=direct.history_root,
        nullifier_root=direct.nullifier_root,
        outbox_root=direct.outbox_root,
        data_availability_root=direct.data_availability_root,
        verifier_image=subject.risc0_image,
    )
    return ZRPFBatchCandidateV1(direct=direct, chunks=chunks, journal=journal)


def _make_chunk_statement(
    subject: M6PromotionSubjectV1,
    batch: DirectBatchCandidateV1,
    ordinal: int,
) -> ZRPFChunkStatementV1:
    first = ordinal * ZRPF_COMMANDS_PER_LEAF_V1
    last = first + ZRPF_COMMANDS_PER_LEAF_V1
    commands = batch.commands[first:last]
    candidates = batch.candidates[first:last]
    if len(commands) != ZRPF_COMMANDS_PER_LEAF_V1:
        raise ValueError("chunk boundary does not contain sixteen commands")
    return ZRPFChunkStatementV1(
        profile="zenodex/m6-zrpf/1.0",
        promotion_subject_root=subject.subject_root,
        writer_epoch=batch.candidates[0].post_state.writer_epoch,
        ordinal=ordinal,
        pre_state_root=candidates[0].pre_state_root,
        post_state_root=candidates[-1].post_state.state_root,
        command_hashes=tuple(command.command_hash for command in commands),
        nonce_identities=tuple(command.nonce_identity for command in commands),
        value_delta_root=ordered_root_v1(
            "m6-zrpf-chunk-value-delta-root-v1",
            tuple(candidate.value_delta.delta_root for candidate in candidates),
        ),
        history_root=ordered_root_v1(
            "m6-zrpf-chunk-history-root-v1",
            tuple(candidate.history_atom.history_root for candidate in candidates),
        ),
        nullifier_root=candidates[-1].post_state.nullifier_root,
        outbox_root=ordered_root_v1(
            "m6-zrpf-chunk-outbox-root-v1",
            tuple(candidate.publication_atom.outbox_root for candidate in candidates),
        ),
        verifier_image=subject.risc0_image,
    )


def _aggregate_root(chunks: tuple[ZRPFChunkStatementV1, ...], ordinal: int) -> str:
    if len(chunks) != 8:
        raise ValueError("ZRPF aggregate must contain eight chunks")
    return hash_v1(
        "m6-zrpf-aggregate-statement-v1",
        {
            "ordinal": ordinal,
            "first_pre_state_root": chunks[0].pre_state_root,
            "last_post_state_root": chunks[-1].post_state_root,
            "chunk_statement_roots": tuple(chunk.statement_root for chunk in chunks),
        },
    )


def verify_zrpf_structure_v1(
    subject: M6PromotionSubjectV1,
    batch: ZRPFBatchCandidateV1,
) -> ZRPFBatchCandidateV1:
    """Verify the research structural journal without issuing authority."""

    journal = batch.journal
    if journal.profile != "zenodex/m6-zrpf/1.0":
        raise ValueError("ZRPF profile mismatch")
    if journal.promotion_subject_root != subject.subject_root:
        raise ValueError("ZRPF promotion subject mismatch")
    if journal.verifier_image != subject.risc0_image:
        raise ValueError("ZRPF verifier image mismatch")
    if journal.command_count != ZRPF_COMMAND_COUNT_V1:
        raise ValueError("ZRPF command count mismatch")
    if len(journal.chunk_statement_roots) != ZRPF_LEAF_COUNT_V1:
        raise ValueError("ZRPF chunk root count mismatch")
    if len(journal.aggregate_statement_roots) != ZRPF_LEAF_COUNT_V1 // 8:
        raise ValueError("ZRPF aggregate root count mismatch")
    direct = batch.direct
    if batch.direct.subject_root != subject.subject_root:
        raise ValueError("ZRPF direct candidate subject mismatch")
    if not direct.contexts or any(context.epoch != direct.contexts[0].epoch for context in direct.contexts):
        raise ValueError("ZRPF writer epoch mismatch")
    if journal.writer_epoch != direct.contexts[0].epoch:
        raise ValueError("ZRPF writer epoch mismatch")
    if journal.writer_epoch != direct.post_state.writer_epoch:
        raise ValueError("ZRPF writer epoch mismatch")
    if len(batch.chunks) != ZRPF_LEAF_COUNT_V1:
        raise ValueError("ZRPF chunk count mismatch")
    if len(batch.direct.commands) != ZRPF_COMMAND_COUNT_V1:
        raise ValueError("ZRPF command count mismatch")
    if len(direct.contexts) != ZRPF_COMMAND_COUNT_V1 or len(direct.candidates) != ZRPF_COMMAND_COUNT_V1:
        raise ValueError("ZRPF execution witness count mismatch")
    if direct.pre_state.state_root != direct.pre_state_root:
        raise ValueError("ZRPF pre-state root does not match execution state")
    if direct.pre_state.head != direct.pre_head:
        raise ValueError("ZRPF pre-head does not match execution state")
    if len({command.command_hash for command in batch.direct.commands}) != ZRPF_COMMAND_COUNT_V1:
        raise ValueError("ZRPF command replay or duplication detected")
    if len({command.nonce_identity for command in batch.direct.commands}) != ZRPF_COMMAND_COUNT_V1:
        raise ValueError("ZRPF nonce replay or duplication detected")
    previous_post_state_root = direct.pre_state_root
    previous_parent_head = direct.pre_head
    for context, command, candidate in zip(direct.contexts, direct.commands, direct.candidates, strict=True):
        if candidate.command != command:
            raise ValueError("ZRPF command/candidate binding mismatch")
        if context.sender != command.sender or context.nonce != command.nonce:
            raise ValueError("ZRPF context command binding mismatch")
        if context.parent_head != previous_parent_head:
            raise ValueError("ZRPF context parent binding mismatch")
        if candidate.pre_state_root != previous_post_state_root:
            raise ValueError("ZRPF direct state chaining mismatch")
        previous_post_state_root = candidate.post_state.state_root
        previous_parent_head = candidate.post_state.head
    expected_chunks = tuple(
        _make_chunk_statement(subject, direct, ordinal)
        for ordinal in range(ZRPF_LEAF_COUNT_V1)
    )
    if expected_chunks != batch.chunks:
        raise ValueError("ZRPF chunk statement does not match direct execution")
    for ordinal, chunk in enumerate(batch.chunks):
        if chunk.ordinal != ordinal:
            raise ValueError("ZRPF chunk order mismatch")
        if chunk.statement_root != journal.chunk_statement_roots[ordinal]:
            raise ValueError("ZRPF chunk statement root mismatch")
        if ordinal > 0 and chunk.pre_state_root != batch.chunks[ordinal - 1].post_state_root:
            raise ValueError("ZRPF chunk state chaining mismatch")
    expected_aggregates = tuple(
        _aggregate_root(batch.chunks[first : first + 8], ordinal)
        for ordinal, first in enumerate(range(0, ZRPF_LEAF_COUNT_V1, 8))
    )
    if expected_aggregates != journal.aggregate_statement_roots:
        raise ValueError("ZRPF aggregate root mismatch")
    if journal.pre_state_root != direct.pre_state_root or journal.post_state_root != direct.post_state_root:
        raise ValueError("ZRPF state endpoint mismatch")
    expected_roots = {
        "command_root": direct.command_root,
        "nonce_root": direct.nonce_root,
        "value_delta_root": direct.value_delta_root,
        "history_root": direct.history_root,
        "nullifier_root": direct.nullifier_root,
        "outbox_root": direct.outbox_root,
        "data_availability_root": direct.data_availability_root,
    }
    for field_name, expected in expected_roots.items():
        if getattr(journal, field_name) != expected:
            raise ValueError(f"ZRPF {field_name.replace('_', ' ')} mismatch")
    try:
        replayed_direct = execute_direct_batch_v1(
            subject,
            direct.pre_state,
            direct.contexts,
            direct.commands,
        )
    except (TypeError, ValueError) as exc:
        raise ValueError("ZRPF direct replay failed") from exc
    if replayed_direct != direct:
        raise ValueError("ZRPF direct replay does not match execution witness")
    return batch


class M6ZRPFReceiptVerifierV1(Protocol):
    """External verifier port for an actual RISC0/ZRPF receipt."""

    def verify_zrpf_receipt(
        self,
        subject: M6PromotionSubjectV1,
        batch: ZRPFBatchCandidateV1,
        journal: ZRPFRootJournalV1,
    ) -> M6ZRPFVerificationReceiptV1: ...


def _issue_m6_zrpf_verification_receipt_v1(
    *,
    promotion_subject_root: str,
    profile: str,
    verifier_image: str,
    journal_root: str,
    data_availability_root: str,
    attestation_root: str,
) -> M6ZRPFVerificationReceiptV1:
    """Create an adapter receipt after an external proof check.

    This helper only packages a verifier result.  It performs no RISC0 proof
    verification and is suitable for explicitly labelled research fixtures.
    """

    return M6ZRPFVerificationReceiptV1(
        _ZRPF_VERIFICATION_RECEIPT_TOKEN,
        promotion_subject_root=promotion_subject_root,
        profile=profile,
        verifier_image=verifier_image,
        journal_root=journal_root,
        data_availability_root=data_availability_root,
        attestation_root=attestation_root,
    )


def verify_zrpf_root_v1(
    subject: M6PromotionSubjectV1,
    batch: ZRPFBatchCandidateV1,
    *,
    receipt_verifier: M6ZRPFReceiptVerifierV1 | None = None,
) -> VerifiedZRPFRootV1:
    """Issue a verified root only after an explicit proof receipt is returned."""

    checked = verify_zrpf_structure_v1(subject, batch)
    if receipt_verifier is None:
        raise ValueError("ZRPF proof receipt verifier is unavailable")
    try:
        receipt = receipt_verifier.verify_zrpf_receipt(subject, checked, checked.journal)
    except (TypeError, ValueError) as exc:
        raise ValueError(f"ZRPF proof receipt rejected: {exc}") from exc
    if not isinstance(receipt, M6ZRPFVerificationReceiptV1):
        raise TypeError("ZRPF receipt verifier did not return a typed receipt")
    return VerifiedZRPFRootV1(
        _VERIFIED_ZRPF_TOKEN,
        checked.journal,
        checked.candidate_id,
        checked.post_state,
        checked,
        receipt,
    )


def degrade_to_direct_v1(
    subject: M6PromotionSubjectV1,
    state: M6ApplicationStateV1,
    contexts: tuple[AuthenticatedExecutionContextV1, ...],
    commands: tuple[GlobalCommandV1, ...],
    *,
    proof_capacity_available: bool,
) -> DirectBatchCandidateV1:
    """Return the direct candidate when ZRPF capacity is unavailable."""

    if type(proof_capacity_available) is not bool:
        raise TypeError("proof capacity flag must be bool")
    if proof_capacity_available:
        raise ValueError("direct degradation requires unavailable proof capacity")
    # The branch is a performance choice. It never changes the command order
    # or transition semantics and therefore cannot create a second authority.
    return execute_direct_batch_v1(subject, state, contexts, commands)


__all__ = [
    "DirectBatchCandidateV1",
    "direct_candidate_data_availability_projection_v1",
    "direct_batch_publication_root_v1",
    "ZRPFBatchCandidateV1",
    "execute_direct_batch_v1",
    "execute_zrpf_batch_v1",
    "verify_zrpf_structure_v1",
    "verify_zrpf_root_v1",
    "M6ZRPFReceiptVerifierV1",
    "degrade_to_direct_v1",
]
