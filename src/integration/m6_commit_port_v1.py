"""Single in-memory M6 commit port used by the reference and test shell.

The port models compare-and-swap and finality authority without pretending to
be the durable ZenoLedger implementation.  State, replay identity, finality,
and the already-derived outbox remain one publication unit under one lock.
SQLite and legacy adapters are intentionally not imported here.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from enum import Enum
from threading import Lock
from typing import Protocol, cast

from ..core.m6_safe_mount_transition_v1 import (
    expected_finality_mode_v1,
    run_m6_transition_v1,
)
from ..core.m6_safe_mount_types_v1 import (
    ZERO_ROOT_V1,
    AcceptCandidateV1,
    AuthenticatedExecutionContextV1,
    BusinessRejectReasonV1,
    BusinessStatusV1,
    FinalityModeV1,
    GlobalCommandV1,
    M6ApplicationStateV1,
    M6FinalityVerificationReceiptRecordV1,
    M6FinalityVerificationReceiptV1,
    M6PromotionSubjectV1,
    M6ZRPFVerificationReceiptRecordV1,
    M6ZRPFVerificationReceiptV1,
    MigrationPhaseV1,
    OutboxAtomV1,
    RejectNoCommitV1,
    TauBatchCertificateV1,
    VerifiedZenoLedgerFinalityV1,
    VerifiedZRPFRootV1,
    ZenoLedgerFinalityCertificateV1,
    ZRPFRootJournalV1,
    canonical_bytes_v1,
    decode_global_command_v1,
    hash_v1,
    ordered_root_v1,
    validate_authenticated_execution_context_body_v1,
    validate_economic_state_v1,
    verify_finality_certificate_v1,
    verify_zeno_ledger_finality_v1,
)
from ..core.m6_zrpf_v1 import (
    DirectBatchCandidateV1,
    ZRPFBatchCandidateV1,
    direct_batch_publication_root_v1,
    direct_candidate_data_availability_projection_v1,
    execute_direct_batch_v1,
    verify_zrpf_structure_v1,
)
from ..state.canonical import canonical_hex_fixed_allow_0x


class CommitStatusV1(str, Enum):
    COMMITTED = "committed"
    ALREADY_COMMITTED = "already_committed"
    STALE_HEAD = "stale_head"
    FINALITY_REJECTED = "finality_rejected"


class M6FinalityVerifierV1(Protocol):
    """External finality-verifier capability required before publication.

    The commit port never treats a caller-supplied ``Verified`` value as
    sufficient authority.  A configured adapter must independently verify the
    certificate and return a receipt bound to the exact proposal supplied
    below.  The reference repository does not implement that cryptographic
    adapter, so a port without one rejects every publication.
    """

    def verify_finality(
        self,
        subject: M6PromotionSubjectV1,
        *,
        candidate_parent_head: str,
        candidate_head: str,
        publication_root: str,
        expected_writer_epoch: int,
        expected_command_root: str,
        expected_nonce_root: str,
        expected_execution_receipt_root: str | None,
        certificate: ZenoLedgerFinalityCertificateV1,
        tau_certificate: TauBatchCertificateV1 | None,
    ) -> M6FinalityVerificationReceiptV1: ...


def _reject_duplicate_replay_keys(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate direct replay key: {key}")
        result[key] = value
    return result


def _decode_replay_body(value: str, *, name: str) -> tuple[bytes, dict[str, object]]:
    if not isinstance(value, str) or value == "" or value != value.lower():
        raise ValueError(f"{name} must be lowercase hexadecimal JSON")
    try:
        data = bytes.fromhex(value)
        raw = json.loads(
            data.decode("utf-8"),
            object_pairs_hook=_reject_duplicate_replay_keys,
            parse_constant=lambda constant: (_ for _ in ()).throw(
                ValueError(f"{name} contains a forbidden JSON constant: {constant}")
            ),
            parse_float=lambda _value: (_ for _ in ()).throw(
                ValueError(f"{name} contains a forbidden float")
            ),
        )
        if not isinstance(raw, dict) or canonical_bytes_v1(raw) != data:
            raise ValueError(f"{name} is not canonical JSON bytes")
    except (RecursionError, ValueError, TypeError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ValueError(f"{name} is not canonical JSON bytes") from exc
    return data, raw


def direct_batch_data_availability_root_v1(
    replays: tuple[DirectExecutionReplayV1, ...],
) -> str:
    """Recompute the aggregate DA root from retained replay bodies."""

    entries = []
    for replay in replays:
        if replay.candidate_body_hex is None:
            raise ValueError("direct batch replay is missing its candidate projection body")
        entries.append(
            {
                "command": _decode_replay_body(
                    replay.command_body_hex,
                    name="direct command body",
                )[1],
                "context": _decode_replay_body(
                    replay.context_body_hex,
                    name="direct context body",
                )[1],
                "candidate": _decode_replay_body(
                    replay.candidate_body_hex,
                    name="direct candidate projection body",
                )[1],
            }
        )
    return ordered_root_v1("m6-zrpf-data-availability-v1", tuple(entries))


def _require_record_root(value: object, *, name: str, allow_zero: bool = False) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a root string")
    canonical = canonical_hex_fixed_allow_0x(value, nbytes=32, name=name)
    if value != canonical or (not allow_zero and canonical == ZERO_ROOT_V1):
        raise ValueError(f"{name} is not an allowed canonical root")
    return canonical


@dataclass(frozen=True, slots=True)
class DirectExecutionReplayV1:
    """Canonical direct replay bodies retained for durable replay.

    A single-command record already retains the complete typed post-state,
    history, delta roots, publication roots, and outbox suffix.  It therefore
    omits the redundant candidate projection.  Multi-command records retain
    that projection because the aggregate DA root commits each command-local
    effect in order.
    """

    command_body_hex: str
    context_body_hex: str
    candidate_body_hex: str | None
    data_availability_root: str

    def __post_init__(self) -> None:
        command_data, command_raw = _decode_replay_body(self.command_body_hex, name="direct command body")
        _, context_raw = _decode_replay_body(self.context_body_hex, name="direct context body")
        try:
            command = decode_global_command_v1(command_data)
        except (TypeError, ValueError) as exc:
            raise ValueError("direct command body is not a valid GlobalCommandV1") from exc
        if command.to_canonical() != command_raw:
            raise ValueError("direct command body canonical projection mismatch")
        validate_authenticated_execution_context_body_v1(context_raw)
        if self.candidate_body_hex is not None:
            _, candidate_raw = _decode_replay_body(
                self.candidate_body_hex,
                name="direct candidate projection body",
            )
            if set(candidate_raw) != {
                "candidate_id",
                "pre_state_root",
                "post_state_root",
                "value_delta",
                "history_atom",
                "publication_atom",
                "outbox_atoms",
                "business_status",
                "business_reject_reason",
            }:
                raise ValueError("direct candidate projection body keys mismatch")
            value_delta = candidate_raw["value_delta"]
            history_atom = candidate_raw["history_atom"]
            publication_atom = candidate_raw["publication_atom"]
            if not isinstance(value_delta, dict) or not isinstance(history_atom, dict):
                raise ValueError("direct candidate projection effect body is not an object")
            if not isinstance(publication_atom, dict):
                raise ValueError("direct candidate projection publication atom is not an object")
            if value_delta.get("command_hash") != command.command_hash:
                raise ValueError("direct candidate projection delta is not bound to command")
            if history_atom.get("command_hash") != command.command_hash:
                raise ValueError("direct candidate projection history is not bound to command")
            if history_atom.get("sender") != command.sender or history_atom.get("nonce") != command.nonce:
                raise ValueError("direct candidate projection history is not bound to command identity")
            if publication_atom.get("candidate_id") != candidate_raw["candidate_id"]:
                raise ValueError("direct candidate projection candidate id is not bound")
            if publication_atom.get("execution_context_root") != hash_v1(
                "m6-authenticated-execution-context-v1",
                context_raw,
            ):
                raise ValueError("direct candidate projection and context root are not bound")
            for field_name, field in (
                ("value delta", value_delta),
                ("history atom", history_atom),
                ("publication atom", publication_atom),
            ):
                if field.get("post_state_root") != candidate_raw["post_state_root"]:
                    raise ValueError(f"direct candidate projection {field_name} post-state is not bound")
        expected_data_availability_root = hash_v1(
            "m6-direct-data-availability-v1",
            {
                "command_body_hex": self.command_body_hex,
                "context_body_hex": self.context_body_hex,
                "candidate_body_hex": self.candidate_body_hex,
            },
        )
        if self.data_availability_root != expected_data_availability_root:
            raise ValueError("direct data-availability root mismatch")

    @classmethod
    def from_execution(
        cls,
        command: GlobalCommandV1,
        context: AuthenticatedExecutionContextV1,
        candidate: AcceptCandidateV1,
        *,
        retain_candidate_projection: bool = False,
    ) -> DirectExecutionReplayV1:
        command_body_hex = canonical_bytes_v1(command).hex()
        context_body_hex = canonical_bytes_v1(context).hex()
        candidate_body_hex = (
            canonical_bytes_v1(
                direct_candidate_data_availability_projection_v1(candidate),
            ).hex()
            if retain_candidate_projection
            else None
        )
        return cls(
            command_body_hex=command_body_hex,
            context_body_hex=context_body_hex,
            candidate_body_hex=candidate_body_hex,
            data_availability_root=hash_v1(
                "m6-direct-data-availability-v1",
                {
                    "command_body_hex": command_body_hex,
                    "context_body_hex": context_body_hex,
                    "candidate_body_hex": candidate_body_hex,
                },
            ),
        )

    @property
    def command_hash(self) -> str:
        command_data, _ = _decode_replay_body(self.command_body_hex, name="direct command body")
        return decode_global_command_v1(command_data).command_hash

    @property
    def nonce_identity(self) -> str:
        command_data, _ = _decode_replay_body(self.command_body_hex, name="direct command body")
        return decode_global_command_v1(command_data).nonce_identity

    @property
    def context_root(self) -> str:
        _, raw = _decode_replay_body(self.context_body_hex, name="direct context body")
        return hash_v1("m6-authenticated-execution-context-v1", raw)

    @property
    def context_parent_head(self) -> str:
        _, raw = _decode_replay_body(self.context_body_hex, name="direct context body")
        return cast(str, raw["parent_head"])

    @property
    def context_sender(self) -> str:
        _, raw = _decode_replay_body(self.context_body_hex, name="direct context body")
        return cast(str, raw["sender"])

    @property
    def context_nonce(self) -> int:
        _, raw = _decode_replay_body(self.context_body_hex, name="direct context body")
        return cast(int, raw["nonce"])

    @property
    def context_deployment(self) -> str:
        _, raw = _decode_replay_body(self.context_body_hex, name="direct context body")
        return cast(str, raw["deployment"])

    @property
    def context_chain_id(self) -> str:
        _, raw = _decode_replay_body(self.context_body_hex, name="direct context body")
        return cast(str, raw["chain_id"])

    def to_canonical(self) -> dict[str, str | None]:
        return {
            "command_body_hex": self.command_body_hex,
            "context_body_hex": self.context_body_hex,
            "candidate_body_hex": self.candidate_body_hex,
            "data_availability_root": self.data_availability_root,
        }


@dataclass(frozen=True, slots=True)
class M6PublishedRecordV1:
    """One atomic publication receipt retained by the reference commit shell."""

    candidate_id: str
    parent_head: str
    pre_state_root: str
    post_state_root: str
    publication_root: str
    command_root: str
    value_delta_root: str
    history_root: str
    nullifier_root: str
    outbox_root: str
    outbox_atoms: tuple[OutboxAtomV1, ...]
    finality: ZenoLedgerFinalityCertificateV1
    finality_receipt: M6FinalityVerificationReceiptRecordV1 | None = None
    tau_certificate: TauBatchCertificateV1 | None = None
    business_status: BusinessStatusV1 | None = None
    business_reject_reason: BusinessRejectReasonV1 | None = None
    zrpf_journal: ZRPFRootJournalV1 | None = None
    zrpf_receipt: M6ZRPFVerificationReceiptRecordV1 | None = None
    direct_replay: DirectExecutionReplayV1 | None = None
    direct_batch_replay: tuple[DirectExecutionReplayV1, ...] | None = None
    direct_batch_data_availability_root: str | None = None

    def __post_init__(self) -> None:
        _require_record_root(self.candidate_id, name="published candidate id")
        _require_record_root(self.parent_head, name="published parent head", allow_zero=True)
        for name, value in (
            ("published pre-state root", self.pre_state_root),
            ("published post-state root", self.post_state_root),
            ("published publication root", self.publication_root),
            ("published command root", self.command_root),
            ("published value-delta root", self.value_delta_root),
            ("published history root", self.history_root),
            ("published nullifier root", self.nullifier_root),
            ("published outbox root", self.outbox_root),
        ):
            _require_record_root(value, name=name)
        if not isinstance(self.outbox_atoms, tuple) or any(
            not isinstance(atom, OutboxAtomV1) for atom in self.outbox_atoms
        ):
            raise TypeError("published outbox atoms are not a typed tuple")
        if not isinstance(self.finality, ZenoLedgerFinalityCertificateV1):
            raise TypeError("published finality is not typed")
        if self.finality_receipt is not None and not isinstance(
            self.finality_receipt,
            M6FinalityVerificationReceiptRecordV1,
        ):
            raise TypeError("published finality receipt is not typed")
        if self.finality.candidate_head != self.post_state_root:
            raise ValueError("published finality and post-state root are not bound")
        if self.finality.publication_root != self.publication_root:
            raise ValueError("published finality and publication root are not bound")
        if self.finality_receipt is not None:
            if (
                self.finality_receipt.candidate_parent_head != self.parent_head
                or self.finality_receipt.candidate_head != self.post_state_root
                or self.finality_receipt.publication_root != self.publication_root
                or self.finality_receipt.writer_epoch != self.finality.writer_epoch
                or self.finality_receipt.certificate_root != self.finality.certificate_root
            ):
                raise ValueError("published finality and verification receipt are not bound")
        if self.business_status is not None and not isinstance(self.business_status, BusinessStatusV1):
            raise TypeError("published business status is not closed")
        if self.business_reject_reason is not None and not isinstance(
            self.business_reject_reason,
            BusinessRejectReasonV1,
        ):
            raise TypeError("published business reject reason is not closed")
        if self.business_status is BusinessStatusV1.ACCEPTED and self.business_reject_reason is not None:
            raise ValueError("accepted publication record cannot have a business reject reason")
        if self.business_status is BusinessStatusV1.REJECTED_COMMITTED and self.business_reject_reason is None:
            raise ValueError("committed rejection record requires a business reject reason")
        if self.business_status is None and self.business_reject_reason is not None:
            raise ValueError("published reject reason requires a business status")
        if self.zrpf_journal is not None and not isinstance(self.zrpf_journal, ZRPFRootJournalV1):
            raise TypeError("published ZRPF journal is not typed")
        if self.zrpf_receipt is not None and not isinstance(
            self.zrpf_receipt,
            M6ZRPFVerificationReceiptRecordV1,
        ):
            raise TypeError("published ZRPF receipt is not typed")
        if (self.zrpf_journal is None) != (self.zrpf_receipt is None):
            raise ValueError("published ZRPF journal and receipt must be paired")
        expected_execution_receipt_root = (
            None if self.zrpf_receipt is None else self.zrpf_receipt.receipt_root
        )
        if self.finality.execution_receipt_root != expected_execution_receipt_root:
            raise ValueError("published finality and ZRPF receipt are not bound")
        if self.zrpf_journal is not None and self.zrpf_receipt is not None:
            for name, expected_value, actual_value in (
                ("publication", self.publication_root, self.zrpf_journal.journal_root),
                ("pre-state", self.pre_state_root, self.zrpf_journal.pre_state_root),
                ("post-state", self.post_state_root, self.zrpf_journal.post_state_root),
                ("command", self.command_root, self.zrpf_journal.command_root),
                ("value delta", self.value_delta_root, self.zrpf_journal.value_delta_root),
                ("history", self.history_root, self.zrpf_journal.history_root),
                ("nullifier", self.nullifier_root, self.zrpf_journal.nullifier_root),
                ("outbox", self.outbox_root, self.zrpf_journal.outbox_root),
                ("writer epoch", self.finality.writer_epoch, self.zrpf_journal.writer_epoch),
            ):
                if expected_value != actual_value:
                    raise ValueError(f"published ZRPF journal {name} binding mismatch")
            for name, journal_value, receipt_value in (
                ("subject", self.zrpf_journal.promotion_subject_root, self.zrpf_receipt.promotion_subject_root),
                ("profile", self.zrpf_journal.profile, self.zrpf_receipt.profile),
                ("verifier image", self.zrpf_journal.verifier_image, self.zrpf_receipt.verifier_image),
                ("journal", self.zrpf_journal.journal_root, self.zrpf_receipt.journal_root),
                ("data availability", self.zrpf_journal.data_availability_root, self.zrpf_receipt.data_availability_root),
            ):
                if journal_value != receipt_value:
                    raise ValueError(f"published ZRPF journal and receipt {name} mismatch")
        if self.direct_replay is not None and not isinstance(self.direct_replay, DirectExecutionReplayV1):
            raise TypeError("published direct replay is not typed")
        if self.direct_replay is not None and self.direct_replay.candidate_body_hex is not None:
            raise ValueError("single-command direct replay cannot carry a candidate projection body")
        if self.direct_batch_replay is not None:
            if not isinstance(self.direct_batch_replay, tuple) or not self.direct_batch_replay:
                raise ValueError("published direct batch replay must be a non-empty tuple")
            if any(not isinstance(item, DirectExecutionReplayV1) for item in self.direct_batch_replay):
                raise TypeError("published direct batch replay is not a typed tuple")
            if any(item.candidate_body_hex is None for item in self.direct_batch_replay):
                raise ValueError("published direct batch replay requires candidate projection bodies")
        if self.zrpf_journal is not None and (
            self.direct_replay is not None or self.direct_batch_replay is not None
        ):
            raise ValueError("published record cannot carry both ZRPF and direct replay bodies")
        if self.direct_replay is not None and self.direct_batch_replay is not None:
            raise ValueError("published record cannot carry both direct replay shapes")
        if self.tau_certificate is not None:
            if self.tau_certificate.candidate_parent_head != self.parent_head:
                raise ValueError("published Tau certificate and parent head are not bound")
            expected_command_root = ordered_root_v1(
                "m6-direct-command-root-v1",
                self.tau_certificate.ordered_command_hashes,
            )
            if self.command_root != expected_command_root:
                raise ValueError("published Tau certificate and command root are not bound")
        if self.direct_replay is not None:
            if self.direct_replay.context_parent_head != self.parent_head:
                raise ValueError("published direct replay and parent head are not bound")
            expected_command_root = ordered_root_v1(
                "m6-direct-command-root-v1",
                (self.direct_replay.command_hash,),
            )
            if self.command_root != expected_command_root:
                raise ValueError("published direct replay and command root are not bound")
            if self.tau_certificate is not None:
                if self.tau_certificate.ordered_command_hashes != (self.direct_replay.command_hash,):
                    raise ValueError("published direct replay and Tau command ordering are not bound")
                if self.tau_certificate.ordered_nonce_identities != (self.direct_replay.nonce_identity,):
                    raise ValueError("published direct replay and Tau nonce ordering are not bound")
        if self.direct_batch_replay is not None:
            if len(self.direct_batch_replay) < 2:
                raise ValueError("published direct batch replay requires at least two commands")
            if self.direct_batch_data_availability_root is None:
                raise ValueError("published direct batch data-availability root is missing")
            if self.direct_batch_replay[0].context_parent_head != self.parent_head:
                raise ValueError("published direct batch replay and parent head are not bound")
            expected_command_root = ordered_root_v1(
                "m6-direct-command-root-v1",
                tuple(item.command_hash for item in self.direct_batch_replay),
            )
            expected_nonce_root = ordered_root_v1(
                "m6-direct-nonce-root-v1",
                tuple(item.nonce_identity for item in self.direct_batch_replay),
            )
            if self.command_root != expected_command_root:
                raise ValueError("published direct batch replay and command root are not bound")
            if self.tau_certificate is not None:
                if self.tau_certificate.ordered_command_hashes != tuple(
                    item.command_hash for item in self.direct_batch_replay
                ):
                    raise ValueError("published direct batch replay and Tau command ordering are not bound")
                if self.tau_certificate.ordered_nonce_identities != tuple(
                    item.nonce_identity for item in self.direct_batch_replay
                ):
                    raise ValueError("published direct batch replay and Tau nonce ordering are not bound")
            if self.direct_batch_data_availability_root != direct_batch_data_availability_root_v1(
                self.direct_batch_replay,
            ):
                raise ValueError("published direct batch replay data-availability root is not bound")
            if self.publication_root != direct_batch_publication_root_v1(
                pre_head=self.parent_head,
                pre_state_root=self.pre_state_root,
                post_state_root=self.post_state_root,
                candidate_id=self.candidate_id,
                command_root=self.command_root,
                nonce_root=expected_nonce_root,
                value_delta_root=self.value_delta_root,
                history_root=self.history_root,
                nullifier_root=self.nullifier_root,
                outbox_root=self.outbox_root,
                data_availability_root=self.direct_batch_data_availability_root,
            ):
                raise ValueError("published direct batch replay publication root is not bound")
        elif self.direct_batch_data_availability_root is not None:
            raise ValueError("direct batch data-availability root requires a direct batch replay")

    @property
    def receipt_root(self) -> str:
        return hash_v1("m6-published-record-v1", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            "candidate_id": self.candidate_id,
            "parent_head": self.parent_head,
            "pre_state_root": self.pre_state_root,
            "post_state_root": self.post_state_root,
            "publication_root": self.publication_root,
            "command_root": self.command_root,
            "value_delta_root": self.value_delta_root,
            "history_root": self.history_root,
            "nullifier_root": self.nullifier_root,
            "outbox_root": self.outbox_root,
            "outbox_atoms": self.outbox_atoms,
            "finality": self.finality,
            "finality_receipt": self.finality_receipt,
            "tau_certificate": self.tau_certificate,
            "business_status": self.business_status,
            "business_reject_reason": self.business_reject_reason,
            "zrpf_journal": self.zrpf_journal,
            "zrpf_receipt": self.zrpf_receipt,
            "direct_replay": self.direct_replay,
            "direct_batch_replay": self.direct_batch_replay,
            "direct_batch_data_availability_root": self.direct_batch_data_availability_root,
        }


def candidate_matches_published_record_v1(
    candidate: AcceptCandidateV1,
    record: M6PublishedRecordV1,
) -> bool:
    """Check the direct candidate projection used for durable replay."""

    try:
        validate_economic_state_v1(candidate.post_state)
    except ValueError:
        return False
    return (
        candidate.candidate_id == record.candidate_id
        and candidate.pre_state_root == record.pre_state_root
        and ordered_root_v1("m6-direct-command-root-v1", (candidate.command.command_hash,))
        == record.command_root
        and ordered_root_v1("m6-direct-nonce-root-v1", (candidate.command.nonce_identity,))
        == _record_nonce_root(record)
        and candidate.post_state.state_root == record.post_state_root
        and candidate.publication_atom.publication_root == record.publication_root
        and candidate.value_delta.delta_root == record.value_delta_root
        and candidate.post_state.history_root == record.history_root
        and candidate.post_state.nullifier_root == record.nullifier_root
        and candidate.post_state.outbox_root == record.outbox_root
        and candidate.outbox_atoms == record.outbox_atoms
        and record.direct_replay
        == DirectExecutionReplayV1.from_execution(candidate.command, candidate.context, candidate)
        and candidate.business_status is record.business_status
        and candidate.business_reject_reason is record.business_reject_reason
    )


def direct_batch_matches_published_record_v1(
    candidate: DirectBatchCandidateV1,
    record: M6PublishedRecordV1,
) -> bool:
    """Check the complete direct-batch projection used for durable replay."""

    try:
        validate_economic_state_v1(candidate.post_state)
        replays = tuple(
            DirectExecutionReplayV1.from_execution(
                command,
                context,
                candidate_item,
                retain_candidate_projection=True,
            )
            for command, context, candidate_item in zip(
                candidate.commands,
                candidate.contexts,
                candidate.candidates,
                strict=True,
            )
        )
    except (TypeError, ValueError):
        return False
    return (
        candidate.candidate_id == record.candidate_id
        and candidate.pre_state_root == record.pre_state_root
        and candidate.post_state_root == record.post_state_root
        and candidate.publication_root == record.publication_root
        and candidate.command_root == record.command_root
        and candidate.nonce_root == _record_nonce_root(record)
        and candidate.value_delta_root == record.value_delta_root
        and candidate.history_root == record.history_root
        and candidate.nullifier_root == record.nullifier_root
        and candidate.outbox_root == record.outbox_root
        and candidate.data_availability_root == record.direct_batch_data_availability_root
        and candidate.post_state.outbox[len(candidate.pre_state.outbox) :] == record.outbox_atoms
        and record.direct_batch_replay == replays
        and record.direct_replay is None
        and record.zrpf_journal is None
        and record.zrpf_receipt is None
    )


@dataclass(frozen=True, slots=True)
class _CommitProposalV1:
    candidate_id: str
    pre_state_root: str
    post_state: M6ApplicationStateV1
    publication_root: str
    command_root: str
    nonce_root: str
    value_delta_root: str
    history_root: str
    nullifier_root: str
    outbox_root: str
    outbox_atoms: tuple[OutboxAtomV1, ...]
    business_status: BusinessStatusV1 | None
    business_reject_reason: BusinessRejectReasonV1 | None
    zrpf_journal: ZRPFRootJournalV1 | None
    zrpf_receipt: M6ZRPFVerificationReceiptRecordV1 | None
    direct_replay: DirectExecutionReplayV1 | None
    direct_batch_replay: tuple[DirectExecutionReplayV1, ...] | None = None
    direct_batch_data_availability_root: str | None = None


@dataclass(frozen=True, slots=True)
class CommitResultV1:
    status: CommitStatusV1
    state: M6ApplicationStateV1
    candidate_id: str
    reason: str | None = None
    record: M6PublishedRecordV1 | None = None


class M6CommitPortV1:
    """Reference unique commit capability.

    This shell supplies a deterministic CAS and lock.  Filesystem durability,
    validator networking, crash-point recovery, and the 5-of-7 signature
    cryptography remain explicit external obligations.
    """

    def __init__(
        self,
        subject: M6PromotionSubjectV1,
        initial_state: M6ApplicationStateV1,
        finality_verifier: M6FinalityVerifierV1 | None = None,
    ) -> None:
        if initial_state.deployment != subject.deployment:
            raise ValueError("initial state deployment does not match subject")
        if initial_state.writer_epoch < subject.writer_epoch:
            raise ValueError("initial state writer epoch predates subject")
        validate_economic_state_v1(initial_state)
        self._subject = subject
        self._state = initial_state
        self._finality_verifier = finality_verifier
        self._committed_ids: dict[str, str] = {}
        self._records: dict[str, M6PublishedRecordV1] = {}
        self._lock = Lock()

    @property
    def state(self) -> M6ApplicationStateV1:
        with self._lock:
            return self._state

    @property
    def subject(self) -> M6PromotionSubjectV1:
        return self._subject

    def publish(
        self,
        candidate: AcceptCandidateV1,
        finality: VerifiedZenoLedgerFinalityV1,
        tau_certificate: TauBatchCertificateV1 | None,
    ) -> CommitResultV1:
        """Publish one direct candidate after finality and expected-head checks."""
        with self._lock:
            finality_reason = _finality_evidence_reason(self._subject, finality, tau_certificate)
            if finality_reason is not None:
                return CommitResultV1(
                    status=CommitStatusV1.FINALITY_REJECTED,
                    state=self._state,
                    candidate_id=candidate.candidate_id,
                    reason=finality_reason,
                )
            # A committed replay is decided by its stable identity before the
            # current head changes.  The first publication still derives and
            # checks the receipt projection against the locked parent state.
            if candidate.candidate_id in self._committed_ids:
                proposal = _direct_proposal(candidate, candidate.outbox_atoms)
                return self._publish_locked(proposal, finality)
            if self._state.state_root != candidate.pre_state_root:
                return CommitResultV1(
                    status=CommitStatusV1.STALE_HEAD,
                    state=self._state,
                    candidate_id=candidate.candidate_id,
                    reason="expected pre-state root differs from current state",
                )
            try:
                replayed = run_m6_transition_v1(
                    self._subject,
                    self._state,
                    candidate.context,
                    candidate.command,
                )
            except (TypeError, ValueError) as exc:
                return CommitResultV1(
                    status=CommitStatusV1.FINALITY_REJECTED,
                    state=self._state,
                    candidate_id=candidate.candidate_id,
                    reason=f"direct candidate replay rejected: {exc}",
                )
            if isinstance(replayed, RejectNoCommitV1):
                return CommitResultV1(
                    status=CommitStatusV1.FINALITY_REJECTED,
                    state=self._state,
                    candidate_id=candidate.candidate_id,
                    reason=f"direct candidate replay rejected: {replayed.reason.value}",
                )
            if replayed != candidate:
                return CommitResultV1(
                    status=CommitStatusV1.FINALITY_REJECTED,
                    state=self._state,
                    candidate_id=candidate.candidate_id,
                    reason="direct candidate replay does not match execution witness",
                )
            try:
                outbox_atoms = _new_outbox_atoms(self._state, candidate.post_state)
            except ValueError as exc:
                return CommitResultV1(
                    status=CommitStatusV1.FINALITY_REJECTED,
                    state=self._state,
                    candidate_id=candidate.candidate_id,
                    reason=str(exc),
                )
            if candidate.outbox_atoms != outbox_atoms:
                return CommitResultV1(
                    status=CommitStatusV1.FINALITY_REJECTED,
                    state=self._state,
                    candidate_id=candidate.candidate_id,
                    reason="candidate outbox projection does not match post-state suffix",
                )
            reason = _candidate_binding_reason(self._state, candidate)
            if reason is not None:
                return CommitResultV1(
                    status=CommitStatusV1.FINALITY_REJECTED,
                    state=self._state,
                    candidate_id=candidate.candidate_id,
                    reason=reason,
                )
            proposal = _direct_proposal(candidate, outbox_atoms)
            return self._publish_locked(proposal, finality)

    def publish_zrpf(
        self,
        verified_root: VerifiedZRPFRootV1,
        finality: VerifiedZenoLedgerFinalityV1,
        tau_certificate: TauBatchCertificateV1 | None,
    ) -> CommitResultV1:
        """Publish verified ZRPF evidence through the same commit capability."""
        with self._lock:
            finality_reason = _finality_evidence_reason(self._subject, finality, tau_certificate)
            if finality_reason is not None:
                return CommitResultV1(
                    status=CommitStatusV1.FINALITY_REJECTED,
                    state=self._state,
                    candidate_id=verified_root.candidate_id,
                    reason=finality_reason,
                )
            try:
                verified_root = reverify_zrpf_handle_v1(self._subject, verified_root)
            except ValueError as exc:
                return CommitResultV1(
                    status=CommitStatusV1.FINALITY_REJECTED,
                    state=self._state,
                    candidate_id=verified_root.candidate_id,
                    reason=str(exc),
                )
            try:
                outbox_atoms = _new_outbox_atoms(self._state, verified_root.post_state)
            except ValueError as exc:
                return CommitResultV1(
                    status=CommitStatusV1.FINALITY_REJECTED,
                    state=self._state,
                    candidate_id=verified_root.candidate_id,
                    reason=str(exc),
                )
            proposal = _CommitProposalV1(
                candidate_id=verified_root.candidate_id,
                pre_state_root=verified_root.journal.pre_state_root,
                post_state=verified_root.post_state,
                publication_root=verified_root.journal.journal_root,
                command_root=verified_root.journal.command_root,
                nonce_root=verified_root.journal.nonce_root,
                value_delta_root=verified_root.journal.value_delta_root,
                history_root=verified_root.journal.history_root,
                nullifier_root=verified_root.journal.nullifier_root,
                outbox_root=verified_root.journal.outbox_root,
                outbox_atoms=outbox_atoms,
                business_status=None,
                business_reject_reason=None,
                zrpf_journal=verified_root.journal,
                zrpf_receipt=M6ZRPFVerificationReceiptRecordV1.from_verified(
                    verified_root.proof_receipt
                ),
                direct_replay=None,
            )
            return self._publish_locked(proposal, finality)

    def publish_direct_batch(
        self,
        direct: DirectBatchCandidateV1,
        finality: VerifiedZenoLedgerFinalityV1,
        tau_certificate: TauBatchCertificateV1 | None,
    ) -> CommitResultV1:
        """Publish a multi-command direct candidate during proof degradation."""

        if not isinstance(direct, DirectBatchCandidateV1):
            raise TypeError("direct batch candidate is not typed")
        if len(direct.commands) < 2:
            raise ValueError("direct batch publication requires at least two commands")
        with self._lock:
            finality_reason = _finality_evidence_reason(self._subject, finality, tau_certificate)
            if finality_reason is not None:
                return CommitResultV1(
                    status=CommitStatusV1.FINALITY_REJECTED,
                    state=self._state,
                    candidate_id=direct.candidate_id,
                    reason=finality_reason,
                )
            if direct.pre_state_root != self._state.state_root and direct.candidate_id not in self._committed_ids:
                return CommitResultV1(
                    status=CommitStatusV1.STALE_HEAD,
                    state=self._state,
                    candidate_id=direct.candidate_id,
                    reason="expected pre-state root differs from current state",
                )
            if direct.candidate_id not in self._committed_ids:
                try:
                    replayed = execute_direct_batch_v1(
                        self._subject,
                        self._state,
                        direct.contexts,
                        direct.commands,
                    )
                except (TypeError, ValueError) as exc:
                    return CommitResultV1(
                        status=CommitStatusV1.FINALITY_REJECTED,
                        state=self._state,
                        candidate_id=direct.candidate_id,
                        reason=f"direct batch replay rejected: {exc}",
                    )
                if replayed != direct:
                    return CommitResultV1(
                        status=CommitStatusV1.FINALITY_REJECTED,
                        state=self._state,
                        candidate_id=direct.candidate_id,
                        reason="direct batch replay does not match execution witness",
                    )
            try:
                outbox_atoms = _new_outbox_atoms(direct.pre_state, direct.post_state)
            except ValueError as exc:
                return CommitResultV1(
                    status=CommitStatusV1.FINALITY_REJECTED,
                    state=self._state,
                    candidate_id=direct.candidate_id,
                    reason=str(exc),
                )
            proposal = _direct_batch_proposal(direct, outbox_atoms)
            return self._publish_locked(proposal, finality)

    def _publish_locked(
        self,
        proposal: _CommitProposalV1,
        finality: VerifiedZenoLedgerFinalityV1,
    ) -> CommitResultV1:
        committed_post_root = self._committed_ids.get(proposal.candidate_id)
        if committed_post_root is not None:
            record = self._records[proposal.candidate_id]
            replay_reason = _committed_replay_binding_reason(
                record,
                proposal,
                committed_post_root,
            )
            if replay_reason is not None:
                return CommitResultV1(
                    status=CommitStatusV1.FINALITY_REJECTED,
                    state=self._state,
                    candidate_id=proposal.candidate_id,
                    reason=replay_reason,
                )
            finality_binding_reason = _finality_record_binding_reason(
                self._subject,
                record,
                finality,
            )
            if finality_binding_reason is not None:
                return CommitResultV1(
                    status=CommitStatusV1.FINALITY_REJECTED,
                    state=self._state,
                    candidate_id=proposal.candidate_id,
                    reason=finality_binding_reason,
                )
            if (
                record.finality != finality.certificate
                or record.tau_certificate != finality.tau_certificate
            ):
                return CommitResultV1(
                    status=CommitStatusV1.FINALITY_REJECTED,
                    state=self._state,
                    candidate_id=proposal.candidate_id,
                    reason="replay finality evidence conflicts with committed record",
                )
            return CommitResultV1(
                status=CommitStatusV1.ALREADY_COMMITTED,
                state=self._state,
                candidate_id=proposal.candidate_id,
                record=record,
            )
        externally_verified, finality_reason = self._verify_finality_at_commit_boundary(
            proposal,
            finality,
        )
        if externally_verified is None:
            return CommitResultV1(
                status=CommitStatusV1.FINALITY_REJECTED,
                state=self._state,
                candidate_id=proposal.candidate_id,
                reason=finality_reason,
            )
        finality = externally_verified
        if self._state.state_root != proposal.pre_state_root:
            return CommitResultV1(
                status=CommitStatusV1.STALE_HEAD,
                state=self._state,
                candidate_id=proposal.candidate_id,
                reason="expected pre-state root differs from current state",
            )
        reason = self._validation_reason(proposal, finality)
        if reason is not None:
            return CommitResultV1(
                status=CommitStatusV1.FINALITY_REJECTED,
                state=self._state,
                candidate_id=proposal.candidate_id,
                reason=reason,
            )
        committed_state = _with_finality(proposal.post_state, finality.certificate)
        record = _make_published_record(proposal, finality, self._state.head)
        self._state = committed_state
        self._committed_ids[proposal.candidate_id] = proposal.post_state.state_root
        self._records[proposal.candidate_id] = record
        return CommitResultV1(
            status=CommitStatusV1.COMMITTED,
            state=committed_state,
            candidate_id=proposal.candidate_id,
            record=record,
        )

    def _verify_finality_at_commit_boundary(
        self,
        proposal: _CommitProposalV1,
        caller_finality: VerifiedZenoLedgerFinalityV1,
    ) -> tuple[VerifiedZenoLedgerFinalityV1 | None, str | None]:
        """Reauthorize finality through the configured external verifier port."""

        if self._finality_verifier is None:
            return None, "external finality verifier is unavailable"
        if not isinstance(caller_finality, VerifiedZenoLedgerFinalityV1):
            return None, "finality evidence must be verifier-created"
        if caller_finality.candidate_parent_head != self._state.head:
            return None, "finality evidence parent head mismatch"
        if caller_finality.candidate_head != proposal.post_state.state_root:
            return None, "finality evidence candidate head mismatch"
        if caller_finality.publication_root != proposal.publication_root:
            return None, "finality evidence publication root mismatch"
        if caller_finality.expected_command_root != proposal.command_root:
            return None, "finality evidence command root mismatch"
        if caller_finality.expected_nonce_root != proposal.nonce_root:
            return None, "finality evidence nonce root mismatch"
        try:
            receipt = self._finality_verifier.verify_finality(
                self._subject,
                candidate_parent_head=self._state.head,
                candidate_head=proposal.post_state.state_root,
                publication_root=proposal.publication_root,
                expected_writer_epoch=proposal.post_state.writer_epoch,
                expected_command_root=proposal.command_root,
                expected_nonce_root=proposal.nonce_root,
                expected_execution_receipt_root=(
                    None if proposal.zrpf_receipt is None else proposal.zrpf_receipt.receipt_root
                ),
                certificate=caller_finality.certificate,
                tau_certificate=caller_finality.tau_certificate,
            )
            if not isinstance(receipt, M6FinalityVerificationReceiptV1):
                return None, "external finality verifier returned an untyped receipt"
            verified = verify_zeno_ledger_finality_v1(
                self._subject,
                candidate_head=proposal.post_state.state_root,
                publication_root=proposal.publication_root,
                candidate_parent_head=self._state.head,
                expected_writer_epoch=proposal.post_state.writer_epoch,
                expected_command_root=proposal.command_root,
                expected_nonce_root=proposal.nonce_root,
                expected_execution_receipt_root=(
                    None if proposal.zrpf_receipt is None else proposal.zrpf_receipt.receipt_root
                ),
                certificate=caller_finality.certificate,
                tau_certificate=caller_finality.tau_certificate,
                verification_receipt=receipt,
            )
        except (TypeError, ValueError):
            return None, "external finality verification rejected"
        except Exception:
            # The verifier is an imperative adapter boundary.  Backend
            # outages, timeouts, and adapter failures must become a typed
            # no-commit result.  Backend details stay on the trusted side of
            # the publication API because they may contain provider secrets.
            return None, "external finality verification failed"
        return verified, None

    def _validation_reason(
        self,
        proposal: _CommitProposalV1,
        finality: VerifiedZenoLedgerFinalityV1,
        _mode_for_edge=expected_finality_mode_v1,
    ) -> str | None:
        if self._state.deployment != self._subject.deployment:
            return "current state deployment does not match promotion subject"
        if proposal.post_state.deployment != self._subject.deployment:
            return "candidate state deployment does not match promotion subject"
        if proposal.post_state.writer_epoch < self._state.writer_epoch:
            return "candidate writer epoch regresses current writer epoch"
        if proposal.history_root != proposal.post_state.history_root:
            return "candidate history root does not match post-state"
        if proposal.nullifier_root != proposal.post_state.nullifier_root:
            return "candidate nullifier root does not match post-state"
        if proposal.outbox_root != proposal.post_state.outbox_root:
            return "candidate outbox root does not match post-state"
        expected_mode = _mode_for_edge(
            self._state.migration.phase,
            proposal.post_state.migration.phase,
        )
        if expected_mode is None:
            return "migration phase transition is not admitting economic publication"
        if finality.certificate.mode is not expected_mode:
            if expected_mode is FinalityModeV1.TAU_ORDERED:
                return "normal migration phase requires Tau-ordered finality"
            if proposal.post_state.migration.phase is MigrationPhaseV1.FALLBACK:
                return "fallback activation requires forced-inclusion finality"
            return "fallback migration phase requires forced-inclusion finality"
        finality_binding_reason = _finality_proposal_binding_reason(
            self._subject,
            current_parent_head=self._state.head,
            proposal=proposal,
            finality=finality,
        )
        if finality_binding_reason is not None:
            return finality_binding_reason
        try:
            validate_economic_state_v1(self._state)
            validate_economic_state_v1(proposal.post_state)
            verify_finality_certificate_v1(
                self._subject,
                candidate_head=proposal.post_state.state_root,
                publication_root=proposal.publication_root,
                current_writer_epoch=proposal.post_state.writer_epoch,
                candidate_parent_head=self._state.head,
                expected_command_root=proposal.command_root,
                expected_nonce_root=proposal.nonce_root,
                expected_execution_receipt_root=(
                    None if proposal.zrpf_receipt is None else proposal.zrpf_receipt.receipt_root
                ),
                certificate=finality.certificate,
                tau_certificate=finality.tau_certificate,
            )
        except ValueError as exc:
            return str(exc)
        return None


def _committed_replay_binding_reason(
    record: M6PublishedRecordV1,
    proposal: _CommitProposalV1,
    indexed_post_state_root: str,
) -> str | None:
    """Require every publication projection to match an idempotent replay."""

    try:
        validate_economic_state_v1(proposal.post_state)
    except ValueError as exc:
        return f"replay candidate body economic state invalid: {exc}"
    bindings = (
        ("candidate id", record.candidate_id, proposal.candidate_id),
        ("pre-state root", record.pre_state_root, proposal.pre_state_root),
        ("indexed post-state root", indexed_post_state_root, proposal.post_state.state_root),
        ("post-state root", record.post_state_root, proposal.post_state.state_root),
        ("publication root", record.publication_root, proposal.publication_root),
        ("command root", record.command_root, proposal.command_root),
        ("nonce root", _record_nonce_root(record), proposal.nonce_root),
        ("value-delta root", record.value_delta_root, proposal.value_delta_root),
        ("history root", record.history_root, proposal.history_root),
        ("nullifier root", record.nullifier_root, proposal.nullifier_root),
        ("outbox root", record.outbox_root, proposal.outbox_root),
        ("business status", record.business_status, proposal.business_status),
        ("business reject reason", record.business_reject_reason, proposal.business_reject_reason),
    )
    for name, committed_value, replayed_value in bindings:
        if committed_value != replayed_value:
            return f"replay candidate body conflicts with committed record: {name}"
    if record.outbox_atoms != proposal.outbox_atoms:
        return "replay candidate body conflicts with committed record: outbox atoms"
    if record.zrpf_journal != proposal.zrpf_journal:
        return "replay candidate body conflicts with committed record: ZRPF journal"
    if record.zrpf_receipt != proposal.zrpf_receipt:
        return "replay candidate body conflicts with committed record: ZRPF receipt"
    if record.direct_replay != proposal.direct_replay:
        return "replay candidate body conflicts with committed record: direct execution body"
    if record.direct_batch_replay != proposal.direct_batch_replay:
        return "replay candidate body conflicts with committed record: direct batch body"
    if record.direct_batch_data_availability_root != proposal.direct_batch_data_availability_root:
        return "replay candidate body conflicts with committed record: direct batch data availability"
    return None


def _record_nonce_root(record: M6PublishedRecordV1) -> str | None:
    """Derive the committed nonce root from the retained execution body."""

    if record.zrpf_journal is not None:
        return record.zrpf_journal.nonce_root
    if record.direct_replay is not None:
        return ordered_root_v1(
            "m6-direct-nonce-root-v1",
            (f"{record.direct_replay.context_sender}:{record.direct_replay.context_nonce}",),
        )
    if record.direct_batch_replay is not None:
        return ordered_root_v1(
            "m6-direct-nonce-root-v1",
            tuple(item.nonce_identity for item in record.direct_batch_replay),
        )
    return None


def _finality_evidence_reason(
    subject: M6PromotionSubjectV1,
    finality: object,
    tau_certificate: TauBatchCertificateV1 | None,
) -> str | None:
    if not isinstance(finality, VerifiedZenoLedgerFinalityV1):
        return "finality evidence must be verifier-created"
    if finality.subject_root != subject.subject_root:
        return "finality evidence promotion subject mismatch"
    if finality.tau_certificate != tau_certificate:
        return "finality evidence Tau certificate mismatch"
    return None


def _finality_proposal_binding_reason(
    subject: M6PromotionSubjectV1,
    *,
    current_parent_head: str,
    proposal: _CommitProposalV1,
    finality: VerifiedZenoLedgerFinalityV1,
) -> str | None:
    """Bind opaque finality metadata to the exact publication proposal."""

    if finality.subject_root != subject.subject_root:
        return "finality evidence promotion subject mismatch"
    if finality.candidate_parent_head != current_parent_head:
        return "finality evidence parent head mismatch"
    if finality.candidate_head != proposal.post_state.state_root:
        return "finality evidence candidate head mismatch"
    if finality.publication_root != proposal.publication_root:
        return "finality evidence publication root mismatch"
    if finality.expected_command_root != proposal.command_root:
        return "finality evidence command root mismatch"
    if finality.expected_nonce_root != proposal.nonce_root:
        return "finality evidence nonce root mismatch"
    expected_receipt_root = None if proposal.zrpf_receipt is None else proposal.zrpf_receipt.receipt_root
    if finality.certificate.execution_receipt_root != expected_receipt_root:
        return "finality evidence execution receipt root mismatch"
    if (
        finality.verification_receipt.candidate_parent_head != current_parent_head
        or finality.verification_receipt.candidate_head != proposal.post_state.state_root
        or finality.verification_receipt.publication_root != proposal.publication_root
        or finality.verification_receipt.writer_epoch != finality.certificate.writer_epoch
        or finality.verification_receipt.certificate_root != finality.certificate.certificate_root
    ):
        return "finality evidence verification receipt mismatch"
    return None


def _finality_record_binding_reason(
    subject: M6PromotionSubjectV1,
    record: M6PublishedRecordV1,
    finality: VerifiedZenoLedgerFinalityV1,
) -> str | None:
    """Bind replay evidence to the already-published record, not current head."""

    if finality.subject_root != subject.subject_root:
        return "finality evidence promotion subject mismatch"
    if finality.candidate_parent_head != record.parent_head:
        return "finality evidence parent head mismatch"
    if finality.candidate_head != record.post_state_root:
        return "finality evidence candidate head mismatch"
    if finality.publication_root != record.publication_root:
        return "finality evidence publication root mismatch"
    if finality.expected_command_root != record.command_root:
        return "finality evidence command root mismatch"
    if finality.expected_nonce_root != _record_nonce_root(record):
        return "finality evidence nonce root mismatch"
    expected_receipt_root = None if record.zrpf_receipt is None else record.zrpf_receipt.receipt_root
    if finality.certificate.execution_receipt_root != expected_receipt_root:
        return "finality evidence execution receipt root mismatch"
    if record.finality_receipt is None:
        return "durable finality verification receipt is missing"
    if record.finality_receipt.receipt_root != finality.verification_receipt.receipt_root:
        return "finality evidence verification receipt mismatch"
    return None


def finality_evidence_matches_published_record_v1(
    subject: M6PromotionSubjectV1,
    record: M6PublishedRecordV1,
    finality: object,
    tau_certificate: TauBatchCertificateV1 | None,
) -> bool:
    """Share the exact replay-authority predicate with durable storage."""

    if not isinstance(finality, VerifiedZenoLedgerFinalityV1):
        return False
    if _finality_record_binding_reason(subject, record, finality) is not None:
        return False
    return (
        record.finality == finality.certificate
        and record.finality_receipt is not None
        and record.finality_receipt.receipt_root == finality.verification_receipt.receipt_root
        and record.tau_certificate == finality.tau_certificate
        and finality.tau_certificate == tau_certificate
    )


def reverify_zrpf_handle_v1(
    subject: M6PromotionSubjectV1,
    verified_root: VerifiedZRPFRootV1,
) -> VerifiedZRPFRootV1:
    """Recheck the exact batch owned by a ZRPF handle before any publication."""

    execution_batch = verified_root.execution_batch
    if not isinstance(execution_batch, ZRPFBatchCandidateV1):
        raise ValueError("ZRPF handle is missing its checked execution batch")
    try:
        replayed_batch = verify_zrpf_structure_v1(subject, execution_batch)
        proof_receipt = verified_root.proof_receipt
    except (TypeError, ValueError) as exc:
        raise ValueError(f"ZRPF execution replay rejected: {exc}") from exc
    if not isinstance(proof_receipt, M6ZRPFVerificationReceiptV1):
        raise ValueError("ZRPF handle is missing a typed proof receipt")
    if (
        proof_receipt.promotion_subject_root != verified_root.journal.promotion_subject_root
        or proof_receipt.profile != verified_root.journal.profile
        or proof_receipt.verifier_image != verified_root.journal.verifier_image
        or proof_receipt.journal_root != verified_root.journal.journal_root
        or proof_receipt.data_availability_root != verified_root.journal.data_availability_root
    ):
        raise ValueError("ZRPF handle proof receipt binding mismatch")
    if (
        replayed_batch.journal != verified_root.journal
        or replayed_batch.candidate_id != verified_root.candidate_id
        or replayed_batch.post_state != verified_root.post_state
        or replayed_batch != execution_batch
    ):
        raise ValueError("ZRPF handle does not match its checked execution batch")
    for name, journal_value, state_value in (
        ("history root", replayed_batch.journal.history_root, replayed_batch.post_state.history_root),
        ("outbox root", replayed_batch.journal.outbox_root, replayed_batch.post_state.outbox_root),
        ("nullifier root", replayed_batch.journal.nullifier_root, replayed_batch.post_state.nullifier_root),
    ):
        if journal_value != state_value:
            raise ValueError(f"ZRPF journal {name} does not match post-state")
    return verified_root


def _with_finality(
    post_state: M6ApplicationStateV1,
    finality: ZenoLedgerFinalityCertificateV1,
) -> M6ApplicationStateV1:
    return M6ApplicationStateV1(
        deployment=post_state.deployment,
        head=post_state.head,
        writer_epoch=post_state.writer_epoch,
        ingress_nonces=post_state.ingress_nonces,
        economic_atoms=post_state.economic_atoms,
        history=post_state.history,
        nullifiers=post_state.nullifiers,
        finality_certificates=post_state.finality_certificates + (finality,),
        migration=post_state.migration,
        escrows=post_state.escrows,
        withdrawals=post_state.withdrawals,
        outbox=post_state.outbox,
        acknowledgments=post_state.acknowledgments,
        seller_auction_bids=post_state.seller_auction_bids,
        private_swap_participants=post_state.private_swap_participants,
        history_root_cache=post_state.history_root,
        nullifier_root_cache=post_state.nullifier_root,
        outbox_root_cache=post_state.outbox_root,
    )


def _new_outbox_atoms(
    current_state: M6ApplicationStateV1,
    candidate_state: M6ApplicationStateV1,
) -> tuple[OutboxAtomV1, ...]:
    """Return only the outbox rows created by this candidate.

    A verified batch carries the complete post-state, while the publication
    receipt must carry the exact newly-created external effects.  Deriving the
    suffix under the commit lock prevents a ZRPF path from publishing an empty
    or replayed outbox while retaining the candidate's post-state root.
    """

    prefix_length = len(current_state.outbox)
    if candidate_state.outbox[:prefix_length] != current_state.outbox:
        raise ValueError("candidate post-state does not preserve the committed outbox prefix")
    return candidate_state.outbox[prefix_length:]


def _direct_proposal(
    candidate: AcceptCandidateV1,
    outbox_atoms: tuple[OutboxAtomV1, ...],
) -> _CommitProposalV1:
    return _CommitProposalV1(
        candidate_id=candidate.candidate_id,
        pre_state_root=candidate.pre_state_root,
        post_state=candidate.post_state,
        publication_root=candidate.publication_atom.publication_root,
        command_root=ordered_root_v1(
            "m6-direct-command-root-v1",
            (candidate.command.command_hash,),
        ),
        nonce_root=ordered_root_v1(
            "m6-direct-nonce-root-v1",
            (candidate.command.nonce_identity,),
        ),
        value_delta_root=candidate.value_delta.delta_root,
        history_root=candidate.post_state.history_root,
        nullifier_root=candidate.post_state.nullifier_root,
        outbox_root=candidate.post_state.outbox_root,
        outbox_atoms=outbox_atoms,
        business_status=candidate.business_status,
        business_reject_reason=candidate.business_reject_reason,
        zrpf_journal=None,
        zrpf_receipt=None,
        direct_replay=DirectExecutionReplayV1.from_execution(
            candidate.command,
            candidate.context,
            candidate,
        ),
    )


def _direct_batch_proposal(
    candidate: DirectBatchCandidateV1,
    outbox_atoms: tuple[OutboxAtomV1, ...],
) -> _CommitProposalV1:
    return _CommitProposalV1(
        candidate_id=candidate.candidate_id,
        pre_state_root=candidate.pre_state_root,
        post_state=candidate.post_state,
        publication_root=candidate.publication_root,
        command_root=candidate.command_root,
        nonce_root=candidate.nonce_root,
        value_delta_root=candidate.value_delta_root,
        history_root=candidate.history_root,
        nullifier_root=candidate.nullifier_root,
        outbox_root=candidate.outbox_root,
        outbox_atoms=outbox_atoms,
        business_status=None,
        business_reject_reason=None,
        zrpf_journal=None,
        zrpf_receipt=None,
        direct_replay=None,
        direct_batch_replay=tuple(
            DirectExecutionReplayV1.from_execution(
                command,
                context,
                candidate_item,
                retain_candidate_projection=True,
            )
            for command, context, candidate_item in zip(
                candidate.commands,
                candidate.contexts,
                candidate.candidates,
                strict=True,
            )
        ),
        direct_batch_data_availability_root=candidate.data_availability_root,
    )


def _candidate_binding_reason(
    current_state: M6ApplicationStateV1,
    candidate: AcceptCandidateV1,
) -> str | None:
    """Check direct candidate projections before finality can authorize them."""

    if candidate.value_delta.pre_state_root != candidate.pre_state_root:
        return "candidate delta/pre-state root mismatch"
    if candidate.history_atom.pre_state_root != candidate.pre_state_root:
        return "candidate history/pre-state root mismatch"
    if candidate.publication_atom.pre_state_root != candidate.pre_state_root:
        return "candidate publication/pre-state root mismatch"
    if candidate.publication_atom.history_root != candidate.post_state.history_root:
        return "candidate publication history root mismatch"
    if candidate.publication_atom.nullifier_root != candidate.post_state.nullifier_root:
        return "candidate publication nullifier root mismatch"
    if candidate.publication_atom.value_delta_root != candidate.value_delta.delta_root:
        return "candidate publication delta root mismatch"
    if candidate.publication_atom.outbox_root != candidate.post_state.outbox_root:
        return "candidate publication outbox root mismatch"
    if candidate.publication_atom.execution_context_root != candidate.context.authentication_root:
        return "candidate publication/context root mismatch"
    if candidate.publication_atom.writer_epoch != candidate.post_state.writer_epoch:
        return "candidate publication writer epoch mismatch"
    if candidate.publication_atom.business_status is not candidate.business_status:
        return "candidate publication business status mismatch"
    if candidate.publication_atom.business_reject_reason is not candidate.business_reject_reason:
        return "candidate publication business reject reason mismatch"
    if candidate.history_atom.sender != candidate.command.sender:
        return "candidate history sender binding mismatch"
    if candidate.history_atom.nonce != candidate.command.nonce:
        return "candidate history nonce binding mismatch"
    if candidate.history_atom.outcome is not candidate.business_status:
        return "candidate history outcome binding mismatch"
    if candidate.history_atom.business_reject_reason is not candidate.business_reject_reason:
        return "candidate history business reject reason mismatch"
    if candidate.history_atom.value_delta_root != candidate.value_delta.delta_root:
        return "candidate history delta binding mismatch"
    if candidate.post_state.head != candidate.post_state.state_root:
        return "candidate head does not equal post-state root"
    if candidate.post_state.history != current_state.history + (candidate.history_atom,):
        return "candidate history archive is not the current prefix plus one atom"
    if candidate.post_state.nullifiers != current_state.nullifiers + (candidate.history_atom.nullifier,):
        return "candidate nullifier archive is not the current prefix plus one atom"
    if candidate.post_state.finality_certificates != current_state.finality_certificates:
        return "candidate finality archive changed during direct execution"
    if candidate.post_state.deployment != current_state.deployment:
        return "candidate deployment changed during direct execution"
    expected_candidate_id = hash_v1(
        "m6-candidate-id-v1",
        {
            "command_hash": candidate.command.command_hash,
            "pre_state_root": candidate.pre_state_root,
            "post_state_root": candidate.post_state.state_root,
        },
    )
    if candidate.candidate_id != expected_candidate_id:
        return "candidate identity is not bound to command and state roots"
    return None


def _make_published_record(
    proposal: _CommitProposalV1,
    finality: VerifiedZenoLedgerFinalityV1,
    parent_head: str,
) -> M6PublishedRecordV1:
    return M6PublishedRecordV1(
        candidate_id=proposal.candidate_id,
        parent_head=parent_head,
        pre_state_root=proposal.pre_state_root,
        post_state_root=proposal.post_state.state_root,
        publication_root=proposal.publication_root,
        command_root=proposal.command_root,
        value_delta_root=proposal.value_delta_root,
        history_root=proposal.history_root,
        nullifier_root=proposal.nullifier_root,
        outbox_root=proposal.outbox_root,
        outbox_atoms=proposal.outbox_atoms,
        finality=finality.certificate,
        finality_receipt=M6FinalityVerificationReceiptRecordV1.from_verified(
            finality.verification_receipt,
        ),
        tau_certificate=finality.tau_certificate,
        business_status=proposal.business_status,
        business_reject_reason=proposal.business_reject_reason,
        zrpf_journal=proposal.zrpf_journal,
        zrpf_receipt=proposal.zrpf_receipt,
        direct_replay=proposal.direct_replay,
        direct_batch_replay=proposal.direct_batch_replay,
        direct_batch_data_availability_root=proposal.direct_batch_data_availability_root,
    )


__all__ = [
    "CommitStatusV1",
    "M6FinalityVerifierV1",
    "DirectExecutionReplayV1",
    "direct_batch_data_availability_root_v1",
    "M6PublishedRecordV1",
    "candidate_matches_published_record_v1",
    "direct_batch_matches_published_record_v1",
    "finality_evidence_matches_published_record_v1",
    "reverify_zrpf_handle_v1",
    "CommitResultV1",
    "M6CommitPortV1",
]
