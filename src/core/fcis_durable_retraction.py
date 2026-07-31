"""Research-only durable retraction and detectable retry algebra for FCIS.

The module models the missing stateful connective between an authorized FCIS
candidate and its durable, recoverable, and externally deliverable effects.
It is deliberately independent of a concrete database.  Its role is to make the
required refinement contract executable before a SQLite/PostgreSQL adapter is
trusted.

Core construction
-----------------
For canonical authorized histories ``A`` and durable layouts ``D``:

    encode : A -> D
    reopen : D -> A | Reject

The accepted layouts satisfy ``reopen(encode(a)) = a``.  Canonical normalization
is ``N = encode o reopen``.  A durable layout is authoritative only when it is an
exact fixed point of ``N``.  Missing, extra, duplicated, reordered, crossed, or
foreign rows therefore fail the same equality gate rather than relying on a
selected digest.

The module additionally distinguishes durable outcomes from client knowledge.
An indeterminate transport observation is not a fifth durable commit state: a
fresh canonical read resolves it to already-committed, stale, rejected/collision,
or safely retryable.

This remains unmounted research evidence.  It does not prove that a production
datastore implements the abstract atomic step, that a destination implements
idempotent effect identities, or that every production publisher is inventoried.
"""

from __future__ import annotations

from dataclasses import InitVar, dataclass
from enum import Enum
from hashlib import sha256
from typing import Final, TypeAlias, TypeGuard, cast

MAX_TRANSITIONS: Final = 128
MAX_OUTBOX_PER_TRANSITION: Final = 64
MAX_ACKS: Final = 8_192
MAX_AUTHORITY_EPOCHS: Final = MAX_TRANSITIONS + 1
MAX_EVIDENCE_ROWS: Final = MAX_TRANSITIONS * 7
MAX_NULLIFIER_ROWS: Final = MAX_TRANSITIONS
MAX_OUTBOX_ROWS: Final = MAX_TRANSITIONS * MAX_OUTBOX_PER_TRANSITION
MAX_DESTINATION_RECEIPTS: Final = MAX_OUTBOX_ROWS
MAX_DURABLE_CANONICAL_BYTES: Final = 8 * 1024 * 1024
U32_MAX: Final = (1 << 32) - 1
MAX_TEXT_BYTES: Final = 256
_HEX: Final = frozenset("0123456789abcdef")


class DurableRetractionError(ValueError):
    """Exact validation or canonical reconstruction failure."""


def _exact_int(value: object, name: str, *, minimum: int = 0) -> int:
    if type(value) is not int or value < minimum:
        raise DurableRetractionError(f"{name} must be an exact int >= {minimum}")
    return value


def _exact_u32(value: object, name: str) -> int:
    checked = _exact_int(value, name)
    if checked > U32_MAX:
        raise DurableRetractionError(f"{name} must fit the u32 domain")
    return checked


def _bounded_text(value: object, name: str) -> str:
    if type(value) is not str:
        raise DurableRetractionError(f"{name} must be an exact string")
    encoded = value.encode("utf-8")
    if not encoded or len(encoded) > MAX_TEXT_BYTES:
        raise DurableRetractionError(f"{name} is empty or exceeds its byte bound")
    return value


def _digest(value: object, name: str) -> str:
    if (
        type(value) is not str
        or len(value) != 64
        or any(character not in _HEX for character in value)
    ):
        raise DurableRetractionError(f"{name} must be 64 lowercase hexadecimal characters")
    return value


def _frame(value: bytes) -> bytes:
    return len(value).to_bytes(8, "big") + value


def _hash_fields(domain: str, fields: tuple[bytes, ...]) -> str:
    digest = sha256()
    digest.update(_frame(domain.encode("ascii")))
    digest.update(len(fields).to_bytes(4, "big"))
    for field in fields:
        digest.update(_frame(field))
    return digest.hexdigest()


def tagged_digest(label: str) -> str:
    """Deterministic test/research digest helper; not a production codec."""

    return _hash_fields("zenodex/fcis/dra/tagged/v1", (label.encode("utf-8"),))


_DEFAULT_DEPLOYMENT_CONFIG_ROOT: Final = tagged_digest("deployment/config/research-v1")
_DEFAULT_VERIFIER_PROFILE_ROOT: Final = tagged_digest("verifier/reopen/research-v1")
_DEFAULT_DESTINATION_VERIFIER_PROFILE_ROOT: Final = tagged_digest(
    "verifier/destination/research-v1"
)


class MigrationPhaseV1(Enum):
    LEGACY = "LEGACY"
    SHADOW_REPLAY = "SHADOW_REPLAY"
    DUAL_CHECK = "DUAL_CHECK"
    QUIESCED = "QUIESCED"
    AUTHORITY_SWITCH = "AUTHORITY_SWITCH"
    POST_SWITCH_VALIDATION = "POST_SWITCH_VALIDATION"
    LEGACY_DISABLED = "LEGACY_DISABLED"


_PHASE_ORDER: Final = (
    MigrationPhaseV1.LEGACY,
    MigrationPhaseV1.SHADOW_REPLAY,
    MigrationPhaseV1.DUAL_CHECK,
    MigrationPhaseV1.QUIESCED,
    MigrationPhaseV1.AUTHORITY_SWITCH,
    MigrationPhaseV1.POST_SWITCH_VALIDATION,
    MigrationPhaseV1.LEGACY_DISABLED,
)


@dataclass(frozen=True, slots=True, order=True)
class OutboxEffectV1:
    effect_id: str
    ordinal: int
    destination: str
    payload_root: str
    adapter_profile_root: str

    def __post_init__(self) -> None:
        _digest(self.effect_id, "effect_id")
        ordinal = _exact_u32(self.ordinal, "ordinal")
        if ordinal >= MAX_OUTBOX_PER_TRANSITION:
            raise DurableRetractionError("ordinal exceeds the per-transition bound")
        _bounded_text(self.destination, "destination")
        _digest(self.payload_root, "payload_root")
        _digest(self.adapter_profile_root, "adapter_profile_root")


@dataclass(frozen=True, slots=True, order=True)
class DeliveryAckV1:
    effect_id: str
    destination: str
    payload_root: str
    destination_receipt_root: str
    adapter_profile_root: str
    idempotency_root: str
    response_root: str

    def __post_init__(self) -> None:
        _digest(self.effect_id, "effect_id")
        _bounded_text(self.destination, "destination")
        _digest(self.payload_root, "payload_root")
        _digest(self.destination_receipt_root, "destination_receipt_root")
        _digest(self.adapter_profile_root, "adapter_profile_root")
        _digest(self.idempotency_root, "idempotency_root")
        _digest(self.response_root, "response_root")


@dataclass(frozen=True, slots=True)
class PublicationAtomV1:
    sequence: int
    commit_id: str
    command_root: str
    expected_pre_root: str
    post_state_root: str
    writer_profile_root: str
    authority_epoch_index: int
    authority_state_root: str
    nullifier_root: str
    response_root: str
    receipt_root: str
    decision_root: str
    bundle_root: str
    replay_root: str
    outbox: tuple[OutboxEffectV1, ...]

    def __post_init__(self) -> None:
        sequence = _exact_int(self.sequence, "sequence", minimum=1)
        if sequence > MAX_TRANSITIONS:
            raise DurableRetractionError("sequence exceeds the transition bound")
        _exact_u32(self.authority_epoch_index, "authority_epoch_index")
        for name in (
            "commit_id",
            "command_root",
            "expected_pre_root",
            "post_state_root",
            "writer_profile_root",
            "authority_state_root",
            "nullifier_root",
            "response_root",
            "receipt_root",
            "decision_root",
            "bundle_root",
            "replay_root",
        ):
            _digest(object.__getattribute__(self, name), name)
        if type(self.outbox) is not tuple:
            raise DurableRetractionError("outbox must be an exact tuple")
        if len(self.outbox) > MAX_OUTBOX_PER_TRANSITION:
            raise DurableRetractionError("outbox exceeds the per-transition bound")
        for effect in self.outbox:
            if type(effect) is not OutboxEffectV1:
                raise DurableRetractionError("outbox effect has the wrong exact type")
            effect.__post_init__()
        if tuple(sorted(self.outbox, key=lambda item: item.ordinal)) != self.outbox:
            raise DurableRetractionError("outbox effects must be in ordinal order")
        if tuple(effect.ordinal for effect in self.outbox) != tuple(range(len(self.outbox))):
            raise DurableRetractionError("outbox ordinals must be contiguous from zero")
        effect_ids = tuple(effect.effect_id for effect in self.outbox)
        if len(set(effect_ids)) != len(effect_ids):
            raise DurableRetractionError("outbox effect identities must be unique")
        for effect in self.outbox:
            expected = derive_effect_id(
                commit_id=self.commit_id,
                ordinal=effect.ordinal,
                destination=effect.destination,
                payload_root=effect.payload_root,
                writer_profile_root=self.writer_profile_root,
                adapter_profile_root=effect.adapter_profile_root,
            )
            if effect.effect_id != expected:
                raise DurableRetractionError(
                    "outbox effect identity is not derived from its publication atom"
                )

    @property
    def fingerprint(self) -> str:
        return _hash_fields(
            "zenodex/fcis/dra/commit-fingerprint/v1",
            (
                bytes.fromhex(self.commit_id),
                bytes.fromhex(self.command_root),
                bytes.fromhex(self.expected_pre_root),
                bytes.fromhex(self.post_state_root),
                bytes.fromhex(self.writer_profile_root),
                self.authority_epoch_index.to_bytes(4, "big"),
                bytes.fromhex(self.authority_state_root),
                bytes.fromhex(self.nullifier_root),
                bytes.fromhex(self.response_root),
                bytes.fromhex(self.receipt_root),
                bytes.fromhex(self.decision_root),
                bytes.fromhex(self.bundle_root),
                bytes.fromhex(self.replay_root),
                bytes.fromhex(outbox_root(self.outbox)),
            ),
        )

    @property
    def atom_root(self) -> str:
        return _hash_fields(
            "zenodex/fcis/dra/publication-atom/v1",
            (
                self.sequence.to_bytes(8, "big"),
                bytes.fromhex(self.fingerprint),
            ),
        )


def derive_effect_id(
    *,
    commit_id: str,
    ordinal: int,
    destination: str,
    payload_root: str,
    writer_profile_root: str,
    adapter_profile_root: str,
) -> str:
    _digest(commit_id, "commit_id")
    checked_ordinal = _exact_u32(ordinal, "ordinal")
    _bounded_text(destination, "destination")
    _digest(payload_root, "payload_root")
    _digest(writer_profile_root, "writer_profile_root")
    _digest(adapter_profile_root, "adapter_profile_root")
    return _hash_fields(
        "zenodex/fcis/dra/effect-id/v1",
        (
            bytes.fromhex(commit_id),
            checked_ordinal.to_bytes(4, "big"),
            destination.encode("utf-8"),
            bytes.fromhex(payload_root),
            bytes.fromhex(writer_profile_root),
            bytes.fromhex(adapter_profile_root),
        ),
    )


def outbox_root(outbox: tuple[OutboxEffectV1, ...]) -> str:
    if type(outbox) is not tuple:
        raise DurableRetractionError("outbox must be an exact tuple")
    fields: list[bytes] = []
    for effect in outbox:
        if type(effect) is not OutboxEffectV1:
            raise DurableRetractionError("outbox effect has the wrong exact type")
        effect.__post_init__()
        fields.extend(
            (
                bytes.fromhex(effect.effect_id),
                effect.ordinal.to_bytes(4, "big"),
                effect.destination.encode("utf-8"),
                bytes.fromhex(effect.payload_root),
                bytes.fromhex(effect.adapter_profile_root),
            )
        )
    return _hash_fields("zenodex/fcis/dra/outbox/v1", tuple(fields))


@dataclass(frozen=True, slots=True)
class AuthorityStateV1:
    epoch_index: int
    phase: MigrationPhaseV1
    legacy_profile_root: str
    target_profile_root: str
    active_profile_root: str
    allowed_writer_roots: tuple[str, ...]
    transport_root: str

    def __post_init__(self) -> None:
        _exact_int(self.epoch_index, "epoch_index")
        if type(self.phase) is not MigrationPhaseV1:
            raise DurableRetractionError("phase has the wrong exact type")
        for name in (
            "legacy_profile_root",
            "target_profile_root",
            "active_profile_root",
            "transport_root",
        ):
            _digest(object.__getattribute__(self, name), name)
        if type(self.allowed_writer_roots) is not tuple:
            raise DurableRetractionError("allowed_writer_roots must be an exact tuple")
        for writer in self.allowed_writer_roots:
            _digest(writer, "allowed_writer_root")
        if tuple(sorted(self.allowed_writer_roots)) != self.allowed_writer_roots:
            raise DurableRetractionError("allowed writers must be canonically ordered")
        if len(set(self.allowed_writer_roots)) != len(self.allowed_writer_roots):
            raise DurableRetractionError("allowed writers must be unique")
        expected_active, expected_writers = _authority_profile_for_phase(
            self.phase,
            self.legacy_profile_root,
            self.target_profile_root,
        )
        if self.active_profile_root != expected_active:
            raise DurableRetractionError("active profile disagrees with the lifecycle phase")
        if self.allowed_writer_roots != expected_writers:
            raise DurableRetractionError("writer set disagrees with the lifecycle phase")

    @property
    def root(self) -> str:
        fields: list[bytes] = [
            self.epoch_index.to_bytes(4, "big"),
            self.phase.value.encode("ascii"),
            bytes.fromhex(self.legacy_profile_root),
            bytes.fromhex(self.target_profile_root),
            bytes.fromhex(self.active_profile_root),
            bytes.fromhex(self.transport_root),
        ]
        fields.extend(bytes.fromhex(writer) for writer in self.allowed_writer_roots)
        return _hash_fields("zenodex/fcis/dra/authority-state/v1", tuple(fields))


def _authority_profile_for_phase(
    phase: MigrationPhaseV1,
    legacy_profile_root: str,
    target_profile_root: str,
) -> tuple[str, tuple[str, ...]]:
    if phase in (
        MigrationPhaseV1.LEGACY,
        MigrationPhaseV1.SHADOW_REPLAY,
        MigrationPhaseV1.DUAL_CHECK,
    ):
        return legacy_profile_root, (legacy_profile_root,)
    if phase is MigrationPhaseV1.QUIESCED:
        return legacy_profile_root, ()
    return target_profile_root, (target_profile_root,)


def initial_authority_state(
    legacy_profile_root: str,
    target_profile_root: str,
) -> AuthorityStateV1:
    return AuthorityStateV1(
        epoch_index=0,
        phase=MigrationPhaseV1.LEGACY,
        legacy_profile_root=_digest(legacy_profile_root, "legacy_profile_root"),
        target_profile_root=_digest(target_profile_root, "target_profile_root"),
        active_profile_root=legacy_profile_root,
        allowed_writer_roots=(legacy_profile_root,),
        transport_root=tagged_digest("migration/genesis"),
    )


def advance_authority_state(
    authority: AuthorityStateV1,
    next_phase: MigrationPhaseV1,
    transport_root: str,
) -> AuthorityStateV1:
    if type(authority) is not AuthorityStateV1:
        raise DurableRetractionError("authority has the wrong exact type")
    authority.__post_init__()
    if type(next_phase) is not MigrationPhaseV1:
        raise DurableRetractionError("next_phase has the wrong exact type")
    current_index = _PHASE_ORDER.index(authority.phase)
    if current_index + 1 >= len(_PHASE_ORDER):
        raise DurableRetractionError("the authority lifecycle is already terminal")
    if _PHASE_ORDER[current_index + 1] is not next_phase:
        raise DurableRetractionError("authority phases must advance one edge at a time")
    active, writers = _authority_profile_for_phase(
        next_phase,
        authority.legacy_profile_root,
        authority.target_profile_root,
    )
    return AuthorityStateV1(
        epoch_index=authority.epoch_index + 1,
        phase=next_phase,
        legacy_profile_root=authority.legacy_profile_root,
        target_profile_root=authority.target_profile_root,
        active_profile_root=active,
        allowed_writer_roots=writers,
        transport_root=_digest(transport_root, "transport_root"),
    )


@dataclass(frozen=True, slots=True, order=True)
class EvidenceRowV1:
    commit_id: str
    kind: str
    value_root: str

    def __post_init__(self) -> None:
        _digest(self.commit_id, "commit_id")
        _bounded_text(self.kind, "kind")
        _digest(self.value_root, "value_root")


@dataclass(frozen=True, slots=True, order=True)
class NullifierRowV1:
    nullifier_root: str
    commit_id: str
    fingerprint: str

    def __post_init__(self) -> None:
        _digest(self.nullifier_root, "nullifier_root")
        _digest(self.commit_id, "commit_id")
        _digest(self.fingerprint, "fingerprint")


@dataclass(frozen=True, slots=True, order=True)
class OutboxRowV1:
    effect_id: str
    commit_id: str
    ordinal: int
    destination: str
    payload_root: str
    adapter_profile_root: str

    def __post_init__(self) -> None:
        _digest(self.effect_id, "effect_id")
        _digest(self.commit_id, "commit_id")
        _exact_u32(self.ordinal, "ordinal")
        _bounded_text(self.destination, "destination")
        _digest(self.payload_root, "payload_root")
        _digest(self.adapter_profile_root, "adapter_profile_root")


@dataclass(frozen=True, slots=True)
class AuthorizedHistoryV1:
    genesis_state_root: str
    authority_epochs: tuple[AuthorityStateV1, ...]
    atoms: tuple[PublicationAtomV1, ...]
    acks: tuple[DeliveryAckV1, ...]
    deployment_config_root: str = _DEFAULT_DEPLOYMENT_CONFIG_ROOT
    verifier_profile_root: str = _DEFAULT_VERIFIER_PROFILE_ROOT

    def __post_init__(self) -> None:
        _digest(self.genesis_state_root, "genesis_state_root")
        _digest(self.deployment_config_root, "deployment_config_root")
        _digest(self.verifier_profile_root, "verifier_profile_root")
        if type(self.authority_epochs) is not tuple or not self.authority_epochs:
            raise DurableRetractionError("authority_epochs must be a nonempty exact tuple")
        if len(self.authority_epochs) > MAX_AUTHORITY_EPOCHS:
            raise DurableRetractionError("authority_epochs exceeds its row bound")
        previous: AuthorityStateV1 | None = None
        for index, authority in enumerate(self.authority_epochs):
            if type(authority) is not AuthorityStateV1:
                raise DurableRetractionError("authority epoch has the wrong exact type")
            authority.__post_init__()
            if authority.epoch_index != index:
                raise DurableRetractionError("authority epoch indices must be contiguous")
            if previous is not None:
                if (
                    authority.legacy_profile_root != previous.legacy_profile_root
                    or authority.target_profile_root != previous.target_profile_root
                ):
                    raise DurableRetractionError("authority profile lineage changed identity")
                previous_index = _PHASE_ORDER.index(previous.phase)
                if (
                    previous_index + 1 >= len(_PHASE_ORDER)
                    or _PHASE_ORDER[previous_index + 1] is not authority.phase
                ):
                    raise DurableRetractionError("authority lifecycle skipped or regressed")
            previous = authority
        if type(self.atoms) is not tuple or len(self.atoms) > MAX_TRANSITIONS:
            raise DurableRetractionError("atoms has the wrong bounded shape")
        expected_pre = self.genesis_state_root
        previous_epoch = 0
        commit_ids: set[str] = set()
        nullifiers: set[str] = set()
        effect_ids: set[str] = set()
        for index, atom in enumerate(self.atoms, start=1):
            if type(atom) is not PublicationAtomV1:
                raise DurableRetractionError("atom has the wrong exact type")
            atom.__post_init__()
            if atom.sequence != index:
                raise DurableRetractionError("atom sequence must be contiguous from one")
            if atom.expected_pre_root != expected_pre:
                raise DurableRetractionError("publication atoms do not form a state chain")
            if atom.commit_id in commit_ids:
                raise DurableRetractionError("commit identities must be unique")
            if atom.nullifier_root in nullifiers:
                raise DurableRetractionError("nullifiers must be unique")
            if atom.authority_epoch_index >= len(self.authority_epochs):
                raise DurableRetractionError("publication atom names an unknown authority epoch")
            if atom.authority_epoch_index < previous_epoch:
                raise DurableRetractionError("publication authority epochs must be monotone")
            authority = self.authority_epochs[atom.authority_epoch_index]
            if atom.authority_state_root != authority.root:
                raise DurableRetractionError(
                    "publication atom is not bound to its exact authority epoch"
                )
            if atom.writer_profile_root not in authority.allowed_writer_roots:
                raise DurableRetractionError("publication atom uses a disabled writer")
            previous_epoch = atom.authority_epoch_index
            commit_ids.add(atom.commit_id)
            nullifiers.add(atom.nullifier_root)
            for effect in atom.outbox:
                if effect.effect_id in effect_ids:
                    raise DurableRetractionError("effect identities must be globally unique")
                effect_ids.add(effect.effect_id)
            expected_pre = atom.post_state_root
        if type(self.acks) is not tuple or len(self.acks) > MAX_ACKS:
            raise DurableRetractionError("acks has the wrong bounded shape")
        for ack in self.acks:
            if type(ack) is not DeliveryAckV1:
                raise DurableRetractionError("ack has the wrong exact type")
            ack.__post_init__()
        if tuple(sorted(self.acks, key=lambda item: item.effect_id)) != self.acks:
            raise DurableRetractionError("acks must be in canonical effect order")
        ack_ids = tuple(ack.effect_id for ack in self.acks)
        if len(set(ack_ids)) != len(ack_ids):
            raise DurableRetractionError("each effect may have at most one durable ack")
        effects = {effect.effect_id: effect for atom in self.atoms for effect in atom.outbox}
        for ack in self.acks:
            committed_effect = effects.get(ack.effect_id)
            if committed_effect is None:
                raise DurableRetractionError("ack has no committed outbox ancestor")
            if (
                ack.destination != committed_effect.destination
                or ack.payload_root != committed_effect.payload_root
                or ack.adapter_profile_root != committed_effect.adapter_profile_root
                or ack.idempotency_root
                != derive_destination_idempotency_root(committed_effect.effect_id)
            ):
                raise DurableRetractionError("ack is crossed with a different effect")

    @property
    def authority(self) -> AuthorityStateV1:
        return self.authority_epochs[-1]

    @property
    def current_state_root(self) -> str:
        if not self.atoms:
            return self.genesis_state_root
        return self.atoms[-1].post_state_root

    @property
    def root(self) -> str:
        fields: list[bytes] = [
            bytes.fromhex(self.genesis_state_root),
            *(bytes.fromhex(authority.root) for authority in self.authority_epochs),
        ]
        fields.extend(bytes.fromhex(atom.atom_root) for atom in self.atoms)
        for ack in self.acks:
            fields.extend(
                (
                    bytes.fromhex(ack.effect_id),
                    ack.destination.encode("utf-8"),
                    bytes.fromhex(ack.payload_root),
                    bytes.fromhex(ack.destination_receipt_root),
                    bytes.fromhex(ack.adapter_profile_root),
                    bytes.fromhex(ack.idempotency_root),
                    bytes.fromhex(ack.response_root),
                )
            )
        fields.extend(
            (
                bytes.fromhex(self.deployment_config_root),
                bytes.fromhex(self.verifier_profile_root),
            )
        )
        return _hash_fields("zenodex/fcis/dra/authorized-history/v1", tuple(fields))


@dataclass(frozen=True, slots=True)
class DurableSnapshotV1:
    genesis_state_root: str
    authority_epochs: tuple[AuthorityStateV1, ...]
    current_state_root: str
    atom_rows: tuple[PublicationAtomV1, ...]
    evidence_rows: tuple[EvidenceRowV1, ...]
    nullifier_rows: tuple[NullifierRowV1, ...]
    outbox_rows: tuple[OutboxRowV1, ...]
    ack_rows: tuple[DeliveryAckV1, ...]
    snapshot_root: str
    deployment_config_root: str = _DEFAULT_DEPLOYMENT_CONFIG_ROOT
    verifier_profile_root: str = _DEFAULT_VERIFIER_PROFILE_ROOT

    def __post_init__(self) -> None:
        _digest(self.genesis_state_root, "genesis_state_root")
        _digest(self.deployment_config_root, "deployment_config_root")
        _digest(self.verifier_profile_root, "verifier_profile_root")
        if type(self.authority_epochs) is not tuple or not self.authority_epochs:
            raise DurableRetractionError("authority_epochs must be a nonempty exact tuple")
        if len(self.authority_epochs) > MAX_AUTHORITY_EPOCHS:
            raise DurableRetractionError("authority_epochs exceeds its row bound")
        for authority in self.authority_epochs:
            if type(authority) is not AuthorityStateV1:
                raise DurableRetractionError("authority epoch has the wrong exact type")
            authority.__post_init__()
        _digest(self.current_state_root, "current_state_root")
        _digest(self.snapshot_root, "snapshot_root")
        _validate_snapshot_tables(self)


def _validate_snapshot_tables(snapshot: DurableSnapshotV1) -> None:
    tables = (
        ("atom_rows", snapshot.atom_rows, MAX_TRANSITIONS, PublicationAtomV1),
        ("evidence_rows", snapshot.evidence_rows, MAX_EVIDENCE_ROWS, EvidenceRowV1),
        (
            "nullifier_rows",
            snapshot.nullifier_rows,
            MAX_NULLIFIER_ROWS,
            NullifierRowV1,
        ),
        ("outbox_rows", snapshot.outbox_rows, MAX_OUTBOX_ROWS, OutboxRowV1),
        ("ack_rows", snapshot.ack_rows, MAX_ACKS, DeliveryAckV1),
    )
    for name, rows, maximum, row_type in tables:
        if type(rows) is not tuple:
            raise DurableRetractionError(f"{name} must be an exact tuple")
        if len(rows) > maximum:
            raise DurableRetractionError(f"{name} exceeds its row bound")
        for row in rows:
            if type(row) is not row_type:
                raise DurableRetractionError(f"{name} contains the wrong exact type")
            row.__post_init__()

    estimated_bytes = 128
    estimated_bytes += 64 * len(snapshot.authority_epochs)
    estimated_bytes += 32 * len(snapshot.atom_rows)
    estimated_bytes += sum(96 + len(row.kind.encode("utf-8")) for row in snapshot.evidence_rows)
    estimated_bytes += 96 * len(snapshot.nullifier_rows)
    estimated_bytes += sum(
        132 + len(row.destination.encode("utf-8")) for row in snapshot.outbox_rows
    )
    estimated_bytes += sum(192 + len(row.destination.encode("utf-8")) for row in snapshot.ack_rows)
    if estimated_bytes > MAX_DURABLE_CANONICAL_BYTES:
        raise DurableRetractionError("durable snapshot exceeds its total canonical-byte budget")


class ReopenCodeV1(Enum):
    WRONG_EXACT_TYPE = "wrong_exact_type"
    INVALID_ROW = "invalid_row"
    NONCANONICAL_LAYOUT = "noncanonical_layout"
    INCOMPLETE_OR_SURPLUS_EVIDENCE = "incomplete_or_surplus_evidence"
    HISTORY_INVALID = "history_invalid"
    SNAPSHOT_ROOT_MISMATCH = "snapshot_root_mismatch"
    RESOURCE_LIMIT = "resource_limit"
    UNVERIFIED_AUTHORIZATION = "unverified_authorization"
    AUTHORIZATION_EXPIRED = "authorization_expired"
    UNVERIFIED_DESTINATION_RECEIPT = "unverified_destination_receipt"


@dataclass(frozen=True, slots=True)
class ReopenRejectV1:
    code: ReopenCodeV1
    path: tuple[str, ...]


ReopenResultV1: TypeAlias = AuthorizedHistoryV1 | ReopenRejectV1


def _is_history(value: ReopenResultV1) -> TypeGuard[AuthorizedHistoryV1]:
    return type(value) is AuthorizedHistoryV1


def _evidence_rows(atoms: tuple[PublicationAtomV1, ...]) -> tuple[EvidenceRowV1, ...]:
    rows: list[EvidenceRowV1] = []
    for atom in atoms:
        for kind, value in (
            ("command", atom.command_root),
            ("response", atom.response_root),
            ("receipt", atom.receipt_root),
            ("decision", atom.decision_root),
            ("bundle", atom.bundle_root),
            ("replay", atom.replay_root),
            ("authority", atom.authority_state_root),
        ):
            rows.append(EvidenceRowV1(atom.commit_id, kind, value))
    return tuple(sorted(rows))


def _nullifier_rows(atoms: tuple[PublicationAtomV1, ...]) -> tuple[NullifierRowV1, ...]:
    return tuple(
        sorted(
            NullifierRowV1(atom.nullifier_root, atom.commit_id, atom.fingerprint) for atom in atoms
        )
    )


def _outbox_rows(atoms: tuple[PublicationAtomV1, ...]) -> tuple[OutboxRowV1, ...]:
    rows = (
        OutboxRowV1(
            effect.effect_id,
            atom.commit_id,
            effect.ordinal,
            effect.destination,
            effect.payload_root,
            effect.adapter_profile_root,
        )
        for atom in atoms
        for effect in atom.outbox
    )
    return tuple(sorted(rows))


def _snapshot_root_without_cache(snapshot: DurableSnapshotV1) -> str:
    _validate_snapshot_tables(snapshot)
    fields: list[bytes] = [
        bytes.fromhex(snapshot.genesis_state_root),
        *(bytes.fromhex(authority.root) for authority in snapshot.authority_epochs),
        bytes.fromhex(snapshot.current_state_root),
        bytes.fromhex(snapshot.deployment_config_root),
        bytes.fromhex(snapshot.verifier_profile_root),
    ]
    fields.extend(bytes.fromhex(atom.atom_root) for atom in snapshot.atom_rows)
    for evidence_row in snapshot.evidence_rows:
        fields.extend(
            (
                bytes.fromhex(evidence_row.commit_id),
                evidence_row.kind.encode("utf-8"),
                bytes.fromhex(evidence_row.value_root),
            )
        )
    for nullifier_row in snapshot.nullifier_rows:
        fields.extend(
            (
                bytes.fromhex(nullifier_row.nullifier_root),
                bytes.fromhex(nullifier_row.commit_id),
                bytes.fromhex(nullifier_row.fingerprint),
            )
        )
    for outbox_row in snapshot.outbox_rows:
        fields.extend(
            (
                bytes.fromhex(outbox_row.effect_id),
                bytes.fromhex(outbox_row.commit_id),
                outbox_row.ordinal.to_bytes(4, "big"),
                outbox_row.destination.encode("utf-8"),
                bytes.fromhex(outbox_row.payload_root),
                bytes.fromhex(outbox_row.adapter_profile_root),
            )
        )
    for ack in snapshot.ack_rows:
        fields.extend(
            (
                bytes.fromhex(ack.effect_id),
                ack.destination.encode("utf-8"),
                bytes.fromhex(ack.payload_root),
                bytes.fromhex(ack.destination_receipt_root),
                bytes.fromhex(ack.adapter_profile_root),
                bytes.fromhex(ack.idempotency_root),
                bytes.fromhex(ack.response_root),
            )
        )
    return _hash_fields("zenodex/fcis/dra/durable-snapshot/v1", tuple(fields))


def encode_history(history: AuthorizedHistoryV1) -> DurableSnapshotV1:
    if type(history) is not AuthorizedHistoryV1:
        raise DurableRetractionError("history has the wrong exact type")
    history.__post_init__()
    provisional = DurableSnapshotV1(
        genesis_state_root=history.genesis_state_root,
        authority_epochs=history.authority_epochs,
        current_state_root=history.current_state_root,
        atom_rows=history.atoms,
        evidence_rows=_evidence_rows(history.atoms),
        nullifier_rows=_nullifier_rows(history.atoms),
        outbox_rows=_outbox_rows(history.atoms),
        ack_rows=history.acks,
        snapshot_root="0" * 64,
        deployment_config_root=history.deployment_config_root,
        verifier_profile_root=history.verifier_profile_root,
    )
    return DurableSnapshotV1(
        genesis_state_root=provisional.genesis_state_root,
        authority_epochs=provisional.authority_epochs,
        current_state_root=provisional.current_state_root,
        atom_rows=provisional.atom_rows,
        evidence_rows=provisional.evidence_rows,
        nullifier_rows=provisional.nullifier_rows,
        outbox_rows=provisional.outbox_rows,
        ack_rows=provisional.ack_rows,
        snapshot_root=_snapshot_root_without_cache(provisional),
        deployment_config_root=provisional.deployment_config_root,
        verifier_profile_root=provisional.verifier_profile_root,
    )


def reopen_snapshot(snapshot: object) -> ReopenResultV1:
    if not isinstance(snapshot, DurableSnapshotV1) or type(snapshot) is not DurableSnapshotV1:
        return ReopenRejectV1(ReopenCodeV1.WRONG_EXACT_TYPE, ("snapshot",))
    exact = snapshot
    try:
        exact.__post_init__()
        for atom in exact.atom_rows:
            if type(atom) is not PublicationAtomV1:
                raise DurableRetractionError("atom row has the wrong exact type")
            atom.__post_init__()
        for evidence_row in exact.evidence_rows:
            if type(evidence_row) is not EvidenceRowV1:
                raise DurableRetractionError("evidence row has the wrong exact type")
            evidence_row.__post_init__()
        for nullifier_row in exact.nullifier_rows:
            if type(nullifier_row) is not NullifierRowV1:
                raise DurableRetractionError("nullifier row has the wrong exact type")
            nullifier_row.__post_init__()
        for outbox_row in exact.outbox_rows:
            if type(outbox_row) is not OutboxRowV1:
                raise DurableRetractionError("outbox row has the wrong exact type")
            outbox_row.__post_init__()
        for ack in exact.ack_rows:
            if type(ack) is not DeliveryAckV1:
                raise DurableRetractionError("ack row has the wrong exact type")
            ack.__post_init__()
    except (AttributeError, DurableRetractionError, TypeError, ValueError):
        return ReopenRejectV1(ReopenCodeV1.INVALID_ROW, ("snapshot",))
    try:
        recomputed_snapshot_root = _snapshot_root_without_cache(exact)
    except (OverflowError, AttributeError, DurableRetractionError, TypeError, ValueError):
        return ReopenRejectV1(ReopenCodeV1.RESOURCE_LIMIT, ("snapshot_root",))
    if recomputed_snapshot_root != exact.snapshot_root:
        return ReopenRejectV1(
            ReopenCodeV1.SNAPSHOT_ROOT_MISMATCH,
            ("snapshot_root",),
        )
    if exact.evidence_rows != _evidence_rows(exact.atom_rows):
        return ReopenRejectV1(
            ReopenCodeV1.INCOMPLETE_OR_SURPLUS_EVIDENCE,
            ("evidence_rows",),
        )
    if exact.nullifier_rows != _nullifier_rows(exact.atom_rows):
        return ReopenRejectV1(
            ReopenCodeV1.INCOMPLETE_OR_SURPLUS_EVIDENCE,
            ("nullifier_rows",),
        )
    if exact.outbox_rows != _outbox_rows(exact.atom_rows):
        return ReopenRejectV1(
            ReopenCodeV1.INCOMPLETE_OR_SURPLUS_EVIDENCE,
            ("outbox_rows",),
        )
    try:
        history = AuthorizedHistoryV1(
            genesis_state_root=exact.genesis_state_root,
            authority_epochs=exact.authority_epochs,
            atoms=exact.atom_rows,
            acks=exact.ack_rows,
            deployment_config_root=exact.deployment_config_root,
            verifier_profile_root=exact.verifier_profile_root,
        )
        history.__post_init__()
    except (AttributeError, DurableRetractionError, TypeError, ValueError):
        return ReopenRejectV1(ReopenCodeV1.HISTORY_INVALID, ("history",))
    if history.current_state_root != exact.current_state_root:
        return ReopenRejectV1(
            ReopenCodeV1.NONCANONICAL_LAYOUT,
            ("current_state_root",),
        )
    canonical = encode_history(history)
    if canonical != exact:
        return ReopenRejectV1(
            ReopenCodeV1.NONCANONICAL_LAYOUT,
            ("fixed_point",),
        )
    return history


def normalize_snapshot(snapshot: object) -> DurableSnapshotV1 | ReopenRejectV1:
    reopened = reopen_snapshot(snapshot)
    if not _is_history(reopened):
        return cast(ReopenRejectV1, reopened)
    return encode_history(reopened)


_HEAD_AUTHORIZATION_TOKEN_V1 = object()
_VERIFIED_EXTERNAL_AUTHORIZATION_TOKEN_V1 = object()


def _external_attestation_root(
    *,
    snapshot_root: str,
    current_state_root: str,
    authority_state_root: str,
    authority_epoch_index: int,
    deployment_config_root: str,
    verifier_profile_root: str,
    external_statement_root: str,
    activation_epoch: int,
    expiration_epoch: int | None,
) -> str:
    expiration = U32_MAX if expiration_epoch is None else expiration_epoch
    return _hash_fields(
        "zenodex/fcis/dra/external-head-attestation/v1",
        (
            bytes.fromhex(snapshot_root),
            bytes.fromhex(current_state_root),
            bytes.fromhex(authority_state_root),
            authority_epoch_index.to_bytes(4, "big"),
            bytes.fromhex(deployment_config_root),
            bytes.fromhex(verifier_profile_root),
            bytes.fromhex(external_statement_root),
            activation_epoch.to_bytes(4, "big"),
            expiration.to_bytes(4, "big"),
        ),
    )


def _external_evidence_root(
    *,
    attestation_root: str,
    external_statement_root: str,
    verifier_profile_root: str,
) -> str:
    return _hash_fields(
        "zenodex/fcis/dra/verified-external-head-evidence/v1",
        (
            bytes.fromhex(attestation_root),
            bytes.fromhex(external_statement_root),
            bytes.fromhex(verifier_profile_root),
        ),
    )


@dataclass(frozen=True, slots=True)
class ExternalHeadAuthorizationEvidenceV1:
    """Raw shell evidence awaiting an authoritative verifier decision."""

    snapshot_root: str
    current_state_root: str
    authority_state_root: str
    authority_epoch_index: int
    deployment_config_root: str
    verifier_profile_root: str
    external_statement_root: str
    activation_epoch: int
    expiration_epoch: int | None
    attestation_root: str

    def __post_init__(self) -> None:
        for name in (
            "snapshot_root",
            "current_state_root",
            "authority_state_root",
            "deployment_config_root",
            "verifier_profile_root",
            "external_statement_root",
            "attestation_root",
        ):
            _digest(object.__getattribute__(self, name), name)
        _exact_u32(self.authority_epoch_index, "authority_epoch_index")
        _exact_u32(self.activation_epoch, "activation_epoch")
        if self.expiration_epoch is not None:
            _exact_u32(self.expiration_epoch, "expiration_epoch")
            if self.expiration_epoch <= self.activation_epoch:
                raise DurableRetractionError("expiration_epoch must follow activation_epoch")
        expected = _external_attestation_root(
            snapshot_root=self.snapshot_root,
            current_state_root=self.current_state_root,
            authority_state_root=self.authority_state_root,
            authority_epoch_index=self.authority_epoch_index,
            deployment_config_root=self.deployment_config_root,
            verifier_profile_root=self.verifier_profile_root,
            external_statement_root=self.external_statement_root,
            activation_epoch=self.activation_epoch,
            expiration_epoch=self.expiration_epoch,
        )
        if self.attestation_root != expected:
            raise DurableRetractionError("external authorization evidence attestation mismatch")


@dataclass(frozen=True, slots=True)
class VerifiedExternalHeadAuthorizationV1:
    """Verifier-produced authority witness consumed by the deterministic core."""

    snapshot_root: str
    current_state_root: str
    authority_state_root: str
    authority_epoch_index: int
    deployment_config_root: str
    verifier_profile_root: str
    external_statement_root: str
    activation_epoch: int
    expiration_epoch: int | None
    attestation_root: str
    evidence_root: str
    _construction_token: InitVar[object]

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _VERIFIED_EXTERNAL_AUTHORIZATION_TOKEN_V1:
            raise DurableRetractionError(
                "verified external authorization requires the verifier boundary"
            )
        evidence = ExternalHeadAuthorizationEvidenceV1(
            snapshot_root=self.snapshot_root,
            current_state_root=self.current_state_root,
            authority_state_root=self.authority_state_root,
            authority_epoch_index=self.authority_epoch_index,
            deployment_config_root=self.deployment_config_root,
            verifier_profile_root=self.verifier_profile_root,
            external_statement_root=self.external_statement_root,
            activation_epoch=self.activation_epoch,
            expiration_epoch=self.expiration_epoch,
            attestation_root=self.attestation_root,
        )
        expected = _external_evidence_root(
            attestation_root=evidence.attestation_root,
            external_statement_root=evidence.external_statement_root,
            verifier_profile_root=evidence.verifier_profile_root,
        )
        if self.evidence_root != expected:
            raise DurableRetractionError("verified external evidence root mismatch")


def verify_external_head_authorization(
    evidence: object,
    *,
    expected_snapshot_root: object,
    expected_current_state_root: object,
    expected_authority_state_root: object,
    expected_authority_epoch_index: object,
    expected_deployment_config_root: object,
    expected_verifier_profile_root: object,
    current_epoch: object,
) -> VerifiedExternalHeadAuthorizationV1 | ReopenRejectV1:
    """Model the shell-owned verifier boundary; deployment trust is a nonclaim."""

    if type(evidence) is not ExternalHeadAuthorizationEvidenceV1:
        return ReopenRejectV1(ReopenCodeV1.UNVERIFIED_AUTHORIZATION, ("evidence",))
    try:
        evidence.__post_init__()
        expected_values = (
            (_digest(expected_snapshot_root, "expected_snapshot_root"), evidence.snapshot_root),
            (
                _digest(expected_current_state_root, "expected_current_state_root"),
                evidence.current_state_root,
            ),
            (
                _digest(expected_authority_state_root, "expected_authority_state_root"),
                evidence.authority_state_root,
            ),
            (
                _exact_u32(expected_authority_epoch_index, "expected_authority_epoch_index"),
                evidence.authority_epoch_index,
            ),
            (
                _digest(expected_deployment_config_root, "expected_deployment_config_root"),
                evidence.deployment_config_root,
            ),
            (
                _digest(expected_verifier_profile_root, "expected_verifier_profile_root"),
                evidence.verifier_profile_root,
            ),
        )
        if any(expected != actual for expected, actual in expected_values):
            return ReopenRejectV1(
                ReopenCodeV1.NONCANONICAL_LAYOUT,
                ("authorization", "subject"),
            )
        epoch = _exact_u32(current_epoch, "current_epoch")
        if epoch < evidence.activation_epoch or (
            evidence.expiration_epoch is not None and epoch >= evidence.expiration_epoch
        ):
            return ReopenRejectV1(
                ReopenCodeV1.AUTHORIZATION_EXPIRED,
                ("authorization", "bounds"),
            )
        evidence_root = _external_evidence_root(
            attestation_root=evidence.attestation_root,
            external_statement_root=evidence.external_statement_root,
            verifier_profile_root=evidence.verifier_profile_root,
        )
        return VerifiedExternalHeadAuthorizationV1(
            snapshot_root=evidence.snapshot_root,
            current_state_root=evidence.current_state_root,
            authority_state_root=evidence.authority_state_root,
            authority_epoch_index=evidence.authority_epoch_index,
            deployment_config_root=evidence.deployment_config_root,
            verifier_profile_root=evidence.verifier_profile_root,
            external_statement_root=evidence.external_statement_root,
            activation_epoch=evidence.activation_epoch,
            expiration_epoch=evidence.expiration_epoch,
            attestation_root=evidence.attestation_root,
            evidence_root=evidence_root,
            _construction_token=_VERIFIED_EXTERNAL_AUTHORIZATION_TOKEN_V1,
        )
    except (AttributeError, DurableRetractionError, TypeError, ValueError, OverflowError):
        return ReopenRejectV1(ReopenCodeV1.UNVERIFIED_AUTHORIZATION, ("evidence",))


def _reopen_authorization_root(
    *,
    snapshot_root: str,
    current_state_root: str,
    authority_state_root: str,
    authority_epoch_index: int,
    deployment_config_root: str,
    verifier_profile_root: str,
    external_statement_root: str,
    activation_epoch: int,
    expiration_epoch: int | None,
    evidence_root: str,
) -> str:
    expiration = U32_MAX if expiration_epoch is None else expiration_epoch
    return _hash_fields(
        "zenodex/fcis/dra/reopen-authorization/v2",
        (
            bytes.fromhex(snapshot_root),
            bytes.fromhex(current_state_root),
            bytes.fromhex(authority_state_root),
            authority_epoch_index.to_bytes(4, "big"),
            bytes.fromhex(deployment_config_root),
            bytes.fromhex(verifier_profile_root),
            bytes.fromhex(external_statement_root),
            activation_epoch.to_bytes(4, "big"),
            expiration.to_bytes(4, "big"),
            bytes.fromhex(evidence_root),
        ),
    )


@dataclass(frozen=True, slots=True)
class ReopenAuthorizationV1:
    """Fresh authorization derived only from a verifier-produced exact witness."""

    snapshot_root: str
    current_state_root: str
    authority_state_root: str
    authority_epoch_index: int
    deployment_config_root: str
    verifier_profile_root: str
    external_statement_root: str
    activation_epoch: int
    expiration_epoch: int | None
    evidence_root: str
    authorization_root: str
    _construction_token: InitVar[object]

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _HEAD_AUTHORIZATION_TOKEN_V1:
            raise DurableRetractionError(
                "reopen authorization requires a verified external witness"
            )
        self._revalidate()

    def _revalidate(self) -> None:
        for name in (
            "snapshot_root",
            "current_state_root",
            "authority_state_root",
            "deployment_config_root",
            "verifier_profile_root",
            "external_statement_root",
            "evidence_root",
            "authorization_root",
        ):
            _digest(object.__getattribute__(self, name), name)
        _exact_u32(self.authority_epoch_index, "authority_epoch_index")
        _exact_u32(self.activation_epoch, "activation_epoch")
        if self.expiration_epoch is not None:
            _exact_u32(self.expiration_epoch, "expiration_epoch")
            if self.expiration_epoch <= self.activation_epoch:
                raise DurableRetractionError("expiration_epoch must follow activation_epoch")
        expected = _reopen_authorization_root(
            snapshot_root=self.snapshot_root,
            current_state_root=self.current_state_root,
            authority_state_root=self.authority_state_root,
            authority_epoch_index=self.authority_epoch_index,
            deployment_config_root=self.deployment_config_root,
            verifier_profile_root=self.verifier_profile_root,
            external_statement_root=self.external_statement_root,
            activation_epoch=self.activation_epoch,
            expiration_epoch=self.expiration_epoch,
            evidence_root=self.evidence_root,
        )
        if self.authorization_root != expected:
            raise DurableRetractionError(
                "reopen authorization root does not match its exact subject"
            )


def authorize_reopened_snapshot(
    snapshot: object,
    *,
    verified_external_authorization: object,
) -> ReopenAuthorizationV1 | ReopenRejectV1:
    if not isinstance(snapshot, DurableSnapshotV1) or type(snapshot) is not DurableSnapshotV1:
        return ReopenRejectV1(ReopenCodeV1.WRONG_EXACT_TYPE, ("snapshot",))
    reopened = reopen_snapshot(snapshot)
    if _is_history(reopened):
        history = reopened
    else:
        return cast(ReopenRejectV1, reopened)
    exact_snapshot = snapshot
    if type(verified_external_authorization) is not VerifiedExternalHeadAuthorizationV1:
        return ReopenRejectV1(ReopenCodeV1.UNVERIFIED_AUTHORIZATION, ("authorization",))
    verified = verified_external_authorization
    try:
        verified.__post_init__(_VERIFIED_EXTERNAL_AUTHORIZATION_TOKEN_V1)
    except (AttributeError, DurableRetractionError, TypeError, ValueError, OverflowError):
        return ReopenRejectV1(ReopenCodeV1.UNVERIFIED_AUTHORIZATION, ("authorization",))
    if (
        verified.snapshot_root != exact_snapshot.snapshot_root
        or verified.current_state_root != history.current_state_root
        or verified.authority_state_root != history.authority.root
        or verified.authority_epoch_index != history.authority.epoch_index
        or verified.deployment_config_root != exact_snapshot.deployment_config_root
        or verified.verifier_profile_root != exact_snapshot.verifier_profile_root
    ):
        return ReopenRejectV1(
            ReopenCodeV1.NONCANONICAL_LAYOUT,
            ("authorization", "subject"),
        )
    current_epoch = history.authority.epoch_index
    if current_epoch < verified.activation_epoch or (
        verified.expiration_epoch is not None and current_epoch >= verified.expiration_epoch
    ):
        return ReopenRejectV1(
            ReopenCodeV1.AUTHORIZATION_EXPIRED,
            ("authorization", "bounds"),
        )
    authorization_root = _reopen_authorization_root(
        snapshot_root=verified.snapshot_root,
        current_state_root=verified.current_state_root,
        authority_state_root=verified.authority_state_root,
        authority_epoch_index=verified.authority_epoch_index,
        deployment_config_root=verified.deployment_config_root,
        verifier_profile_root=verified.verifier_profile_root,
        external_statement_root=verified.external_statement_root,
        activation_epoch=verified.activation_epoch,
        expiration_epoch=verified.expiration_epoch,
        evidence_root=verified.evidence_root,
    )
    return ReopenAuthorizationV1(
        snapshot_root=verified.snapshot_root,
        current_state_root=verified.current_state_root,
        authority_state_root=verified.authority_state_root,
        authority_epoch_index=verified.authority_epoch_index,
        deployment_config_root=verified.deployment_config_root,
        verifier_profile_root=verified.verifier_profile_root,
        external_statement_root=verified.external_statement_root,
        activation_epoch=verified.activation_epoch,
        expiration_epoch=verified.expiration_epoch,
        evidence_root=verified.evidence_root,
        authorization_root=authorization_root,
        _construction_token=_HEAD_AUTHORIZATION_TOKEN_V1,
    )


def _authorization_matches_snapshot(
    snapshot: DurableSnapshotV1,
    history: AuthorizedHistoryV1,
    authorization: object,
) -> bool:
    if type(authorization) is not ReopenAuthorizationV1:
        return False
    try:
        authorization._revalidate()
    except (AttributeError, DurableRetractionError, TypeError, ValueError, OverflowError):
        return False
    current_epoch = history.authority.epoch_index
    return (
        authorization.snapshot_root == snapshot.snapshot_root
        and authorization.current_state_root == history.current_state_root
        and authorization.authority_state_root == history.authority.root
        and authorization.authority_epoch_index == history.authority.epoch_index
        and authorization.deployment_config_root == snapshot.deployment_config_root
        and authorization.verifier_profile_root == snapshot.verifier_profile_root
        and current_epoch >= authorization.activation_epoch
        and (
            authorization.expiration_epoch is None or current_epoch < authorization.expiration_epoch
        )
    )


class CommitResolutionV1(Enum):
    """The durable store's exact resolution for one stable commit identity."""

    NEWLY_COMMITTED = "newly_committed"
    ALREADY_COMMITTED = "already_committed"
    ABSENT_RETRYABLE = "absent_retryable"
    STALE_STATE = "stale_state"
    DEFINITE_REJECTION = "definite_rejection"


class ClientObservationV1(Enum):
    """What the client learned; transport uncertainty is not a durable state."""

    CONFIRMED_NEW = "confirmed_new"
    CONFIRMED_ALREADY = "confirmed_already"
    CONFIRMED_STALE = "confirmed_stale"
    CONFIRMED_REJECTION = "confirmed_rejection"
    INDETERMINATE = "indeterminate"


class CrashPointV1(Enum):
    NONE = "none"
    BEFORE_LINEARIZATION = "before_linearization"
    AFTER_LINEARIZATION = "after_linearization"


@dataclass(frozen=True, slots=True)
class CommitAttemptV1:
    snapshot: DurableSnapshotV1
    durable_resolution: CommitResolutionV1
    client_observation: ClientObservationV1
    response_root: str | None


def classify_retry(
    history: AuthorizedHistoryV1,
    atom: PublicationAtomV1,
) -> tuple[CommitResolutionV1, str | None]:
    if type(history) is not AuthorizedHistoryV1:
        raise DurableRetractionError("history has the wrong exact type")
    if type(atom) is not PublicationAtomV1:
        raise DurableRetractionError("atom has the wrong exact type")
    history.__post_init__()
    atom.__post_init__()
    for committed in history.atoms:
        if committed.commit_id == atom.commit_id:
            if committed.fingerprint == atom.fingerprint:
                return CommitResolutionV1.ALREADY_COMMITTED, committed.response_root
            return CommitResolutionV1.DEFINITE_REJECTION, None
        if committed.nullifier_root == atom.nullifier_root:
            return CommitResolutionV1.DEFINITE_REJECTION, None
    if history.current_state_root != atom.expected_pre_root:
        return CommitResolutionV1.STALE_STATE, None
    if atom.authority_state_root != history.authority.root:
        return CommitResolutionV1.DEFINITE_REJECTION, None
    if atom.writer_profile_root not in history.authority.allowed_writer_roots:
        return CommitResolutionV1.DEFINITE_REJECTION, None
    return CommitResolutionV1.ABSENT_RETRYABLE, None


def attempt_commit(
    snapshot: DurableSnapshotV1,
    authorization: object,
    atom: PublicationAtomV1,
    crash_point: CrashPointV1 = CrashPointV1.NONE,
) -> CommitAttemptV1:
    if type(crash_point) is not CrashPointV1:
        return CommitAttemptV1(
            snapshot=snapshot,
            durable_resolution=CommitResolutionV1.DEFINITE_REJECTION,
            client_observation=ClientObservationV1.CONFIRMED_REJECTION,
            response_root=None,
        )
    reopened = reopen_snapshot(snapshot)
    if not _is_history(reopened):
        return CommitAttemptV1(
            snapshot=snapshot,
            durable_resolution=CommitResolutionV1.DEFINITE_REJECTION,
            client_observation=ClientObservationV1.CONFIRMED_REJECTION,
            response_root=None,
        )
    history = reopened
    if not _authorization_matches_snapshot(snapshot, history, authorization):
        return CommitAttemptV1(
            snapshot=snapshot,
            durable_resolution=CommitResolutionV1.DEFINITE_REJECTION,
            client_observation=ClientObservationV1.CONFIRMED_REJECTION,
            response_root=None,
        )
    resolution, response_root = classify_retry(history, atom)
    if resolution is CommitResolutionV1.ALREADY_COMMITTED:
        return CommitAttemptV1(
            snapshot,
            resolution,
            ClientObservationV1.CONFIRMED_ALREADY,
            response_root,
        )
    if resolution is CommitResolutionV1.STALE_STATE:
        return CommitAttemptV1(
            snapshot,
            resolution,
            ClientObservationV1.CONFIRMED_STALE,
            None,
        )
    if resolution is CommitResolutionV1.DEFINITE_REJECTION:
        return CommitAttemptV1(
            snapshot,
            resolution,
            ClientObservationV1.CONFIRMED_REJECTION,
            None,
        )
    if crash_point is CrashPointV1.BEFORE_LINEARIZATION:
        return CommitAttemptV1(
            snapshot=snapshot,
            durable_resolution=CommitResolutionV1.ABSENT_RETRYABLE,
            client_observation=ClientObservationV1.INDETERMINATE,
            response_root=None,
        )
    try:
        appended = AuthorizedHistoryV1(
            genesis_state_root=history.genesis_state_root,
            authority_epochs=history.authority_epochs,
            atoms=history.atoms + (atom,),
            acks=history.acks,
            deployment_config_root=history.deployment_config_root,
            verifier_profile_root=history.verifier_profile_root,
        )
        post = encode_history(appended)
    except (AttributeError, DurableRetractionError, TypeError, ValueError):
        return CommitAttemptV1(
            snapshot=snapshot,
            durable_resolution=CommitResolutionV1.DEFINITE_REJECTION,
            client_observation=ClientObservationV1.CONFIRMED_REJECTION,
            response_root=None,
        )
    observation = (
        ClientObservationV1.INDETERMINATE
        if crash_point is CrashPointV1.AFTER_LINEARIZATION
        else ClientObservationV1.CONFIRMED_NEW
    )
    return CommitAttemptV1(
        snapshot=post,
        durable_resolution=CommitResolutionV1.NEWLY_COMMITTED,
        client_observation=observation,
        response_root=(
            atom.response_root if observation is ClientObservationV1.CONFIRMED_NEW else None
        ),
    )


def derive_destination_receipt_root(
    *,
    effect_id: str,
    destination: str,
    payload_root: str,
) -> str:
    """Derive a structural response digest; this does not prove delivery."""
    _digest(effect_id, "effect_id")
    _bounded_text(destination, "destination")
    _digest(payload_root, "payload_root")
    return _hash_fields(
        "zenodex/fcis/dra/destination-receipt/v1",
        (
            bytes.fromhex(effect_id),
            destination.encode("utf-8"),
            bytes.fromhex(payload_root),
        ),
    )


def derive_destination_idempotency_root(effect_id: str) -> str:
    _digest(effect_id, "effect_id")
    return _hash_fields(
        "zenodex/fcis/dra/destination-idempotency/v1",
        (bytes.fromhex(effect_id),),
    )


def _destination_attestation_root(
    *,
    effect_id: str,
    destination: str,
    payload_root: str,
    destination_receipt_root: str,
    adapter_profile_root: str,
    idempotency_root: str,
    response_root: str,
) -> str:
    return _hash_fields(
        "zenodex/fcis/dra/destination-response-attestation/v1",
        (
            bytes.fromhex(effect_id),
            destination.encode("utf-8"),
            bytes.fromhex(payload_root),
            bytes.fromhex(destination_receipt_root),
            bytes.fromhex(adapter_profile_root),
            bytes.fromhex(idempotency_root),
            bytes.fromhex(response_root),
        ),
    )


@dataclass(frozen=True, slots=True)
class DestinationResponseEvidenceV1:
    """Raw destination response awaiting the destination verifier adapter."""

    effect_id: str
    destination: str
    payload_root: str
    destination_receipt_root: str
    adapter_profile_root: str
    idempotency_root: str
    response_root: str
    attestation_root: str

    def __post_init__(self) -> None:
        _digest(self.effect_id, "effect_id")
        _bounded_text(self.destination, "destination")
        for name in (
            "payload_root",
            "destination_receipt_root",
            "adapter_profile_root",
            "idempotency_root",
            "response_root",
            "attestation_root",
        ):
            _digest(object.__getattribute__(self, name), name)
        expected = _destination_attestation_root(
            effect_id=self.effect_id,
            destination=self.destination,
            payload_root=self.payload_root,
            destination_receipt_root=self.destination_receipt_root,
            adapter_profile_root=self.adapter_profile_root,
            idempotency_root=self.idempotency_root,
            response_root=self.response_root,
        )
        if self.attestation_root != expected:
            raise DurableRetractionError("destination response attestation mismatch")


_VERIFIED_DESTINATION_RECEIPT_TOKEN_V1 = object()


def _verified_destination_evidence_root(
    *,
    attestation_root: str,
    adapter_profile_root: str,
    idempotency_root: str,
) -> str:
    return _hash_fields(
        "zenodex/fcis/dra/verified-destination-receipt/v1",
        (
            bytes.fromhex(attestation_root),
            bytes.fromhex(adapter_profile_root),
            bytes.fromhex(idempotency_root),
        ),
    )


@dataclass(frozen=True, slots=True)
class VerifiedDestinationReceiptV1:
    """Adapter-produced receipt consumed by durable acknowledgment."""

    effect_id: str
    destination: str
    payload_root: str
    destination_receipt_root: str
    adapter_profile_root: str
    idempotency_root: str
    response_root: str
    attestation_root: str
    evidence_root: str
    _construction_token: InitVar[object]

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _VERIFIED_DESTINATION_RECEIPT_TOKEN_V1:
            raise DurableRetractionError("destination receipt requires a verifier adapter")
        self._revalidate()

    def _revalidate(self) -> None:
        evidence = DestinationResponseEvidenceV1(
            effect_id=self.effect_id,
            destination=self.destination,
            payload_root=self.payload_root,
            destination_receipt_root=self.destination_receipt_root,
            adapter_profile_root=self.adapter_profile_root,
            idempotency_root=self.idempotency_root,
            response_root=self.response_root,
            attestation_root=self.attestation_root,
        )
        expected = _verified_destination_evidence_root(
            attestation_root=evidence.attestation_root,
            adapter_profile_root=evidence.adapter_profile_root,
            idempotency_root=evidence.idempotency_root,
        )
        if self.evidence_root != expected:
            raise DurableRetractionError("verified destination evidence root mismatch")


def verify_destination_response(
    response: object,
    *,
    expected_effect: OutboxEffectV1,
    expected_adapter_profile_root: object,
    expected_idempotency_root: object,
) -> VerifiedDestinationReceiptV1 | ReopenRejectV1:
    """Model a destination-specific verifier; delivery deployment is a nonclaim."""

    if type(response) is not DestinationResponseEvidenceV1:
        return ReopenRejectV1(
            ReopenCodeV1.UNVERIFIED_DESTINATION_RECEIPT,
            ("destination_response",),
        )
    try:
        response.__post_init__()
        if type(expected_effect) is not OutboxEffectV1:
            return ReopenRejectV1(
                ReopenCodeV1.UNVERIFIED_DESTINATION_RECEIPT,
                ("effect",),
            )
        expected_effect.__post_init__()
        adapter_profile_root = _digest(
            expected_adapter_profile_root,
            "expected_adapter_profile_root",
        )
        idempotency_root = _digest(
            expected_idempotency_root,
            "expected_idempotency_root",
        )
        if (
            response.effect_id != expected_effect.effect_id
            or response.destination != expected_effect.destination
            or response.payload_root != expected_effect.payload_root
            or response.adapter_profile_root != expected_effect.adapter_profile_root
            or response.adapter_profile_root != adapter_profile_root
            or response.idempotency_root != idempotency_root
            or response.idempotency_root
            != derive_destination_idempotency_root(expected_effect.effect_id)
            or response.destination_receipt_root
            != derive_destination_receipt_root(
                effect_id=expected_effect.effect_id,
                destination=expected_effect.destination,
                payload_root=expected_effect.payload_root,
            )
        ):
            return ReopenRejectV1(
                ReopenCodeV1.UNVERIFIED_DESTINATION_RECEIPT,
                ("destination_response", "binding"),
            )
        evidence_root = _verified_destination_evidence_root(
            attestation_root=response.attestation_root,
            adapter_profile_root=response.adapter_profile_root,
            idempotency_root=response.idempotency_root,
        )
        return VerifiedDestinationReceiptV1(
            effect_id=response.effect_id,
            destination=response.destination,
            payload_root=response.payload_root,
            destination_receipt_root=response.destination_receipt_root,
            adapter_profile_root=response.adapter_profile_root,
            idempotency_root=response.idempotency_root,
            response_root=response.response_root,
            attestation_root=response.attestation_root,
            evidence_root=evidence_root,
            _construction_token=_VERIFIED_DESTINATION_RECEIPT_TOKEN_V1,
        )
    except (AttributeError, DurableRetractionError, TypeError, ValueError, OverflowError):
        return ReopenRejectV1(
            ReopenCodeV1.UNVERIFIED_DESTINATION_RECEIPT,
            ("destination_response",),
        )


@dataclass(frozen=True, slots=True, order=True)
class DestinationReceiptV1:
    effect_id: str
    destination: str
    payload_root: str
    receipt_root: str

    def __post_init__(self) -> None:
        _digest(self.effect_id, "effect_id")
        _bounded_text(self.destination, "destination")
        _digest(self.payload_root, "payload_root")
        _digest(self.receipt_root, "receipt_root")
        expected = derive_destination_receipt_root(
            effect_id=self.effect_id,
            destination=self.destination,
            payload_root=self.payload_root,
        )
        if self.receipt_root != expected:
            raise DurableRetractionError(
                "destination receipt root is not bound to the exact effect"
            )


@dataclass(frozen=True, slots=True)
class DestinationStateV1:
    receipts: tuple[VerifiedDestinationReceiptV1, ...]

    def __post_init__(self) -> None:
        if type(self.receipts) is not tuple:
            raise DurableRetractionError("receipts must be an exact tuple")
        if len(self.receipts) > MAX_DESTINATION_RECEIPTS:
            raise DurableRetractionError("destination receipts exceed their row bound")
        for receipt in self.receipts:
            if type(receipt) is not VerifiedDestinationReceiptV1:
                raise DurableRetractionError("receipt has the wrong exact type")
            receipt._revalidate()
        if tuple(sorted(self.receipts, key=lambda item: item.effect_id)) != self.receipts:
            raise DurableRetractionError("destination receipts must be canonical")
        ids = tuple(receipt.effect_id for receipt in self.receipts)
        if len(set(ids)) != len(ids):
            raise DurableRetractionError("destination effect identities must be unique")


class DeliveryClassV1(Enum):
    ACCEPTED_NEW = "accepted_new"
    ALREADY_ACCEPTED = "already_accepted"
    NOT_COMMITTED = "not_committed"
    PAYLOAD_COLLISION = "payload_collision"
    INDETERMINATE_AFTER_ACCEPT = "indeterminate_after_accept"
    VERIFIER_REJECTED = "verifier_rejected"


@dataclass(frozen=True, slots=True)
class DeliveryAttemptV1:
    destination_state: DestinationStateV1
    delivery_class: DeliveryClassV1
    receipt: VerifiedDestinationReceiptV1 | None


def _find_effect(history: AuthorizedHistoryV1, effect_id: str) -> OutboxEffectV1 | None:
    for atom in history.atoms:
        for effect in atom.outbox:
            if effect.effect_id == effect_id:
                return effect
    return None


def deliver_effect(
    snapshot: DurableSnapshotV1,
    destination_state: DestinationStateV1,
    effect_id: str,
    *,
    lose_ack: bool = False,
) -> DeliveryAttemptV1:
    _digest(effect_id, "effect_id")
    reopened = reopen_snapshot(snapshot)
    if not _is_history(reopened):
        return DeliveryAttemptV1(
            destination_state,
            DeliveryClassV1.NOT_COMMITTED,
            None,
        )
    history = reopened
    effect = _find_effect(history, effect_id)
    if effect is None:
        return DeliveryAttemptV1(
            destination_state,
            DeliveryClassV1.NOT_COMMITTED,
            None,
        )
    destination_state.__post_init__()
    for existing in destination_state.receipts:
        if existing.effect_id != effect.effect_id:
            continue
        if (
            existing.destination == effect.destination
            and existing.payload_root == effect.payload_root
            and existing.adapter_profile_root == effect.adapter_profile_root
            and existing.idempotency_root == derive_destination_idempotency_root(effect.effect_id)
        ):
            return DeliveryAttemptV1(
                destination_state,
                DeliveryClassV1.ALREADY_ACCEPTED,
                existing,
            )
        return DeliveryAttemptV1(
            destination_state,
            DeliveryClassV1.PAYLOAD_COLLISION,
            None,
        )
    idempotency_root = derive_destination_idempotency_root(effect.effect_id)
    destination_receipt_root = derive_destination_receipt_root(
        effect_id=effect.effect_id,
        destination=effect.destination,
        payload_root=effect.payload_root,
    )
    response_root = tagged_digest(f"destination-response/{effect.effect_id}")
    raw_response = DestinationResponseEvidenceV1(
        effect_id=effect.effect_id,
        destination=effect.destination,
        payload_root=effect.payload_root,
        destination_receipt_root=destination_receipt_root,
        adapter_profile_root=effect.adapter_profile_root,
        idempotency_root=idempotency_root,
        response_root=response_root,
        attestation_root=_destination_attestation_root(
            effect_id=effect.effect_id,
            destination=effect.destination,
            payload_root=effect.payload_root,
            destination_receipt_root=destination_receipt_root,
            adapter_profile_root=effect.adapter_profile_root,
            idempotency_root=idempotency_root,
            response_root=response_root,
        ),
    )
    verified = verify_destination_response(
        raw_response,
        expected_effect=effect,
        expected_adapter_profile_root=effect.adapter_profile_root,
        expected_idempotency_root=idempotency_root,
    )
    if type(verified) is not VerifiedDestinationReceiptV1:
        return DeliveryAttemptV1(
            destination_state,
            DeliveryClassV1.VERIFIER_REJECTED,
            None,
        )
    receipt = verified
    next_state = DestinationStateV1(
        tuple(sorted(destination_state.receipts + (receipt,), key=lambda item: item.effect_id))
    )
    delivery_class = (
        DeliveryClassV1.INDETERMINATE_AFTER_ACCEPT if lose_ack else DeliveryClassV1.ACCEPTED_NEW
    )
    return DeliveryAttemptV1(next_state, delivery_class, receipt)


def acknowledge_delivery(
    snapshot: DurableSnapshotV1,
    authorization: object,
    receipt: object,
) -> DurableSnapshotV1 | ReopenRejectV1:
    reopened = reopen_snapshot(snapshot)
    if _is_history(reopened):
        history = reopened
    else:
        return cast(ReopenRejectV1, reopened)
    if not _authorization_matches_snapshot(snapshot, history, authorization):
        return ReopenRejectV1(
            ReopenCodeV1.NONCANONICAL_LAYOUT,
            ("authorization",),
        )
    if type(receipt) is not VerifiedDestinationReceiptV1:
        return ReopenRejectV1(
            ReopenCodeV1.UNVERIFIED_DESTINATION_RECEIPT,
            ("receipt",),
        )
    try:
        receipt._revalidate()
    except (AttributeError, DurableRetractionError, TypeError, ValueError, OverflowError):
        return ReopenRejectV1(
            ReopenCodeV1.UNVERIFIED_DESTINATION_RECEIPT,
            ("receipt",),
        )
    effect = _find_effect(history, receipt.effect_id)
    if effect is None:
        return ReopenRejectV1(
            ReopenCodeV1.INCOMPLETE_OR_SURPLUS_EVIDENCE,
            ("receipt", "effect_id"),
        )
    if (
        receipt.destination != effect.destination
        or receipt.payload_root != effect.payload_root
        or receipt.adapter_profile_root != effect.adapter_profile_root
        or receipt.idempotency_root != derive_destination_idempotency_root(effect.effect_id)
    ):
        return ReopenRejectV1(
            ReopenCodeV1.INCOMPLETE_OR_SURPLUS_EVIDENCE,
            ("receipt", "crossed"),
        )
    ack = DeliveryAckV1(
        effect_id=receipt.effect_id,
        destination=receipt.destination,
        payload_root=receipt.payload_root,
        destination_receipt_root=receipt.destination_receipt_root,
        adapter_profile_root=receipt.adapter_profile_root,
        idempotency_root=receipt.idempotency_root,
        response_root=receipt.response_root,
    )
    existing = {item.effect_id: item for item in history.acks}
    old = existing.get(ack.effect_id)
    if old is not None:
        if old == ack:
            return snapshot
        return ReopenRejectV1(
            ReopenCodeV1.INCOMPLETE_OR_SURPLUS_EVIDENCE,
            ("ack", "collision"),
        )
    next_history = AuthorizedHistoryV1(
        genesis_state_root=history.genesis_state_root,
        authority_epochs=history.authority_epochs,
        atoms=history.atoms,
        acks=tuple(sorted(history.acks + (ack,), key=lambda item: item.effect_id)),
        deployment_config_root=history.deployment_config_root,
        verifier_profile_root=history.verifier_profile_root,
    )
    return encode_history(next_history)


def migrate_snapshot(
    snapshot: DurableSnapshotV1,
    authorization: object,
    next_phase: MigrationPhaseV1,
    transport_root: str,
) -> DurableSnapshotV1 | ReopenRejectV1:
    reopened = reopen_snapshot(snapshot)
    if _is_history(reopened):
        history = reopened
    else:
        return cast(ReopenRejectV1, reopened)
    if not _authorization_matches_snapshot(snapshot, history, authorization):
        return ReopenRejectV1(
            ReopenCodeV1.NONCANONICAL_LAYOUT,
            ("authorization",),
        )
    try:
        next_authority = advance_authority_state(
            history.authority,
            next_phase,
            transport_root,
        )
        # Existing atoms are historical facts and keep their contemporaneous
        # authority roots.  A profile transition is represented in the durable
        # header only in this bounded model.  The production model must add an
        # explicit authority-history event before mounting.
        migrated = AuthorizedHistoryV1(
            genesis_state_root=history.genesis_state_root,
            authority_epochs=history.authority_epochs + (next_authority,),
            atoms=history.atoms,
            acks=history.acks,
            deployment_config_root=history.deployment_config_root,
            verifier_profile_root=history.verifier_profile_root,
        )
        return encode_history(migrated)
    except (AttributeError, DurableRetractionError, TypeError, ValueError):
        return ReopenRejectV1(ReopenCodeV1.HISTORY_INVALID, ("migration",))


__all__ = (
    "AuthorityStateV1",
    "AuthorizedHistoryV1",
    "ClientObservationV1",
    "CommitAttemptV1",
    "CommitResolutionV1",
    "CrashPointV1",
    "DeliveryAckV1",
    "DeliveryAttemptV1",
    "DeliveryClassV1",
    "DestinationReceiptV1",
    "DestinationResponseEvidenceV1",
    "DestinationStateV1",
    "DurableRetractionError",
    "DurableSnapshotV1",
    "EvidenceRowV1",
    "ExternalHeadAuthorizationEvidenceV1",
    "MigrationPhaseV1",
    "NullifierRowV1",
    "OutboxEffectV1",
    "OutboxRowV1",
    "PublicationAtomV1",
    "ReopenAuthorizationV1",
    "ReopenCodeV1",
    "ReopenRejectV1",
    "VerifiedDestinationReceiptV1",
    "VerifiedExternalHeadAuthorizationV1",
    "acknowledge_delivery",
    "advance_authority_state",
    "authorize_reopened_snapshot",
    "attempt_commit",
    "classify_retry",
    "deliver_effect",
    "derive_destination_idempotency_root",
    "derive_destination_receipt_root",
    "derive_effect_id",
    "encode_history",
    "initial_authority_state",
    "migrate_snapshot",
    "normalize_snapshot",
    "outbox_root",
    "reopen_snapshot",
    "tagged_digest",
    "verify_destination_response",
    "verify_external_head_authorization",
)
