"""Typed, authority-neutral records for the experimental Spot V7 atomic store.

The cell hashing functions intentionally mirror
``spot_settlement_v7_effect_binding_shared``.  The retained vector establishes
agreement for that exact bounded case only.  Receipt verification and a
governed Firecracker execution capability remain external obligations.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from enum import Enum
from typing import Final

MAX_U64: Final = (1 << 64) - 1
MAX_U128: Final = (1 << 128) - 1
MAX_SPOT_V7_SETTLEMENT_REVISIONS_V1: Final = 1_048_576

SPOT_V7_ATOMIC_SETTLEMENT_AUTHORITY_BLOCKED_REASON_V1: Final = (
    "governed_firecracker_runner_to_atomic_store_binder_not_implemented"
)

_CELL_KEY_DOMAIN_V1 = b"zenodex.zrpf.spot_typed_cell_key.v1"
_CELL_VALUE_DOMAIN_V1 = b"zenodex.zrpf.spot_typed_cell_value.v1"
_CELL_CHANGE_DOMAIN_V1 = b"zenodex.zrpf.spot_typed_cell_change.v1"
_CELL_CHANGES_ROOT_DOMAIN_V1 = b"zenodex.zrpf.spot_typed_cell_changes_root.v1"
_STORAGE_EFFECT_ID_DOMAIN_V1 = b"zenodex.zrpf.spot_v7_atomic_storage_effect.v1"


class SpotV7AtomicSettlementStoreErrorV1(RuntimeError):
    """Stable fail-closed store error."""

    def __init__(self, code: str, detail: str) -> None:
        super().__init__(f"{code}: {detail}")
        self.code = code
        self.detail = detail


class SpotV7CellKindV1(Enum):
    """The two economic cell kinds admitted by restricted ordinary Spot V7."""

    ACCOUNT_BALANCE = 1
    POOL_RESERVE = 2


class SpotV7CellRoleV1(Enum):
    """Direction of one cell transition."""

    DEBIT = 1
    CREDIT = 2


@dataclass(frozen=True, slots=True)
class SpotV7CellOpeningV1:
    """Canonical opening for one account balance or pool reserve in atoms."""

    kind: SpotV7CellKindV1
    subject_id: str
    asset_id: str
    atoms: int

    def __post_init__(self) -> None:
        if type(self.kind) is not SpotV7CellKindV1:
            raise TypeError("cell kind must be SpotV7CellKindV1")
        expected_subject_bytes = (
            48 if self.kind is SpotV7CellKindV1.ACCOUNT_BALANCE else 32
        )
        _identifier_bytes(
            self.subject_id,
            name="cell subject_id",
            length=expected_subject_bytes,
        )
        _hash_bytes(self.asset_id, name="cell asset_id")
        _require_uint(self.atoms, name="cell atoms", maximum=MAX_U128)

    @property
    def cell_key(self) -> str:
        body = b"".join(
            (
                bytes((self.kind.value,)),
                _identifier_bytes(
                    self.subject_id,
                    name="cell subject_id",
                    length=(
                        48 if self.kind is SpotV7CellKindV1.ACCOUNT_BALANCE else 32
                    ),
                ),
                _hash_bytes(self.asset_id, name="cell asset_id"),
            )
        )
        return _domain_hash(_CELL_KEY_DOMAIN_V1, body)

    @property
    def value_hash(self) -> str:
        body = _hash_bytes(self.cell_key, name="cell key") + self.atoms.to_bytes(16, "big")
        return _domain_hash(_CELL_VALUE_DOMAIN_V1, body)


@dataclass(frozen=True, slots=True)
class SpotV7CellTransitionV1:
    """One nonzero, direction-checked Spot V7 cell update."""

    role: SpotV7CellRoleV1
    pre: SpotV7CellOpeningV1
    post: SpotV7CellOpeningV1

    def __post_init__(self) -> None:
        if type(self.role) is not SpotV7CellRoleV1:
            raise TypeError("cell transition role must be SpotV7CellRoleV1")
        if type(self.pre) is not SpotV7CellOpeningV1 or type(self.post) is not SpotV7CellOpeningV1:
            raise TypeError("cell transition openings must be exact SpotV7CellOpeningV1 values")
        identities = (
            self.pre.kind == self.post.kind,
            self.pre.subject_id == self.post.subject_id,
            self.pre.asset_id == self.post.asset_id,
            self.pre.cell_key == self.post.cell_key,
        )
        if not all(identities):
            raise ValueError("cell transition identity changed")
        if self.role is SpotV7CellRoleV1.DEBIT:
            amount = self.pre.atoms - self.post.atoms
        else:
            amount = self.post.atoms - self.pre.atoms
        if amount <= 0:
            raise ValueError("cell transition direction or amount is invalid")

    @property
    def cell_key(self) -> str:
        return self.pre.cell_key

    @property
    def amount_atoms(self) -> int:
        if self.role is SpotV7CellRoleV1.DEBIT:
            return self.pre.atoms - self.post.atoms
        return self.post.atoms - self.pre.atoms

    @property
    def commitment(self) -> str:
        body = b"".join(
            (
                bytes((self.pre.kind.value, self.role.value)),
                _hash_bytes(self.cell_key, name="cell transition key"),
                _hash_bytes(self.pre.asset_id, name="cell transition asset"),
                _hash_bytes(self.pre.value_hash, name="cell transition pre value"),
                _hash_bytes(self.post.value_hash, name="cell transition post value"),
                self.amount_atoms.to_bytes(16, "big"),
            )
        )
        return _domain_hash(_CELL_CHANGE_DOMAIN_V1, body)


@dataclass(frozen=True, slots=True)
class SpotV7AssetEffectV1:
    """One ordinary conserved asset effect applied by the local store."""

    economic_action_id: str
    asset_id: str
    amount_atoms: int

    def __post_init__(self) -> None:
        _hash_bytes(self.economic_action_id, name="asset effect economic_action_id")
        _hash_bytes(self.asset_id, name="asset effect asset_id")
        _require_uint(
            self.amount_atoms,
            name="asset effect amount_atoms",
            maximum=MAX_U128,
            minimum=1,
        )

    @property
    def debit_atoms(self) -> int:
        return self.amount_atoms

    @property
    def credit_atoms(self) -> int:
        return self.amount_atoms

    @property
    def effect_id(self) -> str:
        """Local audit identity derived from output-bound action, asset, and amount."""

        body = b"".join(
            (
                _hash_bytes(self.economic_action_id, name="asset effect action"),
                _hash_bytes(self.asset_id, name="asset effect asset"),
                self.amount_atoms.to_bytes(16, "big"),
            )
        )
        return _domain_hash(_STORAGE_EFFECT_ID_DOMAIN_V1, body)


def spot_v7_cell_transitions_root_v1(
    transitions: tuple[SpotV7CellTransitionV1, ...],
) -> str:
    """Derive the exact Rust V7 cell-transition root from canonical rows."""

    if type(transitions) is not tuple or not transitions:
        raise ValueError("cell transitions must be a nonempty tuple")
    if any(type(row) is not SpotV7CellTransitionV1 for row in transitions):
        raise TypeError("cell transitions must contain exact SpotV7CellTransitionV1 values")
    keys = tuple(row.cell_key for row in transitions)
    if keys != tuple(sorted(keys)) or len(set(keys)) != len(keys):
        raise ValueError("cell transitions must be strictly ordered by unique cell key")
    body = len(transitions).to_bytes(4, "big") + b"".join(
        _hash_bytes(row.commitment, name="cell transition commitment") for row in transitions
    )
    return _domain_hash(_CELL_CHANGES_ROOT_DOMAIN_V1, body)


@dataclass(frozen=True, slots=True)
class SpotV7AtomicSettlementStoreIdentityV1:
    """Governed identity expected by one scoped experimental store."""

    application_id: str
    chain_or_domain_id: str
    verified_program_id: str
    verified_profile_id: str
    verified_program_manifest_root: str
    genesis_state_root: str

    def __post_init__(self) -> None:
        for name in (
            "application_id",
            "chain_or_domain_id",
            "verified_program_id",
            "verified_profile_id",
            "verified_program_manifest_root",
            "genesis_state_root",
        ):
            _hash_bytes(getattr(self, name), name=f"store identity {name}")


@dataclass(frozen=True, slots=True)
class SpotV7AtomicSettlementCursorV1:
    """Compare-and-swap cursor over root and economic cell state."""

    revision: int
    state_root: str
    settlement_count: int
    cell_count: int
    last_epoch_id: int | None

    def __post_init__(self) -> None:
        _require_uint(
            self.revision,
            name="cursor revision",
            maximum=MAX_SPOT_V7_SETTLEMENT_REVISIONS_V1,
        )
        _hash_bytes(self.state_root, name="cursor state_root")
        _require_uint(
            self.settlement_count,
            name="cursor settlement_count",
            maximum=MAX_SPOT_V7_SETTLEMENT_REVISIONS_V1,
        )
        _require_uint(self.cell_count, name="cursor cell_count", maximum=1_048_576)
        if self.revision != self.settlement_count:
            raise ValueError("cursor revision and settlement_count must match")
        if self.last_epoch_id is None:
            if self.revision != 0:
                raise ValueError("non-genesis cursor requires last_epoch_id")
        else:
            _require_uint(self.last_epoch_id, name="cursor last_epoch_id", maximum=MAX_U64)
            if self.revision == 0:
                raise ValueError("genesis cursor cannot carry last_epoch_id")


class SpotV7AtomicSettlementRejectReasonV1(Enum):
    """Stable rejection reasons evaluated while holding the SQLite write lock."""

    CURSOR_MISMATCH = "spot_v7.atomic_settlement.cursor_mismatch"
    STORE_IDENTITY_MISMATCH = "spot_v7.atomic_settlement.store_identity_mismatch"
    PRE_STATE_ROOT_MISMATCH = "spot_v7.atomic_settlement.pre_state_root_mismatch"
    EPOCH_NOT_MONOTONIC = "spot_v7.atomic_settlement.epoch_not_monotonic"
    CELL_PRE_STATE_MISMATCH = "spot_v7.atomic_settlement.cell_pre_state_mismatch"
    DUPLICATE_RECEIPT = "spot_v7.atomic_settlement.duplicate_receipt"
    DUPLICATE_JOURNAL = "spot_v7.atomic_settlement.duplicate_journal"
    DUPLICATE_FIRECRACKER_EXECUTION = "spot_v7.atomic_settlement.duplicate_firecracker_execution"
    DUPLICATE_FIRECRACKER_OUTPUT = "spot_v7.atomic_settlement.duplicate_firecracker_output"
    DUPLICATE_SETTLEMENT_PLAN = "spot_v7.atomic_settlement.duplicate_settlement_plan"
    DUPLICATE_SOURCE_CHILD = "spot_v7.atomic_settlement.duplicate_source_child"
    DUPLICATE_POST_STATE_ROOT = "spot_v7.atomic_settlement.duplicate_post_state_root"
    DUPLICATE_ECONOMIC_ACTION = "spot_v7.atomic_settlement.duplicate_economic_action"
    DUPLICATE_AUTHORIZATION_NULLIFIER = (
        "spot_v7.atomic_settlement.duplicate_authorization_nullifier"
    )
    DUPLICATE_AUTHORIZATION_GRANT_SPEND = (
        "spot_v7.atomic_settlement.duplicate_authorization_grant_spend"
    )
    DUPLICATE_CONSUMED_OBJECT = "spot_v7.atomic_settlement.duplicate_consumed_object"
    OPERATIONAL_POLICY_REQUIRED = "spot_v7.atomic_settlement.operational_policy_required"
    OPERATIONAL_POLICY_NOT_CONFIGURED = (
        "spot_v7.atomic_settlement.operational_policy_not_configured"
    )
    FINALITY_CURSOR_MISMATCH = "spot_v7.atomic_settlement.finality_cursor_mismatch"
    DUPLICATE_DA_CERTIFICATE = "spot_v7.atomic_settlement.duplicate_da_certificate"
    DUPLICATE_FINALITY_CERTIFICATE = (
        "spot_v7.atomic_settlement.duplicate_finality_certificate"
    )
    DUPLICATE_APPLICATION_CHECKPOINT = (
        "spot_v7.atomic_settlement.duplicate_application_checkpoint"
    )


class SpotV7AtomicSettlementDispositionV1(Enum):
    """Transaction disposition with authority status encoded in its spelling."""

    COMMITTED = "committed_test_only_authority_false"
    IDEMPOTENT_REPLAY = "idempotent_replay_test_only_authority_false"
    REJECTED = "rejected"


@dataclass(frozen=True, slots=True)
class DurableSpotV7AtomicSettlementReceiptV1:
    """Persisted exact identity packet for one test-only settlement commit."""

    settlement_commitment: str
    settlement_revision: int
    epoch_id: int
    previous_state_root: str
    result_state_root: str
    receipt_sha256: str
    journal_sha256: str
    firecracker_execution_record_sha256: str
    firecracker_output_sha256: str
    settlement_effect_plan_commitment: str
    economic_action_id: str
    authorization_nullifier: str
    authorization_grant_spend_nullifier: str
    settlement_authority: bool
    production_authority: bool
    firecracker_execution_verified: bool
    authority_blocked_reason: str

    def __post_init__(self) -> None:
        for name in (
            "settlement_commitment",
            "previous_state_root",
            "result_state_root",
            "receipt_sha256",
            "journal_sha256",
            "firecracker_execution_record_sha256",
            "firecracker_output_sha256",
            "settlement_effect_plan_commitment",
            "economic_action_id",
            "authorization_nullifier",
            "authorization_grant_spend_nullifier",
        ):
            _hash_bytes(getattr(self, name), name=f"settlement receipt {name}")
        _require_uint(
            self.settlement_revision,
            name="settlement receipt revision",
            maximum=MAX_SPOT_V7_SETTLEMENT_REVISIONS_V1,
            minimum=1,
        )
        _require_uint(self.epoch_id, name="settlement receipt epoch_id", maximum=MAX_U64)
        if any(
            value is not False
            for value in (
                self.settlement_authority,
                self.production_authority,
                self.firecracker_execution_verified,
            )
        ):
            raise ValueError("test-only settlement receipt authority flags must remain false")
        if self.authority_blocked_reason != (
            SPOT_V7_ATOMIC_SETTLEMENT_AUTHORITY_BLOCKED_REASON_V1
        ):
            raise ValueError("settlement receipt authority blocked reason mismatch")


@dataclass(frozen=True, slots=True)
class SpotV7AtomicSettlementResultV1:
    """Data-only result from the serializable test-only transaction boundary."""

    disposition: SpotV7AtomicSettlementDispositionV1
    head_cursor: SpotV7AtomicSettlementCursorV1
    receipt: DurableSpotV7AtomicSettlementReceiptV1 | None
    reject_reason: SpotV7AtomicSettlementRejectReasonV1 | None

    def __post_init__(self) -> None:
        if type(self.disposition) is not SpotV7AtomicSettlementDispositionV1:
            raise TypeError("settlement result disposition must be exact enum")
        if type(self.head_cursor) is not SpotV7AtomicSettlementCursorV1:
            raise TypeError("settlement result cursor must be exact cursor")
        if self.disposition is SpotV7AtomicSettlementDispositionV1.REJECTED:
            if self.receipt is not None or type(self.reject_reason) is not SpotV7AtomicSettlementRejectReasonV1:
                raise ValueError("rejected settlement requires one reason and no receipt")
            return
        if type(self.receipt) is not DurableSpotV7AtomicSettlementReceiptV1:
            raise ValueError("accepted settlement requires an exact stored receipt")
        if self.reject_reason is not None:
            raise ValueError("accepted settlement cannot include a reject reason")

    @property
    def committed(self) -> bool:
        return self.disposition is SpotV7AtomicSettlementDispositionV1.COMMITTED

    @property
    def idempotent_replay(self) -> bool:
        return self.disposition is SpotV7AtomicSettlementDispositionV1.IDEMPOTENT_REPLAY

    @property
    def settlement_authority(self) -> bool:
        return False

    @property
    def production_authority(self) -> bool:
        return False


def _require_uint(value: int, *, name: str, maximum: int, minimum: int = 0) -> int:
    if type(value) is not int or value < minimum or value > maximum:
        raise ValueError(f"{name} must be an integer in {minimum}..{maximum}")
    return value


def _identifier_bytes(value: str, *, name: str, length: int) -> bytes:
    if type(value) is not str or len(value) != 2 + 2 * length or not value.startswith("0x"):
        raise ValueError(f"{name} must be canonical {length}-byte lowercase hex")
    bare = value[2:]
    if any(character not in "0123456789abcdef" for character in bare):
        raise ValueError(f"{name} must be canonical {length}-byte lowercase hex")
    result = bytes.fromhex(bare)
    if not any(result):
        raise ValueError(f"{name} must be nonzero")
    return result


def _hash_bytes(value: str, *, name: str) -> bytes:
    return _identifier_bytes(value, name=name, length=32)


def _root_bytes_allow_zero(value: str, *, name: str) -> bytes:
    """Decode one exact canonical root whose all-zero sentinel is meaningful."""

    if type(value) is not str or len(value) != 66 or not value.startswith("0x"):
        raise ValueError(f"{name} must be canonical 32-byte lowercase hex")
    bare = value[2:]
    if any(character not in "0123456789abcdef" for character in bare):
        raise ValueError(f"{name} must be canonical 32-byte lowercase hex")
    return bytes.fromhex(bare)


def _hex_hash(value: bytes) -> str:
    if type(value) is not bytes or len(value) != 32:
        raise ValueError("hash bytes must be exactly 32 bytes")
    return "0x" + value.hex()


def _domain_hash(domain: bytes, body: bytes) -> str:
    if len(domain) > 0xFFFF:
        raise ValueError("hash domain is too long")
    return _hex_hash(hashlib.sha256(len(domain).to_bytes(2, "big") + domain + body).digest())


def _sha256_prefixed(value: bytes) -> str:
    if type(value) is not bytes:
        raise TypeError("hashed value must be exact bytes")
    return _hex_hash(hashlib.sha256(value).digest())
