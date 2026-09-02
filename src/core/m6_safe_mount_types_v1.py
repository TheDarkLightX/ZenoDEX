"""Typed M6 safe-mount contract and canonical evidence values.

This module is the Python reference projection for the M6 launch constitution.
It deliberately contains values only: no filesystem, clock, network, process
global, or datastore access is allowed here.  The integration shell consumes
the candidate produced by :mod:`m6_safe_mount_transition_v1` through one
commit port.

The types are research-grade executable contracts.  They do not claim that the
existing production build has been mounted, that a RISC0 receipt was verified,
or that the full M6 readiness predicate holds.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass, field
from enum import Enum
from typing import Final, Mapping, TypeAlias, TypeGuard, cast

from ..state.canonical import canonical_hex_fixed_allow_0x, canonical_json_bytes

SCHEMA_V1: Final = "zenodex/m6-safe-mount/v1"
DURABILITY_PROFILE_SCHEMA_V1: Final = "zenodex/m6-durability-profile/v1"
ZRPF_PROFILE_V1: Final = "zenodex/m6-zrpf/1.0"
ZRPF_RECEIPT_RECORD_SCHEMA_V1: Final = "zenodex/m6-zrpf-verification-receipt-record/v1"
FINALITY_RECEIPT_RECORD_SCHEMA_V1: Final = "zenodex/m6-finality-verification-receipt-record/v1"
DIRECT_PROFILE_V1: Final = "zenodex/m6-direct/1.0"
MAX_TOKEN_BYTES: Final = 128
MAX_ARGUMENTS: Final = 32
MAX_HISTORY_LENGTH: Final = 1_048_576
MAX_DURABILITY_PROFILE_JSON_BYTES_V1: Final = 1 << 30
MAX_DURABILITY_PROFILE_CHAIN_BLOCKS_V1: Final = MAX_HISTORY_LENGTH
DEFAULT_DURABILITY_JSON_BYTES_V1: Final = 256 * 1024 * 1024
MAX_ECONOMIC_ATOMS: Final = 1_048_576
MAX_OUTBOX_ROWS: Final = 1_048_576
MAX_ATOMS_V1: Final = (1 << 128) - 1
ZRPF_LEAF_COUNT_V1: Final = 64
ZRPF_COMMANDS_PER_LEAF_V1: Final = 16
ZRPF_COMMAND_COUNT_V1: Final = ZRPF_LEAF_COUNT_V1 * ZRPF_COMMANDS_PER_LEAF_V1
ZRPF_AGGREGATE_COUNT_V1: Final = 8
ZRPF_LEAVES_PER_AGGREGATE_V1: Final = 8
ZERO_ROOT_V1: Final = "0x" + "00" * 32
ZERO_IMAGE_ID_V1: Final = "0x" + "00" * 32
SEALED_BID_PRICE_SCALE_E8_V1: Final = 100_000_000
MAX_SEALED_BID_PRICE_E8_V1: Final = (1 << 63) - 1
MAX_PRICE_E8_V1: Final = (1 << 63) - 1


def _is_int(value: object) -> TypeGuard[int]:
    return type(value) is int


def _require_nonnegative_int(value: object, *, name: str) -> int:
    if not _is_int(value) or value < 0:
        raise ValueError(f"{name} must be a non-negative integer")
    return value


def _require_positive_int(value: object, *, name: str) -> int:
    result = _require_nonnegative_int(value, name=name)
    if result == 0:
        raise ValueError(f"{name} must be positive")
    return result


def _require_token(value: object, *, name: str, allow_empty: bool = False) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a string")
    if not allow_empty and not value:
        raise ValueError(f"{name} must not be empty")
    if len(value.encode("utf-8")) > MAX_TOKEN_BYTES:
        raise ValueError(f"{name} exceeds {MAX_TOKEN_BYTES} UTF-8 bytes")
    if any(ord(char) < 0x21 or ord(char) > 0x7E for char in value):
        raise ValueError(f"{name} must use printable ASCII")
    return value


def _require_root(value: object, *, name: str, allow_zero: bool = False) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a string")
    canonical = canonical_hex_fixed_allow_0x(value, nbytes=32, name=name)
    if value != canonical:
        raise ValueError(f"{name} must be canonical lowercase 0x-prefixed hex")
    if not allow_zero and canonical == ZERO_ROOT_V1:
        raise ValueError(f"{name} must be nonzero")
    return canonical


def _require_image_id(value: object, *, name: str) -> str:
    return _require_root(value, name=name, allow_zero=False)


def _ordered_unique(values: object, *, name: str, max_items: int) -> tuple[str, ...]:
    if not isinstance(values, tuple):
        raise TypeError(f"{name} must be a tuple")
    if len(values) > max_items:
        raise ValueError(f"{name} exceeds {max_items} entries")
    normalized = tuple(_require_token(item, name=f"{name}[{index}]") for index, item in enumerate(values))
    if normalized != tuple(sorted(set(normalized))):
        raise ValueError(f"{name} must be sorted and unique")
    return normalized


def _ordered_tokens(values: object, *, name: str, max_items: int) -> tuple[str, ...]:
    """Validate a sequence whose order is semantic while forbidding duplicates."""

    if not isinstance(values, tuple):
        raise TypeError(f"{name} must be a tuple")
    if len(values) > max_items:
        raise ValueError(f"{name} exceeds {max_items} entries")
    normalized = tuple(_require_token(item, name=f"{name}[{index}]") for index, item in enumerate(values))
    if len(set(normalized)) != len(normalized):
        raise ValueError(f"{name} must be unique")
    return normalized


def _canonical_value(value: object) -> object:
    if isinstance(value, Enum):
        return value.value
    if hasattr(value, "to_canonical"):
        return _canonical_value(value.to_canonical())
    if isinstance(value, tuple):
        return [_canonical_value(item) for item in value]
    if isinstance(value, list):
        return [_canonical_value(item) for item in value]
    if isinstance(value, Mapping):
        return {
            str(key): _canonical_value(item)
            for key, item in sorted(value.items(), key=lambda pair: str(pair[0]))
        }
    return value


def canonical_bytes_v1(value: object) -> bytes:
    """Return the versioned canonical JSON bytes for a typed value."""

    return canonical_json_bytes(_canonical_value(value))


def hash_v1(domain: str, value: object) -> str:
    """Hash a canonical value with an ASCII domain separator."""

    _require_token(domain, name="hash domain")
    digest = hashlib.sha256()
    domain_bytes = domain.encode("ascii")
    digest.update(len(domain_bytes).to_bytes(2, "big"))
    digest.update(domain_bytes)
    digest.update(canonical_bytes_v1(value))
    return "0x" + digest.hexdigest()


def m6_chain_id_root_from_external_v1(external_chain_id: str) -> str:
    """Map a textual Tau/ZenoLedger chain id to the M6 root representation."""

    canonical = _require_token(external_chain_id, name="external chain id")
    return hash_v1("m6-chain-identity-v1", {"external_chain_id": canonical})


def ordered_root_v1(domain: str, values: tuple[object, ...]) -> str:
    return hash_v1(domain, {"schema": SCHEMA_V1, "values": values})


def append_root_v1(domain: str, previous_root: str | None, value: object) -> str:
    """Commit an append-only sequence without rescanning its prefix."""

    previous = previous_root or hash_v1(f"{domain}-genesis", {"schema": SCHEMA_V1, "values": ()})
    _require_root(previous, name=f"{domain} previous root")
    return hash_v1(f"{domain}-append", {"previous_root": previous, "value": value})


def _fold_root_v1(domain: str, values: tuple[object, ...]) -> str:
    root: str | None = None
    for value in values:
        root = append_root_v1(domain, root, value)
    return root or hash_v1(f"{domain}-genesis", {"schema": SCHEMA_V1, "values": ()})


class GlobalCommandKindV1(str, Enum):
    """Closed launch-profile command registry."""

    SPOT_SWAP = "spot_swap"
    LP_ADD = "lp_add"
    LP_REMOVE = "lp_remove"
    ZUSD_BORROW = "zusd_borrow"
    ZUSD_REPAY = "zusd_repay"
    ZUSD_REDEEM = "zusd_redeem"
    ZUSD_LIQUIDATE = "zusd_liquidate"
    STABILITY_POOL_DEPOSIT = "stability_pool_deposit"
    STABILITY_POOL_WITHDRAW = "stability_pool_withdraw"
    ZUSD_REDISTRIBUTE = "zusd_redistribute"
    PERP_OPEN = "perp_open"
    PERP_CLOSE = "perp_close"
    PERP_FUNDING = "perp_funding"
    PERP_LIQUIDATE = "perp_liquidate"
    ORACLE_SUBMIT = "oracle_submit"
    ORACLE_DISPUTE = "oracle_dispute"
    PROTOCOL_BUY_AND_BURN = "protocol_buy_and_burn"
    ZRPF_PROVER_REWARD = "zrpf_prover_reward"
    SELLER_AUCTION_COMMIT = "seller_auction_commit"
    SELLER_AUCTION_REVEAL = "seller_auction_reveal"
    SELLER_AUCTION_SETTLE = "seller_auction_settle"
    SELLER_AUCTION_CANCEL = "seller_auction_cancel"
    SELLER_AUCTION_EXPIRE = "seller_auction_expire"
    PRIVATE_SWAP_COMMIT = "private_swap_commit"
    PRIVATE_SWAP_REVEAL = "private_swap_reveal"
    PRIVATE_SWAP_SETTLE = "private_swap_settle"
    PRIVATE_SWAP_CANCEL = "private_swap_cancel"
    PRIVATE_SWAP_EXPIRE = "private_swap_expire"
    TAU_ESCROW_DEPOSIT = "tau_escrow_deposit"
    TAU_WITHDRAWAL = "tau_withdrawal"
    TAU_WITHDRAWAL_ACK = "tau_withdrawal_ack"
    FALLBACK_ACTIVATE = "fallback_activate"
    TAU_REJOIN = "tau_rejoin"


LAUNCH_COMMANDS_V1: Final = frozenset(GlobalCommandKindV1)

# This reference profile distinguishes the closed command vocabulary from
# the subset whose business semantics are currently enabled.  The transition
# still admits every well-formed registry command so an authenticated command
# can consume its ingress nonce and record a typed committed failure.  These
# constants are research metadata, not a production policy authority; a
# mounted deployment must bind its enabled set to a promotion subject/profile.
M6_RESEARCH_DISABLED_COMMANDS_V1: Final = frozenset(
    {
        # These handlers currently lack a subject-bound policy or authority
        # witness for the value they would select.  They remain in the closed
        # command registry so authenticated attempts consume a nonce as a
        # committed business failure, while the reference profile cannot
        # mistake partial semantics for mounted authority.
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
M6_RESEARCH_ENABLED_COMMANDS_V1: Final = LAUNCH_COMMANDS_V1 - M6_RESEARCH_DISABLED_COMMANDS_V1


class BusinessStatusV1(str, Enum):
    ACCEPTED = "accepted"
    REJECTED_COMMITTED = "rejected_committed"


class AdmissionRejectReasonV1(str, Enum):
    MALFORMED_COMMAND = "malformed_command"
    UNAUTHENTICATED_CONTEXT = "unauthenticated_context"
    STATE_CAPACITY_EXCEEDED = "state_capacity_exceeded"
    CONTEXT_DEPLOYMENT_MISMATCH = "context_deployment_mismatch"
    CONTEXT_CHAIN_ID_MISMATCH = "context_chain_id_mismatch"
    CONTEXT_PARENT_HEAD_MISMATCH = "context_parent_head_mismatch"
    CONTEXT_EPOCH_MISMATCH = "context_epoch_mismatch"
    CONTEXT_TAU_PROFILE_MISMATCH = "context_tau_profile_mismatch"
    CONTEXT_VERIFIER_MISMATCH = "context_verifier_mismatch"
    SENDER_MISMATCH = "sender_mismatch"
    NONCE_MISMATCH = "nonce_mismatch"
    UNSUPPORTED_COMMAND = "unsupported_command"
    STALE_ORACLE_CONTEXT = "stale_oracle_context"
    STALE_TAU_CONTEXT = "stale_tau_context"
    STALE_COMMAND_CONTEXT = "stale_command_context"
    INVALID_FINALITY = "invalid_finality"
    INVALID_ZRPF_ROOT = "invalid_zrpf_root"


class BusinessRejectReasonV1(str, Enum):
    INVALID_AMOUNT = "invalid_amount"
    INSUFFICIENT_BALANCE = "insufficient_balance"
    INSUFFICIENT_RESERVE = "insufficient_reserve"
    INVALID_ASSET = "invalid_asset"
    INVALID_PRICE = "invalid_price"
    INVALID_DEADLINE = "invalid_deadline"
    INVALID_COMMITMENT = "invalid_commitment"
    INVALID_ESCROW = "invalid_escrow"
    INVALID_WITHDRAWAL = "invalid_withdrawal"
    INVALID_PHASE = "invalid_phase"
    INVALID_AUTHORITY = "invalid_authority"
    UNSUPPORTED_OPERATION = "unsupported_operation"


class EconomicAtomKindV1(str, Enum):
    BALANCE = "balance"
    SUPPLY = "supply"
    DEBT = "debt"
    LP_SHARE = "lp_share"
    STABILITY_POOL_SHARE = "stability_pool_share"
    MARGIN = "margin"
    POSITION = "position"
    POSITION_ENTRY_PRICE = "position_entry_price"
    ORACLE_PRICE = "oracle_price"
    INSURANCE = "insurance"
    REWARD = "reward"
    ORACLE_BOND = "oracle_bond"
    ESCROW = "escrow"
    REFUND = "refund"
    SLASH = "slash"
    PROTOCOL_RESERVE = "protocol_reserve"
    ROUNDING_BUCKET = "rounding_bucket"
    WITHDRAWAL_LIABILITY = "withdrawal_liability"


class ValueDeltaClassV1(str, Enum):
    INTERNAL_TRANSFER = "internal_transfer"
    MINT = "mint"
    BURN = "burn"
    LIABILITY = "liability"
    EXTERNAL_IN = "external_in"
    EXTERNAL_OUT = "external_out"
    NOOP = "noop"
    REFUND = "refund"
    SLASH = "slash"


class TauWithdrawalStatusV1(str, Enum):
    PENDING = "pending"
    ACKNOWLEDGED = "acknowledged"
    CANCELLED = "cancelled"


class MigrationPhaseV1(str, Enum):
    NORMAL = "normal"
    FALLBACK = "fallback"
    REJOINING = "rejoining"
    QUIESCENT = "quiescent"


class MigrationEvidenceKindV1(str, Enum):
    FALLBACK_LIVENESS = "fallback_liveness"
    TAU_REJOIN_CATCHUP = "tau_rejoin_catchup"


class FinalityModeV1(str, Enum):
    TAU_ORDERED = "tau_ordered"
    FALLBACK_FORCED_INCLUSION = "fallback_forced_inclusion"


class SellerAuctionPhaseV1(str, Enum):
    COMMIT = "commit"
    REVEAL = "reveal"
    SETTLE = "settle"
    CANCELLED = "cancelled"
    EXPIRED = "expired"


class PrivateSwapPhaseV1(str, Enum):
    COMMIT = "commit"
    REVEAL = "reveal"
    SETTLE = "settle"
    CANCELLED = "cancelled"
    EXPIRED = "expired"


@dataclass(frozen=True, slots=True)
class DestinationAdapterRootV1:
    adapter: str
    root: str

    def __post_init__(self) -> None:
        _require_token(self.adapter, name="destination adapter")
        _require_root(self.root, name="destination adapter root")

    def to_canonical(self) -> dict[str, object]:
        return {"adapter": self.adapter, "root": self.root}


@dataclass(frozen=True, slots=True)
class AssetPolicyV1:
    asset: str
    issue_authority: str
    burn_authority: str
    custody_domain: str
    terminal_drain: str

    def __post_init__(self) -> None:
        for field_name, value in (
            ("asset", self.asset),
            ("issue_authority", self.issue_authority),
            ("burn_authority", self.burn_authority),
            ("custody_domain", self.custody_domain),
            ("terminal_drain", self.terminal_drain),
        ):
            _require_token(value, name=f"asset policy {field_name}")

    def to_canonical(self) -> dict[str, str]:
        return {
            "asset": self.asset,
            "issue_authority": self.issue_authority,
            "burn_authority": self.burn_authority,
            "custody_domain": self.custody_domain,
            "terminal_drain": self.terminal_drain,
        }


@dataclass(frozen=True, slots=True)
class FreshnessBoundsV1:
    max_oracle_age_blocks: int
    max_tau_age_blocks: int
    max_command_age_blocks: int

    def __post_init__(self) -> None:
        for field_name, value in (
            ("max_oracle_age_blocks", self.max_oracle_age_blocks),
            ("max_tau_age_blocks", self.max_tau_age_blocks),
            ("max_command_age_blocks", self.max_command_age_blocks),
        ):
            _require_nonnegative_int(value, name=field_name)

    def to_canonical(self) -> dict[str, int]:
        return {
            "max_oracle_age_blocks": self.max_oracle_age_blocks,
            "max_tau_age_blocks": self.max_tau_age_blocks,
            "max_command_age_blocks": self.max_command_age_blocks,
        }


@dataclass(frozen=True, slots=True)
class OracleContextV1:
    context_root: str
    observed_height: int
    oracle_height: int

    def __post_init__(self) -> None:
        _require_root(self.context_root, name="oracle context root")
        _require_nonnegative_int(self.observed_height, name="oracle observed height")
        _require_nonnegative_int(self.oracle_height, name="oracle height")
        if self.oracle_height > self.observed_height:
            raise ValueError("oracle height cannot be ahead of observed height")

    def to_canonical(self) -> dict[str, object]:
        return {
            "context_root": self.context_root,
            "observed_height": self.observed_height,
            "oracle_height": self.oracle_height,
        }


@dataclass(frozen=True, slots=True)
class M6DurabilityProfileV1:
    """Subject-bound limits for the research durable adapter."""

    max_json_bytes: int
    max_chain_blocks: int

    def __post_init__(self) -> None:
        max_json_bytes = _require_positive_int(self.max_json_bytes, name="durability max JSON bytes")
        if max_json_bytes > MAX_DURABILITY_PROFILE_JSON_BYTES_V1:
            raise ValueError("durability max JSON bytes exceeds the profile ceiling")
        max_chain_blocks = _require_positive_int(
            self.max_chain_blocks,
            name="durability max chain blocks",
        )
        if max_chain_blocks > MAX_DURABILITY_PROFILE_CHAIN_BLOCKS_V1:
            raise ValueError("durability max chain blocks exceeds the profile ceiling")

    @property
    def profile_root(self) -> str:
        return hash_v1("m6-durability-profile-v1", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": DURABILITY_PROFILE_SCHEMA_V1,
            "max_json_bytes": self.max_json_bytes,
            "max_chain_blocks": self.max_chain_blocks,
        }


DEFAULT_DURABILITY_PROFILE_V1 = M6DurabilityProfileV1(
    max_json_bytes=DEFAULT_DURABILITY_JSON_BYTES_V1,
    max_chain_blocks=MAX_DURABILITY_PROFILE_CHAIN_BLOCKS_V1,
)


@dataclass(frozen=True, slots=True)
class M6PromotionSubjectV1:
    """One exact source/build/deployment subject for promotion evidence."""

    source: str
    proof: str
    build: str
    schema: str
    deployment: str
    chain_id: str
    verifier: str
    tau_profile: str
    validator_set: str
    writer_epoch: int
    managed_asset_policy: str
    risc0_image: str
    destination_adapter_roots: tuple[DestinationAdapterRootV1, ...]
    durability_profile: M6DurabilityProfileV1 = DEFAULT_DURABILITY_PROFILE_V1

    def __post_init__(self) -> None:
        for field_name in (
            "source",
            "proof",
            "build",
            "schema",
            "deployment",
            "chain_id",
            "verifier",
            "tau_profile",
            "validator_set",
            "managed_asset_policy",
        ):
            _require_root(getattr(self, field_name), name=f"promotion {field_name}")
        _require_nonnegative_int(self.writer_epoch, name="promotion writer epoch")
        _require_image_id(self.risc0_image, name="promotion RISC0 image")
        if not isinstance(self.durability_profile, M6DurabilityProfileV1):
            raise TypeError("durability_profile must be M6DurabilityProfileV1")
        if not isinstance(self.destination_adapter_roots, tuple):
            raise TypeError("destination_adapter_roots must be a tuple")
        adapters = tuple(self.destination_adapter_roots)
        if any(not isinstance(item, DestinationAdapterRootV1) for item in adapters):
            raise TypeError("destination_adapter_roots contains an invalid value")
        names = tuple(item.adapter for item in adapters)
        if names != tuple(sorted(set(names))):
            raise ValueError("destination adapter roots must be sorted and unique")

    @property
    def subject_root(self) -> str:
        return hash_v1("m6-promotion-subject-v1", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": SCHEMA_V1,
            "source": self.source,
            "proof": self.proof,
            "build": self.build,
            "schema_root": self.schema,
            "deployment": self.deployment,
            "chain_id": self.chain_id,
            "verifier": self.verifier,
            "tau_profile": self.tau_profile,
            "validator_set": self.validator_set,
            "writer_epoch": self.writer_epoch,
            "managed_asset_policy": self.managed_asset_policy,
            "risc0_image": self.risc0_image,
            "destination_adapter_roots": self.destination_adapter_roots,
            "durability_profile": self.durability_profile,
        }


_M6_VERIFIER_APPROVAL_SEAL = object()


class _M6VerifierApproval:
    """Initialized marker issued by a verifier port.

    Python does not provide process isolation for a same-process caller, so
    this marker is not a cryptographic authority.  The seal does close the
    accidental ``object.__new__`` bypass: an uninitialized instance cannot
    enter either opaque witness constructor.
    """

    __slots__ = ("_seal",)

    def __init__(self) -> None:
        raise TypeError("M6 verifier approval is issued by the verifier port")

    def _is_sealed(self) -> bool:
        return getattr(self, "_seal", None) is _M6_VERIFIER_APPROVAL_SEAL


def _is_verifier_approval(value: object) -> bool:
    return type(value) is _M6VerifierApproval and value._is_sealed()


class _M6ExecutionContextWitness:
    """Private binding witness issued only after an ingress verifier approves."""

    _context_root: str
    _sealed: bool
    __slots__ = ("_approval", "_context_root", "_sealed")

    def __init__(self, approval: object, context_root: str) -> None:
        if not _is_verifier_approval(approval):
            raise TypeError("M6 execution context witness requires a sealed verifier approval")
        _require_root(context_root, name="M6 execution context witness root")
        object.__setattr__(self, "_approval", approval)
        object.__setattr__(self, "_context_root", context_root)
        object.__setattr__(self, "_sealed", True)

    @property
    def context_root(self) -> str:
        return self._context_root

    def __setattr__(self, name: str, value: object) -> None:
        if getattr(self, "_sealed", False):
            raise AttributeError("M6 execution context witness is immutable")
        object.__setattr__(self, name, value)


@dataclass(frozen=True, slots=True)
class M6ExecutionContextClaimsV1:
    """Typed, unauthenticated claims presented to the ingress verifier."""

    deployment: str
    chain_id: str
    parent_head: str
    epoch: int
    sender: str
    nonce: int
    oracle_context: OracleContextV1
    tau_profile: str
    verifier_registry: str
    freshness_bounds: FreshnessBoundsV1
    ledger_height: int = 0
    authority_evidence: M6AuthorityEvidenceV1 | None = None

    def __post_init__(self) -> None:
        _require_root(self.deployment, name="claims deployment")
        _require_root(self.chain_id, name="claims chain id")
        _require_root(self.parent_head, name="claims parent head", allow_zero=True)
        _require_nonnegative_int(self.epoch, name="claims epoch")
        _require_token(self.sender, name="claims sender")
        _require_positive_int(self.nonce, name="claims nonce")
        if not isinstance(self.oracle_context, OracleContextV1):
            raise TypeError("claims oracle_context must be OracleContextV1")
        _require_root(self.tau_profile, name="claims Tau profile")
        _require_root(self.verifier_registry, name="claims verifier registry")
        if not isinstance(self.freshness_bounds, FreshnessBoundsV1):
            raise TypeError("claims freshness_bounds must be FreshnessBoundsV1")
        _require_nonnegative_int(self.ledger_height, name="claims ledger height")
        if self.authority_evidence is not None and not isinstance(
            self.authority_evidence,
            M6AuthorityEvidenceV1,
        ):
            raise TypeError("claims authority_evidence must be verifier-created")

    @property
    def authentication_root(self) -> str:
        return hash_v1("m6-authenticated-execution-context-v1", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            "deployment": self.deployment,
            "chain_id": self.chain_id,
            "parent_head": self.parent_head,
            "epoch": self.epoch,
            "sender": self.sender,
            "nonce": self.nonce,
            "oracle_context": self.oracle_context,
            "tau_profile": self.tau_profile,
            "verifier_registry": self.verifier_registry,
            "freshness_bounds": self.freshness_bounds,
            "ledger_height": self.ledger_height,
            "authority_evidence": self.authority_evidence,
        }


@dataclass(frozen=True, slots=True)
class AuthenticatedExecutionContextV1:
    """Verifier-produced consensus context supplied to the pure transition.

    The public dataclass shape is convenient for canonical projection, while
    the private witness prevents a caller from constructing an apparently
    authenticated context directly.  The witness is bound to every canonical
    context field and is issued by the ingress verifier port.
    """

    deployment: str
    chain_id: str
    parent_head: str
    epoch: int
    sender: str
    nonce: int
    oracle_context: OracleContextV1
    tau_profile: str
    verifier_registry: str
    freshness_bounds: FreshnessBoundsV1
    ledger_height: int = 0
    authority_evidence: M6AuthorityEvidenceV1 | None = None
    _verification_witness: _M6ExecutionContextWitness | None = field(default=None, repr=False, compare=False)

    @classmethod
    def _from_verifier(
        cls,
        *,
        claims: M6ExecutionContextClaimsV1,
        verification_approval: object,
    ) -> AuthenticatedExecutionContextV1:
        if not isinstance(claims, M6ExecutionContextClaimsV1):
            raise TypeError("authenticated context claims are not typed")
        canonical = claims.to_canonical()
        witness = _M6ExecutionContextWitness(
            verification_approval,
            hash_v1("m6-authenticated-execution-context-v1", canonical),
        )
        return cls(
            deployment=claims.deployment,
            chain_id=claims.chain_id,
            parent_head=claims.parent_head,
            epoch=claims.epoch,
            sender=claims.sender,
            nonce=claims.nonce,
            oracle_context=claims.oracle_context,
            tau_profile=claims.tau_profile,
            verifier_registry=claims.verifier_registry,
            freshness_bounds=claims.freshness_bounds,
            ledger_height=claims.ledger_height,
            authority_evidence=claims.authority_evidence,
            _verification_witness=witness,
        )

    def __post_init__(self) -> None:
        _require_root(self.deployment, name="context deployment")
        _require_root(self.chain_id, name="context chain id")
        _require_root(self.parent_head, name="context parent head", allow_zero=True)
        _require_nonnegative_int(self.epoch, name="context epoch")
        _require_token(self.sender, name="context sender")
        _require_positive_int(self.nonce, name="context nonce")
        if not isinstance(self.oracle_context, OracleContextV1):
            raise TypeError("context oracle_context must be OracleContextV1")
        _require_root(self.tau_profile, name="context Tau profile")
        _require_root(self.verifier_registry, name="context verifier registry")
        if not isinstance(self.freshness_bounds, FreshnessBoundsV1):
            raise TypeError("context freshness_bounds must be FreshnessBoundsV1")
        _require_nonnegative_int(self.ledger_height, name="context ledger height")
        if self.authority_evidence is not None and not isinstance(
            self.authority_evidence,
            M6AuthorityEvidenceV1,
        ):
            raise TypeError("context authority_evidence must be verifier-created")
        if not isinstance(self._verification_witness, _M6ExecutionContextWitness):
            raise TypeError("AuthenticatedExecutionContextV1 is verifier-created")
        if self._verification_witness.context_root != self.authentication_root:
            raise ValueError("authenticated execution context witness binding mismatch")

    @property
    def authentication_root(self) -> str:
        return hash_v1("m6-authenticated-execution-context-v1", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            "deployment": self.deployment,
            "chain_id": self.chain_id,
            "parent_head": self.parent_head,
            "epoch": self.epoch,
            "sender": self.sender,
            "nonce": self.nonce,
            "oracle_context": self.oracle_context,
            "tau_profile": self.tau_profile,
            "verifier_registry": self.verifier_registry,
            "freshness_bounds": self.freshness_bounds,
            "ledger_height": self.ledger_height,
            "authority_evidence": self.authority_evidence,
        }


@dataclass(frozen=True, slots=True, order=True)
class NonceAtomV1:
    sender: str
    last_nonce: int

    def __post_init__(self) -> None:
        _require_token(self.sender, name="nonce sender")
        _require_nonnegative_int(self.last_nonce, name="last nonce")

    def to_canonical(self) -> dict[str, object]:
        return {"sender": self.sender, "last_nonce": self.last_nonce}


@dataclass(frozen=True, slots=True)
class EconomicAtomV1:
    """One positive amount in a logical M6 ledger allocation.

    ``custody`` is retained as the V1 constructor and canonical-wire field so
    existing state roots and reopen records remain reproducible.  Its semantic
    meaning in this model is a ``ledger_allocation``: an internal accounting
    partition such as ``ledger``, ``liability``, or ``stability_pool``.  It
    does not assert legal custody, beneficial ownership, or an escrow role.
    New callers should use :meth:`from_ledger_allocation` and
    :attr:`ledger_allocation`.
    """

    kind: EconomicAtomKindV1
    owner: str
    asset: str
    custody: str
    amount_atoms: int

    def __post_init__(self) -> None:
        if not isinstance(self.kind, EconomicAtomKindV1):
            raise TypeError("economic atom kind is not closed")
        _require_token(self.owner, name="economic atom owner")
        _require_token(self.asset, name="economic atom asset")
        _require_token(self.custody, name="economic atom custody")
        _require_positive_int(self.amount_atoms, name="economic atom amount")
        if self.amount_atoms > MAX_ATOMS_V1:
            raise ValueError("economic atom amount exceeds 128-bit atom domain")

    @classmethod
    def from_ledger_allocation(
        cls,
        *,
        kind: EconomicAtomKindV1,
        owner: str,
        asset: str,
        ledger_allocation: str,
        amount_atoms: int,
    ) -> "EconomicAtomV1":
        """Construct an atom with the legal-neutral internal term."""

        return cls(
            kind=kind,
            owner=owner,
            asset=asset,
            custody=ledger_allocation,
            amount_atoms=amount_atoms,
        )

    @property
    def ledger_allocation(self) -> str:
        """Return this atom's internal accounting partition.

        This is the normative API term.  ``custody`` remains only for V1
        wire compatibility and should not be read as a legal classification.
        """

        return self.custody

    @property
    def key(self) -> tuple[str, str, str, str]:
        return (self.kind.value, self.owner, self.asset, self.custody)

    def to_canonical(self) -> dict[str, object]:
        return {
            "kind": self.kind,
            "owner": self.owner,
            "asset": self.asset,
            # V1 wire compatibility.  See ``ledger_allocation`` above.
            "custody": self.custody,
            "amount_atoms": self.amount_atoms,
        }


@dataclass(frozen=True, slots=True)
class EscrowAtomV1:
    escrow_id: str
    owner: str
    asset: str
    amount_atoms: int
    terminal_state: str

    def __post_init__(self) -> None:
        for field_name, value in (
            ("escrow_id", self.escrow_id),
            ("owner", self.owner),
            ("asset", self.asset),
            ("terminal_state", self.terminal_state),
        ):
            _require_token(value, name=f"escrow {field_name}")
        _require_nonnegative_int(self.amount_atoms, name="escrow amount")

    def to_canonical(self) -> dict[str, object]:
        return {
            "escrow_id": self.escrow_id,
            "owner": self.owner,
            "asset": self.asset,
            "amount_atoms": self.amount_atoms,
            "terminal_state": self.terminal_state,
        }


@dataclass(frozen=True, slots=True)
class SellerAuctionBidStateV1:
    """One bidder's durable state in a bounded seller-inventory auction.

    The record is participant-scoped so multiple commitments for one auction
    cannot alias one escrow.  A terminal row remains in state with a zero
    escrow amount and its settlement metadata, which makes refunds, slashes,
    and replay audits explicit.
    """

    auction_id: str
    bidder: str
    escrow_id: str
    bond_asset: str
    bond_atoms: int
    commitment: str
    commit_height: int
    reveal_deadline_height: int
    settle_deadline_height: int
    inventory_asset: str | None = None
    quantity_atoms: int | None = None
    price_e8: int | None = None
    reveal_nonce: int | None = None
    filled_quantity_atoms: int = 0
    paid_atoms: int = 0
    rounding_remainder_e8: int = 0
    phase: SellerAuctionPhaseV1 = SellerAuctionPhaseV1.COMMIT

    def __post_init__(self) -> None:
        for field_name, value in (
            ("auction id", self.auction_id),
            ("bidder", self.bidder),
            ("escrow id", self.escrow_id),
            ("bond asset", self.bond_asset),
        ):
            _require_token(value, name=f"seller auction state {field_name}")
        _require_root(self.commitment, name="seller auction state commitment")
        _require_positive_int(self.bond_atoms, name="seller auction state bond")
        numeric_fields: tuple[tuple[str, int], ...] = (
            ("commit height", self.commit_height),
            ("reveal deadline height", self.reveal_deadline_height),
            ("settle deadline height", self.settle_deadline_height),
        )
        for numeric_name, numeric_value in numeric_fields:
            _require_nonnegative_int(numeric_value, name=f"seller auction state {numeric_name}")
        if not self.commit_height < self.reveal_deadline_height < self.settle_deadline_height:
            raise ValueError("seller auction state deadline order is invalid")
        if not isinstance(self.phase, SellerAuctionPhaseV1):
            raise TypeError("seller auction state phase is not closed")
        _require_nonnegative_int(self.filled_quantity_atoms, name="seller auction filled quantity")
        _require_nonnegative_int(self.paid_atoms, name="seller auction paid atoms")
        _require_nonnegative_int(self.rounding_remainder_e8, name="seller auction rounding remainder")
        reveal_values = (
            self.inventory_asset,
            self.quantity_atoms,
            self.price_e8,
            self.reveal_nonce,
        )
        has_reveal = all(value is not None for value in reveal_values)
        has_no_reveal = all(value is None for value in reveal_values)
        if not (has_reveal or has_no_reveal):
            raise ValueError("seller auction reveal fields must be all present or all absent")
        if has_reveal:
            _require_token(self.inventory_asset, name="seller auction inventory asset")
            _require_positive_int(self.quantity_atoms, name="seller auction quantity")
            price_e8 = _require_positive_int(self.price_e8, name="seller auction price")
            if price_e8 > MAX_SEALED_BID_PRICE_E8_V1:
                raise ValueError("seller auction price exceeds bounded range")
            _require_positive_int(self.reveal_nonce, name="seller auction reveal nonce")
        if self.rounding_remainder_e8 >= SEALED_BID_PRICE_SCALE_E8_V1:
            raise ValueError("seller auction rounding remainder exceeds one atom scale")
        if self.phase in (SellerAuctionPhaseV1.COMMIT, SellerAuctionPhaseV1.CANCELLED) and not has_no_reveal:
            raise ValueError("seller auction phase cannot retain reveal data")
        if self.phase in (SellerAuctionPhaseV1.REVEAL, SellerAuctionPhaseV1.SETTLE) and not has_reveal:
            raise ValueError("seller auction phase requires reveal data")
        if self.phase is not SellerAuctionPhaseV1.SETTLE and (
            self.filled_quantity_atoms or self.paid_atoms or self.rounding_remainder_e8
        ):
            raise ValueError("seller auction settlement amounts require settle phase")
        if self.filled_quantity_atoms > (self.quantity_atoms or 0):
            raise ValueError("seller auction fill exceeds revealed quantity")
        if self.filled_quantity_atoms == 0 and (self.paid_atoms or self.rounding_remainder_e8):
            raise ValueError("seller auction zero fill cannot retain payment or rounding residue")
        if self.filled_quantity_atoms > 0 and self.paid_atoms == 0:
            raise ValueError("seller auction positive fill requires payment")

    @property
    def key(self) -> tuple[str, str, str]:
        return (self.auction_id, self.bidder, self.commitment)

    def to_canonical(self) -> dict[str, object]:
        return {
            "auction_id": self.auction_id,
            "bidder": self.bidder,
            "escrow_id": self.escrow_id,
            "bond_asset": self.bond_asset,
            "bond_atoms": self.bond_atoms,
            "commitment": self.commitment,
            "commit_height": self.commit_height,
            "reveal_deadline_height": self.reveal_deadline_height,
            "settle_deadline_height": self.settle_deadline_height,
            "inventory_asset": self.inventory_asset,
            "quantity_atoms": self.quantity_atoms,
            "price_e8": self.price_e8,
            "reveal_nonce": self.reveal_nonce,
            "filled_quantity_atoms": self.filled_quantity_atoms,
            "paid_atoms": self.paid_atoms,
            "rounding_remainder_e8": self.rounding_remainder_e8,
            "phase": self.phase,
        }


@dataclass(frozen=True, slots=True)
class PrivateSwapParticipantStateV1:
    """One trader's durable state in a bounded two-party private swap batch."""

    batch_id: str
    trader: str
    escrow_id: str
    bond_asset: str
    bond_atoms: int
    commitment: str
    commit_height: int
    reveal_deadline_height: int
    settle_deadline_height: int
    asset_in: str | None = None
    amount_in_atoms: int | None = None
    asset_out: str | None = None
    amount_out_atoms: int | None = None
    reveal_nonce: int | None = None
    phase: PrivateSwapPhaseV1 = PrivateSwapPhaseV1.COMMIT

    def __post_init__(self) -> None:
        for field_name, value in (
            ("batch id", self.batch_id),
            ("trader", self.trader),
            ("escrow id", self.escrow_id),
            ("bond asset", self.bond_asset),
        ):
            _require_token(value, name=f"private swap state {field_name}")
        _require_root(self.commitment, name="private swap state commitment")
        _require_positive_int(self.bond_atoms, name="private swap state bond")
        numeric_fields: tuple[tuple[str, int], ...] = (
            ("commit height", self.commit_height),
            ("reveal deadline height", self.reveal_deadline_height),
            ("settle deadline height", self.settle_deadline_height),
        )
        for numeric_name, numeric_value in numeric_fields:
            _require_nonnegative_int(numeric_value, name=f"private swap state {numeric_name}")
        if not self.commit_height < self.reveal_deadline_height < self.settle_deadline_height:
            raise ValueError("private swap state deadline order is invalid")
        if not isinstance(self.phase, PrivateSwapPhaseV1):
            raise TypeError("private swap state phase is not closed")
        reveal_values = (
            self.asset_in,
            self.amount_in_atoms,
            self.asset_out,
            self.amount_out_atoms,
            self.reveal_nonce,
        )
        has_reveal = all(value is not None for value in reveal_values)
        has_no_reveal = all(value is None for value in reveal_values)
        if not (has_reveal or has_no_reveal):
            raise ValueError("private swap reveal fields must be all present or all absent")
        if has_reveal:
            _require_token(self.asset_in, name="private swap input asset")
            _require_positive_int(self.amount_in_atoms, name="private swap input amount")
            _require_token(self.asset_out, name="private swap output asset")
            _require_positive_int(self.amount_out_atoms, name="private swap output amount")
            _require_positive_int(self.reveal_nonce, name="private swap reveal nonce")
            if self.asset_in == self.asset_out:
                raise ValueError("private swap input and output assets must differ")
        if self.phase in (PrivateSwapPhaseV1.COMMIT, PrivateSwapPhaseV1.CANCELLED) and not has_no_reveal:
            raise ValueError("private swap phase cannot retain reveal data")
        if self.phase in (PrivateSwapPhaseV1.REVEAL, PrivateSwapPhaseV1.SETTLE) and not has_reveal:
            raise ValueError("private swap phase requires reveal data")

    @property
    def key(self) -> tuple[str, str, str]:
        return (self.batch_id, self.trader, self.commitment)

    def to_canonical(self) -> dict[str, object]:
        return {
            "batch_id": self.batch_id,
            "trader": self.trader,
            "escrow_id": self.escrow_id,
            "bond_asset": self.bond_asset,
            "bond_atoms": self.bond_atoms,
            "commitment": self.commitment,
            "commit_height": self.commit_height,
            "reveal_deadline_height": self.reveal_deadline_height,
            "settle_deadline_height": self.settle_deadline_height,
            "asset_in": self.asset_in,
            "amount_in_atoms": self.amount_in_atoms,
            "asset_out": self.asset_out,
            "amount_out_atoms": self.amount_out_atoms,
            "reveal_nonce": self.reveal_nonce,
            "phase": self.phase,
        }


@dataclass(frozen=True, slots=True)
class TauWithdrawalIntentV1:
    withdrawal_id: str
    beneficiary: str
    asset: str
    amount_atoms: int
    source_state_root: str
    candidate_id: str
    status: TauWithdrawalStatusV1 = TauWithdrawalStatusV1.PENDING

    def __post_init__(self) -> None:
        for field_name, value in (
            ("withdrawal_id", self.withdrawal_id),
            ("beneficiary", self.beneficiary),
            ("asset", self.asset),
            ("candidate_id", self.candidate_id),
        ):
            _require_token(value, name=f"withdrawal {field_name}")
        _require_positive_int(self.amount_atoms, name="withdrawal amount")
        _require_root(self.source_state_root, name="withdrawal source state root")
        if not isinstance(self.status, TauWithdrawalStatusV1):
            raise TypeError("withdrawal status is not closed")

    def to_canonical(self) -> dict[str, object]:
        return {
            "withdrawal_id": self.withdrawal_id,
            "beneficiary": self.beneficiary,
            "asset": self.asset,
            "amount_atoms": self.amount_atoms,
            "source_state_root": self.source_state_root,
            "candidate_id": self.candidate_id,
            "status": self.status,
        }


@dataclass(frozen=True, slots=True)
class WithdrawalAcknowledgmentV1:
    withdrawal_id: str
    provenance_root: str
    tau_receipt_root: str
    acknowledged_state_root: str
    tau_receipt_height: int = 0

    def __post_init__(self) -> None:
        _require_token(self.withdrawal_id, name="ack withdrawal id")
        for field_name, value in (
            ("provenance_root", self.provenance_root),
            ("tau_receipt_root", self.tau_receipt_root),
            ("acknowledged_state_root", self.acknowledged_state_root),
        ):
            _require_root(value, name=f"ack {field_name}")
        _require_nonnegative_int(self.tau_receipt_height, name="ack Tau receipt height")

    @property
    def acknowledgment_root(self) -> str:
        return hash_v1("m6-withdrawal-ack-v1", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            "withdrawal_id": self.withdrawal_id,
            "provenance_root": self.provenance_root,
            "tau_receipt_root": self.tau_receipt_root,
            "acknowledged_state_root": self.acknowledged_state_root,
            "tau_receipt_height": self.tau_receipt_height,
        }


@dataclass(frozen=True, slots=True)
class OutboxAtomV1:
    effect_id: str
    effect_type: str
    destination: str
    asset: str
    amount_atoms: int
    source_state_root: str

    def __post_init__(self) -> None:
        for field_name, value in (
            ("effect_id", self.effect_id),
            ("effect_type", self.effect_type),
            ("destination", self.destination),
            ("asset", self.asset),
        ):
            _require_token(value, name=f"outbox {field_name}")
        _require_positive_int(self.amount_atoms, name="outbox amount")
        _require_root(self.source_state_root, name="outbox source state root")

    def to_canonical(self) -> dict[str, object]:
        return {
            "effect_id": self.effect_id,
            "effect_type": self.effect_type,
            "destination": self.destination,
            "asset": self.asset,
            "amount_atoms": self.amount_atoms,
            "source_state_root": self.source_state_root,
        }


@dataclass(frozen=True, slots=True)
class MigrationStateV1:
    phase: MigrationPhaseV1
    authority_epoch: int
    previous_authority_root: str
    checkpoint_root: str
    quiescent: bool

    def __post_init__(self) -> None:
        if not isinstance(self.phase, MigrationPhaseV1):
            raise TypeError("migration phase is not closed")
        _require_nonnegative_int(self.authority_epoch, name="migration authority epoch")
        _require_root(self.previous_authority_root, name="previous authority root", allow_zero=True)
        _require_root(self.checkpoint_root, name="migration checkpoint root", allow_zero=True)
        if type(self.quiescent) is not bool:
            raise TypeError("migration quiescent must be bool")
        if self.phase is MigrationPhaseV1.QUIESCENT and not self.quiescent:
            raise ValueError("quiescent phase requires quiescent=true")

    def to_canonical(self) -> dict[str, object]:
        return {
            "phase": self.phase,
            "authority_epoch": self.authority_epoch,
            "previous_authority_root": self.previous_authority_root,
            "checkpoint_root": self.checkpoint_root,
            "quiescent": self.quiescent,
        }


@dataclass(frozen=True, slots=True)
class TauFinalityBoundDepositWitnessV1:
    """One external deposit fact bound to a Tau finality root.

    This value says that a named inbound transfer was observed under the named
    Tau profile and finality root.  It is neither a statement of legal
    custody or ownership nor an aggregate account-balance snapshot.  The
    verifier-owned :class:`M6AuthorityEvidenceV1` binds it to one M6 subject,
    pre-state, and command before a deposit can be credited.

    The legacy ``proof_root`` name and commitment domain remain available for
    canonical compatibility.  They do not change this value's narrower
    witness semantics.
    """

    deposit_id: str
    tau_transaction_root: str
    tau_finality_root: str
    tau_profile_root: str
    beneficiary: str
    asset: str
    amount_atoms: int
    tau_finality_height: int = 0

    def __post_init__(self) -> None:
        _require_token(self.deposit_id, name="Tau deposit id")
        for field_name, value in (
            ("tau_transaction_root", self.tau_transaction_root),
            ("tau_finality_root", self.tau_finality_root),
            ("tau_profile_root", self.tau_profile_root),
        ):
            _require_root(value, name=f"Tau deposit {field_name}")
        _require_token(self.beneficiary, name="Tau deposit beneficiary")
        _require_token(self.asset, name="Tau deposit asset")
        _require_positive_int(self.amount_atoms, name="Tau deposit amount")
        _require_nonnegative_int(self.tau_finality_height, name="Tau deposit finality height")

    @property
    def witness_root(self) -> str:
        return hash_v1("m6-tau-escrow-deposit-proof-v1", self.to_canonical())

    @property
    def proof_root(self) -> str:
        """Compatibility spelling for the stable witness commitment."""

        return self.witness_root

    def to_canonical(self) -> dict[str, object]:
        return {
            "deposit_id": self.deposit_id,
            "tau_transaction_root": self.tau_transaction_root,
            "tau_finality_root": self.tau_finality_root,
            "tau_profile_root": self.tau_profile_root,
            "beneficiary": self.beneficiary,
            "asset": self.asset,
            "amount_atoms": self.amount_atoms,
            "tau_finality_height": self.tau_finality_height,
        }


# Compatibility for research callers that predate the narrower witness name.
# New M6-facing interfaces must use ``TauFinalityBoundDepositWitnessV1``.
TauEscrowDepositProofV1: TypeAlias = TauFinalityBoundDepositWitnessV1


@dataclass(frozen=True, slots=True)
class MigrationAuthorityProofV1:
    """Claim data that a migration verifier must authenticate before use."""

    kind: MigrationEvidenceKindV1
    checkpoint_root: str
    compatible_profile_root: str
    condition_root: str
    source_authority_epoch: int

    def __post_init__(self) -> None:
        if not isinstance(self.kind, MigrationEvidenceKindV1):
            raise TypeError("migration evidence kind is not closed")
        _require_root(self.checkpoint_root, name="migration proof checkpoint root")
        _require_root(
            self.compatible_profile_root,
            name="migration proof compatible profile root",
            allow_zero=True,
        )
        _require_root(self.condition_root, name="migration proof condition root")
        _require_nonnegative_int(self.source_authority_epoch, name="migration proof source epoch")

    def to_canonical(self) -> dict[str, object]:
        return {
            "kind": self.kind,
            "checkpoint_root": self.checkpoint_root,
            "compatible_profile_root": self.compatible_profile_root,
            "condition_root": self.condition_root,
            "source_authority_epoch": self.source_authority_epoch,
        }


M6AuthorityEvidencePayloadV1: TypeAlias = (
    TauFinalityBoundDepositWitnessV1 | WithdrawalAcknowledgmentV1 | MigrationAuthorityProofV1
)


class M6AuthorityEvidenceV1:
    """Opaque evidence handle issued only by an authority verifier.

    The wrapped values are canonical inputs to the verifier.  This reference
    layer does not provide Tau cryptography or migration liveness proofs; the
    verifier port must establish those conditions before it receives the
    private construction token.
    """

    _kind: GlobalCommandKindV1
    _subject_root: str
    _pre_state_root: str
    _command_hash: str
    _payload: M6AuthorityEvidencePayloadV1
    _sealed: bool
    __slots__ = ("_kind", "_subject_root", "_pre_state_root", "_command_hash", "_payload", "_sealed")

    def __init__(
        self,
        verification_approval: object,
        kind: GlobalCommandKindV1,
        subject_root: str,
        pre_state_root: str,
        command_hash: str,
        payload: M6AuthorityEvidencePayloadV1,
    ) -> None:
        if not _is_verifier_approval(verification_approval):
            raise TypeError("M6 authority evidence requires a sealed verifier approval")
        if kind not in {
            GlobalCommandKindV1.TAU_ESCROW_DEPOSIT,
            GlobalCommandKindV1.TAU_WITHDRAWAL_ACK,
            GlobalCommandKindV1.FALLBACK_ACTIVATE,
            GlobalCommandKindV1.TAU_REJOIN,
        }:
            raise ValueError("unsupported M6 authority evidence kind")
        _require_root(subject_root, name="authority evidence subject root")
        _require_root(pre_state_root, name="authority evidence pre-state root")
        _require_root(command_hash, name="authority evidence command hash")
        expected_types: dict[GlobalCommandKindV1, type[object]] = {
            GlobalCommandKindV1.TAU_ESCROW_DEPOSIT: TauFinalityBoundDepositWitnessV1,
            GlobalCommandKindV1.TAU_WITHDRAWAL_ACK: WithdrawalAcknowledgmentV1,
            GlobalCommandKindV1.FALLBACK_ACTIVATE: MigrationAuthorityProofV1,
            GlobalCommandKindV1.TAU_REJOIN: MigrationAuthorityProofV1,
        }
        if not isinstance(payload, expected_types[kind]):
            raise TypeError("authority evidence payload does not match its kind")
        object.__setattr__(self, "_kind", kind)
        object.__setattr__(self, "_subject_root", subject_root)
        object.__setattr__(self, "_pre_state_root", pre_state_root)
        object.__setattr__(self, "_command_hash", command_hash)
        object.__setattr__(self, "_payload", payload)
        object.__setattr__(self, "_sealed", True)

    @property
    def kind(self) -> GlobalCommandKindV1:
        return self._kind

    @property
    def subject_root(self) -> str:
        return self._subject_root

    @property
    def pre_state_root(self) -> str:
        return self._pre_state_root

    @property
    def command_hash(self) -> str:
        return self._command_hash

    @property
    def payload(self) -> M6AuthorityEvidencePayloadV1:
        return self._payload

    def to_canonical(self) -> dict[str, object]:
        return {
            "kind": self._kind,
            "subject_root": self._subject_root,
            "pre_state_root": self._pre_state_root,
            "command_hash": self._command_hash,
            "payload": self._payload,
        }

    def __setattr__(self, name: str, value: object) -> None:
        if getattr(self, "_sealed", False):
            raise AttributeError("M6 authority evidence is immutable")
        object.__setattr__(self, name, value)

    def __repr__(self) -> str:
        return f"M6AuthorityEvidenceV1(kind={self.kind.value!r}, command_hash={self.command_hash!r})"


def validate_authenticated_execution_context_body_v1(raw: object) -> str:
    """Validate a persisted context projection without issuing authority.

    Durable replay stores the canonical context body, while the verifier-owned
    witness cannot be reconstructed after a process restart.  This function
    therefore reconstructs only the value-level projection and returns its
    authentication root.  It never creates an ``AuthenticatedExecutionContextV1``
    or any external-authority witness.
    """

    expected_keys = {
        "deployment",
        "chain_id",
        "parent_head",
        "epoch",
        "sender",
        "nonce",
        "oracle_context",
        "tau_profile",
        "verifier_registry",
        "freshness_bounds",
        "ledger_height",
        "authority_evidence",
    }
    if not isinstance(raw, Mapping) or set(raw) != expected_keys:
        raise ValueError("authenticated execution context body keys mismatch")

    def _nested(value: object, *, name: str, keys: set[str]) -> Mapping[str, object]:
        if not isinstance(value, Mapping) or set(value) != keys:
            raise ValueError(f"{name} keys mismatch")
        return cast(Mapping[str, object], value)

    _require_root(raw["deployment"], name="context deployment")
    _require_root(raw["chain_id"], name="context chain id")
    _require_root(raw["parent_head"], name="context parent head", allow_zero=True)
    _require_nonnegative_int(raw["epoch"], name="context epoch")
    _require_token(raw["sender"], name="context sender")
    _require_positive_int(raw["nonce"], name="context nonce")
    oracle_raw = _nested(
        raw["oracle_context"],
        name="context oracle context",
        keys={"context_root", "observed_height", "oracle_height"},
    )
    oracle = OracleContextV1(
        context_root=cast(str, oracle_raw["context_root"]),
        observed_height=cast(int, oracle_raw["observed_height"]),
        oracle_height=cast(int, oracle_raw["oracle_height"]),
    )
    _require_root(raw["tau_profile"], name="context Tau profile")
    _require_root(raw["verifier_registry"], name="context verifier registry")
    freshness_raw = _nested(
        raw["freshness_bounds"],
        name="context freshness bounds",
        keys={"max_oracle_age_blocks", "max_tau_age_blocks", "max_command_age_blocks"},
    )
    freshness = FreshnessBoundsV1(
        max_oracle_age_blocks=cast(int, freshness_raw["max_oracle_age_blocks"]),
        max_tau_age_blocks=cast(int, freshness_raw["max_tau_age_blocks"]),
        max_command_age_blocks=cast(int, freshness_raw["max_command_age_blocks"]),
    )
    _require_nonnegative_int(raw["ledger_height"], name="context ledger height")

    authority_raw = raw["authority_evidence"]
    authority_projection: dict[str, object] | None = None
    if authority_raw is not None:
        authority = _nested(
            authority_raw,
            name="context authority evidence",
            keys={"kind", "subject_root", "pre_state_root", "command_hash", "payload"},
        )
        try:
            authority_kind = GlobalCommandKindV1(authority["kind"])
        except (TypeError, ValueError) as exc:
            raise ValueError("context authority evidence kind is invalid") from exc
        _require_root(authority["subject_root"], name="context authority subject root")
        _require_root(authority["pre_state_root"], name="context authority pre-state root")
        _require_root(authority["command_hash"], name="context authority command hash")
        payload_raw = authority["payload"]
        payload: M6AuthorityEvidencePayloadV1
        if authority_kind is GlobalCommandKindV1.TAU_ESCROW_DEPOSIT:
            payload_obj = _nested(
                payload_raw,
                name="context Tau deposit evidence",
                keys={
                    "deposit_id",
                    "tau_transaction_root",
                    "tau_finality_root",
                    "tau_profile_root",
                    "beneficiary",
                    "asset",
                    "amount_atoms",
                    "tau_finality_height",
                },
            )
            payload = TauFinalityBoundDepositWitnessV1(
                deposit_id=cast(str, payload_obj["deposit_id"]),
                tau_transaction_root=cast(str, payload_obj["tau_transaction_root"]),
                tau_finality_root=cast(str, payload_obj["tau_finality_root"]),
                tau_profile_root=cast(str, payload_obj["tau_profile_root"]),
                beneficiary=cast(str, payload_obj["beneficiary"]),
                asset=cast(str, payload_obj["asset"]),
                amount_atoms=cast(int, payload_obj["amount_atoms"]),
                tau_finality_height=cast(int, payload_obj["tau_finality_height"]),
            )
        elif authority_kind is GlobalCommandKindV1.TAU_WITHDRAWAL_ACK:
            payload_obj = _nested(
                payload_raw,
                name="context Tau acknowledgment evidence",
                keys={
                    "withdrawal_id",
                    "provenance_root",
                    "tau_receipt_root",
                    "acknowledged_state_root",
                    "tau_receipt_height",
                },
            )
            payload = WithdrawalAcknowledgmentV1(
                withdrawal_id=cast(str, payload_obj["withdrawal_id"]),
                provenance_root=cast(str, payload_obj["provenance_root"]),
                tau_receipt_root=cast(str, payload_obj["tau_receipt_root"]),
                acknowledged_state_root=cast(str, payload_obj["acknowledged_state_root"]),
                tau_receipt_height=cast(int, payload_obj["tau_receipt_height"]),
            )
        elif authority_kind in {
            GlobalCommandKindV1.FALLBACK_ACTIVATE,
            GlobalCommandKindV1.TAU_REJOIN,
        }:
            payload_obj = _nested(
                payload_raw,
                name="context migration evidence",
                keys={
                    "kind",
                    "checkpoint_root",
                    "compatible_profile_root",
                    "condition_root",
                    "source_authority_epoch",
                },
            )
            try:
                migration_kind = MigrationEvidenceKindV1(payload_obj["kind"])
            except (TypeError, ValueError) as exc:
                raise ValueError("context migration evidence kind is invalid") from exc
            payload = MigrationAuthorityProofV1(
                kind=migration_kind,
                checkpoint_root=cast(str, payload_obj["checkpoint_root"]),
                compatible_profile_root=cast(str, payload_obj["compatible_profile_root"]),
                condition_root=cast(str, payload_obj["condition_root"]),
                source_authority_epoch=cast(int, payload_obj["source_authority_epoch"]),
            )
        else:
            raise ValueError("context authority evidence kind is unsupported")
        authority_projection = {
            "kind": authority_kind,
            "subject_root": authority["subject_root"],
            "pre_state_root": authority["pre_state_root"],
            "command_hash": authority["command_hash"],
            "payload": payload,
        }

    canonical_context = {
        "deployment": raw["deployment"],
        "chain_id": raw["chain_id"],
        "parent_head": raw["parent_head"],
        "epoch": raw["epoch"],
        "sender": raw["sender"],
        "nonce": raw["nonce"],
        "oracle_context": oracle,
        "tau_profile": raw["tau_profile"],
        "verifier_registry": raw["verifier_registry"],
        "freshness_bounds": freshness,
        "ledger_height": raw["ledger_height"],
        "authority_evidence": authority_projection,
    }
    if canonical_bytes_v1(canonical_context) != canonical_bytes_v1(raw):
        raise ValueError("authenticated execution context canonical projection mismatch")
    return hash_v1("m6-authenticated-execution-context-v1", raw)


@dataclass(frozen=True, slots=True)
class TauBatchCertificateV1:
    batch_id: str
    tau_profile_root: str
    chain_id: str
    ordered_command_hashes: tuple[str, ...]
    ordered_nonce_identities: tuple[str, ...]
    candidate_parent_head: str
    certificate_root: str

    def __post_init__(self) -> None:
        _require_token(self.batch_id, name="Tau batch id")
        _require_root(self.tau_profile_root, name="Tau batch profile root")
        _require_root(self.chain_id, name="Tau batch chain id")
        hashes = tuple(_require_root(item, name="Tau command hash") for item in self.ordered_command_hashes)
        if not hashes:
            raise ValueError("Tau batch must contain commands")
        identities = _ordered_tokens(
            self.ordered_nonce_identities,
            name="Tau nonce identities",
            max_items=ZRPF_COMMAND_COUNT_V1,
        )
        if len(hashes) != len(identities):
            raise ValueError("Tau command and nonce identity counts must match")
        _require_root(self.candidate_parent_head, name="Tau candidate parent head", allow_zero=True)
        expected = hash_v1(
            "m6-tau-batch-certificate-v1",
            {
                "batch_id": self.batch_id,
                "tau_profile_root": self.tau_profile_root,
                "chain_id": self.chain_id,
                "ordered_command_hashes": hashes,
                "ordered_nonce_identities": identities,
                "candidate_parent_head": self.candidate_parent_head,
            },
        )
        if self.certificate_root != expected:
            raise ValueError("Tau batch certificate root mismatch")

    def to_canonical(self) -> dict[str, object]:
        return {
            "batch_id": self.batch_id,
            "tau_profile_root": self.tau_profile_root,
            "chain_id": self.chain_id,
            "ordered_command_hashes": self.ordered_command_hashes,
            "ordered_nonce_identities": self.ordered_nonce_identities,
            "candidate_parent_head": self.candidate_parent_head,
            "certificate_root": self.certificate_root,
        }


@dataclass(frozen=True, slots=True)
class ZenoLedgerFinalityCertificateV1:
    finality_id: str
    candidate_head: str
    publication_root: str
    chain_id: str
    validator_set_root: str
    writer_epoch: int
    signer_ids: tuple[str, ...]
    quorum: int
    mode: FinalityModeV1
    signature_root: str
    execution_receipt_root: str | None = None

    def __post_init__(self) -> None:
        _require_token(self.finality_id, name="finality id")
        _require_root(self.candidate_head, name="finality candidate head")
        _require_root(self.publication_root, name="finality publication root")
        _require_root(self.chain_id, name="finality chain id")
        _require_root(self.validator_set_root, name="finality validator set root")
        _require_nonnegative_int(self.writer_epoch, name="finality writer epoch")
        signers = _ordered_unique(self.signer_ids, name="finality signer ids", max_items=7)
        if len(signers) > 7:
            raise ValueError("finality signer set exceeds seven validators")
        _require_positive_int(self.quorum, name="finality quorum")
        if self.quorum < 5 or self.quorum > 7 or len(signers) < self.quorum:
            raise ValueError("finality certificate does not meet the 5-of-7 quorum")
        if not isinstance(self.mode, FinalityModeV1):
            raise TypeError("finality mode is not closed")
        _require_root(self.signature_root, name="finality signature root")
        if self.execution_receipt_root is not None:
            _require_root(self.execution_receipt_root, name="finality execution receipt root")

    def to_canonical(self) -> dict[str, object]:
        return {
            "finality_id": self.finality_id,
            "candidate_head": self.candidate_head,
            "publication_root": self.publication_root,
            "chain_id": self.chain_id,
            "validator_set_root": self.validator_set_root,
            "writer_epoch": self.writer_epoch,
            "signer_ids": self.signer_ids,
            "quorum": self.quorum,
            "mode": self.mode,
            "signature_root": self.signature_root,
            "execution_receipt_root": self.execution_receipt_root,
        }

    @property
    def certificate_root(self) -> str:
        return hash_v1("m6-zeno-ledger-finality-certificate-v1", self.to_canonical())


_FINALITY_VERIFICATION_RECEIPT_TOKEN = object()


class M6FinalityVerificationReceiptV1:
    """Opaque receipt returned by the external validator-finality verifier.

    The structural certificate checks below do not verify validator signatures.
    This receipt is the explicit port through which an external verifier binds
    its cryptographic result to the exact certificate and expected writer epoch.
    """

    _subject_root: str
    _candidate_parent_head: str
    _candidate_head: str
    _publication_root: str
    _writer_epoch: int
    _certificate_root: str
    _attestation_root: str
    _sealed: bool

    __slots__ = (
        "_subject_root",
        "_candidate_parent_head",
        "_candidate_head",
        "_publication_root",
        "_writer_epoch",
        "_certificate_root",
        "_attestation_root",
        "_sealed",
    )

    def __init__(
        self,
        token: object,
        *,
        subject_root: str,
        candidate_parent_head: str,
        candidate_head: str,
        publication_root: str,
        writer_epoch: int,
        certificate_root: str,
        attestation_root: str,
    ) -> None:
        if token is not _FINALITY_VERIFICATION_RECEIPT_TOKEN:
            raise TypeError("M6 finality verification receipt is verifier-created")
        _require_root(subject_root, name="M6 finality receipt subject root")
        _require_root(
            candidate_parent_head,
            name="M6 finality receipt parent head",
            allow_zero=True,
        )
        _require_root(candidate_head, name="M6 finality receipt candidate head")
        _require_root(publication_root, name="M6 finality receipt publication root")
        _require_nonnegative_int(writer_epoch, name="M6 finality receipt writer epoch")
        _require_root(certificate_root, name="M6 finality receipt certificate root")
        _require_root(attestation_root, name="M6 finality receipt attestation root")
        object.__setattr__(self, "_subject_root", subject_root)
        object.__setattr__(self, "_candidate_parent_head", candidate_parent_head)
        object.__setattr__(self, "_candidate_head", candidate_head)
        object.__setattr__(self, "_publication_root", publication_root)
        object.__setattr__(self, "_writer_epoch", writer_epoch)
        object.__setattr__(self, "_certificate_root", certificate_root)
        object.__setattr__(self, "_attestation_root", attestation_root)
        object.__setattr__(self, "_sealed", True)

    @property
    def subject_root(self) -> str:
        return self._subject_root

    @property
    def candidate_parent_head(self) -> str:
        return self._candidate_parent_head

    @property
    def candidate_head(self) -> str:
        return self._candidate_head

    @property
    def publication_root(self) -> str:
        return self._publication_root

    @property
    def writer_epoch(self) -> int:
        return self._writer_epoch

    @property
    def certificate_root(self) -> str:
        return self._certificate_root

    @property
    def attestation_root(self) -> str:
        return self._attestation_root

    @property
    def receipt_root(self) -> str:
        return hash_v1(
            "m6-finality-verification-receipt-v1",
            {
                "subject_root": self.subject_root,
                "candidate_parent_head": self.candidate_parent_head,
                "candidate_head": self.candidate_head,
                "publication_root": self.publication_root,
                "writer_epoch": self.writer_epoch,
                "certificate_root": self.certificate_root,
                "attestation_root": self.attestation_root,
            },
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            "subject_root": self.subject_root,
            "candidate_parent_head": self.candidate_parent_head,
            "candidate_head": self.candidate_head,
            "publication_root": self.publication_root,
            "writer_epoch": self.writer_epoch,
            "certificate_root": self.certificate_root,
            "attestation_root": self.attestation_root,
            "receipt_root": self.receipt_root,
        }

    def __setattr__(self, name: str, value: object) -> None:
        if getattr(self, "_sealed", False):
            raise AttributeError("M6 finality verification receipt is immutable")
        object.__setattr__(self, name, value)


@dataclass(frozen=True, slots=True)
class M6FinalityVerificationReceiptRecordV1:
    """Canonical non-authorizing projection retained for durable replay."""

    subject_root: str
    candidate_parent_head: str
    candidate_head: str
    publication_root: str
    writer_epoch: int
    certificate_root: str
    attestation_root: str

    def __post_init__(self) -> None:
        _require_root(self.subject_root, name="finality receipt record subject root")
        _require_root(
            self.candidate_parent_head,
            name="finality receipt record parent head",
            allow_zero=True,
        )
        _require_root(self.candidate_head, name="finality receipt record candidate head")
        _require_root(self.publication_root, name="finality receipt record publication root")
        _require_nonnegative_int(self.writer_epoch, name="finality receipt record writer epoch")
        _require_root(self.certificate_root, name="finality receipt record certificate root")
        _require_root(self.attestation_root, name="finality receipt record attestation root")

    @classmethod
    def from_verified(
        cls,
        receipt: M6FinalityVerificationReceiptV1,
    ) -> "M6FinalityVerificationReceiptRecordV1":
        if not isinstance(receipt, M6FinalityVerificationReceiptV1):
            raise TypeError("finality verification receipt is not typed")
        return cls(
            subject_root=receipt.subject_root,
            candidate_parent_head=receipt.candidate_parent_head,
            candidate_head=receipt.candidate_head,
            publication_root=receipt.publication_root,
            writer_epoch=receipt.writer_epoch,
            certificate_root=receipt.certificate_root,
            attestation_root=receipt.attestation_root,
        )

    @property
    def receipt_root(self) -> str:
        return hash_v1(
            "m6-finality-verification-receipt-v1",
            {
                "subject_root": self.subject_root,
                "candidate_parent_head": self.candidate_parent_head,
                "candidate_head": self.candidate_head,
                "publication_root": self.publication_root,
                "writer_epoch": self.writer_epoch,
                "certificate_root": self.certificate_root,
                "attestation_root": self.attestation_root,
            },
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": FINALITY_RECEIPT_RECORD_SCHEMA_V1,
            "subject_root": self.subject_root,
            "candidate_parent_head": self.candidate_parent_head,
            "candidate_head": self.candidate_head,
            "publication_root": self.publication_root,
            "writer_epoch": self.writer_epoch,
            "certificate_root": self.certificate_root,
            "attestation_root": self.attestation_root,
            "receipt_root": self.receipt_root,
        }


class _VerifiedZenoLedgerFinalityToken:
    pass


_VERIFIED_ZENO_LEDGER_FINALITY_TOKEN = _VerifiedZenoLedgerFinalityToken()


class VerifiedZenoLedgerFinalityV1:
    """Opaque finality evidence issued by the M6 finality verifier.

    The Python reference verifier below checks structural certificate bindings
    and quorum shape.  It does not implement validator signature cryptography,
    validator-independent data availability, or the 5-of-7 fault premise.
    Keeping the evidence opaque still prevents the commit port from accepting
    a caller-authored certificate as if it had crossed the verifier boundary.
    """

    _subject_root: str
    _candidate_parent_head: str
    _candidate_head: str
    _publication_root: str
    _expected_command_root: str | None
    _expected_nonce_root: str | None
    _certificate: ZenoLedgerFinalityCertificateV1
    _tau_certificate: TauBatchCertificateV1 | None
    _verification_receipt: M6FinalityVerificationReceiptV1
    _sealed: bool
    __slots__ = (
        "_subject_root",
        "_candidate_parent_head",
        "_candidate_head",
        "_publication_root",
        "_expected_command_root",
        "_expected_nonce_root",
        "_certificate",
        "_tau_certificate",
        "_verification_receipt",
        "_sealed",
    )

    def __init__(
        self,
        token: _VerifiedZenoLedgerFinalityToken,
        *,
        subject_root: str,
        candidate_parent_head: str,
        candidate_head: str,
        publication_root: str,
        expected_command_root: str | None,
        expected_nonce_root: str | None,
        certificate: ZenoLedgerFinalityCertificateV1,
        tau_certificate: TauBatchCertificateV1 | None,
        verification_receipt: M6FinalityVerificationReceiptV1,
    ) -> None:
        if token is not _VERIFIED_ZENO_LEDGER_FINALITY_TOKEN:
            raise TypeError("VerifiedZenoLedgerFinalityV1 is verifier-created")
        if not isinstance(certificate, ZenoLedgerFinalityCertificateV1):
            raise TypeError("verified finality certificate is not typed")
        if not isinstance(verification_receipt, M6FinalityVerificationReceiptV1):
            raise TypeError("verified finality receipt is not typed")
        _require_root(subject_root, name="verified finality subject root")
        _require_root(candidate_parent_head, name="verified finality parent head", allow_zero=True)
        _require_root(candidate_head, name="verified finality candidate head")
        _require_root(publication_root, name="verified finality publication root")
        if expected_command_root is not None:
            _require_root(expected_command_root, name="verified finality command root")
        if expected_nonce_root is not None:
            _require_root(expected_nonce_root, name="verified finality nonce root")
        if certificate.candidate_head != candidate_head:
            raise ValueError("verified finality candidate head mismatch")
        if certificate.publication_root != publication_root:
            raise ValueError("verified finality publication root mismatch")
        if (
            verification_receipt.subject_root != subject_root
            or verification_receipt.candidate_parent_head != candidate_parent_head
            or verification_receipt.candidate_head != candidate_head
            or verification_receipt.publication_root != publication_root
            or verification_receipt.writer_epoch != certificate.writer_epoch
            or verification_receipt.certificate_root != certificate.certificate_root
        ):
            raise ValueError("verified finality receipt binding mismatch")
        if tau_certificate is not None and not isinstance(tau_certificate, TauBatchCertificateV1):
            raise TypeError("verified finality Tau certificate is not typed")
        if certificate.mode is FinalityModeV1.FALLBACK_FORCED_INCLUSION and tau_certificate is not None:
            raise ValueError("fallback finality forbids a Tau batch certificate")
        object.__setattr__(self, "_subject_root", subject_root)
        object.__setattr__(self, "_candidate_parent_head", candidate_parent_head)
        object.__setattr__(self, "_candidate_head", candidate_head)
        object.__setattr__(self, "_publication_root", publication_root)
        object.__setattr__(self, "_expected_command_root", expected_command_root)
        object.__setattr__(self, "_expected_nonce_root", expected_nonce_root)
        object.__setattr__(self, "_certificate", certificate)
        object.__setattr__(self, "_tau_certificate", tau_certificate)
        object.__setattr__(self, "_verification_receipt", verification_receipt)
        object.__setattr__(self, "_sealed", True)

    @property
    def subject_root(self) -> str:
        return self._subject_root

    @property
    def candidate_parent_head(self) -> str:
        return self._candidate_parent_head

    @property
    def candidate_head(self) -> str:
        return self._candidate_head

    @property
    def publication_root(self) -> str:
        return self._publication_root

    @property
    def expected_command_root(self) -> str | None:
        return self._expected_command_root

    @property
    def expected_nonce_root(self) -> str | None:
        return self._expected_nonce_root

    @property
    def certificate(self) -> ZenoLedgerFinalityCertificateV1:
        return self._certificate

    @property
    def tau_certificate(self) -> TauBatchCertificateV1 | None:
        return self._tau_certificate

    @property
    def verification_receipt(self) -> M6FinalityVerificationReceiptV1:
        return self._verification_receipt

    @property
    def evidence_root(self) -> str:
        return hash_v1(
            "m6-verified-zeno-ledger-finality-v1",
            self.to_canonical(),
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            "subject_root": self._subject_root,
            "candidate_parent_head": self._candidate_parent_head,
            "candidate_head": self._candidate_head,
            "publication_root": self._publication_root,
            "expected_command_root": self._expected_command_root,
            "expected_nonce_root": self._expected_nonce_root,
            "certificate": self._certificate,
            "tau_certificate": self._tau_certificate,
            "verification_receipt": self._verification_receipt,
        }

    def __setattr__(self, name: str, value: object) -> None:
        if getattr(self, "_sealed", False):
            raise AttributeError("verified finality evidence is immutable")
        object.__setattr__(self, name, value)

    def __repr__(self) -> str:
        return f"VerifiedZenoLedgerFinalityV1(evidence_root={self.evidence_root!r})"


@dataclass(frozen=True, slots=True)
class ValueDeltaEntryV1:
    """One signed delta in a logical M6 ledger allocation.

    ``custody`` is the immutable V1 wire spelling.  The value denotes an
    internal allocation partition only; it does not make a legal-custody,
    beneficial-ownership, or escrow assertion.
    """

    delta_class: ValueDeltaClassV1
    owner: str
    asset: str
    custody: str
    delta_atoms: int

    def __post_init__(self) -> None:
        if not isinstance(self.delta_class, ValueDeltaClassV1):
            raise TypeError("value delta class is not closed")
        _require_token(self.owner, name="value delta owner")
        _require_token(self.asset, name="value delta asset")
        _require_token(self.custody, name="value delta custody")
        if not _is_int(self.delta_atoms) or self.delta_atoms == 0:
            raise ValueError("value delta amount must be a nonzero integer")

    @classmethod
    def from_ledger_allocation(
        cls,
        *,
        delta_class: ValueDeltaClassV1,
        owner: str,
        asset: str,
        ledger_allocation: str,
        delta_atoms: int,
    ) -> "ValueDeltaEntryV1":
        """Construct a delta with the legal-neutral internal term."""

        return cls(
            delta_class=delta_class,
            owner=owner,
            asset=asset,
            custody=ledger_allocation,
            delta_atoms=delta_atoms,
        )

    @property
    def ledger_allocation(self) -> str:
        """Return the internal allocation partition for this delta."""

        return self.custody

    @property
    def key(self) -> tuple[str, str, str, str]:
        return (self.delta_class.value, self.owner, self.asset, self.custody)

    def to_canonical(self) -> dict[str, object]:
        return {
            "delta_class": self.delta_class,
            "owner": self.owner,
            "asset": self.asset,
            # V1 wire compatibility.  See ``ledger_allocation`` above.
            "custody": self.custody,
            "delta_atoms": self.delta_atoms,
        }


@dataclass(frozen=True, slots=True)
class ValueDeltaCertificateV1:
    command_hash: str
    pre_state_root: str
    post_state_root: str
    entries: tuple[ValueDeltaEntryV1, ...]
    delta_root: str

    def __post_init__(self) -> None:
        _require_root(self.command_hash, name="delta command hash")
        _require_root(self.pre_state_root, name="delta pre-state root")
        _require_root(self.post_state_root, name="delta post-state root")
        if not isinstance(self.entries, tuple):
            raise TypeError("value delta entries must be a tuple")
        if tuple(entry.key for entry in self.entries) != tuple(sorted(entry.key for entry in self.entries)):
            raise ValueError("value delta entries must be canonically ordered")
        if len({entry.key for entry in self.entries}) != len(self.entries):
            raise ValueError("value delta entries must be unique")
        expected = hash_v1(
            "m6-value-delta-certificate-v1",
            {
                "command_hash": self.command_hash,
                "pre_state_root": self.pre_state_root,
                "post_state_root": self.post_state_root,
                "entries": self.entries,
            },
        )
        if self.delta_root != expected:
            raise ValueError("value delta root mismatch")

    def internal_transfer_totals(self) -> dict[tuple[str, str], int]:
        totals: dict[tuple[str, str], int] = {}
        for entry in self.entries:
            if entry.delta_class is ValueDeltaClassV1.INTERNAL_TRANSFER:
                key = (entry.asset, entry.custody)
                totals[key] = totals.get(key, 0) + entry.delta_atoms
        return totals

    def preserves_internal_conservation(self) -> bool:
        return all(total == 0 for total in self.internal_transfer_totals().values())

    def to_canonical(self) -> dict[str, object]:
        return {
            "command_hash": self.command_hash,
            "pre_state_root": self.pre_state_root,
            "post_state_root": self.post_state_root,
            "entries": self.entries,
            "delta_root": self.delta_root,
        }


@dataclass(frozen=True, slots=True)
class HistoryAtomV1:
    sequence: int
    command_hash: str
    sender: str
    nonce: int
    pre_state_root: str
    post_state_root: str
    outcome: BusinessStatusV1
    value_delta_root: str
    nullifier: str
    business_reject_reason: BusinessRejectReasonV1 | None = None

    def __post_init__(self) -> None:
        _require_nonnegative_int(self.sequence, name="history sequence")
        _require_root(self.command_hash, name="history command hash")
        _require_token(self.sender, name="history sender")
        _require_positive_int(self.nonce, name="history nonce")
        _require_root(self.pre_state_root, name="history pre-state root")
        _require_root(self.post_state_root, name="history post-state root")
        if not isinstance(self.outcome, BusinessStatusV1):
            raise TypeError("history outcome is not closed")
        if self.outcome is BusinessStatusV1.ACCEPTED and self.business_reject_reason is not None:
            raise ValueError("accepted history cannot have a business reject reason")
        if self.outcome is BusinessStatusV1.REJECTED_COMMITTED and self.business_reject_reason is None:
            raise ValueError("committed rejection history requires a business reject reason")
        _require_root(self.value_delta_root, name="history value delta root")
        _require_root(self.nullifier, name="history nullifier")

    @property
    def history_root(self) -> str:
        return hash_v1("m6-history-atom-v1", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            "sequence": self.sequence,
            "command_hash": self.command_hash,
            "sender": self.sender,
            "nonce": self.nonce,
            "pre_state_root": self.pre_state_root,
            "post_state_root": self.post_state_root,
            "outcome": self.outcome,
            "value_delta_root": self.value_delta_root,
            "nullifier": self.nullifier,
            "business_reject_reason": self.business_reject_reason,
        }


@dataclass(frozen=True, slots=True)
class PublicationAtomV1:
    candidate_id: str
    pre_state_root: str
    post_state_root: str
    history_root: str
    nullifier_root: str
    value_delta_root: str
    outbox_root: str
    execution_context_root: str
    writer_epoch: int
    business_status: BusinessStatusV1 | None = None
    business_reject_reason: BusinessRejectReasonV1 | None = None

    def __post_init__(self) -> None:
        _require_token(self.candidate_id, name="publication candidate id")
        for field_name, value in (
            ("pre_state_root", self.pre_state_root),
            ("post_state_root", self.post_state_root),
            ("history_root", self.history_root),
            ("nullifier_root", self.nullifier_root),
            ("value_delta_root", self.value_delta_root),
            ("outbox_root", self.outbox_root),
            ("execution_context_root", self.execution_context_root),
        ):
            _require_root(value, name=f"publication {field_name}")
        _require_nonnegative_int(self.writer_epoch, name="publication writer epoch")
        if self.business_status is not None and not isinstance(self.business_status, BusinessStatusV1):
            raise TypeError("publication business status is not closed")
        if self.business_status is BusinessStatusV1.ACCEPTED and self.business_reject_reason is not None:
            raise ValueError("accepted publication cannot have a business reject reason")
        if self.business_status is BusinessStatusV1.REJECTED_COMMITTED and self.business_reject_reason is None:
            raise ValueError("committed rejection publication requires a business reject reason")
        if self.business_status is None and self.business_reject_reason is not None:
            raise ValueError("publication reject reason requires a business status")

    @property
    def publication_root(self) -> str:
        return hash_v1("m6-publication-atom-v1", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            "candidate_id": self.candidate_id,
            "pre_state_root": self.pre_state_root,
            "post_state_root": self.post_state_root,
            "history_root": self.history_root,
            "nullifier_root": self.nullifier_root,
            "value_delta_root": self.value_delta_root,
            "outbox_root": self.outbox_root,
            "execution_context_root": self.execution_context_root,
            "writer_epoch": self.writer_epoch,
            "business_status": self.business_status,
            "business_reject_reason": self.business_reject_reason,
        }


@dataclass(frozen=True, slots=True)
class M6ApplicationStateV1:
    """Complete candidate state carried by the M6 reference transition."""

    deployment: str
    head: str
    writer_epoch: int
    ingress_nonces: tuple[NonceAtomV1, ...] = ()
    economic_atoms: tuple[EconomicAtomV1, ...] = ()
    history: tuple[HistoryAtomV1, ...] = ()
    nullifiers: tuple[str, ...] = ()
    finality_certificates: tuple[ZenoLedgerFinalityCertificateV1, ...] = ()
    migration: MigrationStateV1 = MigrationStateV1(
        phase=MigrationPhaseV1.NORMAL,
        authority_epoch=0,
        previous_authority_root=ZERO_ROOT_V1,
        checkpoint_root=ZERO_ROOT_V1,
        quiescent=False,
    )
    escrows: tuple[EscrowAtomV1, ...] = ()
    withdrawals: tuple[TauWithdrawalIntentV1, ...] = ()
    outbox: tuple[OutboxAtomV1, ...] = ()
    acknowledgments: tuple[WithdrawalAcknowledgmentV1, ...] = ()
    seller_auction_bids: tuple[SellerAuctionBidStateV1, ...] = ()
    private_swap_participants: tuple[PrivateSwapParticipantStateV1, ...] = ()
    history_root_cache: str | None = field(default=None, repr=False)
    nullifier_root_cache: str | None = field(default=None, repr=False)
    outbox_root_cache: str | None = field(default=None, repr=False)

    def __post_init__(self) -> None:
        _require_root(self.deployment, name="state deployment")
        _require_root(self.head, name="state head", allow_zero=True)
        _require_nonnegative_int(self.writer_epoch, name="state writer epoch")
        if not isinstance(self.ingress_nonces, tuple):
            raise TypeError("state ingress_nonces must be a tuple")
        if tuple(item.sender for item in self.ingress_nonces) != tuple(
            sorted(item.sender for item in self.ingress_nonces)
        ):
            raise ValueError("state ingress nonces must be sender ordered")
        if len({item.sender for item in self.ingress_nonces}) != len(self.ingress_nonces):
            raise ValueError("state ingress nonces must be unique")
        if not isinstance(self.economic_atoms, tuple):
            raise TypeError("state economic_atoms must be a tuple")
        if tuple(item.key for item in self.economic_atoms) != tuple(
            sorted(item.key for item in self.economic_atoms)
        ):
            raise ValueError("state economic atoms must be canonically ordered")
        if len({item.key for item in self.economic_atoms}) != len(self.economic_atoms):
            raise ValueError("state economic atoms must be unique")
        if len(self.economic_atoms) > MAX_ECONOMIC_ATOMS:
            raise ValueError("state economic atom capacity exceeded")
        if not isinstance(self.history, tuple) or len(self.history) > MAX_HISTORY_LENGTH:
            raise ValueError("state history capacity exceeded")
        if tuple(item.sequence for item in self.history) != tuple(range(len(self.history))):
            raise ValueError("state history sequence must be contiguous")
        _ordered_tokens(self.nullifiers, name="state nullifiers", max_items=MAX_HISTORY_LENGTH)
        if not isinstance(self.finality_certificates, tuple):
            raise TypeError("state finality certificates must be a tuple")
        if not isinstance(self.migration, MigrationStateV1):
            raise TypeError("state migration must be MigrationStateV1")
        if self.migration.authority_epoch != self.writer_epoch:
            raise ValueError("migration and state writer epochs must match")
        for field_name, values, max_items in (
            ("escrows", self.escrows, MAX_HISTORY_LENGTH),
            ("withdrawals", self.withdrawals, MAX_HISTORY_LENGTH),
            ("outbox", self.outbox, MAX_OUTBOX_ROWS),
            ("acknowledgments", self.acknowledgments, MAX_HISTORY_LENGTH),
            ("seller auction bids", self.seller_auction_bids, MAX_HISTORY_LENGTH),
            ("private swap participants", self.private_swap_participants, MAX_HISTORY_LENGTH),
        ):
            if not isinstance(values, tuple) or len(values) > max_items:
                raise ValueError(f"state {field_name} capacity/type invalid")
        if tuple(item.key for item in self.seller_auction_bids) != tuple(
            sorted(item.key for item in self.seller_auction_bids)
        ):
            raise ValueError("state seller auction bids must be canonically ordered")
        if len({item.key for item in self.seller_auction_bids}) != len(self.seller_auction_bids):
            raise ValueError("state seller auction bids must be unique")
        if tuple(item.key for item in self.private_swap_participants) != tuple(
            sorted(item.key for item in self.private_swap_participants)
        ):
            raise ValueError("state private swap participants must be canonically ordered")
        if len({item.key for item in self.private_swap_participants}) != len(self.private_swap_participants):
            raise ValueError("state private swap participants must be unique")
        for rows, identity_name, identity_attr in (
            (self.seller_auction_bids, "auction", "auction_id"),
            (self.private_swap_participants, "batch", "batch_id"),
        ):
            grouped: dict[str, list[SellerAuctionBidStateV1 | PrivateSwapParticipantStateV1]] = {}
            for row in rows:
                grouped.setdefault(str(getattr(row, identity_attr)), []).append(row)
            for identity, grouped_rows in grouped.items():
                first = grouped_rows[0]
                if any(
                    row.bond_asset != first.bond_asset
                    or row.commit_height != first.commit_height
                    or row.reveal_deadline_height != first.reveal_deadline_height
                    or row.settle_deadline_height != first.settle_deadline_height
                    for row in grouped_rows
                ):
                    raise ValueError(f"state {identity_name} {identity} has inconsistent settlement profile")
        escrow_by_id = {item.escrow_id: item for item in self.escrows}
        lifecycle_escrow_ids: set[str] = set()
        lifecycle_rows: tuple[SellerAuctionBidStateV1 | PrivateSwapParticipantStateV1, ...] = (
            *self.seller_auction_bids,
            *self.private_swap_participants,
        )
        for row in lifecycle_rows:
            if row.escrow_id in lifecycle_escrow_ids:
                raise ValueError("state lifecycle escrow ids must be unique across registries")
            lifecycle_escrow_ids.add(row.escrow_id)
            escrow = escrow_by_id.get(row.escrow_id)
            if escrow is None:
                raise ValueError("state lifecycle row must bind to an escrow record")
            participant = row.bidder if isinstance(row, SellerAuctionBidStateV1) else row.trader
            if escrow.owner != participant or escrow.asset != row.bond_asset:
                raise ValueError("state lifecycle escrow owner or asset mismatch")
            active = row.phase in (
                SellerAuctionPhaseV1.COMMIT,
                SellerAuctionPhaseV1.REVEAL,
            ) if isinstance(row, SellerAuctionBidStateV1) else row.phase in (
                PrivateSwapPhaseV1.COMMIT,
                PrivateSwapPhaseV1.REVEAL,
            )
            expected_amount = row.bond_atoms if active else 0
            if escrow.amount_atoms != expected_amount:
                raise ValueError("state lifecycle escrow amount does not match phase")
        self._require_unique_ids()
        if self.history_root_cache is None:
            object.__setattr__(
                self,
                "history_root_cache",
                _fold_root_v1("m6-history-root-v1", tuple(item.history_root for item in self.history)),
            )
        else:
            _require_root(self.history_root_cache, name="state history root cache")
        if self.nullifier_root_cache is None:
            object.__setattr__(
                self,
                "nullifier_root_cache",
                _fold_root_v1("m6-nullifier-root-v1", self.nullifiers),
            )
        else:
            _require_root(self.nullifier_root_cache, name="state nullifier root cache")
        if self.outbox_root_cache is None:
            object.__setattr__(
                self,
                "outbox_root_cache",
                _fold_root_v1("m6-outbox-root-v1", tuple(item.effect_id for item in self.outbox)),
            )
        else:
            _require_root(self.outbox_root_cache, name="state outbox root cache")

    def _require_unique_ids(self) -> None:
        ids = tuple(item.escrow_id for item in self.escrows)
        if len(set(ids)) != len(ids):
            raise ValueError("state escrow ids must be unique")
        withdrawal_ids = tuple(item.withdrawal_id for item in self.withdrawals)
        if len(set(withdrawal_ids)) != len(withdrawal_ids):
            raise ValueError("state withdrawal ids must be unique")
        outbox_ids = tuple(item.effect_id for item in self.outbox)
        if len(set(outbox_ids)) != len(outbox_ids):
            raise ValueError("state outbox effect ids must be unique")
        ack_ids = tuple(item.withdrawal_id for item in self.acknowledgments)
        if len(set(ack_ids)) != len(ack_ids):
            raise ValueError("state acknowledgment ids must be unique")

    def _state_root_canonical(self) -> dict[str, object]:
        # History, nullifiers, and finality are committed through separate roots
        # in PublicationAtomV1. Excluding those archives prevents a certificate
        # or history append from changing the head it certifies.
        return {
            "schema": SCHEMA_V1,
            "deployment": self.deployment,
            "writer_epoch": self.writer_epoch,
            "ingress_nonces": self.ingress_nonces,
            "economic_atoms": self.economic_atoms,
            "migration": self.migration,
            "escrows": self.escrows,
            "withdrawals": self.withdrawals,
            "outbox": self.outbox,
            "acknowledgments": self.acknowledgments,
            "seller_auction_bids": self.seller_auction_bids,
            "private_swap_participants": self.private_swap_participants,
        }

    @property
    def state_root(self) -> str:
        return hash_v1("m6-application-state-root-v1", self._state_root_canonical())

    @property
    def history_root(self) -> str:
        if self.history_root_cache is None:
            raise RuntimeError("state history root cache missing after validation")
        return self.history_root_cache

    @property
    def nullifier_root(self) -> str:
        if self.nullifier_root_cache is None:
            raise RuntimeError("state nullifier root cache missing after validation")
        return self.nullifier_root_cache

    @property
    def outbox_root(self) -> str:
        if self.outbox_root_cache is None:
            raise RuntimeError("state outbox root cache missing after validation")
        return self.outbox_root_cache

    def get_nonce(self, sender: str) -> int:
        for item in self.ingress_nonces:
            if item.sender == sender:
                return item.last_nonce
        return 0

    def get_ledger_allocation(
        self,
        kind: EconomicAtomKindV1,
        owner: str,
        asset: str,
        ledger_allocation: str,
    ) -> int:
        """Read one internal accounting allocation without a custody claim."""

        key = (kind.value, owner, asset, ledger_allocation)
        for item in self.economic_atoms:
            if item.key == key:
                return item.amount_atoms
        return 0

    def get_atom(self, kind: EconomicAtomKindV1, owner: str, asset: str, custody: str) -> int:
        """Return a V1 atom using its legacy wire-field vocabulary.

        New callers should use :meth:`get_ledger_allocation`.  This wrapper
        preserves V1 API and reopen compatibility without assigning a legal
        custody meaning to the allocation label.
        """

        return self.get_ledger_allocation(kind, owner, asset, custody)

    def to_canonical(self) -> dict[str, object]:
        return {
            **self._state_root_canonical(),
            "head": self.head,
            "history": self.history,
            "nullifiers": self.nullifiers,
            "finality_certificates": self.finality_certificates,
            "history_root_cache": self.history_root_cache,
            "nullifier_root_cache": self.nullifier_root_cache,
            "outbox_root_cache": self.outbox_root_cache,
        }


@dataclass(frozen=True, slots=True)
class CommandArgumentV1:
    key: str
    value: str | int

    def __post_init__(self) -> None:
        _require_token(self.key, name="command argument key")
        if not isinstance(self.value, (str, int)) or isinstance(self.value, bool):
            raise TypeError("command arguments must be strings or integers")
        if isinstance(self.value, str):
            _require_token(self.value, name=f"command argument {self.key}")
        elif not -MAX_ATOMS_V1 <= self.value <= MAX_ATOMS_V1:
            raise ValueError(f"command argument {self.key} exceeds 128-bit atom domain")

    def to_canonical(self) -> dict[str, object]:
        return {"key": self.key, "value": self.value}


_REQUIRED_COMMAND_FIELDS: Final[dict[GlobalCommandKindV1, frozenset[str]]] = {
    GlobalCommandKindV1.SPOT_SWAP: frozenset({"asset_in", "asset_out", "amount_in_atoms", "amount_out_atoms", "pool"}),
    GlobalCommandKindV1.LP_ADD: frozenset({"asset", "amount_atoms", "pool", "lp_shares_atoms"}),
    GlobalCommandKindV1.LP_REMOVE: frozenset({"asset", "amount_atoms", "pool", "lp_shares_atoms"}),
    GlobalCommandKindV1.ZUSD_BORROW: frozenset({"collateral_asset", "collateral_atoms", "amount_atoms", "vault_id"}),
    GlobalCommandKindV1.ZUSD_REPAY: frozenset({"amount_atoms", "vault_id"}),
    GlobalCommandKindV1.ZUSD_REDEEM: frozenset({"amount_atoms", "collateral_asset", "vault_id"}),
    GlobalCommandKindV1.ZUSD_LIQUIDATE: frozenset({"vault_id", "debtor", "debt_atoms", "collateral_asset", "collateral_atoms"}),
    GlobalCommandKindV1.STABILITY_POOL_DEPOSIT: frozenset({"amount_atoms"}),
    GlobalCommandKindV1.STABILITY_POOL_WITHDRAW: frozenset({"amount_atoms"}),
    GlobalCommandKindV1.ZUSD_REDISTRIBUTE: frozenset({"amount_atoms", "collateral_asset", "collateral_atoms", "source_vault"}),
    GlobalCommandKindV1.PERP_OPEN: frozenset({"market", "margin_atoms", "size_atoms", "price_e8"}),
    GlobalCommandKindV1.PERP_CLOSE: frozenset({"market", "size_atoms", "pnl_atoms"}),
    GlobalCommandKindV1.PERP_FUNDING: frozenset({"market", "amount_atoms"}),
    GlobalCommandKindV1.PERP_LIQUIDATE: frozenset({"market", "margin_atoms", "insurance_atoms"}),
    GlobalCommandKindV1.ORACLE_SUBMIT: frozenset({"oracle_id", "price_e8", "bond_atoms"}),
    GlobalCommandKindV1.ORACLE_DISPUTE: frozenset({"oracle_id", "bond_atoms"}),
    GlobalCommandKindV1.PROTOCOL_BUY_AND_BURN: frozenset({"asset", "amount_atoms"}),
    GlobalCommandKindV1.ZRPF_PROVER_REWARD: frozenset({"prover", "reward_asset", "amount_atoms"}),
    GlobalCommandKindV1.SELLER_AUCTION_COMMIT: frozenset({"auction_id", "bond_asset", "bond_atoms", "commitment", "commit_height", "reveal_deadline_height", "settle_deadline_height"}),
    GlobalCommandKindV1.SELLER_AUCTION_REVEAL: frozenset({"auction_id", "inventory_asset", "quantity_atoms", "price_e8", "nonce"}),
    GlobalCommandKindV1.SELLER_AUCTION_SETTLE: frozenset({"auction_id", "clearing_price_e8"}),
    GlobalCommandKindV1.SELLER_AUCTION_CANCEL: frozenset({"auction_id"}),
    GlobalCommandKindV1.SELLER_AUCTION_EXPIRE: frozenset({"auction_id"}),
    GlobalCommandKindV1.PRIVATE_SWAP_COMMIT: frozenset({"batch_id", "bond_asset", "bond_atoms", "commitment", "commit_height", "reveal_deadline_height", "settle_deadline_height"}),
    GlobalCommandKindV1.PRIVATE_SWAP_REVEAL: frozenset({"batch_id", "asset_in", "amount_in_atoms", "asset_out", "amount_out_atoms", "nonce"}),
    GlobalCommandKindV1.PRIVATE_SWAP_SETTLE: frozenset({"batch_id", "clearing_root"}),
    GlobalCommandKindV1.PRIVATE_SWAP_CANCEL: frozenset({"batch_id"}),
    GlobalCommandKindV1.PRIVATE_SWAP_EXPIRE: frozenset({"batch_id"}),
    GlobalCommandKindV1.TAU_ESCROW_DEPOSIT: frozenset({"deposit_id", "asset", "amount_atoms", "tau_transaction_root", "tau_finality_root", "tau_profile_root"}),
    GlobalCommandKindV1.TAU_WITHDRAWAL: frozenset({"withdrawal_id", "asset", "amount_atoms", "destination"}),
    GlobalCommandKindV1.TAU_WITHDRAWAL_ACK: frozenset({"withdrawal_id", "ack_root", "tau_receipt_root"}),
    GlobalCommandKindV1.FALLBACK_ACTIVATE: frozenset({"checkpoint_root"}),
    GlobalCommandKindV1.TAU_REJOIN: frozenset({"checkpoint_root", "compatible_profile_root"}),
}


_OPTIONAL_COMMAND_FIELDS: Final[dict[GlobalCommandKindV1, frozenset[str]]] = {
    GlobalCommandKindV1.SPOT_SWAP: frozenset({"fee_atoms", "recipient"}),
    GlobalCommandKindV1.SELLER_AUCTION_CANCEL: frozenset({"commitment"}),
    GlobalCommandKindV1.PRIVATE_SWAP_CANCEL: frozenset({"commitment"}),
    GlobalCommandKindV1.TAU_ESCROW_DEPOSIT: frozenset({"tau_finality_height"}),
    GlobalCommandKindV1.TAU_WITHDRAWAL_ACK: frozenset({"tau_receipt_height"}),
}


_ALLOWED_COMMAND_FIELDS: Final[dict[GlobalCommandKindV1, frozenset[str]]] = {
    kind: _REQUIRED_COMMAND_FIELDS[kind] | _OPTIONAL_COMMAND_FIELDS.get(kind, frozenset())
    for kind in GlobalCommandKindV1
}


@dataclass(frozen=True, slots=True)
class GlobalCommandV1:
    kind: GlobalCommandKindV1
    command_id: str
    sender: str
    nonce: int
    payload: tuple[CommandArgumentV1, ...] | Mapping[str, str | int] = ()
    created_height: int = 0

    def __post_init__(self) -> None:
        if not isinstance(self.kind, GlobalCommandKindV1):
            raise TypeError("command kind is not in the closed launch registry")
        _require_root(self.command_id, name="command id")
        _require_token(self.sender, name="command sender")
        _require_positive_int(self.nonce, name="command nonce")
        if self.nonce > MAX_ATOMS_V1:
            raise ValueError("command nonce exceeds 128-bit atom domain")
        _require_nonnegative_int(self.created_height, name="command created height")
        raw_payload = self.payload
        if isinstance(raw_payload, Mapping):
            normalized = tuple(
                CommandArgumentV1(key=key, value=value)
                for key, value in sorted(raw_payload.items(), key=lambda item: item[0])
            )
            object.__setattr__(self, "payload", normalized)
        elif isinstance(raw_payload, tuple):
            normalized = raw_payload
        else:
            raise TypeError("command payload must be an immutable tuple or mapping at decode")
        if len(normalized) > MAX_ARGUMENTS:
            raise ValueError("command payload exceeds argument capacity")
        if any(not isinstance(item, CommandArgumentV1) for item in normalized):
            raise TypeError("command payload contains an invalid argument")
        keys = tuple(item.key for item in normalized)
        if keys != tuple(sorted(set(keys))):
            raise ValueError("command payload keys must be sorted and unique")
        required = _REQUIRED_COMMAND_FIELDS[self.kind]
        if not required.issubset(keys):
            raise ValueError(f"command payload is missing fields: {sorted(required - set(keys))}")
        unknown = set(keys) - _ALLOWED_COMMAND_FIELDS[self.kind]
        if unknown:
            raise ValueError(f"command payload contains unknown fields: {sorted(unknown)}")

    def payload_value(self, key: str, default: str | int | None = None) -> str | int | None:
        arguments = cast(tuple[CommandArgumentV1, ...], self.payload)
        for argument in arguments:
            if argument.key == key:
                return argument.value
        return default

    @property
    def command_hash(self) -> str:
        return hash_v1("m6-global-command-v1", self.to_canonical())

    @property
    def nonce_identity(self) -> str:
        return f"{self.sender}:{self.nonce}"

    def to_canonical(self) -> dict[str, object]:
        arguments = cast(tuple[CommandArgumentV1, ...], self.payload)
        return {
            "schema": SCHEMA_V1,
            "kind": self.kind,
            "command_id": self.command_id,
            "sender": self.sender,
            "nonce": self.nonce,
            "created_height": self.created_height,
            "payload": {item.key: item.value for item in arguments},
        }


class CommandDecodeError(ValueError):
    """Malformed or ambiguous command bytes; no nonce may be consumed."""


def _reject_json_constant(value: str) -> object:
    raise CommandDecodeError(f"JSON constant is forbidden: {value}")


def _reject_duplicate_json_keys(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise CommandDecodeError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def decode_global_command_v1(raw: bytes) -> GlobalCommandV1:
    if not isinstance(raw, bytes):
        raise TypeError("raw command must be bytes")
    try:
        value = json.loads(
            raw.decode("utf-8"),
            object_pairs_hook=_reject_duplicate_json_keys,
            parse_constant=_reject_json_constant,
            parse_float=lambda _value: (_ for _ in ()).throw(CommandDecodeError("floats are forbidden")),
        )
    except (UnicodeDecodeError, json.JSONDecodeError, CommandDecodeError) as exc:
        raise CommandDecodeError(str(exc)) from exc
    if not isinstance(value, dict) or set(value) != {
        "schema",
        "kind",
        "command_id",
        "sender",
        "nonce",
        "created_height",
        "payload",
    }:
        raise CommandDecodeError("command schema keys mismatch")
    if value["schema"] != SCHEMA_V1 or not isinstance(value["payload"], dict):
        raise CommandDecodeError("command schema mismatch")
    try:
        kind = GlobalCommandKindV1(value["kind"])
        command = GlobalCommandV1(
            kind=kind,
            command_id=value["command_id"],
            sender=value["sender"],
            nonce=value["nonce"],
            created_height=value["created_height"],
            payload=value["payload"],
        )
    except (KeyError, TypeError, ValueError) as exc:
        raise CommandDecodeError("command typed validation failed") from exc
    if canonical_bytes_v1(command) != raw:
        raise CommandDecodeError("command bytes are not canonical")
    return command


@dataclass(frozen=True, slots=True)
class RejectNoCommitV1:
    reason: AdmissionRejectReasonV1
    pre_state_root: str
    command_hash: str | None = None

    def __post_init__(self) -> None:
        if not isinstance(self.reason, AdmissionRejectReasonV1):
            raise TypeError("no-commit reject reason is not closed")
        _require_root(self.pre_state_root, name="reject pre-state root", allow_zero=True)
        if self.command_hash is not None:
            _require_root(self.command_hash, name="reject command hash")

    @property
    def committed(self) -> bool:
        return False

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": SCHEMA_V1,
            "outcome": "reject_no_commit",
            "reason": self.reason,
            "pre_state_root": self.pre_state_root,
            "command_hash": self.command_hash,
        }


def admit_global_command_v1(
    raw: object,
    *,
    pre_state_root: str,
) -> GlobalCommandV1 | RejectNoCommitV1:
    """Convert untrusted command bytes into a typed command or no-commit reject."""

    try:
        if not isinstance(raw, bytes):
            raise TypeError("raw command must be bytes")
        return decode_global_command_v1(raw)
    except (CommandDecodeError, TypeError, ValueError):
        return RejectNoCommitV1(
            reason=AdmissionRejectReasonV1.MALFORMED_COMMAND,
            pre_state_root=pre_state_root,
        )


@dataclass(frozen=True, slots=True)
class AcceptCandidateV1:
    context: AuthenticatedExecutionContextV1
    command: GlobalCommandV1
    pre_state_root: str
    post_state: M6ApplicationStateV1
    value_delta: ValueDeltaCertificateV1
    history_atom: HistoryAtomV1
    publication_atom: PublicationAtomV1
    outbox_atoms: tuple[OutboxAtomV1, ...]
    business_status: BusinessStatusV1
    business_reject_reason: BusinessRejectReasonV1 | None

    def __post_init__(self) -> None:
        _require_root(self.pre_state_root, name="candidate pre-state root")
        if not isinstance(self.context, AuthenticatedExecutionContextV1):
            raise TypeError("candidate context is not typed")
        if not isinstance(self.command, GlobalCommandV1):
            raise TypeError("candidate command is not typed")
        if self.context.sender != self.command.sender:
            raise ValueError("candidate context sender binding mismatch")
        if self.context.nonce != self.command.nonce:
            raise ValueError("candidate context nonce binding mismatch")
        if not isinstance(self.post_state, M6ApplicationStateV1):
            raise TypeError("candidate post-state is not typed")
        for field_name, value in (
            ("value_delta", self.value_delta),
            ("history_atom", self.history_atom),
            ("publication_atom", self.publication_atom),
        ):
            if not isinstance(value, (ValueDeltaCertificateV1, HistoryAtomV1, PublicationAtomV1)):
                raise TypeError(f"candidate {field_name} is not typed")
        if self.publication_atom.post_state_root != self.post_state.state_root:
            raise ValueError("candidate publication/post-state root mismatch")
        if self.publication_atom.execution_context_root != self.context.authentication_root:
            raise ValueError("candidate publication/context root mismatch")
        if self.value_delta.post_state_root != self.post_state.state_root:
            raise ValueError("candidate delta/post-state root mismatch")
        if self.history_atom.post_state_root != self.post_state.state_root:
            raise ValueError("candidate history/post-state root mismatch")
        if self.history_atom.command_hash != self.command.command_hash:
            raise ValueError("candidate history command binding mismatch")
        if self.value_delta.command_hash != self.command.command_hash:
            raise ValueError("candidate delta command binding mismatch")
        if self.history_atom.outcome is not self.business_status:
            raise ValueError("candidate history business status mismatch")
        if self.history_atom.business_reject_reason is not self.business_reject_reason:
            raise ValueError("candidate history business reject reason mismatch")
        if self.publication_atom.business_status is not self.business_status:
            raise ValueError("candidate publication business status mismatch")
        if self.publication_atom.business_reject_reason is not self.business_reject_reason:
            raise ValueError("candidate publication business reject reason mismatch")
        if self.business_status is BusinessStatusV1.ACCEPTED and self.business_reject_reason is not None:
            raise ValueError("accepted candidate cannot have a business reject reason")
        if self.business_status is BusinessStatusV1.REJECTED_COMMITTED and self.business_reject_reason is None:
            raise ValueError("committed rejection requires a business reject reason")
        if self.outbox_atoms:
            expected_outbox_ids = tuple(
                item.effect_id for item in self.post_state.outbox[-len(self.outbox_atoms) :]
            )
            if tuple(item.effect_id for item in self.outbox_atoms) != expected_outbox_ids:
                raise ValueError("candidate outbox projection mismatch")

    @property
    def candidate_id(self) -> str:
        return self.publication_atom.candidate_id

    @property
    def committed(self) -> bool:
        return True

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": SCHEMA_V1,
            "outcome": "accept_candidate",
            "context": self.context,
            "command": self.command,
            "pre_state_root": self.pre_state_root,
            "post_state": self.post_state,
            "value_delta": self.value_delta,
            "history_atom": self.history_atom,
            "publication_atom": self.publication_atom,
            "outbox_atoms": self.outbox_atoms,
            "business_status": self.business_status,
            "business_reject_reason": self.business_reject_reason,
        }


GlobalOutcomeV1: TypeAlias = RejectNoCommitV1 | AcceptCandidateV1


@dataclass(frozen=True, slots=True)
class SellerInventoryAuctionCommitV1:
    auction_id: str
    seller: str
    inventory_asset: str
    inventory_amount_atoms: int
    bond_asset: str
    bond_atoms: int
    commitment: str
    phase: SellerAuctionPhaseV1 = SellerAuctionPhaseV1.COMMIT

    def __post_init__(self) -> None:
        for field_name, value in (("auction_id", self.auction_id), ("seller", self.seller), ("inventory_asset", self.inventory_asset), ("bond_asset", self.bond_asset), ("commitment", self.commitment)):
            _require_token(value, name=f"seller auction {field_name}")
        _require_positive_int(self.inventory_amount_atoms, name="seller inventory amount")
        _require_positive_int(self.bond_atoms, name="seller auction bond")
        _require_root(self.commitment, name="seller auction commitment")
        if self.phase is not SellerAuctionPhaseV1.COMMIT:
            raise ValueError("seller auction commit must start in commit phase")

    def to_canonical(self) -> dict[str, object]:
        return {
            "auction_id": self.auction_id,
            "seller": self.seller,
            "inventory_asset": self.inventory_asset,
            "inventory_amount_atoms": self.inventory_amount_atoms,
            "bond_asset": self.bond_asset,
            "bond_atoms": self.bond_atoms,
            "commitment": self.commitment,
            "phase": self.phase,
        }


@dataclass(frozen=True, slots=True)
class SellerInventoryAuctionRevealV1:
    auction_id: str
    seller: str
    quantity_atoms: int
    limit_price_e8: int
    nonce: int
    commitment: str
    phase: SellerAuctionPhaseV1 = SellerAuctionPhaseV1.REVEAL

    def __post_init__(self) -> None:
        _require_token(self.auction_id, name="seller reveal auction id")
        _require_token(self.seller, name="seller reveal seller")
        _require_positive_int(self.quantity_atoms, name="seller reveal quantity")
        _require_positive_int(self.limit_price_e8, name="seller reveal price")
        _require_positive_int(self.nonce, name="seller reveal nonce")
        _require_root(self.commitment, name="seller reveal commitment")
        if self.phase is not SellerAuctionPhaseV1.REVEAL:
            raise ValueError("seller auction reveal must be in reveal phase")

    def to_canonical(self) -> dict[str, object]:
        return {
            "auction_id": self.auction_id,
            "seller": self.seller,
            "quantity_atoms": self.quantity_atoms,
            "limit_price_e8": self.limit_price_e8,
            "nonce": self.nonce,
            "commitment": self.commitment,
            "phase": self.phase,
        }


@dataclass(frozen=True, slots=True)
class PrivateSwapCommitV1:
    batch_id: str
    trader: str
    bond_asset: str
    bond_atoms: int
    commitment: str
    phase: PrivateSwapPhaseV1 = PrivateSwapPhaseV1.COMMIT

    def __post_init__(self) -> None:
        for field_name, value in (("batch_id", self.batch_id), ("trader", self.trader), ("bond_asset", self.bond_asset), ("commitment", self.commitment)):
            _require_token(value, name=f"private swap {field_name}")
        _require_positive_int(self.bond_atoms, name="private swap bond")
        _require_root(self.commitment, name="private swap commitment")
        if self.phase is not PrivateSwapPhaseV1.COMMIT:
            raise ValueError("private swap commit must start in commit phase")

    def to_canonical(self) -> dict[str, object]:
        return {
            "batch_id": self.batch_id,
            "trader": self.trader,
            "bond_asset": self.bond_asset,
            "bond_atoms": self.bond_atoms,
            "commitment": self.commitment,
            "phase": self.phase,
        }


@dataclass(frozen=True, slots=True)
class PrivateSwapRevealV1:
    batch_id: str
    trader: str
    asset_in: str
    amount_in_atoms: int
    asset_out: str
    amount_out_atoms: int
    nonce: int
    commitment: str
    phase: PrivateSwapPhaseV1 = PrivateSwapPhaseV1.REVEAL

    def __post_init__(self) -> None:
        for field_name, value in (("batch_id", self.batch_id), ("trader", self.trader), ("asset_in", self.asset_in), ("asset_out", self.asset_out), ("commitment", self.commitment)):
            _require_token(value, name=f"private reveal {field_name}")
        _require_positive_int(self.amount_in_atoms, name="private reveal input")
        _require_positive_int(self.amount_out_atoms, name="private reveal output")
        _require_positive_int(self.nonce, name="private reveal nonce")
        _require_root(self.commitment, name="private reveal commitment")
        if self.phase is not PrivateSwapPhaseV1.REVEAL:
            raise ValueError("private swap reveal must be in reveal phase")

    def to_canonical(self) -> dict[str, object]:
        return {
            "batch_id": self.batch_id,
            "trader": self.trader,
            "asset_in": self.asset_in,
            "amount_in_atoms": self.amount_in_atoms,
            "asset_out": self.asset_out,
            "amount_out_atoms": self.amount_out_atoms,
            "nonce": self.nonce,
            "commitment": self.commitment,
            "phase": self.phase,
        }


@dataclass(frozen=True, slots=True)
class ZRPFChunkStatementV1:
    profile: str
    promotion_subject_root: str
    writer_epoch: int
    ordinal: int
    pre_state_root: str
    post_state_root: str
    command_hashes: tuple[str, ...]
    nonce_identities: tuple[str, ...]
    value_delta_root: str
    history_root: str
    nullifier_root: str
    outbox_root: str
    verifier_image: str

    def __post_init__(self) -> None:
        if self.profile != ZRPF_PROFILE_V1:
            raise ValueError("ZRPF chunk profile mismatch")
        _require_root(self.promotion_subject_root, name="ZRPF chunk subject")
        _require_nonnegative_int(self.writer_epoch, name="ZRPF chunk writer epoch")
        _require_nonnegative_int(self.ordinal, name="ZRPF chunk ordinal")
        _require_root(self.pre_state_root, name="ZRPF chunk pre-state", allow_zero=True)
        _require_root(self.post_state_root, name="ZRPF chunk post-state")
        if len(self.command_hashes) != ZRPF_COMMANDS_PER_LEAF_V1:
            raise ValueError("ZRPF chunk must contain exactly sixteen commands")
        for value in self.command_hashes:
            _require_root(value, name="ZRPF chunk command hash")
        if len(self.nonce_identities) != len(self.command_hashes):
            raise ValueError("ZRPF chunk command/nonce count mismatch")
        _ordered_tokens(self.nonce_identities, name="ZRPF chunk nonce identities", max_items=ZRPF_COMMANDS_PER_LEAF_V1)
        for field_name, value in (
            ("value_delta_root", self.value_delta_root),
            ("history_root", self.history_root),
            ("nullifier_root", self.nullifier_root),
            ("outbox_root", self.outbox_root),
        ):
            _require_root(value, name=f"ZRPF chunk {field_name}")
        _require_image_id(self.verifier_image, name="ZRPF chunk verifier image")

    @property
    def statement_root(self) -> str:
        return hash_v1("m6-zrpf-chunk-statement-v1", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            "profile": self.profile,
            "promotion_subject_root": self.promotion_subject_root,
            "writer_epoch": self.writer_epoch,
            "ordinal": self.ordinal,
            "pre_state_root": self.pre_state_root,
            "post_state_root": self.post_state_root,
            "command_hashes": self.command_hashes,
            "nonce_identities": self.nonce_identities,
            "value_delta_root": self.value_delta_root,
            "history_root": self.history_root,
            "nullifier_root": self.nullifier_root,
            "outbox_root": self.outbox_root,
            "verifier_image": self.verifier_image,
        }


@dataclass(frozen=True, slots=True)
class ZRPFRootJournalV1:
    profile: str
    promotion_subject_root: str
    writer_epoch: int
    pre_state_root: str
    post_state_root: str
    command_count: int
    chunk_statement_roots: tuple[str, ...]
    aggregate_statement_roots: tuple[str, ...]
    command_root: str
    nonce_root: str
    value_delta_root: str
    history_root: str
    nullifier_root: str
    outbox_root: str
    data_availability_root: str
    verifier_image: str

    def __post_init__(self) -> None:
        if self.profile != ZRPF_PROFILE_V1:
            raise ValueError("ZRPF root profile mismatch")
        _require_root(self.promotion_subject_root, name="ZRPF root subject")
        _require_nonnegative_int(self.writer_epoch, name="ZRPF root writer epoch")
        _require_root(self.pre_state_root, name="ZRPF root pre-state", allow_zero=True)
        _require_root(self.post_state_root, name="ZRPF root post-state")
        if self.command_count != ZRPF_COMMAND_COUNT_V1:
            raise ValueError("ZRPF root command count must be 1024")
        if len(self.chunk_statement_roots) != ZRPF_LEAF_COUNT_V1:
            raise ValueError("ZRPF root must contain 64 chunks")
        if len(self.aggregate_statement_roots) != ZRPF_AGGREGATE_COUNT_V1:
            raise ValueError("ZRPF root must contain eight aggregates")
        for name, values in (("chunk roots", self.chunk_statement_roots), ("aggregate roots", self.aggregate_statement_roots)):
            for value in values:
                _require_root(value, name=f"ZRPF {name} entry")
        for field_name, value in (
            ("command_root", self.command_root),
            ("nonce_root", self.nonce_root),
            ("value_delta_root", self.value_delta_root),
            ("history_root", self.history_root),
            ("nullifier_root", self.nullifier_root),
            ("outbox_root", self.outbox_root),
            ("data_availability_root", self.data_availability_root),
        ):
            _require_root(value, name=f"ZRPF root {field_name}")
        _require_image_id(self.verifier_image, name="ZRPF root verifier image")

    @property
    def journal_root(self) -> str:
        return hash_v1("m6-zrpf-root-journal-v1", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            "profile": self.profile,
            "promotion_subject_root": self.promotion_subject_root,
            "writer_epoch": self.writer_epoch,
            "pre_state_root": self.pre_state_root,
            "post_state_root": self.post_state_root,
            "command_count": self.command_count,
            "chunk_statement_roots": self.chunk_statement_roots,
            "aggregate_statement_roots": self.aggregate_statement_roots,
            "command_root": self.command_root,
            "nonce_root": self.nonce_root,
            "value_delta_root": self.value_delta_root,
            "history_root": self.history_root,
            "nullifier_root": self.nullifier_root,
            "outbox_root": self.outbox_root,
            "data_availability_root": self.data_availability_root,
            "verifier_image": self.verifier_image,
        }


class _ZRPFVerificationReceiptToken:
    pass


_ZRPF_VERIFICATION_RECEIPT_TOKEN = _ZRPFVerificationReceiptToken()


class M6ZRPFVerificationReceiptV1:
    """Opaque proof receipt required before a ZRPF root becomes verified."""

    _promotion_subject_root: str
    _profile: str
    _verifier_image: str
    _journal_root: str
    _data_availability_root: str
    _attestation_root: str
    _sealed: bool

    __slots__ = (
        "_promotion_subject_root",
        "_profile",
        "_verifier_image",
        "_journal_root",
        "_data_availability_root",
        "_attestation_root",
        "_sealed",
    )

    def __init__(
        self,
        token: object,
        *,
        promotion_subject_root: str,
        profile: str,
        verifier_image: str,
        journal_root: str,
        data_availability_root: str,
        attestation_root: str,
    ) -> None:
        if token is not _ZRPF_VERIFICATION_RECEIPT_TOKEN:
            raise TypeError("M6 ZRPF verification receipt is verifier-created")
        _require_root(promotion_subject_root, name="ZRPF receipt subject root")
        _require_root(journal_root, name="ZRPF receipt journal root")
        _require_root(data_availability_root, name="ZRPF receipt DA root")
        _require_image_id(verifier_image, name="ZRPF receipt verifier image")
        if not isinstance(profile, str) or not profile:
            raise ValueError("ZRPF receipt profile must be non-empty")
        _require_root(attestation_root, name="ZRPF receipt attestation root")
        object.__setattr__(self, "_promotion_subject_root", promotion_subject_root)
        object.__setattr__(self, "_profile", profile)
        object.__setattr__(self, "_verifier_image", verifier_image)
        object.__setattr__(self, "_journal_root", journal_root)
        object.__setattr__(self, "_data_availability_root", data_availability_root)
        object.__setattr__(self, "_attestation_root", attestation_root)
        object.__setattr__(self, "_sealed", True)

    @property
    def promotion_subject_root(self) -> str:
        return self._promotion_subject_root

    @property
    def profile(self) -> str:
        return self._profile

    @property
    def verifier_image(self) -> str:
        return self._verifier_image

    @property
    def journal_root(self) -> str:
        return self._journal_root

    @property
    def data_availability_root(self) -> str:
        return self._data_availability_root

    @property
    def attestation_root(self) -> str:
        return self._attestation_root

    @property
    def receipt_root(self) -> str:
        return hash_v1(
            "m6-zrpf-verification-receipt-v1",
            {
                "promotion_subject_root": self.promotion_subject_root,
                "profile": self.profile,
                "verifier_image": self.verifier_image,
                "journal_root": self.journal_root,
                "data_availability_root": self.data_availability_root,
                "attestation_root": self.attestation_root,
            },
        )

    def to_canonical(self) -> dict[str, object]:
        """Expose the exact receipt projection without granting authority."""

        return {
            "promotion_subject_root": self.promotion_subject_root,
            "profile": self.profile,
            "verifier_image": self.verifier_image,
            "journal_root": self.journal_root,
            "data_availability_root": self.data_availability_root,
            "attestation_root": self.attestation_root,
            "receipt_root": self.receipt_root,
        }

    def __setattr__(self, name: str, value: object) -> None:
        if getattr(self, "_sealed", False):
            raise AttributeError("M6 ZRPF verification receipt is immutable")
        object.__setattr__(self, name, value)


@dataclass(frozen=True, slots=True)
class M6ZRPFVerificationReceiptRecordV1:
    """Durable, non-authorizing projection of an accepted ZRPF receipt.

    This value preserves the verifier output and its hash across process
    restart.  It cannot create ``VerifiedZRPFRootV1`` and does not replace
    cryptographic receipt verification by the external proof verifier.
    """

    promotion_subject_root: str
    profile: str
    verifier_image: str
    journal_root: str
    data_availability_root: str
    attestation_root: str

    def __post_init__(self) -> None:
        _require_root(self.promotion_subject_root, name="ZRPF receipt record subject root")
        if not isinstance(self.profile, str) or not self.profile:
            raise ValueError("ZRPF receipt record profile must be non-empty")
        _require_image_id(self.verifier_image, name="ZRPF receipt record verifier image")
        _require_root(self.journal_root, name="ZRPF receipt record journal root")
        _require_root(self.data_availability_root, name="ZRPF receipt record DA root")
        _require_root(self.attestation_root, name="ZRPF receipt record attestation root")

    @classmethod
    def from_verified(
        cls,
        receipt: M6ZRPFVerificationReceiptV1,
    ) -> M6ZRPFVerificationReceiptRecordV1:
        if not isinstance(receipt, M6ZRPFVerificationReceiptV1):
            raise TypeError("ZRPF receipt record requires a typed verifier receipt")
        return cls(
            promotion_subject_root=receipt.promotion_subject_root,
            profile=receipt.profile,
            verifier_image=receipt.verifier_image,
            journal_root=receipt.journal_root,
            data_availability_root=receipt.data_availability_root,
            attestation_root=receipt.attestation_root,
        )

    @property
    def receipt_root(self) -> str:
        return hash_v1(
            "m6-zrpf-verification-receipt-v1",
            {
                "promotion_subject_root": self.promotion_subject_root,
                "profile": self.profile,
                "verifier_image": self.verifier_image,
                "journal_root": self.journal_root,
                "data_availability_root": self.data_availability_root,
                "attestation_root": self.attestation_root,
            },
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": ZRPF_RECEIPT_RECORD_SCHEMA_V1,
            "promotion_subject_root": self.promotion_subject_root,
            "profile": self.profile,
            "verifier_image": self.verifier_image,
            "journal_root": self.journal_root,
            "data_availability_root": self.data_availability_root,
            "attestation_root": self.attestation_root,
            "receipt_root": self.receipt_root,
        }


class _VerifiedZRPFToken:
    pass


_VERIFIED_ZRPF_TOKEN = _VerifiedZRPFToken()


class VerifiedZRPFRootV1:
    """Opaque root evidence created by the structural verifier only.

    Python cannot provide Rust's constructor privacy.  The private token still
    prevents ordinary callers from constructing this object accidentally.  The
    verifier in this repository checks typed journal structure and bindings;
    it does not replace a cryptographic RISC0 receipt verifier.
    """

    _journal: ZRPFRootJournalV1
    _candidate_id: str
    _post_state: M6ApplicationStateV1
    _execution_batch: object
    _proof_receipt: M6ZRPFVerificationReceiptV1
    _sealed: bool
    __slots__ = (
        "_journal",
        "_candidate_id",
        "_post_state",
        "_execution_batch",
        "_proof_receipt",
        "_sealed",
    )

    def __init__(
        self,
        token: _VerifiedZRPFToken,
        journal: ZRPFRootJournalV1,
        candidate_id: str,
        post_state: M6ApplicationStateV1,
        execution_batch: object,
        proof_receipt: M6ZRPFVerificationReceiptV1,
    ) -> None:
        if token is not _VERIFIED_ZRPF_TOKEN:
            raise TypeError("VerifiedZRPFRootV1 is verifier-created")
        if not isinstance(proof_receipt, M6ZRPFVerificationReceiptV1):
            raise TypeError("VerifiedZRPFRootV1 requires a typed proof receipt")
        if (
            proof_receipt.promotion_subject_root != journal.promotion_subject_root
            or proof_receipt.profile != journal.profile
            or proof_receipt.verifier_image != journal.verifier_image
            or proof_receipt.journal_root != journal.journal_root
            or proof_receipt.data_availability_root != journal.data_availability_root
        ):
            raise ValueError("VerifiedZRPFRootV1 proof receipt binding mismatch")
        object.__setattr__(self, "_journal", journal)
        object.__setattr__(self, "_candidate_id", candidate_id)
        object.__setattr__(self, "_post_state", post_state)
        object.__setattr__(self, "_execution_batch", execution_batch)
        object.__setattr__(self, "_proof_receipt", proof_receipt)
        object.__setattr__(self, "_sealed", True)

    @property
    def journal(self) -> ZRPFRootJournalV1:
        return self._journal

    @property
    def candidate_id(self) -> str:
        return self._candidate_id

    @property
    def post_state(self) -> M6ApplicationStateV1:
        return self._post_state

    @property
    def execution_batch(self) -> object:
        """The exact batch that the verifier checked before issuing this handle."""

        return self._execution_batch

    @property
    def proof_receipt(self) -> M6ZRPFVerificationReceiptV1:
        return self._proof_receipt

    def __setattr__(self, name: str, value: object) -> None:
        if getattr(self, "_sealed", False):
            raise AttributeError("verified ZRPF root is immutable")
        object.__setattr__(self, name, value)

    def __repr__(self) -> str:
        return f"VerifiedZRPFRootV1(journal_root={self.journal.journal_root!r}, candidate_id={self.candidate_id!r})"


def initial_application_state_v1(subject: M6PromotionSubjectV1) -> M6ApplicationStateV1:
    migration = MigrationStateV1(
        phase=MigrationPhaseV1.NORMAL,
        authority_epoch=subject.writer_epoch,
        previous_authority_root=ZERO_ROOT_V1,
        checkpoint_root=ZERO_ROOT_V1,
        quiescent=False,
    )
    return M6ApplicationStateV1(
        deployment=subject.deployment,
        head=ZERO_ROOT_V1,
        writer_epoch=subject.writer_epoch,
        migration=migration,
    )


def validate_state_commitments_v1(state: M6ApplicationStateV1) -> None:
    """Recompute archive roots at a shell/reopen boundary.

    The transition carries append-bound roots for bounded batch performance.
    A fresh-process reopen or external state load must call this function so a
    caller cannot replace history, nullifiers, or outbox rows while retaining a
    stale derived root.
    """

    expected_history = _fold_root_v1(
        "m6-history-root-v1",
        tuple(item.history_root for item in state.history),
    )
    expected_nullifiers = _fold_root_v1("m6-nullifier-root-v1", state.nullifiers)
    expected_outbox = _fold_root_v1(
        "m6-outbox-root-v1",
        tuple(item.effect_id for item in state.outbox),
    )
    if state.history_root != expected_history:
        raise ValueError("state history root cache mismatch")
    if state.nullifier_root != expected_nullifiers:
        raise ValueError("state nullifier root cache mismatch")
    if state.outbox_root != expected_outbox:
        raise ValueError("state outbox root cache mismatch")
    if state.migration.authority_epoch != state.writer_epoch:
        raise ValueError("state writer epoch and migration authority epoch mismatch")


def validate_economic_state_v1(state: M6ApplicationStateV1) -> None:
    """Validate the closed economic relations required at an authority boundary.

    ``validate_state_commitments_v1`` protects archive roots.  This companion
    check protects the small set of economic relations implemented by the
    current research profile before a state can become commit-port or durable
    authority.  Unimplemented economic modules remain outside this validator
    and are disabled by the transition registry.
    """

    if not isinstance(state, M6ApplicationStateV1):
        raise TypeError("economic state is not typed")
    validate_state_commitments_v1(state)

    atoms = {atom.key: atom.amount_atoms for atom in state.economic_atoms}

    aggregate_amounts: dict[tuple[str, str, str], int] = {}
    for atom in state.economic_atoms:
        aggregate_key = (atom.kind.value, atom.asset, atom.custody)
        aggregate_amounts[aggregate_key] = aggregate_amounts.get(aggregate_key, 0) + atom.amount_atoms
        if aggregate_amounts[aggregate_key] > MAX_ATOMS_V1:
            raise ValueError(
                "economic aggregate exceeds 128-bit atom domain: "
                f"kind={atom.kind.value}, asset={atom.asset}, custody={atom.custody}"
            )

    def amount(kind: EconomicAtomKindV1, owner: str, asset: str, custody: str) -> int:
        return atoms.get((kind.value, owner, asset, custody), 0)

    def total(
        kind: EconomicAtomKindV1,
        *,
        asset: str | None = None,
        custody: str | None = None,
    ) -> int:
        return sum(
            atom.amount_atoms
            for atom in state.economic_atoms
            if atom.kind is kind
            and (asset is None or atom.asset == asset)
            and (custody is None or atom.custody == custody)
        )

    zusd_supply_rows = [
        atom
        for atom in state.economic_atoms
        if atom.kind is EconomicAtomKindV1.SUPPLY and atom.asset == "zUSD"
    ]
    unsupported_supply_rows = [
        atom
        for atom in state.economic_atoms
        if atom.kind is EconomicAtomKindV1.SUPPLY and atom.asset != "zUSD"
    ]
    if unsupported_supply_rows:
        assets = sorted({atom.asset for atom in unsupported_supply_rows})
        raise ValueError(
            "non-zUSD supply requires a mounted issuance kernel: "
            f"assets={assets}"
        )
    if any(
        atom.owner != "__supply__" or atom.custody != "ledger"
        for atom in zusd_supply_rows
    ):
        raise ValueError("zUSD supply must have the canonical monetary-kernel owner")
    zusd_supply = amount(EconomicAtomKindV1.SUPPLY, "__supply__", "zUSD", "ledger")

    zusd_debt = 0
    for atom in state.economic_atoms:
        if atom.kind is not EconomicAtomKindV1.DEBT:
            continue
        if not atom.asset.startswith("debt:") or atom.custody != "liability":
            raise ValueError("zUSD debt must use debt:<vault> liability identities")
        zusd_debt += atom.amount_atoms
    if zusd_supply != zusd_debt:
        raise ValueError(
            "zUSD supply/debt mismatch: "
            f"supply={zusd_supply}, debt={zusd_debt}"
        )

    for atom in state.economic_atoms:
        if atom.kind is EconomicAtomKindV1.STABILITY_POOL_SHARE and (
            atom.asset != "zUSD" or atom.custody != "stability_pool"
        ):
            raise ValueError("Stability Pool claims must be zUSD/stability_pool identities")
    pool_balance = amount(EconomicAtomKindV1.BALANCE, "stability_pool", "zUSD", "ledger")
    pool_claims = total(
        EconomicAtomKindV1.STABILITY_POOL_SHARE,
        asset="zUSD",
        custody="stability_pool",
    )
    if pool_balance != pool_claims:
        raise ValueError(
            "Stability Pool custody/claim mismatch: "
            f"custody={pool_balance}, claims={pool_claims}"
        )

    withdrawal_amounts: dict[tuple[str, str], int] = {}
    pending_withdrawal_amounts: dict[tuple[str, str], int] = {}
    for withdrawal in state.withdrawals:
        key = (withdrawal.beneficiary, withdrawal.asset)
        withdrawal_amounts[key] = withdrawal_amounts.get(key, 0) + withdrawal.amount_atoms
        if withdrawal.status is TauWithdrawalStatusV1.PENDING:
            pending_withdrawal_amounts[key] = (
                pending_withdrawal_amounts.get(key, 0) + withdrawal.amount_atoms
            )
    liability_amounts: dict[tuple[str, str], int] = {}
    for atom in state.economic_atoms:
        if atom.kind is not EconomicAtomKindV1.WITHDRAWAL_LIABILITY:
            continue
        if atom.custody != "tau":
            raise ValueError("withdrawal liabilities must use Tau custody")
        key = (atom.owner, atom.asset)
        liability_amounts[key] = liability_amounts.get(key, 0) + atom.amount_atoms
    if liability_amounts != pending_withdrawal_amounts:
        raise ValueError("withdrawal liability does not match pending intent state")

    zusd_balances = total(EconomicAtomKindV1.BALANCE, asset="zUSD")
    zusd_escrows = total(EconomicAtomKindV1.ESCROW, asset="zUSD")
    if zusd_escrows:
        raise ValueError("canonical zUSD cannot enter the Tau escrow deposit lane")
    zusd_withdrawals = sum(
        withdrawal.amount_atoms
        for withdrawal in state.withdrawals
        if withdrawal.asset == "zUSD"
    )
    if zusd_supply != zusd_balances + zusd_withdrawals:
        raise ValueError(
            "zUSD custody/supply mismatch: "
            f"supply={zusd_supply}, balances={zusd_balances}, "
            f"withdrawals={zusd_withdrawals}"
        )

    tau_escrow_amounts: dict[tuple[str, str], int] = {}
    for escrow in state.escrows:
        if escrow.terminal_state.startswith("tau_finalized:"):
            key = (escrow.owner, escrow.asset)
            tau_escrow_amounts[key] = tau_escrow_amounts.get(key, 0) + escrow.amount_atoms
            continue
        expected_balance = amount(
            EconomicAtomKindV1.BALANCE,
            f"escrow:{escrow.escrow_id}",
            escrow.asset,
            "ledger",
        )
        if expected_balance != escrow.amount_atoms:
            raise ValueError(
                f"escrow custody mismatch for {escrow.escrow_id}: "
                f"record={escrow.amount_atoms}, balance={expected_balance}"
            )
    economic_tau_escrow_amounts: dict[tuple[str, str], int] = {}
    for atom in state.economic_atoms:
        if atom.kind is not EconomicAtomKindV1.ESCROW:
            continue
        if atom.custody != "tau_escrow":
            raise ValueError("external escrow atoms must use tau_escrow custody")
        key = (atom.owner, atom.asset)
        economic_tau_escrow_amounts[key] = (
            economic_tau_escrow_amounts.get(key, 0) + atom.amount_atoms
        )
    if economic_tau_escrow_amounts != tau_escrow_amounts:
        raise ValueError("Tau escrow custody does not match finalized deposit records")

    rewards_by_asset: dict[str, int] = {}
    reserves_by_asset: dict[str, int] = {}
    for atom in state.economic_atoms:
        if atom.kind is EconomicAtomKindV1.REWARD:
            rewards_by_asset[atom.asset] = rewards_by_asset.get(atom.asset, 0) + atom.amount_atoms
        elif atom.kind is EconomicAtomKindV1.PROTOCOL_RESERVE:
            reserves_by_asset[atom.asset] = reserves_by_asset.get(atom.asset, 0) + atom.amount_atoms
    for asset, rewards in rewards_by_asset.items():
        reserve = reserves_by_asset.get(asset, 0)
        if rewards > reserve:
            raise ValueError(
                f"reward/reserve mismatch for {asset}: rewards={rewards}, reserve={reserve}"
            )


def m6_ready_v1(statuses: Mapping[str, Mapping[str, object]]) -> bool:
    """Reject self-declared readiness until verifier-owned evidence is present.

    A caller-supplied status mapping can describe an evidence request, but it
    cannot establish proofs, implementation, mounting, or test receipts.  The
    promotion gate must consume a verifier-created, subject-bound receipt.
    This compatibility function therefore fails closed for every mapping.
    """

    del statuses
    return False


def verify_finality_certificate_v1(
    subject: M6PromotionSubjectV1,
    *,
    candidate_head: str,
    publication_root: str,
    current_writer_epoch: int,
    candidate_parent_head: str | None = None,
    expected_command_root: str | None = None,
    expected_nonce_root: str | None = None,
    expected_execution_receipt_root: str | None = None,
    certificate: ZenoLedgerFinalityCertificateV1,
    tau_certificate: TauBatchCertificateV1 | None,
) -> None:
    """Check the finality binding required by the unique commit port."""

    _require_root(candidate_head, name="candidate head")
    _require_root(publication_root, name="candidate publication root")
    if certificate.candidate_head != candidate_head:
        raise ValueError("finality candidate head mismatch")
    if certificate.publication_root != publication_root:
        raise ValueError("finality publication root mismatch")
    if certificate.chain_id != subject.chain_id:
        raise ValueError("finality chain identity mismatch")
    if certificate.validator_set_root != subject.validator_set:
        raise ValueError("finality validator-set mismatch")
    if certificate.writer_epoch != current_writer_epoch:
        raise ValueError("finality writer epoch mismatch")
    if expected_command_root is not None:
        _require_root(expected_command_root, name="expected finality command root")
    if expected_nonce_root is not None:
        _require_root(expected_nonce_root, name="expected finality nonce root")
    if expected_execution_receipt_root is not None:
        _require_root(
            expected_execution_receipt_root,
            name="expected finality execution receipt root",
        )
    if certificate.execution_receipt_root != expected_execution_receipt_root:
        raise ValueError("finality execution receipt binding mismatch")
    if certificate.mode is FinalityModeV1.TAU_ORDERED:
        if tau_certificate is None:
            raise ValueError("Tau-ordered finality requires a Tau batch certificate")
        expected_parent = candidate_parent_head if candidate_parent_head is not None else ZERO_ROOT_V1
        if tau_certificate.candidate_parent_head != expected_parent:
            raise ValueError("Tau certificate is bound to a different candidate")
        if tau_certificate.tau_profile_root != subject.tau_profile:
            raise ValueError("Tau certificate profile mismatch")
        if tau_certificate.chain_id != subject.chain_id:
            raise ValueError("Tau certificate chain identity mismatch")
        if expected_command_root is not None:
            actual_command_root = ordered_root_v1(
                "m6-direct-command-root-v1",
                tau_certificate.ordered_command_hashes,
            )
            if actual_command_root != expected_command_root:
                raise ValueError("Tau certificate command binding mismatch")
        if expected_nonce_root is None:
            raise ValueError("Tau certificate nonce binding is required")
        actual_nonce_root = ordered_root_v1(
            "m6-direct-nonce-root-v1",
            tau_certificate.ordered_nonce_identities,
        )
        if actual_nonce_root != expected_nonce_root:
            raise ValueError("Tau certificate nonce binding mismatch")
    elif certificate.mode is FinalityModeV1.FALLBACK_FORCED_INCLUSION:
        if certificate.writer_epoch <= subject.writer_epoch:
            raise ValueError("fallback finality requires a fresh writer epoch")
        if tau_certificate is not None:
            raise ValueError("fallback finality forbids a Tau batch certificate")


def verify_zeno_ledger_finality_v1(
    subject: M6PromotionSubjectV1,
    *,
    candidate_head: str,
    publication_root: str,
    candidate_parent_head: str,
    expected_writer_epoch: int,
    expected_command_root: str | None,
    expected_nonce_root: str | None = None,
    expected_execution_receipt_root: str | None = None,
    certificate: ZenoLedgerFinalityCertificateV1,
    tau_certificate: TauBatchCertificateV1 | None,
    verification_receipt: M6FinalityVerificationReceiptV1,
) -> VerifiedZenoLedgerFinalityV1:
    """Issue a subject-bound finality witness after an external verifier receipt.

    The structural checks here are necessary bindings.  Validator signature
    cryptography, validator-independent data availability, and the 5-of-7
    fault premise remain obligations of the external verifier that created
    ``verification_receipt``.
    """

    if not isinstance(subject, M6PromotionSubjectV1):
        raise TypeError("finality subject is not typed")
    if not isinstance(certificate, ZenoLedgerFinalityCertificateV1):
        raise TypeError("finality certificate is not typed")
    if not isinstance(verification_receipt, M6FinalityVerificationReceiptV1):
        raise TypeError("finality verification receipt is not typed")
    if tau_certificate is not None and not isinstance(tau_certificate, TauBatchCertificateV1):
        raise TypeError("Tau finality certificate is not typed")
    _require_root(candidate_parent_head, name="candidate parent head", allow_zero=True)
    _require_root(candidate_head, name="candidate head")
    _require_root(publication_root, name="candidate publication root")
    _require_nonnegative_int(expected_writer_epoch, name="expected finality writer epoch")
    if (
        verification_receipt.subject_root != subject.subject_root
        or verification_receipt.candidate_parent_head != candidate_parent_head
        or verification_receipt.candidate_head != candidate_head
        or verification_receipt.publication_root != publication_root
        or verification_receipt.writer_epoch != expected_writer_epoch
        or verification_receipt.certificate_root != certificate.certificate_root
    ):
        raise ValueError("finality verification receipt binding mismatch")
    if expected_command_root is not None:
        _require_root(expected_command_root, name="expected finality command root")
    verify_finality_certificate_v1(
        subject,
        candidate_head=candidate_head,
        publication_root=publication_root,
        current_writer_epoch=expected_writer_epoch,
        candidate_parent_head=candidate_parent_head,
        expected_command_root=expected_command_root,
        expected_nonce_root=expected_nonce_root,
        expected_execution_receipt_root=expected_execution_receipt_root,
        certificate=certificate,
        tau_certificate=tau_certificate,
    )
    return VerifiedZenoLedgerFinalityV1(
        _VERIFIED_ZENO_LEDGER_FINALITY_TOKEN,
        subject_root=subject.subject_root,
        candidate_parent_head=candidate_parent_head,
        candidate_head=candidate_head,
        publication_root=publication_root,
        expected_command_root=expected_command_root,
        expected_nonce_root=expected_nonce_root,
        certificate=certificate,
        tau_certificate=tau_certificate,
        verification_receipt=verification_receipt,
    )


__all__ = [
    "SCHEMA_V1",
    "DURABILITY_PROFILE_SCHEMA_V1",
    "FINALITY_RECEIPT_RECORD_SCHEMA_V1",
    "ZRPF_PROFILE_V1",
    "DIRECT_PROFILE_V1",
    "ZRPF_LEAF_COUNT_V1",
    "ZRPF_COMMANDS_PER_LEAF_V1",
    "ZRPF_COMMAND_COUNT_V1",
    "ZRPF_AGGREGATE_COUNT_V1",
    "ZRPF_LEAVES_PER_AGGREGATE_V1",
    "ZERO_ROOT_V1",
    "MAX_DURABILITY_PROFILE_JSON_BYTES_V1",
    "MAX_DURABILITY_PROFILE_CHAIN_BLOCKS_V1",
    "DEFAULT_DURABILITY_JSON_BYTES_V1",
    "M6DurabilityProfileV1",
    "DEFAULT_DURABILITY_PROFILE_V1",
    "MAX_ATOMS_V1",
    "MAX_PRICE_E8_V1",
    "SEALED_BID_PRICE_SCALE_E8_V1",
    "MAX_SEALED_BID_PRICE_E8_V1",
    "GlobalCommandKindV1",
    "LAUNCH_COMMANDS_V1",
    "M6_RESEARCH_DISABLED_COMMANDS_V1",
    "M6_RESEARCH_ENABLED_COMMANDS_V1",
    "BusinessStatusV1",
    "AdmissionRejectReasonV1",
    "BusinessRejectReasonV1",
    "EconomicAtomKindV1",
    "ValueDeltaClassV1",
    "TauWithdrawalStatusV1",
    "MigrationPhaseV1",
    "MigrationEvidenceKindV1",
    "FinalityModeV1",
    "SellerAuctionPhaseV1",
    "PrivateSwapPhaseV1",
    "DestinationAdapterRootV1",
    "AssetPolicyV1",
    "FreshnessBoundsV1",
    "OracleContextV1",
    "M6PromotionSubjectV1",
    "M6ExecutionContextClaimsV1",
    "AuthenticatedExecutionContextV1",
    "validate_authenticated_execution_context_body_v1",
    "NonceAtomV1",
    "EconomicAtomV1",
    "EscrowAtomV1",
    "SellerAuctionBidStateV1",
    "PrivateSwapParticipantStateV1",
    "TauWithdrawalIntentV1",
    "WithdrawalAcknowledgmentV1",
    "OutboxAtomV1",
    "MigrationStateV1",
    "TauFinalityBoundDepositWitnessV1",
    "TauEscrowDepositProofV1",
    "MigrationAuthorityProofV1",
    "M6AuthorityEvidenceV1",
    "TauBatchCertificateV1",
    "ZenoLedgerFinalityCertificateV1",
    "M6FinalityVerificationReceiptV1",
    "M6FinalityVerificationReceiptRecordV1",
    "VerifiedZenoLedgerFinalityV1",
    "ValueDeltaEntryV1",
    "ValueDeltaCertificateV1",
    "HistoryAtomV1",
    "PublicationAtomV1",
    "M6ApplicationStateV1",
    "CommandArgumentV1",
    "GlobalCommandV1",
    "CommandDecodeError",
    "decode_global_command_v1",
    "admit_global_command_v1",
    "RejectNoCommitV1",
    "AcceptCandidateV1",
    "GlobalOutcomeV1",
    "SellerInventoryAuctionCommitV1",
    "SellerInventoryAuctionRevealV1",
    "PrivateSwapCommitV1",
    "PrivateSwapRevealV1",
    "ZRPFChunkStatementV1",
    "ZRPFRootJournalV1",
    "M6ZRPFVerificationReceiptV1",
    "VerifiedZRPFRootV1",
    "initial_application_state_v1",
    "validate_state_commitments_v1",
    "validate_economic_state_v1",
    "m6_ready_v1",
    "verify_finality_certificate_v1",
    "verify_zeno_ledger_finality_v1",
    "canonical_bytes_v1",
    "hash_v1",
    "m6_chain_id_root_from_external_v1",
    "ordered_root_v1",
]
