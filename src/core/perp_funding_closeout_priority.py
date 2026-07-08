from __future__ import annotations

import hashlib
from collections.abc import Mapping
from dataclasses import dataclass

from py_ecc.bls import G2Basic

from ..state.canonical import canonical_json_bytes
from .perp_funding_closeout_policy_ledger import (
    FundingCloseoutPolicyLedger,
    funding_closeout_policy_ledger_hash,
)

RECOVERY_PRIORITY_CERT_SCHEMA = "zenodex.perp.funding_closeout_recovery_priority.v1"
RECOVERY_COLLECTION_RECEIPT_SCHEMA = (
    "zenodex.perp.funding_closeout_recovery_collection.v1"
)
RECOVERY_SOURCE_AUTHORITY_SCHEMA = (
    "zenodex.perp.funding_closeout_recovery_source_authority.v1"
)
RECOVERY_SOURCE_AUTHORITY_BINDING_SCHEMA = (
    "zenodex.perp.funding_closeout_recovery_source_authority_binding.v1"
)
RECEIVER_RECOVERY_DISTRIBUTION_SCHEMA = (
    "zenodex.perp.funding_closeout_receiver_recovery_distribution.v1"
)
SINK_RECOVERY_DISTRIBUTION_SCHEMA = (
    "zenodex.perp.funding_closeout_sink_recovery_distribution.v1"
)
RECOVERY_PRIORITY_RECEIVER_FIRST = "receiver_first"
RECOVERY_PRIORITY_SINK_FIRST = "sink_first"
RECEIVER_DISTRIBUTION_LARGEST_REMAINDER = "pro_rata_largest_remainder"
SINK_DISTRIBUTION_LARGEST_REMAINDER = "pro_rata_largest_remainder"
_RECOVERY_PRIORITY_POLICIES = {
    RECOVERY_PRIORITY_RECEIVER_FIRST,
    RECOVERY_PRIORITY_SINK_FIRST,
}
_RECEIVER_DISTRIBUTION_POLICIES = {RECEIVER_DISTRIBUTION_LARGEST_REMAINDER}
_SINK_DISTRIBUTION_POLICIES = {SINK_DISTRIBUTION_LARGEST_REMAINDER}
_RECOVERY_SOURCE_AUTHORITY_BINDING_KEYS = {
    "authority_hash",
    "authority_state_root_hash",
    "canonical_sha256",
    "market_id",
    "policy_hash",
    "schema",
    "signature",
    "signer_pubkey",
    "valid_from_epoch",
    "valid_until_epoch",
}


def _require_int(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    return int(value)


def _require_non_negative_int(value: object, *, name: str) -> int:
    out = _require_int(value, name=name)
    if out < 0:
        raise ValueError(f"{name} must be non-negative")
    return out


def _require_account(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    if not value:
        raise ValueError(f"{name} must be non-empty")
    if "\x00" in value:
        raise ValueError(f"{name} must not contain NUL")
    return value


def _require_hash(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    if not value.startswith("sha256:") or len(value) != len("sha256:") + 64:
        raise ValueError(f"{name} must be sha256:<64 lowercase hex chars>")
    suffix = value[len("sha256:") :]
    if suffix.lower() != suffix or any(ch not in "0123456789abcdef" for ch in suffix):
        raise ValueError(f"{name} must be sha256:<64 lowercase hex chars>")
    return value


def _require_prefixed_hex(value: object, *, name: str, nbytes: int) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    expected_len = len("0x") + 2 * nbytes
    if not value.startswith("0x") or len(value) != expected_len:
        raise ValueError(f"{name} must be 0x-prefixed {nbytes}-byte hex")
    suffix = value[2:]
    if suffix.lower() != suffix or any(ch not in "0123456789abcdef" for ch in suffix):
        raise ValueError(f"{name} must be 0x-prefixed lowercase hex")
    return value


def _require_signer_pubkeys(value: object, *, name: str) -> tuple[str, ...]:
    if not isinstance(value, tuple):
        raise TypeError(f"{name} must be a tuple")
    out = tuple(
        _require_prefixed_hex(signer, name="signer_pubkey", nbytes=48)
        for signer in value
    )
    if not out:
        raise ValueError(f"{name} must be non-empty")
    if list(out) != sorted(out):
        raise ValueError(f"{name} must be sorted")
    if len(out) != len(set(out)):
        raise ValueError(f"{name} must be unique")
    return out


def _signature_message(payload: object) -> bytes:
    return hashlib.sha256(canonical_json_bytes(payload)).digest()


def _require_priority_policy(value: object) -> str:
    if not isinstance(value, str):
        raise TypeError("priority_policy must be a str")
    if value not in _RECOVERY_PRIORITY_POLICIES:
        raise ValueError("priority_policy must be receiver_first or sink_first")
    return value


def _require_receiver_distribution_policy(value: object) -> str:
    if not isinstance(value, str):
        raise TypeError("distribution_policy must be a str")
    if value not in _RECEIVER_DISTRIBUTION_POLICIES:
        raise ValueError("distribution_policy must be pro_rata_largest_remainder")
    return value


def _require_sink_distribution_policy(value: object) -> str:
    if not isinstance(value, str):
        raise TypeError("distribution_policy must be a str")
    if value not in _SINK_DISTRIBUTION_POLICIES:
        raise ValueError("distribution_policy must be pro_rata_largest_remainder")
    return value


def _require_payload_mapping(value: object, *, name: str) -> Mapping[str, object]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be an object")
    if not all(isinstance(key, str) for key in value.keys()):
        raise ValueError(f"{name} keys must be strings")
    return value


def _require_exact_keys(value: Mapping[str, object], *, name: str, keys: set[str]) -> None:
    if set(value.keys()) != keys:
        raise ValueError(f"{name} keys mismatch")


def _require_payload_list(value: object, *, name: str) -> tuple[object, ...]:
    if not isinstance(value, list):
        raise TypeError(f"{name} must be a list")
    return tuple(value)


def _require_source_ids(value: object) -> tuple[str, ...]:
    if not isinstance(value, tuple):
        raise TypeError("source_ids must be a tuple")
    out = tuple(_require_account(source_id, name="source_id") for source_id in value)
    if not out:
        raise ValueError("source_ids must be non-empty")
    if list(out) != sorted(out):
        raise ValueError("source_ids must be sorted")
    if len(out) != len(set(out)):
        raise ValueError("source_ids must be unique")
    return out


def _recovery_source_authority_unsigned_payload(
    authority: "FundingCloseoutRecoverySourceAuthority",
) -> dict[str, object]:
    return {
        "authorized_source_ids": list(authority.authorized_source_ids),
        "market_id": authority.market_id,
        "schema": authority.schema,
        "valid_from_epoch": int(authority.valid_from_epoch),
        "valid_until_epoch": int(authority.valid_until_epoch),
    }


@dataclass(frozen=True)
class RecoveryPriorityVerdict:
    ok: bool
    error: str | None

    def __post_init__(self) -> None:
        if not isinstance(self.ok, bool):
            raise TypeError("ok must be a bool")
        if self.error is not None and not isinstance(self.error, str):
            raise TypeError("error must be None or str")


@dataclass(frozen=True)
class RecoverySourceAuthorityVerdict:
    ok: bool
    error: str | None
    authority: "FundingCloseoutRecoverySourceAuthority | None" = None

    def __post_init__(self) -> None:
        if not isinstance(self.ok, bool):
            raise TypeError("ok must be a bool")
        if self.error is not None and not isinstance(self.error, str):
            raise TypeError("error must be None or str")
        if self.authority is not None and not isinstance(
            self.authority,
            FundingCloseoutRecoverySourceAuthority,
        ):
            raise TypeError(
                "authority must be a FundingCloseoutRecoverySourceAuthority or None"
            )


@dataclass(frozen=True)
class RecoveryPriorityAllocation:
    receiver_recovery_quote: int
    sink_recovery_quote: int

    def __post_init__(self) -> None:
        _require_non_negative_int(
            self.receiver_recovery_quote,
            name="receiver_recovery_quote",
        )
        _require_non_negative_int(
            self.sink_recovery_quote,
            name="sink_recovery_quote",
        )


@dataclass(frozen=True)
class ReceiverRecoveryDistributionRow:
    account_pubkey: str
    recoverable_claim_quote: int
    recovery_quote: int

    def __post_init__(self) -> None:
        _require_account(self.account_pubkey, name="account_pubkey")
        claim = _require_non_negative_int(
            self.recoverable_claim_quote,
            name="recoverable_claim_quote",
        )
        recovery = _require_non_negative_int(
            self.recovery_quote,
            name="recovery_quote",
        )
        if recovery > claim:
            raise ValueError("receiver recovery row exceeds recoverable claim")


@dataclass(frozen=True)
class SinkRecoveryDistributionRow:
    account_pubkey: str
    claimant: str
    subrogated_claim_quote: int
    recovery_quote: int

    def __post_init__(self) -> None:
        _require_account(self.account_pubkey, name="account_pubkey")
        _require_account(self.claimant, name="claimant")
        claim = _require_non_negative_int(
            self.subrogated_claim_quote,
            name="subrogated_claim_quote",
        )
        recovery = _require_non_negative_int(
            self.recovery_quote,
            name="recovery_quote",
        )
        if recovery > claim:
            raise ValueError("sink recovery row exceeds subrogated claim")


@dataclass(frozen=True)
class FundingCloseoutRecoveryPriorityCertificate:
    schema: str
    market_id: str
    epoch: int
    policy_ledger_hash: str
    priority_policy: str
    source_capacity_quote: int
    total_recoverable_claim_quote: int
    total_subrogated_claim_quote: int
    receiver_recovery_quote: int
    sink_recovery_quote: int

    def __post_init__(self) -> None:
        if self.schema != RECOVERY_PRIORITY_CERT_SCHEMA:
            raise ValueError("invalid recovery priority certificate schema")
        _require_account(self.market_id, name="market_id")
        _require_non_negative_int(self.epoch, name="epoch")
        _require_hash(self.policy_ledger_hash, name="policy_ledger_hash")
        priority = _require_priority_policy(self.priority_policy)
        source_capacity = _require_non_negative_int(
            self.source_capacity_quote,
            name="source_capacity_quote",
        )
        recoverable_claim = _require_non_negative_int(
            self.total_recoverable_claim_quote,
            name="total_recoverable_claim_quote",
        )
        subrogated_claim = _require_non_negative_int(
            self.total_subrogated_claim_quote,
            name="total_subrogated_claim_quote",
        )
        receiver_recovery = _require_non_negative_int(
            self.receiver_recovery_quote,
            name="receiver_recovery_quote",
        )
        sink_recovery = _require_non_negative_int(
            self.sink_recovery_quote,
            name="sink_recovery_quote",
        )

        if receiver_recovery > recoverable_claim:
            raise ValueError("receiver recovery exceeds recoverable claim")
        if sink_recovery > subrogated_claim:
            raise ValueError("sink recovery exceeds subrogated claim")
        if receiver_recovery + sink_recovery > source_capacity:
            raise ValueError("recovery allocation exceeds source capacity")

        expected = compute_recovery_priority_allocation(
            priority_policy=priority,
            source_capacity_quote=source_capacity,
            total_recoverable_claim_quote=recoverable_claim,
            total_subrogated_claim_quote=subrogated_claim,
        )
        if receiver_recovery != expected.receiver_recovery_quote:
            raise ValueError(f"{priority} receiver recovery mismatch")
        if sink_recovery != expected.sink_recovery_quote:
            raise ValueError(f"{priority} sink recovery mismatch")


@dataclass(frozen=True)
class FundingCloseoutRecoveryCollectionReceipt:
    schema: str
    market_id: str
    epoch: int
    policy_ledger_hash: str
    priority_certificate_hash: str
    source_id: str
    collection_nonce: int
    source_capacity_quote: int
    collected_source_quote: int

    def __post_init__(self) -> None:
        if self.schema != RECOVERY_COLLECTION_RECEIPT_SCHEMA:
            raise ValueError("invalid recovery collection receipt schema")
        _require_account(self.market_id, name="market_id")
        _require_non_negative_int(self.epoch, name="epoch")
        _require_hash(self.policy_ledger_hash, name="policy_ledger_hash")
        _require_hash(
            self.priority_certificate_hash,
            name="priority_certificate_hash",
        )
        _require_account(self.source_id, name="source_id")
        _require_non_negative_int(self.collection_nonce, name="collection_nonce")
        source_capacity = _require_non_negative_int(
            self.source_capacity_quote,
            name="source_capacity_quote",
        )
        collected = _require_non_negative_int(
            self.collected_source_quote,
            name="collected_source_quote",
        )
        if collected > source_capacity:
            raise ValueError("recovery collection exceeds source capacity")


@dataclass(frozen=True)
class FundingCloseoutRecoverySourceAuthority:
    schema: str
    market_id: str
    valid_from_epoch: int
    valid_until_epoch: int
    authorized_source_ids: tuple[str, ...]
    canonical_sha256: str

    def __post_init__(self) -> None:
        if self.schema != RECOVERY_SOURCE_AUTHORITY_SCHEMA:
            raise ValueError("invalid recovery source authority schema")
        _require_account(self.market_id, name="market_id")
        valid_from = _require_non_negative_int(
            self.valid_from_epoch,
            name="valid_from_epoch",
        )
        valid_until = _require_non_negative_int(
            self.valid_until_epoch,
            name="valid_until_epoch",
        )
        if valid_from > valid_until:
            raise ValueError("valid_from_epoch must be <= valid_until_epoch")
        _require_source_ids(self.authorized_source_ids)
        _require_hash(self.canonical_sha256, name="canonical_sha256")
        if self.canonical_sha256 != funding_closeout_recovery_source_authority_hash(
            self
        ):
            raise ValueError("canonical_sha256 mismatch")


@dataclass(frozen=True)
class FundingCloseoutRecoverySourceAuthorityBinding:
    schema: str
    market_id: str
    valid_from_epoch: int
    valid_until_epoch: int
    authority_hash: str
    authority_state_root_hash: str
    policy_hash: str
    signer_pubkey: str
    signature: str
    canonical_sha256: str

    def __post_init__(self) -> None:
        if self.schema != RECOVERY_SOURCE_AUTHORITY_BINDING_SCHEMA:
            raise ValueError("invalid recovery source authority binding schema")
        _require_account(self.market_id, name="market_id")
        valid_from = _require_non_negative_int(
            self.valid_from_epoch,
            name="valid_from_epoch",
        )
        valid_until = _require_non_negative_int(
            self.valid_until_epoch,
            name="valid_until_epoch",
        )
        if valid_from > valid_until:
            raise ValueError("valid_from_epoch must be <= valid_until_epoch")
        _require_hash(self.authority_hash, name="authority_hash")
        _require_hash(self.authority_state_root_hash, name="authority_state_root_hash")
        _require_hash(self.policy_hash, name="policy_hash")
        _require_prefixed_hex(self.signer_pubkey, name="signer_pubkey", nbytes=48)
        _require_prefixed_hex(self.signature, name="signature", nbytes=96)
        _require_hash(self.canonical_sha256, name="canonical_sha256")
        if (
            self.canonical_sha256
            != funding_closeout_recovery_source_authority_binding_hash(self)
        ):
            raise ValueError("canonical_sha256 mismatch")

    def unsigned_payload(self) -> dict[str, object]:
        return {
            "authority_hash": self.authority_hash,
            "authority_state_root_hash": self.authority_state_root_hash,
            "market_id": self.market_id,
            "policy_hash": self.policy_hash,
            "schema": self.schema,
            "signer_pubkey": self.signer_pubkey,
            "valid_from_epoch": int(self.valid_from_epoch),
            "valid_until_epoch": int(self.valid_until_epoch),
        }

    def to_payload(self) -> dict[str, object]:
        payload = self.unsigned_payload()
        payload["canonical_sha256"] = self.canonical_sha256
        payload["signature"] = self.signature
        return payload


@dataclass(frozen=True)
class RecoverySourceAuthorityBindingVerdict:
    ok: bool
    error: str | None
    binding: "FundingCloseoutRecoverySourceAuthorityBinding | None" = None

    def __post_init__(self) -> None:
        if not isinstance(self.ok, bool):
            raise TypeError("ok must be a bool")
        if self.error is not None and not isinstance(self.error, str):
            raise TypeError("error must be None or str")
        if self.binding is not None and not isinstance(
            self.binding,
            FundingCloseoutRecoverySourceAuthorityBinding,
        ):
            raise TypeError(
                "binding must be a FundingCloseoutRecoverySourceAuthorityBinding or None"
            )


@dataclass(frozen=True)
class FundingCloseoutReceiverRecoveryDistributionCertificate:
    schema: str
    market_id: str
    epoch: int
    policy_ledger_hash: str
    priority_certificate_hash: str
    distribution_policy: str
    total_receiver_recovery_quote: int
    total_recoverable_claim_quote: int
    receiver_rows: tuple[ReceiverRecoveryDistributionRow, ...]

    def __post_init__(self) -> None:
        if self.schema != RECEIVER_RECOVERY_DISTRIBUTION_SCHEMA:
            raise ValueError("invalid receiver recovery distribution schema")
        _require_account(self.market_id, name="market_id")
        _require_non_negative_int(self.epoch, name="epoch")
        _require_hash(self.policy_ledger_hash, name="policy_ledger_hash")
        _require_hash(
            self.priority_certificate_hash,
            name="priority_certificate_hash",
        )
        policy = _require_receiver_distribution_policy(self.distribution_policy)
        total_recovery = _require_non_negative_int(
            self.total_receiver_recovery_quote,
            name="total_receiver_recovery_quote",
        )
        total_claim = _require_non_negative_int(
            self.total_recoverable_claim_quote,
            name="total_recoverable_claim_quote",
        )
        rows = _require_receiver_recovery_distribution_rows(self.receiver_rows)
        if total_recovery > total_claim:
            raise ValueError("receiver recovery exceeds total recoverable claim")
        if sum(row.recoverable_claim_quote for row in rows) != total_claim:
            raise ValueError("receiver distribution recoverable claim total mismatch")
        if sum(row.recovery_quote for row in rows) != total_recovery:
            raise ValueError("receiver distribution recovery total mismatch")
        if policy == RECEIVER_DISTRIBUTION_LARGEST_REMAINDER:
            expected = compute_receiver_largest_remainder_distribution(
                tuple(
                    (row.account_pubkey, row.recoverable_claim_quote)
                    for row in rows
                ),
                total_receiver_recovery_quote=total_recovery,
            )
            if rows != expected:
                raise ValueError("receiver largest-remainder distribution mismatch")


@dataclass(frozen=True)
class FundingCloseoutSinkRecoveryDistributionCertificate:
    schema: str
    market_id: str
    epoch: int
    policy_ledger_hash: str
    priority_certificate_hash: str
    distribution_policy: str
    total_sink_recovery_quote: int
    total_subrogated_claim_quote: int
    sink_rows: tuple[SinkRecoveryDistributionRow, ...]

    def __post_init__(self) -> None:
        if self.schema != SINK_RECOVERY_DISTRIBUTION_SCHEMA:
            raise ValueError("invalid sink recovery distribution schema")
        _require_account(self.market_id, name="market_id")
        _require_non_negative_int(self.epoch, name="epoch")
        _require_hash(self.policy_ledger_hash, name="policy_ledger_hash")
        _require_hash(
            self.priority_certificate_hash,
            name="priority_certificate_hash",
        )
        policy = _require_sink_distribution_policy(self.distribution_policy)
        total_recovery = _require_non_negative_int(
            self.total_sink_recovery_quote,
            name="total_sink_recovery_quote",
        )
        total_claim = _require_non_negative_int(
            self.total_subrogated_claim_quote,
            name="total_subrogated_claim_quote",
        )
        rows = _require_sink_recovery_distribution_rows(self.sink_rows)
        if total_recovery > total_claim:
            raise ValueError("sink recovery exceeds total subrogated claim")
        if sum(row.subrogated_claim_quote for row in rows) != total_claim:
            raise ValueError("sink distribution subrogated claim total mismatch")
        if sum(row.recovery_quote for row in rows) != total_recovery:
            raise ValueError("sink distribution recovery total mismatch")
        if policy == SINK_DISTRIBUTION_LARGEST_REMAINDER:
            expected = compute_sink_largest_remainder_distribution(
                tuple(
                    (
                        row.account_pubkey,
                        row.claimant,
                        row.subrogated_claim_quote,
                    )
                    for row in rows
                ),
                total_sink_recovery_quote=total_recovery,
            )
            if rows != expected:
                raise ValueError("sink largest-remainder distribution mismatch")


def _require_receiver_recovery_distribution_rows(
    rows: object,
) -> tuple[ReceiverRecoveryDistributionRow, ...]:
    if not isinstance(rows, tuple):
        raise TypeError("receiver_rows must be a tuple")
    if not all(isinstance(row, ReceiverRecoveryDistributionRow) for row in rows):
        raise TypeError("receiver_rows must contain ReceiverRecoveryDistributionRow values")
    accounts = [row.account_pubkey for row in rows]
    if accounts != sorted(accounts):
        raise ValueError("receiver_rows must be sorted by account_pubkey")
    if len(accounts) != len(set(accounts)):
        raise ValueError("duplicate receiver recovery account")
    return rows


def _require_sink_recovery_distribution_rows(
    rows: object,
) -> tuple[SinkRecoveryDistributionRow, ...]:
    if not isinstance(rows, tuple):
        raise TypeError("sink_rows must be a tuple")
    if not all(isinstance(row, SinkRecoveryDistributionRow) for row in rows):
        raise TypeError("sink_rows must contain SinkRecoveryDistributionRow values")
    keys = [(row.account_pubkey, row.claimant) for row in rows]
    if keys != sorted(keys):
        raise ValueError("sink_rows must be sorted by account_pubkey and claimant")
    if len(keys) != len(set(keys)):
        raise ValueError("duplicate sink recovery row")
    return rows


def compute_recovery_priority_allocation(
    *,
    priority_policy: str,
    source_capacity_quote: int,
    total_recoverable_claim_quote: int,
    total_subrogated_claim_quote: int,
) -> RecoveryPriorityAllocation:
    priority = _require_priority_policy(priority_policy)
    source_capacity = _require_non_negative_int(
        source_capacity_quote,
        name="source_capacity_quote",
    )
    recoverable_claim = _require_non_negative_int(
        total_recoverable_claim_quote,
        name="total_recoverable_claim_quote",
    )
    subrogated_claim = _require_non_negative_int(
        total_subrogated_claim_quote,
        name="total_subrogated_claim_quote",
    )

    if priority == RECOVERY_PRIORITY_RECEIVER_FIRST:
        receiver_recovery = min(recoverable_claim, source_capacity)
        remaining = source_capacity - receiver_recovery
        return RecoveryPriorityAllocation(
            receiver_recovery_quote=receiver_recovery,
            sink_recovery_quote=min(subrogated_claim, remaining),
        )

    sink_recovery = min(subrogated_claim, source_capacity)
    remaining = source_capacity - sink_recovery
    return RecoveryPriorityAllocation(
        receiver_recovery_quote=min(recoverable_claim, remaining),
        sink_recovery_quote=sink_recovery,
    )


def compute_receiver_largest_remainder_distribution(
    claims_by_account: tuple[tuple[str, int], ...],
    *,
    total_receiver_recovery_quote: int,
) -> tuple[ReceiverRecoveryDistributionRow, ...]:
    total_recovery = _require_non_negative_int(
        total_receiver_recovery_quote,
        name="total_receiver_recovery_quote",
    )
    checked_claims = tuple(
        sorted(
            (
                (
                    _require_account(account, name="account_pubkey"),
                    _require_non_negative_int(
                        claim,
                        name="recoverable_claim_quote",
                    ),
                )
                for account, claim in claims_by_account
                if _require_non_negative_int(
                    claim,
                    name="recoverable_claim_quote",
                )
                > 0
            ),
            key=lambda item: item[0],
        )
    )
    accounts = [account for account, _claim in checked_claims]
    if len(accounts) != len(set(accounts)):
        raise ValueError("duplicate receiver recovery account")
    total_claim = sum(claim for _account, claim in checked_claims)
    if total_recovery > total_claim:
        raise ValueError("receiver recovery exceeds total recoverable claim")
    if total_claim == 0:
        if total_recovery != 0:
            raise ValueError("receiver recovery requires recoverable claims")
        return ()

    bases: list[tuple[str, int, int, int]] = []
    base_sum = 0
    for account, claim in checked_claims:
        weighted = claim * total_recovery
        base = weighted // total_claim
        remainder = weighted % total_claim
        bases.append((account, claim, base, remainder))
        base_sum += base

    dust = total_recovery - base_sum
    if dust < 0 or dust > len(bases):
        raise ValueError("largest-remainder dust out of bounds")
    bonus_accounts = {
        account
        for account, _claim, _base, _remainder in sorted(
            bases,
            key=lambda item: (-item[3], item[0]),
        )[:dust]
    }
    return tuple(
        ReceiverRecoveryDistributionRow(
            account_pubkey=account,
            recoverable_claim_quote=claim,
            recovery_quote=base + int(account in bonus_accounts),
        )
        for account, claim, base, _remainder in bases
    )


def compute_sink_largest_remainder_distribution(
    claims_by_sink: tuple[tuple[str, str, int], ...],
    *,
    total_sink_recovery_quote: int,
) -> tuple[SinkRecoveryDistributionRow, ...]:
    total_recovery = _require_non_negative_int(
        total_sink_recovery_quote,
        name="total_sink_recovery_quote",
    )
    checked_claims = tuple(
        sorted(
            (
                (
                    _require_account(account, name="account_pubkey"),
                    _require_account(claimant, name="claimant"),
                    _require_non_negative_int(
                        claim,
                        name="subrogated_claim_quote",
                    ),
                )
                for account, claimant, claim in claims_by_sink
                if _require_non_negative_int(
                    claim,
                    name="subrogated_claim_quote",
                )
                > 0
            ),
            key=lambda item: (item[0], item[1]),
        )
    )
    keys = [(account, claimant) for account, claimant, _claim in checked_claims]
    if len(keys) != len(set(keys)):
        raise ValueError("duplicate sink recovery row")
    total_claim = sum(claim for _account, _claimant, claim in checked_claims)
    if total_recovery > total_claim:
        raise ValueError("sink recovery exceeds total subrogated claim")
    if total_claim == 0:
        if total_recovery != 0:
            raise ValueError("sink recovery requires subrogated claims")
        return ()

    bases: list[tuple[str, str, int, int, int]] = []
    base_sum = 0
    for account, claimant, claim in checked_claims:
        weighted = claim * total_recovery
        base = weighted // total_claim
        remainder = weighted % total_claim
        bases.append((account, claimant, claim, base, remainder))
        base_sum += base

    dust = total_recovery - base_sum
    if dust < 0 or dust > len(bases):
        raise ValueError("largest-remainder dust out of bounds")
    bonus_keys = {
        (account, claimant)
        for account, claimant, _claim, _base, _remainder in sorted(
            bases,
            key=lambda item: (-item[4], item[0], item[1]),
        )[:dust]
    }
    return tuple(
        SinkRecoveryDistributionRow(
            account_pubkey=account,
            claimant=claimant,
            subrogated_claim_quote=claim,
            recovery_quote=base + int((account, claimant) in bonus_keys),
        )
        for account, claimant, claim, base, _remainder in bases
    )


def build_funding_closeout_recovery_priority_certificate(
    policy_ledger: FundingCloseoutPolicyLedger,
    *,
    priority_policy: str,
    source_capacity_quote: int,
) -> FundingCloseoutRecoveryPriorityCertificate:
    if not isinstance(policy_ledger, FundingCloseoutPolicyLedger):
        raise TypeError("policy_ledger must be a FundingCloseoutPolicyLedger")
    allocation = compute_recovery_priority_allocation(
        priority_policy=priority_policy,
        source_capacity_quote=source_capacity_quote,
        total_recoverable_claim_quote=policy_ledger.total_recoverable_claim_quote,
        total_subrogated_claim_quote=policy_ledger.total_subrogated_claim_quote,
    )
    return FundingCloseoutRecoveryPriorityCertificate(
        schema=RECOVERY_PRIORITY_CERT_SCHEMA,
        market_id=policy_ledger.market_id,
        epoch=policy_ledger.epoch,
        policy_ledger_hash=funding_closeout_policy_ledger_hash(policy_ledger),
        priority_policy=_require_priority_policy(priority_policy),
        source_capacity_quote=_require_non_negative_int(
            source_capacity_quote,
            name="source_capacity_quote",
        ),
        total_recoverable_claim_quote=policy_ledger.total_recoverable_claim_quote,
        total_subrogated_claim_quote=policy_ledger.total_subrogated_claim_quote,
        receiver_recovery_quote=allocation.receiver_recovery_quote,
        sink_recovery_quote=allocation.sink_recovery_quote,
    )


def build_funding_closeout_recovery_collection_receipt(
    policy_ledger: FundingCloseoutPolicyLedger,
    priority_certificate: FundingCloseoutRecoveryPriorityCertificate,
    *,
    source_id: str,
    collection_nonce: int,
) -> FundingCloseoutRecoveryCollectionReceipt:
    validate_recovery_priority_certificate_against_policy_ledger(
        priority_certificate,
        policy_ledger,
    )
    return FundingCloseoutRecoveryCollectionReceipt(
        schema=RECOVERY_COLLECTION_RECEIPT_SCHEMA,
        market_id=policy_ledger.market_id,
        epoch=policy_ledger.epoch,
        policy_ledger_hash=funding_closeout_policy_ledger_hash(policy_ledger),
        priority_certificate_hash=funding_closeout_recovery_priority_certificate_hash(
            priority_certificate
        ),
        source_id=_require_account(source_id, name="source_id"),
        collection_nonce=_require_non_negative_int(
            collection_nonce,
            name="collection_nonce",
        ),
        source_capacity_quote=priority_certificate.source_capacity_quote,
        collected_source_quote=(
            priority_certificate.receiver_recovery_quote
            + priority_certificate.sink_recovery_quote
        ),
    )


def build_funding_closeout_recovery_source_authority(
    *,
    market_id: str,
    valid_from_epoch: int,
    valid_until_epoch: int,
    authorized_source_ids: tuple[str, ...],
) -> FundingCloseoutRecoverySourceAuthority:
    source_ids = _require_source_ids(authorized_source_ids)
    valid_from = _require_non_negative_int(
        valid_from_epoch,
        name="valid_from_epoch",
    )
    valid_until = _require_non_negative_int(
        valid_until_epoch,
        name="valid_until_epoch",
    )
    if valid_from > valid_until:
        raise ValueError("valid_from_epoch must be <= valid_until_epoch")
    unsigned = {
        "authorized_source_ids": list(source_ids),
        "market_id": _require_account(market_id, name="market_id"),
        "schema": RECOVERY_SOURCE_AUTHORITY_SCHEMA,
        "valid_from_epoch": valid_from,
        "valid_until_epoch": valid_until,
    }
    return FundingCloseoutRecoverySourceAuthority(
        schema=RECOVERY_SOURCE_AUTHORITY_SCHEMA,
        market_id=str(unsigned["market_id"]),
        valid_from_epoch=valid_from,
        valid_until_epoch=valid_until,
        authorized_source_ids=source_ids,
        canonical_sha256="sha256:"
        + hashlib.sha256(canonical_json_bytes(unsigned)).hexdigest(),
    )


def build_funding_closeout_recovery_source_authority_binding(
    *,
    market_id: str,
    valid_from_epoch: int,
    valid_until_epoch: int,
    authority_hash: str,
    authority_state_root_hash: str,
    policy_hash: str,
    signer_privkey: int,
) -> FundingCloseoutRecoverySourceAuthorityBinding:
    if (
        not isinstance(signer_privkey, int)
        or isinstance(signer_privkey, bool)
        or signer_privkey <= 0
    ):
        raise ValueError("signer_privkey must be a positive int")
    signer_pubkey = "0x" + G2Basic.SkToPk(signer_privkey).hex()
    unsigned = {
        "authority_hash": _require_hash(authority_hash, name="authority_hash"),
        "authority_state_root_hash": _require_hash(
            authority_state_root_hash,
            name="authority_state_root_hash",
        ),
        "market_id": _require_account(market_id, name="market_id"),
        "policy_hash": _require_hash(policy_hash, name="policy_hash"),
        "schema": RECOVERY_SOURCE_AUTHORITY_BINDING_SCHEMA,
        "signer_pubkey": signer_pubkey,
        "valid_from_epoch": _require_non_negative_int(
            valid_from_epoch,
            name="valid_from_epoch",
        ),
        "valid_until_epoch": _require_non_negative_int(
            valid_until_epoch,
            name="valid_until_epoch",
        ),
    }
    if int(unsigned["valid_from_epoch"]) > int(unsigned["valid_until_epoch"]):
        raise ValueError("valid_from_epoch must be <= valid_until_epoch")
    signature = "0x" + G2Basic.Sign(
        signer_privkey,
        _signature_message(unsigned),
    ).hex()
    return FundingCloseoutRecoverySourceAuthorityBinding(
        schema=RECOVERY_SOURCE_AUTHORITY_BINDING_SCHEMA,
        market_id=str(unsigned["market_id"]),
        valid_from_epoch=int(unsigned["valid_from_epoch"]),
        valid_until_epoch=int(unsigned["valid_until_epoch"]),
        authority_hash=str(unsigned["authority_hash"]),
        authority_state_root_hash=str(unsigned["authority_state_root_hash"]),
        policy_hash=str(unsigned["policy_hash"]),
        signer_pubkey=signer_pubkey,
        signature=signature,
        canonical_sha256="sha256:"
        + hashlib.sha256(canonical_json_bytes(unsigned)).hexdigest(),
    )


def build_funding_closeout_receiver_recovery_distribution_certificate(
    policy_ledger: FundingCloseoutPolicyLedger,
    priority_certificate: FundingCloseoutRecoveryPriorityCertificate,
    *,
    distribution_policy: str = RECEIVER_DISTRIBUTION_LARGEST_REMAINDER,
) -> FundingCloseoutReceiverRecoveryDistributionCertificate:
    validate_recovery_priority_certificate_against_policy_ledger(
        priority_certificate,
        policy_ledger,
    )
    policy = _require_receiver_distribution_policy(distribution_policy)
    claims = tuple(
        (row.account_pubkey, row.recoverable_claim_quote)
        for row in policy_ledger.receiver_haircut_rows
    )
    rows = compute_receiver_largest_remainder_distribution(
        claims,
        total_receiver_recovery_quote=priority_certificate.receiver_recovery_quote,
    )
    return FundingCloseoutReceiverRecoveryDistributionCertificate(
        schema=RECEIVER_RECOVERY_DISTRIBUTION_SCHEMA,
        market_id=policy_ledger.market_id,
        epoch=policy_ledger.epoch,
        policy_ledger_hash=funding_closeout_policy_ledger_hash(policy_ledger),
        priority_certificate_hash=funding_closeout_recovery_priority_certificate_hash(
            priority_certificate
        ),
        distribution_policy=policy,
        total_receiver_recovery_quote=priority_certificate.receiver_recovery_quote,
        total_recoverable_claim_quote=policy_ledger.total_recoverable_claim_quote,
        receiver_rows=rows,
    )


def build_funding_closeout_sink_recovery_distribution_certificate(
    policy_ledger: FundingCloseoutPolicyLedger,
    priority_certificate: FundingCloseoutRecoveryPriorityCertificate,
    *,
    distribution_policy: str = SINK_DISTRIBUTION_LARGEST_REMAINDER,
) -> FundingCloseoutSinkRecoveryDistributionCertificate:
    validate_recovery_priority_certificate_against_policy_ledger(
        priority_certificate,
        policy_ledger,
    )
    policy = _require_sink_distribution_policy(distribution_policy)
    claims = tuple(
        (row.account_pubkey, row.claimant, row.subrogated_claim_quote)
        for row in policy_ledger.sink_subrogation_rows
    )
    rows = compute_sink_largest_remainder_distribution(
        claims,
        total_sink_recovery_quote=priority_certificate.sink_recovery_quote,
    )
    return FundingCloseoutSinkRecoveryDistributionCertificate(
        schema=SINK_RECOVERY_DISTRIBUTION_SCHEMA,
        market_id=policy_ledger.market_id,
        epoch=policy_ledger.epoch,
        policy_ledger_hash=funding_closeout_policy_ledger_hash(policy_ledger),
        priority_certificate_hash=funding_closeout_recovery_priority_certificate_hash(
            priority_certificate
        ),
        distribution_policy=policy,
        total_sink_recovery_quote=priority_certificate.sink_recovery_quote,
        total_subrogated_claim_quote=policy_ledger.total_subrogated_claim_quote,
        sink_rows=rows,
    )


def funding_closeout_recovery_priority_certificate_to_payload(
    certificate: FundingCloseoutRecoveryPriorityCertificate,
) -> dict[str, object]:
    if not isinstance(certificate, FundingCloseoutRecoveryPriorityCertificate):
        raise TypeError(
            "certificate must be a FundingCloseoutRecoveryPriorityCertificate"
        )
    return {
        "schema": certificate.schema,
        "market_id": certificate.market_id,
        "epoch": certificate.epoch,
        "policy_ledger_hash": certificate.policy_ledger_hash,
        "priority_policy": certificate.priority_policy,
        "source_capacity_quote": certificate.source_capacity_quote,
        "total_recoverable_claim_quote": certificate.total_recoverable_claim_quote,
        "total_subrogated_claim_quote": certificate.total_subrogated_claim_quote,
        "receiver_recovery_quote": certificate.receiver_recovery_quote,
        "sink_recovery_quote": certificate.sink_recovery_quote,
    }


def funding_closeout_recovery_collection_receipt_to_payload(
    receipt: FundingCloseoutRecoveryCollectionReceipt,
) -> dict[str, object]:
    if not isinstance(receipt, FundingCloseoutRecoveryCollectionReceipt):
        raise TypeError(
            "receipt must be a FundingCloseoutRecoveryCollectionReceipt"
        )
    return {
        "schema": receipt.schema,
        "market_id": receipt.market_id,
        "epoch": receipt.epoch,
        "policy_ledger_hash": receipt.policy_ledger_hash,
        "priority_certificate_hash": receipt.priority_certificate_hash,
        "source_id": receipt.source_id,
        "collection_nonce": receipt.collection_nonce,
        "source_capacity_quote": receipt.source_capacity_quote,
        "collected_source_quote": receipt.collected_source_quote,
    }


def funding_closeout_recovery_source_authority_to_payload(
    authority: FundingCloseoutRecoverySourceAuthority,
) -> dict[str, object]:
    if not isinstance(authority, FundingCloseoutRecoverySourceAuthority):
        raise TypeError(
            "authority must be a FundingCloseoutRecoverySourceAuthority"
        )
    payload = _recovery_source_authority_unsigned_payload(authority)
    payload["canonical_sha256"] = authority.canonical_sha256
    return payload


def funding_closeout_recovery_source_authority_binding_to_payload(
    binding: FundingCloseoutRecoverySourceAuthorityBinding,
) -> dict[str, object]:
    if not isinstance(binding, FundingCloseoutRecoverySourceAuthorityBinding):
        raise TypeError(
            "binding must be a FundingCloseoutRecoverySourceAuthorityBinding"
        )
    return binding.to_payload()


def funding_closeout_receiver_recovery_distribution_certificate_to_payload(
    certificate: FundingCloseoutReceiverRecoveryDistributionCertificate,
) -> dict[str, object]:
    if not isinstance(
        certificate,
        FundingCloseoutReceiverRecoveryDistributionCertificate,
    ):
        raise TypeError(
            "certificate must be a FundingCloseoutReceiverRecoveryDistributionCertificate"
        )
    return {
        "schema": certificate.schema,
        "market_id": certificate.market_id,
        "epoch": certificate.epoch,
        "policy_ledger_hash": certificate.policy_ledger_hash,
        "priority_certificate_hash": certificate.priority_certificate_hash,
        "distribution_policy": certificate.distribution_policy,
        "total_receiver_recovery_quote": certificate.total_receiver_recovery_quote,
        "total_recoverable_claim_quote": certificate.total_recoverable_claim_quote,
        "receiver_rows": [
            {
                "account_pubkey": row.account_pubkey,
                "recoverable_claim_quote": row.recoverable_claim_quote,
                "recovery_quote": row.recovery_quote,
            }
            for row in certificate.receiver_rows
        ],
    }


def funding_closeout_sink_recovery_distribution_certificate_to_payload(
    certificate: FundingCloseoutSinkRecoveryDistributionCertificate,
) -> dict[str, object]:
    if not isinstance(
        certificate,
        FundingCloseoutSinkRecoveryDistributionCertificate,
    ):
        raise TypeError(
            "certificate must be a FundingCloseoutSinkRecoveryDistributionCertificate"
        )
    return {
        "schema": certificate.schema,
        "market_id": certificate.market_id,
        "epoch": certificate.epoch,
        "policy_ledger_hash": certificate.policy_ledger_hash,
        "priority_certificate_hash": certificate.priority_certificate_hash,
        "distribution_policy": certificate.distribution_policy,
        "total_sink_recovery_quote": certificate.total_sink_recovery_quote,
        "total_subrogated_claim_quote": certificate.total_subrogated_claim_quote,
        "sink_rows": [
            {
                "account_pubkey": row.account_pubkey,
                "claimant": row.claimant,
                "subrogated_claim_quote": row.subrogated_claim_quote,
                "recovery_quote": row.recovery_quote,
            }
            for row in certificate.sink_rows
        ],
    }


def funding_closeout_recovery_priority_certificate_hash(
    certificate: FundingCloseoutRecoveryPriorityCertificate,
) -> str:
    return "sha256:" + hashlib.sha256(
        canonical_json_bytes(
            funding_closeout_recovery_priority_certificate_to_payload(certificate)
        )
    ).hexdigest()


def funding_closeout_recovery_collection_receipt_hash(
    receipt: FundingCloseoutRecoveryCollectionReceipt,
) -> str:
    return "sha256:" + hashlib.sha256(
        canonical_json_bytes(
            funding_closeout_recovery_collection_receipt_to_payload(receipt)
        )
    ).hexdigest()


def funding_closeout_recovery_source_authority_hash(
    authority: FundingCloseoutRecoverySourceAuthority,
) -> str:
    if not isinstance(authority, FundingCloseoutRecoverySourceAuthority):
        raise TypeError(
            "authority must be a FundingCloseoutRecoverySourceAuthority"
        )
    return "sha256:" + hashlib.sha256(
        canonical_json_bytes(_recovery_source_authority_unsigned_payload(authority))
    ).hexdigest()


def funding_closeout_recovery_source_authority_binding_hash(
    binding: FundingCloseoutRecoverySourceAuthorityBinding,
) -> str:
    if not isinstance(binding, FundingCloseoutRecoverySourceAuthorityBinding):
        raise TypeError(
            "binding must be a FundingCloseoutRecoverySourceAuthorityBinding"
        )
    return "sha256:" + hashlib.sha256(
        canonical_json_bytes(binding.unsigned_payload())
    ).hexdigest()


def funding_closeout_receiver_recovery_distribution_certificate_hash(
    certificate: FundingCloseoutReceiverRecoveryDistributionCertificate,
) -> str:
    return "sha256:" + hashlib.sha256(
        canonical_json_bytes(
            funding_closeout_receiver_recovery_distribution_certificate_to_payload(
                certificate
            )
        )
    ).hexdigest()


def funding_closeout_sink_recovery_distribution_certificate_hash(
    certificate: FundingCloseoutSinkRecoveryDistributionCertificate,
) -> str:
    return "sha256:" + hashlib.sha256(
        canonical_json_bytes(
            funding_closeout_sink_recovery_distribution_certificate_to_payload(
                certificate
            )
        )
    ).hexdigest()


def funding_closeout_recovery_priority_certificate_from_payload(
    payload: object,
) -> FundingCloseoutRecoveryPriorityCertificate:
    data = _require_payload_mapping(payload, name="recovery_priority_certificate")
    _require_exact_keys(
        data,
        name="recovery_priority_certificate",
        keys={
            "schema",
            "market_id",
            "epoch",
            "policy_ledger_hash",
            "priority_policy",
            "source_capacity_quote",
            "total_recoverable_claim_quote",
            "total_subrogated_claim_quote",
            "receiver_recovery_quote",
            "sink_recovery_quote",
        },
    )
    schema = data["schema"]
    if not isinstance(schema, str):
        raise TypeError("schema must be a str")
    return FundingCloseoutRecoveryPriorityCertificate(
        schema=schema,
        market_id=_require_account(data["market_id"], name="market_id"),
        epoch=_require_non_negative_int(data["epoch"], name="epoch"),
        policy_ledger_hash=_require_hash(
            data["policy_ledger_hash"],
            name="policy_ledger_hash",
        ),
        priority_policy=_require_priority_policy(data["priority_policy"]),
        source_capacity_quote=_require_non_negative_int(
            data["source_capacity_quote"],
            name="source_capacity_quote",
        ),
        total_recoverable_claim_quote=_require_non_negative_int(
            data["total_recoverable_claim_quote"],
            name="total_recoverable_claim_quote",
        ),
        total_subrogated_claim_quote=_require_non_negative_int(
            data["total_subrogated_claim_quote"],
            name="total_subrogated_claim_quote",
        ),
        receiver_recovery_quote=_require_non_negative_int(
            data["receiver_recovery_quote"],
            name="receiver_recovery_quote",
        ),
        sink_recovery_quote=_require_non_negative_int(
            data["sink_recovery_quote"],
            name="sink_recovery_quote",
        ),
    )


def funding_closeout_recovery_collection_receipt_from_payload(
    payload: object,
) -> FundingCloseoutRecoveryCollectionReceipt:
    data = _require_payload_mapping(payload, name="recovery_collection_receipt")
    _require_exact_keys(
        data,
        name="recovery_collection_receipt",
        keys={
            "schema",
            "market_id",
            "epoch",
            "policy_ledger_hash",
            "priority_certificate_hash",
            "source_id",
            "collection_nonce",
            "source_capacity_quote",
            "collected_source_quote",
        },
    )
    schema = data["schema"]
    if not isinstance(schema, str):
        raise TypeError("schema must be a str")
    return FundingCloseoutRecoveryCollectionReceipt(
        schema=schema,
        market_id=_require_account(data["market_id"], name="market_id"),
        epoch=_require_non_negative_int(data["epoch"], name="epoch"),
        policy_ledger_hash=_require_hash(
            data["policy_ledger_hash"],
            name="policy_ledger_hash",
        ),
        priority_certificate_hash=_require_hash(
            data["priority_certificate_hash"],
            name="priority_certificate_hash",
        ),
        source_id=_require_account(data["source_id"], name="source_id"),
        collection_nonce=_require_non_negative_int(
            data["collection_nonce"],
            name="collection_nonce",
        ),
        source_capacity_quote=_require_non_negative_int(
            data["source_capacity_quote"],
            name="source_capacity_quote",
        ),
        collected_source_quote=_require_non_negative_int(
            data["collected_source_quote"],
            name="collected_source_quote",
        ),
    )


def funding_closeout_recovery_source_authority_from_payload(
    payload: object,
) -> FundingCloseoutRecoverySourceAuthority:
    data = _require_payload_mapping(payload, name="recovery_source_authority")
    _require_exact_keys(
        data,
        name="recovery_source_authority",
        keys={
            "schema",
            "market_id",
            "valid_from_epoch",
            "valid_until_epoch",
            "authorized_source_ids",
            "canonical_sha256",
        },
    )
    schema = data["schema"]
    if not isinstance(schema, str):
        raise TypeError("schema must be a str")
    source_ids_raw = data["authorized_source_ids"]
    if not isinstance(source_ids_raw, list):
        raise TypeError("authorized_source_ids must be a list")
    return FundingCloseoutRecoverySourceAuthority(
        schema=schema,
        market_id=_require_account(data["market_id"], name="market_id"),
        valid_from_epoch=_require_non_negative_int(
            data["valid_from_epoch"],
            name="valid_from_epoch",
        ),
        valid_until_epoch=_require_non_negative_int(
            data["valid_until_epoch"],
            name="valid_until_epoch",
        ),
        authorized_source_ids=tuple(source_ids_raw),
        canonical_sha256=_require_hash(
            data["canonical_sha256"],
            name="canonical_sha256",
        ),
    )


def funding_closeout_recovery_source_authority_binding_from_payload(
    payload: object,
) -> FundingCloseoutRecoverySourceAuthorityBinding:
    data = _require_payload_mapping(
        payload,
        name="recovery_source_authority_binding",
    )
    _require_exact_keys(
        data,
        name="recovery_source_authority_binding",
        keys=_RECOVERY_SOURCE_AUTHORITY_BINDING_KEYS,
    )
    schema = data["schema"]
    if not isinstance(schema, str):
        raise TypeError("schema must be a str")
    return FundingCloseoutRecoverySourceAuthorityBinding(
        schema=schema,
        market_id=_require_account(data["market_id"], name="market_id"),
        valid_from_epoch=_require_non_negative_int(
            data["valid_from_epoch"],
            name="valid_from_epoch",
        ),
        valid_until_epoch=_require_non_negative_int(
            data["valid_until_epoch"],
            name="valid_until_epoch",
        ),
        authority_hash=_require_hash(data["authority_hash"], name="authority_hash"),
        authority_state_root_hash=_require_hash(
            data["authority_state_root_hash"],
            name="authority_state_root_hash",
        ),
        policy_hash=_require_hash(data["policy_hash"], name="policy_hash"),
        signer_pubkey=_require_prefixed_hex(
            data["signer_pubkey"],
            name="signer_pubkey",
            nbytes=48,
        ),
        signature=_require_prefixed_hex(
            data["signature"],
            name="signature",
            nbytes=96,
        ),
        canonical_sha256=_require_hash(
            data["canonical_sha256"],
            name="canonical_sha256",
        ),
    )


def _receiver_recovery_distribution_row_from_payload(
    row: object,
) -> ReceiverRecoveryDistributionRow:
    data = _require_payload_mapping(row, name="receiver_recovery_distribution_row")
    _require_exact_keys(
        data,
        name="receiver_recovery_distribution_row",
        keys={
            "account_pubkey",
            "recoverable_claim_quote",
            "recovery_quote",
        },
    )
    return ReceiverRecoveryDistributionRow(
        account_pubkey=_require_account(data["account_pubkey"], name="account_pubkey"),
        recoverable_claim_quote=_require_non_negative_int(
            data["recoverable_claim_quote"],
            name="recoverable_claim_quote",
        ),
        recovery_quote=_require_non_negative_int(
            data["recovery_quote"],
            name="recovery_quote",
        ),
    )


def _sink_recovery_distribution_row_from_payload(
    row: object,
) -> SinkRecoveryDistributionRow:
    data = _require_payload_mapping(row, name="sink_recovery_distribution_row")
    _require_exact_keys(
        data,
        name="sink_recovery_distribution_row",
        keys={
            "account_pubkey",
            "claimant",
            "subrogated_claim_quote",
            "recovery_quote",
        },
    )
    return SinkRecoveryDistributionRow(
        account_pubkey=_require_account(data["account_pubkey"], name="account_pubkey"),
        claimant=_require_account(data["claimant"], name="claimant"),
        subrogated_claim_quote=_require_non_negative_int(
            data["subrogated_claim_quote"],
            name="subrogated_claim_quote",
        ),
        recovery_quote=_require_non_negative_int(
            data["recovery_quote"],
            name="recovery_quote",
        ),
    )


def funding_closeout_receiver_recovery_distribution_certificate_from_payload(
    payload: object,
) -> FundingCloseoutReceiverRecoveryDistributionCertificate:
    data = _require_payload_mapping(
        payload,
        name="receiver_recovery_distribution_certificate",
    )
    _require_exact_keys(
        data,
        name="receiver_recovery_distribution_certificate",
        keys={
            "schema",
            "market_id",
            "epoch",
            "policy_ledger_hash",
            "priority_certificate_hash",
            "distribution_policy",
            "total_receiver_recovery_quote",
            "total_recoverable_claim_quote",
            "receiver_rows",
        },
    )
    schema = data["schema"]
    if not isinstance(schema, str):
        raise TypeError("schema must be a str")
    return FundingCloseoutReceiverRecoveryDistributionCertificate(
        schema=schema,
        market_id=_require_account(data["market_id"], name="market_id"),
        epoch=_require_non_negative_int(data["epoch"], name="epoch"),
        policy_ledger_hash=_require_hash(
            data["policy_ledger_hash"],
            name="policy_ledger_hash",
        ),
        priority_certificate_hash=_require_hash(
            data["priority_certificate_hash"],
            name="priority_certificate_hash",
        ),
        distribution_policy=_require_receiver_distribution_policy(
            data["distribution_policy"]
        ),
        total_receiver_recovery_quote=_require_non_negative_int(
            data["total_receiver_recovery_quote"],
            name="total_receiver_recovery_quote",
        ),
        total_recoverable_claim_quote=_require_non_negative_int(
            data["total_recoverable_claim_quote"],
            name="total_recoverable_claim_quote",
        ),
        receiver_rows=tuple(
            _receiver_recovery_distribution_row_from_payload(row)
            for row in _require_payload_list(
                data["receiver_rows"],
                name="receiver_rows",
            )
        ),
    )


def funding_closeout_sink_recovery_distribution_certificate_from_payload(
    payload: object,
) -> FundingCloseoutSinkRecoveryDistributionCertificate:
    data = _require_payload_mapping(
        payload,
        name="sink_recovery_distribution_certificate",
    )
    _require_exact_keys(
        data,
        name="sink_recovery_distribution_certificate",
        keys={
            "schema",
            "market_id",
            "epoch",
            "policy_ledger_hash",
            "priority_certificate_hash",
            "distribution_policy",
            "total_sink_recovery_quote",
            "total_subrogated_claim_quote",
            "sink_rows",
        },
    )
    schema = data["schema"]
    if not isinstance(schema, str):
        raise TypeError("schema must be a str")
    return FundingCloseoutSinkRecoveryDistributionCertificate(
        schema=schema,
        market_id=_require_account(data["market_id"], name="market_id"),
        epoch=_require_non_negative_int(data["epoch"], name="epoch"),
        policy_ledger_hash=_require_hash(
            data["policy_ledger_hash"],
            name="policy_ledger_hash",
        ),
        priority_certificate_hash=_require_hash(
            data["priority_certificate_hash"],
            name="priority_certificate_hash",
        ),
        distribution_policy=_require_sink_distribution_policy(
            data["distribution_policy"]
        ),
        total_sink_recovery_quote=_require_non_negative_int(
            data["total_sink_recovery_quote"],
            name="total_sink_recovery_quote",
        ),
        total_subrogated_claim_quote=_require_non_negative_int(
            data["total_subrogated_claim_quote"],
            name="total_subrogated_claim_quote",
        ),
        sink_rows=tuple(
            _sink_recovery_distribution_row_from_payload(row)
            for row in _require_payload_list(
                data["sink_rows"],
                name="sink_rows",
            )
        ),
    )


def validate_recovery_priority_certificate_against_policy_ledger(
    certificate: FundingCloseoutRecoveryPriorityCertificate,
    policy_ledger: FundingCloseoutPolicyLedger,
) -> None:
    if not isinstance(certificate, FundingCloseoutRecoveryPriorityCertificate):
        raise TypeError(
            "certificate must be a FundingCloseoutRecoveryPriorityCertificate"
        )
    if not isinstance(policy_ledger, FundingCloseoutPolicyLedger):
        raise TypeError("policy_ledger must be a FundingCloseoutPolicyLedger")
    if certificate.market_id != policy_ledger.market_id:
        raise ValueError("recovery priority market_id mismatch")
    if certificate.epoch != policy_ledger.epoch:
        raise ValueError("recovery priority epoch mismatch")
    if certificate.policy_ledger_hash != funding_closeout_policy_ledger_hash(
        policy_ledger
    ):
        raise ValueError("recovery priority policy ledger hash mismatch")
    if (
        certificate.total_recoverable_claim_quote
        != policy_ledger.total_recoverable_claim_quote
    ):
        raise ValueError("recovery priority recoverable claim total mismatch")
    if (
        certificate.total_subrogated_claim_quote
        != policy_ledger.total_subrogated_claim_quote
    ):
        raise ValueError("recovery priority subrogated claim total mismatch")


def validate_recovery_collection_receipt_against_sources(
    receipt: FundingCloseoutRecoveryCollectionReceipt,
    policy_ledger: FundingCloseoutPolicyLedger,
    priority_certificate: FundingCloseoutRecoveryPriorityCertificate,
) -> None:
    if not isinstance(receipt, FundingCloseoutRecoveryCollectionReceipt):
        raise TypeError("receipt must be a FundingCloseoutRecoveryCollectionReceipt")
    validate_recovery_priority_certificate_against_policy_ledger(
        priority_certificate,
        policy_ledger,
    )
    if receipt.market_id != policy_ledger.market_id:
        raise ValueError("recovery collection market_id mismatch")
    if receipt.epoch != policy_ledger.epoch:
        raise ValueError("recovery collection epoch mismatch")
    if receipt.policy_ledger_hash != funding_closeout_policy_ledger_hash(
        policy_ledger
    ):
        raise ValueError("recovery collection policy ledger hash mismatch")
    if (
        receipt.priority_certificate_hash
        != funding_closeout_recovery_priority_certificate_hash(priority_certificate)
    ):
        raise ValueError("recovery collection priority certificate hash mismatch")
    if receipt.source_capacity_quote != priority_certificate.source_capacity_quote:
        raise ValueError("recovery collection source capacity mismatch")
    credited = (
        priority_certificate.receiver_recovery_quote
        + priority_certificate.sink_recovery_quote
    )
    if receipt.collected_source_quote != credited:
        raise ValueError("recovery collection credited amount mismatch")


def validate_recovery_source_authority_for_sources(
    authority: FundingCloseoutRecoverySourceAuthority,
    *,
    expected_market_id: str,
    now_epoch: int,
    required_source_ids: tuple[str, ...],
) -> None:
    if not isinstance(authority, FundingCloseoutRecoverySourceAuthority):
        raise TypeError(
            "authority must be a FundingCloseoutRecoverySourceAuthority"
        )
    market_id = _require_account(expected_market_id, name="expected_market_id")
    epoch = _require_non_negative_int(now_epoch, name="now_epoch")
    required_sources = _require_source_ids(required_source_ids)
    if authority.market_id != market_id:
        raise ValueError("recovery source authority market_id mismatch")
    if epoch < authority.valid_from_epoch or epoch > authority.valid_until_epoch:
        raise ValueError("recovery source authority epoch out of range")
    authorized = set(authority.authorized_source_ids)
    for source_id in required_sources:
        if source_id not in authorized:
            raise ValueError(f"recovery source_id not authorized: {source_id}")


def verify_funding_closeout_recovery_source_authority_binding_payload(
    payload: object,
    *,
    authority: FundingCloseoutRecoverySourceAuthority,
    expected_market_id: str,
    now_epoch: int,
    expected_authority_state_root_hash: str,
    expected_policy_hash: str,
    allowed_signer_pubkeys: tuple[str, ...],
) -> RecoverySourceAuthorityBindingVerdict:
    if not isinstance(payload, Mapping):
        return RecoverySourceAuthorityBindingVerdict(
            False,
            "recovery source authority binding must be an object",
        )
    try:
        if not isinstance(authority, FundingCloseoutRecoverySourceAuthority):
            raise TypeError(
                "authority must be a FundingCloseoutRecoverySourceAuthority"
            )
        binding = funding_closeout_recovery_source_authority_binding_from_payload(
            payload
        )
        market_id = _require_account(expected_market_id, name="expected_market_id")
        epoch = _require_non_negative_int(now_epoch, name="now_epoch")
        expected_root = _require_hash(
            expected_authority_state_root_hash,
            name="expected_authority_state_root_hash",
        )
        expected_policy = _require_hash(
            expected_policy_hash,
            name="expected_policy_hash",
        )
        allowed_signers = _require_signer_pubkeys(
            allowed_signer_pubkeys,
            name="allowed_signer_pubkeys",
        )
        if binding.market_id != market_id:
            return RecoverySourceAuthorityBindingVerdict(
                False,
                "recovery source authority binding market_id mismatch",
            )
        if epoch < binding.valid_from_epoch or epoch > binding.valid_until_epoch:
            return RecoverySourceAuthorityBindingVerdict(
                False,
                "recovery source authority binding epoch out of range",
            )
        if binding.authority_hash != funding_closeout_recovery_source_authority_hash(
            authority
        ):
            return RecoverySourceAuthorityBindingVerdict(
                False,
                "recovery source authority binding authority_hash mismatch",
            )
        if binding.authority_state_root_hash != expected_root:
            return RecoverySourceAuthorityBindingVerdict(
                False,
                "recovery source authority binding state_root_hash mismatch",
            )
        if binding.policy_hash != expected_policy:
            return RecoverySourceAuthorityBindingVerdict(
                False,
                "recovery source authority binding policy_hash mismatch",
            )
        if binding.signer_pubkey not in allowed_signers:
            return RecoverySourceAuthorityBindingVerdict(
                False,
                "recovery source authority binding signer not allowed",
            )
        try:
            signature_ok = G2Basic.Verify(
                bytes.fromhex(binding.signer_pubkey.removeprefix("0x")),
                _signature_message(binding.unsigned_payload()),
                bytes.fromhex(binding.signature.removeprefix("0x")),
            )
        except AssertionError:
            signature_ok = False
        if not signature_ok:
            return RecoverySourceAuthorityBindingVerdict(
                False,
                "recovery source authority binding signature invalid",
            )
    except (TypeError, ValueError) as exc:
        return RecoverySourceAuthorityBindingVerdict(False, str(exc))
    return RecoverySourceAuthorityBindingVerdict(True, None, binding)


def validate_receiver_recovery_distribution_against_sources(
    certificate: FundingCloseoutReceiverRecoveryDistributionCertificate,
    policy_ledger: FundingCloseoutPolicyLedger,
    priority_certificate: FundingCloseoutRecoveryPriorityCertificate,
) -> None:
    if not isinstance(
        certificate,
        FundingCloseoutReceiverRecoveryDistributionCertificate,
    ):
        raise TypeError(
            "certificate must be a FundingCloseoutReceiverRecoveryDistributionCertificate"
        )
    validate_recovery_priority_certificate_against_policy_ledger(
        priority_certificate,
        policy_ledger,
    )
    if certificate.market_id != policy_ledger.market_id:
        raise ValueError("receiver distribution market_id mismatch")
    if certificate.epoch != policy_ledger.epoch:
        raise ValueError("receiver distribution epoch mismatch")
    if certificate.policy_ledger_hash != funding_closeout_policy_ledger_hash(
        policy_ledger
    ):
        raise ValueError("receiver distribution policy ledger hash mismatch")
    if (
        certificate.priority_certificate_hash
        != funding_closeout_recovery_priority_certificate_hash(priority_certificate)
    ):
        raise ValueError("receiver distribution priority certificate hash mismatch")
    if (
        certificate.total_receiver_recovery_quote
        != priority_certificate.receiver_recovery_quote
    ):
        raise ValueError("receiver distribution recovery total mismatch")
    if (
        certificate.total_recoverable_claim_quote
        != policy_ledger.total_recoverable_claim_quote
    ):
        raise ValueError("receiver distribution recoverable claim total mismatch")
    expected_rows = compute_receiver_largest_remainder_distribution(
        tuple(
            (row.account_pubkey, row.recoverable_claim_quote)
            for row in policy_ledger.receiver_haircut_rows
        ),
        total_receiver_recovery_quote=priority_certificate.receiver_recovery_quote,
    )
    if certificate.receiver_rows != expected_rows:
        raise ValueError("receiver distribution rows mismatch")


def validate_sink_recovery_distribution_against_sources(
    certificate: FundingCloseoutSinkRecoveryDistributionCertificate,
    policy_ledger: FundingCloseoutPolicyLedger,
    priority_certificate: FundingCloseoutRecoveryPriorityCertificate,
) -> None:
    if not isinstance(
        certificate,
        FundingCloseoutSinkRecoveryDistributionCertificate,
    ):
        raise TypeError(
            "certificate must be a FundingCloseoutSinkRecoveryDistributionCertificate"
        )
    validate_recovery_priority_certificate_against_policy_ledger(
        priority_certificate,
        policy_ledger,
    )
    if certificate.market_id != policy_ledger.market_id:
        raise ValueError("sink distribution market_id mismatch")
    if certificate.epoch != policy_ledger.epoch:
        raise ValueError("sink distribution epoch mismatch")
    if certificate.policy_ledger_hash != funding_closeout_policy_ledger_hash(
        policy_ledger
    ):
        raise ValueError("sink distribution policy ledger hash mismatch")
    if (
        certificate.priority_certificate_hash
        != funding_closeout_recovery_priority_certificate_hash(priority_certificate)
    ):
        raise ValueError("sink distribution priority certificate hash mismatch")
    if certificate.total_sink_recovery_quote != priority_certificate.sink_recovery_quote:
        raise ValueError("sink distribution recovery total mismatch")
    if (
        certificate.total_subrogated_claim_quote
        != policy_ledger.total_subrogated_claim_quote
    ):
        raise ValueError("sink distribution subrogated claim total mismatch")
    expected_rows = compute_sink_largest_remainder_distribution(
        tuple(
            (row.account_pubkey, row.claimant, row.subrogated_claim_quote)
            for row in policy_ledger.sink_subrogation_rows
        ),
        total_sink_recovery_quote=priority_certificate.sink_recovery_quote,
    )
    if certificate.sink_rows != expected_rows:
        raise ValueError("sink distribution rows mismatch")


def verify_funding_closeout_recovery_priority_certificate_payload(
    payload: object,
    *,
    policy_ledger: FundingCloseoutPolicyLedger | None = None,
) -> RecoveryPriorityVerdict:
    try:
        certificate = funding_closeout_recovery_priority_certificate_from_payload(
            payload
        )
        if policy_ledger is not None:
            validate_recovery_priority_certificate_against_policy_ledger(
                certificate,
                policy_ledger,
            )
    except (TypeError, ValueError) as exc:
        return RecoveryPriorityVerdict(False, str(exc))
    return RecoveryPriorityVerdict(True, None)


def verify_funding_closeout_recovery_collection_receipt_payload(
    payload: object,
    *,
    policy_ledger: FundingCloseoutPolicyLedger | None = None,
    priority_certificate: FundingCloseoutRecoveryPriorityCertificate | None = None,
) -> RecoveryPriorityVerdict:
    try:
        receipt = funding_closeout_recovery_collection_receipt_from_payload(payload)
        if (policy_ledger is None) != (priority_certificate is None):
            raise ValueError(
                "policy_ledger and priority_certificate must be provided together"
            )
        if policy_ledger is not None and priority_certificate is not None:
            validate_recovery_collection_receipt_against_sources(
                receipt,
                policy_ledger,
                priority_certificate,
            )
    except (TypeError, ValueError) as exc:
        return RecoveryPriorityVerdict(False, str(exc))
    return RecoveryPriorityVerdict(True, None)


def verify_funding_closeout_recovery_source_authority_payload(
    payload: object,
    *,
    expected_market_id: str,
    now_epoch: int,
    required_source_ids: tuple[str, ...],
) -> RecoverySourceAuthorityVerdict:
    try:
        authority = funding_closeout_recovery_source_authority_from_payload(payload)
        validate_recovery_source_authority_for_sources(
            authority,
            expected_market_id=expected_market_id,
            now_epoch=now_epoch,
            required_source_ids=required_source_ids,
        )
    except (TypeError, ValueError) as exc:
        return RecoverySourceAuthorityVerdict(False, str(exc), None)
    return RecoverySourceAuthorityVerdict(True, None, authority)


def verify_funding_closeout_receiver_recovery_distribution_payload(
    payload: object,
    *,
    policy_ledger: FundingCloseoutPolicyLedger | None = None,
    priority_certificate: FundingCloseoutRecoveryPriorityCertificate | None = None,
) -> RecoveryPriorityVerdict:
    try:
        certificate = (
            funding_closeout_receiver_recovery_distribution_certificate_from_payload(
                payload
            )
        )
        if (policy_ledger is None) != (priority_certificate is None):
            raise ValueError(
                "policy_ledger and priority_certificate must be provided together"
            )
        if policy_ledger is not None and priority_certificate is not None:
            validate_receiver_recovery_distribution_against_sources(
                certificate,
                policy_ledger,
                priority_certificate,
            )
    except (TypeError, ValueError) as exc:
        return RecoveryPriorityVerdict(False, str(exc))
    return RecoveryPriorityVerdict(True, None)


def verify_funding_closeout_sink_recovery_distribution_payload(
    payload: object,
    *,
    policy_ledger: FundingCloseoutPolicyLedger | None = None,
    priority_certificate: FundingCloseoutRecoveryPriorityCertificate | None = None,
) -> RecoveryPriorityVerdict:
    try:
        certificate = (
            funding_closeout_sink_recovery_distribution_certificate_from_payload(
                payload
            )
        )
        if policy_ledger is not None or priority_certificate is not None:
            if policy_ledger is None or priority_certificate is None:
                raise ValueError(
                    "policy_ledger and priority_certificate must be provided together"
                )
            validate_sink_recovery_distribution_against_sources(
                certificate,
                policy_ledger,
                priority_certificate,
            )
    except (TypeError, ValueError) as exc:
        return RecoveryPriorityVerdict(False, str(exc))
    return RecoveryPriorityVerdict(True, None)
