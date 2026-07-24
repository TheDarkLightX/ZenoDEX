"""Bounded application-neutral values for sampled retrievability evidence."""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Final, Mapping

from src.integration.zeno_ledger_v0 import hash_v0
from src.state.canonical import canonical_hex_fixed_allow_0x

MAX_U64: Final = (1 << 64) - 1
# Eight max-size, eight-opening response records remain representable inside
# the 20 MiB exact-evidence cap after the outer canonical hex encoding.
MAX_PROVIDERS_V1: Final = 8
MAX_CHALLENGES_PER_PROVIDER_V1: Final = 8
MAX_RESPONSE_WINDOW_EPOCHS_V1: Final = 64
MAX_EXACT_RESPONSE_BYTES_V1: Final = 2 * 1_024 * 1_024
MAX_EXACT_EVIDENCE_BYTES_V1: Final = 20 * 1_024 * 1_024

_TOKEN_RE: Final = re.compile(r"^[A-Za-z0-9_.:/-]{1,128}$")


def require_root(value: object, *, name: str) -> str:
    if type(value) is not str:
        raise TypeError(f"{name} must be a str")
    canonical = canonical_hex_fixed_allow_0x(value, nbytes=32, name=name)
    if value != canonical or value == "0x" + "00" * 32:
        raise ValueError(f"{name} must be canonical nonzero lowercase hex")
    return canonical


def require_u64(value: object, *, name: str) -> int:
    if type(value) is not int or not 0 <= value <= MAX_U64:
        raise ValueError(f"{name} must be a u64")
    return value


def require_token(value: object, *, name: str) -> str:
    if type(value) is not str or _TOKEN_RE.fullmatch(value) is None:
        raise ValueError(f"{name} must be a bounded canonical token")
    return value


def require_bls_public_key(value: object, *, name: str) -> str:
    if type(value) is not str:
        raise TypeError(f"{name} must be a str")
    canonical = canonical_hex_fixed_allow_0x(value, nbytes=48, name=name)
    if value != canonical:
        raise ValueError(f"{name} must be canonical lowercase hex")
    return canonical


@dataclass(frozen=True, slots=True)
class ProviderKeyLifecycleV1:
    """One provider key and its half-open active epoch interval."""

    provider_id: str
    key_id: str
    public_key: str
    activation_epoch: int
    revocation_epoch: int | None

    def __post_init__(self) -> None:
        require_token(self.provider_id, name="provider_id")
        require_token(self.key_id, name="key_id")
        require_bls_public_key(self.public_key, name="provider public_key")
        require_u64(self.activation_epoch, name="provider activation_epoch")
        if self.revocation_epoch is not None:
            require_u64(self.revocation_epoch, name="provider revocation_epoch")
            if self.revocation_epoch <= self.activation_epoch:
                raise ValueError("provider revocation must follow activation")

    def is_active_at(self, epoch: int) -> bool:
        require_u64(epoch, name="provider evaluation epoch")
        return self.activation_epoch <= epoch and (
            self.revocation_epoch is None or epoch < self.revocation_epoch
        )

    def to_document(self) -> dict[str, object]:
        return {
            "activation_epoch": self.activation_epoch,
            "key_id": self.key_id,
            "provider_id": self.provider_id,
            "public_key": self.public_key,
            "revocation_epoch": self.revocation_epoch,
        }


@dataclass(frozen=True, slots=True)
class SampledRetrievabilityPolicyV1:
    """Explicit bounded sampling policy; governance provenance is external."""

    application_id: str
    chain_or_domain_id: str
    policy_revision: int
    activation_epoch: int
    revocation_epoch: int | None
    storage_policy_hash: str
    beacon_source_id: str
    beacon_policy_hash: str
    minimum_retention_epochs: int
    minimum_remaining_epochs: int
    challenge_count: int
    response_window_epochs: int
    minimum_provider_responses: int
    providers: tuple[ProviderKeyLifecycleV1, ...]

    @classmethod
    def validated(
        cls,
        *,
        application_id: str,
        chain_or_domain_id: str,
        policy_revision: int,
        activation_epoch: int,
        revocation_epoch: int | None,
        storage_policy_hash: str,
        beacon_source_id: str,
        beacon_policy_hash: str,
        minimum_retention_epochs: int,
        minimum_remaining_epochs: int,
        challenge_count: int,
        response_window_epochs: int,
        minimum_provider_responses: int,
        providers: tuple[ProviderKeyLifecycleV1, ...],
    ) -> SampledRetrievabilityPolicyV1:
        return cls(
            application_id=application_id,
            chain_or_domain_id=chain_or_domain_id,
            policy_revision=policy_revision,
            activation_epoch=activation_epoch,
            revocation_epoch=revocation_epoch,
            storage_policy_hash=storage_policy_hash,
            beacon_source_id=beacon_source_id,
            beacon_policy_hash=beacon_policy_hash,
            minimum_retention_epochs=minimum_retention_epochs,
            minimum_remaining_epochs=minimum_remaining_epochs,
            challenge_count=challenge_count,
            response_window_epochs=response_window_epochs,
            minimum_provider_responses=minimum_provider_responses,
            providers=providers,
        )

    def __post_init__(self) -> None:
        require_root(self.application_id, name="policy application_id")
        require_root(self.chain_or_domain_id, name="policy chain_or_domain_id")
        require_u64(self.policy_revision, name="policy_revision")
        require_u64(self.activation_epoch, name="policy activation_epoch")
        if self.revocation_epoch is not None:
            require_u64(self.revocation_epoch, name="policy revocation_epoch")
            if self.revocation_epoch <= self.activation_epoch:
                raise ValueError("policy revocation must follow activation")
        require_root(self.storage_policy_hash, name="policy storage_policy_hash")
        require_root(self.beacon_source_id, name="policy beacon_source_id")
        require_root(self.beacon_policy_hash, name="policy beacon_policy_hash")
        require_u64(self.minimum_retention_epochs, name="minimum_retention_epochs")
        require_u64(self.minimum_remaining_epochs, name="minimum_remaining_epochs")
        if type(self.challenge_count) is not int or not (
            1 <= self.challenge_count <= MAX_CHALLENGES_PER_PROVIDER_V1
        ):
            raise ValueError("challenge_count is outside the V1 bound")
        if type(self.response_window_epochs) is not int or not (
            0 <= self.response_window_epochs <= MAX_RESPONSE_WINDOW_EPOCHS_V1
        ):
            raise ValueError("response_window_epochs is outside the V1 bound")
        if type(self.providers) is not tuple or not self.providers:
            raise TypeError("providers must be a nonempty tuple")
        if len(self.providers) > MAX_PROVIDERS_V1:
            raise ValueError("provider count exceeds the V1 bound")
        if any(type(provider) is not ProviderKeyLifecycleV1 for provider in self.providers):
            raise TypeError("providers must contain exact ProviderKeyLifecycleV1 values")
        canonical = tuple(
            sorted(
                self.providers,
                key=lambda item: (item.provider_id, item.activation_epoch, item.key_id),
            )
        )
        if self.providers != canonical:
            raise ValueError("provider lifecycles must be canonically ordered")
        self._validate_provider_registry()

    def _validate_provider_registry(self) -> None:
        seen_keys: set[tuple[str, str]] = set()
        seen_public_keys: set[str] = set()
        by_provider: dict[str, list[ProviderKeyLifecycleV1]] = {}
        for provider in self.providers:
            identity = (provider.provider_id, provider.key_id)
            if identity in seen_keys:
                raise ValueError("duplicate provider identity/key")
            if provider.public_key in seen_public_keys:
                raise ValueError("duplicate provider public key")
            seen_keys.add(identity)
            seen_public_keys.add(provider.public_key)
            by_provider.setdefault(provider.provider_id, []).append(provider)
        for lifecycles in by_provider.values():
            for left, right in zip(lifecycles, lifecycles[1:], strict=False):
                if left.revocation_epoch is None or right.activation_epoch < left.revocation_epoch:
                    raise ValueError("overlapping provider key lifecycles")
        provider_count = len(by_provider)
        if type(self.minimum_provider_responses) is not int or not (
            1 <= self.minimum_provider_responses <= provider_count
        ):
            raise ValueError("minimum_provider_responses exceeds distinct providers")

    @property
    def policy_root(self) -> str:
        return hash_v0("zrpf_sampled_retrievability_policy_v1", self.to_document())

    def is_active_at(self, epoch: int) -> bool:
        require_u64(epoch, name="policy evaluation epoch")
        return self.activation_epoch <= epoch and (
            self.revocation_epoch is None or epoch < self.revocation_epoch
        )

    def find_provider(self, provider_id: str, key_id: str) -> ProviderKeyLifecycleV1 | None:
        for provider in self.providers:
            if provider.provider_id == provider_id and provider.key_id == key_id:
                return provider
        return None

    def active_provider_ids_at(self, epoch: int) -> tuple[str, ...]:
        return tuple(
            sorted(
                {
                    provider.provider_id
                    for provider in self.providers
                    if provider.is_active_at(epoch)
                }
            )
        )

    def to_document(self) -> dict[str, object]:
        return {
            "activation_epoch": self.activation_epoch,
            "application_id": self.application_id,
            "beacon_policy_hash": self.beacon_policy_hash,
            "beacon_source_id": self.beacon_source_id,
            "chain_or_domain_id": self.chain_or_domain_id,
            "challenge_count": self.challenge_count,
            "minimum_provider_responses": self.minimum_provider_responses,
            "minimum_remaining_epochs": self.minimum_remaining_epochs,
            "minimum_retention_epochs": self.minimum_retention_epochs,
            "policy_revision": self.policy_revision,
            "providers": [provider.to_document() for provider in self.providers],
            "response_window_epochs": self.response_window_epochs,
            "revocation_epoch": self.revocation_epoch,
            "storage_policy_hash": self.storage_policy_hash,
        }

    def constructor_fields(self) -> dict[str, object]:
        return {
            "application_id": self.application_id,
            "chain_or_domain_id": self.chain_or_domain_id,
            "policy_revision": self.policy_revision,
            "activation_epoch": self.activation_epoch,
            "revocation_epoch": self.revocation_epoch,
            "storage_policy_hash": self.storage_policy_hash,
            "beacon_source_id": self.beacon_source_id,
            "beacon_policy_hash": self.beacon_policy_hash,
            "minimum_retention_epochs": self.minimum_retention_epochs,
            "minimum_remaining_epochs": self.minimum_remaining_epochs,
            "challenge_count": self.challenge_count,
            "response_window_epochs": self.response_window_epochs,
            "minimum_provider_responses": self.minimum_provider_responses,
            "providers": self.providers,
        }


@dataclass(frozen=True, slots=True)
class BeaconCommitmentV1:
    source_id: str
    policy_hash: str
    beacon_epoch: int
    commitment: str

    @classmethod
    def validated(
        cls,
        *,
        source_id: str,
        policy_hash: str,
        beacon_epoch: int,
        commitment: str,
    ) -> BeaconCommitmentV1:
        return cls(source_id, policy_hash, beacon_epoch, commitment)

    def __post_init__(self) -> None:
        require_root(self.source_id, name="beacon source_id")
        require_root(self.policy_hash, name="beacon policy_hash")
        require_u64(self.beacon_epoch, name="beacon_epoch")
        require_root(self.commitment, name="beacon commitment")

    def to_document(self) -> dict[str, object]:
        return {
            "beacon_epoch": self.beacon_epoch,
            "commitment": self.commitment,
            "policy_hash": self.policy_hash,
            "source_id": self.source_id,
        }


@dataclass(frozen=True, slots=True)
class FullBlobRetrievabilityTargetV1:
    certificate_version: int
    application_id: str
    chain_or_domain_id: str
    epoch_id: int
    data_schema_id: str
    data_root: str
    blob_length: int
    chunk_size: int
    chunk_count: int
    chunk_root: str
    retention_through_epoch: int
    storage_policy_hash: str
    certificate_root: str

    def __post_init__(self) -> None:
        if type(self.certificate_version) is not int or self.certificate_version != 1:
            raise ValueError("only full-blob certificate version 1 is supported")
        for field in (
            "application_id",
            "chain_or_domain_id",
            "data_schema_id",
            "data_root",
            "chunk_root",
            "storage_policy_hash",
            "certificate_root",
        ):
            require_root(getattr(self, field), name=f"full-blob target {field}")
        for field in ("epoch_id", "blob_length", "retention_through_epoch"):
            require_u64(getattr(self, field), name=f"full-blob target {field}")
        if type(self.chunk_size) is not int or self.chunk_size != 65_536:
            raise ValueError("full-blob target chunk_size must be 65536")
        if type(self.chunk_count) is not int or not 1 <= self.chunk_count <= 128:
            raise ValueError("full-blob target chunk_count is outside 1..128")
        if not 1 <= self.blob_length <= 8 * 1_024 * 1_024:
            raise ValueError("full-blob target blob_length exceeds the V1 bound")
        expected_chunk_count = self.blob_length // self.chunk_size
        if self.blob_length % self.chunk_size != 0:
            expected_chunk_count += 1
        if self.chunk_count != expected_chunk_count:
            raise ValueError("full-blob target chunk_count does not match blob_length")
        if self.retention_through_epoch < self.epoch_id:
            raise ValueError("full-blob target retention ends before its epoch")

    def to_document(self) -> dict[str, object]:
        return {
            "application_id": self.application_id,
            "blob_length": self.blob_length,
            "certificate_root": self.certificate_root,
            "certificate_version": self.certificate_version,
            "chain_or_domain_id": self.chain_or_domain_id,
            "chunk_count": self.chunk_count,
            "chunk_root": self.chunk_root,
            "chunk_size": self.chunk_size,
            "data_root": self.data_root,
            "data_schema_id": self.data_schema_id,
            "epoch_id": self.epoch_id,
            "retention_through_epoch": self.retention_through_epoch,
            "storage_policy_hash": self.storage_policy_hash,
        }


@dataclass(frozen=True, slots=True)
class SignedProviderResponseV1:
    """Data-only provider proposal; cryptographic verification occurs later."""

    response_bytes: bytes
    signature_envelope: Mapping[str, object]

    def __post_init__(self) -> None:
        if type(self.response_bytes) is not bytes or not (
            1 <= len(self.response_bytes) <= MAX_EXACT_RESPONSE_BYTES_V1
        ):
            raise ValueError("provider response bytes are empty or oversized")
        if not isinstance(self.signature_envelope, Mapping):
            raise TypeError("signature_envelope must be a mapping")
