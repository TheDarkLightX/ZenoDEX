"""Domain-separated hashes and unsigned epoch encoding for ZRPF admission."""

from __future__ import annotations

import hashlib
from dataclasses import dataclass

from src.core.recursive_stark_admission import (
    RecursiveStarkRootFacts,
    _AuthenticatedRecursiveStarkRootFacts,
)
from src.integration.recursive_stark_admission_store_types import (
    DurableRecursiveStarkAdmissionCursor,
    _hash_bytes,
)

_FACTS_DOMAIN = b"zenodex.zrpf.durable_admission.facts.v1"
_OUTCOME_DOMAIN = b"zenodex.zrpf.durable_admission.outcome.v1"
_STATE_DOMAIN = b"zenodex.zrpf.durable_admission.state.v1"


@dataclass(frozen=True, slots=True)
class _StateRootInput:
    previous: DurableRecursiveStarkAdmissionCursor
    revision: int
    facts: RecursiveStarkRootFacts
    outcome_key: bytes
    facts_digest: bytes
    counts: tuple[int, int, int, int, int]


def _facts_digest(facts: RecursiveStarkRootFacts) -> bytes:
    return _domain_hash(
        _FACTS_DOMAIN,
        (
            facts.chain_id.encode("ascii"),
            _epoch_blob(facts.epoch_id),
            facts.proof_profile.encode("ascii"),
            _hash_bytes(facts.root_journal_hash, name="facts.root_journal_hash"),
            _hash_bytes(facts.verifier_set_root, name="facts.verifier_set_root"),
            _hash_bytes(facts.public_policy_hash, name="facts.public_policy_hash"),
            _hash_bytes(facts.child_verification_claims_root, name="facts child root"),
            _hash_bytes(facts.accepted_receipts_root, name="facts receipt root"),
            _hash_bytes(facts.cross_shard_message_ids_root, name="facts message root"),
        ),
    )


def _outcome_key(
    authenticated_root: _AuthenticatedRecursiveStarkRootFacts,
    facts_digest: bytes,
) -> bytes:
    provenance = authenticated_root.provenance
    if (
        provenance.release_binding_config_digest is None
        or provenance.replay_manifest_sha256 is None
    ):
        raise TypeError("durable admission outcome requires release provenance")
    return _domain_hash(
        _OUTCOME_DOMAIN,
        (
            facts_digest,
            bytes.fromhex(provenance.authority_manifest_sha256),
            bytes.fromhex(provenance.verifier_executable_sha256),
            bytes.fromhex(provenance.verification_request_sha256),
            bytes.fromhex(provenance.release_binding_config_digest.removeprefix("0x")),
            bytes.fromhex(provenance.replay_manifest_sha256.removeprefix("sha256:")),
        ),
    )


def _state_root(value: _StateRootInput) -> bytes:
    return _domain_hash(
        _STATE_DOMAIN,
        (
            _hash_bytes(value.previous.state_root, name="previous state root"),
            value.revision.to_bytes(8, "big"),
            value.facts.chain_id.encode("ascii"),
            _epoch_blob(value.facts.epoch_id),
            value.facts.proof_profile.encode("ascii"),
            value.facts_digest,
            value.outcome_key,
            b"".join(count.to_bytes(8, "big") for count in value.counts),
        ),
    )


def _domain_hash(domain: bytes, values: tuple[bytes, ...]) -> bytes:
    digest = hashlib.sha256()
    digest.update(domain)
    for value in values:
        digest.update(len(value).to_bytes(8, "big"))
        digest.update(value)
    return digest.digest()


def _epoch_blob(value: int) -> bytes:
    if type(value) is not int or value < 0 or value > (1 << 64) - 1:
        raise ValueError("epoch_id must be an unsigned 64-bit integer")
    return value.to_bytes(8, "big")
