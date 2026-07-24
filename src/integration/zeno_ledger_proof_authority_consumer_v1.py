"""Typed consumer boundary for ZenoLedger proof-required authority.

The current V0 ledger profile and replay configuration do not commit a proof
authority policy.  This module makes that missing binding a typed pending
obligation.  Caller mappings and caller booleans cannot produce a satisfied
decision.

The future positive path needs three independent inputs:

* a data-only governed binding whose policy ID is committed by ledger state;
* a private authenticated result minted by the exact cryptographic verifier;
* a typed proof that the authenticated Spot state equals the ledger state domain.

The restricted positive path joins the authenticated legacy Spot roots to
replayed application state and derives the ZenoLedger state-root-v5 pair from
that same state.  The two root domains remain distinct.  A decision can become
``SATISFIED`` only when the private strict-verifier observation contains that
exact private bridge capability.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Any, Mapping, NoReturn, final

from src.integration.zeno_ledger_profile import (
    validate_zeno_ledger_profile_v0,
    zeno_ledger_profile_requires_proof_authority_v0,
)
from src.integration.zeno_ledger_spot_state_domain_bridge_v1 import (
    RESTRICTED_SPOT_STATE_DOMAIN_COMPATIBILITY_PROFILE_ID_V1,
    RESTRICTED_SPOT_STATE_ROOT_SCHEME_ID_V5,
    _AuthenticatedSpotLedgerStateDomainBridgeV1,
)
from src.integration.zeno_ledger_v0 import hash_v0
from src.state.canonical import canonical_hex_fixed_allow_0x

GOVERNED_PROOF_AUTHORITY_BINDING_SCHEMA_V1 = (
    "zenodex.zeno_ledger.governed_proof_authority_binding.v1"
)
SPOT_AUTHORITY_RESULT_SCHEMA_V1 = "zenodex.zeno_ledger.authenticated_spot_proof_facts.v1"
SPOT_PROOF_PROFILE_V1 = "risc0_spot_state_transition_v1"
PROOF_AUTHORITY_PENDING_SCHEMA_V1 = "zenodex.zeno_ledger.proof_authority_pending.v1"
PROOF_AUTHORITY_OBLIGATION_ID_V1 = "zeno_ledger.proof_authority.consumer_binding.v1"

_TOKEN_CHARS = frozenset("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789._:/-")
_MAX_U64 = (1 << 64) - 1
_GOVERNED_BINDING_KEYS_V1 = frozenset(
    {
        "schema",
        "policy_id",
        "chain_id",
        "authority_manifest_sha256",
        "verifier_registry_id",
        "verifier_registry_entry_id",
        "strict_result_schema",
        "proof_profile",
        "valid_from_height",
        "valid_until_height",
    }
)
_CURRENT_V0_MISSING_BINDINGS = (
    "authenticated_strict_verifier_result",
    "authenticated_spot_to_ledger_state_domain_bridge",
    "consensus_bound_authority_manifest_sha256",
    "consensus_bound_proof_authority_policy_id",
    "consensus_bound_verifier_registry_id",
    "replay_config_digest",
)


class ProofAuthorityConsumerRejectReasonV1(str, Enum):
    """Stable rejection classes for the proof-authority consumer port."""

    INVALID_REQUIREMENT = "proof_authority_consumer.invalid_requirement"
    GOVERNED_BINDING_INVALID = "proof_authority_consumer.governed_binding_invalid"
    POLICY_MISMATCH = "proof_authority_consumer.policy_mismatch"
    POLICY_NOT_YET_VALID = "proof_authority_consumer.policy_not_yet_valid"
    POLICY_STALE = "proof_authority_consumer.policy_stale"
    AUTHENTICATED_RESULT_TYPE_INVALID = "proof_authority_consumer.authenticated_result_type_invalid"


class ProofAuthorityDecisionStatusV1(str, Enum):
    """Range-level authority disposition derived by the final consumer."""

    NOT_REQUIRED = "not_required"
    REQUIRED_PENDING = "required_pending"
    SATISFIED = "satisfied"


class ProofAuthorityConsumerError(ValueError):
    """Typed fail-closed proof-authority consumer rejection."""

    def __init__(self, reason: ProofAuthorityConsumerRejectReasonV1, detail: str) -> None:
        self.reason = reason
        super().__init__(f"{reason.value}: {detail}")


@dataclass(frozen=True, slots=True)
class ProofAuthorityRequirementV1:
    """Validated range requirement derived from a ledger profile and config."""

    required: bool
    profile_id: str
    chain_id: str
    replay_config_digest: str | None
    expected_policy_id: str | None
    from_height: int
    to_height: int

    def __post_init__(self) -> None:
        if not isinstance(self.required, bool):
            raise TypeError("required must be a bool")
        _require_root(self.profile_id, name="profile_id")
        _require_token(self.chain_id, name="chain_id")
        if self.replay_config_digest is not None:
            _require_root(self.replay_config_digest, name="replay_config_digest")
        if self.expected_policy_id is not None:
            _require_root(self.expected_policy_id, name="expected_policy_id")
        _require_height(self.from_height, name="from_height")
        _require_height(self.to_height, name="to_height")
        if self.to_height < self.from_height:
            raise ValueError("to_height precedes from_height")


@dataclass(frozen=True, slots=True)
class GovernedProofAuthorityBindingV1:
    """Data-only policy identity expected to be committed by governed state.

    This value carries no proof authority by itself.  The consumer must compare
    ``policy_id`` with the ID committed by the replay configuration/header.
    """

    schema: str
    policy_id: str
    chain_id: str
    authority_manifest_sha256: str
    verifier_registry_id: str
    verifier_registry_entry_id: str
    strict_result_schema: str
    proof_profile: str
    valid_from_height: int
    valid_until_height: int

    def __post_init__(self) -> None:
        if self.schema != GOVERNED_PROOF_AUTHORITY_BINDING_SCHEMA_V1:
            raise ValueError("governed proof-authority binding schema mismatch")
        _require_root(self.policy_id, name="policy_id")
        _require_token(self.chain_id, name="chain_id")
        _require_bare_sha256(
            self.authority_manifest_sha256,
            name="authority_manifest_sha256",
        )
        _require_root(self.verifier_registry_id, name="verifier_registry_id")
        _require_root(
            self.verifier_registry_entry_id,
            name="verifier_registry_entry_id",
        )
        if self.strict_result_schema != SPOT_AUTHORITY_RESULT_SCHEMA_V1:
            raise ValueError("governed proof-authority strict result schema mismatch")
        if self.proof_profile != SPOT_PROOF_PROFILE_V1:
            raise ValueError("governed proof-authority proof profile mismatch")
        _require_height(self.valid_from_height, name="valid_from_height")
        _require_height(self.valid_until_height, name="valid_until_height")
        if self.valid_until_height < self.valid_from_height:
            raise ValueError("valid_until_height precedes valid_from_height")
        if self.policy_id != governed_proof_authority_binding_id_v1(self):
            raise ValueError("governed proof-authority policy_id mismatch")


@dataclass(frozen=True, slots=True)
class ProofAuthorityPendingObligationV1:
    """Data-only explanation for a fail-closed proof-required range."""

    schema: str
    obligation_id: str
    profile_id: str
    chain_id: str
    replay_config_digest: str | None
    from_height: int
    to_height: int
    missing_bindings: tuple[str, ...]

    def __post_init__(self) -> None:
        if self.schema != PROOF_AUTHORITY_PENDING_SCHEMA_V1:
            raise ValueError("proof-authority pending schema mismatch")
        if self.obligation_id != PROOF_AUTHORITY_OBLIGATION_ID_V1:
            raise ValueError("proof-authority pending obligation ID mismatch")
        _require_root(self.profile_id, name="profile_id")
        _require_token(self.chain_id, name="chain_id")
        if self.replay_config_digest is not None:
            _require_root(self.replay_config_digest, name="replay_config_digest")
        _require_height(self.from_height, name="from_height")
        _require_height(self.to_height, name="to_height")
        if self.to_height < self.from_height:
            raise ValueError("to_height precedes from_height")
        if self.missing_bindings != tuple(sorted(set(self.missing_bindings))):
            raise ValueError("missing_bindings must be sorted and unique")
        if not self.missing_bindings:
            raise ValueError("pending obligation must name a missing binding")
        for index, binding in enumerate(self.missing_bindings):
            _require_token(binding, name=f"missing_bindings[{index}]")

    def to_report(self) -> dict[str, object]:
        """Return a canonical JSON-compatible diagnostic projection."""

        return {
            "schema": self.schema,
            "obligation_id": self.obligation_id,
            "profile_id": self.profile_id,
            "chain_id": self.chain_id,
            "replay_config_digest": self.replay_config_digest,
            "from_height": self.from_height,
            "to_height": self.to_height,
            "missing_bindings": list(self.missing_bindings),
        }


_DECISION_SEAL = object()


@final
class ProofAuthorityDecisionV1:
    """Immutable range decision whose satisfied state has no public factory."""

    __slots__ = ("_pending", "_seal", "_status")

    def __init__(
        self,
        status: ProofAuthorityDecisionStatusV1,
        pending: ProofAuthorityPendingObligationV1 | None,
        *,
        seal: object,
    ) -> None:
        if seal is not _DECISION_SEAL:
            raise TypeError("proof-authority decision requires the private seal")
        if not isinstance(status, ProofAuthorityDecisionStatusV1):
            raise TypeError("status must be ProofAuthorityDecisionStatusV1")
        if status is ProofAuthorityDecisionStatusV1.REQUIRED_PENDING:
            if type(pending) is not ProofAuthorityPendingObligationV1:
                raise TypeError("pending decision requires an exact pending obligation")
        elif pending is not None:
            raise TypeError("non-pending decision cannot carry a pending obligation")
        object.__setattr__(self, "_status", status)
        object.__setattr__(self, "_pending", pending)
        object.__setattr__(self, "_seal", seal)

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("ProofAuthorityDecisionV1 cannot be subclassed")

    def __setattr__(self, _name: str, _value: object) -> None:
        raise AttributeError("ProofAuthorityDecisionV1 is immutable")

    @property
    def status(self) -> ProofAuthorityDecisionStatusV1:
        return object.__getattribute__(self, "_status")

    @property
    def required(self) -> bool:
        return self.status is not ProofAuthorityDecisionStatusV1.NOT_REQUIRED

    @property
    def satisfied(self) -> bool:
        return self.status is ProofAuthorityDecisionStatusV1.SATISFIED

    @property
    def capable(self) -> bool:
        # V1 keeps capability false until the governed strict-verifier join is
        # implemented and exercised by the final consumer.
        return self.satisfied

    def pending_report(self) -> dict[str, object] | None:
        pending = object.__getattribute__(self, "_pending")
        return pending.to_report() if pending is not None else None


_AUTHENTICATED_STRICT_SPOT_OBSERVATION_SEAL = object()


@final
class _AuthenticatedStrictSpotObservationV1:
    """Private receipt observation with an optional exact state-domain join."""

    __slots__ = (
        "_authority_manifest_sha256",
        "_chain_id",
        "_from_height",
        "_policy_id",
        "_replay_config_digest",
        "_seal",
        "_spot_ledger_state_domain_bridge_verified",
        "_state_domain_bridge",
        "_strict_result_schema",
        "_to_height",
        "_verifier_registry_entry_id",
        "_verifier_registry_id",
    )

    def __init__(
        self,
        *,
        policy_id: str,
        chain_id: str,
        from_height: int,
        to_height: int,
        replay_config_digest: str,
        authority_manifest_sha256: str,
        verifier_registry_id: str,
        verifier_registry_entry_id: str,
        strict_result_schema: str,
        state_domain_bridge: _AuthenticatedSpotLedgerStateDomainBridgeV1 | None,
        seal: object,
    ) -> None:
        if seal is not _AUTHENTICATED_STRICT_SPOT_OBSERVATION_SEAL:
            raise TypeError("authenticated strict Spot observation requires the private seal")
        object.__setattr__(self, "_policy_id", _require_root(policy_id, name="policy_id"))
        object.__setattr__(self, "_chain_id", _require_token(chain_id, name="chain_id"))
        object.__setattr__(self, "_from_height", _require_height(from_height, name="from_height"))
        object.__setattr__(self, "_to_height", _require_height(to_height, name="to_height"))
        object.__setattr__(
            self,
            "_replay_config_digest",
            _require_root(replay_config_digest, name="replay_config_digest"),
        )
        object.__setattr__(
            self,
            "_authority_manifest_sha256",
            _require_bare_sha256(
                authority_manifest_sha256,
                name="authority_manifest_sha256",
            ),
        )
        object.__setattr__(
            self,
            "_verifier_registry_id",
            _require_root(verifier_registry_id, name="verifier_registry_id"),
        )
        object.__setattr__(
            self,
            "_verifier_registry_entry_id",
            _require_root(
                verifier_registry_entry_id,
                name="verifier_registry_entry_id",
            ),
        )
        if strict_result_schema != SPOT_AUTHORITY_RESULT_SCHEMA_V1:
            raise ValueError("authenticated strict result schema mismatch")
        object.__setattr__(self, "_strict_result_schema", strict_result_schema)
        if state_domain_bridge is not None and type(
            state_domain_bridge
        ) is not _AuthenticatedSpotLedgerStateDomainBridgeV1:
            raise TypeError("state_domain_bridge must be the exact private bridge type")
        object.__setattr__(self, "_state_domain_bridge", state_domain_bridge)
        object.__setattr__(
            self,
            "_spot_ledger_state_domain_bridge_verified",
            state_domain_bridge is not None,
        )
        object.__setattr__(self, "_seal", seal)

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("authenticated strict Spot observation cannot be subclassed")

    def _has_private_seal(self) -> bool:
        """Reject nominal instances that did not pass the private mint site."""

        return getattr(self, "_seal", None) is _AUTHENTICATED_STRICT_SPOT_OBSERVATION_SEAL

    def __setattr__(self, _name: str, _value: object) -> None:
        raise AttributeError("authenticated strict Spot observation is immutable")

    def __copy__(self) -> NoReturn:
        raise TypeError("authenticated strict Spot observation cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("authenticated strict Spot observation cannot be copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("authenticated strict Spot observation cannot be serialized")


def _mint_authenticated_strict_spot_observation_v1(
    *,
    policy_id: str,
    chain_id: str,
    height: int,
    replay_config_digest: str,
    authority_manifest_sha256: str,
    verifier_registry_id: str,
    verifier_registry_entry_id: str,
    strict_result_schema: str,
    state_domain_bridge: _AuthenticatedSpotLedgerStateDomainBridgeV1 | None = None,
) -> _AuthenticatedStrictSpotObservationV1:
    """Mint only after exact strict verification and optional bridge derivation."""

    return _AuthenticatedStrictSpotObservationV1(
        policy_id=policy_id,
        chain_id=chain_id,
        from_height=height,
        to_height=height,
        replay_config_digest=replay_config_digest,
        authority_manifest_sha256=authority_manifest_sha256,
        verifier_registry_id=verifier_registry_id,
        verifier_registry_entry_id=verifier_registry_entry_id,
        strict_result_schema=strict_result_schema,
        state_domain_bridge=state_domain_bridge,
        seal=_AUTHENTICATED_STRICT_SPOT_OBSERVATION_SEAL,
    )


def make_proof_authority_requirement_v1(
    *,
    profile: Mapping[str, Any],
    replay_config_digest: str | None,
    expected_policy_id: str | None,
    from_height: int,
    to_height: int,
) -> ProofAuthorityRequirementV1:
    """Derive the only admissible proof requirement from a validated profile."""

    try:
        profile_obj = dict(profile)
        validate_zeno_ledger_profile_v0(profile_obj)
        required = zeno_ledger_profile_requires_proof_authority_v0(profile_obj)
        return ProofAuthorityRequirementV1(
            required=required,
            profile_id=str(profile_obj["profile_id"]),
            chain_id=str(profile_obj["chain_id"]),
            replay_config_digest=replay_config_digest,
            expected_policy_id=expected_policy_id,
            from_height=from_height,
            to_height=to_height,
        )
    except (KeyError, TypeError, ValueError) as exc:
        raise ProofAuthorityConsumerError(
            ProofAuthorityConsumerRejectReasonV1.INVALID_REQUIREMENT,
            "proof-authority requirement is not a valid governed range",
        ) from exc


def proof_authority_not_required_v1() -> ProofAuthorityDecisionV1:
    """Return the only public decision for a range without a proof profile."""

    return _decision(ProofAuthorityDecisionStatusV1.NOT_REQUIRED)


def resolve_proof_authority_v1(
    *,
    requirement: ProofAuthorityRequirementV1,
    governed_binding: GovernedProofAuthorityBindingV1 | None,
    authenticated_result: object | None,
) -> ProofAuthorityDecisionV1:
    """Resolve a range decision without accepting caller-declared success.

    Supplying a mapping, Boolean, or duck-typed result fails closed.  The only
    satisfied path requires the consumer-private observation and its exact
    private restricted state-domain bridge.
    """

    if type(requirement) is not ProofAuthorityRequirementV1:
        raise ProofAuthorityConsumerError(
            ProofAuthorityConsumerRejectReasonV1.INVALID_REQUIREMENT,
            "requirement must be exactly ProofAuthorityRequirementV1",
        )
    if not requirement.required:
        if governed_binding is not None or authenticated_result is not None:
            raise ProofAuthorityConsumerError(
                ProofAuthorityConsumerRejectReasonV1.INVALID_REQUIREMENT,
                "non-proof profile rejects proof-authority inputs",
            )
        return _decision(ProofAuthorityDecisionStatusV1.NOT_REQUIRED)

    missing = set(_CURRENT_V0_MISSING_BINDINGS)
    if requirement.replay_config_digest is not None:
        missing.discard("replay_config_digest")
    if requirement.expected_policy_id is not None:
        missing.discard("consensus_bound_proof_authority_policy_id")
    if governed_binding is None:
        if authenticated_result is not None:
            raise ProofAuthorityConsumerError(
                ProofAuthorityConsumerRejectReasonV1.AUTHENTICATED_RESULT_TYPE_INVALID,
                "authenticated result cannot precede the governed policy binding",
            )
        return _pending_decision(requirement, tuple(sorted(missing)))
    if type(governed_binding) is not GovernedProofAuthorityBindingV1:
        raise ProofAuthorityConsumerError(
            ProofAuthorityConsumerRejectReasonV1.GOVERNED_BINDING_INVALID,
            "governed binding must be exactly GovernedProofAuthorityBindingV1",
        )
    _validate_governed_binding(requirement=requirement, binding=governed_binding)
    missing.discard("consensus_bound_authority_manifest_sha256")
    missing.discard("consensus_bound_verifier_registry_id")

    if authenticated_result is None:
        return _pending_decision(requirement, tuple(sorted(missing)))
    if type(authenticated_result) is not _AuthenticatedStrictSpotObservationV1:
        raise ProofAuthorityConsumerError(
            ProofAuthorityConsumerRejectReasonV1.AUTHENTICATED_RESULT_TYPE_INVALID,
            "caller data cannot stand in for a private strict Spot observation",
        )
    if not authenticated_result._has_private_seal():
        raise ProofAuthorityConsumerError(
            ProofAuthorityConsumerRejectReasonV1.AUTHENTICATED_RESULT_TYPE_INVALID,
            "strict Spot observation lacks the private mint seal",
        )
    authenticated_expectations = {
        "_policy_id": governed_binding.policy_id,
        "_chain_id": requirement.chain_id,
        "_from_height": requirement.from_height,
        "_to_height": requirement.to_height,
        "_replay_config_digest": requirement.replay_config_digest,
        "_authority_manifest_sha256": governed_binding.authority_manifest_sha256,
        "_verifier_registry_id": governed_binding.verifier_registry_id,
        "_verifier_registry_entry_id": governed_binding.verifier_registry_entry_id,
        "_strict_result_schema": governed_binding.strict_result_schema,
    }
    if any(
        object.__getattribute__(authenticated_result, field) != expected
        for field, expected in authenticated_expectations.items()
    ):
        raise ProofAuthorityConsumerError(
            ProofAuthorityConsumerRejectReasonV1.POLICY_MISMATCH,
            "strict Spot observation does not bind the governed range and policy",
        )
    missing.discard("authenticated_strict_verifier_result")
    state_domain_bridge = object.__getattribute__(
        authenticated_result,
        "_state_domain_bridge",
    )
    if state_domain_bridge is None:
        return _pending_decision(requirement, tuple(sorted(missing)))
    if (
        type(state_domain_bridge) is not _AuthenticatedSpotLedgerStateDomainBridgeV1
        or not state_domain_bridge._has_private_seal()
        or object.__getattribute__(
            authenticated_result,
            "_spot_ledger_state_domain_bridge_verified",
        )
        is not True
        or object.__getattribute__(
            state_domain_bridge,
            "_source_and_ledger_roots_verified",
        )
        is not True
        or object.__getattribute__(
            state_domain_bridge,
            "_compatibility_profile_id",
        )
        != RESTRICTED_SPOT_STATE_DOMAIN_COMPATIBILITY_PROFILE_ID_V1
        or object.__getattribute__(state_domain_bridge, "_state_root_scheme_id")
        != RESTRICTED_SPOT_STATE_ROOT_SCHEME_ID_V5
    ):
        raise ProofAuthorityConsumerError(
            ProofAuthorityConsumerRejectReasonV1.AUTHENTICATED_RESULT_TYPE_INVALID,
            "strict Spot observation does not carry the governed bridge capability",
        )
    missing.discard("authenticated_spot_to_ledger_state_domain_bridge")
    if missing:
        return _pending_decision(requirement, tuple(sorted(missing)))
    return _decision(ProofAuthorityDecisionStatusV1.SATISFIED)


def make_governed_proof_authority_binding_v1(
    *,
    chain_id: str,
    authority_manifest_sha256: str,
    verifier_registry_id: str,
    verifier_registry_entry_id: str,
    valid_from_height: int,
    valid_until_height: int,
) -> GovernedProofAuthorityBindingV1:
    """Build canonical data for a future consensus-bound authority policy."""

    values = {
        "schema": GOVERNED_PROOF_AUTHORITY_BINDING_SCHEMA_V1,
        "chain_id": chain_id,
        "authority_manifest_sha256": authority_manifest_sha256,
        "verifier_registry_id": verifier_registry_id,
        "verifier_registry_entry_id": verifier_registry_entry_id,
        "strict_result_schema": SPOT_AUTHORITY_RESULT_SCHEMA_V1,
        "proof_profile": SPOT_PROOF_PROFILE_V1,
        "valid_from_height": valid_from_height,
        "valid_until_height": valid_until_height,
    }
    policy_id = hash_v0("governed_proof_authority_binding_v1", values)
    return GovernedProofAuthorityBindingV1(
        schema=GOVERNED_PROOF_AUTHORITY_BINDING_SCHEMA_V1,
        policy_id=policy_id,
        chain_id=chain_id,
        authority_manifest_sha256=authority_manifest_sha256,
        verifier_registry_id=verifier_registry_id,
        verifier_registry_entry_id=verifier_registry_entry_id,
        strict_result_schema=SPOT_AUTHORITY_RESULT_SCHEMA_V1,
        proof_profile=SPOT_PROOF_PROFILE_V1,
        valid_from_height=valid_from_height,
        valid_until_height=valid_until_height,
    )


def governed_proof_authority_binding_document_v1(
    binding: GovernedProofAuthorityBindingV1,
) -> dict[str, object]:
    """Return the exact canonical data object committed by config V1."""

    if type(binding) is not GovernedProofAuthorityBindingV1:
        raise TypeError("binding must be exactly GovernedProofAuthorityBindingV1")
    return {
        "schema": binding.schema,
        "policy_id": binding.policy_id,
        "chain_id": binding.chain_id,
        "authority_manifest_sha256": binding.authority_manifest_sha256,
        "verifier_registry_id": binding.verifier_registry_id,
        "verifier_registry_entry_id": binding.verifier_registry_entry_id,
        "strict_result_schema": binding.strict_result_schema,
        "proof_profile": binding.proof_profile,
        "valid_from_height": binding.valid_from_height,
        "valid_until_height": binding.valid_until_height,
    }


def parse_governed_proof_authority_binding_v1(
    value: Mapping[str, Any],
) -> GovernedProofAuthorityBindingV1:
    """Parse an exact policy object and independently recompute its ID."""

    obj = dict(value)
    if set(obj) != _GOVERNED_BINDING_KEYS_V1:
        raise ValueError("governed proof-authority binding keys mismatch")
    return GovernedProofAuthorityBindingV1(
        schema=obj["schema"],
        policy_id=obj["policy_id"],
        chain_id=obj["chain_id"],
        authority_manifest_sha256=obj["authority_manifest_sha256"],
        verifier_registry_id=obj["verifier_registry_id"],
        verifier_registry_entry_id=obj["verifier_registry_entry_id"],
        strict_result_schema=obj["strict_result_schema"],
        proof_profile=obj["proof_profile"],
        valid_from_height=obj["valid_from_height"],
        valid_until_height=obj["valid_until_height"],
    )


def governed_proof_authority_binding_id_v1(
    binding: GovernedProofAuthorityBindingV1,
) -> str:
    """Recompute the policy ID without trusting the carried identifier."""

    return hash_v0(
        "governed_proof_authority_binding_v1",
        {
            "schema": binding.schema,
            "chain_id": binding.chain_id,
            "authority_manifest_sha256": binding.authority_manifest_sha256,
            "verifier_registry_id": binding.verifier_registry_id,
            "verifier_registry_entry_id": binding.verifier_registry_entry_id,
            "strict_result_schema": binding.strict_result_schema,
            "proof_profile": binding.proof_profile,
            "valid_from_height": binding.valid_from_height,
            "valid_until_height": binding.valid_until_height,
        },
    )


def _validate_governed_binding(
    *,
    requirement: ProofAuthorityRequirementV1,
    binding: GovernedProofAuthorityBindingV1,
) -> None:
    if requirement.expected_policy_id is None:
        raise ProofAuthorityConsumerError(
            ProofAuthorityConsumerRejectReasonV1.POLICY_MISMATCH,
            "replay configuration does not commit a proof-authority policy ID",
        )
    if (
        binding.policy_id != requirement.expected_policy_id
        or binding.chain_id != requirement.chain_id
    ):
        raise ProofAuthorityConsumerError(
            ProofAuthorityConsumerRejectReasonV1.POLICY_MISMATCH,
            "governed binding does not match the committed range policy",
        )
    if requirement.from_height < binding.valid_from_height:
        raise ProofAuthorityConsumerError(
            ProofAuthorityConsumerRejectReasonV1.POLICY_NOT_YET_VALID,
            "governed proof-authority policy is not yet valid",
        )
    if requirement.to_height > binding.valid_until_height:
        raise ProofAuthorityConsumerError(
            ProofAuthorityConsumerRejectReasonV1.POLICY_STALE,
            "governed proof-authority policy is stale for the requested range",
        )


def _decision(status: ProofAuthorityDecisionStatusV1) -> ProofAuthorityDecisionV1:
    return ProofAuthorityDecisionV1(status, None, seal=_DECISION_SEAL)


def _pending_decision(
    requirement: ProofAuthorityRequirementV1,
    missing_bindings: tuple[str, ...],
) -> ProofAuthorityDecisionV1:
    pending = ProofAuthorityPendingObligationV1(
        schema=PROOF_AUTHORITY_PENDING_SCHEMA_V1,
        obligation_id=PROOF_AUTHORITY_OBLIGATION_ID_V1,
        profile_id=requirement.profile_id,
        chain_id=requirement.chain_id,
        replay_config_digest=requirement.replay_config_digest,
        from_height=requirement.from_height,
        to_height=requirement.to_height,
        missing_bindings=missing_bindings,
    )
    return ProofAuthorityDecisionV1(
        ProofAuthorityDecisionStatusV1.REQUIRED_PENDING,
        pending,
        seal=_DECISION_SEAL,
    )


def _require_root(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    canonical = canonical_hex_fixed_allow_0x(value, nbytes=32, name=name)
    if value != canonical:
        raise ValueError(f"{name} must be canonical lowercase 0x-prefixed hex")
    return canonical


def _require_bare_sha256(value: object, *, name: str) -> str:
    if (
        not isinstance(value, str)
        or len(value) != 64
        or any(char not in "0123456789abcdef" for char in value)
    ):
        raise ValueError(f"{name} must be lowercase 64-character SHA-256 hex")
    return value


def _require_token(value: object, *, name: str) -> str:
    if not isinstance(value, str) or not value or len(value.encode("utf-8")) > 256:
        raise ValueError(f"{name} must be a non-empty bounded str")
    if any(char not in _TOKEN_CHARS for char in value):
        raise ValueError(f"{name} contains unsupported characters")
    return value


def _require_height(value: object, *, name: str) -> int:
    if (
        not isinstance(value, int)
        or isinstance(value, bool)
        or value < 0
        or value > _MAX_U64
    ):
        raise ValueError(f"{name} must be a u64")
    return value
