"""Deterministic consensus clock policy and non-circular block contexts.

The core has no wall-clock input. ``HEIGHT_ONLY_V1`` derives protocol epochs
solely from a committed height policy. The executor verifies an execution
header core before proof material or current-block finality exists; external
consumers use a separate finalized context after a certificate is available.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Final, Mapping, Protocol

from src.state.canonical import (
    canonical_hex_fixed_allow_0x,
    canonical_json_bytes,
    domain_sep_bytes,
    encode_bytes,
    sha256_hex,
)

U64_MAX: Final[int] = (1 << 64) - 1
ROOT_NBYTES: Final[int] = 32
ZERO_ROOT_V1: Final[str] = "0x" + "00" * ROOT_NBYTES
CLOCK_POLICY_ID_HEIGHT_ONLY_V1: Final[str] = "HEIGHT_ONLY_V1"
CLOCK_POLICY_VERSION_V1: Final[int] = 1
EXECUTION_HEADER_CORE_VERSION_V1: Final[int] = 1
PROOF_JOURNAL_BINDING_VERSION_V1: Final[int] = 1


class ClockAuthorityProfileV1(str, Enum):
    """Exactly one consensus domain supplies the immediate execution clock."""

    TAU_NATIVE_V1 = "TAU_NATIVE_V1"
    ZENO_LEDGER_SOVEREIGN_V1 = "ZENO_LEDGER_SOVEREIGN_V1"
    ZENO_LEDGER_TAU_CHECKPOINTED_V1 = "ZENO_LEDGER_TAU_CHECKPOINTED_V1"

    @property
    def immediate_clock_authority(self) -> str:
        if self is ClockAuthorityProfileV1.TAU_NATIVE_V1:
            return "tau_consensus"
        return "zeno_ledger_consensus"


def _require_u64(value: object, *, name: str) -> int:
    if type(value) is not int:
        raise TypeError(f"{name} must be an int")
    if value < 0 or value > U64_MAX:
        raise ValueError(f"{name} must be in u64 range")
    return value


def _require_nonempty_str(value: object, *, name: str) -> str:
    if type(value) is not str:
        raise TypeError(f"{name} must be a str")
    if not value:
        raise ValueError(f"{name} must be non-empty")
    if "\x00" in value:
        raise ValueError(f"{name} must not contain NUL")
    return value


def _require_root(value: object, *, name: str, allow_zero: bool = True) -> str:
    if type(value) is not str:
        raise TypeError(f"{name} must be a str")
    canonical = canonical_hex_fixed_allow_0x(value, nbytes=ROOT_NBYTES, name=name)
    if type(canonical) is not str:
        raise TypeError(f"{name} canonicalizer must return a str")
    if value != canonical:
        raise ValueError(f"{name} must be canonical lowercase 0x-prefixed hex")
    if not allow_zero and canonical == "0x" + "00" * ROOT_NBYTES:
        raise ValueError(f"{name} must be non-zero")
    return canonical


def _hash_canonical(*, domain: str, value: object) -> str:
    payload = domain_sep_bytes(domain, version=1) + encode_bytes(canonical_json_bytes(value))
    digest = sha256_hex(payload)
    if type(digest) is not str:
        raise TypeError("sha256_hex must return a str")
    return digest


@dataclass(frozen=True, slots=True)
class ClockPolicyV1:
    """Committed height-to-epoch policy, with u64 fields and no hidden time."""

    clock_policy_id: str
    clock_policy_version: int
    chain_id: str
    deployment_profile: ClockAuthorityProfileV1
    consensus_domain_id: str
    activation_height: int
    epoch_base: int
    blocks_per_epoch: int

    def __post_init__(self) -> None:
        _require_nonempty_str(self.clock_policy_id, name="clock_policy_id")
        if self.clock_policy_id != CLOCK_POLICY_ID_HEIGHT_ONLY_V1:
            raise ValueError("clock_policy_id must be HEIGHT_ONLY_V1")
        _require_u64(self.clock_policy_version, name="clock_policy_version")
        if self.clock_policy_version != CLOCK_POLICY_VERSION_V1:
            raise ValueError("clock_policy_version must equal 1")
        _require_nonempty_str(self.chain_id, name="chain_id")
        if type(self.deployment_profile) is not ClockAuthorityProfileV1:
            raise TypeError("deployment_profile must be ClockAuthorityProfileV1")
        _require_nonempty_str(self.consensus_domain_id, name="consensus_domain_id")
        _require_u64(self.activation_height, name="activation_height")
        _require_u64(self.epoch_base, name="epoch_base")
        _require_u64(self.blocks_per_epoch, name="blocks_per_epoch")
        if self.blocks_per_epoch == 0:
            raise ValueError("blocks_per_epoch must be positive")

    def epoch_at_height(self, height: int) -> int:
        """Return the exact epoch at ``height`` or reject outside this policy."""

        height_v = _require_u64(height, name="height")
        if height_v < self.activation_height:
            raise ValueError("height is before clock policy activation")
        epoch_offset = (height_v - self.activation_height) // self.blocks_per_epoch
        derived_epoch = self.epoch_base + epoch_offset
        if derived_epoch > U64_MAX:
            raise ValueError("derived epoch overflows u64")
        return derived_epoch

    def require_continuous_upgrade(self, successor: "ClockPolicyV1") -> None:
        """Reject a successor that reinterprets the activation-boundary epoch."""

        if type(successor) is not ClockPolicyV1:
            raise TypeError("successor must be ClockPolicyV1")
        if successor.chain_id != self.chain_id:
            raise ValueError("clock policy chain_id mismatch")
        if successor.consensus_domain_id != self.consensus_domain_id:
            raise ValueError("clock policy consensus domain mismatch")
        if successor.deployment_profile is not self.deployment_profile:
            raise ValueError("clock policy deployment profile mismatch")
        if successor.activation_height <= self.activation_height:
            raise ValueError("successor activation_height must increase")
        expected_epoch_base = self.epoch_at_height(successor.activation_height)
        if successor.epoch_base != expected_epoch_base:
            raise ValueError("clock policy epoch discontinuity")

    def to_obj(self) -> dict[str, object]:
        return {
            "schema": "zenodex/clock_policy/height_only/v1",
            "clock_policy_id": self.clock_policy_id,
            "clock_policy_version": self.clock_policy_version,
            "chain_id": self.chain_id,
            "deployment_profile": self.deployment_profile.value,
            "consensus_domain_id": self.consensus_domain_id,
            "activation_height": self.activation_height,
            "epoch_base": self.epoch_base,
            "blocks_per_epoch": self.blocks_per_epoch,
        }

    @classmethod
    def from_obj(cls, value: object) -> "ClockPolicyV1":
        if not isinstance(value, Mapping):
            raise TypeError("clock policy must be an object")
        expected = {
            "schema",
            "clock_policy_id",
            "clock_policy_version",
            "chain_id",
            "deployment_profile",
            "consensus_domain_id",
            "activation_height",
            "epoch_base",
            "blocks_per_epoch",
        }
        if set(value) != expected:
            raise ValueError("clock policy fields mismatch")
        if value["schema"] != "zenodex/clock_policy/height_only/v1":
            raise ValueError("clock policy schema unsupported")
        try:
            profile = ClockAuthorityProfileV1(value["deployment_profile"])
        except (TypeError, ValueError) as exc:
            raise ValueError("clock policy deployment_profile unsupported") from exc
        return cls(
            clock_policy_id=value["clock_policy_id"],
            clock_policy_version=value["clock_policy_version"],
            chain_id=value["chain_id"],
            deployment_profile=profile,
            consensus_domain_id=value["consensus_domain_id"],
            activation_height=value["activation_height"],
            epoch_base=value["epoch_base"],
            blocks_per_epoch=value["blocks_per_epoch"],
        )


def clock_policy_hash_v1(policy: ClockPolicyV1) -> str:
    if type(policy) is not ClockPolicyV1:
        raise TypeError("policy must be ClockPolicyV1")
    return _hash_canonical(domain="clock_policy_height_only", value=policy.to_obj())


@dataclass(frozen=True, slots=True)
class ClockPolicyScheduleV1:
    """Governed, ordered HEIGHT_ONLY_V1 activation schedule."""

    policies: tuple[ClockPolicyV1, ...]

    def __post_init__(self) -> None:
        if type(self.policies) is not tuple:
            raise TypeError("policies must be a tuple")
        if not self.policies:
            raise ValueError("clock policy schedule must be non-empty")
        for index, policy in enumerate(self.policies):
            if type(policy) is not ClockPolicyV1:
                raise TypeError(f"policies[{index}] must be ClockPolicyV1")
            if index == 0:
                continue
            previous = self.policies[index - 1]
            if policy.chain_id != previous.chain_id:
                raise ValueError("clock policy schedule chain_id mismatch")
            if policy.consensus_domain_id != previous.consensus_domain_id:
                raise ValueError("clock policy schedule consensus domain mismatch")
            if policy.deployment_profile is not previous.deployment_profile:
                raise ValueError("clock policy schedule deployment profile mismatch")
            if (
                policy.activation_height - previous.activation_height
            ) % previous.blocks_per_epoch != 0:
                raise ValueError("successor policy must activate on an epoch boundary")
            previous.require_continuous_upgrade(policy)

    def active_policy_at_height(self, height: int) -> ClockPolicyV1:
        height_v = _require_u64(height, name="height")
        active: ClockPolicyV1 | None = None
        for policy in self.policies:
            if policy.activation_height > height_v:
                break
            active = policy
        if active is None:
            raise ValueError("height is before clock policy schedule activation")
        return active

    def to_obj(self) -> dict[str, object]:
        return {
            "schema": "zenodex/clock_policy_schedule/v1",
            "policies": [policy.to_obj() for policy in self.policies],
        }

    @classmethod
    def from_obj(cls, value: object) -> "ClockPolicyScheduleV1":
        if not isinstance(value, Mapping):
            raise TypeError("clock policy schedule must be an object")
        if set(value) != {"schema", "policies"}:
            raise ValueError("clock policy schedule fields mismatch")
        if value["schema"] != "zenodex/clock_policy_schedule/v1":
            raise ValueError("clock policy schedule schema unsupported")
        raw_policies = value["policies"]
        if not isinstance(raw_policies, list):
            raise TypeError("clock policy schedule policies must be a list")
        return cls(policies=tuple(ClockPolicyV1.from_obj(policy) for policy in raw_policies))


def clock_policy_schedule_hash_v1(schedule: ClockPolicyScheduleV1) -> str:
    if type(schedule) is not ClockPolicyScheduleV1:
        raise TypeError("schedule must be ClockPolicyScheduleV1")
    return _hash_canonical(
        domain="clock_policy_schedule",
        value=schedule.to_obj(),
    )


def default_height_only_clock_policy_v1(
    *,
    chain_id: str,
    blocks_per_epoch: int = 1,
) -> ClockPolicyV1:
    """Return the explicit local/default ZenoLedger clock policy.

    This helper is a deterministic construction convenience. Authoritative
    zUSD state commits the resulting policy hash, and execution still rejects
    any clock whose policy hash differs from that commitment.
    """

    chain_id_v = _require_nonempty_str(chain_id, name="chain_id")
    return ClockPolicyV1(
        clock_policy_id=CLOCK_POLICY_ID_HEIGHT_ONLY_V1,
        clock_policy_version=CLOCK_POLICY_VERSION_V1,
        chain_id=chain_id_v,
        deployment_profile=(ClockAuthorityProfileV1.ZENO_LEDGER_TAU_CHECKPOINTED_V1),
        consensus_domain_id=f"{chain_id_v}:zeno-ledger",
        activation_height=0,
        epoch_base=0,
        blocks_per_epoch=_require_u64(
            blocks_per_epoch,
            name="blocks_per_epoch",
        ),
    )


def default_height_only_clock_schedule_v1(
    *,
    chain_id: str,
    blocks_per_epoch: int = 1,
) -> ClockPolicyScheduleV1:
    return ClockPolicyScheduleV1(
        policies=(
            default_height_only_clock_policy_v1(
                chain_id=chain_id,
                blocks_per_epoch=blocks_per_epoch,
            ),
        )
    )


@dataclass(frozen=True, slots=True, init=False)
class VerifiedExecutionClockV1:
    """Policy-checked pre-execution height and epoch from one consensus domain.

    This value carries no current-block finality claim. The consensus shell
    constructs it after authorizing the parent and candidate height. Python's
    type system does not make it an unforgeable capability, so public decoders
    must never deserialize it directly from transaction data.
    """

    chain_id: str
    consensus_domain_id: str
    deployment_profile: ClockAuthorityProfileV1
    height: int
    derived_epoch: int
    clock_policy_hash: str
    clock_policy_schedule_hash: str
    clock_policy_schedule: ClockPolicyScheduleV1

    def __post_init__(self) -> None:
        _require_nonempty_str(self.chain_id, name="chain_id")
        _require_nonempty_str(self.consensus_domain_id, name="consensus_domain_id")
        if type(self.deployment_profile) is not ClockAuthorityProfileV1:
            raise TypeError("deployment_profile must be ClockAuthorityProfileV1")
        _require_u64(self.height, name="height")
        _require_u64(self.derived_epoch, name="derived_epoch")
        _require_root(self.clock_policy_hash, name="clock_policy_hash", allow_zero=False)
        _require_root(
            self.clock_policy_schedule_hash,
            name="clock_policy_schedule_hash",
            allow_zero=False,
        )
        if type(self.clock_policy_schedule) is not ClockPolicyScheduleV1:
            raise TypeError("clock_policy_schedule must be ClockPolicyScheduleV1")
        observed_schedule_hash = clock_policy_schedule_hash_v1(self.clock_policy_schedule)
        if self.clock_policy_schedule_hash != observed_schedule_hash:
            raise ValueError("clock_policy_schedule_hash mismatch")
        policy = self.clock_policy_schedule.active_policy_at_height(self.height)
        if self.chain_id != policy.chain_id:
            raise ValueError("chain_id mismatch")
        if self.consensus_domain_id != policy.consensus_domain_id:
            raise ValueError("consensus_domain_id mismatch")
        if self.deployment_profile is not policy.deployment_profile:
            raise ValueError("deployment_profile mismatch")
        if self.clock_policy_hash != clock_policy_hash_v1(policy):
            raise ValueError("clock_policy_hash mismatch")
        if self.derived_epoch != policy.epoch_at_height(self.height):
            raise ValueError("derived_epoch mismatch")


def verify_execution_clock_v1(
    *,
    chain_id: str,
    height: int,
    schedule: ClockPolicyScheduleV1,
    expected_schedule_hash: str,
) -> VerifiedExecutionClockV1:
    """Construct a clock under the governed policy schedule commitment."""

    if type(schedule) is not ClockPolicyScheduleV1:
        raise TypeError("schedule must be ClockPolicyScheduleV1")
    expected_hash = _require_root(
        expected_schedule_hash,
        name="expected_schedule_hash",
        allow_zero=False,
    )
    if clock_policy_schedule_hash_v1(schedule) != expected_hash:
        raise ValueError("clock policy schedule hash mismatch")
    chain_id_v = _require_nonempty_str(chain_id, name="chain_id")
    height_v = _require_u64(height, name="height")
    policy = schedule.active_policy_at_height(height_v)
    if policy.chain_id != chain_id_v:
        raise ValueError("clock policy chain_id mismatch")
    verified = object.__new__(VerifiedExecutionClockV1)
    object.__setattr__(verified, "chain_id", chain_id_v)
    object.__setattr__(verified, "consensus_domain_id", policy.consensus_domain_id)
    object.__setattr__(verified, "deployment_profile", policy.deployment_profile)
    object.__setattr__(verified, "height", height_v)
    object.__setattr__(verified, "derived_epoch", policy.epoch_at_height(height_v))
    object.__setattr__(verified, "clock_policy_hash", clock_policy_hash_v1(policy))
    object.__setattr__(verified, "clock_policy_schedule_hash", expected_hash)
    object.__setattr__(verified, "clock_policy_schedule", schedule)
    verified.__post_init__()
    return verified


@dataclass(frozen=True, slots=True)
class ExecutionHeaderCoreV1:
    """Acyclic block statement committed before proof and finality material."""

    schema_version: int
    chain_id: str
    consensus_domain_id: str
    deployment_profile: ClockAuthorityProfileV1
    height: int
    derived_epoch: int
    parent_header_hash: str
    sequencer_or_validator_set_hash: str
    ingress_root: str
    tx_root: str
    pre_state_root: str
    post_state_root: str
    app_hash: str
    effect_plan_hash: str
    evidence_root: str
    body_root: str
    data_availability_root: str
    clock_policy_hash: str
    clock_policy_schedule_hash: str
    finality_policy_hash: str
    config_digest: str
    module_versions_digest: str

    def __post_init__(self) -> None:
        _require_u64(self.schema_version, name="schema_version")
        if self.schema_version != EXECUTION_HEADER_CORE_VERSION_V1:
            raise ValueError("execution header core schema_version must equal 1")
        _require_nonempty_str(self.chain_id, name="chain_id")
        _require_nonempty_str(self.consensus_domain_id, name="consensus_domain_id")
        if type(self.deployment_profile) is not ClockAuthorityProfileV1:
            raise TypeError("deployment_profile must be ClockAuthorityProfileV1")
        _require_u64(self.height, name="height")
        _require_u64(self.derived_epoch, name="derived_epoch")
        for name in (
            "parent_header_hash",
            "sequencer_or_validator_set_hash",
            "ingress_root",
            "tx_root",
            "pre_state_root",
            "post_state_root",
            "app_hash",
            "effect_plan_hash",
            "evidence_root",
            "body_root",
            "data_availability_root",
            "clock_policy_hash",
            "clock_policy_schedule_hash",
            "finality_policy_hash",
            "config_digest",
            "module_versions_digest",
        ):
            _require_root(getattr(self, name), name=name)
        _require_root(self.effect_plan_hash, name="effect_plan_hash", allow_zero=False)
        _require_root(self.clock_policy_hash, name="clock_policy_hash", allow_zero=False)
        if self.height == 0:
            if self.parent_header_hash != ZERO_ROOT_V1:
                raise ValueError("genesis execution context parent_header_hash must be zero")
        elif self.parent_header_hash == ZERO_ROOT_V1:
            raise ValueError(
                "non-genesis execution context parent_header_hash must be non-zero"
            )

    def to_obj(self) -> dict[str, object]:
        return {
            "schema": "zenodex/execution_header_core/v1",
            "schema_version": self.schema_version,
            "chain_id": self.chain_id,
            "consensus_domain_id": self.consensus_domain_id,
            "deployment_profile": self.deployment_profile.value,
            "height": self.height,
            "derived_epoch": self.derived_epoch,
            "parent_header_hash": self.parent_header_hash,
            "sequencer_or_validator_set_hash": self.sequencer_or_validator_set_hash,
            "ingress_root": self.ingress_root,
            "tx_root": self.tx_root,
            "pre_state_root": self.pre_state_root,
            "post_state_root": self.post_state_root,
            "app_hash": self.app_hash,
            "effect_plan_hash": self.effect_plan_hash,
            "evidence_root": self.evidence_root,
            "body_root": self.body_root,
            "data_availability_root": self.data_availability_root,
            "clock_policy_hash": self.clock_policy_hash,
            "clock_policy_schedule_hash": self.clock_policy_schedule_hash,
            "finality_policy_hash": self.finality_policy_hash,
            "config_digest": self.config_digest,
            "module_versions_digest": self.module_versions_digest,
        }


def execution_context_hash_v1(core: ExecutionHeaderCoreV1) -> str:
    if type(core) is not ExecutionHeaderCoreV1:
        raise TypeError("core must be ExecutionHeaderCoreV1")
    return _hash_canonical(domain="execution_context", value=core.to_obj())


@dataclass(frozen=True, slots=True)
class ProofJournalBindingV1:
    """Acyclic proof commitment tied to one execution context.

    The backend verifier remains responsible for proving that
    ``raw_journal_hash`` names an authenticated journal whose decoded
    ``execution_context_hash`` equals this value.
    """

    schema_version: int
    execution_context_hash: str
    proof_metadata_hash: str
    raw_journal_hash: str

    def __post_init__(self) -> None:
        _require_u64(self.schema_version, name="proof journal binding schema_version")
        if self.schema_version != PROOF_JOURNAL_BINDING_VERSION_V1:
            raise ValueError("proof journal binding schema_version must equal 1")
        _require_root(
            self.execution_context_hash,
            name="proof journal binding execution_context_hash",
            allow_zero=False,
        )
        _require_root(
            self.proof_metadata_hash,
            name="proof journal binding proof_metadata_hash",
            allow_zero=False,
        )
        _require_root(
            self.raw_journal_hash,
            name="proof journal binding raw_journal_hash",
            allow_zero=False,
        )

    def to_obj(self) -> dict[str, object]:
        return {
            "schema": "zenodex/proof_journal_binding/v1",
            "schema_version": self.schema_version,
            "execution_context_hash": self.execution_context_hash,
            "proof_metadata_hash": self.proof_metadata_hash,
            "raw_journal_hash": self.raw_journal_hash,
        }


def proof_journal_binding_hash_v1(binding: ProofJournalBindingV1) -> str:
    if type(binding) is not ProofJournalBindingV1:
        raise TypeError("binding must be ProofJournalBindingV1")
    return _hash_canonical(domain="proof_journal_binding", value=binding.to_obj())


class ProofJournalVerifierV1(Protocol):
    """Trusted port that authenticates a proof receipt and decodes its journal."""

    def verify_proof_journal_v1(
        self,
        *,
        proof_artifact: bytes,
        expected_execution_context_hash: str,
    ) -> Mapping[str, object]: ...


@dataclass(frozen=True, slots=True, init=False)
class VerifiedProofJournalBindingV1:
    """Proof binding returned only after backend receipt admission succeeds."""

    binding: ProofJournalBindingV1
    binding_hash: str
    proof_artifact_hash: str
    proof_verifier_policy_hash: str

    def __post_init__(self) -> None:
        if type(self.binding) is not ProofJournalBindingV1:
            raise TypeError("binding must be ProofJournalBindingV1")
        expected_binding_hash = proof_journal_binding_hash_v1(self.binding)
        if self.binding_hash != expected_binding_hash:
            raise ValueError("verified proof binding_hash mismatch")
        _require_root(
            self.proof_artifact_hash,
            name="verified proof artifact hash",
            allow_zero=False,
        )
        _require_root(
            self.proof_verifier_policy_hash,
            name="verified proof verifier policy hash",
            allow_zero=False,
        )


@dataclass(frozen=True, slots=True, init=False)
class VerifiedExecutionContextV1:
    """Post-execution, pre-proof admission context for a candidate block."""

    core: ExecutionHeaderCoreV1
    execution_context_hash: str

    def __post_init__(self) -> None:
        _require_root(self.execution_context_hash, name="execution_context_hash")
        if self.execution_context_hash != execution_context_hash_v1(self.core):
            raise ValueError("execution_context_hash mismatch")

    @property
    def height(self) -> int:
        return self.core.height

    @property
    def derived_epoch(self) -> int:
        return self.core.derived_epoch

    def to_obj(self) -> dict[str, object]:
        return {
            "schema": "zenodex/verified_execution_context/v1",
            "execution_header_core": self.core.to_obj(),
            "execution_context_hash": self.execution_context_hash,
        }


def verify_execution_context_v1(
    *,
    core: ExecutionHeaderCoreV1,
    schedule: ClockPolicyScheduleV1,
    expected_schedule_hash: str,
) -> VerifiedExecutionContextV1:
    """Validate every clock binding and return an immutable execution witness."""

    if type(core) is not ExecutionHeaderCoreV1:
        raise TypeError("core must be ExecutionHeaderCoreV1")
    if type(schedule) is not ClockPolicyScheduleV1:
        raise TypeError("schedule must be ClockPolicyScheduleV1")
    expected_hash = _require_root(
        expected_schedule_hash,
        name="expected_schedule_hash",
        allow_zero=False,
    )
    if clock_policy_schedule_hash_v1(schedule) != expected_hash:
        raise ValueError("clock policy schedule hash mismatch")
    if core.clock_policy_schedule_hash != expected_hash:
        raise ValueError("execution context clock_policy_schedule_hash mismatch")
    policy = schedule.active_policy_at_height(core.height)
    if core.chain_id != policy.chain_id:
        raise ValueError("execution context chain_id mismatch")
    if core.consensus_domain_id != policy.consensus_domain_id:
        raise ValueError("execution context consensus_domain_id mismatch")
    if core.deployment_profile is not policy.deployment_profile:
        raise ValueError("execution context deployment_profile mismatch")
    if core.clock_policy_hash != clock_policy_hash_v1(policy):
        raise ValueError("execution context clock_policy_hash mismatch")
    expected_epoch = policy.epoch_at_height(core.height)
    if core.derived_epoch != expected_epoch:
        raise ValueError("execution context derived_epoch mismatch")
    verified = object.__new__(VerifiedExecutionContextV1)
    object.__setattr__(verified, "core", core)
    object.__setattr__(
        verified,
        "execution_context_hash",
        execution_context_hash_v1(core),
    )
    verified.__post_init__()
    return verified


def verify_proof_journal_binding_v1(
    *,
    verified_execution_context: VerifiedExecutionContextV1,
    proof_artifact: bytes,
    verifier: ProofJournalVerifierV1,
    expected_proof_verifier_policy_hash: str,
) -> VerifiedProofJournalBindingV1:
    """Authenticate one proof artifact and bind its decoded journal to context."""

    if type(verified_execution_context) is not VerifiedExecutionContextV1:
        raise TypeError("verified_execution_context must be VerifiedExecutionContextV1")
    if type(proof_artifact) is not bytes or not proof_artifact:
        raise ValueError("proof_artifact must be non-empty bytes")
    expected_policy_hash = _require_root(
        expected_proof_verifier_policy_hash,
        name="expected_proof_verifier_policy_hash",
        allow_zero=False,
    )
    artifact_hash = sha256_hex(
        domain_sep_bytes("proof_artifact", version=1) + encode_bytes(proof_artifact)
    )
    raw_facts = verifier.verify_proof_journal_v1(
        proof_artifact=proof_artifact,
        expected_execution_context_hash=(
            verified_execution_context.execution_context_hash
        ),
    )
    if not isinstance(raw_facts, Mapping):
        raise TypeError("proof journal verifier facts must be a mapping")
    expected_keys = {
        "execution_context_hash",
        "proof_metadata_hash",
        "raw_journal_hash",
        "proof_artifact_hash",
        "proof_verifier_policy_hash",
    }
    if set(raw_facts) != expected_keys:
        raise ValueError("proof journal verifier facts fields mismatch")
    execution_context_hash = _require_root(
        raw_facts["execution_context_hash"],
        name="proof verifier execution_context_hash",
        allow_zero=False,
    )
    if execution_context_hash != verified_execution_context.execution_context_hash:
        raise ValueError("proof verifier execution_context_hash mismatch")
    proof_metadata_hash = _require_root(
        raw_facts["proof_metadata_hash"],
        name="proof verifier proof_metadata_hash",
        allow_zero=False,
    )
    raw_journal_hash = _require_root(
        raw_facts["raw_journal_hash"],
        name="proof verifier raw_journal_hash",
        allow_zero=False,
    )
    bound_artifact_hash = _require_root(
        raw_facts["proof_artifact_hash"],
        name="proof verifier proof_artifact_hash",
        allow_zero=False,
    )
    if bound_artifact_hash != artifact_hash:
        raise ValueError("proof verifier proof_artifact_hash mismatch")
    verifier_policy_hash = _require_root(
        raw_facts["proof_verifier_policy_hash"],
        name="proof verifier policy hash",
        allow_zero=False,
    )
    if verifier_policy_hash != expected_policy_hash:
        raise ValueError("proof verifier policy hash mismatch")
    binding = ProofJournalBindingV1(
        schema_version=PROOF_JOURNAL_BINDING_VERSION_V1,
        execution_context_hash=execution_context_hash,
        proof_metadata_hash=proof_metadata_hash,
        raw_journal_hash=raw_journal_hash,
    )
    verified = object.__new__(VerifiedProofJournalBindingV1)
    object.__setattr__(verified, "binding", binding)
    object.__setattr__(
        verified,
        "binding_hash",
        proof_journal_binding_hash_v1(binding),
    )
    object.__setattr__(verified, "proof_artifact_hash", artifact_hash)
    object.__setattr__(
        verified,
        "proof_verifier_policy_hash",
        verifier_policy_hash,
    )
    verified.__post_init__()
    return verified


@dataclass(frozen=True, slots=True, init=False)
class FinalHeaderV1:
    """Final candidate header; signatures and finality stay outside this value."""

    execution_header_core: ExecutionHeaderCoreV1
    execution_context_hash: str
    proof_journal_hash: str

    def __post_init__(self) -> None:
        _require_root(self.execution_context_hash, name="execution_context_hash")
        _require_root(
            self.proof_journal_hash,
            name="proof_journal_hash",
            allow_zero=False,
        )
        if self.execution_context_hash != execution_context_hash_v1(self.execution_header_core):
            raise ValueError("final header execution_context_hash mismatch")

    def to_obj(self) -> dict[str, object]:
        return {
            "schema": "zenodex/final_header/v1",
            "execution_header_core": self.execution_header_core.to_obj(),
            "execution_context_hash": self.execution_context_hash,
            "proof_journal_hash": self.proof_journal_hash,
        }


def build_final_header_v1(
    *,
    verified_execution_context: VerifiedExecutionContextV1,
    verified_proof_binding: VerifiedProofJournalBindingV1,
) -> FinalHeaderV1:
    """Build a final-header candidate only from verified context and proof facts."""

    if type(verified_execution_context) is not VerifiedExecutionContextV1:
        raise TypeError("verified_execution_context must be VerifiedExecutionContextV1")
    if type(verified_proof_binding) is not VerifiedProofJournalBindingV1:
        raise TypeError("verified_proof_binding must be VerifiedProofJournalBindingV1")
    if verified_proof_binding.binding.execution_context_hash != (
        verified_execution_context.execution_context_hash
    ):
        raise ValueError("verified proof binding execution_context_hash mismatch")
    header = object.__new__(FinalHeaderV1)
    object.__setattr__(
        header,
        "execution_header_core",
        verified_execution_context.core,
    )
    object.__setattr__(
        header,
        "execution_context_hash",
        verified_execution_context.execution_context_hash,
    )
    object.__setattr__(
        header,
        "proof_journal_hash",
        verified_proof_binding.binding_hash,
    )
    header.__post_init__()
    return header


def final_header_hash_v1(header: FinalHeaderV1) -> str:
    if type(header) is not FinalHeaderV1:
        raise TypeError("header must be FinalHeaderV1")
    return _hash_canonical(domain="final_header", value=header.to_obj())


class FinalityCertificateVerifierV1(Protocol):
    """Trusted port that verifies quorum evidence for one final-header hash."""

    def verify_finality_certificate_v1(
        self,
        *,
        final_header_hash: str,
        certificate: bytes,
    ) -> Mapping[str, object]: ...


@dataclass(frozen=True, slots=True)
class _VerifiedFinalityFactsV1:
    final_header_hash: str
    certificate_hash: str
    finality_policy_hash: str
    signer_set_root: str
    signed_power: int
    total_power: int

    def __post_init__(self) -> None:
        _require_root(self.final_header_hash, name="finality facts final_header_hash")
        _require_root(self.certificate_hash, name="finality facts certificate_hash")
        _require_root(self.finality_policy_hash, name="finality facts finality_policy_hash")
        _require_root(self.signer_set_root, name="finality facts signer_set_root")
        _require_u64(self.signed_power, name="finality facts signed_power")
        _require_u64(self.total_power, name="finality facts total_power")


@dataclass(frozen=True, slots=True, init=False)
class FinalizedBlockContextV1:
    """Block context returned only after the configured verifier accepts."""

    verified_execution_context: VerifiedExecutionContextV1
    verified_proof_binding: VerifiedProofJournalBindingV1
    final_header: FinalHeaderV1
    final_header_hash: str
    _finality_facts: _VerifiedFinalityFactsV1

    @property
    def finality_certificate_hash(self) -> str:
        return self._finality_facts.certificate_hash

    def __post_init__(self) -> None:
        if type(self.verified_execution_context) is not VerifiedExecutionContextV1:
            raise TypeError(
                "verified_execution_context must be VerifiedExecutionContextV1"
            )
        if type(self.final_header) is not FinalHeaderV1:
            raise TypeError("final_header must be FinalHeaderV1")
        if type(self.verified_proof_binding) is not VerifiedProofJournalBindingV1:
            raise TypeError(
                "verified_proof_binding must be VerifiedProofJournalBindingV1"
            )
        if type(self._finality_facts) is not _VerifiedFinalityFactsV1:
            raise TypeError("_finality_facts must be _VerifiedFinalityFactsV1")
        expected_hash = final_header_hash_v1(self.final_header)
        if self.final_header_hash != expected_hash:
            raise ValueError("finalized context final_header_hash mismatch")
        if self._finality_facts.final_header_hash != expected_hash:
            raise ValueError("finalized context finality facts hash mismatch")
        if self.final_header.execution_header_core != self.verified_execution_context.core:
            raise ValueError("finalized context execution header core mismatch")
        if self.final_header.execution_context_hash != (
            self.verified_execution_context.execution_context_hash
        ):
            raise ValueError("finalized context execution_context_hash mismatch")
        if self.final_header.proof_journal_hash != (
            self.verified_proof_binding.binding_hash
        ):
            raise ValueError("finalized context proof binding mismatch")
        core = self.final_header.execution_header_core
        if self._finality_facts.signer_set_root != (
            core.sequencer_or_validator_set_hash
        ):
            raise ValueError("finality facts signer_set_root mismatch")
        if self._finality_facts.finality_policy_hash != core.finality_policy_hash:
            raise ValueError("finality facts finality_policy_hash mismatch")


def verify_finalized_block_context_v1(
    *,
    verified_execution_context: VerifiedExecutionContextV1,
    verified_proof_binding: VerifiedProofJournalBindingV1,
    final_header: FinalHeaderV1,
    certificate: bytes,
    verifier: FinalityCertificateVerifierV1,
    expected_finality_policy_hash: str,
) -> FinalizedBlockContextV1:
    """Verify finality evidence and bind it to the exact final-header hash."""

    if type(verified_execution_context) is not VerifiedExecutionContextV1:
        raise TypeError("verified_execution_context must be VerifiedExecutionContextV1")
    if type(final_header) is not FinalHeaderV1:
        raise TypeError("final_header must be FinalHeaderV1")
    if type(verified_proof_binding) is not VerifiedProofJournalBindingV1:
        raise TypeError("verified_proof_binding must be VerifiedProofJournalBindingV1")
    if type(certificate) is not bytes or not certificate:
        raise ValueError("certificate must be non-empty bytes")
    if final_header.execution_context_hash != (verified_execution_context.execution_context_hash):
        raise ValueError("finalized context execution_context_hash mismatch")
    if final_header.proof_journal_hash != verified_proof_binding.binding_hash:
        raise ValueError("finalized context proof binding mismatch")
    expected_policy_hash = _require_root(
        expected_finality_policy_hash,
        name="expected_finality_policy_hash",
        allow_zero=False,
    )
    final_hash = final_header_hash_v1(final_header)
    raw_facts = verifier.verify_finality_certificate_v1(
        final_header_hash=final_hash,
        certificate=certificate,
    )
    if not isinstance(raw_facts, Mapping):
        raise TypeError("finality verifier facts must be a mapping")
    expected_keys = {
        "final_header_hash",
        "certificate_hash",
        "finality_policy_hash",
        "signer_set_root",
        "signed_power",
        "total_power",
    }
    if set(raw_facts) != expected_keys:
        raise ValueError("finality verifier facts fields mismatch")
    bound_final_hash = _require_root(
        raw_facts["final_header_hash"],
        name="finality_facts.final_header_hash",
        allow_zero=False,
    )
    if bound_final_hash != final_hash:
        raise ValueError("finality certificate final_header_hash mismatch")
    expected_certificate_hash = sha256_hex(
        domain_sep_bytes("finality_certificate", version=1) + encode_bytes(certificate)
    )
    certificate_hash = _require_root(
        raw_facts["certificate_hash"],
        name="finality_facts.certificate_hash",
        allow_zero=False,
    )
    if certificate_hash != expected_certificate_hash:
        raise ValueError("finality certificate hash mismatch")
    finality_policy_hash = _require_root(
        raw_facts["finality_policy_hash"],
        name="finality_facts.finality_policy_hash",
        allow_zero=False,
    )
    if finality_policy_hash != expected_policy_hash:
        raise ValueError("finality certificate policy hash mismatch")
    signer_set_root = _require_root(
        raw_facts["signer_set_root"],
        name="finality_facts.signer_set_root",
        allow_zero=False,
    )
    core = final_header.execution_header_core
    if finality_policy_hash != core.finality_policy_hash:
        raise ValueError("finality certificate finality_policy_hash mismatch")
    if signer_set_root != core.sequencer_or_validator_set_hash:
        raise ValueError("finality certificate signer_set_root mismatch")
    signed_power = _require_u64(
        raw_facts["signed_power"],
        name="finality_facts.signed_power",
    )
    total_power = _require_u64(
        raw_facts["total_power"],
        name="finality_facts.total_power",
    )
    if total_power == 0 or signed_power == 0 or signed_power > total_power:
        raise ValueError("finality verifier power facts invalid")
    facts = _VerifiedFinalityFactsV1(
        final_header_hash=bound_final_hash,
        certificate_hash=certificate_hash,
        finality_policy_hash=finality_policy_hash,
        signer_set_root=signer_set_root,
        signed_power=signed_power,
        total_power=total_power,
    )
    finalized = object.__new__(FinalizedBlockContextV1)
    object.__setattr__(
        finalized,
        "verified_execution_context",
        verified_execution_context,
    )
    object.__setattr__(
        finalized,
        "verified_proof_binding",
        verified_proof_binding,
    )
    object.__setattr__(finalized, "final_header", final_header)
    object.__setattr__(finalized, "final_header_hash", final_hash)
    object.__setattr__(finalized, "_finality_facts", facts)
    finalized.__post_init__()
    return finalized


def derive_genesis_execution_clock_v1(
    *,
    chain_id: str,
    schedule: ClockPolicyScheduleV1,
    expected_schedule_hash: str,
) -> VerifiedExecutionClockV1:
    """Construct the height-zero clock under the governed genesis schedule."""

    return verify_execution_clock_v1(
        chain_id=chain_id,
        height=0,
        schedule=schedule,
        expected_schedule_hash=expected_schedule_hash,
    )


def derive_child_execution_clock_v1(
    *,
    finalized_parent: FinalizedBlockContextV1,
    schedule: ClockPolicyScheduleV1,
    expected_schedule_hash: str,
) -> VerifiedExecutionClockV1:
    """Derive candidate height as exactly one more than a finalized parent."""

    if type(finalized_parent) is not FinalizedBlockContextV1:
        raise TypeError("finalized_parent must be FinalizedBlockContextV1")
    expected_hash = _require_root(
        expected_schedule_hash,
        name="expected_schedule_hash",
        allow_zero=False,
    )
    if finalized_parent.verified_execution_context.core.clock_policy_schedule_hash != expected_hash:
        raise ValueError("parent clock policy schedule hash mismatch")
    parent_height = finalized_parent.verified_execution_context.core.height
    if parent_height == U64_MAX:
        raise ValueError("candidate height overflows u64")
    return verify_execution_clock_v1(
        chain_id=finalized_parent.verified_execution_context.core.chain_id,
        height=parent_height + 1,
        schedule=schedule,
        expected_schedule_hash=expected_hash,
    )
