"""Fail-closed composition checker for the unmounted FCIS M6 D08 stage.

D08 is a research verifier. It recomputes the source-bound pre-ANF lineage,
checks independent TCG/proof/DRA evidence, then evaluates the ANF-bound
decision and bundle. The module grants no runtime authority and performs no
datastore or external proof verification.
"""

from __future__ import annotations

from dataclasses import InitVar, dataclass
from enum import Enum
from typing import TypeAlias, cast, final

from ..state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex
from .fcis_authority_normal_form_v1 import (
    FCISAuthorityNormalFormV1,
    FCISProofContextRequirementV1,
)
from .fcis_commit_bundle_derivation import (
    CommitBundleV1,
    build_anf_bound_commit_bundle_v1,
    recompute_bundle_root_v1,
    recompute_outbox_plan_v1,
    verify_anf_bound_commit_bundle_v1,
)
from .fcis_decision_derivation import (
    AcceptV1,
    acceptance_receipt_root_v1,
    evaluate_source_bound_fcis_decision_with_anf_v1,
)
from .fcis_durable_retraction import (
    AuthorizedHistoryV1,
    DurableRetractionError,
    DurableSnapshotV1,
    OutboxEffectV1,
    PublicationAtomV1,
    ReopenRejectV1,
    derive_effect_id,
    encode_history,
    reopen_snapshot,
    tagged_digest,
)
from .fcis_lineage_closure import (
    FCISLineageClaimKeyV1,
)
from .fcis_source_bound_lineage import (
    FCISSourceBoundLineageCertificateV1,
    derive_source_bound_fcis_lineage_v1,
)
from .fcis_transition_budget import TransitionBudgetV1
from .fcis_tree_chord_gate_authority import (
    AuthorityGateV1,
    LineageV1,
    NodeArtifactExpectationV1,
    TreeChordGateCertificateV1,
    verify_tree_chord_gate_certificate,
)

D08_COMBINED_ANF_SCHEMA_V1 = "zenodex/fcis/m6/d08/combined-anf/v1"
_D08_CONSTRUCTION_TOKEN_V1 = object()
_HEX = frozenset("0123456789abcdef")


class D08CombinedANFCodeV1(Enum):
    """Stable fail-closed outcomes for the combined checker."""

    WRONG_EXACT_TYPE = "wrong_exact_type"
    SOURCE_EXTRACTION_REJECTED = "source_extraction_rejected"
    SOURCE_LINEAGE_MISMATCH = "source_lineage_mismatch"
    C3_ROOT_MISMATCH = "c3_root_mismatch"
    ANF_BASE_BINDING_MISMATCH = "anf_base_binding_mismatch"
    TCG_EXPECTATION_MISMATCH = "tcg_expectation_mismatch"
    TCG_REJECTED = "tcg_rejected"
    PROOF_CONTEXT_MISMATCH = "proof_context_mismatch"
    PUBLICATION_REJECTED = "publication_rejected"
    HISTORY_REJECTED = "history_rejected"
    POST_HISTORY_MISMATCH = "post_history_mismatch"
    ANF_DECISION_REJECTED = "anf_decision_rejected"
    LATER_ROOT_SUBSTITUTION = "later_root_substitution"
    BUNDLE_REJECTED = "bundle_rejected"


class D08CombinedANFError(ValueError):
    """Typed construction or derivation failure in the D08 language."""


def _digest(value: object, name: str) -> str:
    if (
        type(value) is not str
        or len(value) != 64
        or value != value.lower()
        or any(character not in _HEX for character in value)
    ):
        raise D08CombinedANFError(f"{name} must be 64 lowercase hexadecimal characters")
    return value


def _anf_digest(value: object, name: str) -> str:
    if (
        type(value) is not str
        or len(value) != 66
        or not value.startswith("0x")
        or value != value.lower()
        or any(character not in _HEX for character in value[2:])
    ):
        raise D08CombinedANFError(f"{name} must be a lowercase 0x digest")
    _digest(value[2:], name)
    return value


def _raw(value: str) -> str:
    return value[2:] if value.startswith("0x") else value


def _tagged(label: str) -> str:
    return cast(str, tagged_digest(label))


def _anf_tagged(label: str) -> str:
    return f"0x{_tagged(label)}"


def _decision_root_v1(decision: AcceptV1, bundle: CommitBundleV1) -> str:
    """Derive a pre-ANF decision identity from already-derived artifacts."""

    return _tagged(
        "d08/decision/"
        + acceptance_receipt_root_v1(decision)
        + "/"
        + decision.receipt.binding.commit_plan_root
        + "/"
        + bundle.bundle_root
    )


def _exact_text(value: object, name: str) -> str:
    if type(value) is not str or not value:
        raise D08CombinedANFError(f"{name} must be an exact nonempty string")
    return value


def derive_d08_proof_context_root_v1(
    *,
    proof_id: str,
    command_root: str,
    execution_context_root: str,
    pre_state_root: str,
    next_state_root: str,
    authority_epoch_root: str,
    verifier_profile_root: str,
    proof_root: str,
) -> str:
    """Derive one structural proof-context root from its exact fields."""

    payload = {
        "schema": D08_COMBINED_ANF_SCHEMA_V1 + "/proof-context",
        "proof_id": proof_id,
        "command_root": command_root,
        "execution_context_root": execution_context_root,
        "pre_state_root": pre_state_root,
        "next_state_root": next_state_root,
        "authority_epoch_root": authority_epoch_root,
        "verifier_profile_root": verifier_profile_root,
        "proof_root": proof_root,
    }
    return cast(
        str,
        sha256_hex(
            domain_sep_bytes(
                "zenodex/fcis/m6/d08/proof-context",
                version=1,
            )
            + canonical_json_bytes(payload)
        ),
    )


@final
@dataclass(frozen=True, slots=True)
class D08ProofContextV1:
    """Structural proof-context binding supplied by the external verifier lane."""

    proof_id: str
    command_root: str
    execution_context_root: str
    pre_state_root: str
    next_state_root: str
    authority_epoch_root: str
    verifier_profile_root: str
    proof_root: str
    context_root: str

    def __post_init__(self) -> None:
        _exact_text(self.proof_id, "proof_id")
        for name in (
            "command_root",
            "execution_context_root",
            "pre_state_root",
            "next_state_root",
            "authority_epoch_root",
            "verifier_profile_root",
            "proof_root",
            "context_root",
        ):
            _anf_digest(object.__getattribute__(self, name), name)
        if self.context_root != self.recomputed_root:
            raise D08CombinedANFError("proof context root does not rederive")

    @property
    def recomputed_root(self) -> str:
        return derive_d08_proof_context_root_v1(
            proof_id=self.proof_id,
            command_root=self.command_root,
            execution_context_root=self.execution_context_root,
            pre_state_root=self.pre_state_root,
            next_state_root=self.next_state_root,
            authority_epoch_root=self.authority_epoch_root,
            verifier_profile_root=self.verifier_profile_root,
            proof_root=self.proof_root,
        )


@final
@dataclass(frozen=True, slots=True)
class D08OutboxBindingV1:
    """External destination metadata needed to project one ANF effect to DRA."""

    ordinal: int
    record_identity: str
    destination: str
    payload_root: str
    adapter_profile_root: str

    def __post_init__(self) -> None:
        if type(self.ordinal) is not int or self.ordinal < 0:
            raise D08CombinedANFError("outbox binding ordinal must be a bounded int")
        _anf_digest(self.record_identity, "record_identity")
        _exact_text(self.destination, "destination")
        _anf_digest(self.payload_root, "payload_root")
        _digest(self.adapter_profile_root, "adapter_profile_root")


@final
@dataclass(frozen=True, slots=True)
class D08TCGExpectationV1:
    """Externally anchored TCG and D05 inventory expectations."""

    inventory_root: str
    topology_root: str
    instance_root: str
    source_node_id: str
    source_artifact_digest: str
    source_lineage: LineageV1
    sink_artifacts: tuple[NodeArtifactExpectationV1, ...]
    gates: tuple[AuthorityGateV1, ...]

    def __post_init__(self) -> None:
        _digest(self.inventory_root, "inventory_root")
        _digest(self.topology_root, "topology_root")
        _digest(self.instance_root, "instance_root")
        _exact_text(self.source_node_id, "source_node_id")
        _digest(self.source_artifact_digest, "source_artifact_digest")
        if type(self.source_lineage) is not tuple:
            raise D08CombinedANFError("source_lineage must be an exact tuple")
        if type(self.sink_artifacts) is not tuple or not self.sink_artifacts:
            raise D08CombinedANFError("sink_artifacts must be nonempty")
        if type(self.gates) is not tuple:
            raise D08CombinedANFError("gates must be an exact tuple")


@final
@dataclass(frozen=True, slots=True)
class D08CombinedANFInstanceV1:
    """All externally supplied values for one finite D08 composition check."""

    state_source: object
    settlement: object
    intents: object
    context: object
    budget: TransitionBudgetV1
    authority_normal_form: FCISAuthorityNormalFormV1
    base_decision: AcceptV1
    base_bundle: CommitBundleV1
    decision: AcceptV1
    bundle: CommitBundleV1
    tcg_certificate: TreeChordGateCertificateV1
    tcg_expectation: D08TCGExpectationV1
    proof_context: D08ProofContextV1 | None
    pre_snapshot: DurableSnapshotV1
    publication_atom: PublicationAtomV1
    outbox_bindings: tuple[D08OutboxBindingV1, ...]
    post_snapshot: DurableSnapshotV1

    def __post_init__(self) -> None:
        if type(self.budget) is not TransitionBudgetV1:
            raise D08CombinedANFError("budget must be exact")
        if type(self.authority_normal_form) is not FCISAuthorityNormalFormV1:
            raise D08CombinedANFError("authority normal form must be exact")
        for name in (
            "base_decision",
            "decision",
        ):
            if type(object.__getattribute__(self, name)) is not AcceptV1:
                raise D08CombinedANFError(f"{name} must be exact AcceptV1")
        for name in ("base_bundle", "bundle"):
            if type(object.__getattribute__(self, name)) is not CommitBundleV1:
                raise D08CombinedANFError(f"{name} must be exact CommitBundleV1")
        if type(self.tcg_certificate) is not TreeChordGateCertificateV1:
            raise D08CombinedANFError("tcg_certificate must be exact")
        if type(self.tcg_expectation) is not D08TCGExpectationV1:
            raise D08CombinedANFError("tcg_expectation must be exact")
        if self.proof_context is not None and type(self.proof_context) is not D08ProofContextV1:
            raise D08CombinedANFError("proof_context must be exact or None")
        for name in ("pre_snapshot", "post_snapshot"):
            if type(object.__getattribute__(self, name)) is not DurableSnapshotV1:
                raise D08CombinedANFError(f"{name} must be exact DurableSnapshotV1")
        if type(self.publication_atom) is not PublicationAtomV1:
            raise D08CombinedANFError("publication_atom must be exact")
        if type(self.outbox_bindings) is not tuple:
            raise D08CombinedANFError("outbox_bindings must be an exact tuple")
        for binding in self.outbox_bindings:
            if type(binding) is not D08OutboxBindingV1:
                raise D08CombinedANFError("outbox binding must be exact")
        if tuple(item.ordinal for item in self.outbox_bindings) != tuple(
            range(len(self.outbox_bindings))
        ):
            raise D08CombinedANFError("outbox binding ordinals must be contiguous")


@final
@dataclass(frozen=True, slots=True)
class D08CombinedANFAcceptV1:
    """Verifier-minted result carrying exactly one canonical ANF root."""

    anf_root: str
    _construction_token: InitVar[object]

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _D08_CONSTRUCTION_TOKEN_V1:
            raise TypeError("D08 acceptance requires controlled verification")
        _anf_digest(self.anf_root, "anf_root")


@final
@dataclass(frozen=True, slots=True)
class D08CombinedANFRejectV1:
    """Verifier-minted typed rejection with no authority payload."""

    code: D08CombinedANFCodeV1
    path: tuple[str, ...]
    _construction_token: InitVar[object]

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _D08_CONSTRUCTION_TOKEN_V1:
            raise TypeError("D08 rejection requires controlled verification")
        if type(self.code) is not D08CombinedANFCodeV1:
            raise TypeError("D08 rejection code must be exact")
        if type(self.path) is not tuple or any(type(item) is not str for item in self.path):
            raise TypeError("D08 rejection path must be exact")


D08CombinedANFResultV1: TypeAlias = D08CombinedANFAcceptV1 | D08CombinedANFRejectV1


def _reject(
    code: D08CombinedANFCodeV1,
    *path: str,
) -> D08CombinedANFRejectV1:
    return D08CombinedANFRejectV1(
        code=code,
        path=path,
        _construction_token=_D08_CONSTRUCTION_TOKEN_V1,
    )


def _validate_base_lineage(
    instance: D08CombinedANFInstanceV1,
    source: FCISSourceBoundLineageCertificateV1,
) -> D08CombinedANFRejectV1 | None:
    closure = source.closure
    if closure.decision != instance.base_decision:
        return _reject(D08CombinedANFCodeV1.SOURCE_LINEAGE_MISMATCH, "base_decision")
    if closure.bundle != instance.base_bundle:
        return _reject(D08CombinedANFCodeV1.SOURCE_LINEAGE_MISMATCH, "base_bundle")
    anf = instance.authority_normal_form
    binding = instance.base_decision.receipt.binding
    evidence = closure.evaluation.evidence
    segment = closure.occurrence_segment
    expected_pairs = (
        ("command_root", evidence.command_root),
        ("execution_context_root", evidence.execution_context_hash),
        ("pre_state_root", evidence.pre_state_root),
        ("next_state_root", evidence.post_state_root),
        ("support_root", evidence.support_root),
        ("support_set_commitment", evidence.support_set_commitment),
        ("snapshot_commitment", evidence.snapshot_commitment),
        ("patch_root", binding.patch_root),
        ("commit_plan_root", binding.commit_plan_root),
        ("budget_root", binding.budget_hash),
        ("boundary_root", f"0x{segment.boundary_root}"),
        ("policy_root", f"0x{segment.policy_root}"),
        ("witness_tuple_root", f"0x{segment.witness_tuple_root}"),
        ("semantic_stream_root", f"0x{segment.semantic_stream_root}"),
        ("lineage_stream_root", f"0x{segment.lineage_stream_root}"),
    )
    for field_name, expected in expected_pairs:
        if getattr(anf, field_name) != expected:
            return _reject(
                D08CombinedANFCodeV1.ANF_BASE_BINDING_MISMATCH,
                field_name,
            )
    if anf.acceptance_receipt_root != acceptance_receipt_root_v1(instance.base_decision):
        return _reject(
            D08CombinedANFCodeV1.ANF_BASE_BINDING_MISMATCH,
            "acceptance_receipt_root",
        )
    if anf.base_bundle_root != instance.base_bundle.bundle_root:
        return _reject(
            D08CombinedANFCodeV1.ANF_BASE_BINDING_MISMATCH,
            "base_bundle_root",
        )
    if anf.outbox_plan_root != instance.base_bundle.outbox_root:
        return _reject(
            D08CombinedANFCodeV1.ANF_BASE_BINDING_MISMATCH,
            "outbox_plan_root",
        )
    if (
        anf.acceptance_decision_root
        != f"0x{_decision_root_v1(instance.base_decision, instance.base_bundle)}"
    ):
        return _reject(
            D08CombinedANFCodeV1.ANF_BASE_BINDING_MISMATCH,
            "acceptance_decision_root",
        )
    if anf.c3_claim_set_root != closure.closed_claims.root:
        return _reject(
            D08CombinedANFCodeV1.C3_ROOT_MISMATCH,
            "c3_claim_set_root",
        )
    for key, field_name in (
        (FCISLineageClaimKeyV1.EVALUATION_CERTIFICATE_ROOT, "evaluation_certificate_root"),
        (FCISLineageClaimKeyV1.RECEIPT_CERTIFICATE_ROOT, "receipt_certificate_root"),
        (FCISLineageClaimKeyV1.BUNDLE_CERTIFICATE_ROOT, "bundle_certificate_root"),
        (FCISLineageClaimKeyV1.OUTBOX_CERTIFICATE_ROOT, "outbox_certificate_root"),
    ):
        expected = closure.closed_claims.value_for(key)
        if expected is None or getattr(anf, field_name) != expected:
            return _reject(
                D08CombinedANFCodeV1.C3_ROOT_MISMATCH,
                field_name,
            )
    return None


def _verify_tcg(
    instance: D08CombinedANFInstanceV1,
) -> D08CombinedANFRejectV1 | None:
    expected = instance.tcg_expectation
    certificate = instance.tcg_certificate
    try:
        verdict = verify_tree_chord_gate_certificate(
            expected_topology_root=expected.topology_root,
            expected_instance_root=expected.instance_root,
            expected_source_node_id=expected.source_node_id,
            expected_source_artifact_digest=expected.source_artifact_digest,
            expected_source_lineage=expected.source_lineage,
            expected_sink_artifacts=expected.sink_artifacts,
            expected_gates=expected.gates,
            certificate=certificate,
        )
    except (
        AttributeError,
        TypeError,
        ValueError,
        ArithmeticError,
        OverflowError,
        RecursionError,
    ):
        return _reject(D08CombinedANFCodeV1.TCG_REJECTED, "certificate")
    if not verdict.accepted:
        return _reject(D08CombinedANFCodeV1.TCG_REJECTED, verdict.reason)
    anf = instance.authority_normal_form
    if anf.tcg_topology_root != f"0x{expected.topology_root}":
        return _reject(
            D08CombinedANFCodeV1.TCG_EXPECTATION_MISMATCH,
            "anf",
            "tcg_topology_root",
        )
    if anf.tcg_instance_root != f"0x{expected.instance_root}":
        return _reject(
            D08CombinedANFCodeV1.TCG_EXPECTATION_MISMATCH,
            "anf",
            "tcg_instance_root",
        )
    return None


def _verify_proof_context(
    instance: D08CombinedANFInstanceV1,
    pre_history: AuthorizedHistoryV1,
) -> D08CombinedANFRejectV1 | None:
    anf = instance.authority_normal_form
    context = instance.proof_context
    if anf.proof_context_requirement is FCISProofContextRequirementV1.NOT_REQUIRED:
        if context is not None:
            return _reject(
                D08CombinedANFCodeV1.PROOF_CONTEXT_MISMATCH,
                "unexpected_context",
            )
        return None
    if context is None:
        return _reject(
            D08CombinedANFCodeV1.PROOF_CONTEXT_MISMATCH,
            "missing_context",
        )
    try:
        context.__post_init__()
    except (D08CombinedANFError, TypeError, ValueError):
        return _reject(
            D08CombinedANFCodeV1.PROOF_CONTEXT_MISMATCH,
            "context",
        )
    expected = (
        ("command_root", anf.command_root),
        ("execution_context_root", anf.execution_context_root),
        ("pre_state_root", anf.pre_state_root),
        ("next_state_root", anf.next_state_root),
        ("authority_epoch_root", f"0x{pre_history.authority.root}"),
        ("verifier_profile_root", f"0x{pre_history.verifier_profile_root}"),
    )
    for field_name, value in expected:
        if getattr(context, field_name) != value:
            return _reject(
                D08CombinedANFCodeV1.PROOF_CONTEXT_MISMATCH,
                field_name,
            )
    if anf.proof_context_root != context.context_root:
        return _reject(
            D08CombinedANFCodeV1.PROOF_CONTEXT_MISMATCH,
            "context_root",
        )
    return None


def _expected_outbox(
    base_bundle: CommitBundleV1,
    bindings: tuple[D08OutboxBindingV1, ...],
    *,
    commit_id: str,
    writer_profile_root: str,
) -> tuple[OutboxEffectV1, ...]:
    records = base_bundle.outbox_plan.records
    if len(records) != len(bindings):
        raise D08CombinedANFError("outbox binding cardinality does not match the plan")
    effects: list[OutboxEffectV1] = []
    for binding in bindings:
        record = records[binding.ordinal]
        if record.effect_identity != binding.record_identity:
            raise D08CombinedANFError("outbox record identity is crossed")
        effects.append(
            OutboxEffectV1(
                effect_id=derive_effect_id(
                    commit_id=commit_id,
                    ordinal=binding.ordinal,
                    destination=binding.destination,
                    payload_root=_raw(binding.payload_root),
                    writer_profile_root=writer_profile_root,
                ),
                ordinal=binding.ordinal,
                destination=binding.destination,
                payload_root=_raw(binding.payload_root),
                adapter_profile_root=binding.adapter_profile_root,
            )
        )
    return tuple(effects)


def derive_d08_publication_atom_v1(
    *,
    authority_normal_form: FCISAuthorityNormalFormV1,
    base_bundle: CommitBundleV1,
    pre_history: AuthorizedHistoryV1,
    outbox_bindings: tuple[D08OutboxBindingV1, ...],
) -> PublicationAtomV1:
    """Derive the expected DRA atom from pre-ANF artifacts and supplied effects."""

    if type(authority_normal_form) is not FCISAuthorityNormalFormV1:
        raise D08CombinedANFError("authority normal form must be exact")
    if type(base_bundle) is not CommitBundleV1:
        raise D08CombinedANFError("base bundle must be exact")
    if type(pre_history) is not AuthorizedHistoryV1:
        raise D08CombinedANFError("pre-history must be exact")
    authority_normal_form.__post_init__()
    try:
        canonical_bytes, bundle_root = recompute_bundle_root_v1(base_bundle)
        if (
            canonical_bytes != base_bundle.canonical_bundle_bytes
            or bundle_root != base_bundle.bundle_root
            or recompute_outbox_plan_v1(base_bundle) != base_bundle.outbox_plan
        ):
            raise D08CombinedANFError("base bundle does not rederive")
    except (AttributeError, TypeError, ValueError, ArithmeticError) as exc:
        raise D08CombinedANFError("base bundle is invalid") from exc
    pre_history.__post_init__()
    if pre_history.current_state_root != _raw(authority_normal_form.pre_state_root):
        raise D08CombinedANFError("pre-history state root does not match ANF")
    if type(outbox_bindings) is not tuple:
        raise D08CombinedANFError("outbox bindings must be exact")
    if tuple(item.ordinal for item in outbox_bindings) != tuple(range(len(outbox_bindings))):
        raise D08CombinedANFError("outbox binding order is not canonical")
    commit_id = _tagged("d08/commit/" + base_bundle.bundle_root + "/" + pre_history.root)
    writer_profile_root = pre_history.authority.allowed_writer_roots[0]
    outbox = _expected_outbox(
        base_bundle,
        outbox_bindings,
        commit_id=commit_id,
        writer_profile_root=writer_profile_root,
    )
    return PublicationAtomV1(
        sequence=len(pre_history.atoms) + 1,
        commit_id=commit_id,
        command_root=_raw(authority_normal_form.command_root),
        expected_pre_root=pre_history.current_state_root,
        post_state_root=_raw(authority_normal_form.next_state_root),
        writer_profile_root=writer_profile_root,
        authority_epoch_index=pre_history.authority.epoch_index,
        authority_state_root=pre_history.authority.root,
        nullifier_root=_tagged("d08/nullifier/" + commit_id),
        response_root=_tagged("d08/response/" + base_bundle.receipt_root),
        receipt_root=_raw(base_bundle.receipt_root),
        decision_root=_decision_root_v1(
            base_bundle.decision,
            base_bundle,
        ),
        bundle_root=_raw(base_bundle.bundle_root),
        replay_root=_tagged("d08/replay/" + base_bundle.bundle_root),
        outbox=outbox,
        deployment_config_root=pre_history.deployment_config_root,
        verifier_profile_root=pre_history.verifier_profile_root,
    )


def _verify_dra(
    instance: D08CombinedANFInstanceV1,
    pre_history: AuthorizedHistoryV1,
) -> D08CombinedANFRejectV1 | None:
    try:
        expected_atom = derive_d08_publication_atom_v1(
            authority_normal_form=instance.authority_normal_form,
            base_bundle=instance.base_bundle,
            pre_history=pre_history,
            outbox_bindings=instance.outbox_bindings,
        )
    except (
        AttributeError,
        D08CombinedANFError,
        DurableRetractionError,
        IndexError,
        TypeError,
        ValueError,
        OverflowError,
    ):
        return _reject(D08CombinedANFCodeV1.PUBLICATION_REJECTED, "atom")
    if instance.publication_atom != expected_atom:
        return _reject(D08CombinedANFCodeV1.PUBLICATION_REJECTED, "atom")
    if instance.authority_normal_form.dra_pre_history_root != f"0x{pre_history.root}":
        return _reject(
            D08CombinedANFCodeV1.PUBLICATION_REJECTED,
            "dra_pre_history_root",
        )
    if instance.authority_normal_form.migration_authority_epoch_root != (
        f"0x{pre_history.authority.root}"
    ):
        return _reject(
            D08CombinedANFCodeV1.PUBLICATION_REJECTED,
            "migration_authority_epoch_root",
        )
    try:
        reopened_post = reopen_snapshot(instance.post_snapshot)
    except (AttributeError, TypeError, ValueError, DurableRetractionError):
        return _reject(D08CombinedANFCodeV1.HISTORY_REJECTED, "post")
    if isinstance(reopened_post, ReopenRejectV1):
        return _reject(
            D08CombinedANFCodeV1.HISTORY_REJECTED,
            "post",
            reopened_post.code.value,
        )
    expected_history = AuthorizedHistoryV1(
        genesis_state_root=pre_history.genesis_state_root,
        authority_epochs=pre_history.authority_epochs,
        atoms=pre_history.atoms + (expected_atom,),
        acks=pre_history.acks,
        deployment_config_root=pre_history.deployment_config_root,
        verifier_profile_root=pre_history.verifier_profile_root,
    )
    expected_snapshot = encode_history(expected_history)
    if instance.authority_normal_form.dra_post_history_root != (f"0x{expected_history.root}"):
        return _reject(
            D08CombinedANFCodeV1.POST_HISTORY_MISMATCH,
            "dra_post_history_root",
        )
    if instance.post_snapshot != expected_snapshot:
        return _reject(
            D08CombinedANFCodeV1.POST_HISTORY_MISMATCH,
            "post_snapshot",
        )
    if reopened_post != expected_history:
        return _reject(
            D08CombinedANFCodeV1.POST_HISTORY_MISMATCH,
            "post_history",
        )
    return None


def verify_combined_anf_v1(
    instance: object,
) -> D08CombinedANFResultV1:
    """Recompute every D08 stage and return one verifier-minted ANF root."""

    if type(instance) is not D08CombinedANFInstanceV1:
        return _reject(D08CombinedANFCodeV1.WRONG_EXACT_TYPE, "instance")
    exact = instance
    try:
        exact.__post_init__()
    except (
        AttributeError,
        D08CombinedANFError,
        DurableRetractionError,
        TypeError,
        ValueError,
        OverflowError,
    ):
        return _reject(D08CombinedANFCodeV1.WRONG_EXACT_TYPE, "instance")

    try:
        source_result = derive_source_bound_fcis_lineage_v1(
            state_source=exact.state_source,
            settlement=exact.settlement,
            intents=exact.intents,
            context=exact.context,
            budget=exact.budget,
        )
    except (
        AttributeError,
        DurableRetractionError,
        TypeError,
        ValueError,
        ArithmeticError,
        OverflowError,
        RecursionError,
    ):
        return _reject(
            D08CombinedANFCodeV1.SOURCE_EXTRACTION_REJECTED,
            "source",
        )
    if type(source_result) is not FCISSourceBoundLineageCertificateV1:
        return _reject(
            D08CombinedANFCodeV1.SOURCE_EXTRACTION_REJECTED,
            "source",
        )
    base_reject = _validate_base_lineage(exact, source_result)
    if base_reject is not None:
        return base_reject

    try:
        pre_reopened = reopen_snapshot(exact.pre_snapshot)
    except (AttributeError, TypeError, ValueError, DurableRetractionError):
        return _reject(D08CombinedANFCodeV1.HISTORY_REJECTED, "pre")
    if isinstance(pre_reopened, ReopenRejectV1):
        return _reject(
            D08CombinedANFCodeV1.HISTORY_REJECTED,
            "pre",
            pre_reopened.code.value,
        )
    if pre_reopened.current_state_root != _raw(exact.authority_normal_form.pre_state_root):
        return _reject(D08CombinedANFCodeV1.PUBLICATION_REJECTED, "pre_state_root")

    tcg_reject = _verify_tcg(exact)
    if tcg_reject is not None:
        return tcg_reject
    proof_reject = _verify_proof_context(exact, pre_reopened)
    if proof_reject is not None:
        return proof_reject
    dra_reject = _verify_dra(exact, pre_reopened)
    if dra_reject is not None:
        return dra_reject

    try:
        anf_root = exact.authority_normal_form.root
        fresh_decision = evaluate_source_bound_fcis_decision_with_anf_v1(
            source_occurrence=source_result.extraction,
            budget=exact.budget,
            authority_normal_form=exact.authority_normal_form,
        )
    except (AttributeError, TypeError, ValueError, ArithmeticError):
        return _reject(D08CombinedANFCodeV1.ANF_DECISION_REJECTED, "decision")
    if type(fresh_decision) is not AcceptV1:
        return _reject(D08CombinedANFCodeV1.ANF_DECISION_REJECTED, "decision")
    if fresh_decision != exact.decision:
        return _reject(
            D08CombinedANFCodeV1.LATER_ROOT_SUBSTITUTION,
            "decision",
        )
    try:
        fresh_bundle = build_anf_bound_commit_bundle_v1(
            fresh_decision,
            exact.authority_normal_form,
        )
    except (AttributeError, TypeError, ValueError, ArithmeticError):
        return _reject(D08CombinedANFCodeV1.BUNDLE_REJECTED, "bundle")
    if type(fresh_bundle) is not CommitBundleV1:
        return _reject(D08CombinedANFCodeV1.BUNDLE_REJECTED, "bundle")
    if fresh_bundle != exact.bundle:
        return _reject(
            D08CombinedANFCodeV1.LATER_ROOT_SUBSTITUTION,
            "bundle",
        )
    if not verify_anf_bound_commit_bundle_v1(exact.bundle):
        return _reject(D08CombinedANFCodeV1.BUNDLE_REJECTED, "bundle")
    return D08CombinedANFAcceptV1(
        anf_root=anf_root,
        _construction_token=_D08_CONSTRUCTION_TOKEN_V1,
    )


__all__ = (
    "D08_COMBINED_ANF_SCHEMA_V1",
    "D08CombinedANFCodeV1",
    "D08CombinedANFError",
    "D08CombinedANFInstanceV1",
    "D08CombinedANFAcceptV1",
    "D08CombinedANFRejectV1",
    "D08CombinedANFResultV1",
    "D08OutboxBindingV1",
    "D08ProofContextV1",
    "D08TCGExpectationV1",
    "derive_d08_proof_context_root_v1",
    "derive_d08_publication_atom_v1",
    "verify_combined_anf_v1",
)
