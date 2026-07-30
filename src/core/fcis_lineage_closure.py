"""Unmounted concrete certificate-closure spine for FCIS lineage.

This module projects the actual step evaluation, acceptance receipt, commit
bundle, and outbox plan into one closed claim language.  It also binds the
Segmented Lineage Normal Form semantic and provenance roots through explicit
receipt and bundle extension roots.

The construction is deliberately unmounted. The low-level artifact builders are
private because they accept an already-derived occurrence segment. The public
research constructor in ``fcis_source_bound_lineage`` derives that segment from
admitted pre-state, command, context, and exact settlement replay before candidate
evaluation. Closure confluence still does not authenticate shell or datastore
sources.
"""

from __future__ import annotations

from dataclasses import InitVar, dataclass
from enum import Enum
from typing import TypeAlias, cast, final

from ..state.canonical import domain_sep_bytes, hex_to_bytes_fixed, sha256_hex
from .fcis_commit_bundle_derivation import (
    CommitBundleV1,
    build_commit_bundle_v1,
    recompute_bundle_root_v1,
    recompute_outbox_plan_v1,
)
from .fcis_decision_derivation import (
    FCIS_SPOT_TRANSITION_BUDGET_V1,
    AcceptV1,
    RejectV1,
    _claim_root_v1,
    _derive_plan_v1,
    _revalidate_evaluation_v1,
    acceptance_receipt_root_v1,
    evaluate_fcis_decision_v1,
)
from .fcis_fee_occurrence_normal_form import (
    CanonicalFeeOccurrenceSegmentV1,
    fee_amount_candidates_from_segment_v1,
)
from .fcis_outbox_values import FCIS_OUTBOX_PLAN_SCHEMA_ID_V1
from .fcis_step_evaluation_values import (
    FCISStepEvaluationOkV1,
    FCISStepEvaluationRejectV1,
)
from .fcis_step_evaluator import evaluate_fcis_step_candidate_v1
from .fcis_transition_budget import (
    FCIS_TRANSITION_BUDGET_SCHEMA_ID_V1,
    TransitionBudgetV1,
)
from .fcis_transition_values import (
    FCIS_COMMIT_PLAN_SCHEMA_ID_V1,
    FCIS_DEX_PATCH_SCHEMA_ID_V1,
)

FCIS_LINEAGE_CLOSURE_VERSION_V1 = "zenodex/fcis/lineage-closure/v1"
FCIS_LINEAGE_RECEIPT_EXTENSION_VERSION_V1 = "zenodex/fcis/lineage-receipt-extension/v1"
FCIS_LINEAGE_BUNDLE_EXTENSION_VERSION_V1 = "zenodex/fcis/lineage-bundle-extension/v1"
MAX_FCIS_LINEAGE_CLAIMS_V1 = 64

_LINEAGE_CONSTRUCTION_TOKEN_V1 = object()


class FCISLineageAxisV1(Enum):
    SEMANTIC = "semantic"
    AUTHORITY = "authority"
    DURABILITY = "durability"


FCIS_LINEAGE_CANONICAL_AXIS_ORDER_V1 = (
    FCISLineageAxisV1.SEMANTIC,
    FCISLineageAxisV1.AUTHORITY,
    FCISLineageAxisV1.DURABILITY,
)


class FCISLineageClaimKeyV1(Enum):
    COMMAND_ROOT = "source/command_root"
    EXECUTION_CONTEXT_HASH = "source/execution_context_hash"
    PRE_STATE_ROOT = "source/pre_state_root"
    NEXT_STATE_ROOT = "source/next_state_root"
    SUPPORT_ROOT = "source/support_root"
    SUPPORT_SET_COMMITMENT = "source/support_set_commitment"
    SNAPSHOT_COMMITMENT = "source/snapshot_commitment"
    PATCH_ROOT = "candidate/patch_root"
    COMMIT_PLAN_ROOT = "candidate/commit_plan_root"
    FEE_BOUNDARY_ROOT = "fee/boundary_root"
    FEE_POLICY_ROOT = "fee/policy_root"
    FEE_WITNESS_TUPLE_ROOT = "fee/witness_tuple_root"
    FEE_SEMANTIC_STREAM_ROOT = "fee/semantic_stream_root"
    FEE_LINEAGE_STREAM_ROOT = "fee/lineage_stream_root"
    BUDGET_HASH = "authority/budget_hash"
    ACCEPTANCE_RECEIPT_ROOT = "authority/acceptance_receipt_root"
    OUTBOX_PLAN_ROOT = "durability/outbox_plan_root"
    BASE_BUNDLE_ROOT = "durability/base_bundle_root"
    EVALUATION_CERTIFICATE_ROOT = "derived/evaluation_certificate_root"
    RECEIPT_CERTIFICATE_ROOT = "derived/receipt_certificate_root"
    BUNDLE_CERTIFICATE_ROOT = "derived/bundle_certificate_root"
    OUTBOX_CERTIFICATE_ROOT = "derived/outbox_certificate_root"


class FCISLineageClosureCodeV1(Enum):
    WRONG_EXACT_TYPE = "wrong_exact_type"
    INVALID_AXIS_ORDER = "invalid_axis_order"
    INVALID_OCCURRENCE_SEGMENT = "invalid_occurrence_segment"
    EVALUATION_REJECTED = "evaluation_rejected"
    DECISION_REJECTED = "decision_rejected"
    BUNDLE_REJECTED = "bundle_rejected"
    LINEAGE_MISMATCH = "lineage_mismatch"
    CLAIM_CONFLICT = "claim_conflict"
    DERIVED_CLAIM_CONFLICT = "derived_claim_conflict"
    INTERNAL_RELATION_FAILURE = "internal_relation_failure"


def _is_digest_v1(value: object) -> bool:
    return (
        type(value) is str
        and len(value) == 66
        and value.startswith("0x")
        and value == value.lower()
        and all(character in "0123456789abcdef" for character in value[2:])
    )


def _require_digest_v1(name: str, value: object) -> str:
    if not _is_digest_v1(value):
        raise ValueError(f"{name} must be a canonical lowercase 0x digest")
    exact = cast(str, value)
    hex_to_bytes_fixed(exact, nbytes=32, name=name)
    return exact


def _segment_digest_v1(name: str, value: object) -> str:
    if (
        type(value) is not str
        or len(value) != 64
        or value != value.lower()
        or any(character not in "0123456789abcdef" for character in value)
    ):
        raise ValueError(f"{name} must be a lowercase SHA-256 hex digest")
    return f"0x{value}"


def _u32_be_v1(value: int) -> bytes:
    if type(value) is not int or not 0 <= value < 1 << 32:
        raise ValueError("lineage frame integer must fit U32")
    return value.to_bytes(4, "big")


def _frame_v1(value: bytes) -> bytes:
    return _u32_be_v1(len(value)) + value


def _raw32_v1(value: str) -> bytes:
    return hex_to_bytes_fixed(value, nbytes=32, name="lineage_digest")


@final
@dataclass(frozen=True, slots=True)
class FCISLineageClaimV1:
    key: FCISLineageClaimKeyV1
    value_digest: str

    def __post_init__(self) -> None:
        if type(self.key) is not FCISLineageClaimKeyV1:
            raise TypeError("lineage claim key must be exact")
        _require_digest_v1("lineage claim value", self.value_digest)


@final
@dataclass(frozen=True, slots=True)
class FCISLineageClaimSetV1:
    """Canonical conflict-free claims; replay evidence, not commit authority."""

    claims: tuple[FCISLineageClaimV1, ...]

    def __post_init__(self) -> None:
        if type(self.claims) is not tuple:
            raise TypeError("lineage claims must be an exact tuple")
        if len(self.claims) > MAX_FCIS_LINEAGE_CLAIMS_V1:
            raise ValueError("lineage claim set exceeds its item bound")
        for claim in self.claims:
            if type(claim) is not FCISLineageClaimV1:
                raise TypeError("lineage claim must be exact")
            claim.__post_init__()
        keys = tuple(claim.key.value for claim in self.claims)
        if keys != tuple(sorted(keys, key=lambda value: value.encode("utf-8"))):
            raise ValueError("lineage claims must use canonical key order")
        if len(set(keys)) != len(keys):
            raise ValueError("lineage claim keys must be unique")

    def value_for(self, key: FCISLineageClaimKeyV1) -> str | None:
        if type(key) is not FCISLineageClaimKeyV1:
            raise TypeError("lineage claim lookup key must be exact")
        for claim in self.claims:
            if claim.key is key:
                return claim.value_digest
        return None

    @property
    def root(self) -> str:
        payload = bytearray()
        payload.extend(_u32_be_v1(len(self.claims)))
        for claim in self.claims:
            payload.extend(_frame_v1(claim.key.value.encode("utf-8")))
            payload.extend(_raw32_v1(claim.value_digest))
        return sha256_hex(
            domain_sep_bytes("zenodex/fcis/lineage-closure-claim-set", version=1) + bytes(payload)
        )


@final
@dataclass(frozen=True, slots=True)
class FCISLineageReceiptExtensionV1:
    """Research extension binding one existing receipt to exact fee lineage."""

    acceptance_receipt_root: str
    boundary_root: str
    policy_root: str
    witness_tuple_root: str
    semantic_stream_root: str
    lineage_stream_root: str
    extension_root: str
    _construction_token: InitVar[object]

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _LINEAGE_CONSTRUCTION_TOKEN_V1:
            raise TypeError("lineage receipt extension requires controlled derivation")
        for name in (
            "acceptance_receipt_root",
            "boundary_root",
            "policy_root",
            "witness_tuple_root",
            "semantic_stream_root",
            "lineage_stream_root",
            "extension_root",
        ):
            _require_digest_v1(name, object.__getattribute__(self, name))


@final
@dataclass(frozen=True, slots=True)
class FCISLineageBundleExtensionV1:
    """Research extension binding one base bundle and outbox to lineage receipt."""

    receipt_extension_root: str
    base_bundle_root: str
    outbox_plan_root: str
    bundle_extension_root: str
    outbox_extension_root: str
    _construction_token: InitVar[object]

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _LINEAGE_CONSTRUCTION_TOKEN_V1:
            raise TypeError("lineage bundle extension requires controlled derivation")
        for name in (
            "receipt_extension_root",
            "base_bundle_root",
            "outbox_plan_root",
            "bundle_extension_root",
            "outbox_extension_root",
        ):
            _require_digest_v1(name, object.__getattribute__(self, name))


@final
@dataclass(frozen=True, slots=True)
class FCISLineageClosureCertificateV1:
    """One exact evaluation/receipt/bundle/outbox lineage closure."""

    evaluation: FCISStepEvaluationOkV1
    occurrence_segment: CanonicalFeeOccurrenceSegmentV1
    decision: AcceptV1
    bundle: CommitBundleV1
    receipt_extension: FCISLineageReceiptExtensionV1
    bundle_extension: FCISLineageBundleExtensionV1
    semantic_claims: FCISLineageClaimSetV1
    authority_claims: FCISLineageClaimSetV1
    durability_claims: FCISLineageClaimSetV1
    closed_claims: FCISLineageClaimSetV1
    certificate_root: str
    _construction_token: InitVar[object]

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _LINEAGE_CONSTRUCTION_TOKEN_V1:
            raise TypeError("lineage closure certificate requires controlled derivation")
        if type(self.evaluation) is not FCISStepEvaluationOkV1:
            raise TypeError("lineage certificate evaluation must be exact")
        if type(self.occurrence_segment) is not CanonicalFeeOccurrenceSegmentV1:
            raise TypeError("lineage certificate occurrence segment must be exact")
        if type(self.decision) is not AcceptV1:
            raise TypeError("lineage certificate decision must be exact")
        if type(self.bundle) is not CommitBundleV1:
            raise TypeError("lineage certificate bundle must be exact")
        if type(self.receipt_extension) is not FCISLineageReceiptExtensionV1:
            raise TypeError("lineage receipt extension must be exact")
        if type(self.bundle_extension) is not FCISLineageBundleExtensionV1:
            raise TypeError("lineage bundle extension must be exact")
        for claim_set in (
            self.semantic_claims,
            self.authority_claims,
            self.durability_claims,
            self.closed_claims,
        ):
            if type(claim_set) is not FCISLineageClaimSetV1:
                raise TypeError("lineage certificate claim set must be exact")
            claim_set.__post_init__()
        _require_digest_v1("lineage certificate root", self.certificate_root)
        if self.certificate_root != self.closed_claims.root:
            raise ValueError("lineage certificate root does not match its closed claims")


@final
@dataclass(frozen=True, slots=True)
class FCISLineageClosureRejectV1:
    code: FCISLineageClosureCodeV1
    path: tuple[str, ...]
    _construction_token: InitVar[object]

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _LINEAGE_CONSTRUCTION_TOKEN_V1:
            raise TypeError("lineage closure rejection requires controlled derivation")
        if type(self.code) is not FCISLineageClosureCodeV1:
            raise TypeError("lineage closure rejection code must be exact")
        if type(self.path) is not tuple or any(type(part) is not str for part in self.path):
            raise TypeError("lineage closure rejection path must be an exact string tuple")


FCISLineageClosureResultV1: TypeAlias = FCISLineageClosureCertificateV1 | FCISLineageClosureRejectV1
FCISLineageClaimClosureResultV1: TypeAlias = FCISLineageClaimSetV1 | FCISLineageClosureRejectV1


def _reject_v1(
    code: FCISLineageClosureCodeV1,
    *path: str,
) -> FCISLineageClosureRejectV1:
    return FCISLineageClosureRejectV1(
        code,
        path,
        _construction_token=_LINEAGE_CONSTRUCTION_TOKEN_V1,
    )


def canonicalize_fcis_lineage_claims_v1(
    claims: object,
) -> FCISLineageClaimSetV1:
    """Canonicalize exact claims while rejecting conflicting duplicates."""

    if type(claims) is not tuple:
        raise TypeError("lineage claim source must be an exact tuple")
    values: dict[FCISLineageClaimKeyV1, str] = {}
    for claim_object in cast(tuple[object, ...], claims):
        if type(claim_object) is not FCISLineageClaimV1:
            raise TypeError("lineage claim source item must be exact")
        claim = claim_object
        claim.__post_init__()
        previous = values.get(claim.key)
        if previous is not None and previous != claim.value_digest:
            raise ValueError(f"conflicting lineage claim: {claim.key.value}")
        values[claim.key] = claim.value_digest
    ordered = tuple(
        FCISLineageClaimV1(key, values[key])
        for key in sorted(values, key=lambda item: item.value.encode("utf-8"))
    )
    return FCISLineageClaimSetV1(ordered)


def _claim_set_v1(
    values: tuple[tuple[FCISLineageClaimKeyV1, str], ...],
) -> FCISLineageClaimSetV1:
    return canonicalize_fcis_lineage_claims_v1(
        tuple(FCISLineageClaimV1(key, value) for key, value in values)
    )


def _join_claim_sets_v1(
    left: FCISLineageClaimSetV1,
    right: FCISLineageClaimSetV1,
) -> FCISLineageClaimSetV1:
    if type(left) is not FCISLineageClaimSetV1 or type(right) is not FCISLineageClaimSetV1:
        raise TypeError("lineage join requires exact claim sets")
    left.__post_init__()
    right.__post_init__()
    return canonicalize_fcis_lineage_claims_v1(left.claims + right.claims)


@dataclass(frozen=True, slots=True)
class _LineageRuleV1:
    rule_id: str
    output: FCISLineageClaimKeyV1
    dependencies: tuple[FCISLineageClaimKeyV1, ...]


_LINEAGE_RULES_V1 = tuple(
    sorted(
        (
            _LineageRuleV1(
                "derive-evaluation-certificate",
                FCISLineageClaimKeyV1.EVALUATION_CERTIFICATE_ROOT,
                tuple(
                    sorted(
                        (
                            FCISLineageClaimKeyV1.COMMAND_ROOT,
                            FCISLineageClaimKeyV1.EXECUTION_CONTEXT_HASH,
                            FCISLineageClaimKeyV1.PRE_STATE_ROOT,
                            FCISLineageClaimKeyV1.NEXT_STATE_ROOT,
                            FCISLineageClaimKeyV1.SUPPORT_ROOT,
                            FCISLineageClaimKeyV1.SUPPORT_SET_COMMITMENT,
                            FCISLineageClaimKeyV1.SNAPSHOT_COMMITMENT,
                            FCISLineageClaimKeyV1.PATCH_ROOT,
                            FCISLineageClaimKeyV1.COMMIT_PLAN_ROOT,
                            FCISLineageClaimKeyV1.FEE_BOUNDARY_ROOT,
                            FCISLineageClaimKeyV1.FEE_POLICY_ROOT,
                            FCISLineageClaimKeyV1.FEE_WITNESS_TUPLE_ROOT,
                            FCISLineageClaimKeyV1.FEE_SEMANTIC_STREAM_ROOT,
                            FCISLineageClaimKeyV1.FEE_LINEAGE_STREAM_ROOT,
                        ),
                        key=lambda item: item.value.encode("utf-8"),
                    )
                ),
            ),
            _LineageRuleV1(
                "derive-receipt-certificate",
                FCISLineageClaimKeyV1.RECEIPT_CERTIFICATE_ROOT,
                tuple(
                    sorted(
                        (
                            FCISLineageClaimKeyV1.EVALUATION_CERTIFICATE_ROOT,
                            FCISLineageClaimKeyV1.BUDGET_HASH,
                            FCISLineageClaimKeyV1.ACCEPTANCE_RECEIPT_ROOT,
                        ),
                        key=lambda item: item.value.encode("utf-8"),
                    )
                ),
            ),
            _LineageRuleV1(
                "derive-bundle-certificate",
                FCISLineageClaimKeyV1.BUNDLE_CERTIFICATE_ROOT,
                tuple(
                    sorted(
                        (
                            FCISLineageClaimKeyV1.RECEIPT_CERTIFICATE_ROOT,
                            FCISLineageClaimKeyV1.BASE_BUNDLE_ROOT,
                            FCISLineageClaimKeyV1.OUTBOX_PLAN_ROOT,
                        ),
                        key=lambda item: item.value.encode("utf-8"),
                    )
                ),
            ),
            _LineageRuleV1(
                "derive-outbox-certificate",
                FCISLineageClaimKeyV1.OUTBOX_CERTIFICATE_ROOT,
                tuple(
                    sorted(
                        (
                            FCISLineageClaimKeyV1.BUNDLE_CERTIFICATE_ROOT,
                            FCISLineageClaimKeyV1.OUTBOX_PLAN_ROOT,
                            FCISLineageClaimKeyV1.ACCEPTANCE_RECEIPT_ROOT,
                        ),
                        key=lambda item: item.value.encode("utf-8"),
                    )
                ),
            ),
        ),
        key=lambda rule: rule.output.value.encode("utf-8"),
    )
)


def _derive_rule_value_v1(
    rule: _LineageRuleV1,
    values: dict[FCISLineageClaimKeyV1, str],
) -> str:
    payload = bytearray()
    payload.extend(_frame_v1(FCIS_LINEAGE_CLOSURE_VERSION_V1.encode("utf-8")))
    payload.extend(_frame_v1(rule.rule_id.encode("utf-8")))
    payload.extend(_frame_v1(rule.output.value.encode("utf-8")))
    payload.extend(_u32_be_v1(len(rule.dependencies)))
    for dependency in rule.dependencies:
        payload.extend(_frame_v1(dependency.value.encode("utf-8")))
        payload.extend(_raw32_v1(values[dependency]))
    return sha256_hex(
        domain_sep_bytes("zenodex/fcis/lineage-closure-derived-claim", version=1) + bytes(payload)
    )


def _close_claims_v1(seed: FCISLineageClaimSetV1) -> FCISLineageClaimSetV1:
    if type(seed) is not FCISLineageClaimSetV1:
        raise TypeError("lineage closure seed must be exact")
    seed.__post_init__()
    values = {claim.key: claim.value_digest for claim in seed.claims}
    for _round in range(len(_LINEAGE_RULES_V1) + 1):
        changed = False
        for rule in _LINEAGE_RULES_V1:
            if any(dependency not in values for dependency in rule.dependencies):
                continue
            derived = _derive_rule_value_v1(rule, values)
            current = values.get(rule.output)
            if current is None:
                values[rule.output] = derived
                changed = True
            elif current != derived:
                raise ValueError(f"derived lineage claim conflict: {rule.output.value}")
        if not changed:
            return _claim_set_v1(tuple(values.items()))
    raise RuntimeError("bounded lineage closure did not reach a fixed point")


def close_fcis_lineage_claim_sets_v1(
    claim_sets: object,
) -> FCISLineageClaimClosureResultV1:
    """Join and close an explicit axis order, rejecting every conflict."""

    if type(claim_sets) is not tuple:
        return _reject_v1(FCISLineageClosureCodeV1.WRONG_EXACT_TYPE, "claim_sets")
    result = FCISLineageClaimSetV1(())
    for index, claim_set_object in enumerate(cast(tuple[object, ...], claim_sets)):
        if type(claim_set_object) is not FCISLineageClaimSetV1:
            return _reject_v1(
                FCISLineageClosureCodeV1.WRONG_EXACT_TYPE,
                "claim_sets",
                str(index),
            )
        try:
            result = _close_claims_v1(_join_claim_sets_v1(result, claim_set_object))
        except ValueError as exc:
            code = (
                FCISLineageClosureCodeV1.DERIVED_CLAIM_CONFLICT
                if "derived lineage claim conflict" in str(exc)
                else FCISLineageClosureCodeV1.CLAIM_CONFLICT
            )
            return _reject_v1(code, "claim_sets", str(index), str(exc))
        except (TypeError, ArithmeticError):
            return _reject_v1(
                FCISLineageClosureCodeV1.INTERNAL_RELATION_FAILURE,
                "claim_sets",
                str(index),
            )
    return result


def _segment_claims_v1(
    segment: CanonicalFeeOccurrenceSegmentV1,
) -> tuple[tuple[FCISLineageClaimKeyV1, str], ...]:
    fee_amount_candidates_from_segment_v1(segment)
    return (
        (
            FCISLineageClaimKeyV1.FEE_BOUNDARY_ROOT,
            _segment_digest_v1("fee boundary root", segment.boundary_root),
        ),
        (
            FCISLineageClaimKeyV1.FEE_POLICY_ROOT,
            _segment_digest_v1("fee policy root", segment.policy_root),
        ),
        (
            FCISLineageClaimKeyV1.FEE_WITNESS_TUPLE_ROOT,
            _segment_digest_v1("fee witness tuple root", segment.witness_tuple_root),
        ),
        (
            FCISLineageClaimKeyV1.FEE_SEMANTIC_STREAM_ROOT,
            _segment_digest_v1("fee semantic stream root", segment.semantic_stream_root),
        ),
        (
            FCISLineageClaimKeyV1.FEE_LINEAGE_STREAM_ROOT,
            _segment_digest_v1("fee lineage stream root", segment.lineage_stream_root),
        ),
    )


def _semantic_claims_v1(
    evaluation: FCISStepEvaluationOkV1,
    segment: CanonicalFeeOccurrenceSegmentV1,
) -> FCISLineageClaimSetV1:
    _revalidate_evaluation_v1(evaluation)
    plan = _derive_plan_v1(evaluation)
    _, patch_root = _claim_root_v1(FCIS_DEX_PATCH_SCHEMA_ID_V1, plan.patch)
    _, plan_root = _claim_root_v1(FCIS_COMMIT_PLAN_SCHEMA_ID_V1, plan)
    evidence = evaluation.evidence
    return _claim_set_v1(
        (
            (FCISLineageClaimKeyV1.COMMAND_ROOT, evidence.command_root),
            (
                FCISLineageClaimKeyV1.EXECUTION_CONTEXT_HASH,
                evidence.execution_context_hash,
            ),
            (FCISLineageClaimKeyV1.PRE_STATE_ROOT, evidence.pre_state_root),
            (FCISLineageClaimKeyV1.NEXT_STATE_ROOT, evidence.post_state_root),
            (FCISLineageClaimKeyV1.SUPPORT_ROOT, evidence.support_root),
            (
                FCISLineageClaimKeyV1.SUPPORT_SET_COMMITMENT,
                evidence.support_set_commitment,
            ),
            (
                FCISLineageClaimKeyV1.SNAPSHOT_COMMITMENT,
                evidence.snapshot_commitment,
            ),
            (FCISLineageClaimKeyV1.PATCH_ROOT, patch_root),
            (FCISLineageClaimKeyV1.COMMIT_PLAN_ROOT, plan_root),
            *_segment_claims_v1(segment),
        )
    )


def _authority_claims_v1(
    decision: AcceptV1,
    receipt_extension: FCISLineageReceiptExtensionV1,
) -> FCISLineageClaimSetV1:
    binding = decision.receipt.binding
    return _claim_set_v1(
        (
            (FCISLineageClaimKeyV1.COMMAND_ROOT, binding.command_or_batch_root),
            (
                FCISLineageClaimKeyV1.EXECUTION_CONTEXT_HASH,
                binding.execution_context_hash,
            ),
            (FCISLineageClaimKeyV1.PRE_STATE_ROOT, binding.pre_state_root),
            (FCISLineageClaimKeyV1.NEXT_STATE_ROOT, binding.next_state_root),
            (FCISLineageClaimKeyV1.SUPPORT_ROOT, binding.support_root),
            (
                FCISLineageClaimKeyV1.SUPPORT_SET_COMMITMENT,
                binding.support_set_commitment,
            ),
            (
                FCISLineageClaimKeyV1.SNAPSHOT_COMMITMENT,
                binding.snapshot_commitment,
            ),
            (FCISLineageClaimKeyV1.PATCH_ROOT, binding.patch_root),
            (FCISLineageClaimKeyV1.COMMIT_PLAN_ROOT, binding.commit_plan_root),
            (FCISLineageClaimKeyV1.BUDGET_HASH, binding.budget_hash),
            (
                FCISLineageClaimKeyV1.ACCEPTANCE_RECEIPT_ROOT,
                receipt_extension.acceptance_receipt_root,
            ),
            (
                FCISLineageClaimKeyV1.FEE_BOUNDARY_ROOT,
                receipt_extension.boundary_root,
            ),
            (FCISLineageClaimKeyV1.FEE_POLICY_ROOT, receipt_extension.policy_root),
            (
                FCISLineageClaimKeyV1.FEE_WITNESS_TUPLE_ROOT,
                receipt_extension.witness_tuple_root,
            ),
            (
                FCISLineageClaimKeyV1.FEE_SEMANTIC_STREAM_ROOT,
                receipt_extension.semantic_stream_root,
            ),
            (
                FCISLineageClaimKeyV1.FEE_LINEAGE_STREAM_ROOT,
                receipt_extension.lineage_stream_root,
            ),
            (
                FCISLineageClaimKeyV1.RECEIPT_CERTIFICATE_ROOT,
                receipt_extension.extension_root,
            ),
        )
    )


def _durability_claims_v1(
    bundle: CommitBundleV1,
    receipt_extension: FCISLineageReceiptExtensionV1,
    bundle_extension: FCISLineageBundleExtensionV1,
) -> FCISLineageClaimSetV1:
    binding = bundle.receipt.binding
    return _claim_set_v1(
        (
            (FCISLineageClaimKeyV1.PRE_STATE_ROOT, bundle.expected_pre_root),
            (FCISLineageClaimKeyV1.NEXT_STATE_ROOT, binding.next_state_root),
            (
                FCISLineageClaimKeyV1.ACCEPTANCE_RECEIPT_ROOT,
                bundle.receipt_root,
            ),
            (
                FCISLineageClaimKeyV1.FEE_BOUNDARY_ROOT,
                receipt_extension.boundary_root,
            ),
            (FCISLineageClaimKeyV1.FEE_POLICY_ROOT, receipt_extension.policy_root),
            (
                FCISLineageClaimKeyV1.FEE_WITNESS_TUPLE_ROOT,
                receipt_extension.witness_tuple_root,
            ),
            (
                FCISLineageClaimKeyV1.FEE_SEMANTIC_STREAM_ROOT,
                receipt_extension.semantic_stream_root,
            ),
            (
                FCISLineageClaimKeyV1.FEE_LINEAGE_STREAM_ROOT,
                receipt_extension.lineage_stream_root,
            ),
            (
                FCISLineageClaimKeyV1.RECEIPT_CERTIFICATE_ROOT,
                bundle_extension.receipt_extension_root,
            ),
            (
                FCISLineageClaimKeyV1.OUTBOX_PLAN_ROOT,
                bundle_extension.outbox_plan_root,
            ),
            (
                FCISLineageClaimKeyV1.BASE_BUNDLE_ROOT,
                bundle_extension.base_bundle_root,
            ),
            (
                FCISLineageClaimKeyV1.BUNDLE_CERTIFICATE_ROOT,
                bundle_extension.bundle_extension_root,
            ),
            (
                FCISLineageClaimKeyV1.OUTBOX_CERTIFICATE_ROOT,
                bundle_extension.outbox_extension_root,
            ),
        )
    )


def _validate_axis_order_v1(axis_order: object) -> tuple[FCISLineageAxisV1, ...]:
    if type(axis_order) is not tuple:
        raise TypeError("lineage axis order must be an exact tuple")
    exact = cast(tuple[object, ...], axis_order)
    if any(type(axis) is not FCISLineageAxisV1 for axis in exact):
        raise TypeError("lineage axis order item must be exact")
    typed = cast(tuple[FCISLineageAxisV1, ...], exact)
    if len(typed) != 3 or set(typed) != set(FCIS_LINEAGE_CANONICAL_AXIS_ORDER_V1):
        raise ValueError("lineage axis order must be one permutation of all three axes")
    return typed


def _validate_evaluation_decision_v1(
    evaluation: FCISStepEvaluationOkV1,
    decision: AcceptV1,
    budget: TransitionBudgetV1,
) -> None:
    _revalidate_evaluation_v1(evaluation)
    if type(decision) is not AcceptV1:
        raise TypeError("lineage decision must be an exact acceptance")
    if type(budget) is not TransitionBudgetV1:
        raise TypeError("lineage budget must be exact")
    plan = _derive_plan_v1(evaluation)
    _, patch_root = _claim_root_v1(FCIS_DEX_PATCH_SCHEMA_ID_V1, plan.patch)
    _, plan_root = _claim_root_v1(FCIS_COMMIT_PLAN_SCHEMA_ID_V1, plan)
    _, budget_hash = _claim_root_v1(FCIS_TRANSITION_BUDGET_SCHEMA_ID_V1, budget)
    evidence = evaluation.evidence
    binding = decision.receipt.binding
    if (
        decision.next_state != evaluation.candidate.state
        or decision.commit_plan != plan
        or binding.algorithm_id != evidence.algorithm_id
        or binding.algorithm_version != evidence.algorithm_version
        or binding.execution_context_hash != evidence.execution_context_hash
        or binding.command_or_batch_root != evidence.command_root
        or binding.budget_hash != budget_hash
        or binding.pre_state_root != evidence.pre_state_root
        or binding.next_state_root != evidence.post_state_root
        or binding.support_root_version != evidence.support_root_version
        or binding.support_root != evidence.support_root
        or binding.support_set_commitment != evidence.support_set_commitment
        or binding.snapshot_version != evidence.snapshot_version
        or binding.snapshot_commitment != evidence.snapshot_commitment
        or binding.patch_root != patch_root
        or binding.commit_plan_root != plan_root
    ):
        raise ValueError("evaluation and acceptance receipt do not share one exact lineage")


def _validate_bundle_v1(bundle: CommitBundleV1, decision: AcceptV1) -> tuple[str, str]:
    if type(bundle) is not CommitBundleV1:
        raise TypeError("lineage bundle must be exact")
    if bundle.decision is not decision:
        raise ValueError("bundle must retain the exact acceptance object")
    canonical_bytes, bundle_root = recompute_bundle_root_v1(bundle)
    if canonical_bytes != bundle.canonical_bundle_bytes or bundle_root != bundle.bundle_root:
        raise ValueError("bundle canonical bytes or root failed recomputation")
    recomputed_outbox = recompute_outbox_plan_v1(bundle)
    if recomputed_outbox != bundle.outbox_plan:
        raise ValueError("bundle outbox plan failed recomputation")
    _, outbox_root = _claim_root_v1(FCIS_OUTBOX_PLAN_SCHEMA_ID_V1, bundle.outbox_plan)
    return bundle_root, outbox_root


def _build_extensions_v1(
    semantic_claims: FCISLineageClaimSetV1,
    segment: CanonicalFeeOccurrenceSegmentV1,
    decision: AcceptV1,
    bundle: CommitBundleV1,
) -> tuple[FCISLineageReceiptExtensionV1, FCISLineageBundleExtensionV1]:
    semantic_closed = _close_claims_v1(semantic_claims)
    evaluation_root = semantic_closed.value_for(FCISLineageClaimKeyV1.EVALUATION_CERTIFICATE_ROOT)
    if evaluation_root is None:
        raise ValueError("semantic claims did not derive an evaluation certificate")
    receipt_root = acceptance_receipt_root_v1(decision)
    receipt_seed = _claim_set_v1(
        (
            (
                FCISLineageClaimKeyV1.EVALUATION_CERTIFICATE_ROOT,
                evaluation_root,
            ),
            (FCISLineageClaimKeyV1.BUDGET_HASH, decision.receipt.binding.budget_hash),
            (FCISLineageClaimKeyV1.ACCEPTANCE_RECEIPT_ROOT, receipt_root),
        )
    )
    receipt_closed = _close_claims_v1(receipt_seed)
    receipt_extension_root = receipt_closed.value_for(
        FCISLineageClaimKeyV1.RECEIPT_CERTIFICATE_ROOT
    )
    if receipt_extension_root is None:
        raise ValueError("receipt inputs did not derive a receipt extension")
    segment_values = dict(_segment_claims_v1(segment))
    receipt_extension = FCISLineageReceiptExtensionV1(
        acceptance_receipt_root=receipt_root,
        boundary_root=segment_values[FCISLineageClaimKeyV1.FEE_BOUNDARY_ROOT],
        policy_root=segment_values[FCISLineageClaimKeyV1.FEE_POLICY_ROOT],
        witness_tuple_root=segment_values[FCISLineageClaimKeyV1.FEE_WITNESS_TUPLE_ROOT],
        semantic_stream_root=segment_values[FCISLineageClaimKeyV1.FEE_SEMANTIC_STREAM_ROOT],
        lineage_stream_root=segment_values[FCISLineageClaimKeyV1.FEE_LINEAGE_STREAM_ROOT],
        extension_root=receipt_extension_root,
        _construction_token=_LINEAGE_CONSTRUCTION_TOKEN_V1,
    )
    bundle_root, outbox_root = _validate_bundle_v1(bundle, decision)
    bundle_seed = _claim_set_v1(
        (
            (
                FCISLineageClaimKeyV1.RECEIPT_CERTIFICATE_ROOT,
                receipt_extension_root,
            ),
            (FCISLineageClaimKeyV1.BASE_BUNDLE_ROOT, bundle_root),
            (FCISLineageClaimKeyV1.OUTBOX_PLAN_ROOT, outbox_root),
            (FCISLineageClaimKeyV1.ACCEPTANCE_RECEIPT_ROOT, receipt_root),
        )
    )
    bundle_closed = _close_claims_v1(bundle_seed)
    bundle_extension_root = bundle_closed.value_for(FCISLineageClaimKeyV1.BUNDLE_CERTIFICATE_ROOT)
    outbox_extension_root = bundle_closed.value_for(FCISLineageClaimKeyV1.OUTBOX_CERTIFICATE_ROOT)
    if bundle_extension_root is None or outbox_extension_root is None:
        raise ValueError("bundle inputs did not derive complete durability extensions")
    bundle_extension = FCISLineageBundleExtensionV1(
        receipt_extension_root=receipt_extension_root,
        base_bundle_root=bundle_root,
        outbox_plan_root=outbox_root,
        bundle_extension_root=bundle_extension_root,
        outbox_extension_root=outbox_extension_root,
        _construction_token=_LINEAGE_CONSTRUCTION_TOKEN_V1,
    )
    return receipt_extension, bundle_extension


def _build_fcis_lineage_closure_from_artifacts_v1(
    *,
    evaluation: object,
    occurrence_segment: object,
    decision: object,
    bundle: object,
    budget: object = FCIS_SPOT_TRANSITION_BUDGET_V1,
    axis_order: object = FCIS_LINEAGE_CANONICAL_AXIS_ORDER_V1,
) -> FCISLineageClosureResultV1:
    """Validate and close one exact unmounted artifact lineage."""

    if type(evaluation) is not FCISStepEvaluationOkV1:
        return _reject_v1(FCISLineageClosureCodeV1.WRONG_EXACT_TYPE, "evaluation")
    if type(occurrence_segment) is not CanonicalFeeOccurrenceSegmentV1:
        return _reject_v1(
            FCISLineageClosureCodeV1.WRONG_EXACT_TYPE,
            "occurrence_segment",
        )
    if type(decision) is not AcceptV1:
        return _reject_v1(FCISLineageClosureCodeV1.WRONG_EXACT_TYPE, "decision")
    if type(bundle) is not CommitBundleV1:
        return _reject_v1(FCISLineageClosureCodeV1.WRONG_EXACT_TYPE, "bundle")
    if type(budget) is not TransitionBudgetV1:
        return _reject_v1(FCISLineageClosureCodeV1.WRONG_EXACT_TYPE, "budget")
    try:
        exact_axis_order = _validate_axis_order_v1(axis_order)
    except (TypeError, ValueError):
        return _reject_v1(FCISLineageClosureCodeV1.INVALID_AXIS_ORDER, "axis_order")
    try:
        fee_amount_candidates_from_segment_v1(occurrence_segment)
    except (TypeError, ValueError, ArithmeticError):
        return _reject_v1(
            FCISLineageClosureCodeV1.INVALID_OCCURRENCE_SEGMENT,
            "occurrence_segment",
        )
    try:
        _validate_evaluation_decision_v1(evaluation, decision, budget)
        semantic_claims = _semantic_claims_v1(evaluation, occurrence_segment)
        receipt_extension, bundle_extension = _build_extensions_v1(
            semantic_claims,
            occurrence_segment,
            decision,
            bundle,
        )
        authority_claims = _authority_claims_v1(decision, receipt_extension)
        durability_claims = _durability_claims_v1(
            bundle,
            receipt_extension,
            bundle_extension,
        )
    except (TypeError, ValueError, ArithmeticError):
        return _reject_v1(
            FCISLineageClosureCodeV1.LINEAGE_MISMATCH,
            "artifacts",
        )
    claims_by_axis = {
        FCISLineageAxisV1.SEMANTIC: semantic_claims,
        FCISLineageAxisV1.AUTHORITY: authority_claims,
        FCISLineageAxisV1.DURABILITY: durability_claims,
    }
    closed = close_fcis_lineage_claim_sets_v1(
        tuple(claims_by_axis[axis] for axis in exact_axis_order)
    )
    if type(closed) is FCISLineageClosureRejectV1:
        return closed
    expected_receipt = closed.value_for(FCISLineageClaimKeyV1.RECEIPT_CERTIFICATE_ROOT)
    expected_bundle = closed.value_for(FCISLineageClaimKeyV1.BUNDLE_CERTIFICATE_ROOT)
    expected_outbox = closed.value_for(FCISLineageClaimKeyV1.OUTBOX_CERTIFICATE_ROOT)
    if (
        expected_receipt != receipt_extension.extension_root
        or expected_bundle != bundle_extension.bundle_extension_root
        or expected_outbox != bundle_extension.outbox_extension_root
    ):
        return _reject_v1(
            FCISLineageClosureCodeV1.DERIVED_CLAIM_CONFLICT,
            "extensions",
        )
    try:
        return FCISLineageClosureCertificateV1(
            evaluation=evaluation,
            occurrence_segment=occurrence_segment,
            decision=decision,
            bundle=bundle,
            receipt_extension=receipt_extension,
            bundle_extension=bundle_extension,
            semantic_claims=semantic_claims,
            authority_claims=authority_claims,
            durability_claims=durability_claims,
            closed_claims=closed,
            certificate_root=closed.root,
            _construction_token=_LINEAGE_CONSTRUCTION_TOKEN_V1,
        )
    except (TypeError, ValueError, ArithmeticError):
        return _reject_v1(
            FCISLineageClosureCodeV1.INTERNAL_RELATION_FAILURE,
            "certificate",
        )


def _derive_fcis_lineage_closure_from_segment_v1(
    *,
    state_source: object,
    settlement: object,
    intents: object,
    context: object,
    budget: object,
    occurrence_segment: object,
    axis_order: object = FCIS_LINEAGE_CANONICAL_AXIS_ORDER_V1,
) -> FCISLineageClosureResultV1:
    """Evaluate, decide, bundle, and close one research-only lineage certificate."""

    evaluation = evaluate_fcis_step_candidate_v1(
        state_source=state_source,
        settlement=settlement,
        intents=intents,
        context=context,
    )
    if type(evaluation) is FCISStepEvaluationRejectV1:
        return _reject_v1(
            FCISLineageClosureCodeV1.EVALUATION_REJECTED,
            evaluation.phase.value,
            evaluation.code,
        )
    if type(evaluation) is not FCISStepEvaluationOkV1:
        return _reject_v1(
            FCISLineageClosureCodeV1.INTERNAL_RELATION_FAILURE,
            "evaluation",
        )
    decision = evaluate_fcis_decision_v1(
        state_source=state_source,
        settlement=settlement,
        intents=intents,
        context=context,
        budget=budget,
    )
    if type(decision) is RejectV1:
        return _reject_v1(
            FCISLineageClosureCodeV1.DECISION_REJECTED,
            "decision",
        )
    if type(decision) is not AcceptV1:
        return _reject_v1(
            FCISLineageClosureCodeV1.DECISION_REJECTED,
            "unsupported_variant",
        )
    bundle = build_commit_bundle_v1(decision)
    if type(bundle) is RejectV1:
        return _reject_v1(
            FCISLineageClosureCodeV1.BUNDLE_REJECTED,
            "bundle",
        )
    if type(bundle) is not CommitBundleV1:
        return _reject_v1(
            FCISLineageClosureCodeV1.INTERNAL_RELATION_FAILURE,
            "bundle",
        )
    return _build_fcis_lineage_closure_from_artifacts_v1(
        evaluation=evaluation,
        occurrence_segment=occurrence_segment,
        decision=decision,
        bundle=bundle,
        budget=budget,
        axis_order=axis_order,
    )


__all__ = (
    "FCISLineageAxisV1",
    "FCISLineageBundleExtensionV1",
    "FCISLineageClaimKeyV1",
    "FCISLineageClaimSetV1",
    "FCISLineageClaimV1",
    "FCISLineageClosureCertificateV1",
    "FCISLineageClosureCodeV1",
    "FCISLineageClosureRejectV1",
    "FCISLineageClosureResultV1",
    "FCISLineageReceiptExtensionV1",
    "FCIS_LINEAGE_CANONICAL_AXIS_ORDER_V1",
    "canonicalize_fcis_lineage_claims_v1",
    "close_fcis_lineage_claim_sets_v1",
)
