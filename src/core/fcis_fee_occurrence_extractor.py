"""Pure source-bound extraction of one transition-local fee occurrence segment.

This unmounted research module removes caller-selected SLNF boundary, policy,
and witness roots. It replays an exact ``FCISStepEvaluationOkV1`` from its
retained committed pre-state, settlement, intents, and context, derives one
canonical direct-swap protocol-fee witness tuple, and then invokes the existing
Segmented Lineage Normal Form normalizer.

The resulting roots are bound to the retained evaluation. They are not yet
proof that the shell authenticated the command, current store head, context,
fee policy, deployment, or configuration. Route protocol-fee extraction remains
fail-closed because the current route fill does not retain per-leg protocol-fee
amounts and assets.
"""

from __future__ import annotations

from dataclasses import InitVar, dataclass
from enum import Enum
from hashlib import sha256
from typing import TypeAlias, cast, final

from ..state.intent_snapshots import owned_intent_field_v1, owned_intent_kind_text_v1
from ..state.intents import IntentKind
from .fcis_decision_derivation import _revalidate_evaluation_v1
from .fcis_fee_apportionment_values import (
    MAX_FEE_AMOUNT_V2,
    SRGD_ALGORITHM_VERSION_V1,
    FeeApportionmentKeyV2,
)
from .fcis_fee_occurrence_normal_form import (
    FEE_OCCURRENCE_ROLE_ORDER_V1,
    CanonicalFeeOccurrenceSegmentV1,
    FeeOccurrenceNormalizationRejectV1,
    FeeWitnessOccurrenceClaimV1,
    canonicalize_fee_occurrence_segment_v1,
    fee_amount_candidates_from_segment_v1,
)
from .fcis_settlement_index import (
    ExactSettlementIndexRejectV1,
    ExactSettlementIndexV1,
    derive_exact_settlement_index_admitted_v1,
)
from .fcis_step_evaluation_values import FCISStepEvaluationOkV1
from .fcis_step_evaluator import evaluate_fcis_step_candidate_v1
from .settlement_schema import fill_action_text_v1
from .settlement_snapshots import OwnedFillV1

SOURCE_BOUND_FEE_OCCURRENCE_VERSION_V1 = "zenodex/fcis/fee-occurrence/source-bound-extractor/v1"
PROTOCOL_FEE_DISTRIBUTION_DOMAIN_ID_V1 = "protocol-fees"

_SOURCE_BOUND_FEE_OCCURRENCE_TOKEN_V1 = object()
_DIRECT_SWAP_KINDS_V1 = (
    IntentKind.SWAP_EXACT_IN.value,
    IntentKind.SWAP_EXACT_OUT.value,
)
_ROUTE_KINDS_V1 = (
    IntentKind.ROUTE_EXACT_IN.value,
    IntentKind.ROUTE_EXACT_OUT.value,
)


class SourceBoundFeeOccurrenceCodeV1(Enum):
    WRONG_EXACT_TYPE = "wrong_exact_type"
    EVALUATION_LINEAGE_MISMATCH = "evaluation_lineage_mismatch"
    SETTLEMENT_INDEX_REJECTED = "settlement_index_rejected"
    MISSING_FEE_DISTRIBUTION_POLICY = "missing_fee_distribution_policy"
    MISSING_PROTOCOL_FEE_WITNESS = "missing_protocol_fee_witness"
    ROUTE_FEE_PROVENANCE_GAP = "route_fee_provenance_gap"
    INVALID_SOURCE_WITNESS = "invalid_source_witness"
    NORMALIZATION_REJECTED = "normalization_rejected"
    INTERNAL_RELATION_FAILURE = "internal_relation_failure"


@final
@dataclass(frozen=True, slots=True)
class SourceBoundFeeOccurrenceRejectV1:
    """Stable extraction failure with no candidate or publication authority."""

    code: SourceBoundFeeOccurrenceCodeV1
    path: tuple[str, ...]
    _construction_token: InitVar[object]

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _SOURCE_BOUND_FEE_OCCURRENCE_TOKEN_V1:
            raise TypeError("source-bound fee rejection requires controlled derivation")
        if type(self.code) is not SourceBoundFeeOccurrenceCodeV1:
            raise TypeError("source-bound fee rejection code must be exact")
        if type(self.path) is not tuple or any(type(part) is not str for part in self.path):
            raise TypeError("source-bound fee rejection path must be an exact string tuple")


@final
@dataclass(frozen=True, slots=True)
class SourceBoundFeeOccurrenceV1:
    """One replay-derived SLNF segment retaining the exact source evaluation."""

    evaluation: FCISStepEvaluationOkV1
    settlement_index: ExactSettlementIndexV1
    boundary_root: str
    policy_root: str
    segment: CanonicalFeeOccurrenceSegmentV1
    _construction_token: InitVar[object]

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _SOURCE_BOUND_FEE_OCCURRENCE_TOKEN_V1:
            raise TypeError("source-bound fee occurrence requires controlled derivation")
        if type(self.evaluation) is not FCISStepEvaluationOkV1:
            raise TypeError("source-bound fee evaluation must be exact")
        if type(self.settlement_index) is not ExactSettlementIndexV1:
            raise TypeError("source-bound fee settlement index must be exact")
        if not _plain_digest_is_canonical_v1(self.boundary_root):
            raise TypeError("source-bound fee boundary root must be canonical")
        if not _plain_digest_is_canonical_v1(self.policy_root):
            raise TypeError("source-bound fee policy root must be canonical")
        if type(self.segment) is not CanonicalFeeOccurrenceSegmentV1:
            raise TypeError("source-bound fee segment must be exact")
        fee_amount_candidates_from_segment_v1(self.segment)
        if self.segment.boundary_root != self.boundary_root:
            raise ValueError("source-bound fee boundary root drift")
        if self.segment.policy_root != self.policy_root:
            raise ValueError("source-bound fee policy root drift")


SourceBoundFeeOccurrenceResultV1: TypeAlias = (
    SourceBoundFeeOccurrenceV1 | SourceBoundFeeOccurrenceRejectV1
)


def _reject_v1(
    code: SourceBoundFeeOccurrenceCodeV1,
    *path: str,
) -> SourceBoundFeeOccurrenceRejectV1:
    return SourceBoundFeeOccurrenceRejectV1(
        code=code,
        path=path,
        _construction_token=_SOURCE_BOUND_FEE_OCCURRENCE_TOKEN_V1,
    )


def _plain_digest_is_canonical_v1(value: object) -> bool:
    return (
        type(value) is str
        and len(value) == 64
        and value == value.lower()
        and all(character in "0123456789abcdef" for character in value)
    )


def _require_0x_digest_bytes_v1(name: str, value: object) -> bytes:
    if (
        type(value) is not str
        or len(value) != 66
        or not value.startswith("0x")
        or value != value.lower()
        or any(character not in "0123456789abcdef" for character in value[2:])
    ):
        raise ValueError(f"{name} must be a canonical lowercase 0x digest")
    return bytes.fromhex(value[2:])


def _require_plain_digest_bytes_v1(name: str, value: object) -> bytes:
    if not _plain_digest_is_canonical_v1(value):
        raise ValueError(f"{name} must be a canonical lowercase digest")
    return bytes.fromhex(cast(str, value))


def _u32_v1(value: int) -> bytes:
    if type(value) is not int or not 0 <= value < 1 << 32:
        raise ValueError("source-bound fee frame integer must fit U32")
    return value.to_bytes(4, "big")


def _u256_v1(value: int) -> bytes:
    if type(value) is not int or not 0 <= value <= MAX_FEE_AMOUNT_V2:
        raise ValueError("source-bound fee amount must fit U256")
    return value.to_bytes(32, "big")


def _frame_v1(value: bytes) -> bytes:
    return len(value).to_bytes(8, "big") + value


def _text_v1(value: str) -> bytes:
    if type(value) is not str:
        raise TypeError("source-bound fee text must be exact")
    return value.encode("utf-8")


def _optional_text_v1(value: str | None) -> bytes:
    if value is None:
        return b"\x00"
    return b"\x01" + _frame_v1(_text_v1(value))


def _optional_u256_v1(value: int | None) -> bytes:
    if value is None:
        return b"\x00"
    return b"\x01" + _u256_v1(value)


def _hash_frames_v1(domain: str, *fields: bytes) -> str:
    digest = sha256()
    domain_bytes = domain.encode("ascii")
    digest.update(len(domain_bytes).to_bytes(4, "big"))
    digest.update(domain_bytes)
    digest.update(len(fields).to_bytes(4, "big"))
    for field in fields:
        digest.update(_frame_v1(field))
    return digest.hexdigest()


def _boundary_root_v1(evaluation: FCISStepEvaluationOkV1) -> str:
    evidence = evaluation.evidence
    return _hash_frames_v1(
        "zenodex/fcis/fee-occurrence/source-boundary/v1",
        _text_v1(SOURCE_BOUND_FEE_OCCURRENCE_VERSION_V1),
        _text_v1(evidence.algorithm_id),
        _u32_v1(evidence.algorithm_version),
        _require_0x_digest_bytes_v1("command root", evidence.command_root),
        _require_0x_digest_bytes_v1("execution context hash", evidence.execution_context_hash),
        _require_0x_digest_bytes_v1("pre-state root", evidence.pre_state_root),
        _require_0x_digest_bytes_v1("post-state root", evidence.post_state_root),
        _require_0x_digest_bytes_v1("support root", evidence.support_root),
        _require_0x_digest_bytes_v1("support-set commitment", evidence.support_set_commitment),
        _require_0x_digest_bytes_v1("snapshot commitment", evidence.snapshot_commitment),
    )


def _policy_root_v1(evaluation: FCISStepEvaluationOkV1) -> str:
    context = evaluation.material.context
    policy = context.fee_split_policy
    if policy is None:
        raise ValueError("source-bound extraction requires a fee distribution policy")
    context.__post_init__()
    context.settlement.__post_init__()
    policy.__post_init__()
    return _hash_frames_v1(
        "zenodex/fcis/fee-occurrence/source-policy/v1",
        _text_v1(SOURCE_BOUND_FEE_OCCURRENCE_VERSION_V1),
        _text_v1(SRGD_ALGORITHM_VERSION_V1),
        _text_v1(PROTOCOL_FEE_DISTRIBUTION_DOMAIN_ID_V1),
        *(_text_v1(role) for role in FEE_OCCURRENCE_ROLE_ORDER_V1),
        _u32_v1(policy.buyback_bps),
        _u32_v1(policy.treasury_bps),
        _u32_v1(policy.rewards_bps),
        _u32_v1(context.settlement.protocol_fee_share_bps),
        _optional_text_v1(context.settlement.protocol_fee_recipient_pubkey),
    )


def _validated_optional_amount_v1(name: str, value: object) -> int | None:
    if value is None:
        return None
    if type(value) is not int or not 0 <= value <= MAX_FEE_AMOUNT_V2:
        raise ValueError(f"{name} must be None or an exact U256 value")
    return value


def _source_witness_root_v1(
    *,
    evaluation: FCISStepEvaluationOkV1,
    boundary_root: str,
    policy_root: str,
    settlement_position: int,
    witness_position: int,
    intent_id: str,
    intent_kind: str,
    pool_id: str,
    asset_in: str,
    asset_out: str,
    amount: int,
    fill: OwnedFillV1,
) -> str:
    evidence = evaluation.evidence
    return _hash_frames_v1(
        "zenodex/fcis/fee-occurrence/source-witness/v1",
        _text_v1(SOURCE_BOUND_FEE_OCCURRENCE_VERSION_V1),
        _require_plain_digest_bytes_v1("boundary root", boundary_root),
        _require_plain_digest_bytes_v1("policy root", policy_root),
        _require_0x_digest_bytes_v1("command root", evidence.command_root),
        _require_0x_digest_bytes_v1("execution context hash", evidence.execution_context_hash),
        _require_0x_digest_bytes_v1("pre-state root", evidence.pre_state_root),
        _require_0x_digest_bytes_v1("post-state root", evidence.post_state_root),
        _u32_v1(settlement_position),
        _u32_v1(witness_position),
        _text_v1(intent_id),
        _text_v1(intent_kind),
        _text_v1(pool_id),
        _text_v1(asset_in),
        _text_v1(asset_out),
        _u256_v1(amount),
        _optional_text_v1(fill.reason),
        _optional_u256_v1(
            _validated_optional_amount_v1("fill.amount_in_filled", fill.amount_in_filled)
        ),
        _optional_u256_v1(
            _validated_optional_amount_v1("fill.amount_out_filled", fill.amount_out_filled)
        ),
        _optional_u256_v1(_validated_optional_amount_v1("fill.fee_paid", fill.fee_paid)),
        _optional_u256_v1(
            _validated_optional_amount_v1("fill.protocol_fee_paid", fill.protocol_fee_paid)
        ),
        _optional_u256_v1(
            _validated_optional_amount_v1("fill.reserve_in_before", fill.reserve_in_before)
        ),
        _optional_u256_v1(
            _validated_optional_amount_v1("fill.reserve_out_before", fill.reserve_out_before)
        ),
    )


def _replay_matches_v1(evaluation: FCISStepEvaluationOkV1) -> bool:
    material = evaluation.material
    replay = evaluate_fcis_step_candidate_v1(
        state_source=material.pre_state,
        settlement=material.settlement,
        intents=material.intents,
        context=material.context,
    )
    return type(replay) is FCISStepEvaluationOkV1 and replay == evaluation


def extract_source_bound_fee_occurrence_v1(
    evaluation: object,
) -> SourceBoundFeeOccurrenceResultV1:
    """Replay one exact evaluation and derive its direct-swap fee witness segment."""

    if type(evaluation) is not FCISStepEvaluationOkV1:
        return _reject_v1(SourceBoundFeeOccurrenceCodeV1.WRONG_EXACT_TYPE, "evaluation")
    exact_evaluation = evaluation
    try:
        _revalidate_evaluation_v1(exact_evaluation)
        if not _replay_matches_v1(exact_evaluation):
            return _reject_v1(
                SourceBoundFeeOccurrenceCodeV1.EVALUATION_LINEAGE_MISMATCH,
                "evaluation",
                "replay",
            )
    except (AttributeError, TypeError, ValueError, ArithmeticError):
        return _reject_v1(
            SourceBoundFeeOccurrenceCodeV1.EVALUATION_LINEAGE_MISMATCH,
            "evaluation",
        )

    material = exact_evaluation.material
    index_result = derive_exact_settlement_index_admitted_v1(
        material.settlement,
        material.intents,
        allow_cow_netting=material.context.settlement.allow_cow_netting,
    )
    if type(index_result) is ExactSettlementIndexRejectV1:
        return _reject_v1(
            SourceBoundFeeOccurrenceCodeV1.SETTLEMENT_INDEX_REJECTED,
            "settlement_index",
            index_result.reason,
        )
    if type(index_result) is not ExactSettlementIndexV1:
        return _reject_v1(
            SourceBoundFeeOccurrenceCodeV1.INTERNAL_RELATION_FAILURE,
            "settlement_index",
        )
    settlement_index = index_result

    if material.context.fee_split_policy is None:
        return _reject_v1(
            SourceBoundFeeOccurrenceCodeV1.MISSING_FEE_DISTRIBUTION_POLICY,
            "context",
            "fee_split_policy",
        )
    try:
        boundary_root = _boundary_root_v1(exact_evaluation)
        policy_root = _policy_root_v1(exact_evaluation)
    except (AttributeError, TypeError, ValueError, ArithmeticError):
        return _reject_v1(
            SourceBoundFeeOccurrenceCodeV1.INTERNAL_RELATION_FAILURE,
            "roots",
        )

    witnesses: list[FeeWitnessOccurrenceClaimV1] = []
    protocol_share = material.context.settlement.protocol_fee_share_bps
    for settlement_position, entry in enumerate(settlement_index.entries):
        try:
            if fill_action_text_v1(entry.action) != "FILL":
                continue
            intent_kind = owned_intent_kind_text_v1(entry.intent)
        except (AttributeError, TypeError, ValueError, ArithmeticError):
            return _reject_v1(
                SourceBoundFeeOccurrenceCodeV1.INVALID_SOURCE_WITNESS,
                "settlement_index",
                str(settlement_position),
            )

        if intent_kind in _ROUTE_KINDS_V1:
            if protocol_share > 0:
                return _reject_v1(
                    SourceBoundFeeOccurrenceCodeV1.ROUTE_FEE_PROVENANCE_GAP,
                    "settlement_index",
                    str(settlement_position),
                    "route",
                )
            continue
        if intent_kind not in _DIRECT_SWAP_KINDS_V1:
            fill = entry.fill
            if (
                type(fill) is OwnedFillV1
                and fill.protocol_fee_paid is not None
                and fill.protocol_fee_paid != 0
            ):
                return _reject_v1(
                    SourceBoundFeeOccurrenceCodeV1.INVALID_SOURCE_WITNESS,
                    "settlement_index",
                    str(settlement_position),
                    "unexpected_protocol_fee",
                )
            continue

        fill = entry.fill
        if type(fill) is not OwnedFillV1:
            return _reject_v1(
                SourceBoundFeeOccurrenceCodeV1.MISSING_PROTOCOL_FEE_WITNESS,
                "settlement_index",
                str(settlement_position),
                "fill",
            )
        protocol_fee = fill.protocol_fee_paid
        if protocol_fee is None:
            if protocol_share > 0:
                return _reject_v1(
                    SourceBoundFeeOccurrenceCodeV1.MISSING_PROTOCOL_FEE_WITNESS,
                    "settlement_index",
                    str(settlement_position),
                    "protocol_fee_paid",
                )
            protocol_fee = 0
        if type(protocol_fee) is not int or not 0 <= protocol_fee <= MAX_FEE_AMOUNT_V2:
            return _reject_v1(
                SourceBoundFeeOccurrenceCodeV1.INVALID_SOURCE_WITNESS,
                "settlement_index",
                str(settlement_position),
                "protocol_fee_paid",
            )

        try:
            pool_id = owned_intent_field_v1(entry.intent, "pool_id")
            asset_in = owned_intent_field_v1(entry.intent, "asset_in")
            asset_out = owned_intent_field_v1(entry.intent, "asset_out")
            if type(pool_id) is not str or not pool_id:
                raise ValueError("direct swap pool identifier is invalid")
            if type(asset_in) is not str or not asset_in:
                raise ValueError("direct swap input asset is invalid")
            if type(asset_out) is not str or not asset_out:
                raise ValueError("direct swap output asset is invalid")
            key = FeeApportionmentKeyV2(
                PROTOCOL_FEE_DISTRIBUTION_DOMAIN_ID_V1,
                asset_in,
            )
            witness_position = len(witnesses)
            source_root = _source_witness_root_v1(
                evaluation=exact_evaluation,
                boundary_root=boundary_root,
                policy_root=policy_root,
                settlement_position=settlement_position,
                witness_position=witness_position,
                intent_id=entry.intent_id,
                intent_kind=intent_kind,
                pool_id=pool_id,
                asset_in=asset_in,
                asset_out=asset_out,
                amount=protocol_fee,
                fill=fill,
            )
            witnesses.append(
                FeeWitnessOccurrenceClaimV1(
                    position=witness_position,
                    key=key,
                    amount=protocol_fee,
                    source_witness_root=source_root,
                )
            )
        except (AttributeError, TypeError, ValueError, ArithmeticError):
            return _reject_v1(
                SourceBoundFeeOccurrenceCodeV1.INVALID_SOURCE_WITNESS,
                "settlement_index",
                str(settlement_position),
            )

    segment_result = canonicalize_fee_occurrence_segment_v1(
        boundary_root=boundary_root,
        policy_root=policy_root,
        witnesses=tuple(witnesses),
    )
    if type(segment_result) is FeeOccurrenceNormalizationRejectV1:
        return _reject_v1(
            SourceBoundFeeOccurrenceCodeV1.NORMALIZATION_REJECTED,
            segment_result.code.value,
            *segment_result.path,
        )
    if type(segment_result) is not CanonicalFeeOccurrenceSegmentV1:
        return _reject_v1(
            SourceBoundFeeOccurrenceCodeV1.INTERNAL_RELATION_FAILURE,
            "segment",
        )
    segment = segment_result
    try:
        return SourceBoundFeeOccurrenceV1(
            evaluation=exact_evaluation,
            settlement_index=settlement_index,
            boundary_root=boundary_root,
            policy_root=policy_root,
            segment=segment,
            _construction_token=_SOURCE_BOUND_FEE_OCCURRENCE_TOKEN_V1,
        )
    except (AttributeError, TypeError, ValueError, ArithmeticError):
        return _reject_v1(
            SourceBoundFeeOccurrenceCodeV1.INTERNAL_RELATION_FAILURE,
            "result",
        )


__all__ = (
    "PROTOCOL_FEE_DISTRIBUTION_DOMAIN_ID_V1",
    "SOURCE_BOUND_FEE_OCCURRENCE_VERSION_V1",
    "SourceBoundFeeOccurrenceCodeV1",
    "SourceBoundFeeOccurrenceRejectV1",
    "SourceBoundFeeOccurrenceResultV1",
    "SourceBoundFeeOccurrenceV1",
    "extract_source_bound_fee_occurrence_v1",
)
