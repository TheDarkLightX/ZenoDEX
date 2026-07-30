"""Pure pre-evaluation extraction of one transition-local fee segment.

This unmounted research module removes caller-selected SLNF boundary, policy,
and witness roots. It first performs the evaluator's exact command, context,
state, and pre-state-binding admissions, but it does not run the nonce, spot,
fee, or successor transition. It then derives the exact direct-swap
protocol-fee witness tuple from the admitted settlement and invokes the existing
Segmented Lineage Normal Form normalizer.

The resulting occurrence evidence is therefore upstream of the candidate and
post-state. It cannot form a hash cycle when a later evaluator consumes the
segment. Exact Python admission is still not proof that the shell authenticated
the command, selected the datastore-current state, or pinned the deployment and
configuration. Route protocol-fee extraction remains fail-closed because the
current route fill does not retain per-leg protocol-fee amounts and assets.
"""

from __future__ import annotations

from dataclasses import InitVar, dataclass
from enum import Enum
from hashlib import sha256
from typing import TypeAlias, cast, final

from ..state.canonical import sha256_hex
from ..state.intent_snapshots import owned_intent_field_v1, owned_intent_kind_text_v1
from ..state.intents import IntentKind
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
from .fcis_step_evaluation_values import (
    FCISEvaluatedMaterialV1,
    FCISStepEvaluationRejectV1,
)
from .fcis_step_evaluator import (
    _admit_context_v1,
    _admit_exact_command_v1,
    _admit_exact_state_v1,
    _pre_state_binding_v1,
)
from .fcis_support_profile_v5 import _command_preimage_v5
from .settlement_schema import fill_action_text_v1
from .settlement_snapshots import OwnedFillV1

SOURCE_BOUND_FEE_OCCURRENCE_VERSION_V1 = "zenodex/fcis/fee-occurrence/source-bound-extractor/v2"
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
    SOURCE_ADMISSION_REJECTED = "source_admission_rejected"
    SOURCE_BINDING_REJECTED = "source_binding_rejected"
    SETTLEMENT_INDEX_REJECTED = "settlement_index_rejected"
    MISSING_FEE_DISTRIBUTION_POLICY = "missing_fee_distribution_policy"
    MISSING_PROTOCOL_FEE_WITNESS = "missing_protocol_fee_witness"
    ROUTE_FEE_PROVENANCE_GAP = "route_fee_provenance_gap"
    INVALID_SOURCE_WITNESS = "invalid_source_witness"
    NORMALIZATION_REJECTED = "normalization_rejected"
    SOURCE_REDERIVATION_MISMATCH = "source_rederivation_mismatch"
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
    """One admitted pre-evaluation material and its exact SLNF segment."""

    material: FCISEvaluatedMaterialV1
    command_root: str
    execution_context_hash: str
    pre_state_root: str
    settlement_index: ExactSettlementIndexV1
    boundary_root: str
    policy_root: str
    segment: CanonicalFeeOccurrenceSegmentV1
    _construction_token: InitVar[object]

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _SOURCE_BOUND_FEE_OCCURRENCE_TOKEN_V1:
            raise TypeError("source-bound fee occurrence requires controlled derivation")
        if type(self.material) is not FCISEvaluatedMaterialV1:
            raise TypeError("source-bound fee material must be exact")
        self.material.__post_init__()
        for name, value in (
            ("command_root", self.command_root),
            ("execution_context_hash", self.execution_context_hash),
            ("pre_state_root", self.pre_state_root),
        ):
            if not _0x_digest_is_canonical_v1(value):
                raise TypeError(f"source-bound fee {name} must be canonical")
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


def _path_text_v1(path: tuple[str | int, ...]) -> tuple[str, ...]:
    return tuple(str(part) for part in path)


def _source_reject_v1(reject: FCISStepEvaluationRejectV1) -> SourceBoundFeeOccurrenceRejectV1:
    return _reject_v1(
        SourceBoundFeeOccurrenceCodeV1.SOURCE_ADMISSION_REJECTED,
        reject.phase.value,
        reject.code,
        *_path_text_v1(reject.path),
    )


def _plain_digest_is_canonical_v1(value: object) -> bool:
    return (
        type(value) is str
        and len(value) == 64
        and value == value.lower()
        and all(character in "0123456789abcdef" for character in value)
    )


def _0x_digest_is_canonical_v1(value: object) -> bool:
    return (
        type(value) is str
        and len(value) == 66
        and value.startswith("0x")
        and value == value.lower()
        and all(character in "0123456789abcdef" for character in value[2:])
    )


def _require_0x_digest_bytes_v1(name: str, value: object) -> bytes:
    if not _0x_digest_is_canonical_v1(value):
        raise ValueError(f"{name} must be a canonical lowercase 0x digest")
    return bytes.fromhex(cast(str, value)[2:])


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


def _boundary_root_v1(
    command_root: str,
    execution_context_hash: str,
    pre_state_root: str,
) -> str:
    return _hash_frames_v1(
        "zenodex/fcis/fee-occurrence/source-boundary/v2",
        _text_v1(SOURCE_BOUND_FEE_OCCURRENCE_VERSION_V1),
        _require_0x_digest_bytes_v1("command root", command_root),
        _require_0x_digest_bytes_v1(
            "execution context hash",
            execution_context_hash,
        ),
        _require_0x_digest_bytes_v1("pre-state root", pre_state_root),
    )


def _policy_root_v1(material: FCISEvaluatedMaterialV1) -> str:
    context = material.context
    policy = context.fee_split_policy
    if policy is None:
        raise ValueError("source-bound extraction requires a fee distribution policy")
    context.__post_init__()
    context.settlement.__post_init__()
    policy.__post_init__()
    return _hash_frames_v1(
        "zenodex/fcis/fee-occurrence/source-policy/v2",
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
    command_root: str,
    execution_context_hash: str,
    pre_state_root: str,
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
    return _hash_frames_v1(
        "zenodex/fcis/fee-occurrence/source-witness/v2",
        _text_v1(SOURCE_BOUND_FEE_OCCURRENCE_VERSION_V1),
        _require_plain_digest_bytes_v1("boundary root", boundary_root),
        _require_plain_digest_bytes_v1("policy root", policy_root),
        _require_0x_digest_bytes_v1("command root", command_root),
        _require_0x_digest_bytes_v1(
            "execution context hash",
            execution_context_hash,
        ),
        _require_0x_digest_bytes_v1("pre-state root", pre_state_root),
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
            _validated_optional_amount_v1(
                "fill.amount_in_filled",
                fill.amount_in_filled,
            )
        ),
        _optional_u256_v1(
            _validated_optional_amount_v1(
                "fill.amount_out_filled",
                fill.amount_out_filled,
            )
        ),
        _optional_u256_v1(
            _validated_optional_amount_v1(
                "fill.fee_paid",
                fill.fee_paid,
            )
        ),
        _optional_u256_v1(
            _validated_optional_amount_v1(
                "fill.protocol_fee_paid",
                fill.protocol_fee_paid,
            )
        ),
        _optional_u256_v1(
            _validated_optional_amount_v1(
                "fill.reserve_in_before",
                fill.reserve_in_before,
            )
        ),
        _optional_u256_v1(
            _validated_optional_amount_v1(
                "fill.reserve_out_before",
                fill.reserve_out_before,
            )
        ),
    )


def _admit_material_v1(
    *,
    state_source: object,
    settlement: object,
    intents: object,
    context: object,
) -> (
    tuple[FCISEvaluatedMaterialV1, str, str, str]
    | SourceBoundFeeOccurrenceRejectV1
):
    command = _admit_exact_command_v1(settlement, intents)
    if type(command) is FCISStepEvaluationRejectV1:
        return _source_reject_v1(command)
    exact_settlement, exact_intents = command

    exact_context = _admit_context_v1(context)
    if type(exact_context) is FCISStepEvaluationRejectV1:
        return _source_reject_v1(exact_context)

    exact_state = _admit_exact_state_v1(state_source)
    if type(exact_state) is FCISStepEvaluationRejectV1:
        return _source_reject_v1(exact_state)

    pre_binding = _pre_state_binding_v1(exact_state, exact_context)
    if type(pre_binding) is FCISStepEvaluationRejectV1:
        return _reject_v1(
            SourceBoundFeeOccurrenceCodeV1.SOURCE_BINDING_REJECTED,
            pre_binding.phase.value,
            pre_binding.code,
            *_path_text_v1(pre_binding.path),
        )
    _context_bytes, execution_context_hash, _preimage, pre_state_root = pre_binding
    try:
        command_root = sha256_hex(
            _command_preimage_v5(
                exact_settlement,
                exact_intents,
            )
        )
        material = FCISEvaluatedMaterialV1(
            pre_state=exact_state,
            settlement=exact_settlement,
            intents=exact_intents,
            context=exact_context,
        )
    except (AttributeError, TypeError, ValueError, ArithmeticError):
        return _reject_v1(
            SourceBoundFeeOccurrenceCodeV1.INTERNAL_RELATION_FAILURE,
            "material",
        )
    return material, command_root, execution_context_hash, pre_state_root


def _extract_admitted_v1(
    *,
    material: FCISEvaluatedMaterialV1,
    command_root: str,
    execution_context_hash: str,
    pre_state_root: str,
) -> SourceBoundFeeOccurrenceResultV1:
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
    settlement_index = index_result

    if material.context.fee_split_policy is None:
        return _reject_v1(
            SourceBoundFeeOccurrenceCodeV1.MISSING_FEE_DISTRIBUTION_POLICY,
            "context",
            "fee_split_policy",
        )
    try:
        boundary_root = _boundary_root_v1(
            command_root,
            execution_context_hash,
            pre_state_root,
        )
        policy_root = _policy_root_v1(material)
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
                command_root=command_root,
                execution_context_hash=execution_context_hash,
                pre_state_root=pre_state_root,
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
    try:
        return SourceBoundFeeOccurrenceV1(
            material=material,
            command_root=command_root,
            execution_context_hash=execution_context_hash,
            pre_state_root=pre_state_root,
            settlement_index=settlement_index,
            boundary_root=boundary_root,
            policy_root=policy_root,
            segment=segment_result,
            _construction_token=_SOURCE_BOUND_FEE_OCCURRENCE_TOKEN_V1,
        )
    except (AttributeError, TypeError, ValueError, ArithmeticError):
        return _reject_v1(
            SourceBoundFeeOccurrenceCodeV1.INTERNAL_RELATION_FAILURE,
            "result",
        )


def extract_source_bound_fee_occurrence_v1(
    *,
    state_source: object,
    settlement: object,
    intents: object,
    context: object,
) -> SourceBoundFeeOccurrenceResultV1:
    """Derive SLNF occurrence evidence before candidate evaluation."""

    admitted = _admit_material_v1(
        state_source=state_source,
        settlement=settlement,
        intents=intents,
        context=context,
    )
    if type(admitted) is SourceBoundFeeOccurrenceRejectV1:
        return admitted
    material, command_root, execution_context_hash, pre_state_root = admitted
    return _extract_admitted_v1(
        material=material,
        command_root=command_root,
        execution_context_hash=execution_context_hash,
        pre_state_root=pre_state_root,
    )


def verify_source_bound_fee_occurrence_v1(
    occurrence: object,
) -> SourceBoundFeeOccurrenceRejectV1 | None:
    """Re-admit the retained sources and compare the complete fresh extraction."""

    if type(occurrence) is not SourceBoundFeeOccurrenceV1:
        return _reject_v1(
            SourceBoundFeeOccurrenceCodeV1.WRONG_EXACT_TYPE,
            "occurrence",
        )
    try:
        occurrence.__post_init__(_SOURCE_BOUND_FEE_OCCURRENCE_TOKEN_V1)
    except (AttributeError, TypeError, ValueError, ArithmeticError):
        return _reject_v1(
            SourceBoundFeeOccurrenceCodeV1.SOURCE_REDERIVATION_MISMATCH,
            "occurrence",
        )
    fresh = extract_source_bound_fee_occurrence_v1(
        state_source=occurrence.material.pre_state,
        settlement=occurrence.material.settlement,
        intents=occurrence.material.intents,
        context=occurrence.material.context,
    )
    if type(fresh) is SourceBoundFeeOccurrenceRejectV1:
        return fresh
    if fresh != occurrence:
        return _reject_v1(
            SourceBoundFeeOccurrenceCodeV1.SOURCE_REDERIVATION_MISMATCH,
            "occurrence",
        )
    return None


__all__ = (
    "PROTOCOL_FEE_DISTRIBUTION_DOMAIN_ID_V1",
    "SOURCE_BOUND_FEE_OCCURRENCE_VERSION_V1",
    "SourceBoundFeeOccurrenceCodeV1",
    "SourceBoundFeeOccurrenceRejectV1",
    "SourceBoundFeeOccurrenceResultV1",
    "SourceBoundFeeOccurrenceV1",
    "extract_source_bound_fee_occurrence_v1",
    "verify_source_bound_fee_occurrence_v1",
)
