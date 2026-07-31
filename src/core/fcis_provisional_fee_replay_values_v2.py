"""Immutable values for unmounted V2 provisional-fee replay.

The input claims and policy are untrusted exact data. Controlled construction
is reserved for replay-derived candidates, witnesses, and typed rejections.

These values do not authenticate a fee policy, construct a receipt, publish
state, or mount runtime authority.
"""

from __future__ import annotations

from dataclasses import InitVar, dataclass
from enum import Enum
from hashlib import sha256
from typing import TypeAlias, cast, final

from ..state.canonical import canonical_json_bytes
from ..state.state_snapshot_values import (
    MAX_STATE_STRING_CHARACTERS_V1,
    MAX_STATE_STRING_UTF8_BYTES_V1,
)
from .domain_limits import DEX_SWAP_AMOUNT_MAX, require_int_range
from .fcis_fee_apportionment_values import (
    MAX_FEE_AMOUNT_CANDIDATES_V2,
    FeeApportionmentKeyV2,
)
from .fcis_fee_occurrence_normal_form import FeeWitnessOccurrenceClaimV1
from .fcis_settlement_strong_values import ExactSpotPreStateV1

PROVISIONAL_FEE_REPLAY_VERSION_V2 = "zenodex/fcis/provisional-fee-replay/v2"
PROVISIONAL_FEE_WITNESS_SCHEMA_ID_V2 = "zenodex/fcis/provisional-fee-replay/witness/v2"

_HEX_LOWER_V2 = frozenset("0123456789abcdef")
_PROVISIONAL_FEE_REPLAY_TOKEN_V2 = object()


class ProvisionalSwapKindV2(Enum):
    EXACT_IN = "swap_exact_in"
    EXACT_OUT = "swap_exact_out"


class ProvisionalFeeReplayCodeV2(Enum):
    INVALID_INPUT = "invalid_input"
    NONCANONICAL_POSITION = "noncanonical_position"
    DUPLICATE_INTENT = "duplicate_intent"
    POOL_NOT_FOUND = "pool_not_found"
    POOL_NOT_ACTIVE = "pool_not_active"
    ASSET_MISMATCH = "asset_mismatch"
    UNSUPPORTED_PROTOCOL_FEE_CURVE = "unsupported_protocol_fee_curve"
    QUOTE_REJECTED = "quote_rejected"
    DECLARED_FILL_MISMATCH = "declared_fill_mismatch"
    SLIPPAGE = "slippage"
    STATE_TRANSITION_REJECTED = "state_transition_rejected"
    POST_STATE_MISMATCH = "post_state_mismatch"


def _require_text_v2(name: str, value: object) -> str:
    if type(value) is not str or not value:
        raise TypeError(f"{name} must be an exact nonempty string")
    if len(value) > MAX_STATE_STRING_CHARACTERS_V1:
        raise ValueError(f"{name} exceeds its character bound")
    try:
        encoded = value.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise ValueError(f"{name} must contain Unicode scalar values") from exc
    if len(encoded) > MAX_STATE_STRING_UTF8_BYTES_V1:
        raise ValueError(f"{name} exceeds its UTF-8 bound")
    return value


def _require_pool_fingerprint_v2(value: object) -> str:
    if (
        type(value) is not str
        or len(value) != 66
        or not value.startswith("0x")
        or value != value.lower()
        or any(character not in _HEX_LOWER_V2 for character in value[2:])
    ):
        raise ValueError("pool snapshot fingerprint must be a canonical 0x digest")
    return value


def _require_position_v2(value: object) -> int:
    return require_int_range(
        "provisional swap position",
        value,
        minimum=0,
        maximum=MAX_FEE_AMOUNT_CANDIDATES_V2 - 1,
    )


def _require_swap_amount_v2(name: str, value: object, *, minimum: int = 0) -> int:
    return require_int_range(
        name,
        value,
        minimum=minimum,
        maximum=DEX_SWAP_AMOUNT_MAX,
    )


@final
@dataclass(frozen=True, slots=True)
class ProvisionalQuotedSwapClaimV2:
    """One untrusted quoted-swap claim in canonical settlement order."""

    position: int
    kind: ProvisionalSwapKindV2
    intent_id: str
    sender_pubkey: str
    recipient_pubkey: str
    pool_id: str
    asset_in: str
    asset_out: str
    amount_specified: int
    limit_amount: int
    amount_in_filled: int
    amount_out_filled: int
    fee_paid: int
    protocol_fee_paid: int

    def __post_init__(self) -> None:
        _require_position_v2(self.position)
        if type(self.kind) is not ProvisionalSwapKindV2:
            raise TypeError("provisional swap kind must be exact")
        for name, value in (
            ("intent identifier", self.intent_id),
            ("sender public key", self.sender_pubkey),
            ("recipient public key", self.recipient_pubkey),
            ("pool identifier", self.pool_id),
            ("input asset", self.asset_in),
            ("output asset", self.asset_out),
        ):
            _require_text_v2(name, value)
        if self.asset_in == self.asset_out:
            raise ValueError("provisional swap assets must be distinct")
        _require_swap_amount_v2("amount specified", self.amount_specified, minimum=1)
        _require_swap_amount_v2("limit amount", self.limit_amount)
        _require_swap_amount_v2("filled input amount", self.amount_in_filled, minimum=1)
        _require_swap_amount_v2("filled output amount", self.amount_out_filled, minimum=1)
        _require_swap_amount_v2("total fee", self.fee_paid)
        _require_swap_amount_v2("protocol fee", self.protocol_fee_paid)
        if self.protocol_fee_paid > self.fee_paid:
            raise ValueError("protocol fee cannot exceed total fee")


@final
@dataclass(frozen=True, slots=True)
class ProvisionalFeeReplayPolicyV2:
    """Untrusted semantic policy input; later authority binding is required."""

    fee_distribution_domain_id: str
    protocol_fee_share_bps: int

    def __post_init__(self) -> None:
        _require_text_v2(
            "fee distribution domain identifier",
            self.fee_distribution_domain_id,
        )
        require_int_range(
            "protocol fee share bps",
            self.protocol_fee_share_bps,
            minimum=0,
            maximum=10_000,
        )


@final
@dataclass(frozen=True, slots=True)
class ProvisionalProtocolFeeWitnessV2:
    """One replay-derived fee occurrence, still without publication authority."""

    fill_position: int
    intent_id: str
    fee_distribution_domain_id: str
    pool_snapshot_fingerprint: str
    pool_id: str
    asset: str
    sender_pubkey: str
    kind: ProvisionalSwapKindV2
    recipient_pubkey: str
    asset_out: str
    amount_specified: int
    limit_amount: int
    recipient_output_credit: int
    total_fee_amount: int
    protocol_fee_share_bps: int
    sender_input_debit: int
    pool_reserve_credit: int
    provisional_fee_amount: int
    reserve_in_before: int
    reserve_out_before: int
    reserve_in_after: int
    reserve_out_after: int
    source_witness_root: str
    _construction_token: InitVar[object]

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _PROVISIONAL_FEE_REPLAY_TOKEN_V2:
            raise TypeError("provisional fee witness requires controlled replay")
        _revalidate_witness_v2(self)


@final
@dataclass(frozen=True, slots=True)
class ProvisionalFeeReplayCandidateV2:
    """Complete replay state and fee witnesses from one pure ordered fold."""

    post_state: ExactSpotPreStateV1
    fee_witnesses: tuple[ProvisionalProtocolFeeWitnessV2, ...]
    _construction_token: InitVar[object]

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _PROVISIONAL_FEE_REPLAY_TOKEN_V2:
            raise TypeError("provisional fee replay candidate requires controlled replay")
        if type(self.post_state) is not ExactSpotPreStateV1:
            raise TypeError("provisional fee replay post-state must be exact")
        self.post_state.__post_init__()
        if type(self.fee_witnesses) is not tuple:
            raise TypeError("provisional fee witnesses must be an exact tuple")
        for witness in self.fee_witnesses:
            if type(witness) is not ProvisionalProtocolFeeWitnessV2:
                raise TypeError("provisional fee witness must be exact")
            _revalidate_witness_v2(witness)
        positions = tuple(witness.fill_position for witness in self.fee_witnesses)
        if positions != tuple(sorted(set(positions))):
            raise ValueError("provisional fee witnesses must retain unique fill order")
        roots = tuple(witness.source_witness_root for witness in self.fee_witnesses)
        if len(roots) != len(set(roots)):
            raise ValueError("provisional fee witnesses must have unique source roots")


@final
@dataclass(frozen=True, slots=True)
class ProvisionalFeeReplayRejectV2:
    """Stable failure with no successor or fee-witness authority."""

    code: ProvisionalFeeReplayCodeV2
    position: int | None
    detail: str
    _construction_token: InitVar[object]

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _PROVISIONAL_FEE_REPLAY_TOKEN_V2:
            raise TypeError("provisional fee replay rejection requires controlled replay")
        if type(self.code) is not ProvisionalFeeReplayCodeV2:
            raise TypeError("provisional fee replay code must be exact")
        if self.position is not None:
            _require_position_v2(self.position)
        _require_text_v2("provisional fee replay rejection detail", self.detail)


ProvisionalFeeReplayResultV2: TypeAlias = (
    ProvisionalFeeReplayCandidateV2 | ProvisionalFeeReplayRejectV2
)


def _reject_v2(
    code: ProvisionalFeeReplayCodeV2,
    position: int | None,
    detail: str,
) -> ProvisionalFeeReplayRejectV2:
    return ProvisionalFeeReplayRejectV2(
        code=code,
        position=position,
        detail=detail,
        _construction_token=_PROVISIONAL_FEE_REPLAY_TOKEN_V2,
    )


def _witness_payload_v2(fields: dict[str, str | int]) -> dict[str, object]:
    return {
        "schema": PROVISIONAL_FEE_WITNESS_SCHEMA_ID_V2,
        "value": fields,
    }


def _source_witness_root_v2(fields: dict[str, str | int]) -> str:
    domain = PROVISIONAL_FEE_REPLAY_VERSION_V2.encode("ascii")
    payload = canonical_json_bytes(_witness_payload_v2(fields))
    return sha256(len(domain).to_bytes(4, "big") + domain + payload).hexdigest()


def _witness_fields_v2(
    witness: ProvisionalProtocolFeeWitnessV2,
) -> dict[str, str | int]:
    if type(witness.kind) is not ProvisionalSwapKindV2:
        raise TypeError("provisional fee witness swap kind must be exact")
    return {
        "fill_position": witness.fill_position,
        "intent_id": witness.intent_id,
        "pool_snapshot_fingerprint": witness.pool_snapshot_fingerprint,
        "fee_distribution_domain_id": witness.fee_distribution_domain_id,
        "pool_id": witness.pool_id,
        "asset": witness.asset,
        "sender_pubkey": witness.sender_pubkey,
        "swap_kind": witness.kind.value,
        "recipient_pubkey": witness.recipient_pubkey,
        "asset_out": witness.asset_out,
        "amount_specified": witness.amount_specified,
        "limit_amount": witness.limit_amount,
        "recipient_output_credit": witness.recipient_output_credit,
        "total_fee_amount": witness.total_fee_amount,
        "protocol_fee_share_bps": witness.protocol_fee_share_bps,
        "sender_input_debit": witness.sender_input_debit,
        "pool_reserve_credit": witness.pool_reserve_credit,
        "provisional_fee_amount": witness.provisional_fee_amount,
        "reserve_in_before": witness.reserve_in_before,
        "reserve_out_before": witness.reserve_out_before,
        "reserve_in_after": witness.reserve_in_after,
        "reserve_out_after": witness.reserve_out_after,
    }


def _validate_witness_representation_v2(
    witness: ProvisionalProtocolFeeWitnessV2, fields: dict[str, str | int]
) -> None:
    _require_position_v2(witness.fill_position)
    for name in (
        "intent_id",
        "fee_distribution_domain_id",
        "pool_id",
        "asset",
        "sender_pubkey",
        "recipient_pubkey",
        "asset_out",
    ):
        _require_text_v2(name, fields[name])
    _require_pool_fingerprint_v2(witness.pool_snapshot_fingerprint)
    for name in (
        "amount_specified",
        "limit_amount",
        "recipient_output_credit",
        "total_fee_amount",
        "sender_input_debit",
        "pool_reserve_credit",
        "provisional_fee_amount",
        "reserve_in_before",
        "reserve_out_before",
        "reserve_in_after",
        "reserve_out_after",
    ):
        _require_swap_amount_v2(name, fields[name])
    require_int_range(
        "protocol fee share bps",
        witness.protocol_fee_share_bps,
        minimum=0,
        maximum=10_000,
    )


def _validate_witness_semantics_v2(
    witness: ProvisionalProtocolFeeWitnessV2,
) -> None:
    if witness.asset == witness.asset_out:
        raise ValueError("provisional fee witness assets must be distinct")
    if witness.provisional_fee_amount == 0:
        raise ValueError("provisional fee witness amount must be positive")
    if witness.total_fee_amount < witness.provisional_fee_amount:
        raise ValueError("provisional fee witness protocol fee exceeds total fee")
    if witness.sender_input_debit != (witness.pool_reserve_credit + witness.provisional_fee_amount):
        raise ValueError("provisional fee witness violates input conservation")
    if witness.reserve_in_after - witness.reserve_in_before != witness.pool_reserve_credit:
        raise ValueError("provisional fee witness input reserve delta mismatch")
    if witness.reserve_out_before - witness.reserve_out_after != witness.recipient_output_credit:
        raise ValueError("provisional fee witness output reserve delta mismatch")
    if witness.kind is ProvisionalSwapKindV2.EXACT_IN:
        if witness.amount_specified != witness.sender_input_debit:
            raise ValueError("exact-in witness amount mismatch")
        if witness.recipient_output_credit < witness.limit_amount:
            raise ValueError("exact-in witness violates its minimum output")
    else:
        if witness.amount_specified != witness.recipient_output_credit:
            raise ValueError("exact-out witness amount mismatch")
        if witness.sender_input_debit > witness.limit_amount:
            raise ValueError("exact-out witness violates its maximum input")


def _revalidate_witness_v2(witness: ProvisionalProtocolFeeWitnessV2) -> None:
    fields = _witness_fields_v2(witness)
    _validate_witness_representation_v2(witness, fields)
    _validate_witness_semantics_v2(witness)
    expected_root = _source_witness_root_v2(fields)
    if witness.source_witness_root != expected_root:
        raise ValueError("provisional fee witness root mismatch")


def _admit_context_v2(
    pre_state: object,
    policy: object,
) -> tuple[ExactSpotPreStateV1, ProvisionalFeeReplayPolicyV2] | ProvisionalFeeReplayRejectV2:
    if type(pre_state) is not ExactSpotPreStateV1:
        return _reject_v2(
            ProvisionalFeeReplayCodeV2.INVALID_INPUT,
            None,
            "pre-state must be exact",
        )
    if type(policy) is not ProvisionalFeeReplayPolicyV2:
        return _reject_v2(
            ProvisionalFeeReplayCodeV2.INVALID_INPUT,
            None,
            "policy must be exact",
        )
    exact_pre_state = cast(ExactSpotPreStateV1, pre_state)
    exact_policy = policy
    try:
        exact_pre_state.__post_init__()
        exact_policy.__post_init__()
    except (ArithmeticError, TypeError, ValueError) as exc:
        return _reject_v2(
            ProvisionalFeeReplayCodeV2.INVALID_INPUT,
            None,
            str(exc),
        )
    return exact_pre_state, exact_policy


def provisional_fee_witness_claims_v2(
    candidate: ProvisionalFeeReplayCandidateV2,
) -> tuple[FeeWitnessOccurrenceClaimV1, ...]:
    """Project replay-derived witnesses into the untrusted SLNF claim carrier."""

    if type(candidate) is not ProvisionalFeeReplayCandidateV2:
        raise TypeError("provisional fee replay candidate must be exact")
    candidate.__post_init__(_PROVISIONAL_FEE_REPLAY_TOKEN_V2)
    return tuple(
        FeeWitnessOccurrenceClaimV1(
            position=position,
            key=FeeApportionmentKeyV2(
                witness.fee_distribution_domain_id,
                witness.asset,
            ),
            amount=witness.provisional_fee_amount,
            source_witness_root=witness.source_witness_root,
        )
        for position, witness in enumerate(candidate.fee_witnesses)
    )


__all__ = (
    "PROVISIONAL_FEE_REPLAY_VERSION_V2",
    "PROVISIONAL_FEE_WITNESS_SCHEMA_ID_V2",
    "ProvisionalFeeReplayCandidateV2",
    "ProvisionalFeeReplayCodeV2",
    "ProvisionalFeeReplayPolicyV2",
    "ProvisionalFeeReplayRejectV2",
    "ProvisionalFeeReplayResultV2",
    "ProvisionalProtocolFeeWitnessV2",
    "ProvisionalQuotedSwapClaimV2",
    "ProvisionalSwapKindV2",
    "provisional_fee_witness_claims_v2",
)
