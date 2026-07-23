"""Read-only exact spot-candidate observation for the pre-M5 migration.

The normative migration forbids partially mounting exact spot fields while the
rest of ``DexState`` and its consumers remain on legacy values.  This module
therefore produces differential evidence only.  The mounted engine must not
import it, and its result does not authorize state publication.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import List, final

from ..core.dex import DexState, _first_rejected_settlement_intent_error
from ..core.fee_accumulator_transition import (
    FeeAccumulatorTransitionOkV1,
    FeeAccumulatorTransitionRejectV1,
    split_fee_with_committed_dust_carry_v1,
)
from ..core.fees import FeeSplitParams
from ..core.nonce_batch_transition import (
    IntentNonceBatchOkV1,
    IntentNonceBatchRejectV1,
    validate_and_apply_intent_nonce_batch_committed_v1,
)
from ..core.settlement import Settlement
from ..core.settlement_strong_validator import (
    StrongSettlementEvaluationResultV1,
    StrongSettlementRejectV1,
    StrongSettlementStateCandidateV1,
    evaluate_settlement_strong_committed_v1,
)
from ..state.canonical import domain_sep_bytes, sha256_hex
from ..state.committed_dex_snapshot import canonical_snapshot_bytes_from_committed_state_v1
from ..state.intents import Intent
from ..state.lp_duration_transitions import LPDurationRiskPolicyV1
from ..state.owned_collections import OwnedMapV1
from ..state.snapshot_combinators import AdmitOk, AdmitReject, format_admit_path
from ..state.state_root import state_root_preimage_with_committed_spot_state_v1
from ..state.state_snapshot_values import (
    CommittedBalanceTableV1,
    CommittedFeeAccumulatorStateV1,
    CommittedLPTableV1,
    CommittedNonceTableV1,
    CommittedOracleStateV1,
    CommittedPerpsStateV1,
    CommittedPoolStateV1,
    CommittedVaultStateV1,
)
from ..state.state_snapshots import (
    StateAdmissionError,
    snapshot_balance_table,
    snapshot_fee_accumulator,
    snapshot_lp_table,
    snapshot_nonce_table,
    snapshot_oracle,
    snapshot_perps,
    snapshot_pool_map,
    snapshot_vault,
)
from .dex_snapshot import DEX_SNAPSHOT_VERSION
from .lp_position_age_gate import admit_lp_duration_risk_policy_context_v1

FCIS_SPOT_SHADOW_ONLY_V1 = True


@final
@dataclass(frozen=True, slots=True)
class FCISSpotShadowContextV1:
    """Explicit shell-supplied context forwarded to the exact evaluator."""

    now: int
    min_lp_position_age_seconds: int
    mode: str
    allow_cow_netting: bool
    allow_snapshot_bound_quote_bindings: bool
    protocol_fee_share_bps: int
    protocol_fee_recipient_pubkey: str | None

    def __post_init__(self) -> None:
        if type(self.now) is not int or self.now < 0:
            raise TypeError("now must be an exact nonnegative int")
        if (
            type(self.min_lp_position_age_seconds) is not int
            or self.min_lp_position_age_seconds < 0
        ):
            raise TypeError("min_lp_position_age_seconds must be an exact nonnegative int")
        if type(self.mode) is not str or self.mode not in {
            "strong_replay",
            "strong_proof_carrying",
        }:
            raise ValueError("mode must be one supported exact settlement mode")
        if type(self.allow_cow_netting) is not bool:
            raise TypeError("allow_cow_netting must be an exact bool")
        if type(self.allow_snapshot_bound_quote_bindings) is not bool:
            raise TypeError("allow_snapshot_bound_quote_bindings must be an exact bool")
        if (
            type(self.protocol_fee_share_bps) is not int
            or not 0 <= self.protocol_fee_share_bps <= 10_000
        ):
            raise TypeError("protocol_fee_share_bps must be an exact int in [0, 10000]")
        if self.protocol_fee_recipient_pubkey is not None and (
            type(self.protocol_fee_recipient_pubkey) is not str
            or not self.protocol_fee_recipient_pubkey
        ):
            raise TypeError("protocol_fee_recipient_pubkey must be None or an exact string")
        if self.protocol_fee_share_bps > 0 and self.protocol_fee_recipient_pubkey is None:
            raise ValueError("protocol fee recipient is required for a nonzero share")


@final
@dataclass(frozen=True, slots=True)
class FCISStepShadowContextV1:
    """Explicit values needed to replay one complete pre-M5 DEX step."""

    settlement: FCISSpotShadowContextV1
    require_all_nonces: bool
    reject_settlements_with_rejected_intents: bool
    fee_split_params: FeeSplitParams | None
    snapshot_version: int

    def __post_init__(self) -> None:
        if type(self.settlement) is not FCISSpotShadowContextV1:
            raise TypeError("settlement must be an exact FCISSpotShadowContextV1")
        if type(self.require_all_nonces) is not bool:
            raise TypeError("require_all_nonces must be an exact bool")
        if type(self.reject_settlements_with_rejected_intents) is not bool:
            raise TypeError("reject_settlements_with_rejected_intents must be an exact bool")
        if self.fee_split_params is not None and type(self.fee_split_params) is not FeeSplitParams:
            raise TypeError("fee_split_params must be None or an exact FeeSplitParams")
        if (
            type(self.snapshot_version) is not int
            or not 1 <= self.snapshot_version <= DEX_SNAPSHOT_VERSION
        ):
            raise TypeError("snapshot_version must be an exact supported positive int")


class FCISStepShadowPhaseV1(Enum):
    """Stable phase identifiers for a no-output shadow rejection."""

    STATE_ADMISSION = "state_admission"
    POLICY_ADMISSION = "policy_admission"
    NONCE = "nonce"
    SETTLEMENT = "settlement"
    FEE = "fee"
    ENCODING = "encoding"


@final
@dataclass(frozen=True, slots=True)
class FCISStepShadowRejectV1:
    """Pre-M5 diagnostic rejection that carries no successor representation."""

    phase: FCISStepShadowPhaseV1
    reason: str

    def __post_init__(self) -> None:
        if type(self.phase) is not FCISStepShadowPhaseV1:
            raise TypeError("shadow rejection phase must be exact")
        if type(self.reason) is not str or not self.reason:
            raise TypeError("shadow rejection reason must be an exact nonempty string")


@final
@dataclass(frozen=True, slots=True)
class FCISStepShadowReceiptV1:
    """Canonical evidence derived from one complete exact local candidate.

    The receipt deliberately carries only canonical bytes and hashes. It is not
    a committed-state aggregate and cannot be projected back into ``DexState``.
    """

    snapshot_version: int
    canonical_snapshot_bytes: bytes
    state_root_preimage: bytes
    state_root: str
    snapshot_commitment: str

    def __post_init__(self) -> None:
        if (
            type(self.snapshot_version) is not int
            or not 1 <= self.snapshot_version <= DEX_SNAPSHOT_VERSION
        ):
            raise TypeError("shadow receipt snapshot_version must be exact and supported")
        if type(self.canonical_snapshot_bytes) is not bytes:
            raise TypeError("shadow receipt snapshot bytes must be exact")
        if type(self.state_root_preimage) is not bytes:
            raise TypeError("shadow receipt root preimage must be exact")
        for name in ("state_root", "snapshot_commitment"):
            value = object.__getattribute__(self, name)
            if type(value) is not str or len(value) != 66 or not value.startswith("0x"):
                raise TypeError(f"shadow receipt {name} must be a 32-byte hex digest")


FCISStepShadowResultV1 = FCISStepShadowReceiptV1 | FCISStepShadowRejectV1


@final
@dataclass(frozen=True, slots=True)
class _AdmittedStepStateV1:
    """All eight exact pre-state fields, retained only inside shadow replay."""

    balances: CommittedBalanceTableV1
    pools: OwnedMapV1[str, CommittedPoolStateV1]
    lp_balances: CommittedLPTableV1
    nonces: CommittedNonceTableV1
    vault: CommittedVaultStateV1 | None
    oracle: CommittedOracleStateV1 | None
    fee_accumulator: CommittedFeeAccumulatorStateV1
    perps: CommittedPerpsStateV1 | None


@final
@dataclass(frozen=True, slots=True)
class _StepCandidateV1:
    """One complete local candidate used for every emitted evidence value."""

    spot: StrongSettlementStateCandidateV1
    nonces: CommittedNonceTableV1
    fee_accumulator: CommittedFeeAccumulatorStateV1
    vault: CommittedVaultStateV1 | None
    oracle: CommittedOracleStateV1 | None
    perps: CommittedPerpsStateV1 | None


def _admission_reject_text(
    prefix: str,
    reject: AdmitReject | StateAdmissionError,
) -> str:
    return f"{prefix}: {reject.code.value}:{format_admit_path(reject.path)}"


def _clean_shadow_error(exc: Exception) -> str:
    detail = " ".join(str(exc).split())
    if len(detail) > 200:
        detail = detail[:200]
    return type(exc).__name__ if not detail else f"{type(exc).__name__}: {detail}"


def _readmit_spot_shadow_context_v1(source: object) -> FCISSpotShadowContextV1:
    """Own one exact context copy so a caller-retained alias cannot drift."""

    if type(source) is not FCISSpotShadowContextV1:
        raise TypeError("shadow context requires an exact FCISSpotShadowContextV1")
    return FCISSpotShadowContextV1(
        now=object.__getattribute__(source, "now"),
        min_lp_position_age_seconds=object.__getattribute__(
            source,
            "min_lp_position_age_seconds",
        ),
        mode=object.__getattribute__(source, "mode"),
        allow_cow_netting=object.__getattribute__(source, "allow_cow_netting"),
        allow_snapshot_bound_quote_bindings=object.__getattribute__(
            source,
            "allow_snapshot_bound_quote_bindings",
        ),
        protocol_fee_share_bps=object.__getattribute__(source, "protocol_fee_share_bps"),
        protocol_fee_recipient_pubkey=object.__getattribute__(
            source,
            "protocol_fee_recipient_pubkey",
        ),
    )


def _readmit_step_shadow_context_v1(source: object) -> FCISStepShadowContextV1:
    """Own all nested step policy values before exact transition evaluation."""

    if type(source) is not FCISStepShadowContextV1:
        raise TypeError("shadow context requires an exact FCISStepShadowContextV1")
    raw_fee_split = object.__getattribute__(source, "fee_split_params")
    if raw_fee_split is None:
        fee_split = None
    elif type(raw_fee_split) is FeeSplitParams:
        fee_split = FeeSplitParams(
            buyback_bps=object.__getattribute__(raw_fee_split, "buyback_bps"),
            treasury_bps=object.__getattribute__(raw_fee_split, "treasury_bps"),
            rewards_bps=object.__getattribute__(raw_fee_split, "rewards_bps"),
        )
    else:
        raise TypeError("fee_split_params must be None or an exact FeeSplitParams")
    return FCISStepShadowContextV1(
        settlement=_readmit_spot_shadow_context_v1(
            object.__getattribute__(source, "settlement"),
        ),
        require_all_nonces=object.__getattribute__(source, "require_all_nonces"),
        reject_settlements_with_rejected_intents=object.__getattribute__(
            source,
            "reject_settlements_with_rejected_intents",
        ),
        fee_split_params=fee_split,
        snapshot_version=object.__getattribute__(source, "snapshot_version"),
    )


def _admit_all_state_fields_v1(
    state: DexState,
) -> _AdmittedStepStateV1 | FCISStepShadowRejectV1:
    """Admit all eight fields in the normative M5 order without publication."""

    field_name = "balances"
    try:
        balances = snapshot_balance_table(state.balances)
        field_name = "pools"
        pools = snapshot_pool_map(state.pools)
        field_name = "lp_balances"
        lp_balances = snapshot_lp_table(state.lp_balances)
        field_name = "nonces"
        nonces = snapshot_nonce_table(state.nonces)
        field_name = "vault"
        vault = snapshot_vault(state.vault)
        field_name = "oracle"
        oracle = snapshot_oracle(state.oracle)
        field_name = "fee_accumulator"
        fee_accumulator = snapshot_fee_accumulator(state.fee_accumulator)
        field_name = "perps"
        perps = snapshot_perps(state.perps)
    except StateAdmissionError as exc:
        return FCISStepShadowRejectV1(
            FCISStepShadowPhaseV1.STATE_ADMISSION,
            _admission_reject_text(
                f"shadow {field_name} admission rejected",
                exc,
            ),
        )
    except (TypeError, ValueError) as exc:
        return FCISStepShadowRejectV1(
            FCISStepShadowPhaseV1.STATE_ADMISSION,
            f"shadow {field_name} admission rejected: {_clean_shadow_error(exc)}",
        )
    return _AdmittedStepStateV1(
        balances=balances,
        pools=pools,
        lp_balances=lp_balances,
        nonces=nonces,
        vault=vault,
        oracle=oracle,
        fee_accumulator=fee_accumulator,
        perps=perps,
    )


def evaluate_fcis_spot_candidate_shadow_v1(
    *,
    state: DexState,
    settlement: Settlement,
    intents: List[Intent],
    context: object,
    lp_duration_policy: object,
) -> StrongSettlementEvaluationResultV1:
    """Observe the exact candidate without affecting mounted acceptance.

    The legacy state graph is admitted one way into exact values.  No exact
    result is projected back into a mutable authority representation.
    """

    if type(state) is not DexState:
        return StrongSettlementRejectV1("shadow state requires an exact DexState")
    try:
        exact_context = _readmit_spot_shadow_context_v1(context)
    except (AttributeError, TypeError, ValueError) as exc:
        return StrongSettlementRejectV1(
            f"shadow context admission rejected: {_clean_shadow_error(exc)}"
        )
    policy_result = admit_lp_duration_risk_policy_context_v1(lp_duration_policy)
    if type(policy_result) is AdmitReject:
        return StrongSettlementRejectV1(
            _admission_reject_text(
                "shadow LP duration-policy admission rejected",
                policy_result,
            )
        )
    if type(policy_result) is not AdmitOk:
        return StrongSettlementRejectV1(
            "shadow LP duration-policy admission returned an impossible result"
        )
    exact_policy = policy_result.value
    if exact_policy is not None and type(exact_policy) is not LPDurationRiskPolicyV1:
        return StrongSettlementRejectV1(
            "shadow LP duration-policy admission returned a wrong exact type"
        )
    try:
        exact_balances = snapshot_balance_table(state.balances)
        exact_pools = snapshot_pool_map(state.pools)
        exact_lp_balances = snapshot_lp_table(state.lp_balances)
    except StateAdmissionError as exc:
        return StrongSettlementRejectV1(
            f"shadow state admission rejected: {exc.code.value}:{format_admit_path(exc.path)}"
        )
    return evaluate_settlement_strong_committed_v1(
        settlement=settlement,
        intents=intents,
        pre_balances=exact_balances,
        pre_pools=exact_pools,
        pre_lp_balances=exact_lp_balances,
        now=exact_context.now,
        min_lp_position_age_seconds=exact_context.min_lp_position_age_seconds,
        lp_duration_policy=exact_policy,
        mode=exact_context.mode,
        allow_cow_netting=exact_context.allow_cow_netting,
        allow_snapshot_bound_quote_bindings=(exact_context.allow_snapshot_bound_quote_bindings),
        protocol_fee_share_bps=exact_context.protocol_fee_share_bps,
        protocol_fee_recipient_pubkey=exact_context.protocol_fee_recipient_pubkey,
    )


def _admit_step_policy_v1(
    lp_duration_policy: object,
) -> LPDurationRiskPolicyV1 | None | FCISStepShadowRejectV1:
    policy_result = admit_lp_duration_risk_policy_context_v1(lp_duration_policy)
    if type(policy_result) is AdmitReject:
        return FCISStepShadowRejectV1(
            FCISStepShadowPhaseV1.POLICY_ADMISSION,
            _admission_reject_text(
                "shadow LP duration-policy admission rejected",
                policy_result,
            ),
        )
    if type(policy_result) is not AdmitOk:
        return FCISStepShadowRejectV1(
            FCISStepShadowPhaseV1.POLICY_ADMISSION,
            "shadow LP duration-policy admission returned an impossible result",
        )
    exact_policy = policy_result.value
    if exact_policy is not None and type(exact_policy) is not LPDurationRiskPolicyV1:
        return FCISStepShadowRejectV1(
            FCISStepShadowPhaseV1.POLICY_ADMISSION,
            "shadow LP duration-policy admission returned a wrong exact type",
        )
    return exact_policy


def _apply_step_nonce_v1(
    *,
    state: _AdmittedStepStateV1,
    intents: List[Intent],
    context: FCISStepShadowContextV1,
) -> CommittedNonceTableV1 | FCISStepShadowRejectV1:
    nonce_result = validate_and_apply_intent_nonce_batch_committed_v1(
        nonces=state.nonces,
        intents=intents,
        require_all_nonces=context.require_all_nonces,
    )
    if type(nonce_result) is IntentNonceBatchRejectV1:
        return FCISStepShadowRejectV1(
            FCISStepShadowPhaseV1.NONCE,
            nonce_result.public_reason,
        )
    if type(nonce_result) is not IntentNonceBatchOkV1:
        return FCISStepShadowRejectV1(
            FCISStepShadowPhaseV1.NONCE,
            "shadow nonce transition returned an impossible result",
        )
    return nonce_result.state


def _apply_step_settlement_v1(
    *,
    state: _AdmittedStepStateV1,
    settlement: Settlement,
    intents: List[Intent],
    context: FCISStepShadowContextV1,
    lp_duration_policy: LPDurationRiskPolicyV1 | None,
) -> StrongSettlementStateCandidateV1 | FCISStepShadowRejectV1:
    settlement_context = context.settlement
    spot_result = evaluate_settlement_strong_committed_v1(
        settlement=settlement,
        intents=intents,
        pre_balances=state.balances,
        pre_pools=state.pools,
        pre_lp_balances=state.lp_balances,
        now=settlement_context.now,
        min_lp_position_age_seconds=settlement_context.min_lp_position_age_seconds,
        lp_duration_policy=lp_duration_policy,
        mode=settlement_context.mode,
        allow_cow_netting=settlement_context.allow_cow_netting,
        allow_snapshot_bound_quote_bindings=(
            settlement_context.allow_snapshot_bound_quote_bindings
        ),
        protocol_fee_share_bps=settlement_context.protocol_fee_share_bps,
        protocol_fee_recipient_pubkey=settlement_context.protocol_fee_recipient_pubkey,
    )
    if type(spot_result) is StrongSettlementRejectV1:
        return FCISStepShadowRejectV1(
            FCISStepShadowPhaseV1.SETTLEMENT,
            spot_result.reason,
        )
    if type(spot_result) is not StrongSettlementStateCandidateV1:
        return FCISStepShadowRejectV1(
            FCISStepShadowPhaseV1.SETTLEMENT,
            "shadow settlement transition returned an impossible result",
        )
    if context.reject_settlements_with_rejected_intents:
        rejected_intent_error = _first_rejected_settlement_intent_error(settlement)
        if rejected_intent_error is not None:
            return FCISStepShadowRejectV1(
                FCISStepShadowPhaseV1.SETTLEMENT,
                rejected_intent_error,
            )
    return spot_result


def _apply_step_fee_v1(
    *,
    state: CommittedFeeAccumulatorStateV1,
    settlement: Settlement,
    params: FeeSplitParams | None,
) -> CommittedFeeAccumulatorStateV1 | FCISStepShadowRejectV1:
    if params is None:
        return state
    total_fees = 0
    for fill in settlement.fills:
        fee = fill.fee_paid
        if fee is None:
            continue
        if type(fee) is not int or fee < 0:
            return FCISStepShadowRejectV1(
                FCISStepShadowPhaseV1.FEE,
                "settlement fee must be an exact nonnegative int",
            )
        total_fees += fee
    fee_result = split_fee_with_committed_dust_carry_v1(
        fee_amount=total_fees,
        params=params,
        state=state,
    )
    if type(fee_result) is FeeAccumulatorTransitionRejectV1:
        return FCISStepShadowRejectV1(
            FCISStepShadowPhaseV1.FEE,
            f"{fee_result.code.value}:{fee_result.field}",
        )
    if type(fee_result) is not FeeAccumulatorTransitionOkV1:
        return FCISStepShadowRejectV1(
            FCISStepShadowPhaseV1.FEE,
            "shadow fee transition returned an impossible result",
        )
    return fee_result.state


def _evaluate_step_candidate_v1(
    *,
    state: _AdmittedStepStateV1,
    settlement: Settlement,
    intents: List[Intent],
    context: FCISStepShadowContextV1,
    lp_duration_policy: LPDurationRiskPolicyV1 | None,
) -> _StepCandidateV1 | FCISStepShadowRejectV1:
    nonces = _apply_step_nonce_v1(
        state=state,
        intents=intents,
        context=context,
    )
    if type(nonces) is FCISStepShadowRejectV1:
        return nonces
    spot = _apply_step_settlement_v1(
        state=state,
        settlement=settlement,
        intents=intents,
        context=context,
        lp_duration_policy=lp_duration_policy,
    )
    if type(spot) is FCISStepShadowRejectV1:
        return spot
    fee_accumulator = _apply_step_fee_v1(
        state=state.fee_accumulator,
        settlement=settlement,
        params=context.fee_split_params,
    )
    if type(fee_accumulator) is FCISStepShadowRejectV1:
        return fee_accumulator
    return _StepCandidateV1(
        spot=spot,
        nonces=nonces,
        fee_accumulator=fee_accumulator,
        vault=state.vault,
        oracle=state.oracle,
        perps=state.perps,
    )


def _encode_step_receipt_v1(
    candidate: _StepCandidateV1,
    *,
    snapshot_version: int,
) -> FCISStepShadowResultV1:
    try:
        snapshot_bytes = canonical_snapshot_bytes_from_committed_state_v1(
            version=snapshot_version,
            balances=candidate.spot.balances,
            pools=candidate.spot.pools,
            lp_balances=candidate.spot.lp_balances,
            nonces=candidate.nonces,
            fee_accumulator=candidate.fee_accumulator,
            vault=candidate.vault,
            oracle=candidate.oracle,
            perps=candidate.perps,
        )
        root_preimage = state_root_preimage_with_committed_spot_state_v1(
            balances=candidate.spot.balances,
            pools=candidate.spot.pools,
            lp_balances=candidate.spot.lp_balances,
            nonces=candidate.nonces,
            fee_accumulator=candidate.fee_accumulator,
        )
    except (StateAdmissionError, TypeError, ValueError) as exc:
        return FCISStepShadowRejectV1(
            FCISStepShadowPhaseV1.ENCODING,
            f"shadow candidate encoding rejected: {_clean_shadow_error(exc)}",
        )
    return FCISStepShadowReceiptV1(
        snapshot_version=snapshot_version,
        canonical_snapshot_bytes=snapshot_bytes,
        state_root_preimage=root_preimage,
        state_root=sha256_hex(root_preimage),
        snapshot_commitment=sha256_hex(
            domain_sep_bytes("dex_snapshot", version=snapshot_version) + snapshot_bytes
        ),
    )


def evaluate_fcis_step_shadow_v1(
    *,
    state: DexState,
    settlement: Settlement,
    intents: List[Intent],
    context: object,
    lp_duration_policy: object,
) -> FCISStepShadowResultV1:
    """Replay one complete exact step and emit only canonical evidence.

    This function is the pre-M5 composition check. It admits all eight state
    fields in fixed order, applies exact nonce, settlement, LP-duration, and
    fee transitions, then derives the full snapshot and root from those same
    local successor values. No exact candidate is projected into a legacy
    mutable domain object and no state is published.
    """

    if type(state) is not DexState:
        return FCISStepShadowRejectV1(
            FCISStepShadowPhaseV1.STATE_ADMISSION,
            "shadow state requires an exact DexState",
        )
    try:
        exact_context = _readmit_step_shadow_context_v1(context)
    except (AttributeError, TypeError, ValueError) as exc:
        return FCISStepShadowRejectV1(
            FCISStepShadowPhaseV1.POLICY_ADMISSION,
            f"shadow context admission rejected: {_clean_shadow_error(exc)}",
        )

    state_result = _admit_all_state_fields_v1(state)
    if type(state_result) is FCISStepShadowRejectV1:
        return state_result
    policy_result = _admit_step_policy_v1(lp_duration_policy)
    if type(policy_result) is FCISStepShadowRejectV1:
        return policy_result
    candidate = _evaluate_step_candidate_v1(
        state=state_result,
        settlement=settlement,
        intents=intents,
        context=exact_context,
        lp_duration_policy=policy_result,
    )
    if type(candidate) is FCISStepShadowRejectV1:
        return candidate
    return _encode_step_receipt_v1(
        candidate,
        snapshot_version=exact_context.snapshot_version,
    )


__all__ = (
    "FCIS_SPOT_SHADOW_ONLY_V1",
    "FCISSpotShadowContextV1",
    "FCISStepShadowContextV1",
    "FCISStepShadowPhaseV1",
    "FCISStepShadowReceiptV1",
    "FCISStepShadowRejectV1",
    "FCISStepShadowResultV1",
    "evaluate_fcis_spot_candidate_shadow_v1",
    "evaluate_fcis_step_shadow_v1",
)
