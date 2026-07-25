"""Thin compatibility adapter for the unmounted FCIS step evaluator.

Legacy shell values are projected into closed source carriers, admitted once,
and forwarded to the production-owned pure evaluator. This module emits
differential evidence only. The mounted engine must not import it.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import TypeAlias, final

from ..core.dex import DexState
from ..core.fcis_step_evaluation_values import (
    FCISStepEvaluationOkV1,
    FCISStepEvaluationPhaseV1,
    FCISStepEvaluationRejectV1,
)
from ..core.fcis_step_evaluator import (
    evaluate_fcis_spot_candidate_v1,
    evaluate_fcis_step_candidate_v1,
)
from ..core.fees import FeeSplitParams
from ..core.settlement import Settlement
from ..core.settlement_snapshots import snapshot_settlement
from ..core.settlement_strong_validator import (
    StrongSettlementEvaluationResultV1,
    StrongSettlementRejectV1,
)
from ..state.fcis_execution_context import (
    admit_fcis_settlement_execution_context_v1,
    admit_fcis_step_execution_context_v1,
)
from ..state.fcis_execution_context_values import (
    FCISFeeSplitPolicySourceV1,
    FCISSettlementExecutionContextSourceV1,
    FCISSettlementExecutionContextV1,
    FCISSettlementModeV1,
    FCISStepExecutionContextSourceV1,
    FCISStepExecutionContextV1,
)
from ..state.intent_snapshots import admit_intent_batch
from ..state.intents import Intent
from ..state.legacy_state_snapshots import (
    admit_legacy_balance_for_differential_v1,
    admit_legacy_lp_for_differential_v1,
    admit_legacy_nonce_for_differential_v1,
    admit_legacy_pool_map_for_differential_v1,
)
from ..state.lp_duration_policy_values import LPDurationRiskPolicyV1
from ..state.owned_collections import OwnedMapV1
from ..state.snapshot_combinators import AdmitCode, AdmitOk, AdmitReject, format_admit_path
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
    snapshot_fee_accumulator,
    snapshot_oracle,
    snapshot_perps,
    snapshot_vault,
)
from ..state.support_root import EXACT_SUPPORT_ROOT_VERSION_V1
from .dex_snapshot import DEX_SNAPSHOT_VERSION
from .lp_position_age_gate import admit_lp_duration_risk_policy_context_v1

FCIS_SPOT_SHADOW_ONLY_V1 = True


@final
@dataclass(frozen=True, slots=True)
class FCISSpotShadowContextV1:
    """Legacy shell carrier retained only for compatibility projection."""

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
        recipient = self.protocol_fee_recipient_pubkey
        if recipient is not None and (type(recipient) is not str or not recipient):
            raise TypeError("protocol_fee_recipient_pubkey must be None or an exact string")
        if self.protocol_fee_share_bps > 0 and recipient is None:
            raise ValueError("protocol fee recipient is required for a nonzero share")


@final
@dataclass(frozen=True, slots=True)
class FCISStepShadowContextV1:
    """Legacy shell carrier for one complete pre-M5 differential step."""

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
    """Stable compatibility phase identifiers for no-output rejection."""

    COMMAND_ADMISSION = "command_admission"
    STATE_ADMISSION = "state_admission"
    POLICY_ADMISSION = "policy_admission"
    PRE_STATE_BINDING = "pre_state_binding"
    NONCE = "nonce"
    SETTLEMENT = "settlement"
    FEE = "fee"
    ENCODING = "encoding"


@final
@dataclass(frozen=True, slots=True)
class FCISStepShadowRejectV1:
    """Diagnostic rejection carrying no successor or accepted evidence."""

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
    """Compatibility evidence with no state or commit authority."""

    snapshot_version: int
    canonical_snapshot_bytes: bytes
    state_root_preimage: bytes
    state_root: str
    support_root_version: int
    support_root: str
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
        if self.support_root_version != EXACT_SUPPORT_ROOT_VERSION_V1:
            raise ValueError("unexpected shadow exact support-root version")
        for field_name in ("state_root", "support_root", "snapshot_commitment"):
            value = object.__getattribute__(self, field_name)
            if type(value) is not str or len(value) != 66 or not value.startswith("0x"):
                raise TypeError(f"shadow receipt {field_name} must be a 32-byte hex digest")


FCISStepShadowResultV1: TypeAlias = FCISStepShadowReceiptV1 | FCISStepShadowRejectV1


@final
@dataclass(frozen=True, slots=True)
class _ExactLegacyStateProjectionV1:
    balances: CommittedBalanceTableV1
    pools: OwnedMapV1[str, CommittedPoolStateV1]
    lp_balances: CommittedLPTableV1
    nonces: CommittedNonceTableV1
    vault: CommittedVaultStateV1 | None
    oracle: CommittedOracleStateV1 | None
    fee_accumulator: CommittedFeeAccumulatorStateV1
    perps: CommittedPerpsStateV1 | None


def _admission_reason(prefix: str, reject: AdmitReject) -> str:
    return f"{prefix}: {reject.code.value}:{format_admit_path(reject.path)}"


def _legacy_mode_source_v1(mode: object) -> object:
    if type(mode) is not str:
        return mode
    if mode == "strong_replay":
        return FCISSettlementModeV1.STRONG_REPLAY
    if mode == "strong_proof_carrying":
        return FCISSettlementModeV1.STRONG_PROOF_CARRYING
    return mode


def _project_settlement_context_v1(
    source: object,
) -> FCISSettlementExecutionContextSourceV1 | AdmitReject:
    if type(source) is not FCISSpotShadowContextV1:
        return AdmitReject(AdmitCode.WRONG_EXACT_TYPE, ())
    try:
        return FCISSettlementExecutionContextSourceV1(
            now=object.__getattribute__(source, "now"),
            min_lp_position_age_seconds=object.__getattribute__(
                source,
                "min_lp_position_age_seconds",
            ),
            mode=_legacy_mode_source_v1(object.__getattribute__(source, "mode")),
            allow_cow_netting=object.__getattribute__(source, "allow_cow_netting"),
            allow_snapshot_bound_quote_bindings=object.__getattribute__(
                source,
                "allow_snapshot_bound_quote_bindings",
            ),
            protocol_fee_share_bps=object.__getattribute__(
                source,
                "protocol_fee_share_bps",
            ),
            protocol_fee_recipient_pubkey=object.__getattribute__(
                source,
                "protocol_fee_recipient_pubkey",
            ),
        )
    except AttributeError:
        return AdmitReject(AdmitCode.MISSING_FIELD, ())


def _project_fee_policy_v1(source: object) -> object:
    if source is None or type(source) is not FeeSplitParams:
        return source
    try:
        return FCISFeeSplitPolicySourceV1(
            buyback_bps=object.__getattribute__(source, "buyback_bps"),
            treasury_bps=object.__getattribute__(source, "treasury_bps"),
            rewards_bps=object.__getattribute__(source, "rewards_bps"),
        )
    except AttributeError:
        return source


def _admit_legacy_lp_policy_v1(
    source: object,
    *,
    prefix: str,
) -> LPDurationRiskPolicyV1 | None | FCISStepShadowRejectV1:
    result = admit_lp_duration_risk_policy_context_v1(source)
    if type(result) is AdmitReject:
        return FCISStepShadowRejectV1(
            FCISStepShadowPhaseV1.POLICY_ADMISSION,
            _admission_reason(prefix, result),
        )
    if type(result) is not AdmitOk:
        return FCISStepShadowRejectV1(
            FCISStepShadowPhaseV1.POLICY_ADMISSION,
            f"{prefix} returned an impossible result",
        )
    return result.value


def _admit_legacy_step_context_v1(
    context: object,
    lp_duration_policy: object,
) -> FCISStepExecutionContextV1 | FCISStepShadowRejectV1:
    if type(context) is not FCISStepShadowContextV1:
        return FCISStepShadowRejectV1(
            FCISStepShadowPhaseV1.POLICY_ADMISSION,
            "shadow context requires an exact FCISStepShadowContextV1",
        )
    settlement_source = _project_settlement_context_v1(
        object.__getattribute__(context, "settlement")
    )
    if type(settlement_source) is AdmitReject:
        return FCISStepShadowRejectV1(
            FCISStepShadowPhaseV1.POLICY_ADMISSION,
            _admission_reason("shadow context admission rejected", settlement_source),
        )
    exact_lp_policy = _admit_legacy_lp_policy_v1(
        lp_duration_policy,
        prefix="shadow LP duration-policy admission rejected",
    )
    if type(exact_lp_policy) is FCISStepShadowRejectV1:
        return exact_lp_policy
    step_source = FCISStepExecutionContextSourceV1(
        settlement=settlement_source,
        require_all_nonces=object.__getattribute__(context, "require_all_nonces"),
        reject_settlements_with_rejected_intents=object.__getattribute__(
            context,
            "reject_settlements_with_rejected_intents",
        ),
        fee_split_policy=_project_fee_policy_v1(
            object.__getattribute__(context, "fee_split_params")
        ),
        lp_duration_policy=exact_lp_policy,
        snapshot_version=object.__getattribute__(context, "snapshot_version"),
    )
    result = admit_fcis_step_execution_context_v1(step_source)
    if type(result) is AdmitReject:
        return FCISStepShadowRejectV1(
            FCISStepShadowPhaseV1.POLICY_ADMISSION,
            _admission_reason("shadow context admission rejected", result),
        )
    if type(result) is not AdmitOk or type(result.value) is not FCISStepExecutionContextV1:
        return FCISStepShadowRejectV1(
            FCISStepShadowPhaseV1.POLICY_ADMISSION,
            "shadow context admission returned an impossible result",
        )
    return result.value


def _admit_legacy_state_v1(
    state: DexState,
) -> _ExactLegacyStateProjectionV1 | FCISStepShadowRejectV1:
    field_name = "balances"
    try:
        balances = admit_legacy_balance_for_differential_v1(state.balances)
        field_name = "pools"
        pools = admit_legacy_pool_map_for_differential_v1(state.pools)
        field_name = "lp_balances"
        lp_balances = admit_legacy_lp_for_differential_v1(state.lp_balances)
        field_name = "nonces"
        nonces = admit_legacy_nonce_for_differential_v1(state.nonces)
        field_name = "vault"
        vault = snapshot_vault(state.vault)
        field_name = "oracle"
        oracle = snapshot_oracle(state.oracle)
        field_name = "fee_accumulator"
        fee_accumulator = snapshot_fee_accumulator(state.fee_accumulator)
        field_name = "perps"
        perps = snapshot_perps(state.perps)
    except StateAdmissionError as error:
        path = (field_name, *error.path)
        return FCISStepShadowRejectV1(
            FCISStepShadowPhaseV1.STATE_ADMISSION,
            f"shadow state admission rejected: {error.code.value}:{format_admit_path(path)}",
        )
    return _ExactLegacyStateProjectionV1(
        balances=balances,
        pools=pools,
        lp_balances=lp_balances,
        nonces=nonces,
        vault=vault,
        oracle=oracle,
        fee_accumulator=fee_accumulator,
        perps=perps,
    )


def _shadow_phase_v1(phase: FCISStepEvaluationPhaseV1) -> FCISStepShadowPhaseV1:
    if phase is FCISStepEvaluationPhaseV1.COMMAND_ADMISSION:
        return FCISStepShadowPhaseV1.COMMAND_ADMISSION
    if phase is FCISStepEvaluationPhaseV1.CONTEXT_ADMISSION:
        return FCISStepShadowPhaseV1.POLICY_ADMISSION
    if phase is FCISStepEvaluationPhaseV1.STATE_ADMISSION:
        return FCISStepShadowPhaseV1.STATE_ADMISSION
    if phase is FCISStepEvaluationPhaseV1.PRE_STATE_BINDING:
        return FCISStepShadowPhaseV1.PRE_STATE_BINDING
    if phase is FCISStepEvaluationPhaseV1.NONCE:
        return FCISStepShadowPhaseV1.NONCE
    if phase is FCISStepEvaluationPhaseV1.SETTLEMENT:
        return FCISStepShadowPhaseV1.SETTLEMENT
    if phase is FCISStepEvaluationPhaseV1.FEE:
        return FCISStepShadowPhaseV1.FEE
    return FCISStepShadowPhaseV1.ENCODING


def _shadow_result_v1(
    result: FCISStepEvaluationOkV1 | FCISStepEvaluationRejectV1,
) -> FCISStepShadowResultV1:
    if type(result) is FCISStepEvaluationRejectV1:
        return FCISStepShadowRejectV1(
            _shadow_phase_v1(result.phase),
            result.public_reason,
        )
    evidence = result.evidence
    return FCISStepShadowReceiptV1(
        snapshot_version=evidence.snapshot_version,
        canonical_snapshot_bytes=evidence.canonical_snapshot_bytes,
        state_root_preimage=evidence.post_state_root_preimage,
        state_root=evidence.post_state_root,
        support_root_version=evidence.support_root_version,
        support_root=evidence.support_root,
        snapshot_commitment=evidence.snapshot_commitment,
    )


def evaluate_fcis_spot_candidate_shadow_v1(
    *,
    state: DexState,
    settlement: Settlement,
    intents: list[Intent],
    context: object,
    lp_duration_policy: object,
) -> StrongSettlementEvaluationResultV1:
    """Project legacy shell inputs and delegate exact spot evaluation."""

    if type(state) is not DexState:
        return StrongSettlementRejectV1("shadow state requires an exact DexState")
    context_source = _project_settlement_context_v1(context)
    if type(context_source) is AdmitReject:
        return StrongSettlementRejectV1(
            _admission_reason("shadow context admission rejected", context_source)
        )
    context_result = admit_fcis_settlement_execution_context_v1(context_source)
    if type(context_result) is AdmitReject:
        return StrongSettlementRejectV1(
            _admission_reason("shadow context admission rejected", context_result)
        )
    policy = _admit_legacy_lp_policy_v1(
        lp_duration_policy,
        prefix="shadow LP duration-policy admission rejected",
    )
    if type(policy) is FCISStepShadowRejectV1:
        return StrongSettlementRejectV1(policy.reason)
    try:
        balances = admit_legacy_balance_for_differential_v1(state.balances)
        pools = admit_legacy_pool_map_for_differential_v1(state.pools)
        lp_balances = admit_legacy_lp_for_differential_v1(state.lp_balances)
    except StateAdmissionError as error:
        return StrongSettlementRejectV1(
            f"shadow state admission rejected: {error.code.value}:{format_admit_path(error.path)}"
        )
    if (
        type(context_result) is not AdmitOk
        or type(context_result.value) is not FCISSettlementExecutionContextV1
    ):
        return StrongSettlementRejectV1("shadow context admission returned an impossible result")
    return evaluate_fcis_spot_candidate_v1(
        balances=balances,
        pools=pools,
        lp_balances=lp_balances,
        settlement=settlement,
        intents=intents,
        context=context_result.value,
        lp_duration_policy=policy,
    )


def evaluate_fcis_step_shadow_v1(
    *,
    state: DexState,
    settlement: Settlement,
    intents: list[Intent],
    context: object,
    lp_duration_policy: object,
) -> FCISStepShadowResultV1:
    """Delegate one complete pre-M5 evaluation and hide its local candidate."""

    if type(state) is not DexState:
        return FCISStepShadowRejectV1(
            FCISStepShadowPhaseV1.STATE_ADMISSION,
            "shadow state requires an exact DexState",
        )
    if type(settlement) is not Settlement:
        return FCISStepShadowRejectV1(
            FCISStepShadowPhaseV1.COMMAND_ADMISSION,
            "shadow settlement requires an exact legacy Settlement",
        )
    if type(intents) is not list:
        return FCISStepShadowRejectV1(
            FCISStepShadowPhaseV1.COMMAND_ADMISSION,
            "shadow intents require an exact legacy list",
        )
    exact_context = _admit_legacy_step_context_v1(context, lp_duration_policy)
    if type(exact_context) is FCISStepShadowRejectV1:
        return exact_context
    exact_state = _admit_legacy_state_v1(state)
    if type(exact_state) is FCISStepShadowRejectV1:
        return exact_state
    command_field = "settlement"
    try:
        owned_settlement = snapshot_settlement(settlement)
        command_field = "intents"
        owned_intents = admit_intent_batch(intents)
    except StateAdmissionError as error:
        path = (command_field, *error.path)
        detail = f"{error.code.value}:{format_admit_path(path)}"
        return FCISStepShadowRejectV1(
            FCISStepShadowPhaseV1.COMMAND_ADMISSION,
            f"shadow command admission rejected: {detail}",
        )
    except (TypeError, ValueError):
        return FCISStepShadowRejectV1(
            FCISStepShadowPhaseV1.COMMAND_ADMISSION,
            (f"shadow command admission rejected: admission_rejected:{command_field}"),
        )
    result = evaluate_fcis_step_candidate_v1(
        balances=exact_state.balances,
        pools=exact_state.pools,
        lp_balances=exact_state.lp_balances,
        nonces=exact_state.nonces,
        vault=exact_state.vault,
        oracle=exact_state.oracle,
        fee_accumulator=exact_state.fee_accumulator,
        perps=exact_state.perps,
        settlement=owned_settlement,
        intents=owned_intents,
        context=exact_context,
    )
    return _shadow_result_v1(result)


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
