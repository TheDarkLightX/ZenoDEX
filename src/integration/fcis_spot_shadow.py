"""Read-only exact spot-candidate observation for the pre-M5 migration.

The normative migration forbids partially mounting exact spot fields while the
rest of ``DexState`` and its consumers remain on legacy values.  This module
therefore produces differential evidence only.  The mounted engine must not
import it, and its result does not authorize state publication.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import List, final

from ..core.dex import DexState
from ..core.settlement import Settlement
from ..core.settlement_strong_validator import (
    StrongSettlementEvaluationResultV1,
    StrongSettlementRejectV1,
    evaluate_settlement_strong_committed_v1,
)
from ..state.intents import Intent
from ..state.lp_duration_transitions import LPDurationRiskPolicyV1
from ..state.snapshot_combinators import AdmitOk, AdmitReject, format_admit_path
from ..state.state_snapshots import (
    StateAdmissionError,
    snapshot_balance_table,
    snapshot_lp_table,
    snapshot_pool_map,
)
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


def _admission_reject_text(prefix: str, reject: AdmitReject) -> str:
    return f"{prefix}: {reject.code.value}:{format_admit_path(reject.path)}"


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
    if type(context) is not FCISSpotShadowContextV1:
        return StrongSettlementRejectV1("shadow context requires an exact FCISSpotShadowContextV1")
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
        now=context.now,
        min_lp_position_age_seconds=context.min_lp_position_age_seconds,
        lp_duration_policy=exact_policy,
        mode=context.mode,
        allow_cow_netting=context.allow_cow_netting,
        allow_snapshot_bound_quote_bindings=context.allow_snapshot_bound_quote_bindings,
        protocol_fee_share_bps=context.protocol_fee_share_bps,
        protocol_fee_recipient_pubkey=context.protocol_fee_recipient_pubkey,
    )


__all__ = (
    "FCIS_SPOT_SHADOW_ONLY_V1",
    "FCISSpotShadowContextV1",
    "evaluate_fcis_spot_candidate_shadow_v1",
)
