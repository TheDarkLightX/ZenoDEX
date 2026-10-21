from __future__ import annotations

from dataclasses import replace
from pathlib import Path

from src.core.batch_clearing import apply_settlement_pure, compute_settlement
from src.core.dex import DexState
from src.core.fees import FeeAccumulatorState, FeeSplitParams, split_fee_with_dust_carry
from src.core.liquidity import create_pool
from src.core.perps import PERPS_STATE_VERSION_V4, PerpsState
from src.core.settlement import Settlement
from src.core.settlement_strong_validator import (
    StrongSettlementRejectV1,
    StrongSettlementStateCandidateV1,
    validate_settlement_strong,
)
from src.integration.dex_snapshot import snapshot_from_state
from src.integration.fcis_spot_shadow import (
    FCIS_SPOT_SHADOW_ONLY_V1,
    FCISSpotShadowContextV1,
    FCISStepShadowContextV1,
    FCISStepShadowPhaseV1,
    FCISStepShadowReceiptV1,
    FCISStepShadowRejectV1,
    evaluate_fcis_spot_candidate_shadow_v1,
    evaluate_fcis_step_shadow_v1,
)
from src.integration.lp_position_age_gate import (
    LPDurationRiskPolicy,
    apply_lp_mint_timestamps_after_settlement,
)
from src.state import BalanceTable, LPTable
from src.state.canonical import sha256_hex
from src.state.intents import Intent, IntentKind
from src.state.nonces import NonceTable, validate_and_apply_intent_nonce_batch
from src.state.state_root import state_root_preimage
from src.state.state_snapshots import (
    snapshot_balance_table,
    snapshot_lp_table,
    snapshot_pool_map,
)
from src.state.support_root import compute_support_state_root_for_batch
from tools.check_fcis_authority_snapshot_contract import (
    DEFAULT_AUTHORITY_PATHS,
    check_contract,
)

_EXPECTED_SWAP_POST_SUPPORT_ROOT = (
    "0x66c43d933bdf3105ea34adb2adf9fc43745b18fd70693998eda71e44d213dbcf"
)


def _iid(value: int) -> str:
    return "0x" + f"{value:064x}"


def _add_liquidity_case() -> tuple[
    DexState,
    Intent,
    Settlement,
    str,
    LPDurationRiskPolicy,
]:
    owner = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool_id, pool, lp_minted = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=owner,
    )
    balances = BalanceTable()
    balances.set(owner, asset0, 10_000_000)
    balances.set(owner, asset1, 10_000_000)
    lp_balances = LPTable()
    lp_balances.set(owner, pool_id, lp_minted)
    lp_balances.set("0x" + "00" * 48, pool_id, pool.lp_supply - lp_minted)
    lp_balances.set_last_mint_timestamp(owner, pool_id, 100)
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.ADD_LIQUIDITY,
        intent_id=_iid(1),
        sender_pubkey=owner,
        deadline=10_000,
        fields={
            "pool_id": pool_id,
            "amount0_desired": 100_000,
            "amount1_desired": 100_000,
            "amount0_min": 0,
            "amount1_min": 0,
        },
    )
    state = DexState(
        balances=balances,
        pools={pool_id: pool},
        lp_balances=lp_balances,
    )
    settlement = compute_settlement(
        [intent],
        state.pools,
        state.balances,
        state.lp_balances,
    )
    policy = LPDurationRiskPolicy(
        base_age_seconds=60,
        max_age_seconds=3_600,
        churn_window_seconds=600,
        decay_seconds=900,
        multiplier=2,
        max_churn_tier=5,
    )
    return state, intent, settlement, pool_id, policy


def _shadow(
    *,
    state: DexState,
    intent: Intent,
    settlement: Settlement,
    policy: object,
) -> StrongSettlementStateCandidateV1 | StrongSettlementRejectV1:
    return evaluate_fcis_spot_candidate_shadow_v1(
        state=state,
        settlement=settlement,
        intents=[intent],
        context=FCISSpotShadowContextV1(
            now=700,
            min_lp_position_age_seconds=0,
            mode="strong_replay",
            allow_cow_netting=False,
            allow_snapshot_bound_quote_bindings=False,
            protocol_fee_share_bps=0,
            protocol_fee_recipient_pubkey=None,
        ),
        lp_duration_policy=policy,
    )


def _step_context(
    policy: LPDurationRiskPolicy,
    *,
    require_all_nonces: bool = True,
) -> tuple[FCISStepShadowContextV1, LPDurationRiskPolicy]:
    return (
        FCISStepShadowContextV1(
            settlement=FCISSpotShadowContextV1(
                now=700,
                min_lp_position_age_seconds=0,
                mode="strong_replay",
                allow_cow_netting=False,
                allow_snapshot_bound_quote_bindings=False,
                protocol_fee_share_bps=0,
                protocol_fee_recipient_pubkey=None,
            ),
            require_all_nonces=require_all_nonces,
            reject_settlements_with_rejected_intents=True,
            fee_split_params=FeeSplitParams(3_333, 3_333, 3_334),
            snapshot_version=4,
        ),
        policy,
    )


def _swap_case() -> tuple[DexState, Intent, Settlement, LPDurationRiskPolicy]:
    state, add_intent, _settlement, pool_id, policy = _add_liquidity_case()
    swap_intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(2),
        sender_pubkey=add_intent.sender_pubkey,
        deadline=10_000,
        fields={
            "pool_id": pool_id,
            "asset_in": state.pools[pool_id].asset0,
            "asset_out": state.pools[pool_id].asset1,
            "amount_in": 100_000,
            "min_amount_out": 1,
            "nonce": 1,
        },
    )
    settlement = compute_settlement(
        [swap_intent],
        state.pools,
        state.balances,
        state.lp_balances,
    )
    return state, swap_intent, settlement, policy


def test_shadow_candidate_matches_legacy_add_and_duration_application() -> None:
    state, intent, settlement, pool_id, policy = _add_liquidity_case()
    pre_balances = snapshot_balance_table(state.balances)
    pre_pools = snapshot_pool_map(state.pools)
    pre_lp = snapshot_lp_table(state.lp_balances)

    observed = _shadow(
        state=state,
        intent=intent,
        settlement=settlement,
        policy=policy,
    )

    assert type(observed) is StrongSettlementStateCandidateV1
    next_balances, next_pools, next_lp = apply_settlement_pure(
        settlement=settlement,
        balances=state.balances,
        pools=state.pools,
        lp_balances=state.lp_balances,
    )
    assert (
        apply_lp_mint_timestamps_after_settlement(
            lp_balances=next_lp,
            settlement=settlement,
            block_timestamp=700,
            duration_risk_policy=policy,
        )
        is None
    )
    assert observed.balances == snapshot_balance_table(next_balances)
    assert observed.pools == snapshot_pool_map(next_pools)
    assert observed.lp_balances == snapshot_lp_table(next_lp)
    assert observed.lp_balances.get_last_mint_timestamp(intent.sender_pubkey, pool_id) == 700
    assert snapshot_balance_table(state.balances) == pre_balances
    assert snapshot_pool_map(state.pools) == pre_pools
    assert snapshot_lp_table(state.lp_balances) == pre_lp


def test_shadow_replay_rejection_matches_the_legacy_strong_validator() -> None:
    state, intent, settlement, _pool_id, policy = _add_liquidity_case()
    tampered = replace(settlement, balance_deltas=[])

    observed = _shadow(
        state=state,
        intent=intent,
        settlement=tampered,
        policy=policy,
    )
    legacy = validate_settlement_strong(
        settlement=tampered,
        intents=[intent],
        pre_balances=state.balances,
        pre_pools=state.pools,
        pre_lp_balances=state.lp_balances,
    )

    assert type(observed) is StrongSettlementRejectV1
    assert legacy == (False, observed.reason)
    assert not hasattr(observed, "balances")


def test_full_step_shadow_matches_legacy_state_snapshot_and_root() -> None:
    state, intent, settlement, policy = _swap_case()
    context, policy = _step_context(policy)
    pre_snapshot = snapshot_from_state(state).canonical_bytes()

    observed = evaluate_fcis_step_shadow_v1(
        state=state,
        settlement=settlement,
        intents=[intent],
        context=context,
        lp_duration_policy=policy,
    )

    assert type(observed) is FCISStepShadowReceiptV1
    nonce_ok, nonce_error, next_nonces = validate_and_apply_intent_nonce_batch(
        nonces=state.nonces,
        intents=[intent],
        require_all_nonces=True,
    )
    assert nonce_ok is True
    assert nonce_error is None
    assert type(next_nonces) is NonceTable
    next_balances, next_pools, next_lp = apply_settlement_pure(
        settlement=settlement,
        balances=state.balances,
        pools=state.pools,
        lp_balances=state.lp_balances,
    )
    assert (
        apply_lp_mint_timestamps_after_settlement(
            lp_balances=next_lp,
            settlement=settlement,
            block_timestamp=700,
            duration_risk_policy=policy,
        )
        is None
    )
    total_fees = sum(fill.fee_paid or 0 for fill in settlement.fills)
    _allocation, next_fees = split_fee_with_dust_carry(
        total_fees,
        context.fee_split_params,
        state.fee_accumulator,
    )
    legacy_next = DexState(
        balances=next_balances,
        pools=next_pools,
        lp_balances=next_lp,
        nonces=next_nonces,
        vault=state.vault,
        oracle=state.oracle,
        fee_accumulator=next_fees,
        perps=state.perps,
    )
    legacy_snapshot = snapshot_from_state(
        legacy_next,
        version=context.snapshot_version,
    )
    legacy_preimage = state_root_preimage(
        balances=legacy_next.balances,
        pools=legacy_next.pools,
        lp_balances=legacy_next.lp_balances,
        nonces=legacy_next.nonces,
        fee_accumulator=legacy_next.fee_accumulator,
    )

    assert observed.canonical_snapshot_bytes == legacy_snapshot.canonical_bytes()
    assert observed.snapshot_commitment == legacy_snapshot.commitment_hex()
    assert observed.state_root_preimage == legacy_preimage
    assert observed.state_root == sha256_hex(legacy_preimage)
    assert observed.support_root == compute_support_state_root_for_batch(
        intents=[intent],
        balances=legacy_next.balances,
        pools=legacy_next.pools,
        lp_balances=legacy_next.lp_balances,
        nonces=legacy_next.nonces,
    )
    assert observed.support_root == _EXPECTED_SWAP_POST_SUPPORT_ROOT
    assert snapshot_from_state(state).canonical_bytes() == pre_snapshot
    assert not hasattr(observed, "balances")
    assert not hasattr(observed, "nonces")
    assert not hasattr(observed, "fee_accumulator")


def test_full_step_shadow_nonce_rejection_precedes_settlement_rejection() -> None:
    state, intent, settlement, _pool_id, policy = _add_liquidity_case()
    context, policy = _step_context(policy, require_all_nonces=True)
    tampered = replace(settlement, balance_deltas=[])

    observed = evaluate_fcis_step_shadow_v1(
        state=state,
        settlement=tampered,
        intents=[intent],
        context=context,
        lp_duration_policy=policy,
    )

    assert observed == FCISStepShadowRejectV1(
        FCISStepShadowPhaseV1.NONCE,
        "Missing/invalid nonce",
    )
    assert not hasattr(observed, "canonical_snapshot_bytes")
    assert not hasattr(observed, "state_root")


def test_full_step_shadow_settlement_rejection_has_no_candidate_evidence() -> None:
    state, intent, settlement, policy = _swap_case()
    context, policy = _step_context(policy)
    tampered = replace(settlement, balance_deltas=[])
    pre_snapshot = snapshot_from_state(state).canonical_bytes()

    observed = evaluate_fcis_step_shadow_v1(
        state=state,
        settlement=tampered,
        intents=[intent],
        context=context,
        lp_duration_policy=policy,
    )

    assert type(observed) is FCISStepShadowRejectV1
    assert observed.phase is FCISStepShadowPhaseV1.SETTLEMENT
    assert not hasattr(observed, "canonical_snapshot_bytes")
    assert not hasattr(observed, "state_root_preimage")
    assert snapshot_from_state(state).canonical_bytes() == pre_snapshot


def test_full_step_shadow_preserves_the_mounted_rejected_intent_policy() -> None:
    state, intent, _settlement, policy = _swap_case()
    rejected_intent = replace(
        intent,
        fields={key: value for key, value in intent.fields.items() if key != "asset_out"},
    )
    rejected_settlement = compute_settlement(
        [rejected_intent],
        state.pools,
        state.balances,
        state.lp_balances,
    )
    context, policy = _step_context(policy)

    observed = evaluate_fcis_step_shadow_v1(
        state=state,
        settlement=rejected_settlement,
        intents=[rejected_intent],
        context=context,
        lp_duration_policy=policy,
    )

    assert observed == FCISStepShadowRejectV1(
        FCISStepShadowPhaseV1.SETTLEMENT,
        f"settlement rejected intent_id={rejected_intent.intent_id}: MISSING_PARAMS",
    )


def test_full_step_shadow_invalid_eighth_field_rejects_without_partial_evidence() -> None:
    state, intent, settlement, policy = _swap_case()
    state_with_perps = DexState(
        balances=state.balances,
        pools=state.pools,
        lp_balances=state.lp_balances,
        nonces=state.nonces,
        vault=state.vault,
        oracle=state.oracle,
        fee_accumulator=FeeAccumulatorState(),
        perps=PerpsState(version=PERPS_STATE_VERSION_V4, markets={}),
    )
    assert state_with_perps.perps is not None
    object.__setattr__(state_with_perps.perps, "version", True)
    context, policy = _step_context(policy)

    observed = evaluate_fcis_step_shadow_v1(
        state=state_with_perps,
        settlement=settlement,
        intents=[intent],
        context=context,
        lp_duration_policy=policy,
    )

    assert type(observed) is FCISStepShadowRejectV1
    assert observed.phase is FCISStepShadowPhaseV1.STATE_ADMISSION
    assert "perps" in observed.reason
    assert not hasattr(observed, "canonical_snapshot_bytes")


def test_full_step_shadow_readmits_corrupted_context_without_candidate_escape() -> None:
    state, intent, settlement, policy = _swap_case()
    context, policy = _step_context(policy)
    object.__setattr__(context.settlement, "allow_cow_netting", 1)

    observed = evaluate_fcis_step_shadow_v1(
        state=state,
        settlement=settlement,
        intents=[intent],
        context=context,
        lp_duration_policy=policy,
    )

    assert type(observed) is FCISStepShadowRejectV1
    assert observed.phase is FCISStepShadowPhaseV1.POLICY_ADMISSION
    assert "allow_cow_netting must be an exact bool" in observed.reason
    assert not hasattr(observed, "canonical_snapshot_bytes")


def test_shadow_rejects_corrupt_policy_without_state_candidate() -> None:
    state, intent, settlement, _pool_id, policy = _add_liquidity_case()
    object.__setattr__(policy, "multiplier", True)

    observed = _shadow(
        state=state,
        intent=intent,
        settlement=settlement,
        policy=policy,
    )

    assert observed == StrongSettlementRejectV1(
        'shadow LP duration-policy admission rejected: wrong_exact_type:$["multiplier"]'
    )
    assert not hasattr(observed, "balances")


def test_shadow_module_is_not_mounted_as_an_authority_dependency() -> None:
    assert FCIS_SPOT_SHADOW_ONLY_V1 is True
    repository_root = Path(__file__).resolve().parents[2]
    report = check_contract(
        repo_root=repository_root,
        authority_paths=DEFAULT_AUTHORITY_PATHS,
        requirements_path=None,
        test_matrix_paths=(),
    )
    violations = report["violations"]
    assert type(violations) is list
    assert not any(item["code"] == "SHADOW_AUTHORITY_IMPORT" for item in violations)
