from __future__ import annotations

from dataclasses import replace
from pathlib import Path

from src.core.batch_clearing import apply_settlement_pure, compute_settlement
from src.core.dex import DexState
from src.core.liquidity import create_pool
from src.core.settlement import Settlement
from src.core.settlement_strong_validator import (
    StrongSettlementRejectV1,
    StrongSettlementStateCandidateV1,
    validate_settlement_strong,
)
from src.integration.fcis_spot_shadow import (
    FCIS_SPOT_SHADOW_ONLY_V1,
    FCISSpotShadowContextV1,
    evaluate_fcis_spot_candidate_shadow_v1,
)
from src.integration.lp_position_age_gate import (
    LPDurationRiskPolicy,
    apply_lp_mint_timestamps_after_settlement,
)
from src.state import BalanceTable, LPTable
from src.state.intents import Intent, IntentKind
from src.state.state_snapshots import (
    snapshot_balance_table,
    snapshot_lp_table,
    snapshot_pool_map,
)
from tools.check_fcis_authority_snapshot_contract import (
    DEFAULT_AUTHORITY_PATHS,
    check_contract,
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
