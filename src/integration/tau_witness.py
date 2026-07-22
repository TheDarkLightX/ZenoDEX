"""
Tau witness builders (pure, no IO).

These helpers turn Python integers into the exact input streams expected by
selected Tau specs (hi/lo limbs, etc.).
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Dict

from .tau_runner import split_u32

PROJECT_ROOT = Path(__file__).resolve().parents[2]
TAU_SPECS_DIR = PROJECT_ROOT / "src" / "tau_specs"
RECOMMENDED_SPECS_DIR = PROJECT_ROOT / "src" / "tau_specs" / "recommended"

TAU_WITNESS_SCHEMA_VERSION = 1


@dataclass(frozen=True)
class TauSpecRef:
    spec_id: str
    path: Path
    gate_output: str


def _u16(name: str, v: int) -> int:
    if not isinstance(v, int) or isinstance(v, bool) or v < 0 or v > 0xFFFF:
        raise ValueError(f"{name} out of u16 range: {v!r}")
    return int(v)


def _u32(name: str, v: int) -> tuple[int, int]:
    if not isinstance(v, int) or isinstance(v, bool) or v < 0 or v > 0xFFFFFFFF:
        raise ValueError(f"{name} out of u32 range: {v!r}")
    return split_u32(int(v))


def _bv32(name: str, v: int) -> int:
    if not isinstance(v, int) or isinstance(v, bool) or v < 0 or v > 0xFFFFFFFF:
        raise ValueError(f"{name} out of bv[32] range: {v!r}")
    return int(v)


def _u64(name: str, v: int) -> int:
    if not isinstance(v, int) or isinstance(v, bool) or v < 0 or v > 0xFFFFFFFFFFFFFFFF:
        raise ValueError(f"{name} out of u64 range: {v!r}")
    return int(v)


def _sbf(name: str, v: int) -> int:
    if v not in (0, 1):
        raise ValueError(f"{name} must be 0 or 1, got {v!r}")
    return int(v)


def _computed_sbf(name: str, override: int | None, value: bool) -> int:
    if override is None:
        return 1 if value else 0
    return _sbf(name, override)


CPMM_V1 = TauSpecRef(
    spec_id="cpmm_v1",
    path=RECOMMENDED_SPECS_DIR / "cpmm_v1.tau",
    gate_output="o1",
)

NONCE_REPLAY_GUARD_V1 = TauSpecRef(
    spec_id="nonce_replay_guard_v1",
    path=RECOMMENDED_SPECS_DIR / "nonce_replay_guard_v1.tau",
    gate_output="o4",
)

INTENT_EXPIRY_GUARD_V1 = TauSpecRef(
    spec_id="intent_expiry_guard_v1",
    path=RECOMMENDED_SPECS_DIR / "intent_expiry_guard_v1.tau",
    gate_output="o4",
)

ZUSD_ORACLE_COMMIT_GUARD_V2 = TauSpecRef(
    spec_id="zusd_oracle_commit_guard_v2",
    path=RECOMMENDED_SPECS_DIR / "zusd_oracle_commit_guard_v2.tau",
    gate_output="o4",
)

ZUSD_CROSS_MODULE_ORACLE_SYNC_GATE_V1 = TauSpecRef(
    spec_id="zusd_cross_module_oracle_sync_gate_v1",
    path=RECOMMENDED_SPECS_DIR / "zusd_cross_module_oracle_sync_gate_v1.tau",
    gate_output="o2",
)

ZUSD_TRANSFER_GUARD_V1 = TauSpecRef(
    spec_id="zusd_transfer_guard_v1",
    path=RECOMMENDED_SPECS_DIR / "zusd_transfer_guard_v1.tau",
    gate_output="o4",
)

ZUSD_LIQUIDATION_GUARD_V2 = TauSpecRef(
    spec_id="zusd_liquidation_guard_v2",
    path=RECOMMENDED_SPECS_DIR / "zusd_liquidation_guard_v2.tau",
    gate_output="o4",
)

ZUSD_SUPPLY_CONSERVATION_V2 = TauSpecRef(
    spec_id="zusd_supply_conservation_v2",
    path=RECOMMENDED_SPECS_DIR / "zusd_supply_conservation_v2.tau",
    gate_output="o4",
)

ZUSD_MINT_GUARD_V1 = TauSpecRef(
    spec_id="zusd_mint_guard_v1",
    path=RECOMMENDED_SPECS_DIR / "zusd_mint_guard_v1.tau",
    gate_output="o4",
)

ZUSD_REPAY_GUARD_V1 = TauSpecRef(
    spec_id="zusd_repay_guard_v1",
    path=RECOMMENDED_SPECS_DIR / "zusd_repay_guard_v1.tau",
    gate_output="o4",
)

ZUSD_REDEEM_GUARD_V1 = TauSpecRef(
    spec_id="zusd_redeem_guard_v1",
    path=RECOMMENDED_SPECS_DIR / "zusd_redeem_guard_v1.tau",
    gate_output="o4",
)

ZUSD_WITHDRAW_COLLATERAL_GUARD_V1 = TauSpecRef(
    spec_id="zusd_withdraw_collateral_guard_v1",
    path=RECOMMENDED_SPECS_DIR / "zusd_withdraw_collateral_guard_v1.tau",
    gate_output="o4",
)

ZUSD_DEPOSIT_SP_GUARD_V1 = TauSpecRef(
    spec_id="zusd_deposit_sp_guard_v1",
    path=RECOMMENDED_SPECS_DIR / "zusd_deposit_sp_guard_v1.tau",
    gate_output="o4",
)

ZUSD_WITHDRAW_SP_GUARD_V1 = TauSpecRef(
    spec_id="zusd_withdraw_sp_guard_v1",
    path=RECOMMENDED_SPECS_DIR / "zusd_withdraw_sp_guard_v1.tau",
    gate_output="o4",
)

TOKEN_ARCHETYPE_SOULBOUND_V2 = TauSpecRef(
    spec_id="token_archetype_soulbound_v2",
    path=RECOMMENDED_SPECS_DIR / "token_archetype_soulbound_v2.tau",
    gate_output="o4",
)

TOKEN_ARCHETYPE_LOCK_WEIGHTED_REWARDS_32_V1 = TauSpecRef(
    spec_id="token_archetype_lock_weighted_rewards_32_v1",
    path=RECOMMENDED_SPECS_DIR / "token_archetype_lock_weighted_rewards_32_v1.tau",
    gate_output="o3",
)

TOKEN_ARCHETYPE_LOCK_WEIGHTED_REWARDS_32_V2 = TauSpecRef(
    spec_id="token_archetype_lock_weighted_rewards_32_v2",
    path=RECOMMENDED_SPECS_DIR / "token_archetype_lock_weighted_rewards_32_v2.tau",
    gate_output="o3",
)

TOKEN_ARCHETYPE_VESTING_CLIFF_32_V1 = TauSpecRef(
    spec_id="token_archetype_vesting_cliff_32_v1",
    path=RECOMMENDED_SPECS_DIR / "token_archetype_vesting_cliff_32_v1.tau",
    gate_output="o3",
)

TOKEN_ARCHETYPE_VESTING_CLIFF_32_V2 = TauSpecRef(
    spec_id="token_archetype_vesting_cliff_32_v2",
    path=RECOMMENDED_SPECS_DIR / "token_archetype_vesting_cliff_32_v2.tau",
    gate_output="o3",
)

SWAP_EXACT_IN_V4 = TauSpecRef(
    spec_id="swap_exact_in_v4",
    path=TAU_SPECS_DIR / "swap_exact_in_v4.tau",
    gate_output="o1",
)

SWAP_EXACT_OUT_V4 = TauSpecRef(
    spec_id="swap_exact_out_v4",
    path=TAU_SPECS_DIR / "swap_exact_out_v4.tau",
    gate_output="o1",
)

SWAP_EXACT_IN_V3 = TauSpecRef(
    spec_id="swap_exact_in_v3",
    path=TAU_SPECS_DIR / "swap_exact_in_v3.tau",
    gate_output="o1",
)

SWAP_EXACT_OUT_V3 = TauSpecRef(
    spec_id="swap_exact_out_v3",
    path=TAU_SPECS_DIR / "swap_exact_out_v3.tau",
    gate_output="o1",
)

SWAP_EXACT_IN_V1 = TauSpecRef(
    spec_id="swap_exact_in_v1",
    path=RECOMMENDED_SPECS_DIR / "swap_exact_in_v1.tau",
    gate_output="o1",
)

SWAP_EXACT_OUT_V1 = TauSpecRef(
    spec_id="swap_exact_out_v1",
    path=RECOMMENDED_SPECS_DIR / "swap_exact_out_v1.tau",
    gate_output="o1",
)

SWAP_EXACT_IN_PROOF_GATE_V1 = TauSpecRef(
    spec_id="swap_exact_in_proof_gate_v1",
    path=RECOMMENDED_SPECS_DIR / "swap_exact_in_proof_gate_v1.tau",
    gate_output="o1",
)

SWAP_EXACT_OUT_PROOF_GATE_V1 = TauSpecRef(
    spec_id="swap_exact_out_proof_gate_v1",
    path=RECOMMENDED_SPECS_DIR / "swap_exact_out_proof_gate_v1.tau",
    gate_output="o1",
)

SWAP_EXACT_IN_FEE_PROOF_GATE_V1 = TauSpecRef(
    spec_id="swap_exact_in_fee_proof_gate_v1",
    path=RECOMMENDED_SPECS_DIR / "swap_exact_in_fee_proof_gate_v1.tau",
    gate_output="o1",
)

SWAP_EXACT_OUT_FEE_PROOF_GATE_V1 = TauSpecRef(
    spec_id="swap_exact_out_fee_proof_gate_v1",
    path=RECOMMENDED_SPECS_DIR / "swap_exact_out_fee_proof_gate_v1.tau",
    gate_output="o1",
)

SWAP_FEE_TOTAL_CEIL_V1 = TauSpecRef(
    spec_id="swap_fee_total_ceil_v1",
    path=RECOMMENDED_SPECS_DIR / "swap_fee_total_ceil_v1.tau",
    gate_output="o1",
)

PROTOCOL_FEE_FLOOR_V1 = TauSpecRef(
    spec_id="protocol_fee_floor_v1",
    path=RECOMMENDED_SPECS_DIR / "protocol_fee_floor_v1.tau",
    gate_output="o1",
)

SWAP_EXACT_IN_PROTOCOL_FEE_APPLY_V1 = TauSpecRef(
    spec_id="swap_exact_in_protocol_fee_apply_v1",
    path=RECOMMENDED_SPECS_DIR / "swap_exact_in_protocol_fee_apply_v1.tau",
    gate_output="o1",
)

SWAP_EXACT_OUT_PROTOCOL_FEE_APPLY_V1 = TauSpecRef(
    spec_id="swap_exact_out_protocol_fee_apply_v1",
    path=RECOMMENDED_SPECS_DIR / "swap_exact_out_protocol_fee_apply_v1.tau",
    gate_output="o1",
)

LP_BURN_FLOOR_MATH_GUARD_V1 = TauSpecRef(
    spec_id="lp_burn_floor_math_guard_v1",
    path=RECOMMENDED_SPECS_DIR / "lp_burn_floor_math_guard_v1.tau",
    gate_output="o1",
)

LP_MINT_MIN_OF_FLOORS_GUARD_V1 = TauSpecRef(
    spec_id="lp_mint_min_of_floors_guard_v1",
    path=RECOMMENDED_SPECS_DIR / "lp_mint_min_of_floors_guard_v1.tau",
    gate_output="o1",
)

CREATE_POOL_INITIAL_SQRT_GUARD_V1 = TauSpecRef(
    spec_id="create_pool_initial_sqrt_guard_v1",
    path=RECOMMENDED_SPECS_DIR / "create_pool_initial_sqrt_guard_v1.tau",
    gate_output="o1",
)

PRICE_IMPACT_GUARD_V1 = TauSpecRef(
    spec_id="price_impact_guard_v1",
    path=RECOMMENDED_SPECS_DIR / "price_impact_guard_v1.tau",
    gate_output="o1",
)

OPTIMAL_CHOICE_CERTIFICATE_V1 = TauSpecRef(
    spec_id="optimal_choice_certificate_v1",
    path=RECOMMENDED_SPECS_DIR / "optimal_choice_certificate_v1.tau",
    gate_output="o1",
)

ARGMIN_STREAM_CERTIFICATE_V1 = TauSpecRef(
    spec_id="argmin_stream_certificate_v1",
    path=RECOMMENDED_SPECS_DIR / "argmin_stream_certificate_v1.tau",
    gate_output="o1",
)

ARGMAX_STREAM_CERTIFICATE_V1 = TauSpecRef(
    spec_id="argmax_stream_certificate_v1",
    path=RECOMMENDED_SPECS_DIR / "argmax_stream_certificate_v1.tau",
    gate_output="o1",
)

POOL_PARAMS_BINDING_GUARD_V1 = TauSpecRef(
    spec_id="pool_params_binding_guard_v1",
    path=RECOMMENDED_SPECS_DIR / "pool_params_binding_guard_v1.tau",
    gate_output="o1",
)

ADD_LIQUIDITY_RATIO_GUARD_V1 = TauSpecRef(
    spec_id="add_liquidity_ratio_guard_v1",
    path=RECOMMENDED_SPECS_DIR / "add_liquidity_ratio_guard_v1.tau",
    gate_output="o1",
)

ADD_LIQUIDITY_APPLY_V1 = TauSpecRef(
    spec_id="add_liquidity_apply_v1",
    path=RECOMMENDED_SPECS_DIR / "add_liquidity_apply_v1.tau",
    gate_output="o1",
)

REMOVE_LIQUIDITY_APPLY_V1 = TauSpecRef(
    spec_id="remove_liquidity_apply_v1",
    path=RECOMMENDED_SPECS_DIR / "remove_liquidity_apply_v1.tau",
    gate_output="o1",
)

CREATE_POOL_APPLY_PROOF_GATE_V1 = TauSpecRef(
    spec_id="create_pool_apply_proof_gate_v1",
    path=RECOMMENDED_SPECS_DIR / "create_pool_apply_proof_gate_v1.tau",
    gate_output="o1",
)

SETTLEMENT_V1 = TauSpecRef(
    spec_id="settlement_v1",
    path=TAU_SPECS_DIR / "settlement_v1.tau",
    gate_output="o7",
)

SETTLEMENT_V1_PROOF_GATE = TauSpecRef(
    spec_id="settlement_v1_proof_gate",
    path=RECOMMENDED_SPECS_DIR / "settlement_v1_proof_gate.tau",
    gate_output="o7",
)

TOKEN_COMPOSITE_V1 = TauSpecRef(
    spec_id="token_composite_v1",
    path=TAU_SPECS_DIR / "token_composite_v1.tau",
    gate_output="o4",
)

TOKEN_COMPOSITE_V2 = TauSpecRef(
    spec_id="token_composite_v2",
    path=RECOMMENDED_SPECS_DIR / "token_composite_v2.tau",
    gate_output="o4",
)

BALANCE_SAFETY_V1 = TauSpecRef(
    spec_id="balance_safety_v1",
    path=TAU_SPECS_DIR / "balance_safety_v1.tau",
    gate_output="o1",
)

BALANCE_TRANSITION_V1 = TauSpecRef(
    spec_id="balance_transition_v1",
    path=RECOMMENDED_SPECS_DIR / "balance_transition_v1.tau",
    gate_output="o1",
)

BATCHING_V1 = TauSpecRef(
    spec_id="batching_v1",
    path=TAU_SPECS_DIR / "batching_v1.tau",
    gate_output="o1",
)

BATCHING_V1_4 = TauSpecRef(
    spec_id="batching_v1_4",
    path=TAU_SPECS_DIR / "batching_v1_4.tau",
    gate_output="o1",
)

BATCHING_V1_5_COMPACT_SINGLE_GATE = TauSpecRef(
    spec_id="batching_v1_5_compact_single_gate",
    path=RECOMMENDED_SPECS_DIR / "batching_v1_5_compact_single_gate.tau",
    gate_output="o1",
)

BATCHING_ALL_DISTINCT_4_V1 = TauSpecRef(
    spec_id="batching_all_distinct_4_v1",
    path=RECOMMENDED_SPECS_DIR / "batching_all_distinct_4_v1.tau",
    gate_output="o1",
)

BATCHING_LEFT_IN_RIGHT_4_V1 = TauSpecRef(
    spec_id="batching_left_in_right_4_v1",
    path=RECOMMENDED_SPECS_DIR / "batching_left_in_right_4_v1.tau",
    gate_output="o1",
)

BATCHING_EXECUTED_SORTED_4_V1 = TauSpecRef(
    spec_id="batching_executed_sorted_4_v1",
    path=RECOMMENDED_SPECS_DIR / "batching_executed_sorted_4_v1.tau",
    gate_output="o1",
)

BATCH_CANONICAL_V1_4 = TauSpecRef(
    spec_id="batch_canonical_v1_4",
    path=TAU_SPECS_DIR / "batch_canonical_v1_4.tau",
    gate_output="o1",
)

TOKENOMICS_BUYBACK_BURN_V1 = TauSpecRef(
    spec_id="tokenomics_buyback_burn_v1",
    path=TAU_SPECS_DIR / "tokenomics_buyback_burn_v1.tau",
    gate_output="o1",
)

TOKENOMICS_BUYBACK_BURN_V2 = TauSpecRef(
    spec_id="tokenomics_buyback_burn_v2",
    path=RECOMMENDED_SPECS_DIR / "tokenomics_buyback_burn_v2.tau",
    gate_output="o1",
)

BURN_RECEIPT_REPLAY_GUARD_V1 = TauSpecRef(
    spec_id="burn_receipt_replay_guard_v1",
    path=RECOMMENDED_SPECS_DIR / "burn_receipt_replay_guard_v1.tau",
    gate_output="o1",
)

CONFIDENTIAL_EXTENSION_LIVE_ADMISSION_V1 = TauSpecRef(
    spec_id="confidential_extension_live_admission_v1",
    path=RECOMMENDED_SPECS_DIR / "confidential_extension_live_admission_v1.tau",
    gate_output="o1",
)

BURN_RECEIPT_AMOUNT_GUARD_V1 = TauSpecRef(
    spec_id="burn_receipt_amount_guard_v1",
    path=RECOMMENDED_SPECS_DIR / "burn_receipt_amount_guard_v1.tau",
    gate_output="o1",
)

BURN_RECEIPT_SUPPLY_GUARD_V1 = TauSpecRef(
    spec_id="burn_receipt_supply_guard_v1",
    path=RECOMMENDED_SPECS_DIR / "burn_receipt_supply_guard_v1.tau",
    gate_output="o1",
)

BURN_RECEIPT_BATCH_SUM_GUARD_V1 = TauSpecRef(
    spec_id="burn_receipt_batch_sum_guard_v1",
    path=RECOMMENDED_SPECS_DIR / "burn_receipt_batch_sum_guard_v1.tau",
    gate_output="o1",
)

PROTOCOL_TOKEN_V1 = TauSpecRef(
    spec_id="protocol_token_v1",
    path=RECOMMENDED_SPECS_DIR / "protocol_token_v1.tau",
    gate_output="o1",
)

AUTOTRADER_BUDGET_GUARD_V1 = TauSpecRef(
    spec_id="autotrader_budget_guard_v1",
    path=RECOMMENDED_SPECS_DIR / "autotrader_budget_guard_v1.tau",
    gate_output="o1",
)

AUTOTRADER_COMPILE_CONTRACT_V1 = TauSpecRef(
    spec_id="autotrader_compile_contract_v1",
    path=RECOMMENDED_SPECS_DIR / "autotrader_compile_contract_v1.tau",
    gate_output="o1",
)

AUTOTRADER_COMPILATION_WITNESS_V1 = TauSpecRef(
    spec_id="autotrader_compilation_witness_v1",
    path=RECOMMENDED_SPECS_DIR / "autotrader_compilation_witness_v1.tau",
    gate_output="o1",
)

AUTOTRADER_EXECUTION_GUARD_V1 = TauSpecRef(
    spec_id="autotrader_execution_guard_v1",
    path=RECOMMENDED_SPECS_DIR / "autotrader_execution_guard_v1.tau",
    gate_output="o1",
)

AUTOTRADER_ORACLE_FRESHNESS_GUARD_V1 = TauSpecRef(
    spec_id="autotrader_oracle_freshness_guard_v1",
    path=RECOMMENDED_SPECS_DIR / "autotrader_oracle_freshness_guard_v1.tau",
    gate_output="o1",
)

AUTOTRADER_ROUTE_ECONOMIC_SANITY_GUARD_V1 = TauSpecRef(
    spec_id="autotrader_route_economic_sanity_guard_v1",
    path=RECOMMENDED_SPECS_DIR / "autotrader_route_economic_sanity_guard_v1.tau",
    gate_output="o5",
)

AUTOTRADER_EXTERNAL_SIGNAL_SOURCE_REGISTRY_GUARD_V1 = TauSpecRef(
    spec_id="autotrader_external_signal_source_registry_guard_v1",
    path=RECOMMENDED_SPECS_DIR / "autotrader_external_signal_source_registry_guard_v1.tau",
    gate_output="o8",
)

AUTOTRADER_SIGNAL_PROVENANCE_GUARD_V1 = TauSpecRef(
    spec_id="autotrader_signal_provenance_guard_v1",
    path=RECOMMENDED_SPECS_DIR / "autotrader_signal_provenance_guard_v1.tau",
    gate_output="o4",
)

AUTOTRADER_OBSERVATION_PACKET_CONTRACT_V1 = TauSpecRef(
    spec_id="autotrader_observation_packet_contract_v1",
    path=RECOMMENDED_SPECS_DIR / "autotrader_observation_packet_contract_v1.tau",
    gate_output="o5",
)

AUTOTRADER_WALLET_CAPABILITY_GUARD_V1 = TauSpecRef(
    spec_id="autotrader_wallet_capability_guard_v1",
    path=RECOMMENDED_SPECS_DIR / "autotrader_wallet_capability_guard_v1.tau",
    gate_output="o5",
)

AUTOTRADER_WALLET_OUTBOUND_GUARD_V1 = TauSpecRef(
    spec_id="autotrader_wallet_outbound_guard_v1",
    path=RECOMMENDED_SPECS_DIR / "autotrader_wallet_outbound_guard_v1.tau",
    gate_output="o5",
)

AUTOTRADER_SESSION_STATE_GUARD_V1 = TauSpecRef(
    spec_id="autotrader_session_state_guard_v1",
    path=RECOMMENDED_SPECS_DIR / "autotrader_session_state_guard_v1.tau",
    gate_output="o6",
)

AUTOTRADER_SESSION_CAPABILITY_BINDING_GUARD_V1 = TauSpecRef(
    spec_id="autotrader_session_capability_binding_guard_v1",
    path=RECOMMENDED_SPECS_DIR / "autotrader_session_capability_binding_guard_v1.tau",
    gate_output="o7",
)

AUTOTRADER_NONCE_GUARD_V1 = TauSpecRef(
    spec_id="autotrader_nonce_guard_v1",
    path=RECOMMENDED_SPECS_DIR / "autotrader_nonce_guard_v1.tau",
    gate_output="o4",
)

AUTOTRADER_TX_ENVELOPE_GUARD_V1 = TauSpecRef(
    spec_id="autotrader_tx_envelope_guard_v1",
    path=RECOMMENDED_SPECS_DIR / "autotrader_tx_envelope_guard_v1.tau",
    gate_output="o4",
)

AUTOTRADER_SUBMIT_BUNDLE_GUARD_V1 = TauSpecRef(
    spec_id="autotrader_submit_bundle_guard_v1",
    path=RECOMMENDED_SPECS_DIR / "autotrader_submit_bundle_guard_v1.tau",
    gate_output="o5",
)

AUTOTRADER_LIVE_ADMISSION_BUNDLE_V1 = TauSpecRef(
    spec_id="autotrader_live_admission_bundle_v1",
    path=RECOMMENDED_SPECS_DIR / "autotrader_live_admission_bundle_v1.tau",
    gate_output="o12",
)

AUTOTRADER_SYSTEM_COMPOSE_V1 = TauSpecRef(
    spec_id="autotrader_system_compose_v1",
    path=RECOMMENDED_SPECS_DIR / "autotrader_system_compose_v1.tau",
    gate_output="o3",
)

AUTOTRADER_EMIT_FINALIZE_V1 = TauSpecRef(
    spec_id="autotrader_emit_finalize_v1",
    path=RECOMMENDED_SPECS_DIR / "autotrader_emit_finalize_v1.tau",
    gate_output="o1",
)

PROTOCOL_TOKEN_V2 = TauSpecRef(
    spec_id="protocol_token_v2",
    path=RECOMMENDED_SPECS_DIR / "protocol_token_v2.tau",
    gate_output="o1",
)

PROTOCOL_TOKEN_V3 = TauSpecRef(
    spec_id="protocol_token_v3",
    path=RECOMMENDED_SPECS_DIR / "protocol_token_v3.tau",
    gate_output="o1",
)

TDEX_BUYBACK_PULSEX_V1 = TauSpecRef(
    spec_id="tdex_buyback_pulsex_v1",
    path=TAU_SPECS_DIR / "tdex_buyback_pulsex_v1.tau",
    gate_output="o4",
)

TDEX_BUYBACK_FLOOR_V1 = TauSpecRef(
    spec_id="tdex_buyback_floor_v1",
    path=TAU_SPECS_DIR / "tdex_buyback_floor_v1.tau",
    gate_output="o4",
)

TDEX_BUYBACK_FLOOR_FIXEDPOINT_V1 = TauSpecRef(
    spec_id="tdex_buyback_floor_fixedpoint_v1",
    path=TAU_SPECS_DIR / "tdex_buyback_floor_fixedpoint_v1.tau",
    gate_output="o5",
)

TDEX_BUYBACK_FLOOR_V2 = TauSpecRef(
    spec_id="tdex_buyback_floor_v2",
    path=RECOMMENDED_SPECS_DIR / "tdex_buyback_floor_v2.tau",
    gate_output="o4",
)

TDEX_BUYBACK_FLOOR_FIXEDPOINT_V2 = TauSpecRef(
    spec_id="tdex_buyback_floor_fixedpoint_v2",
    path=RECOMMENDED_SPECS_DIR / "tdex_buyback_floor_fixedpoint_v2.tau",
    gate_output="o5",
)

TDEX_FEE_REBATE_V1 = TauSpecRef(
    spec_id="tdex_fee_rebate_v1",
    path=TAU_SPECS_DIR / "tdex_fee_rebate_v1.tau",
    gate_output="o3",
)

TDEX_LOCK_WEIGHT_V1 = TauSpecRef(
    spec_id="tdex_lock_weight_v1",
    path=TAU_SPECS_DIR / "tdex_lock_weight_v1.tau",
    gate_output="o4",
)

GOVERNANCE_TIMELOCK_V1 = TauSpecRef(
    spec_id="governance_timelock_v1",
    path=TAU_SPECS_DIR / "governance_timelock_v1.tau",
    gate_output="o4",
)

REVISION_POLICY_V1 = TauSpecRef(
    spec_id="revision_policy_v1",
    path=RECOMMENDED_SPECS_DIR / "revision_policy_v1.tau",
    gate_output="o10",
)

REVISION_POLICY_V2 = TauSpecRef(
    spec_id="revision_policy_v2",
    path=RECOMMENDED_SPECS_DIR / "revision_policy_v2.tau",
    gate_output="o10",
)

PARAMETER_REGISTRY_V1 = TauSpecRef(
    spec_id="parameter_registry_v1",
    path=TAU_SPECS_DIR / "parameter_registry_v1.tau",
    gate_output="o1",
)

PARAMETER_REGISTRY_V2 = TauSpecRef(
    spec_id="parameter_registry_v2",
    path=RECOMMENDED_SPECS_DIR / "parameter_registry_v2.tau",
    gate_output="o1",
)

SETTLEMENT_V2_BUYBACK = TauSpecRef(
    spec_id="settlement_v2_buyback",
    path=TAU_SPECS_DIR / "settlement_v2_buyback.tau",
    gate_output="o8",
)

SETTLEMENT_V3_BUYBACK_FLOOR = TauSpecRef(
    spec_id="settlement_v3_buyback_floor",
    path=TAU_SPECS_DIR / "settlement_v3_buyback_floor.tau",
    gate_output="o8",
)

SETTLEMENT_V4_BUYBACK_FLOOR_REBATE_LOCK = TauSpecRef(
    spec_id="settlement_v4_buyback_floor_rebate_lock",
    path=RECOMMENDED_SPECS_DIR / "settlement_v4_buyback_floor_rebate_lock.tau",
    gate_output="o11",
)

SETTLEMENT_V2_BUYBACK_PROOF_GATE = TauSpecRef(
    spec_id="settlement_v2_buyback_proof_gate",
    path=RECOMMENDED_SPECS_DIR / "settlement_v2_buyback_proof_gate.tau",
    gate_output="o8",
)

SETTLEMENT_V3_BUYBACK_FLOOR_PROOF_GATE = TauSpecRef(
    spec_id="settlement_v3_buyback_floor_proof_gate",
    path=RECOMMENDED_SPECS_DIR / "settlement_v3_buyback_floor_proof_gate.tau",
    gate_output="o8",
)

SETTLEMENT_V4_BUYBACK_FLOOR_REBATE_LOCK_PROOF_GATE = TauSpecRef(
    spec_id="settlement_v4_buyback_floor_rebate_lock_proof_gate",
    path=RECOMMENDED_SPECS_DIR / "settlement_v4_buyback_floor_rebate_lock_proof_gate.tau",
    gate_output="o11",
)

SWAP_BV32_SAFE_RANGE_GUARD_V1 = TauSpecRef(
    spec_id="swap_bv32_safe_range_guard_v1",
    path=RECOMMENDED_SPECS_DIR / "swap_bv32_safe_range_guard_v1.tau",
    gate_output="o1",
)

SETTLEMENT_CANONICAL_ORDER_V1 = TauSpecRef(
    spec_id="settlement_canonical_order_v1",
    path=RECOMMENDED_SPECS_DIR / "settlement_canonical_order_v1.tau",
    gate_output="o1",
)

SETTLEMENT_NO_SANDWICH_ALIGNED_V1 = TauSpecRef(
    spec_id="settlement_no_sandwich_aligned_v1",
    path=RECOMMENDED_SPECS_DIR / "settlement_no_sandwich_aligned_v1.tau",
    gate_output="o1",
)

SETTLEMENT_PRICE_STABILITY_V1 = TauSpecRef(
    spec_id="settlement_price_stability_v1",
    path=RECOMMENDED_SPECS_DIR / "settlement_price_stability_v1.tau",
    gate_output="o1",
)

SETTLEMENT_PRICE_RAILS_ALIGNED_V1 = TauSpecRef(
    spec_id="settlement_price_rails_aligned_v1",
    path=RECOMMENDED_SPECS_DIR / "settlement_price_rails_aligned_v1.tau",
    gate_output="o1",
)

SETTLEMENT_MODULE_FLAG_BUNDLE_V1 = TauSpecRef(
    spec_id="settlement_module_flag_bundle_v1",
    path=RECOMMENDED_SPECS_DIR / "settlement_module_flag_bundle_v1.tau",
    gate_output="o1",
)

SETTLEMENT_V5_ALIGNED_COMPACT_BUNDLE = TauSpecRef(
    spec_id="settlement_v5_aligned_compact_bundle",
    path=RECOMMENDED_SPECS_DIR / "settlement_v5_aligned_compact_bundle.tau",
    gate_output="o1",
)


def build_token_composite_v1_step(
    *,
    feature_flags: int,
    current_supply: int,
    transfer_amount: int,
    burn_rate_bps: int,
    explicit_floor: int,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/token_composite_v1.tau`.

    All inputs are bv[16], so we bound to 0..65535 here.
    """
    for name, v in (
        ("feature_flags", feature_flags),
        ("current_supply", current_supply),
        ("transfer_amount", transfer_amount),
        ("burn_rate_bps", burn_rate_bps),
        ("explicit_floor", explicit_floor),
    ):
        if not isinstance(v, int) or isinstance(v, bool) or v < 0 or v > 0xFFFF:
            raise ValueError(f"{name} out of u16 range: {v!r}")
    return {
        "i1": int(feature_flags),
        "i2": int(current_supply),
        "i3": int(transfer_amount),
        "i4": int(burn_rate_bps),
        "i5": int(explicit_floor),
    }


def build_token_composite_v2_step(
    *,
    burn_allowed: int,
    never_zero_guaranteed: int,
    feature_config_valid: int,
    proof_ok: int = 1,
    binding_ok: int = 1,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/token_composite_v2.tau`.
    """
    return {
        "i1": _sbf("burn_allowed", burn_allowed),
        "i2": _sbf("never_zero_guaranteed", never_zero_guaranteed),
        "i3": _sbf("feature_config_valid", feature_config_valid),
        "i4": _sbf("proof_ok", proof_ok),
        "i5": _sbf("binding_ok", binding_ok),
    }


def build_settlement_v1_step(
    *,
    # canonical ids
    a: int,
    b: int,
    c: int,
    d: int,
    # price series (pp, p, curr) for no_sandwich + stability
    price_pp: int,
    price_prev: int,
    price_curr: int,
    # cpmm fields
    cpmm_rx: int,
    cpmm_ry: int,
    cpmm_net: int,
    cpmm_out: int,
    # balance transition (32-bit hi/lo)
    bal_before: int,
    delta: int,
    bal_after: int,
    # protocol token transition (32-bit hi/lo), with one-hot action flags
    tok_from: int,
    tok_to: int,
    tok_supply: int,
    tok_amount: int,
    tok_from2: int,
    tok_to2: int,
    tok_supply2: int,
    do_transfer: int,
    do_mint: int,
    do_burn: int,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/settlement_v1.tau`.

    This spec uses bv[16] streams heavily. 32-bit quantities are represented as
    (hi16, lo16) limbs.
    """
    def u16(name: str, v: int) -> int:
        if not isinstance(v, int) or isinstance(v, bool) or v < 0 or v > 0xFFFF:
            raise ValueError(f"{name} out of u16 range: {v!r}")
        return int(v)

    def u32(name: str, v: int) -> tuple[int, int]:
        if not isinstance(v, int) or isinstance(v, bool) or v < 0 or v > 0xFFFFFFFF:
            raise ValueError(f"{name} out of u32 range: {v!r}")
        return split_u32(int(v))

    # canonical/order + price/cpmm are u16
    a16, b16, c16, d16 = (u16("a", a), u16("b", b), u16("c", c), u16("d", d))
    pp16, prev16, curr16 = (u16("price_pp", price_pp), u16("price_prev", price_prev), u16("price_curr", price_curr))
    rx16, ry16, net16, out16 = (u16("cpmm_rx", cpmm_rx), u16("cpmm_ry", cpmm_ry), u16("cpmm_net", cpmm_net), u16("cpmm_out", cpmm_out))

    # balance limbs
    bal0_hi, bal0_lo = u32("bal_before", bal_before)
    d_hi, d_lo = u32("delta", delta)
    bal1_hi, bal1_lo = u32("bal_after", bal_after)

    # token limbs
    f_hi, f_lo = u32("tok_from", tok_from)
    t_hi, t_lo = u32("tok_to", tok_to)
    s_hi, s_lo = u32("tok_supply", tok_supply)
    a_hi, a_lo = u32("tok_amount", tok_amount)
    f2_hi, f2_lo = u32("tok_from2", tok_from2)
    t2_hi, t2_lo = u32("tok_to2", tok_to2)
    s2_hi, s2_lo = u32("tok_supply2", tok_supply2)

    # action flags are sbf but we pass as ints (0/1)
    for name, v in (("do_transfer", do_transfer), ("do_mint", do_mint), ("do_burn", do_burn)):
        if v not in (0, 1):
            raise ValueError(f"{name} must be 0 or 1, got {v!r}")

    return {
        # ids
        "i1": a16,
        "i2": b16,
        "i3": c16,
        "i4": d16,
        # price series
        "i5": pp16,
        "i6": prev16,
        "i7": curr16,
        # cpmm
        "i8": rx16,
        "i9": ry16,
        "i10": net16,
        "i11": out16,
        # balance 32-bit transition
        "i12": int(bal0_hi),
        "i13": int(bal0_lo),
        "i14": int(d_hi),
        "i15": int(d_lo),
        "i16": int(bal1_hi),
        "i17": int(bal1_lo),
        # token transition 32-bit limbs
        "i18": int(f_hi),
        "i19": int(f_lo),
        "i20": int(t_hi),
        "i21": int(t_lo),
        "i22": int(s_hi),
        "i23": int(s_lo),
        "i24": int(a_hi),
        "i25": int(a_lo),
        "i26": int(f2_hi),
        "i27": int(f2_lo),
        "i28": int(t2_hi),
        "i29": int(t2_lo),
        "i30": int(s2_hi),
        "i31": int(s2_lo),
        # action flags (sbf)
        "i32": int(do_transfer),
        "i33": int(do_mint),
        "i34": int(do_burn),
    }


def build_settlement_v1_proof_gate_step(
    *,
    # canonical ids
    a: int,
    b: int,
    c: int,
    d: int,
    # price series for no_sandwich + stability
    price_pp: int,
    price_prev: int,
    price_curr: int,
    # externally verified component flags
    cpmm_ok: int = 1,
    balance_ok: int = 1,
    token_ok: int = 1,
    proof_ok: int = 1,
    binding_ok: int = 1,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/settlement_v1_proof_gate.tau`.
    """
    return {
        "i1": _u16("a", a),
        "i2": _u16("b", b),
        "i3": _u16("c", c),
        "i4": _u16("d", d),
        "i5": _u16("price_pp", price_pp),
        "i6": _u16("price_prev", price_prev),
        "i7": _u16("price_curr", price_curr),
        "i8": _sbf("cpmm_ok", cpmm_ok),
        "i9": _sbf("balance_ok", balance_ok),
        "i10": _sbf("token_ok", token_ok),
        "i11": _sbf("proof_ok", proof_ok),
        "i12": _sbf("binding_ok", binding_ok),
    }


def build_settlement_v2_buyback_proof_gate_step(
    *,
    # canonical ids
    a: int,
    b: int,
    c: int,
    d: int,
    # price series for no_sandwich + stability
    price_pp: int,
    price_prev: int,
    price_curr: int,
    # externally verified component flags
    cpmm_ok: int = 1,
    balance_ok: int = 1,
    token_ok: int = 1,
    buyback_ok: int = 1,
    proof_ok: int = 1,
    binding_ok: int = 1,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/settlement_v2_buyback_proof_gate.tau`.
    """
    return {
        "i1": _u16("a", a),
        "i2": _u16("b", b),
        "i3": _u16("c", c),
        "i4": _u16("d", d),
        "i5": _u16("price_pp", price_pp),
        "i6": _u16("price_prev", price_prev),
        "i7": _u16("price_curr", price_curr),
        "i8": _sbf("cpmm_ok", cpmm_ok),
        "i9": _sbf("balance_ok", balance_ok),
        "i10": _sbf("token_ok", token_ok),
        "i11": _sbf("buyback_ok", buyback_ok),
        "i12": _sbf("proof_ok", proof_ok),
        "i13": _sbf("binding_ok", binding_ok),
    }


def build_settlement_v3_buyback_floor_proof_gate_step(
    *,
    # canonical ids
    a: int,
    b: int,
    c: int,
    d: int,
    # price series for no_sandwich + stability
    price_pp: int,
    price_prev: int,
    price_curr: int,
    # externally verified component flags
    cpmm_ok: int = 1,
    balance_ok: int = 1,
    token_ok: int = 1,
    buyback_floor_ok: int = 1,
    proof_ok: int = 1,
    binding_ok: int = 1,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/settlement_v3_buyback_floor_proof_gate.tau`.
    """
    return {
        "i1": _u16("a", a),
        "i2": _u16("b", b),
        "i3": _u16("c", c),
        "i4": _u16("d", d),
        "i5": _u16("price_pp", price_pp),
        "i6": _u16("price_prev", price_prev),
        "i7": _u16("price_curr", price_curr),
        "i8": _sbf("cpmm_ok", cpmm_ok),
        "i9": _sbf("balance_ok", balance_ok),
        "i10": _sbf("token_ok", token_ok),
        "i11": _sbf("buyback_floor_ok", buyback_floor_ok),
        "i12": _sbf("proof_ok", proof_ok),
        "i13": _sbf("binding_ok", binding_ok),
    }


def build_settlement_v4_buyback_floor_rebate_lock_proof_gate_step(
    *,
    # canonical ids
    a: int,
    b: int,
    c: int,
    d: int,
    # price series for no_sandwich + stability
    price_pp: int,
    price_prev: int,
    price_curr: int,
    # externally verified component flags
    cpmm_ok: int = 1,
    balance_ok: int = 1,
    token_ok: int = 1,
    buyback_floor_ok: int = 1,
    buyback_floor_fixedpoint_ok: int = 1,
    rebate_ok: int = 1,
    lock_weight_ok: int = 1,
    proof_ok: int = 1,
    binding_ok: int = 1,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/settlement_v4_buyback_floor_rebate_lock_proof_gate.tau`.
    """
    return {
        "i1": _u16("a", a),
        "i2": _u16("b", b),
        "i3": _u16("c", c),
        "i4": _u16("d", d),
        "i5": _u16("price_pp", price_pp),
        "i6": _u16("price_prev", price_prev),
        "i7": _u16("price_curr", price_curr),
        "i8": _sbf("cpmm_ok", cpmm_ok),
        "i9": _sbf("balance_ok", balance_ok),
        "i10": _sbf("token_ok", token_ok),
        "i11": _sbf("buyback_floor_ok", buyback_floor_ok),
        "i12": _sbf("buyback_floor_fixedpoint_ok", buyback_floor_fixedpoint_ok),
        "i13": _sbf("rebate_ok", rebate_ok),
        "i14": _sbf("lock_weight_ok", lock_weight_ok),
        "i15": _sbf("proof_ok", proof_ok),
        "i16": _sbf("binding_ok", binding_ok),
    }


def build_settlement_canonical_order_v1_step(*, a: int, b: int, c: int, d: int) -> Dict[str, int]:
    return {
        "i1": _u64("a", a),
        "i2": _u64("b", b),
        "i3": _u64("c", c),
        "i4": _u64("d", d),
    }


def build_settlement_no_sandwich_aligned_v1_step(*, price_pp: int, price_prev: int, price_curr: int) -> Dict[str, int]:
    return {
        "i1": _u16("price_pp", price_pp),
        "i2": _u16("price_prev", price_prev),
        "i3": _u16("price_curr", price_curr),
    }


def build_settlement_price_stability_v1_step(*, price_prev: int, price_curr: int) -> Dict[str, int]:
    return {
        "i1": _u16("price_prev", price_prev),
        "i2": _u16("price_curr", price_curr),
    }


def build_settlement_price_rails_aligned_v1_step(
    *,
    a: int,
    b: int,
    c: int,
    d: int,
    price_pp: int,
    price_prev: int,
    price_curr: int,
) -> Dict[str, int]:
    return {
        "i1": _u64("a", a),
        "i2": _u64("b", b),
        "i3": _u64("c", c),
        "i4": _u64("d", d),
        "i5": _u16("price_pp", price_pp),
        "i6": _u16("price_prev", price_prev),
        "i7": _u16("price_curr", price_curr),
    }


def build_settlement_module_flag_bundle_v1_step(
    *,
    core_module_ok: int = 1,
    feature_extension_ok: int = 1,
    proof_binding_ok: int = 1,
) -> Dict[str, int]:
    return {
        "i1": _sbf("core_module_ok", core_module_ok),
        "i2": _sbf("feature_extension_ok", feature_extension_ok),
        "i3": _sbf("proof_binding_ok", proof_binding_ok),
    }


def build_settlement_core_module_bundle_v1_step(
    *,
    cpmm_ok: int = 1,
    balance_ok: int = 1,
    token_ok: int = 1,
) -> Dict[str, int]:
    return {
        "i1": _sbf("cpmm_ok", cpmm_ok),
        "i2": _sbf("balance_ok", balance_ok),
        "i3": _sbf("token_ok", token_ok),
    }


def build_settlement_feature_extension_bundle_v1_step(
    *,
    buyback_floor_ok: int = 1,
    buyback_floor_fixedpoint_ok: int = 1,
    rebate_ok: int = 1,
    lock_weight_ok: int = 1,
) -> Dict[str, int]:
    return {
        "i1": _sbf("buyback_floor_ok", buyback_floor_ok),
        "i2": _sbf("buyback_floor_fixedpoint_ok", buyback_floor_fixedpoint_ok),
        "i3": _sbf("rebate_ok", rebate_ok),
        "i4": _sbf("lock_weight_ok", lock_weight_ok),
    }


def build_settlement_proof_binding_bundle_v1_step(
    *,
    proof_ok: int = 1,
    binding_ok: int = 1,
) -> Dict[str, int]:
    return {
        "i1": _sbf("proof_ok", proof_ok),
        "i2": _sbf("binding_ok", binding_ok),
    }


def build_settlement_v5_aligned_compact_bundle_step(
    *,
    a: int,
    b: int,
    c: int,
    d: int,
    price_pp: int,
    price_prev: int,
    price_curr: int,
    cpmm_ok: int = 1,
    balance_ok: int = 1,
    token_ok: int = 1,
    buyback_floor_ok: int = 1,
    buyback_floor_fixedpoint_ok: int = 1,
    rebate_ok: int = 1,
    lock_weight_ok: int = 1,
    proof_ok: int = 1,
    binding_ok: int = 1,
) -> Dict[str, int]:
    return {
        "i1": _u64("a", a),
        "i2": _u64("b", b),
        "i3": _u64("c", c),
        "i4": _u64("d", d),
        "i5": _u16("price_pp", price_pp),
        "i6": _u16("price_prev", price_prev),
        "i7": _u16("price_curr", price_curr),
        "i8": _sbf("cpmm_ok", cpmm_ok),
        "i9": _sbf("balance_ok", balance_ok),
        "i10": _sbf("token_ok", token_ok),
        "i11": _sbf("buyback_floor_ok", buyback_floor_ok),
        "i12": _sbf("buyback_floor_fixedpoint_ok", buyback_floor_fixedpoint_ok),
        "i13": _sbf("rebate_ok", rebate_ok),
        "i14": _sbf("lock_weight_ok", lock_weight_ok),
        "i15": _sbf("proof_ok", proof_ok),
        "i16": _sbf("binding_ok", binding_ok),
    }


def build_nonce_replay_guard_v1_step(
    *,
    intent_nonce: int,
    last_used_nonce: int,
    expected_nonce: int,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/nonce_replay_guard_v1.tau`.
    """
    for name, v in (
        ("intent_nonce", intent_nonce),
        ("last_used_nonce", last_used_nonce),
        ("expected_nonce", expected_nonce),
    ):
        if not isinstance(v, int) or isinstance(v, bool) or v < 0 or v > 0xFFFFFFFF:
            raise ValueError(f"{name} out of u32 range: {v!r}")
    return {"i1": int(intent_nonce), "i2": int(last_used_nonce), "i3": int(expected_nonce)}


def build_intent_expiry_guard_v1_step(
    *,
    intent_deadline: int,
    current_timestamp: int,
    min_validity_period: int,
    max_validity_period: int,
    intent_created: int,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/intent_expiry_guard_v1.tau`.
    """
    for name, v in (
        ("intent_deadline", intent_deadline),
        ("current_timestamp", current_timestamp),
        ("min_validity_period", min_validity_period),
        ("max_validity_period", max_validity_period),
        ("intent_created", intent_created),
    ):
        if not isinstance(v, int) or isinstance(v, bool) or v < 0 or v > 0xFFFFFFFF:
            raise ValueError(f"{name} out of u32 range: {v!r}")
    return {
        "i1": int(intent_deadline),
        "i2": int(current_timestamp),
        "i3": int(min_validity_period),
        "i4": int(max_validity_period),
        "i5": int(intent_created),
    }


def build_zusd_oracle_commit_guard_v2_step(
    *,
    oracle_seen: int,
    pending_le_active: int,
    fresh_ok: int,
    auth_ok: int,
    mcr_ok_at_pending: int,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/zusd_oracle_commit_guard_v2.tau`.
    """
    return {
        "i1": _sbf("oracle_seen", oracle_seen),
        "i2": _sbf("pending_le_active", pending_le_active),
        "i3": _sbf("fresh_ok", fresh_ok),
        "i4": _sbf("auth_ok", auth_ok),
        "i5": _sbf("mcr_ok_at_pending", mcr_ok_at_pending),
    }


def build_zusd_cross_module_oracle_sync_gate_v1_step(
    *,
    sync_snapshot_available: int,
    divergence_bounded: int,
    epoch_lag_bounded: int,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/zusd_cross_module_oracle_sync_gate_v1.tau`.
    """
    return {
        "i1": _sbf("sync_snapshot_available", sync_snapshot_available),
        "i2": _sbf("divergence_bounded", divergence_bounded),
        "i3": _sbf("epoch_lag_bounded", epoch_lag_bounded),
    }


def build_zusd_transfer_guard_v1_step(
    *,
    amount_positive: int,
    sender_has_balance: int,
    transfer_deltas_match: int,
    sender_auth_ok: int,
    recipient_valid: int,
    paused: int,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/zusd_transfer_guard_v1.tau`.
    """
    return {
        "i1": _sbf("amount_positive", amount_positive),
        "i2": _sbf("sender_has_balance", sender_has_balance),
        "i3": _sbf("transfer_deltas_match", transfer_deltas_match),
        "i4": _sbf("sender_auth_ok", sender_auth_ok),
        "i5": _sbf("recipient_valid", recipient_valid),
        "i6": _sbf("paused", paused),
    }


def build_zusd_liquidation_guard_v2_step(
    *,
    pending_init: int,
    vault_debt: int,
    under_mcr: int,
    sp_debt: int,
    vault_coll: int,
    sp_coll_before: int,
    max_sp_coll: int,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/zusd_liquidation_guard_v2.tau`.
    """
    return {
        "i1": _sbf("pending_init", pending_init),
        "i2": _u64("vault_debt", vault_debt),
        "i3": _sbf("under_mcr", under_mcr),
        "i4": _u64("sp_debt", sp_debt),
        "i5": _u64("vault_coll", vault_coll),
        "i6": _u64("sp_coll_before", sp_coll_before),
        "i7": _u64("max_sp_coll", max_sp_coll),
    }


def build_zusd_supply_conservation_v2_step(
    *,
    free_before: int,
    sp_before: int,
    total_before: int,
    free_after: int,
    sp_after: int,
    total_after: int,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/zusd_supply_conservation_v2.tau`.
    """
    return {
        "i1": _u64("free_before", free_before),
        "i2": _u64("sp_before", sp_before),
        "i3": _u64("total_before", total_before),
        "i4": _u64("free_after", free_after),
        "i5": _u64("sp_after", sp_after),
        "i6": _u64("total_after", total_after),
    }


def build_zusd_mint_guard_v1_step(
    *,
    amount: int,
    debt_before: int,
    free_before: int,
    debt_after: int,
    free_after: int,
    risky_ops_allowed: int,
    min_open_ok: int,
    max_vault_ok: int,
    max_supply_ok: int,
    mcr_post_ok: int,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/zusd_mint_guard_v1.tau`.
    """
    return {
        "i1": _u64("amount", amount),
        "i2": _u64("debt_before", debt_before),
        "i3": _u64("free_before", free_before),
        "i4": _u64("debt_after", debt_after),
        "i5": _u64("free_after", free_after),
        "i6": _sbf("risky_ops_allowed", risky_ops_allowed),
        "i7": _sbf("min_open_ok", min_open_ok),
        "i8": _sbf("max_vault_ok", max_vault_ok),
        "i9": _sbf("max_supply_ok", max_supply_ok),
        "i10": _sbf("mcr_post_ok", mcr_post_ok),
    }


def build_zusd_repay_guard_v1_step(
    *,
    amount: int,
    debt_before: int,
    free_before: int,
    debt_after: int,
    free_after: int,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/zusd_repay_guard_v1.tau`.
    """
    return {
        "i1": _u64("amount", amount),
        "i2": _u64("debt_before", debt_before),
        "i3": _u64("free_before", free_before),
        "i4": _u64("debt_after", debt_after),
        "i5": _u64("free_after", free_after),
    }


def build_zusd_redeem_guard_v1_step(
    *,
    amount: int,
    debt_before: int,
    free_before: int,
    collateral_before: int,
    debt_after: int,
    free_after: int,
    collateral_after: int,
    gross_collateral: int,
    fee_collateral: int,
    oracle_ok: int,
    mcr_post_ok: int,
    fee_cap_ok: int,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/zusd_redeem_guard_v1.tau`.
    """
    return {
        "i1": _u64("amount", amount),
        "i2": _u64("debt_before", debt_before),
        "i3": _u64("free_before", free_before),
        "i4": _u64("collateral_before", collateral_before),
        "i5": _u64("debt_after", debt_after),
        "i6": _u64("free_after", free_after),
        "i7": _u64("collateral_after", collateral_after),
        "i8": _u64("gross_collateral", gross_collateral),
        "i9": _u64("fee_collateral", fee_collateral),
        "i10": _sbf("oracle_ok", oracle_ok),
        "i11": _sbf("mcr_post_ok", mcr_post_ok),
        "i12": _sbf("fee_cap_ok", fee_cap_ok),
    }


def build_zusd_withdraw_collateral_guard_v1_step(
    *,
    amount: int,
    collateral_before: int,
    collateral_after: int,
    debt_before: int,
    risky_ops_allowed: int,
    mcr_post_ok: int,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/zusd_withdraw_collateral_guard_v1.tau`.
    """
    return {
        "i1": _u64("amount", amount),
        "i2": _u64("collateral_before", collateral_before),
        "i3": _u64("collateral_after", collateral_after),
        "i4": _u64("debt_before", debt_before),
        "i5": _sbf("risky_ops_allowed", risky_ops_allowed),
        "i6": _sbf("mcr_post_ok", mcr_post_ok),
    }


def build_zusd_deposit_sp_guard_v1_step(
    *,
    amount: int,
    free_before: int,
    sp_before: int,
    free_after: int,
    sp_after: int,
    max_supply_ok: int,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/zusd_deposit_sp_guard_v1.tau`.
    """
    return {
        "i1": _u64("amount", amount),
        "i2": _u64("free_before", free_before),
        "i3": _u64("sp_before", sp_before),
        "i4": _u64("free_after", free_after),
        "i5": _u64("sp_after", sp_after),
        "i6": _sbf("max_supply_ok", max_supply_ok),
    }


def build_zusd_withdraw_sp_guard_v1_step(
    *,
    amount: int,
    free_before: int,
    sp_before: int,
    free_after: int,
    sp_after: int,
    risky_ops_allowed: int,
    vault_mcr_ok: int,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/zusd_withdraw_sp_guard_v1.tau`.
    """
    return {
        "i1": _u64("amount", amount),
        "i2": _u64("free_before", free_before),
        "i3": _u64("sp_before", sp_before),
        "i4": _u64("free_after", free_after),
        "i5": _u64("sp_after", sp_after),
        "i6": _sbf("risky_ops_allowed", risky_ops_allowed),
        "i7": _sbf("vault_mcr_ok", vault_mcr_ok),
    }


def build_token_archetype_soulbound_v2_step(
    *,
    from_id: int,
    to_id: int,
    issuer_id: int,
    do_transfer: int,
    do_mint: int,
    do_burn: int,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/token_archetype_soulbound_v2.tau`.
    """
    for name, v in (("from_id", from_id), ("to_id", to_id), ("issuer_id", issuer_id)):
        if not isinstance(v, int) or isinstance(v, bool) or v < 0 or v > 0xFFFF:
            raise ValueError(f"{name} out of u16 range: {v!r}")
    return {
        "i1": int(from_id),
        "i2": int(to_id),
        "i3": int(issuer_id),
        "i4": _sbf("do_transfer", do_transfer),
        "i5": _sbf("do_mint", do_mint),
        "i6": _sbf("do_burn", do_burn),
    }


def build_token_archetype_lock_weighted_rewards_32_v1_step(
    *,
    stake_amount: int,
    lock_weight_bps: int,
    reward_amount: int,
    reward_cap: int,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/token_archetype_lock_weighted_rewards_32_v1.tau`.
    """
    for name, v in (
        ("stake_amount", stake_amount),
        ("lock_weight_bps", lock_weight_bps),
        ("reward_amount", reward_amount),
        ("reward_cap", reward_cap),
    ):
        if not isinstance(v, int) or isinstance(v, bool) or v < 0 or v > 0xFFFFFFFF:
            raise ValueError(f"{name} out of u32 range: {v!r}")
    return {"i1": int(stake_amount), "i2": int(lock_weight_bps), "i3": int(reward_amount), "i4": int(reward_cap)}


def build_token_archetype_lock_weighted_rewards_32_v2_step(
    *,
    stake_amount: int,
    lock_weight_bps: int,
    reward_amount: int,
    reward_cap: int,
    proof_ok: int = 1,
    binding_ok: int = 1,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/token_archetype_lock_weighted_rewards_32_v2.tau`.
    """
    for name, v in (
        ("stake_amount", stake_amount),
        ("lock_weight_bps", lock_weight_bps),
        ("reward_amount", reward_amount),
        ("reward_cap", reward_cap),
    ):
        if not isinstance(v, int) or isinstance(v, bool) or v < 0 or v > 0xFFFF:
            raise ValueError(f"{name} out of u16 range: {v!r}")
    return {
        "i1": int(stake_amount),
        "i2": int(lock_weight_bps),
        "i3": int(reward_amount),
        "i4": int(reward_cap),
        "i5": _sbf("proof_ok", proof_ok),
        "i6": _sbf("binding_ok", binding_ok),
    }


def build_token_archetype_vesting_cliff_32_v1_step(
    *,
    total_allocation: int,
    vested_amount: int,
    claim_amount: int,
    cliff_reached: int,
    claim_cap_amount: int,
    max_claim_bps: int,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/token_archetype_vesting_cliff_32_v1.tau`.
    """
    for name, v in (
        ("total_allocation", total_allocation),
        ("vested_amount", vested_amount),
        ("claim_amount", claim_amount),
        ("claim_cap_amount", claim_cap_amount),
        ("max_claim_bps", max_claim_bps),
    ):
        if not isinstance(v, int) or isinstance(v, bool) or v < 0 or v > 0xFFFFFFFF:
            raise ValueError(f"{name} out of u32 range: {v!r}")
    return {
        "i1": int(total_allocation),
        "i2": int(vested_amount),
        "i3": int(claim_amount),
        "i4": _sbf("cliff_reached", cliff_reached),
        "i5": int(claim_cap_amount),
        "i6": int(max_claim_bps),
    }


def build_token_archetype_vesting_cliff_32_v2_step(
    *,
    total_allocation: int,
    vested_amount: int,
    claim_amount: int,
    cliff_reached: int,
    claim_cap_amount: int,
    max_claim_bps: int,
    proof_ok: int = 1,
    binding_ok: int = 1,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/token_archetype_vesting_cliff_32_v2.tau`.
    """
    for name, v in (
        ("total_allocation", total_allocation),
        ("vested_amount", vested_amount),
        ("claim_amount", claim_amount),
        ("claim_cap_amount", claim_cap_amount),
        ("max_claim_bps", max_claim_bps),
    ):
        if not isinstance(v, int) or isinstance(v, bool) or v < 0 or v > 0xFFFF:
            raise ValueError(f"{name} out of u16 range: {v!r}")
    return {
        "i1": int(total_allocation),
        "i2": int(vested_amount),
        "i3": int(claim_amount),
        "i4": _sbf("cliff_reached", cliff_reached),
        "i5": int(claim_cap_amount),
        "i6": int(max_claim_bps),
        "i7": _sbf("proof_ok", proof_ok),
        "i8": _sbf("binding_ok", binding_ok),
    }


def build_cpmm_v1_step(
    *,
    reserve_in: int,
    reserve_out: int,
    amount_in: int,
    fee_bps: int,
    amount_out: int,
) -> Dict[str, int]:
    rin_hi, rin_lo = split_u32(reserve_in)
    rout_hi, rout_lo = split_u32(reserve_out)
    ain_hi, ain_lo = split_u32(amount_in)
    aout_hi, aout_lo = split_u32(amount_out)

    if not isinstance(fee_bps, int) or isinstance(fee_bps, bool) or not (0 <= fee_bps <= 10_000):
        raise ValueError(f"fee_bps out of range: {fee_bps}")

    return {
        "i1": rin_hi,
        "i2": rin_lo,
        "i3": rout_hi,
        "i4": rout_lo,
        "i5": ain_hi,
        "i6": ain_lo,
        "i7": int(fee_bps),
        "i8": aout_hi,
        "i9": aout_lo,
    }


def build_balance_safety_v1_step(*, balance_before: int, delta_add: int, delta_sub: int) -> Dict[str, int]:
    bal_hi, bal_lo = _u32("balance_before", balance_before)
    add_hi, add_lo = _u32("delta_add", delta_add)
    sub_hi, sub_lo = _u32("delta_sub", delta_sub)
    return {
        "i1": bal_hi,
        "i2": bal_lo,
        "i3": add_hi,
        "i4": add_lo,
        "i5": sub_hi,
        "i6": sub_lo,
    }


def build_balance_transition_v1_step(
    *,
    balance_before: int,
    delta_add: int,
    delta_sub: int,
    balance_mid: int,
    balance_after: int,
) -> Dict[str, int]:
    b0_hi, b0_lo = _u32("balance_before", balance_before)
    add_hi, add_lo = _u32("delta_add", delta_add)
    sub_hi, sub_lo = _u32("delta_sub", delta_sub)
    mid_hi, mid_lo = _u32("balance_mid", balance_mid)
    b1_hi, b1_lo = _u32("balance_after", balance_after)
    return {
        "i1": b0_hi,
        "i2": b0_lo,
        "i3": add_hi,
        "i4": add_lo,
        "i5": sub_hi,
        "i6": sub_lo,
        "i7": mid_hi,
        "i8": mid_lo,
        "i9": b1_hi,
        "i10": b1_lo,
    }


def build_batching_v1_step(
    *,
    intent_a_id: int,
    intent_b_id: int,
    executed_first_id: int,
    executed_second_id: int,
) -> Dict[str, int]:
    return {
        "i1": _u64("intent_a_id", intent_a_id),
        "i2": _u64("intent_b_id", intent_b_id),
        "i3": _u64("executed_first_id", executed_first_id),
        "i4": _u64("executed_second_id", executed_second_id),
    }


def build_batching_v1_4_step(
    *,
    intent_id_0: int,
    intent_id_1: int,
    intent_id_2: int,
    intent_id_3: int,
    executed_id_0: int,
    executed_id_1: int,
    executed_id_2: int,
    executed_id_3: int,
) -> Dict[str, int]:
    return {
        "i1": _u64("intent_id_0", intent_id_0),
        "i2": _u64("intent_id_1", intent_id_1),
        "i3": _u64("intent_id_2", intent_id_2),
        "i4": _u64("intent_id_3", intent_id_3),
        "i5": _u64("executed_id_0", executed_id_0),
        "i6": _u64("executed_id_1", executed_id_1),
        "i7": _u64("executed_id_2", executed_id_2),
        "i8": _u64("executed_id_3", executed_id_3),
    }


def build_batching_v1_5_compact_single_gate_step(
    *,
    intent_id_0: int,
    intent_id_1: int,
    intent_id_2: int,
    intent_id_3: int,
    executed_id_0: int,
    executed_id_1: int,
    executed_id_2: int,
    executed_id_3: int,
) -> Dict[str, int]:
    return build_batching_v1_4_step(
        intent_id_0=intent_id_0,
        intent_id_1=intent_id_1,
        intent_id_2=intent_id_2,
        intent_id_3=intent_id_3,
        executed_id_0=executed_id_0,
        executed_id_1=executed_id_1,
        executed_id_2=executed_id_2,
        executed_id_3=executed_id_3,
    )


def build_batching_all_distinct_4_v1_step(*, a: int, b: int, c: int, d: int) -> Dict[str, int]:
    return {
        "i1": _u64("a", a),
        "i2": _u64("b", b),
        "i3": _u64("c", c),
        "i4": _u64("d", d),
    }


def build_batching_left_in_right_4_v1_step(
    *,
    left_0: int,
    left_1: int,
    left_2: int,
    left_3: int,
    right_0: int,
    right_1: int,
    right_2: int,
    right_3: int,
) -> Dict[str, int]:
    return {
        "i1": _u64("left_0", left_0),
        "i2": _u64("left_1", left_1),
        "i3": _u64("left_2", left_2),
        "i4": _u64("left_3", left_3),
        "i5": _u64("right_0", right_0),
        "i6": _u64("right_1", right_1),
        "i7": _u64("right_2", right_2),
        "i8": _u64("right_3", right_3),
    }


def build_batching_executed_sorted_4_v1_step(*, a: int, b: int, c: int, d: int) -> Dict[str, int]:
    return {
        "i1": _u64("a", a),
        "i2": _u64("b", b),
        "i3": _u64("c", c),
        "i4": _u64("d", d),
    }


def build_batch_canonical_v1_4_step(
    *,
    intent_id_0: int,
    intent_id_1: int,
    intent_id_2: int,
    intent_id_3: int,
) -> Dict[str, int]:
    return {
        "i1": _u64("intent_id_0", intent_id_0),
        "i2": _u64("intent_id_1", intent_id_1),
        "i3": _u64("intent_id_2", intent_id_2),
        "i4": _u64("intent_id_3", intent_id_3),
    }


def build_protocol_token_v1_step(
    *,
    from_before: int,
    to_before: int,
    supply_before: int,
    amount: int,
    from_after: int,
    to_after: int,
    supply_after: int,
    do_transfer: int,
    do_mint: int,
    do_burn: int,
) -> Dict[str, int]:
    f0_hi, f0_lo = _u32("from_before", from_before)
    t0_hi, t0_lo = _u32("to_before", to_before)
    s0_hi, s0_lo = _u32("supply_before", supply_before)
    a_hi, a_lo = _u32("amount", amount)
    f1_hi, f1_lo = _u32("from_after", from_after)
    t1_hi, t1_lo = _u32("to_after", to_after)
    s1_hi, s1_lo = _u32("supply_after", supply_after)
    return {
        "i1": f0_hi,
        "i2": f0_lo,
        "i3": t0_hi,
        "i4": t0_lo,
        "i5": s0_hi,
        "i6": s0_lo,
        "i7": a_hi,
        "i8": a_lo,
        "i9": f1_hi,
        "i10": f1_lo,
        "i11": t1_hi,
        "i12": t1_lo,
        "i13": s1_hi,
        "i14": s1_lo,
        "i15": _sbf("do_transfer", do_transfer),
        "i16": _sbf("do_mint", do_mint),
        "i17": _sbf("do_burn", do_burn),
    }


def build_autotrader_budget_guard_v1_step(
    *,
    spent_before: int,
    order_amount: int,
    per_order_limit: int,
    window_budget: int,
    spent_after: int,
    kill_switch_active: int,
) -> Dict[str, int]:
    return {
        "i1": _bv32("spent_before", spent_before),
        "i2": _bv32("order_amount", order_amount),
        "i3": _bv32("per_order_limit", per_order_limit),
        "i4": _bv32("window_budget", window_budget),
        "i5": _bv32("spent_after", spent_after),
        "i6": _sbf("kill_switch_active", kill_switch_active),
    }


def build_autotrader_compile_contract_v1_step(
    *,
    backend_ok: int,
    template_ok: int,
    strategy_id_ok: int,
    owner_binding_ok: int,
    asset_scope_ok: int,
    required_params_ok: int,
    action_scope_ok: int,
    notional_chain_ok: int,
    slippage_ok: int,
    oracle_window_ok: int,
    strategy_window_ok: int,
    controls_ok: int,
    tau_bundle_ok: int,
) -> Dict[str, int]:
    return {
        "i1": _sbf("backend_ok", backend_ok),
        "i2": _sbf("template_ok", template_ok),
        "i3": _sbf("strategy_id_ok", strategy_id_ok),
        "i4": _sbf("owner_binding_ok", owner_binding_ok),
        "i5": _sbf("asset_scope_ok", asset_scope_ok),
        "i6": _sbf("required_params_ok", required_params_ok),
        "i7": _sbf("action_scope_ok", action_scope_ok),
        "i8": _sbf("notional_chain_ok", notional_chain_ok),
        "i9": _sbf("slippage_ok", slippage_ok),
        "i10": _sbf("oracle_window_ok", oracle_window_ok),
        "i11": _sbf("strategy_window_ok", strategy_window_ok),
        "i12": _sbf("controls_ok", controls_ok),
        "i13": _sbf("tau_bundle_ok", tau_bundle_ok),
    }


def build_autotrader_compilation_witness_v1_step(
    *,
    source_form_ok: int,
    strategy_hash_match: int,
    owner_match: int,
    backend_match: int,
    template_match: int,
    asset_universe_match: int,
    allowed_actions_match: int,
    notional_caps_match: int,
    risk_limits_match: int,
    strategy_window_match: int,
    controls_match: int,
    template_params_match: int,
    tau_policy_specs_match: int,
    compile_contract_ok: int,
) -> Dict[str, int]:
    return {
        "i1": _sbf("source_form_ok", source_form_ok),
        "i2": _sbf("strategy_hash_match", strategy_hash_match),
        "i3": _sbf("owner_match", owner_match),
        "i4": _sbf("backend_match", backend_match),
        "i5": _sbf("template_match", template_match),
        "i6": _sbf("asset_universe_match", asset_universe_match),
        "i7": _sbf("allowed_actions_match", allowed_actions_match),
        "i8": _sbf("notional_caps_match", notional_caps_match),
        "i9": _sbf("risk_limits_match", risk_limits_match),
        "i10": _sbf("strategy_window_match", strategy_window_match),
        "i11": _sbf("controls_match", controls_match),
        "i12": _sbf("template_params_match", template_params_match),
        "i13": _sbf("tau_policy_specs_match", tau_policy_specs_match),
        "i14": _sbf("compile_contract_ok", compile_contract_ok),
    }


def build_autotrader_execution_guard_v1_step(
    *,
    current_epoch: int,
    valid_from_epoch: int,
    valid_until_epoch: int,
    last_action_known: int,
    last_action_epoch: int,
    cadence_epochs: int,
    min_order_spacing_epochs: int,
    projected_live_orders: int,
    max_live_orders: int,
) -> Dict[str, int]:
    return {
        "i1": _bv32("current_epoch", current_epoch),
        "i2": _bv32("valid_from_epoch", valid_from_epoch),
        "i3": _bv32("valid_until_epoch", valid_until_epoch),
        "i4": _sbf("last_action_known", last_action_known),
        "i5": _bv32("last_action_epoch", last_action_epoch),
        "i6": _bv32("cadence_epochs", cadence_epochs),
        "i7": _bv32("min_order_spacing_epochs", min_order_spacing_epochs),
        "i8": _bv32("projected_live_orders", projected_live_orders),
        "i9": _bv32("max_live_orders", max_live_orders),
    }


def build_autotrader_oracle_freshness_guard_v1_step(
    *,
    current_epoch: int,
    quote_epoch: int,
    max_oracle_staleness_epochs: int,
) -> Dict[str, int]:
    return {
        "i1": _bv32("current_epoch", current_epoch),
        "i2": _bv32("quote_epoch", quote_epoch),
        "i3": _bv32("max_oracle_staleness_epochs", max_oracle_staleness_epochs),
    }


def build_autotrader_route_economic_sanity_guard_v1_step(
    *,
    receipt_verified: int,
    route_kind_supported: int,
    body_pair_valid: int,
    legs_present: int,
    all_legs_single_hop: int,
    all_legs_match_body_pair: int,
    multi_hop_present: int,
    max_hop_input_vs_reserve_bps: int,
    max_hop_output_vs_reserve_bps: int,
    max_hop_price_impact_bps: int,
    input_stress_extreme_bps: int,
    output_depletion_extreme_bps: int,
    price_impact_extreme_bps: int,
) -> Dict[str, int]:
    return {
        "i1": _sbf("receipt_verified", receipt_verified),
        "i2": _sbf("route_kind_supported", route_kind_supported),
        "i3": _sbf("body_pair_valid", body_pair_valid),
        "i4": _sbf("legs_present", legs_present),
        "i5": _sbf("all_legs_single_hop", all_legs_single_hop),
        "i6": _sbf("all_legs_match_body_pair", all_legs_match_body_pair),
        "i7": _sbf("multi_hop_present", multi_hop_present),
        "i8": _bv32("max_hop_input_vs_reserve_bps", max_hop_input_vs_reserve_bps),
        "i9": _bv32("max_hop_output_vs_reserve_bps", max_hop_output_vs_reserve_bps),
        "i10": _bv32("max_hop_price_impact_bps", max_hop_price_impact_bps),
        "i11": _bv32("input_stress_extreme_bps", input_stress_extreme_bps),
        "i12": _bv32("output_depletion_extreme_bps", output_depletion_extreme_bps),
        "i13": _bv32("price_impact_extreme_bps", price_impact_extreme_bps),
    }


def build_autotrader_external_signal_source_registry_guard_v1_step(
    *,
    registry_entry_present: int,
    registry_entry_enabled: int,
    observed_source_kind_code: int,
    observed_trust_tier_code: int,
    advisory_only: int,
    auth_ok: int,
    freshness_ok: int,
    registered_source_kind_code: int,
    allow_advisory: int,
    allow_attested: int,
    allow_verified: int,
    allow_protocol: int,
    require_advisory_only: int,
    require_auth: int,
    require_freshness: int,
) -> Dict[str, int]:
    return {
        "i1": _sbf("registry_entry_present", registry_entry_present),
        "i2": _sbf("registry_entry_enabled", registry_entry_enabled),
        "i3": _bv32("observed_source_kind_code", observed_source_kind_code),
        "i4": _bv32("observed_trust_tier_code", observed_trust_tier_code),
        "i5": _sbf("advisory_only", advisory_only),
        "i6": _sbf("auth_ok", auth_ok),
        "i7": _sbf("freshness_ok", freshness_ok),
        "i8": _bv32("registered_source_kind_code", registered_source_kind_code),
        "i9": _sbf("allow_advisory", allow_advisory),
        "i10": _sbf("allow_attested", allow_attested),
        "i11": _sbf("allow_verified", allow_verified),
        "i12": _sbf("allow_protocol", allow_protocol),
        "i13": _sbf("require_advisory_only", require_advisory_only),
        "i14": _sbf("require_auth", require_auth),
        "i15": _sbf("require_freshness", require_freshness),
    }


def build_autotrader_signal_provenance_guard_v1_step(
    *,
    source_kind_code: int,
    trust_tier_code: int,
    quote_receipt_present: int,
    quote_receipt_verified: int,
    quote_epoch_present: int,
    binding_ok: int,
    auth_ok: int,
    source_available: int,
    require_quote_receipts: int,
) -> Dict[str, int]:
    return {
        "i1": _bv32("source_kind_code", source_kind_code),
        "i2": _bv32("trust_tier_code", trust_tier_code),
        "i3": _sbf("quote_receipt_present", quote_receipt_present),
        "i4": _sbf("quote_receipt_verified", quote_receipt_verified),
        "i5": _sbf("quote_epoch_present", quote_epoch_present),
        "i6": _sbf("binding_ok", binding_ok),
        "i7": _sbf("auth_ok", auth_ok),
        "i8": _sbf("source_available", source_available),
        "i9": _sbf("require_quote_receipts", require_quote_receipts),
    }


def build_autotrader_observation_packet_contract_v1_step(
    *,
    primary_source_kind_code: int,
    primary_trust_tier_code: int,
    primary_quote_receipt_present: int,
    primary_quote_receipt_verified: int,
    primary_quote_epoch_present: int,
    primary_source_available: int,
    primary_auth_ok: int,
    primary_binding_ok: int,
    external_signal_count: int,
    advisory_external_count: int,
    trusted_external_count: int,
) -> Dict[str, int]:
    return {
        "i1": _bv32("primary_source_kind_code", primary_source_kind_code),
        "i2": _bv32("primary_trust_tier_code", primary_trust_tier_code),
        "i3": _sbf("primary_quote_receipt_present", primary_quote_receipt_present),
        "i4": _sbf("primary_quote_receipt_verified", primary_quote_receipt_verified),
        "i5": _sbf("primary_quote_epoch_present", primary_quote_epoch_present),
        "i6": _sbf("primary_source_available", primary_source_available),
        "i7": _sbf("primary_auth_ok", primary_auth_ok),
        "i8": _sbf("primary_binding_ok", primary_binding_ok),
        "i9": _bv32("external_signal_count", external_signal_count),
        "i10": _bv32("advisory_external_count", advisory_external_count),
        "i11": _bv32("trusted_external_count", trusted_external_count),
    }


def build_autotrader_wallet_capability_guard_v1_step(
    *,
    enabled: int,
    signer_ok: int,
    asset_in_allowed: int,
    asset_out_allowed: int,
    action_allowed: int,
    chain_id_ok: int,
    current_epoch: int,
    valid_from_epoch: int,
    valid_until_epoch: int,
    order_amount: int,
    notional_remaining: int,
) -> Dict[str, int]:
    return {
        "i1": _sbf("enabled", enabled),
        "i2": _sbf("signer_ok", signer_ok),
        "i3": _sbf("asset_in_allowed", asset_in_allowed),
        "i4": _sbf("asset_out_allowed", asset_out_allowed),
        "i5": _sbf("action_allowed", action_allowed),
        "i6": _sbf("chain_id_ok", chain_id_ok),
        "i7": _bv32("current_epoch", current_epoch),
        "i8": _bv32("valid_from_epoch", valid_from_epoch),
        "i9": _bv32("valid_until_epoch", valid_until_epoch),
        "i10": _bv32("order_amount", order_amount),
        "i11": _bv32("notional_remaining", notional_remaining),
    }


def build_autotrader_wallet_outbound_guard_v1_step(
    *,
    amount: int,
    max_outbound_amount: int,
    sender_id: int,
    scoped_sender_id: int,
    destination_allowed: int,
    session_active: int,
    policy_hash_ok: int,
    enabled: int,
) -> Dict[str, int]:
    return {
        "i1": _bv32("amount", amount),
        "i2": _bv32("max_outbound_amount", max_outbound_amount),
        "i3": _bv32("sender_id", sender_id),
        "i4": _bv32("scoped_sender_id", scoped_sender_id),
        "i5": _sbf("destination_allowed", destination_allowed),
        "i6": _sbf("session_active", session_active),
        "i7": _sbf("policy_hash_ok", policy_hash_ok),
        "i8": _sbf("enabled", enabled),
    }


def build_autotrader_session_state_guard_v1_step(
    *,
    enabled: int,
    session_binding_ok: int,
    owner_binding_ok: int,
    chain_binding_ok: int,
    revocation_epoch_present: int,
    current_epoch: int,
    revoked_at_epoch: int,
) -> Dict[str, int]:
    return {
        "i1": _sbf("enabled", enabled),
        "i2": _sbf("session_binding_ok", session_binding_ok),
        "i3": _sbf("owner_binding_ok", owner_binding_ok),
        "i4": _sbf("chain_binding_ok", chain_binding_ok),
        "i5": _sbf("revocation_epoch_present", revocation_epoch_present),
        "i6": _bv32("current_epoch", current_epoch),
        "i7": _bv32("revoked_at_epoch", revoked_at_epoch),
    }


def build_autotrader_session_capability_binding_guard_v1_step(
    *,
    session_present: int,
    owner_binding_ok: int,
    chain_binding_ok: int,
    asset_scope_ok: int,
    action_scope_ok: int,
    capability_valid_from_epoch: int,
    capability_valid_until_epoch: int,
    strategy_valid_from_epoch: int,
    strategy_valid_until_epoch: int,
) -> Dict[str, int]:
    return {
        "i1": _sbf("session_present", session_present),
        "i2": _sbf("owner_binding_ok", owner_binding_ok),
        "i3": _sbf("chain_binding_ok", chain_binding_ok),
        "i4": _sbf("asset_scope_ok", asset_scope_ok),
        "i5": _sbf("action_scope_ok", action_scope_ok),
        "i6": _bv32("capability_valid_from_epoch", capability_valid_from_epoch),
        "i7": _bv32("capability_valid_until_epoch", capability_valid_until_epoch),
        "i8": _bv32("strategy_valid_from_epoch", strategy_valid_from_epoch),
        "i9": _bv32("strategy_valid_until_epoch", strategy_valid_until_epoch),
    }


def build_autotrader_nonce_guard_v1_step(
    *,
    intent_nonce: int,
    last_used_nonce: int,
    expected_nonce: int,
) -> Dict[str, int]:
    return {
        "i1": _bv32("intent_nonce", intent_nonce),
        "i2": _bv32("last_used_nonce", last_used_nonce),
        "i3": _bv32("expected_nonce", expected_nonce),
    }


def build_autotrader_tx_envelope_guard_v1_step(
    *,
    tx_requested: int,
    sequence_present: int,
    expiration_present: int,
    sequence_valid: int,
    expiration_valid: int,
    fee_limit_valid: int,
    intent_stream_present: int,
    settlement_stream_absent: int,
    extra_custom_streams_absent: int,
) -> Dict[str, int]:
    return {
        "i1": _sbf("tx_requested", tx_requested),
        "i2": _sbf("sequence_present", sequence_present),
        "i3": _sbf("expiration_present", expiration_present),
        "i4": _sbf("sequence_valid", sequence_valid),
        "i5": _sbf("expiration_valid", expiration_valid),
        "i6": _sbf("fee_limit_valid", fee_limit_valid),
        "i7": _sbf("intent_stream_present", intent_stream_present),
        "i8": _sbf("settlement_stream_absent", settlement_stream_absent),
        "i9": _sbf("extra_custom_streams_absent", extra_custom_streams_absent),
    }


def build_autotrader_submit_bundle_guard_v1_step(
    *,
    emit_requested: int,
    signed_intents_present: int,
    signatures_present: int,
    signatures_verify: int,
    sender_binding_ok: int,
    quote_receipts_present: int,
    operations_roundtrip_ok: int,
    tx_requested: int,
    tx_payload_ok: int,
) -> Dict[str, int]:
    return {
        "i1": _sbf("emit_requested", emit_requested),
        "i2": _sbf("signed_intents_present", signed_intents_present),
        "i3": _sbf("signatures_present", signatures_present),
        "i4": _sbf("signatures_verify", signatures_verify),
        "i5": _sbf("sender_binding_ok", sender_binding_ok),
        "i6": _sbf("quote_receipts_present", quote_receipts_present),
        "i7": _sbf("operations_roundtrip_ok", operations_roundtrip_ok),
        "i8": _sbf("tx_requested", tx_requested),
        "i9": _sbf("tx_payload_ok", tx_payload_ok),
    }


def build_autotrader_live_admission_bundle_v1_step(
    *,
    source_registry_ok: int,
    signal_provenance_ok: int,
    route_economic_sanity_ok: int,
    execution_ok: int,
    oracle_freshness_ok: int,
    budget_ok: int,
    tx_envelope_ok: int,
    session_state_ok: int,
    session_capability_binding_ok: int,
    wallet_capability_ok: int,
    nonce_ok: int,
) -> Dict[str, int]:
    return {
        "i1": _sbf("source_registry_ok", source_registry_ok),
        "i2": _sbf("signal_provenance_ok", signal_provenance_ok),
        "i3": _sbf("route_economic_sanity_ok", route_economic_sanity_ok),
        "i4": _sbf("execution_ok", execution_ok),
        "i5": _sbf("oracle_freshness_ok", oracle_freshness_ok),
        "i6": _sbf("budget_ok", budget_ok),
        "i7": _sbf("tx_envelope_ok", tx_envelope_ok),
        "i8": _sbf("session_state_ok", session_state_ok),
        "i9": _sbf("session_capability_binding_ok", session_capability_binding_ok),
        "i10": _sbf("wallet_capability_ok", wallet_capability_ok),
        "i11": _sbf("nonce_ok", nonce_ok),
    }


def build_autotrader_system_compose_v1_step(
    *,
    emit_requested: int,
    policy_artifact_ok: int,
    tau_policy_bundle_ok: int,
    signer_binding_ok: int,
    compile_ok: int,
    source_registry_ok: int,
    signal_provenance_ok: int,
    route_economic_sanity_ok: int,
    execution_ok: int,
    oracle_freshness_ok: int,
    budget_ok: int,
    candidate_set_ok: int,
    decision_ok: int,
    kill_switch_ok: int,
    tx_envelope_ok: int,
    session_state_ok: int,
    session_capability_binding_ok: int,
    wallet_capability_ok: int,
    nonce_ok: int,
) -> Dict[str, int]:
    return {
        "i1": _sbf("emit_requested", emit_requested),
        "i2": _sbf("policy_artifact_ok", policy_artifact_ok),
        "i3": _sbf("tau_policy_bundle_ok", tau_policy_bundle_ok),
        "i4": _sbf("signer_binding_ok", signer_binding_ok),
        "i5": _sbf("compile_ok", compile_ok),
        "i6": _sbf("source_registry_ok", source_registry_ok),
        "i7": _sbf("signal_provenance_ok", signal_provenance_ok),
        "i8": _sbf("route_economic_sanity_ok", route_economic_sanity_ok),
        "i9": _sbf("execution_ok", execution_ok),
        "i10": _sbf("oracle_freshness_ok", oracle_freshness_ok),
        "i11": _sbf("budget_ok", budget_ok),
        "i12": _sbf("candidate_set_ok", candidate_set_ok),
        "i13": _sbf("decision_ok", decision_ok),
        "i14": _sbf("kill_switch_ok", kill_switch_ok),
        "i15": _sbf("tx_envelope_ok", tx_envelope_ok),
        "i16": _sbf("session_state_ok", session_state_ok),
        "i17": _sbf("session_capability_binding_ok", session_capability_binding_ok),
        "i18": _sbf("wallet_capability_ok", wallet_capability_ok),
        "i19": _sbf("nonce_ok", nonce_ok),
    }


def build_autotrader_emit_finalize_v1_step(
    *,
    emit_requested: int,
    system_compose_ok: int,
    submit_bundle_ok: int,
) -> Dict[str, int]:
    return {
        "i1": _sbf("emit_requested", emit_requested),
        "i2": _sbf("system_compose_ok", system_compose_ok),
        "i3": _sbf("submit_bundle_ok", submit_bundle_ok),
    }


def build_protocol_token_v2_step(
    *,
    from_before: int,
    to_before: int,
    supply_before: int,
    amount: int,
    from_after: int,
    to_after: int,
    supply_after: int,
    do_transfer: int,
    do_mint: int,
    do_burn: int,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/protocol_token_v2.tau`.

    v2 uses bv[32] but requires values <= 0xFFFF for non-wrapping addition.
    """
    for name, v in (
        ("from_before", from_before),
        ("to_before", to_before),
        ("supply_before", supply_before),
        ("amount", amount),
        ("from_after", from_after),
        ("to_after", to_after),
        ("supply_after", supply_after),
    ):
        if not isinstance(v, int) or isinstance(v, bool) or v < 0 or v > 0xFFFF:
            raise ValueError(f"{name} out of v2 safe-range (0..65535): {v!r}")
    return {
        "i1": int(from_before),
        "i2": int(to_before),
        "i3": int(supply_before),
        "i4": int(amount),
        "i5": int(from_after),
        "i6": int(to_after),
        "i7": int(supply_after),
        "i8": _sbf("do_transfer", do_transfer),
        "i9": _sbf("do_mint", do_mint),
        "i10": _sbf("do_burn", do_burn),
    }


def build_protocol_token_v3_step(
    *,
    from_before: int,
    to_before: int,
    supply_before: int,
    amount: int,
    from_after: int,
    to_after: int,
    supply_after: int,
    do_transfer: int,
    do_mint: int,
    do_burn: int,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/protocol_token_v3.tau` (bv[16]).
    """
    for name, v in (
        ("from_before", from_before),
        ("to_before", to_before),
        ("supply_before", supply_before),
        ("amount", amount),
        ("from_after", from_after),
        ("to_after", to_after),
        ("supply_after", supply_after),
    ):
        if not isinstance(v, int) or isinstance(v, bool) or v < 0 or v > 0xFFFF:
            raise ValueError(f"{name} out of u16 range: {v!r}")
    return {
        "i1": int(from_before),
        "i2": int(to_before),
        "i3": int(supply_before),
        "i4": int(amount),
        "i5": int(from_after),
        "i6": int(to_after),
        "i7": int(supply_after),
        "i8": _sbf("do_transfer", do_transfer),
        "i9": _sbf("do_mint", do_mint),
        "i10": _sbf("do_burn", do_burn),
    }


def build_tokenomics_buyback_burn_v1_step(
    *,
    fee_total: int,
    fee_to_lp: int,
    fee_to_treasury: int,
    fee_to_burn: int,
    buyback_triggered: int,
    burn_amount: int,
    burn_limit: int,
) -> Dict[str, int]:
    ft_hi, ft_lo = _u32("fee_total", fee_total)
    lp_hi, lp_lo = _u32("fee_to_lp", fee_to_lp)
    tr_hi, tr_lo = _u32("fee_to_treasury", fee_to_treasury)
    burn_hi, burn_lo = _u32("fee_to_burn", fee_to_burn)

    fee_to_lp_u32 = (int(lp_hi) << 16) + int(lp_lo)
    fee_to_treasury_u32 = (int(tr_hi) << 16) + int(tr_lo)
    fee_to_burn_u32 = (int(burn_hi) << 16) + int(burn_lo)

    lpt_hi, lpt_lo = _u32("fee_lp_treasury", fee_to_lp_u32 + fee_to_treasury_u32)
    sum_hi, sum_lo = _u32("fee_sum", (fee_to_lp_u32 + fee_to_treasury_u32) + fee_to_burn_u32)
    ba_hi, ba_lo = _u32("burn_amount", burn_amount)
    lim_hi, lim_lo = _u32("burn_limit", burn_limit)
    return {
        "i1": ft_hi,
        "i2": ft_lo,
        "i3": lp_hi,
        "i4": lp_lo,
        "i5": tr_hi,
        "i6": tr_lo,
        "i7": burn_hi,
        "i8": burn_lo,
        "i9": lpt_hi,
        "i10": lpt_lo,
        "i11": sum_hi,
        "i12": sum_lo,
        "i13": _sbf("buyback_triggered", buyback_triggered),
        "i14": ba_hi,
        "i15": ba_lo,
        "i16": lim_hi,
        "i17": lim_lo,
    }


def build_tokenomics_buyback_burn_v2_step(
    *,
    fee_total: int,
    fee_to_lp: int,
    fee_to_treasury: int,
    fee_to_burn: int,
    buyback_triggered: int,
    burn_amount: int,
    burn_limit: int,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/tokenomics_buyback_burn_v2.tau`.

    Note: v2 uses bv[32] streams, but requires values <= 0xFFFF for non-wrapping addition.
    """
    for name, v in (
        ("fee_total", fee_total),
        ("fee_to_lp", fee_to_lp),
        ("fee_to_treasury", fee_to_treasury),
        ("fee_to_burn", fee_to_burn),
        ("burn_amount", burn_amount),
        ("burn_limit", burn_limit),
    ):
        if not isinstance(v, int) or isinstance(v, bool) or v < 0 or v > 0xFFFF:
            raise ValueError(f"{name} out of v2 safe-range (0..65535): {v!r}")
    return {
        "i1": int(fee_total),
        "i2": int(fee_to_lp),
        "i3": int(fee_to_treasury),
        "i4": int(fee_to_burn),
        "i5": _sbf("buyback_triggered", buyback_triggered),
        "i6": int(burn_amount),
        "i7": int(burn_limit),
    }
def build_burn_receipt_replay_guard_v1_step(
    *,
    do_burn: int,
    receipt_bound: int,
    nullifier_unused: int,
    policy_ok: int,
) -> Dict[str, int]:
    return {
        "i1": _sbf("do_burn", do_burn),
        "i2": _sbf("receipt_bound", receipt_bound),
        "i3": _sbf("nullifier_unused", nullifier_unused),
        "i4": _sbf("policy_ok", policy_ok),
    }


def build_confidential_extension_live_admission_v1_step(
    *,
    do_execute: int,
    receipt_verified: int,
    policy_digest_match: int,
    request_unused: int,
) -> Dict[str, int]:
    return {
        "i1": _sbf("do_execute", do_execute),
        "i2": _sbf("receipt_verified", receipt_verified),
        "i3": _sbf("policy_digest_match", policy_digest_match),
        "i4": _sbf("request_unused", request_unused),
    }


def build_burn_receipt_amount_guard_v1_step(
    *,
    do_burn: int,
    burn_amount: int,
    receipt_amount: int,
    burn_budget: int,
) -> Dict[str, int]:
    for name, v in (("burn_amount", burn_amount), ("receipt_amount", receipt_amount), ("burn_budget", burn_budget)):
        if not isinstance(v, int) or isinstance(v, bool) or v < 0 or v > 0x7FFF:
            raise ValueError(f"{name} out of amount-guard safe-range (0..32767): {v!r}")
    return {
        "i1": _sbf("do_burn", do_burn),
        "i2": int(burn_amount),
        "i3": int(receipt_amount),
        "i4": int(burn_budget),
    }


def build_burn_receipt_supply_guard_v1_step(
    *,
    do_burn: int,
    burn_amount: int,
    supply_before: int,
    supply_after: int,
) -> Dict[str, int]:
    if not isinstance(burn_amount, int) or isinstance(burn_amount, bool) or burn_amount < 0 or burn_amount > 0x7FFF:
        raise ValueError(f"burn_amount out of supply-guard safe-range (0..32767): {burn_amount!r}")
    for name, v in (("supply_before", supply_before), ("supply_after", supply_after)):
        if not isinstance(v, int) or isinstance(v, bool) or v < 0 or v > 0xFFFF:
            raise ValueError(f"{name} out of supply-guard safe-range (0..65535): {v!r}")
    return {
        "i1": _sbf("do_burn", do_burn),
        "i2": int(burn_amount),
        "i3": int(supply_before),
        "i4": int(supply_after),
    }


def build_burn_receipt_batch_sum_guard_v1_step(
    *,
    do_burn: int,
    burn_amount: int,
    batch_burn_sum_before: int,
    batch_burn_sum_after: int,
) -> Dict[str, int]:
    for name, v in (("burn_amount", burn_amount), ("batch_burn_sum_before", batch_burn_sum_before)):
        if not isinstance(v, int) or isinstance(v, bool) or v < 0 or v > 0x7FFF:
            raise ValueError(f"{name} out of batch-sum safe-range (0..32767): {v!r}")
    if not isinstance(batch_burn_sum_after, int) or isinstance(batch_burn_sum_after, bool) or batch_burn_sum_after < 0 or batch_burn_sum_after > 0xFFFF:
        raise ValueError(
            f"batch_burn_sum_after out of batch-sum safe-range (0..65535): {batch_burn_sum_after!r}"
        )
    return {
        "i1": _sbf("do_burn", do_burn),
        "i2": int(burn_amount),
        "i3": int(batch_burn_sum_before),
        "i4": int(batch_burn_sum_after),
    }


def build_tdex_buyback_pulsex_v1_step(
    *,
    trade_amount: int,
    fee_charged: int,
    buyback_amount: int,
    burned_amount: int,
) -> Dict[str, int]:
    return {
        "i1": _u16("trade_amount", trade_amount),
        "i2": _u16("fee_charged", fee_charged),
        "i3": _u16("buyback_amount", buyback_amount),
        "i4": _u16("burned_amount", burned_amount),
    }


def build_tdex_buyback_floor_v1_step(
    *,
    trade_amount: int,
    fee_charged: int,
    buyback_amount: int,
    burned_amount: int,
    supply_before: int,
    supply_after: int,
    supply_floor: int,
) -> Dict[str, int]:
    s0_hi, s0_lo = _u32("supply_before", supply_before)
    s1_hi, s1_lo = _u32("supply_after", supply_after)
    f_hi, f_lo = _u32("supply_floor", supply_floor)
    return {
        "i1": _u16("trade_amount", trade_amount),
        "i2": _u16("fee_charged", fee_charged),
        "i3": _u16("buyback_amount", buyback_amount),
        "i4": _u16("burned_amount", burned_amount),
        "i5": s0_hi,
        "i6": s0_lo,
        "i7": s1_hi,
        "i8": s1_lo,
        "i9": f_hi,
        "i10": f_lo,
    }


def build_tdex_buyback_floor_fixedpoint_v1_step(
    *,
    trade_amount: int,
    fee_charged: int,
    buyback_amount: int,
    burned_amount: int,
    supply_before: int,
    supply_after: int,
    supply_floor: int,
    unit_scale: int,
) -> Dict[str, int]:
    step = build_tdex_buyback_floor_v1_step(
        trade_amount=trade_amount,
        fee_charged=fee_charged,
        buyback_amount=buyback_amount,
        burned_amount=burned_amount,
        supply_before=supply_before,
        supply_after=supply_after,
        supply_floor=supply_floor,
    )
    step["i11"] = _u16("unit_scale", unit_scale)
    return step


def build_tdex_buyback_floor_v2_step(
    *,
    trade_amount: int,
    fee_charged: int,
    buyback_amount: int,
    burned_amount: int,
    supply_before: int,
    supply_after: int,
    supply_floor: int,
    fee_rate_ok: int = 1,
    buyback_share_ok: int = 1,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/tdex_buyback_floor_v2.tau`.
    """
    return {
        "i1": _bv32("trade_amount", trade_amount),
        "i2": _bv32("fee_charged", fee_charged),
        "i3": _bv32("buyback_amount", buyback_amount),
        "i4": _bv32("burned_amount", burned_amount),
        "i5": _bv32("supply_before", supply_before),
        "i6": _bv32("supply_after", supply_after),
        "i7": _bv32("supply_floor", supply_floor),
        "i8": _sbf("fee_rate_ok", fee_rate_ok),
        "i9": _sbf("buyback_share_ok", buyback_share_ok),
    }


def build_tdex_buyback_floor_fixedpoint_v2_step(
    *,
    trade_amount: int,
    fee_charged: int,
    buyback_amount: int,
    burned_amount: int,
    supply_before: int,
    supply_after: int,
    supply_floor: int,
    unit_scale: int,
    fee_rate_ok: int = 1,
    buyback_share_ok: int = 1,
    unit_ok: int = 1,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/tdex_buyback_floor_fixedpoint_v2.tau`.
    """
    return {
        "i1": _bv32("trade_amount", trade_amount),
        "i2": _bv32("fee_charged", fee_charged),
        "i3": _bv32("buyback_amount", buyback_amount),
        "i4": _bv32("burned_amount", burned_amount),
        "i5": _bv32("supply_before", supply_before),
        "i6": _bv32("supply_after", supply_after),
        "i7": _bv32("supply_floor", supply_floor),
        "i8": _bv32("unit_scale", unit_scale),
        "i9": _sbf("fee_rate_ok", fee_rate_ok),
        "i10": _sbf("buyback_share_ok", buyback_share_ok),
        "i11": _sbf("unit_ok", unit_ok),
    }


def build_tdex_fee_rebate_v1_step(
    *,
    trade_fee: int,
    rebate_rate_bps: int,
    rebate_amount: int,
    rebate_cap: int,
) -> Dict[str, int]:
    return {
        "i1": _u16("trade_fee", trade_fee),
        "i2": _u16("rebate_rate_bps", rebate_rate_bps),
        "i3": _u16("rebate_amount", rebate_amount),
        "i4": _u16("rebate_cap", rebate_cap),
    }


def build_tdex_lock_weight_v1_step(
    *,
    lock_days: int,
    stake_amount: int,
    tier1_days: int,
    tier2_days: int,
    weight_t1: int,
    weight_t2: int,
    weight_t3: int,
    weight_claimed: int,
    weighted_stake: int,
) -> Dict[str, int]:
    return {
        "i1": _u16("lock_days", lock_days),
        "i2": _u16("stake_amount", stake_amount),
        "i3": _u16("tier1_days", tier1_days),
        "i4": _u16("tier2_days", tier2_days),
        "i5": _u16("weight_t1", weight_t1),
        "i6": _u16("weight_t2", weight_t2),
        "i7": _u16("weight_t3", weight_t3),
        "i8": _u16("weight_claimed", weight_claimed),
        "i9": _u16("weighted_stake", weighted_stake),
    }


def build_governance_timelock_v1_step(
    *,
    proposal_ts: int,
    current_ts: int,
    min_delay: int,
    exec_req: int,
) -> Dict[str, int]:
    return {
        "i1": _u16("proposal_ts", proposal_ts),
        "i2": _u16("current_ts", current_ts),
        "i3": _u16("min_delay", min_delay),
        "i4": _sbf("exec_req", exec_req),
    }


def build_parameter_registry_v1_step(
    *,
    exec_req: int,
    revision_ok: int,
    fee_curr: int,
    fee_next: int,
    buyback_curr: int,
    buyback_next: int,
    rebate_curr: int,
    rebate_next: int,
    floor_curr: int,
    floor_next: int,
    unit_curr: int,
    unit_next: int,
    tier1_curr: int,
    tier1_next: int,
    tier2_curr: int,
    tier2_next: int,
    weight1_curr: int,
    weight1_next: int,
    weight2_curr: int,
    weight2_next: int,
    weight3_curr: int,
    weight3_next: int,
) -> Dict[str, int]:
    f0_hi, f0_lo = _u32("floor_curr", floor_curr)
    f1_hi, f1_lo = _u32("floor_next", floor_next)
    return {
        "i1": _sbf("exec_req", exec_req),
        "i2": _sbf("revision_ok", revision_ok),
        "i3": _u16("fee_curr", fee_curr),
        "i4": _u16("fee_next", fee_next),
        "i5": _u16("buyback_curr", buyback_curr),
        "i6": _u16("buyback_next", buyback_next),
        "i7": _u16("rebate_curr", rebate_curr),
        "i8": _u16("rebate_next", rebate_next),
        "i9": f0_hi,
        "i10": f0_lo,
        "i11": f1_hi,
        "i12": f1_lo,
        "i13": _u16("unit_curr", unit_curr),
        "i14": _u16("unit_next", unit_next),
        "i15": _u16("tier1_curr", tier1_curr),
        "i16": _u16("tier1_next", tier1_next),
        "i17": _u16("tier2_curr", tier2_curr),
        "i18": _u16("tier2_next", tier2_next),
        "i19": _u16("weight1_curr", weight1_curr),
        "i20": _u16("weight1_next", weight1_next),
        "i21": _u16("weight2_curr", weight2_curr),
        "i22": _u16("weight2_next", weight2_next),
        "i23": _u16("weight3_curr", weight3_curr),
        "i24": _u16("weight3_next", weight3_next),
    }


def build_parameter_registry_v2_step(
    *,
    exec_req: int,
    revision_ok: int,
    fee_applied: int,
    buyback_applied: int,
    rebate_applied: int,
    floor_applied: int,
    unit_applied: int,
    tier1_applied: int,
    tier2_applied: int,
    weight1_applied: int,
    weight2_applied: int,
    weight3_applied: int,
    proof_ok: int = 1,
    binding_ok: int = 1,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/parameter_registry_v2.tau`.
    """
    floor_hi, floor_lo = _u32("floor_applied", floor_applied)
    return {
        "i1": _sbf("exec_req", exec_req),
        "i2": _sbf("revision_ok", revision_ok),
        "i3": _u16("fee_applied", fee_applied),
        "i4": _u16("buyback_applied", buyback_applied),
        "i5": _u16("rebate_applied", rebate_applied),
        "i6": floor_hi,
        "i7": floor_lo,
        "i8": _u16("unit_applied", unit_applied),
        "i9": _u16("tier1_applied", tier1_applied),
        "i10": _u16("tier2_applied", tier2_applied),
        "i11": _u16("weight1_applied", weight1_applied),
        "i12": _u16("weight2_applied", weight2_applied),
        "i13": _u16("weight3_applied", weight3_applied),
        "i14": _sbf("proof_ok", proof_ok),
        "i15": _sbf("binding_ok", binding_ok),
    }


def build_revision_policy_v1_step(
    *,
    # governance
    approved: int,
    exec_req: int,
    proposal_ts: int,
    current_ts: int,
    min_delay: int,
    # fee
    fee_curr: int,
    fee_next: int,
    fee_min: int,
    fee_max: int,
    fee_step: int,
    # buyback
    buyback_curr: int,
    buyback_next: int,
    buyback_min: int,
    buyback_max: int,
    buyback_step: int,
    # rebate
    rebate_curr: int,
    rebate_next: int,
    rebate_min: int,
    rebate_max: int,
    rebate_step: int,
    # floor (u32)
    floor_curr: int,
    floor_next: int,
    floor_min: int,
    floor_max: int,
    floor_step: int,
    # unit
    unit_curr: int,
    unit_next: int,
    unit_min: int,
    unit_max: int,
    unit_step: int,
    # tiers
    tier1_curr: int,
    tier1_next: int,
    tier1_min: int,
    tier1_max: int,
    tier1_step: int,
    tier2_curr: int,
    tier2_next: int,
    tier2_min: int,
    tier2_max: int,
    tier2_step: int,
    # weights
    weight1_curr: int,
    weight1_next: int,
    weight1_min: int,
    weight1_max: int,
    weight1_step: int,
    weight2_curr: int,
    weight2_next: int,
    weight2_min: int,
    weight2_max: int,
    weight2_step: int,
    weight3_curr: int,
    weight3_next: int,
    weight3_min: int,
    weight3_max: int,
    weight3_step: int,
) -> Dict[str, int]:
    fc_hi, fc_lo = _u32("floor_curr", floor_curr)
    fn_hi, fn_lo = _u32("floor_next", floor_next)
    fmin_hi, fmin_lo = _u32("floor_min", floor_min)
    fmax_hi, fmax_lo = _u32("floor_max", floor_max)
    fstep_hi, fstep_lo = _u32("floor_step", floor_step)

    return {
        # governance
        "i1": _sbf("approved", approved),
        "i2": _sbf("exec_req", exec_req),
        "i3": _u16("proposal_ts", proposal_ts),
        "i4": _u16("current_ts", current_ts),
        "i5": _u16("min_delay", min_delay),
        # fee
        "i6": _u16("fee_curr", fee_curr),
        "i7": _u16("fee_next", fee_next),
        "i8": _u16("fee_min", fee_min),
        "i9": _u16("fee_max", fee_max),
        "i10": _u16("fee_step", fee_step),
        # buyback
        "i11": _u16("buyback_curr", buyback_curr),
        "i12": _u16("buyback_next", buyback_next),
        "i13": _u16("buyback_min", buyback_min),
        "i14": _u16("buyback_max", buyback_max),
        "i15": _u16("buyback_step", buyback_step),
        # rebate
        "i16": _u16("rebate_curr", rebate_curr),
        "i17": _u16("rebate_next", rebate_next),
        "i18": _u16("rebate_min", rebate_min),
        "i19": _u16("rebate_max", rebate_max),
        "i20": _u16("rebate_step", rebate_step),
        # floor
        "i21": fc_hi,
        "i22": fc_lo,
        "i23": fn_hi,
        "i24": fn_lo,
        "i25": fmin_hi,
        "i26": fmin_lo,
        "i27": fmax_hi,
        "i28": fmax_lo,
        "i29": fstep_hi,
        "i30": fstep_lo,
        # unit
        "i31": _u16("unit_curr", unit_curr),
        "i32": _u16("unit_next", unit_next),
        "i33": _u16("unit_min", unit_min),
        "i34": _u16("unit_max", unit_max),
        "i35": _u16("unit_step", unit_step),
        # tiers
        "i36": _u16("tier1_curr", tier1_curr),
        "i37": _u16("tier1_next", tier1_next),
        "i38": _u16("tier1_min", tier1_min),
        "i39": _u16("tier1_max", tier1_max),
        "i40": _u16("tier1_step", tier1_step),
        "i41": _u16("tier2_curr", tier2_curr),
        "i42": _u16("tier2_next", tier2_next),
        "i43": _u16("tier2_min", tier2_min),
        "i44": _u16("tier2_max", tier2_max),
        "i45": _u16("tier2_step", tier2_step),
        # weights
        "i46": _u16("weight1_curr", weight1_curr),
        "i47": _u16("weight1_next", weight1_next),
        "i48": _u16("weight1_min", weight1_min),
        "i49": _u16("weight1_max", weight1_max),
        "i50": _u16("weight1_step", weight1_step),
        "i51": _u16("weight2_curr", weight2_curr),
        "i52": _u16("weight2_next", weight2_next),
        "i53": _u16("weight2_min", weight2_min),
        "i54": _u16("weight2_max", weight2_max),
        "i55": _u16("weight2_step", weight2_step),
        "i56": _u16("weight3_curr", weight3_curr),
        "i57": _u16("weight3_next", weight3_next),
        "i58": _u16("weight3_min", weight3_min),
        "i59": _u16("weight3_max", weight3_max),
        "i60": _u16("weight3_step", weight3_step),
    }


def build_revision_policy_v2_step(
    *,
    approved: int,
    exec_req: int,
    governance_ok: int,
    revision_ok: int,
    proof_ok: int = 1,
    binding_ok: int = 1,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/revision_policy_v2.tau`.
    """
    return {
        "i1": _sbf("approved", approved),
        "i2": _sbf("exec_req", exec_req),
        "i3": _sbf("governance_ok", governance_ok),
        "i4": _sbf("revision_ok", revision_ok),
        "i5": _sbf("proof_ok", proof_ok),
        "i6": _sbf("binding_ok", binding_ok),
    }


def build_settlement_v2_buyback_step(
    *,
    settlement_v1_step: Dict[str, int],
    trade_amount: int,
    fee_charged: int,
    buyback_amount: int,
    burned_amount: int,
) -> Dict[str, int]:
    step = dict(settlement_v1_step)
    step["i35"] = _u16("trade_amount", trade_amount)
    step["i36"] = _u16("fee_charged", fee_charged)
    step["i37"] = _u16("buyback_amount", buyback_amount)
    step["i38"] = _u16("burned_amount", burned_amount)
    return step


def build_settlement_v3_buyback_floor_step(*, settlement_v2_step: Dict[str, int], supply_floor: int) -> Dict[str, int]:
    step = dict(settlement_v2_step)
    floor_hi, floor_lo = _u32("supply_floor", supply_floor)
    step["i39"] = floor_hi
    step["i40"] = floor_lo
    return step


def build_settlement_v4_buyback_floor_rebate_lock_step(
    *,
    settlement_v3_step: Dict[str, int],
    unit_scale: int,
    rebate_rate_bps: int,
    rebate_amount: int,
    rebate_cap: int,
    lock_days: int,
    stake_amount: int,
    tier1_days: int,
    tier2_days: int,
    weight_t1: int,
    weight_t2: int,
    weight_t3: int,
    weight_claimed: int,
    weighted_stake: int,
) -> Dict[str, int]:
    step = dict(settlement_v3_step)
    step["i41"] = _u16("unit_scale", unit_scale)
    step["i42"] = _u16("rebate_rate_bps", rebate_rate_bps)
    step["i43"] = _u16("rebate_amount", rebate_amount)
    step["i44"] = _u16("rebate_cap", rebate_cap)
    step["i45"] = _u16("lock_days", lock_days)
    step["i46"] = _u16("stake_amount", stake_amount)
    step["i47"] = _u16("tier1_days", tier1_days)
    step["i48"] = _u16("tier2_days", tier2_days)
    step["i49"] = _u16("weight_t1", weight_t1)
    step["i50"] = _u16("weight_t2", weight_t2)
    step["i51"] = _u16("weight_t3", weight_t3)
    step["i52"] = _u16("weight_claimed", weight_claimed)
    step["i53"] = _u16("weighted_stake", weighted_stake)
    return step


def build_swap_exact_in_v1_step(
    *,
    reserve_in: int,
    reserve_out: int,
    amount_in: int,
    fee_bps: int,
    min_amount_out: int,
    amount_out: int,
    new_reserve_in: int,
    new_reserve_out: int,
) -> Dict[str, int]:
    rin_hi, rin_lo = split_u32(reserve_in)
    rout_hi, rout_lo = split_u32(reserve_out)
    ain_hi, ain_lo = split_u32(amount_in)
    min_hi, min_lo = split_u32(min_amount_out)
    aout_hi, aout_lo = split_u32(amount_out)
    new_rin_hi, new_rin_lo = split_u32(new_reserve_in)
    new_rout_hi, new_rout_lo = split_u32(new_reserve_out)

    if not isinstance(fee_bps, int) or isinstance(fee_bps, bool) or not (0 <= fee_bps <= 10_000):
        raise ValueError(f"fee_bps out of range: {fee_bps}")

    return {
        "i1": rin_hi,
        "i2": rin_lo,
        "i3": rout_hi,
        "i4": rout_lo,
        "i5": ain_hi,
        "i6": ain_lo,
        "i7": int(fee_bps),
        "i8": min_hi,
        "i9": min_lo,
        "i10": aout_hi,
        "i11": aout_lo,
        "i12": new_rin_hi,
        "i13": new_rin_lo,
        "i14": new_rout_hi,
        "i15": new_rout_lo,
    }


def build_swap_exact_in_v4_step(
    *,
    reserve_in: int,
    reserve_out: int,
    amount_in: int,
    fee_bps: int,
    min_amount_out: int,
    amount_out: int,
    new_reserve_in: int,
    new_reserve_out: int,
) -> Dict[str, int]:
    # v4 is bv[32]-native (no hi/lo limbs).
    if not isinstance(fee_bps, int) or isinstance(fee_bps, bool) or not (0 <= fee_bps <= 10_000):
        raise ValueError(f"fee_bps out of range: {fee_bps}")
    return {
        "i1": int(reserve_in),
        "i2": int(reserve_out),
        "i3": int(amount_in),
        "i4": int(fee_bps),
        "i5": int(min_amount_out),
        "i6": int(amount_out),
        "i7": int(new_reserve_in),
        "i8": int(new_reserve_out),
    }


def build_swap_exact_in_proof_gate_v1_step(
    *,
    reserve_in: int,
    reserve_out: int,
    amount_in: int,
    fee_bps: int,
    min_amount_out: int,
    amount_out: int,
    new_reserve_in: int,
    new_reserve_out: int,
    proof_ok: int = 1,
    binding_ok: int = 1,
    reserve_transition_ok: int | None = None,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/swap_exact_in_proof_gate_v1.tau`.
    """
    step = build_swap_exact_in_v4_step(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_in=amount_in,
        fee_bps=fee_bps,
        min_amount_out=min_amount_out,
        amount_out=amount_out,
        new_reserve_in=new_reserve_in,
        new_reserve_out=new_reserve_out,
    )
    step["i9"] = _sbf("proof_ok", proof_ok)
    step["i10"] = _sbf("binding_ok", binding_ok)
    step["i11"] = _computed_sbf(
        "reserve_transition_ok",
        reserve_transition_ok,
        new_reserve_in == reserve_in + amount_in and new_reserve_out == reserve_out - amount_out,
    )
    return step


def build_swap_exact_in_fee_proof_gate_v1_step(
    *,
    reserve_in: int,
    reserve_out: int,
    amount_in: int,
    fee_bps: int,
    min_amount_out: int,
    amount_out: int,
    new_reserve_in: int,
    new_reserve_out: int,
    fee_total: int,
    proof_ok: int = 1,
    binding_ok: int = 1,
    fee_ok: int = 1,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/swap_exact_in_fee_proof_gate_v1.tau`.
    """
    step = build_swap_exact_in_v4_step(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_in=amount_in,
        fee_bps=fee_bps,
        min_amount_out=min_amount_out,
        amount_out=amount_out,
        new_reserve_in=new_reserve_in,
        new_reserve_out=new_reserve_out,
    )
    step["i9"] = _bv32("fee_total", fee_total)
    step["i10"] = _sbf("proof_ok", proof_ok)
    step["i11"] = _sbf("binding_ok", binding_ok)
    step["i12"] = _sbf("fee_ok", fee_ok)
    return step


def build_swap_exact_in_protocol_fee_apply_v1_step(
    *,
    reserve_in: int,
    reserve_out: int,
    amount_in: int,
    fee_bps: int,
    min_amount_out: int,
    amount_out: int,
    new_reserve_in: int,
    new_reserve_out: int,
    fee_total: int,
    protocol_fee: int,
    proof_ok: int = 1,
    binding_ok: int = 1,
    fee_ok: int = 1,
    protocol_fee_ok: int = 1,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/swap_exact_in_protocol_fee_apply_v1.tau`.
    """
    step = build_swap_exact_in_v4_step(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_in=amount_in,
        fee_bps=fee_bps,
        min_amount_out=min_amount_out,
        amount_out=amount_out,
        new_reserve_in=new_reserve_in,
        new_reserve_out=new_reserve_out,
    )
    step["i9"] = _bv32("fee_total", fee_total)
    step["i10"] = _bv32("protocol_fee", protocol_fee)
    step["i11"] = _sbf("proof_ok", proof_ok)
    step["i12"] = _sbf("binding_ok", binding_ok)
    step["i13"] = _sbf("fee_ok", fee_ok)
    step["i14"] = _sbf("protocol_fee_ok", protocol_fee_ok)
    return step


def build_swap_exact_in_v3_step(
    *,
    reserve_in: int,
    reserve_out: int,
    amount_in: int,
    fee_bps: int,
    min_amount_out: int,
    amount_out: int,
    new_reserve_in: int,
    new_reserve_out: int,
    k_old: int,
    k_new: int,
) -> Dict[str, int]:
    # v3 is bv[32] inputs plus precomputed bv[64] k values.
    if not isinstance(fee_bps, int) or isinstance(fee_bps, bool) or not (0 <= fee_bps <= 10_000):
        raise ValueError(f"fee_bps out of range: {fee_bps}")
    for name, v in (("k_old", k_old), ("k_new", k_new)):
        if not isinstance(v, int) or isinstance(v, bool) or v < 0 or v > 0xFFFFFFFFFFFFFFFF:
            raise ValueError(f"{name} out of u64 range: {v!r}")
    return {
        "i1": int(reserve_in),
        "i2": int(reserve_out),
        "i3": int(amount_in),
        "i4": int(fee_bps),
        "i5": int(min_amount_out),
        "i6": int(amount_out),
        "i7": int(new_reserve_in),
        "i8": int(new_reserve_out),
        "i9": int(k_old),
        "i10": int(k_new),
    }


def build_swap_exact_out_v1_step(
    *,
    reserve_in: int,
    reserve_out: int,
    amount_out: int,
    fee_bps: int,
    max_amount_in: int,
    amount_in: int,
    new_reserve_in: int,
    new_reserve_out: int,
) -> Dict[str, int]:
    rin_hi, rin_lo = split_u32(reserve_in)
    rout_hi, rout_lo = split_u32(reserve_out)
    aout_hi, aout_lo = split_u32(amount_out)
    max_hi, max_lo = split_u32(max_amount_in)
    ain_hi, ain_lo = split_u32(amount_in)
    new_rin_hi, new_rin_lo = split_u32(new_reserve_in)
    new_rout_hi, new_rout_lo = split_u32(new_reserve_out)

    if not isinstance(fee_bps, int) or isinstance(fee_bps, bool) or not (0 <= fee_bps <= 10_000):
        raise ValueError(f"fee_bps out of range: {fee_bps}")

    return {
        "i1": rin_hi,
        "i2": rin_lo,
        "i3": rout_hi,
        "i4": rout_lo,
        "i5": aout_hi,
        "i6": aout_lo,
        "i7": int(fee_bps),
        "i8": max_hi,
        "i9": max_lo,
        "i10": ain_hi,
        "i11": ain_lo,
        "i12": new_rin_hi,
        "i13": new_rin_lo,
        "i14": new_rout_hi,
        "i15": new_rout_lo,
    }


def build_swap_exact_out_v4_step(
    *,
    reserve_in: int,
    reserve_out: int,
    amount_out: int,
    fee_bps: int,
    max_amount_in: int,
    amount_in: int,
    new_reserve_in: int,
    new_reserve_out: int,
) -> Dict[str, int]:
    # v4 is bv[32]-native (no hi/lo limbs).
    if not isinstance(fee_bps, int) or isinstance(fee_bps, bool) or not (0 <= fee_bps <= 10_000):
        raise ValueError(f"fee_bps out of range: {fee_bps}")
    return {
        "i1": int(reserve_in),
        "i2": int(reserve_out),
        "i3": int(amount_out),
        "i4": int(fee_bps),
        "i5": int(max_amount_in),
        "i6": int(amount_in),
        "i7": int(new_reserve_in),
        "i8": int(new_reserve_out),
    }


def build_swap_exact_out_proof_gate_v1_step(
    *,
    reserve_in: int,
    reserve_out: int,
    amount_out: int,
    fee_bps: int,
    max_amount_in: int,
    amount_in: int,
    new_reserve_in: int,
    new_reserve_out: int,
    proof_ok: int = 1,
    binding_ok: int = 1,
    reserve_transition_ok: int | None = None,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/swap_exact_out_proof_gate_v1.tau`.
    """
    step = build_swap_exact_out_v4_step(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_out=amount_out,
        fee_bps=fee_bps,
        max_amount_in=max_amount_in,
        amount_in=amount_in,
        new_reserve_in=new_reserve_in,
        new_reserve_out=new_reserve_out,
    )
    step["i9"] = _sbf("proof_ok", proof_ok)
    step["i10"] = _sbf("binding_ok", binding_ok)
    step["i11"] = _computed_sbf(
        "reserve_transition_ok",
        reserve_transition_ok,
        new_reserve_in == reserve_in + amount_in and new_reserve_out == reserve_out - amount_out,
    )
    return step


def build_swap_bv32_safe_range_guard_v1_step(
    *,
    reserve_in: int,
    reserve_out: int,
    delta_primary: int,
    delta_secondary: int,
    new_reserve_in: int,
    new_reserve_out: int,
) -> Dict[str, int]:
    return {
        "i1": _bv32("reserve_in", reserve_in),
        "i2": _bv32("reserve_out", reserve_out),
        "i3": _bv32("delta_primary", delta_primary),
        "i4": _bv32("delta_secondary", delta_secondary),
        "i5": _bv32("new_reserve_in", new_reserve_in),
        "i6": _bv32("new_reserve_out", new_reserve_out),
    }


def build_swap_exact_out_fee_proof_gate_v1_step(
    *,
    reserve_in: int,
    reserve_out: int,
    amount_out: int,
    fee_bps: int,
    max_amount_in: int,
    amount_in: int,
    new_reserve_in: int,
    new_reserve_out: int,
    fee_total: int,
    proof_ok: int = 1,
    binding_ok: int = 1,
    fee_ok: int = 1,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/swap_exact_out_fee_proof_gate_v1.tau`.

    """
    step = build_swap_exact_out_v4_step(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_out=amount_out,
        fee_bps=fee_bps,
        max_amount_in=max_amount_in,
        amount_in=amount_in,
        new_reserve_in=new_reserve_in,
        new_reserve_out=new_reserve_out,
    )
    step["i9"] = _bv32("fee_total", fee_total)
    step["i10"] = _sbf("proof_ok", proof_ok)
    step["i11"] = _sbf("binding_ok", binding_ok)
    step["i12"] = _sbf("fee_ok", fee_ok)
    return step


def build_swap_exact_out_protocol_fee_apply_v1_step(
    *,
    reserve_in: int,
    reserve_out: int,
    amount_out: int,
    fee_bps: int,
    max_amount_in: int,
    amount_in: int,
    new_reserve_in: int,
    new_reserve_out: int,
    fee_total: int,
    protocol_fee: int,
    proof_ok: int = 1,
    binding_ok: int = 1,
    fee_ok: int = 1,
    protocol_fee_ok: int = 1,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/swap_exact_out_protocol_fee_apply_v1.tau`.
    """
    step = build_swap_exact_out_v4_step(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_out=amount_out,
        fee_bps=fee_bps,
        max_amount_in=max_amount_in,
        amount_in=amount_in,
        new_reserve_in=new_reserve_in,
        new_reserve_out=new_reserve_out,
    )
    step["i9"] = _bv32("fee_total", fee_total)
    step["i10"] = _bv32("protocol_fee", protocol_fee)
    step["i11"] = _sbf("proof_ok", proof_ok)
    step["i12"] = _sbf("binding_ok", binding_ok)
    step["i13"] = _sbf("fee_ok", fee_ok)
    step["i14"] = _sbf("protocol_fee_ok", protocol_fee_ok)
    return step


def build_swap_exact_out_v3_step(
    *,
    reserve_in: int,
    reserve_out: int,
    amount_out: int,
    fee_bps: int,
    max_amount_in: int,
    amount_in: int,
    new_reserve_in: int,
    new_reserve_out: int,
    k_old: int,
    k_new: int,
) -> Dict[str, int]:
    # v3 is bv[32] inputs plus precomputed bv[64] k values.
    if not isinstance(fee_bps, int) or isinstance(fee_bps, bool) or not (0 <= fee_bps <= 10_000):
        raise ValueError(f"fee_bps out of range: {fee_bps}")
    for name, v in (("k_old", k_old), ("k_new", k_new)):
        if not isinstance(v, int) or isinstance(v, bool) or v < 0 or v > 0xFFFFFFFFFFFFFFFF:
            raise ValueError(f"{name} out of u64 range: {v!r}")
    return {
        "i1": int(reserve_in),
        "i2": int(reserve_out),
        "i3": int(amount_out),
        "i4": int(fee_bps),
        "i5": int(max_amount_in),
        "i6": int(amount_in),
        "i7": int(new_reserve_in),
        "i8": int(new_reserve_out),
        "i9": int(k_old),
        "i10": int(k_new),
    }


def build_swap_fee_total_ceil_v1_step(*, gross_in: int, fee_bps: int, fee_total: int) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/swap_fee_total_ceil_v1.tau`.
    """
    return {
        "i1": _u64("gross_in", gross_in),
        "i2": _u64("fee_bps", fee_bps),
        "i3": _u64("fee_total", fee_total),
    }


def build_protocol_fee_floor_v1_step(
    *, fee_total: int, protocol_fee_share_bps: int, protocol_fee: int
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/protocol_fee_floor_v1.tau`.
    """
    return {
        "i1": _u64("fee_total", fee_total),
        "i2": _u64("protocol_fee_share_bps", protocol_fee_share_bps),
        "i3": _u64("protocol_fee", protocol_fee),
    }


def build_add_liquidity_ratio_guard_v1_step(
    *,
    reserve0: int,
    reserve1: int,
    amount0_desired: int,
    amount1_desired: int,
    amount0_used: int,
    amount1_used: int,
    amount0_refund: int,
    amount1_refund: int,
    proof_ok: int = 1,
    binding_ok: int = 1,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/add_liquidity_ratio_guard_v1.tau`.

    """
    return {
        "i1": _bv32("reserve0", reserve0),
        "i2": _bv32("reserve1", reserve1),
        "i3": _bv32("amount0_desired", amount0_desired),
        "i4": _bv32("amount1_desired", amount1_desired),
        "i5": _bv32("amount0_used", amount0_used),
        "i6": _bv32("amount1_used", amount1_used),
        "i7": _bv32("amount0_refund", amount0_refund),
        "i8": _bv32("amount1_refund", amount1_refund),
        "i9": _sbf("proof_ok", proof_ok),
        "i10": _sbf("binding_ok", binding_ok),
    }


def build_add_liquidity_apply_v1_step(
    *,
    reserve0_before: int,
    reserve1_before: int,
    lp_supply_before: int,
    amount0_used: int,
    amount1_used: int,
    lp_minted: int,
    reserve0_after: int,
    reserve1_after: int,
    lp_supply_after: int,
    proof_ok: int = 1,
    binding_ok: int = 1,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/add_liquidity_apply_v1.tau`.
    """
    return {
        "i1": _bv32("reserve0_before", reserve0_before),
        "i2": _bv32("reserve1_before", reserve1_before),
        "i3": _bv32("lp_supply_before", lp_supply_before),
        "i4": _bv32("amount0_used", amount0_used),
        "i5": _bv32("amount1_used", amount1_used),
        "i6": _bv32("lp_minted", lp_minted),
        "i7": _bv32("reserve0_after", reserve0_after),
        "i8": _bv32("reserve1_after", reserve1_after),
        "i9": _bv32("lp_supply_after", lp_supply_after),
        "i10": _sbf("proof_ok", proof_ok),
        "i11": _sbf("binding_ok", binding_ok),
    }


def build_lp_mint_min_of_floors_guard_v1_step(
    *,
    amount0: int,
    amount1: int,
    reserve0: int,
    reserve1: int,
    lp_supply: int,
    lp_minted: int,
    proof_ok: int = 1,
    binding_ok: int = 1,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/lp_mint_min_of_floors_guard_v1.tau`.
    """
    return {
        "i1": _bv32("amount0", amount0),
        "i2": _bv32("amount1", amount1),
        "i3": _bv32("reserve0", reserve0),
        "i4": _bv32("reserve1", reserve1),
        "i5": _bv32("lp_supply", lp_supply),
        "i6": _bv32("lp_minted", lp_minted),
        "i7": _sbf("proof_ok", proof_ok),
        "i8": _sbf("binding_ok", binding_ok),
    }


def build_remove_liquidity_apply_v1_step(
    *,
    reserve0_before: int,
    reserve1_before: int,
    lp_supply_before: int,
    lp_burned: int,
    amount0_out: int,
    amount1_out: int,
    reserve0_after: int,
    reserve1_after: int,
    lp_supply_after: int,
    proof_ok: int = 1,
    binding_ok: int = 1,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/remove_liquidity_apply_v1.tau`.
    """
    return {
        "i1": _bv32("reserve0_before", reserve0_before),
        "i2": _bv32("reserve1_before", reserve1_before),
        "i3": _bv32("lp_supply_before", lp_supply_before),
        "i4": _bv32("lp_burned", lp_burned),
        "i5": _bv32("amount0_out", amount0_out),
        "i6": _bv32("amount1_out", amount1_out),
        "i7": _bv32("reserve0_after", reserve0_after),
        "i8": _bv32("reserve1_after", reserve1_after),
        "i9": _bv32("lp_supply_after", lp_supply_after),
        "i10": _sbf("proof_ok", proof_ok),
        "i11": _sbf("binding_ok", binding_ok),
    }


def build_lp_burn_floor_math_guard_v1_step(
    *,
    lp_amount: int,
    reserve0: int,
    reserve1: int,
    lp_supply: int,
    amount0_out: int,
    amount1_out: int,
    proof_ok: int = 1,
    binding_ok: int = 1,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/lp_burn_floor_math_guard_v1.tau`.
    """
    return {
        "i1": _bv32("lp_amount", lp_amount),
        "i2": _bv32("reserve0", reserve0),
        "i3": _bv32("reserve1", reserve1),
        "i4": _bv32("lp_supply", lp_supply),
        "i5": _bv32("amount0_out", amount0_out),
        "i6": _bv32("amount1_out", amount1_out),
        "i7": _sbf("proof_ok", proof_ok),
        "i8": _sbf("binding_ok", binding_ok),
    }


def build_create_pool_apply_proof_gate_v1_step(
    *,
    reserve0_before: int,
    reserve1_before: int,
    lp_supply_before: int,
    amount0_in: int,
    amount1_in: int,
    fee_bps: int,
    lp_minted: int,
    reserve0_after: int,
    reserve1_after: int,
    lp_supply_after: int,
    proof_ok: int = 1,
    binding_ok: int = 1,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/create_pool_apply_proof_gate_v1.tau`.

    Note: this spec expects bv[64] streams but constrains values to u32 range.
    """
    if not isinstance(fee_bps, int) or isinstance(fee_bps, bool) or not (0 <= fee_bps <= 10_000):
        raise ValueError(f"fee_bps out of range: {fee_bps}")
    return {
        "i1": _bv32("reserve0_before", reserve0_before),
        "i2": _bv32("reserve1_before", reserve1_before),
        "i3": _bv32("lp_supply_before", lp_supply_before),
        "i4": _bv32("amount0_in", amount0_in),
        "i5": _bv32("amount1_in", amount1_in),
        "i6": _bv32("fee_bps", fee_bps),
        "i7": _bv32("lp_minted", lp_minted),
        "i8": _bv32("reserve0_after", reserve0_after),
        "i9": _bv32("reserve1_after", reserve1_after),
        "i10": _bv32("lp_supply_after", lp_supply_after),
        "i11": _sbf("proof_ok", proof_ok),
        "i12": _sbf("binding_ok", binding_ok),
    }


def build_create_pool_initial_sqrt_guard_v1_step(
    *,
    amount0: int,
    amount1: int,
    sqrt_floor: int,
    lp_minted: int,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/create_pool_initial_sqrt_guard_v1.tau`.
    """
    return {
        "i1": _u64("amount0", amount0),
        "i2": _u64("amount1", amount1),
        "i3": _u64("sqrt_floor", sqrt_floor),
        "i4": _u64("lp_minted", lp_minted),
    }


def build_price_impact_guard_v1_step(
    *,
    ref_out: int,
    actual_out: int,
    max_impact_bps: int,
    binding_ok: int = 1,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/price_impact_guard_v1.tau`.
    """
    return {
        "i1": _bv32("ref_out", ref_out),
        "i2": _bv32("actual_out", actual_out),
        "i3": _bv32("max_impact_bps", max_impact_bps),
        "i4": _sbf("binding_ok", binding_ok),
    }


def build_optimal_choice_certificate_v1_step(
    *,
    winner_index: int,
    winner_key: int,
    cand0_key: int,
    cand1_key: int,
    cand2_key: int,
    cand3_key: int,
    binding_ok: int = 1,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/optimal_choice_certificate_v1.tau`.
    """
    return {
        "i1": _bv32("winner_index", winner_index),
        "i2": _u64("winner_key", winner_key),
        "i3": _u64("cand0_key", cand0_key),
        "i4": _u64("cand1_key", cand1_key),
        "i5": _u64("cand2_key", cand2_key),
        "i6": _u64("cand3_key", cand3_key),
        "i7": _sbf("binding_ok", binding_ok),
    }


def build_argmin_stream_certificate_v1_step(
    *,
    winner_key: int,
    winner_index: int,
    cand_key: int,
    cand_index: int,
    binding_ok: int = 1,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/argmin_stream_certificate_v1.tau`.
    """
    return {
        "i1": _u64("winner_key", winner_key),
        "i2": _bv32("winner_index", winner_index),
        "i3": _u64("cand_key", cand_key),
        "i4": _bv32("cand_index", cand_index),
        "i5": _sbf("binding_ok", binding_ok),
    }


def build_argmax_stream_certificate_v1_step(
    *,
    winner_key: int,
    winner_index: int,
    cand_key: int,
    cand_index: int,
    binding_ok: int = 1,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/argmax_stream_certificate_v1.tau`.
    """
    return {
        "i1": _u64("winner_key", winner_key),
        "i2": _bv32("winner_index", winner_index),
        "i3": _u64("cand_key", cand_key),
        "i4": _bv32("cand_index", cand_index),
        "i5": _sbf("binding_ok", binding_ok),
    }


def build_pool_params_binding_guard_v1_step(
    *,
    fee_bps: int,
    curve_code: int,
    canonical_order_ok: int = 1,
    curve_tag_ok: int = 1,
    curve_params_ok: int = 1,
    pool_id_ok: int = 1,
    binding_ok: int = 1,
) -> Dict[str, int]:
    """
    Build inputs for `src/tau_specs/recommended/pool_params_binding_guard_v1.tau`.
    """
    return {
        "i1": _bv32("fee_bps", fee_bps),
        "i2": _bv32("curve_code", curve_code),
        "i3": _sbf("canonical_order_ok", canonical_order_ok),
        "i4": _sbf("curve_tag_ok", curve_tag_ok),
        "i5": _sbf("curve_params_ok", curve_params_ok),
        "i6": _sbf("pool_id_ok", pool_id_ok),
        "i7": _sbf("binding_ok", binding_ok),
    }


# Finalized-price authority specs. V2 refs remain for historical replay;
# live transition admission uses V3.
ZUSD_ORACLE_COMMIT_GUARD_V3 = TauSpecRef(
    spec_id="zusd_oracle_commit_guard_v3",
    path=RECOMMENDED_SPECS_DIR / "zusd_oracle_commit_guard_v3.tau",
    gate_output="o4",
)

ZUSD_LIQUIDATION_GUARD_V3 = TauSpecRef(
    spec_id="zusd_liquidation_guard_v3",
    path=RECOMMENDED_SPECS_DIR / "zusd_liquidation_guard_v3.tau",
    gate_output="o4",
)


def build_zusd_oracle_commit_guard_v3_step(
    *,
    oracle_seen: int,
    pending_initialized: int,
    pending_le_active: int,
    auth_ok: int,
    fresh_ok: int,
) -> Dict[str, int]:
    return {
        "i1": _sbf("oracle_seen", oracle_seen),
        "i2": _sbf("pending_initialized", pending_initialized),
        "i3": _sbf("pending_le_active", pending_le_active),
        "i4": _sbf("auth_ok", auth_ok),
        "i5": _sbf("fresh_ok", fresh_ok),
    }


def build_zusd_liquidation_guard_v3_step(
    *,
    finalized_initialized: int,
    vault_debt: int,
    under_mcr_at_finalized: int,
    sp_debt: int,
    vault_coll: int,
    sp_coll_before: int,
    max_sp_coll: int,
    pending_matches_finalized: int,
    fresh_finalized: int,
) -> Dict[str, int]:
    return {
        "i1": _sbf("finalized_initialized", finalized_initialized),
        "i2": _u64("vault_debt", vault_debt),
        "i3": _sbf("under_mcr_at_finalized", under_mcr_at_finalized),
        "i4": _u64("sp_debt", sp_debt),
        "i5": _u64("vault_coll", vault_coll),
        "i6": _u64("sp_coll_before", sp_coll_before),
        "i7": _u64("max_sp_coll", max_sp_coll),
        "i8": _sbf("pending_matches_finalized", pending_matches_finalized),
        "i9": _sbf("fresh_finalized", fresh_finalized),
    }
