"""
Production Tau trace cases (pure, no IO).

These are small, deterministic traces meant to answer:
  "Does Tau execute this spec and emit the expected outputs on representative inputs?"
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, List

from .tau_runner import split_u32
from .tau_witness import (
    BALANCE_SAFETY_V1,
    BALANCE_TRANSITION_V1,
    BATCHING_V1,
    BATCHING_V1_4,
    BATCH_CANONICAL_V1_4,
    CPMM_V1,
    TOKEN_ARCHETYPE_LOCK_WEIGHTED_REWARDS_32_V2,
    TOKEN_ARCHETYPE_SOULBOUND_V2,
    TOKEN_ARCHETYPE_VESTING_CLIFF_32_V2,
    INTENT_EXPIRY_GUARD_V1,
    NONCE_REPLAY_GUARD_V1,
    GOVERNANCE_TIMELOCK_V1,
    PARAMETER_REGISTRY_V2,
    PROTOCOL_TOKEN_V3,
    REVISION_POLICY_V2,
    SETTLEMENT_V1_PROOF_GATE,
    SETTLEMENT_V2_BUYBACK_PROOF_GATE,
    SETTLEMENT_V3_BUYBACK_FLOOR_PROOF_GATE,
    SETTLEMENT_V4_BUYBACK_FLOOR_REBATE_LOCK_PROOF_GATE,
    SWAP_EXACT_IN_PROOF_GATE_V1,
    SWAP_EXACT_IN_V4,
    SWAP_EXACT_OUT_PROOF_GATE_V1,
    SWAP_EXACT_OUT_V4,
    TDEX_BUYBACK_FLOOR_FIXEDPOINT_V2,
    TDEX_BUYBACK_FLOOR_V2,
    TDEX_BUYBACK_PULSEX_V1,
    TDEX_FEE_REBATE_V1,
    TDEX_LOCK_WEIGHT_V1,
    TOKENOMICS_BUYBACK_BURN_V2,
    TOKEN_COMPOSITE_V2,
    TauSpecRef,
    build_balance_safety_v1_step,
    build_balance_transition_v1_step,
    build_batch_canonical_v1_4_step,
    build_batching_v1_4_step,
    build_batching_v1_step,
    build_cpmm_v1_step,
    build_token_archetype_lock_weighted_rewards_32_v2_step,
    build_token_archetype_soulbound_v2_step,
    build_token_archetype_vesting_cliff_32_v2_step,
    build_intent_expiry_guard_v1_step,
    build_nonce_replay_guard_v1_step,
    build_governance_timelock_v1_step,
    build_parameter_registry_v2_step,
    build_protocol_token_v3_step,
    build_revision_policy_v2_step,
    build_settlement_v1_proof_gate_step,
    build_settlement_v2_buyback_proof_gate_step,
    build_settlement_v3_buyback_floor_proof_gate_step,
    build_settlement_v4_buyback_floor_rebate_lock_proof_gate_step,
    build_swap_exact_in_proof_gate_v1_step,
    build_swap_exact_in_v4_step,
    build_swap_exact_out_proof_gate_v1_step,
    build_swap_exact_out_v4_step,
    build_tdex_buyback_floor_fixedpoint_v2_step,
    build_tdex_buyback_floor_v2_step,
    build_tdex_buyback_pulsex_v1_step,
    build_tdex_fee_rebate_v1_step,
    build_tdex_lock_weight_v1_step,
    build_token_composite_v2_step,
    build_tokenomics_buyback_burn_v2_step,
)


@dataclass(frozen=True)
class TauTraceCase:
    case_id: str
    spec: TauSpecRef
    steps: List[Dict[str, int]]
    expected: List[Dict[str, int]]
    mode: str = "repl"  # "repl" (IO harness) or "spec" (tau file-runner)
    timeout_s: float = 30.0
    inline_defs: bool = True
    experimental: bool = False


def production_tau_trace_cases() -> List[TauTraceCase]:
    cases: List[TauTraceCase] = []

    # Intent guards (recommended): replay protection + expiry
    cases.append(
        TauTraceCase(
            case_id="nonce_replay_guard_v1_pass",
            spec=NONCE_REPLAY_GUARD_V1,
            steps=[build_nonce_replay_guard_v1_step(intent_nonce=1, last_used_nonce=0, expected_nonce=1)],
            expected=[{"o4": 1}],
            timeout_s=10.0,
        )
    )
    cases.append(
        TauTraceCase(
            case_id="intent_expiry_guard_v1_pass",
            spec=INTENT_EXPIRY_GUARD_V1,
            steps=[
                build_intent_expiry_guard_v1_step(
                    intent_deadline=1100,
                    current_timestamp=1050,
                    min_validity_period=10,
                    max_validity_period=1000,
                    intent_created=1000,
                )
            ],
            expected=[{"o4": 1}],
            timeout_s=60.0,
        )
    )

    # Token archetypes: soulbound + lock-weighted rewards + vesting cliff
    cases.append(
        TauTraceCase(
            case_id="token_archetype_soulbound_v2_pass_transfer_issuer_involved",
            spec=TOKEN_ARCHETYPE_SOULBOUND_V2,
            steps=[build_token_archetype_soulbound_v2_step(from_id=1, to_id=2, issuer_id=1, do_transfer=1, do_mint=0, do_burn=0)],
            expected=[{"o4": 1}],
            timeout_s=60.0,
            inline_defs=False,
            experimental=False,
        )
    )
    cases.append(
        TauTraceCase(
            case_id="token_archetype_soulbound_v2_fail_transfer_between_users",
            spec=TOKEN_ARCHETYPE_SOULBOUND_V2,
            steps=[build_token_archetype_soulbound_v2_step(from_id=1, to_id=2, issuer_id=9, do_transfer=1, do_mint=0, do_burn=0)],
            expected=[{"o4": 0}],
            timeout_s=60.0,
            inline_defs=False,
            experimental=False,
        )
    )
    cases.append(
        TauTraceCase(
            case_id="token_archetype_lock_weighted_rewards_32_v1_pass",
            spec=TOKEN_ARCHETYPE_LOCK_WEIGHTED_REWARDS_32_V2,
            steps=[
                build_token_archetype_lock_weighted_rewards_32_v2_step(
                    stake_amount=10_000, lock_weight_bps=5000, reward_amount=5000, reward_cap=6000, proof_ok=1, binding_ok=1
                )
            ],
            expected=[{"o3": 1}],
            timeout_s=120.0,
            inline_defs=False,
            experimental=False,
        )
    )
    cases.append(
        TauTraceCase(
            case_id="token_archetype_lock_weighted_rewards_32_v1_fail_reward_too_high",
            spec=TOKEN_ARCHETYPE_LOCK_WEIGHTED_REWARDS_32_V2,
            steps=[
                build_token_archetype_lock_weighted_rewards_32_v2_step(
                    stake_amount=10_000, lock_weight_bps=5000, reward_amount=6000, reward_cap=10_000, proof_ok=0, binding_ok=1
                )
            ],
            expected=[{"o3": 0}],
            timeout_s=120.0,
            inline_defs=False,
            experimental=False,
        )
    )
    cases.append(
        TauTraceCase(
            case_id="token_archetype_vesting_cliff_32_v1_pass",
            spec=TOKEN_ARCHETYPE_VESTING_CLIFF_32_V2,
            steps=[
                build_token_archetype_vesting_cliff_32_v2_step(
                    total_allocation=10_000,
                    vested_amount=4000,
                    claim_amount=1000,
                    cliff_reached=1,
                    claim_cap_amount=2000,
                    max_claim_bps=2500,
                    proof_ok=1,
                    binding_ok=1,
                )
            ],
            expected=[{"o3": 1}],
            timeout_s=120.0,
            inline_defs=False,
            experimental=False,
        )
    )
    cases.append(
        TauTraceCase(
            case_id="token_archetype_vesting_cliff_32_v1_fail_cliff_not_reached",
            spec=TOKEN_ARCHETYPE_VESTING_CLIFF_32_V2,
            steps=[
                build_token_archetype_vesting_cliff_32_v2_step(
                    total_allocation=10_000,
                    vested_amount=0,
                    claim_amount=1,
                    cliff_reached=0,
                    claim_cap_amount=2000,
                    max_claim_bps=2500,
                    proof_ok=1,
                    binding_ok=1,
                )
            ],
            expected=[{"o3": 0}],
            timeout_s=120.0,
            inline_defs=False,
            experimental=False,
        )
    )

    # CPMM (structural, recommended)
    cases.append(
        TauTraceCase(
            case_id="cpmm_v1_pass",
            spec=CPMM_V1,
            steps=[build_cpmm_v1_step(reserve_in=1000, reserve_out=2000, amount_in=100, fee_bps=30, amount_out=180)],
            expected=[{"o1": 1}],
            timeout_s=30.0,
        )
    )
    cases.append(
        TauTraceCase(
            case_id="cpmm_v1_fail_amount_out_zero",
            spec=CPMM_V1,
            steps=[build_cpmm_v1_step(reserve_in=1000, reserve_out=2000, amount_in=100, fee_bps=30, amount_out=0)],
            expected=[{"o1": 0}],
            timeout_s=30.0,
        )
    )

    # Swap exact-in/out (proof gate + v4 structural guard)
    cases.append(
        TauTraceCase(
            case_id="swap_exact_in_proof_gate_v1_pass",
            spec=SWAP_EXACT_IN_PROOF_GATE_V1,
            steps=[
                build_swap_exact_in_proof_gate_v1_step(
                    reserve_in=1000,
                    reserve_out=2000,
                    amount_in=100,
                    fee_bps=30,
                    min_amount_out=1,
                    amount_out=180,
                    new_reserve_in=1100,
                    new_reserve_out=1820,
                )
            ],
            expected=[{"o1": 1}],
            timeout_s=10.0,
        )
    )
    cases.append(
        TauTraceCase(
            case_id="swap_exact_in_proof_gate_v1_fail_bad_reserve_out",
            spec=SWAP_EXACT_IN_PROOF_GATE_V1,
            steps=[
                build_swap_exact_in_proof_gate_v1_step(
                    reserve_in=1000,
                    reserve_out=2000,
                    amount_in=100,
                    fee_bps=30,
                    min_amount_out=1,
                    amount_out=180,
                    new_reserve_in=1100,
                    new_reserve_out=1819,
                )
            ],
            expected=[{"o1": 0}],
            timeout_s=10.0,
        )
    )
    cases.append(
        TauTraceCase(
            case_id="swap_exact_out_proof_gate_v1_pass",
            spec=SWAP_EXACT_OUT_PROOF_GATE_V1,
            steps=[
                build_swap_exact_out_proof_gate_v1_step(
                    reserve_in=1000,
                    reserve_out=2000,
                    amount_out=180,
                    fee_bps=30,
                    max_amount_in=200,
                    amount_in=100,
                    new_reserve_in=1100,
                    new_reserve_out=1820,
                )
            ],
            expected=[{"o1": 1}],
            timeout_s=10.0,
        )
    )
    cases.append(
        TauTraceCase(
            case_id="swap_exact_out_proof_gate_v1_fail_bad_amount_in",
            spec=SWAP_EXACT_OUT_PROOF_GATE_V1,
            steps=[
                build_swap_exact_out_proof_gate_v1_step(
                    reserve_in=1000,
                    reserve_out=2000,
                    amount_out=180,
                    fee_bps=30,
                    max_amount_in=99,
                    amount_in=100,
                    new_reserve_in=1100,
                    new_reserve_out=1820,
                )
            ],
            expected=[{"o1": 0}],
            timeout_s=10.0,
        )
    )

    cases.append(
        TauTraceCase(
            case_id="swap_exact_in_v4_pass",
            spec=SWAP_EXACT_IN_V4,
            steps=[
                build_swap_exact_in_v4_step(
                    reserve_in=1000,
                    reserve_out=2000,
                    amount_in=100,
                    fee_bps=30,
                    min_amount_out=1,
                    amount_out=180,
                    new_reserve_in=1100,
                    new_reserve_out=1820,
                )
            ],
            expected=[{"o1": 1}],
            timeout_s=90.0,
        )
    )
    cases.append(
        TauTraceCase(
            case_id="swap_exact_out_v4_pass",
            spec=SWAP_EXACT_OUT_V4,
            steps=[
                build_swap_exact_out_v4_step(
                    reserve_in=1000,
                    reserve_out=2000,
                    amount_out=180,
                    fee_bps=30,
                    max_amount_in=200,
                    amount_in=100,
                    new_reserve_in=1100,
                    new_reserve_out=1820,
                )
            ],
            expected=[{"o1": 1}],
            timeout_s=90.0,
        )
    )

    # Balance safety + transition
    cases.append(
        TauTraceCase(
            case_id="balance_safety_v1_basic",
            spec=BALANCE_SAFETY_V1,
            steps=[build_balance_safety_v1_step(balance_before=100, delta_add=1, delta_sub=2)],
            expected=[{"o1": 1}],
            timeout_s=10.0,
        )
    )
    cases.append(
        TauTraceCase(
            case_id="balance_transition_v1_pass",
            spec=BALANCE_TRANSITION_V1,
            steps=[
                build_balance_transition_v1_step(
                    balance_before=100,
                    delta_add=10,
                    delta_sub=5,
                    balance_mid=110,
                    balance_after=105,
                )
            ],
            expected=[{"o1": 1}],
            mode="spec",
            timeout_s=20.0,
        )
    )
    cases.append(
        TauTraceCase(
            case_id="balance_transition_v1_fail_bad_after",
            spec=BALANCE_TRANSITION_V1,
            steps=[
                build_balance_transition_v1_step(
                    balance_before=100,
                    delta_add=10,
                    delta_sub=5,
                    balance_mid=110,
                    balance_after=106,
                )
            ],
            expected=[{"o1": 0}],
            mode="spec",
            timeout_s=20.0,
        )
    )

    # Batching (canonical ordering)
    cases.append(
        TauTraceCase(
            case_id="batching_v1_pass",
            spec=BATCHING_V1,
            steps=[build_batching_v1_step(intent_a_id=1, intent_b_id=2, executed_first_id=1, executed_second_id=2)],
            expected=[{"o1": 1}],
            timeout_s=10.0,
        )
    )
    cases.append(
        TauTraceCase(
            case_id="batching_v1_fail_wrong_order",
            spec=BATCHING_V1,
            steps=[build_batching_v1_step(intent_a_id=1, intent_b_id=2, executed_first_id=2, executed_second_id=1)],
            expected=[{"o1": 0}],
            timeout_s=10.0,
        )
    )
    cases.append(
        TauTraceCase(
            case_id="batching_v1_4_pass",
            spec=BATCHING_V1_4,
            steps=[
                build_batching_v1_4_step(
                    intent_id_0=1,
                    intent_id_1=2,
                    intent_id_2=3,
                    intent_id_3=4,
                    executed_id_0=1,
                    executed_id_1=2,
                    executed_id_2=3,
                    executed_id_3=4,
                )
            ],
            expected=[{"o1": 1}],
            timeout_s=30.0,
        )
    )
    cases.append(
        TauTraceCase(
            case_id="batching_v1_4_fail_not_increasing",
            spec=BATCHING_V1_4,
            steps=[
                build_batching_v1_4_step(
                    intent_id_0=1,
                    intent_id_1=2,
                    intent_id_2=3,
                    intent_id_3=4,
                    executed_id_0=1,
                    executed_id_1=3,
                    executed_id_2=2,
                    executed_id_3=4,
                )
            ],
            expected=[{"o1": 0}],
            timeout_s=10.0,
        )
    )
    cases.append(
        TauTraceCase(
            case_id="batch_canonical_v1_4_pass",
            spec=BATCH_CANONICAL_V1_4,
            steps=[build_batch_canonical_v1_4_step(intent_id_0=1, intent_id_1=2, intent_id_2=3, intent_id_3=4)],
            expected=[{"o1": 1}],
            timeout_s=10.0,
        )
    )
    cases.append(
        TauTraceCase(
            case_id="batch_canonical_v1_4_fail_not_sorted",
            spec=BATCH_CANONICAL_V1_4,
            steps=[build_batch_canonical_v1_4_step(intent_id_0=1, intent_id_1=3, intent_id_2=2, intent_id_3=4)],
            expected=[{"o1": 0}],
            timeout_s=10.0,
        )
    )

    # Protocol token transition (recommended)
    cases.append(
        TauTraceCase(
            case_id="protocol_token_v2_transfer_pass",
            spec=PROTOCOL_TOKEN_V3,
            steps=[
                build_protocol_token_v3_step(
                    from_before=100,
                    to_before=50,
                    supply_before=1000,
                    amount=10,
                    from_after=90,
                    to_after=60,
                    supply_after=1000,
                    do_transfer=1,
                    do_mint=0,
                    do_burn=0,
                )
            ],
            expected=[{"o1": 1}],
            timeout_s=60.0,
            inline_defs=False,
            experimental=False,
        )
    )
    cases.append(
        TauTraceCase(
            case_id="protocol_token_v2_transfer_fail_supply_changed",
            spec=PROTOCOL_TOKEN_V3,
            steps=[
                build_protocol_token_v3_step(
                    from_before=100,
                    to_before=50,
                    supply_before=1000,
                    amount=10,
                    from_after=90,
                    to_after=60,
                    supply_after=999,
                    do_transfer=1,
                    do_mint=0,
                    do_burn=0,
                )
            ],
            expected=[{"o1": 0}],
            timeout_s=60.0,
            inline_defs=False,
            experimental=False,
        )
    )

    # Tokenomics: fee split + buyback/burn bounds (v2 is Tau-executable; v1 may time out)
    cases.append(
        TauTraceCase(
            case_id="tokenomics_buyback_burn_v2_pass",
            spec=TOKENOMICS_BUYBACK_BURN_V2,
            steps=[
                build_tokenomics_buyback_burn_v2_step(
                    fee_total=100,
                    fee_to_lp=50,
                    fee_to_treasury=30,
                    fee_to_burn=20,
                    buyback_triggered=1,
                    burn_amount=20,
                    burn_limit=25,
                )
            ],
            expected=[{"o1": 1}],
            timeout_s=15.0,
        )
    )
    cases.append(
        TauTraceCase(
            case_id="tokenomics_buyback_burn_v2_fail_fee_mismatch",
            spec=TOKENOMICS_BUYBACK_BURN_V2,
            steps=[
                build_tokenomics_buyback_burn_v2_step(
                    fee_total=99,
                    fee_to_lp=50,
                    fee_to_treasury=30,
                    fee_to_burn=20,
                    buyback_triggered=1,
                    burn_amount=20,
                    burn_limit=25,
                )
            ],
            expected=[{"o1": 0}],
            timeout_s=15.0,
        )
    )

    # TDEX buyback primitives (PulseX-style)
    cases.append(
        TauTraceCase(
            case_id="tdex_buyback_pulsex_v1_pass",
            spec=TDEX_BUYBACK_PULSEX_V1,
            steps=[build_tdex_buyback_pulsex_v1_step(trade_amount=10_000, fee_charged=29, buyback_amount=7, burned_amount=7)],
            expected=[{"o1": 1, "o2": 1, "o3": 1, "o4": 1}],
            timeout_s=10.0,
        )
    )
    cases.append(
        TauTraceCase(
            case_id="tdex_buyback_pulsex_v1_fail_bad_buyback_share",
            spec=TDEX_BUYBACK_PULSEX_V1,
            steps=[build_tdex_buyback_pulsex_v1_step(trade_amount=10_000, fee_charged=29, buyback_amount=6, burned_amount=6)],
            expected=[{"o4": 0}],
            timeout_s=10.0,
        )
    )

    cases.append(
        TauTraceCase(
            case_id="tdex_buyback_floor_v2_pass",
            spec=TDEX_BUYBACK_FLOOR_V2,
            steps=[
                build_tdex_buyback_floor_v2_step(
                    trade_amount=10_000,
                    fee_charged=29,
                    buyback_amount=7,
                    burned_amount=7,
                    supply_before=1000,
                    supply_after=993,
                    supply_floor=900,
                )
            ],
            expected=[{"o4": 1}],
            timeout_s=30.0,
            inline_defs=False,
        )
    )
    cases.append(
        TauTraceCase(
            case_id="tdex_buyback_floor_v2_fail_below_floor",
            spec=TDEX_BUYBACK_FLOOR_V2,
            steps=[
                build_tdex_buyback_floor_v2_step(
                    trade_amount=10_000,
                    fee_charged=29,
                    buyback_amount=7,
                    burned_amount=7,
                    supply_before=1000,
                    supply_after=892,
                    supply_floor=900,
                )
            ],
            expected=[{"o4": 0}],
            timeout_s=30.0,
            inline_defs=False,
        )
    )

    cases.append(
        TauTraceCase(
            case_id="tdex_buyback_floor_fixedpoint_v2_pass",
            spec=TDEX_BUYBACK_FLOOR_FIXEDPOINT_V2,
            steps=[
                build_tdex_buyback_floor_fixedpoint_v2_step(
                    trade_amount=10_000,
                    fee_charged=29,
                    buyback_amount=7,
                    burned_amount=7,
                    supply_before=1000,
                    supply_after=993,
                    supply_floor=900,
                    unit_scale=1,
                    unit_ok=1,
                )
            ],
            expected=[{"o5": 1}],
            timeout_s=30.0,
            inline_defs=False,
        )
    )
    cases.append(
        TauTraceCase(
            case_id="tdex_buyback_floor_fixedpoint_v2_fail_unit",
            spec=TDEX_BUYBACK_FLOOR_FIXEDPOINT_V2,
            steps=[
                build_tdex_buyback_floor_fixedpoint_v2_step(
                    trade_amount=10_000,
                    fee_charged=29,
                    buyback_amount=7,
                    burned_amount=7,
                    supply_before=1000,
                    supply_after=993,
                    supply_floor=900,
                    unit_scale=2,
                    unit_ok=0,
                )
            ],
            expected=[{"o5": 0}],
            timeout_s=30.0,
            inline_defs=False,
        )
    )

    # Fee rebate and lock weight primitives
    cases.append(
        TauTraceCase(
            case_id="tdex_fee_rebate_v1_pass",
            spec=TDEX_FEE_REBATE_V1,
            steps=[build_tdex_fee_rebate_v1_step(trade_fee=29, rebate_rate_bps=50, rebate_amount=1, rebate_cap=10)],
            expected=[{"o3": 1}],
            timeout_s=10.0,
        )
    )
    cases.append(
        TauTraceCase(
            case_id="tdex_fee_rebate_v1_fail_rebate_zero",
            spec=TDEX_FEE_REBATE_V1,
            steps=[build_tdex_fee_rebate_v1_step(trade_fee=29, rebate_rate_bps=50, rebate_amount=0, rebate_cap=10)],
            expected=[{"o3": 0}],
            timeout_s=10.0,
        )
    )
    cases.append(
        TauTraceCase(
            case_id="tdex_lock_weight_v1_pass",
            spec=TDEX_LOCK_WEIGHT_V1,
            steps=[
                build_tdex_lock_weight_v1_step(
                    lock_days=30,
                    stake_amount=100,
                    tier1_days=10,
                    tier2_days=100,
                    weight_t1=1,
                    weight_t2=2,
                    weight_t3=3,
                    weight_claimed=2,
                    weighted_stake=200,
                )
            ],
            expected=[{"o4": 1}],
            timeout_s=10.0,
        )
    )
    cases.append(
        TauTraceCase(
            case_id="tdex_lock_weight_v1_fail_bad_weight",
            spec=TDEX_LOCK_WEIGHT_V1,
            steps=[
                build_tdex_lock_weight_v1_step(
                    lock_days=30,
                    stake_amount=100,
                    tier1_days=10,
                    tier2_days=100,
                    weight_t1=1,
                    weight_t2=2,
                    weight_t3=3,
                    weight_claimed=3,
                    weighted_stake=300,
                )
            ],
            expected=[{"o4": 0}],
            timeout_s=10.0,
        )
    )

    # Token composite (base-case at t=0)
    cases.append(
        TauTraceCase(
            case_id="token_composite_v2_base_then_valid",
            spec=TOKEN_COMPOSITE_V2,
            steps=[
                build_token_composite_v2_step(
                    burn_allowed=0,
                    never_zero_guaranteed=0,
                    feature_config_valid=0,
                ),
                build_token_composite_v2_step(
                    burn_allowed=1,
                    never_zero_guaranteed=1,
                    feature_config_valid=1,
                ),
            ],
            expected=[{"o4": 0}, {"o4": 1}],
            timeout_s=10.0,
        )
    )

    # Settlement composites (proof-gated, per-step rails)
    cases.append(
        TauTraceCase(
            case_id="settlement_v1_proof_gate_pass",
            spec=SETTLEMENT_V1_PROOF_GATE,
            steps=[build_settlement_v1_proof_gate_step(a=1, b=2, c=3, d=4, price_pp=1000, price_prev=1001, price_curr=1002)],
            expected=[{"o7": 1}],
            mode="spec",
            timeout_s=20.0,
            inline_defs=False,
        )
    )
    cases.append(
        TauTraceCase(
            case_id="settlement_v1_proof_gate_fail_no_sandwich",
            spec=SETTLEMENT_V1_PROOF_GATE,
            steps=[build_settlement_v1_proof_gate_step(a=1, b=2, c=3, d=4, price_pp=1100, price_prev=1000, price_curr=1001)],
            expected=[{"o7": 0}],
            mode="spec",
            timeout_s=20.0,
            inline_defs=False,
        )
    )

    cases.append(
        TauTraceCase(
            case_id="settlement_v2_buyback_proof_gate_pass",
            spec=SETTLEMENT_V2_BUYBACK_PROOF_GATE,
            steps=[
                build_settlement_v2_buyback_proof_gate_step(a=1, b=2, c=3, d=4, price_pp=1000, price_prev=1001, price_curr=1002, buyback_ok=1)
            ],
            expected=[{"o8": 1}],
            mode="spec",
            timeout_s=20.0,
            inline_defs=False,
        )
    )
    cases.append(
        TauTraceCase(
            case_id="settlement_v2_buyback_proof_gate_fail_buyback",
            spec=SETTLEMENT_V2_BUYBACK_PROOF_GATE,
            steps=[
                build_settlement_v2_buyback_proof_gate_step(a=1, b=2, c=3, d=4, price_pp=1000, price_prev=1001, price_curr=1002, buyback_ok=0)
            ],
            expected=[{"o8": 0}],
            mode="spec",
            timeout_s=20.0,
            inline_defs=False,
        )
    )

    cases.append(
        TauTraceCase(
            case_id="settlement_v3_buyback_floor_proof_gate_pass",
            spec=SETTLEMENT_V3_BUYBACK_FLOOR_PROOF_GATE,
            steps=[
                build_settlement_v3_buyback_floor_proof_gate_step(a=1, b=2, c=3, d=4, price_pp=1000, price_prev=1001, price_curr=1002, buyback_ok=1)
            ],
            expected=[{"o8": 1}],
            mode="spec",
            timeout_s=20.0,
            inline_defs=False,
        )
    )
    cases.append(
        TauTraceCase(
            case_id="settlement_v3_buyback_floor_proof_gate_fail_floor",
            spec=SETTLEMENT_V3_BUYBACK_FLOOR_PROOF_GATE,
            steps=[
                build_settlement_v3_buyback_floor_proof_gate_step(a=1, b=2, c=3, d=4, price_pp=1000, price_prev=1001, price_curr=1002, buyback_ok=0)
            ],
            expected=[{"o8": 0}],
            mode="spec",
            timeout_s=20.0,
            inline_defs=False,
        )
    )

    cases.append(
        TauTraceCase(
            case_id="settlement_v4_buyback_floor_rebate_lock_proof_gate_pass",
            spec=SETTLEMENT_V4_BUYBACK_FLOOR_REBATE_LOCK_PROOF_GATE,
            steps=[
                build_settlement_v4_buyback_floor_rebate_lock_proof_gate_step(
                    a=1,
                    b=2,
                    c=3,
                    d=4,
                    price_pp=1000,
                    price_prev=1001,
                    price_curr=1002,
                    buyback_floor_ok=1,
                    buyback_floor_fixedpoint_ok=1,
                    rebate_ok=1,
                    lock_weight_ok=1,
                )
            ],
            expected=[{"o11": 1}],
            mode="spec",
            timeout_s=20.0,
            inline_defs=False,
        )
    )
    cases.append(
        TauTraceCase(
            case_id="settlement_v4_buyback_floor_rebate_lock_proof_gate_fail_lock_weight",
            spec=SETTLEMENT_V4_BUYBACK_FLOOR_REBATE_LOCK_PROOF_GATE,
            steps=[
                build_settlement_v4_buyback_floor_rebate_lock_proof_gate_step(
                    a=1,
                    b=2,
                    c=3,
                    d=4,
                    price_pp=1000,
                    price_prev=1001,
                    price_curr=1002,
                    buyback_floor_ok=1,
                    buyback_floor_fixedpoint_ok=1,
                    rebate_ok=1,
                    lock_weight_ok=0,
                )
            ],
            expected=[{"o11": 0}],
            mode="spec",
            timeout_s=20.0,
            inline_defs=False,
        )
    )

    # Governance timelock (base-case at t=0)
    cases.append(
        TauTraceCase(
            case_id="governance_timelock_v1_base_then_valid",
            spec=GOVERNANCE_TIMELOCK_V1,
            steps=[
                build_governance_timelock_v1_step(proposal_ts=0, current_ts=0, min_delay=0, exec_req=0),
                build_governance_timelock_v1_step(proposal_ts=10, current_ts=20, min_delay=5, exec_req=1),
            ],
            expected=[{"o1": 1, "o2": 0, "o3": 1, "o4": 1}, {"o1": 1, "o2": 1, "o3": 1, "o4": 1}],
            timeout_s=20.0,
        )
    )

    # Revision policy (proof-gated)
    cases.append(
        TauTraceCase(
            case_id="revision_policy_v2_pass",
            spec=REVISION_POLICY_V2,
            steps=[build_revision_policy_v2_step(approved=1, exec_req=1, governance_ok=1, revision_ok=1)],
            expected=[{"o10": 1}],
            timeout_s=10.0,
        )
    )
    cases.append(
        TauTraceCase(
            case_id="revision_policy_v2_fail_not_approved",
            spec=REVISION_POLICY_V2,
            steps=[build_revision_policy_v2_step(approved=0, exec_req=1, governance_ok=1, revision_ok=1)],
            expected=[{"o10": 0}],
            timeout_s=10.0,
        )
    )

    # Parameter registry (applies updates)
    fnext_hi, fnext_lo = split_u32(910)
    fcurr_hi, fcurr_lo = split_u32(900)
    cases.append(
        TauTraceCase(
            case_id="parameter_registry_v2_gate_on",
            spec=PARAMETER_REGISTRY_V2,
            steps=[
                build_parameter_registry_v2_step(
                    exec_req=1,
                    revision_ok=1,
                    fee_applied=31,
                    buyback_applied=22,
                    rebate_applied=51,
                    floor_applied=910,
                    unit_applied=2,
                    tier1_applied=11,
                    tier2_applied=101,
                    weight1_applied=1,
                    weight2_applied=2,
                    weight3_applied=3,
                )
            ],
            expected=[
                {
                    "o1": 1,
                    "o2": 31,
                    "o3": 22,
                    "o4": 51,
                    "o5": int(fnext_hi),
                    "o6": int(fnext_lo),
                    "o7": 2,
                    "o8": 11,
                    "o9": 101,
                    "o10": 1,
                    "o11": 2,
                    "o12": 3,
                }
            ],
            timeout_s=20.0,
        )
    )
    cases.append(
        TauTraceCase(
            case_id="parameter_registry_v2_gate_off",
            spec=PARAMETER_REGISTRY_V2,
            steps=[
                build_parameter_registry_v2_step(
                    exec_req=1,
                    revision_ok=0,
                    fee_applied=30,
                    buyback_applied=21,
                    rebate_applied=50,
                    floor_applied=900,
                    unit_applied=1,
                    tier1_applied=10,
                    tier2_applied=100,
                    weight1_applied=1,
                    weight2_applied=2,
                    weight3_applied=3,
                )
            ],
            expected=[
                {
                    "o1": 0,
                    "o2": 30,
                    "o3": 21,
                    "o4": 50,
                    "o5": int(fcurr_hi),
                    "o6": int(fcurr_lo),
                    "o7": 1,
                    "o8": 10,
                    "o9": 100,
                    "o10": 1,
                    "o11": 2,
                    "o12": 3,
                }
            ],
            timeout_s=20.0,
        )
    )

    return cases
