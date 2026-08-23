"""
Fail-closed Tau transition gate for zUSD state machines.

This module keeps Tau IO outside the pure `src/core/zusd.py` kernel while
allowing transition-level policy checks to run before accepting a state update.
"""

from __future__ import annotations

import os
from dataclasses import dataclass, replace
from typing import Dict, List, Mapping, Optional, Tuple

from ..core.zusd import (
    ZUSDCommand,
    ZUSDMultiCommand,
    ZUSDMultiState,
    ZUSDMultiStepResult,
    ZUSDState,
    ZUSDStepResult,
    check_invariants,
    check_multi_invariants,
    in_multi_recovery_mode,
    in_recovery_mode,
)
from ..core.zusd import (
    step as zusd_step,
)
from ..core.zusd import (
    step_multi as zusd_step_multi,
)
from ..core.zusd_multi_redeem_selector import select_multi_redeem_vault
from .tau_runner import find_tau_bin, run_tau_spec_steps
from .tau_witness import (
    ZUSD_DEPOSIT_SP_GUARD_V1,
    ZUSD_LIQUIDATION_GUARD_V3,
    ZUSD_MINT_GUARD_V1,
    ZUSD_ORACLE_COMMIT_GUARD_V3,
    ZUSD_REDEEM_GUARD_V1,
    ZUSD_REPAY_GUARD_V1,
    ZUSD_SUPPLY_CONSERVATION_V3,
    ZUSD_WITHDRAW_COLLATERAL_GUARD_V1,
    ZUSD_WITHDRAW_SP_GUARD_V1,
    TauSpecRef,
    build_zusd_deposit_sp_guard_v1_step,
    build_zusd_liquidation_guard_v3_step,
    build_zusd_mint_guard_v1_step,
    build_zusd_oracle_commit_guard_v3_step,
    build_zusd_redeem_guard_v1_step,
    build_zusd_repay_guard_v1_step,
    build_zusd_supply_conservation_v3_step,
    build_zusd_withdraw_collateral_guard_v1_step,
    build_zusd_withdraw_sp_guard_v1_step,
)


@dataclass(frozen=True)
class ZUSDTauGateConfig:
    """
    Controls whether and how zUSD Tau transition checks run.

    Default is disabled so zUSD core logic does not require a local Tau binary.
    """

    enabled: bool = False
    timeout_s: float = 2.0
    tau_bin: Optional[str] = None
    allow_path_lookup: bool = False


DEFAULT_ZUSD_TAU_GATE_CONFIG = ZUSDTauGateConfig()


def _is_oracle_fresh(*, now_epoch: int, last_update_epoch: int, max_staleness_epochs: int, oracle_seen: bool) -> bool:
    if not oracle_seen:
        return False
    if max_staleness_epochs < 0:
        return False
    if last_update_epoch > now_epoch:
        return False
    return (now_epoch - last_update_epoch) <= max_staleness_epochs


def _mcr_ok(*, collateral_e8: int, debt_e8: int, price_e8: int, mcr_bps: int) -> bool:
    if debt_e8 == 0:
        return True
    return (collateral_e8 * price_e8 * 10_000) >= (debt_e8 * mcr_bps * 100_000_000)


def _cmd_auth_ok(args: Mapping[str, object]) -> bool:
    return args.get("auth_ok") is True


def _single_risky_ops_allowed(state: ZUSDState) -> bool:
    if not state.oracle_seen or state.price_e8 <= 0 or state.price_pending_e8 <= 0:
        return False
    if state.price_pending_e8 != state.price_e8:
        return False
    if state.oracle_pending_update_epoch != state.oracle_last_update_epoch:
        return False
    if not _is_oracle_fresh(
        now_epoch=state.now_epoch,
        last_update_epoch=state.oracle_last_update_epoch,
        max_staleness_epochs=state.max_oracle_staleness_epochs,
        oracle_seen=state.oracle_seen,
    ):
        return False
    if in_recovery_mode(state):
        return False
    return True


def _multi_risky_ops_allowed(state: ZUSDMultiState) -> bool:
    if not state.oracle_seen or state.price_e8 <= 0 or state.price_pending_e8 <= 0:
        return False
    if state.price_pending_e8 != state.price_e8:
        return False
    if state.oracle_pending_update_epoch != state.oracle_last_update_epoch:
        return False
    if not _is_oracle_fresh(
        now_epoch=state.now_epoch,
        last_update_epoch=state.oracle_last_update_epoch,
        max_staleness_epochs=state.max_oracle_staleness_epochs,
        oracle_seen=state.oracle_seen,
    ):
        return False
    if in_multi_recovery_mode(state):
        return False
    return True


def _require_pos_int_arg(args: Mapping[str, object], key: str) -> int:
    v = args.get(key)
    if not isinstance(v, int) or isinstance(v, bool) or v <= 0:
        raise ValueError(f"{key} must be a positive int")
    return int(v)


def _single_oracle_commit_candidate_ok(
    pre_state: ZUSDState,
    post_state: ZUSDState,
) -> bool:
    expected = replace(
        pre_state,
        price_e8=pre_state.price_pending_e8,
        oracle_last_update_epoch=pre_state.oracle_pending_update_epoch,
    )
    return post_state == expected and check_invariants(post_state) == []


def _multi_oracle_commit_candidate_ok(
    pre_state: ZUSDMultiState,
    post_state: ZUSDMultiState,
) -> bool:
    expected = replace(
        pre_state,
        price_e8=pre_state.price_pending_e8,
        oracle_last_update_epoch=pre_state.oracle_pending_update_epoch,
    )
    return post_state == expected and check_multi_invariants(post_state) == []


def _liquidation_destination_amounts(
    *,
    collateral_e8: int,
    fixed_compensation_e8: int,
    variable_compensation_bps: int,
) -> tuple[int, int]:
    variable_compensation_e8 = (
        (collateral_e8 * variable_compensation_bps) + 9_999
    ) // 10_000
    liquidator_compensation_e8 = min(
        collateral_e8,
        fixed_compensation_e8 + variable_compensation_e8,
    )
    return (
        liquidator_compensation_e8,
        collateral_e8 - liquidator_compensation_e8,
    )


def _single_liquidation_projection_flags(
    pre_state: ZUSDState,
    post_state: ZUSDState,
) -> tuple[bool, bool, bool]:
    expected_compensation_e8, expected_sp_gain_e8 = (
        _liquidation_destination_amounts(
            collateral_e8=pre_state.collateral_e8,
            fixed_compensation_e8=(
                pre_state.liquidation_gas_comp_fixed_collateral_e8
            ),
            variable_compensation_bps=pre_state.liquidation_gas_comp_bps,
        )
    )
    collateral_destinations_exact = (
        post_state.liquidator_compensation_collateral_cum_e8
        - pre_state.liquidator_compensation_collateral_cum_e8
        == expected_compensation_e8
        and post_state.sp_coll_e8 - pre_state.sp_coll_e8
        == expected_sp_gain_e8
    )
    stability_pool_collateral_cap_ok = (
        post_state.sp_coll_e8 <= pre_state.max_sp_coll_e8
    )
    state_delta_ok = post_state == replace(
        pre_state,
        debt_e8=0,
        collateral_e8=0,
        sp_debt_e8=pre_state.sp_debt_e8 - pre_state.debt_e8,
        sp_coll_e8=pre_state.sp_coll_e8 + expected_sp_gain_e8,
        liquidator_compensation_collateral_cum_e8=(
            pre_state.liquidator_compensation_collateral_cum_e8
            + expected_compensation_e8
        ),
    )
    return (
        collateral_destinations_exact,
        stability_pool_collateral_cap_ok,
        state_delta_ok,
    )


def _multi_liquidation_projection_flags(
    pre_state: ZUSDMultiState,
    post_state: ZUSDMultiState,
    cmd: ZUSDMultiCommand,
) -> tuple[bool, bool, bool]:
    raw_vault = cmd.args.get("vault")
    if raw_vault == "a":
        pre_vault = pre_state.vault_a
        vault_update = {"vault_a": replace(pre_vault, collateral_e8=0, debt_e8=0)}
    elif raw_vault == "b":
        pre_vault = pre_state.vault_b
        vault_update = {"vault_b": replace(pre_vault, collateral_e8=0, debt_e8=0)}
    else:
        raise ValueError("vault must be 'a' or 'b'")

    expected_compensation_e8, expected_sp_gain_e8 = (
        _liquidation_destination_amounts(
            collateral_e8=pre_vault.collateral_e8,
            fixed_compensation_e8=(
                pre_state.liquidation_gas_comp_fixed_collateral_e8
            ),
            variable_compensation_bps=pre_state.liquidation_gas_comp_bps,
        )
    )
    collateral_destinations_exact = (
        post_state.liquidator_compensation_collateral_cum_e8
        - pre_state.liquidator_compensation_collateral_cum_e8
        == expected_compensation_e8
        and post_state.sp_coll_e8 - pre_state.sp_coll_e8
        == expected_sp_gain_e8
    )
    stability_pool_collateral_cap_ok = (
        post_state.sp_coll_e8 <= pre_state.max_sp_coll_e8
    )
    state_delta_ok = post_state == replace(
        pre_state,
        **vault_update,
        sp_debt_e8=pre_state.sp_debt_e8 - pre_vault.debt_e8,
        sp_coll_e8=pre_state.sp_coll_e8 + expected_sp_gain_e8,
        liquidator_compensation_collateral_cum_e8=(
            pre_state.liquidator_compensation_collateral_cum_e8
            + expected_compensation_e8
        ),
    )
    return (
        collateral_destinations_exact,
        stability_pool_collateral_cap_ok,
        state_delta_ok,
    )


def _resolve_tau_bin(config: ZUSDTauGateConfig) -> tuple[bool, Optional[str], Optional[str]]:
    if config.tau_bin:
        tau_bin = config.tau_bin
        if not config.allow_path_lookup:
            if not os.path.isabs(tau_bin):
                return False, None, "tau_bin must be an absolute path when allow_path_lookup=False"
            if not (os.path.isfile(tau_bin) and os.access(tau_bin, os.X_OK)):
                return False, None, f"tau_bin is not an executable file: {tau_bin}"
        return True, tau_bin, None
    if config.allow_path_lookup:
        tau_bin = find_tau_bin()
        if tau_bin:
            return True, tau_bin, None
        return False, None, "tau binary not found (fail-closed)"
    return False, None, "tau_bin not configured (set ZUSDTauGateConfig.tau_bin)"


def _require_gate_ok(outputs_by_step: Dict[int, Dict[str, int]], *, spec_ref: TauSpecRef) -> tuple[bool, Optional[str]]:
    out = outputs_by_step.get(0, {})
    value = out.get(spec_ref.gate_output)
    if value is None:
        return False, f"Tau missing {spec_ref.gate_output} for {spec_ref.spec_id}"
    if int(value) != 1:
        return False, f"Tau gate failed for {spec_ref.spec_id} ({spec_ref.gate_output}=0)"
    return True, None


def _single_checks(
    *, pre_state: ZUSDState, cmd: ZUSDCommand, post_state: ZUSDState
) -> List[Tuple[TauSpecRef, Dict[str, int]]]:
    checks: List[Tuple[TauSpecRef, Dict[str, int]]] = []

    if cmd.tag == "oracle_commit":
        checks.append(
            (
                ZUSD_ORACLE_COMMIT_GUARD_V3,
                build_zusd_oracle_commit_guard_v3_step(
                    oracle_seen=1 if pre_state.oracle_seen else 0,
                    pending_price_positive=(
                        1 if pre_state.price_pending_e8 > 0 else 0
                    ),
                    pending_observation_fresh=1
                    if _is_oracle_fresh(
                        now_epoch=pre_state.now_epoch,
                        last_update_epoch=pre_state.oracle_pending_update_epoch,
                        max_staleness_epochs=pre_state.max_oracle_staleness_epochs,
                        oracle_seen=pre_state.oracle_seen,
                    )
                    else 0,
                    auth_ok=1 if _cmd_auth_ok(cmd.args) else 0,
                    commit_candidate_ok=1
                    if _single_oracle_commit_candidate_ok(
                        pre_state,
                        post_state,
                    )
                    else 0,
                ),
            )
        )

    elif cmd.tag == "mint_zusd":
        amount = _require_pos_int_arg(cmd.args, "amount_e8")
        checks.append(
            (
                ZUSD_MINT_GUARD_V1,
                build_zusd_mint_guard_v1_step(
                    amount=amount,
                    debt_before=pre_state.debt_e8,
                    free_before=pre_state.free_debt_e8,
                    debt_after=post_state.debt_e8,
                    free_after=post_state.free_debt_e8,
                    risky_ops_allowed=1 if _single_risky_ops_allowed(pre_state) else 0,
                    min_open_ok=1 if not (pre_state.debt_e8 == 0 and amount < pre_state.min_debt_open_e8) else 0,
                    max_vault_ok=1 if post_state.debt_e8 <= pre_state.max_debt_e8 else 0,
                    max_supply_ok=1 if post_state.free_debt_e8 <= pre_state.max_debt_supply_e8 else 0,
                    mcr_post_ok=1
                    if _mcr_ok(
                        collateral_e8=pre_state.collateral_e8,
                        debt_e8=post_state.debt_e8,
                        price_e8=pre_state.price_e8,
                        mcr_bps=pre_state.mcr_bps,
                    )
                    else 0,
                ),
            )
        )

    elif cmd.tag == "repay_zusd":
        amount = _require_pos_int_arg(cmd.args, "amount_e8")
        checks.append(
            (
                ZUSD_REPAY_GUARD_V1,
                build_zusd_repay_guard_v1_step(
                    amount=amount,
                    debt_before=pre_state.debt_e8,
                    free_before=pre_state.free_debt_e8,
                    debt_after=post_state.debt_e8,
                    free_after=post_state.free_debt_e8,
                ),
            )
        )

    elif cmd.tag == "redeem_zusd":
        amount = _require_pos_int_arg(cmd.args, "amount_e8")
        checks.append(
            (
                ZUSD_REDEEM_GUARD_V1,
                build_zusd_redeem_guard_v1_step(
                    amount=amount,
                    debt_before=pre_state.debt_e8,
                    free_before=pre_state.free_debt_e8,
                    collateral_before=pre_state.collateral_e8,
                    debt_after=post_state.debt_e8,
                    free_after=post_state.free_debt_e8,
                    collateral_after=post_state.collateral_e8,
                    gross_collateral=pre_state.collateral_e8 - post_state.collateral_e8,
                    fee_collateral=post_state.protocol_collateral_e8 - pre_state.protocol_collateral_e8,
                    oracle_ok=1
                    if (
                        pre_state.oracle_seen
                        and pre_state.price_e8 > 0
                        and pre_state.price_pending_e8 > 0
                        and pre_state.price_pending_e8 == pre_state.price_e8
                        and _is_oracle_fresh(
                            now_epoch=pre_state.now_epoch,
                            last_update_epoch=pre_state.oracle_last_update_epoch,
                            max_staleness_epochs=pre_state.max_oracle_staleness_epochs,
                            oracle_seen=pre_state.oracle_seen,
                        )
                    )
                    else 0,
                    mcr_post_ok=1
                    if _mcr_ok(
                        collateral_e8=post_state.collateral_e8,
                        debt_e8=post_state.debt_e8,
                        price_e8=pre_state.price_e8,
                        mcr_bps=pre_state.mcr_bps,
                    )
                    else 0,
                    fee_cap_ok=1 if post_state.protocol_collateral_e8 <= pre_state.max_protocol_coll_e8 else 0,
                ),
            )
        )

    elif cmd.tag == "withdraw_collateral":
        amount = _require_pos_int_arg(cmd.args, "amount_e8")
        checks.append(
            (
                ZUSD_WITHDRAW_COLLATERAL_GUARD_V1,
                build_zusd_withdraw_collateral_guard_v1_step(
                    amount=amount,
                    collateral_before=pre_state.collateral_e8,
                    collateral_after=post_state.collateral_e8,
                    debt_before=pre_state.debt_e8,
                    risky_ops_allowed=1 if _single_risky_ops_allowed(pre_state) else 0,
                    mcr_post_ok=1
                    if _mcr_ok(
                        collateral_e8=post_state.collateral_e8,
                        debt_e8=pre_state.debt_e8,
                        price_e8=pre_state.price_e8,
                        mcr_bps=pre_state.mcr_bps,
                    )
                    else 0,
                ),
            )
        )

    elif cmd.tag == "deposit_sp":
        amount = _require_pos_int_arg(cmd.args, "amount_e8")
        checks.append(
            (
                ZUSD_DEPOSIT_SP_GUARD_V1,
                build_zusd_deposit_sp_guard_v1_step(
                    amount=amount,
                    free_before=pre_state.free_debt_e8,
                    sp_before=pre_state.sp_debt_e8,
                    free_after=post_state.free_debt_e8,
                    sp_after=post_state.sp_debt_e8,
                    max_supply_ok=1 if post_state.sp_debt_e8 <= pre_state.max_debt_supply_e8 else 0,
                ),
            )
        )

    elif cmd.tag == "withdraw_sp":
        amount = _require_pos_int_arg(cmd.args, "amount_e8")
        checks.append(
            (
                ZUSD_WITHDRAW_SP_GUARD_V1,
                build_zusd_withdraw_sp_guard_v1_step(
                    amount=amount,
                    free_before=pre_state.free_debt_e8,
                    sp_before=pre_state.sp_debt_e8,
                    free_after=post_state.free_debt_e8,
                    sp_after=post_state.sp_debt_e8,
                    risky_ops_allowed=1 if _single_risky_ops_allowed(pre_state) else 0,
                    vault_mcr_ok=1
                    if _mcr_ok(
                        collateral_e8=pre_state.collateral_e8,
                        debt_e8=pre_state.debt_e8,
                        price_e8=pre_state.price_e8,
                        mcr_bps=pre_state.mcr_bps,
                    )
                    else 0,
                ),
            )
        )

    elif cmd.tag == "liquidate":
        (
            collateral_destinations_exact,
            stability_pool_collateral_cap_ok,
            state_delta_ok,
        ) = _single_liquidation_projection_flags(pre_state, post_state)
        checks.append(
            (
                ZUSD_LIQUIDATION_GUARD_V3,
                build_zusd_liquidation_guard_v3_step(
                    committed_oracle_initialized=(
                        1
                        if pre_state.oracle_seen and pre_state.price_e8 > 0
                        else 0
                    ),
                    no_uncommitted_report=(
                        1
                        if (
                            pre_state.price_pending_e8 == pre_state.price_e8
                            and pre_state.oracle_pending_update_epoch
                            == pre_state.oracle_last_update_epoch
                        )
                        else 0
                    ),
                    committed_oracle_fresh=1
                    if _is_oracle_fresh(
                        now_epoch=pre_state.now_epoch,
                        last_update_epoch=pre_state.oracle_last_update_epoch,
                        max_staleness_epochs=pre_state.max_oracle_staleness_epochs,
                        oracle_seen=pre_state.oracle_seen,
                    )
                    else 0,
                    positive_debt=1 if pre_state.debt_e8 > 0 else 0,
                    under_mcr_at_committed_price=1
                    if not _mcr_ok(
                        collateral_e8=pre_state.collateral_e8,
                        debt_e8=pre_state.debt_e8,
                        price_e8=pre_state.price_e8,
                        mcr_bps=pre_state.mcr_bps,
                    )
                    else 0,
                    stability_pool_can_absorb=(
                        1 if pre_state.sp_debt_e8 >= pre_state.debt_e8 else 0
                    ),
                    collateral_destinations_exact=(
                        1 if collateral_destinations_exact else 0
                    ),
                    stability_pool_collateral_cap_ok=(
                        1 if stability_pool_collateral_cap_ok else 0
                    ),
                    state_delta_ok=1 if state_delta_ok else 0,
                ),
            )
        )

    checks.append(
        (
            ZUSD_SUPPLY_CONSERVATION_V3,
            build_zusd_supply_conservation_v3_step(
                pre_conservation_ok=1
                if (
                    pre_state.free_debt_e8 + pre_state.sp_debt_e8
                    == pre_state.debt_e8
                )
                else 0,
                post_conservation_ok=1
                if (
                    post_state.free_debt_e8 + post_state.sp_debt_e8
                    == post_state.debt_e8
                )
                else 0,
                transition_delta_ok=1
                if (
                    post_state.debt_e8 - pre_state.debt_e8
                    == (
                        post_state.free_debt_e8 - pre_state.free_debt_e8
                        + post_state.sp_debt_e8
                        - pre_state.sp_debt_e8
                    )
                )
                else 0,
            ),
        )
    )
    return checks


def _multi_total_debt(state: ZUSDMultiState) -> int:
    return state.vault_a.debt_e8 + state.vault_b.debt_e8


def _multi_vault_for_cmd(state: ZUSDMultiState, cmd: ZUSDMultiCommand) -> tuple[int, int]:
    raw = cmd.args.get("vault")
    if raw == "a":
        return state.vault_a.collateral_e8, state.vault_a.debt_e8
    if raw == "b":
        return state.vault_b.collateral_e8, state.vault_b.debt_e8
    raise ValueError("vault must be 'a' or 'b'")


def _infer_multi_redeem_vault(pre_state: ZUSDMultiState, post_state: ZUSDMultiState) -> str:
    a_changed = (
        pre_state.vault_a.debt_e8 != post_state.vault_a.debt_e8
        or pre_state.vault_a.collateral_e8 != post_state.vault_a.collateral_e8
    )
    b_changed = (
        pre_state.vault_b.debt_e8 != post_state.vault_b.debt_e8
        or pre_state.vault_b.collateral_e8 != post_state.vault_b.collateral_e8
    )
    if a_changed and not b_changed:
        return "a"
    if b_changed and not a_changed:
        return "b"
    raise ValueError("unable to infer redeemed vault from state delta")


def _expected_multi_redeem_vault(pre_state: ZUSDMultiState, *, amount_e8: int) -> str:
    selection = select_multi_redeem_vault(
        amount_e8=amount_e8,
        price_e8=pre_state.price_e8,
        mcr_bps=pre_state.mcr_bps,
        vault_a_collateral_e8=pre_state.vault_a.collateral_e8,
        vault_a_debt_e8=pre_state.vault_a.debt_e8,
        vault_b_collateral_e8=pre_state.vault_b.collateral_e8,
        vault_b_debt_e8=pre_state.vault_b.debt_e8,
    )
    if selection.selected_vault is None:
        raise ValueError("no redeemable vault for amount under policy")
    return str(selection.selected_vault)


def _multi_checks(
    *, pre_state: ZUSDMultiState, cmd: ZUSDMultiCommand, post_state: ZUSDMultiState
) -> List[Tuple[TauSpecRef, Dict[str, int]]]:
    checks: List[Tuple[TauSpecRef, Dict[str, int]]] = []

    if cmd.tag == "oracle_commit":
        checks.append(
            (
                ZUSD_ORACLE_COMMIT_GUARD_V3,
                build_zusd_oracle_commit_guard_v3_step(
                    oracle_seen=1 if pre_state.oracle_seen else 0,
                    pending_price_positive=(
                        1 if pre_state.price_pending_e8 > 0 else 0
                    ),
                    pending_observation_fresh=1
                    if _is_oracle_fresh(
                        now_epoch=pre_state.now_epoch,
                        last_update_epoch=pre_state.oracle_pending_update_epoch,
                        max_staleness_epochs=pre_state.max_oracle_staleness_epochs,
                        oracle_seen=pre_state.oracle_seen,
                    )
                    else 0,
                    auth_ok=1 if _cmd_auth_ok(cmd.args) else 0,
                    commit_candidate_ok=1
                    if _multi_oracle_commit_candidate_ok(
                        pre_state,
                        post_state,
                    )
                    else 0,
                ),
            )
        )

    elif cmd.tag == "mint_zusd":
        amount = _require_pos_int_arg(cmd.args, "amount_e8")
        pre_coll, pre_debt = _multi_vault_for_cmd(pre_state, cmd)
        _post_coll, post_debt = _multi_vault_for_cmd(post_state, cmd)
        checks.append(
            (
                ZUSD_MINT_GUARD_V1,
                build_zusd_mint_guard_v1_step(
                    amount=amount,
                    debt_before=pre_debt,
                    free_before=pre_state.free_debt_e8,
                    debt_after=post_debt,
                    free_after=post_state.free_debt_e8,
                    risky_ops_allowed=1 if _multi_risky_ops_allowed(pre_state) else 0,
                    min_open_ok=1 if not (pre_debt == 0 and amount < pre_state.min_debt_open_e8) else 0,
                    max_vault_ok=1 if post_debt <= pre_state.max_debt_e8 else 0,
                    max_supply_ok=1 if post_state.free_debt_e8 <= pre_state.max_debt_supply_e8 else 0,
                    mcr_post_ok=1
                    if _mcr_ok(
                        collateral_e8=pre_coll,
                        debt_e8=post_debt,
                        price_e8=pre_state.price_e8,
                        mcr_bps=pre_state.mcr_bps,
                    )
                    else 0,
                ),
            )
        )

    elif cmd.tag == "repay_zusd":
        amount = _require_pos_int_arg(cmd.args, "amount_e8")
        _pre_coll, pre_debt = _multi_vault_for_cmd(pre_state, cmd)
        _post_coll, post_debt = _multi_vault_for_cmd(post_state, cmd)
        checks.append(
            (
                ZUSD_REPAY_GUARD_V1,
                build_zusd_repay_guard_v1_step(
                    amount=amount,
                    debt_before=pre_debt,
                    free_before=pre_state.free_debt_e8,
                    debt_after=post_debt,
                    free_after=post_state.free_debt_e8,
                ),
            )
        )

    elif cmd.tag == "redeem_zusd":
        amount = _require_pos_int_arg(cmd.args, "amount_e8")
        raw = cmd.args.get("vault")
        if raw in ("a", "b"):
            vault_for_redeem = str(raw)
        elif raw is None:
            expected_vault = _expected_multi_redeem_vault(pre_state, amount_e8=amount)
            actual_vault = _infer_multi_redeem_vault(pre_state, post_state)
            if actual_vault != expected_vault:
                raise ValueError(
                    f"auto redeem selected wrong vault: expected {expected_vault!r}, got {actual_vault!r}"
                )
            vault_for_redeem = expected_vault
        else:
            raise ValueError("vault must be 'a' or 'b'")

        if vault_for_redeem == "a":
            pre_coll, pre_debt = pre_state.vault_a.collateral_e8, pre_state.vault_a.debt_e8
            post_coll, post_debt = post_state.vault_a.collateral_e8, post_state.vault_a.debt_e8
        else:
            pre_coll, pre_debt = pre_state.vault_b.collateral_e8, pre_state.vault_b.debt_e8
            post_coll, post_debt = post_state.vault_b.collateral_e8, post_state.vault_b.debt_e8

        checks.append(
            (
                ZUSD_REDEEM_GUARD_V1,
                build_zusd_redeem_guard_v1_step(
                    amount=amount,
                    debt_before=pre_debt,
                    free_before=pre_state.free_debt_e8,
                    collateral_before=pre_coll,
                    debt_after=post_debt,
                    free_after=post_state.free_debt_e8,
                    collateral_after=post_coll,
                    gross_collateral=pre_coll - post_coll,
                    fee_collateral=post_state.protocol_collateral_e8 - pre_state.protocol_collateral_e8,
                    oracle_ok=1
                    if (
                        pre_state.oracle_seen
                        and pre_state.price_e8 > 0
                        and pre_state.price_pending_e8 > 0
                        and pre_state.price_pending_e8 == pre_state.price_e8
                        and _is_oracle_fresh(
                            now_epoch=pre_state.now_epoch,
                            last_update_epoch=pre_state.oracle_last_update_epoch,
                            max_staleness_epochs=pre_state.max_oracle_staleness_epochs,
                            oracle_seen=pre_state.oracle_seen,
                        )
                    )
                    else 0,
                    mcr_post_ok=1
                    if _mcr_ok(
                        collateral_e8=post_coll,
                        debt_e8=post_debt,
                        price_e8=pre_state.price_e8,
                        mcr_bps=pre_state.mcr_bps,
                    )
                    else 0,
                    fee_cap_ok=1 if post_state.protocol_collateral_e8 <= pre_state.max_protocol_coll_e8 else 0,
                ),
            )
        )

    elif cmd.tag == "withdraw_collateral":
        amount = _require_pos_int_arg(cmd.args, "amount_e8")
        pre_coll, pre_debt = _multi_vault_for_cmd(pre_state, cmd)
        post_coll, _post_debt = _multi_vault_for_cmd(post_state, cmd)
        checks.append(
            (
                ZUSD_WITHDRAW_COLLATERAL_GUARD_V1,
                build_zusd_withdraw_collateral_guard_v1_step(
                    amount=amount,
                    collateral_before=pre_coll,
                    collateral_after=post_coll,
                    debt_before=pre_debt,
                    risky_ops_allowed=1 if _multi_risky_ops_allowed(pre_state) else 0,
                    mcr_post_ok=1
                    if _mcr_ok(
                        collateral_e8=post_coll,
                        debt_e8=pre_debt,
                        price_e8=pre_state.price_e8,
                        mcr_bps=pre_state.mcr_bps,
                    )
                    else 0,
                ),
            )
        )

    elif cmd.tag == "deposit_sp":
        amount = _require_pos_int_arg(cmd.args, "amount_e8")
        checks.append(
            (
                ZUSD_DEPOSIT_SP_GUARD_V1,
                build_zusd_deposit_sp_guard_v1_step(
                    amount=amount,
                    free_before=pre_state.free_debt_e8,
                    sp_before=pre_state.sp_debt_e8,
                    free_after=post_state.free_debt_e8,
                    sp_after=post_state.sp_debt_e8,
                    max_supply_ok=1 if post_state.sp_debt_e8 <= pre_state.max_debt_supply_e8 else 0,
                ),
            )
        )

    elif cmd.tag == "withdraw_sp":
        amount = _require_pos_int_arg(cmd.args, "amount_e8")
        checks.append(
            (
                ZUSD_WITHDRAW_SP_GUARD_V1,
                build_zusd_withdraw_sp_guard_v1_step(
                    amount=amount,
                    free_before=pre_state.free_debt_e8,
                    sp_before=pre_state.sp_debt_e8,
                    free_after=post_state.free_debt_e8,
                    sp_after=post_state.sp_debt_e8,
                    risky_ops_allowed=1 if _multi_risky_ops_allowed(pre_state) else 0,
                    vault_mcr_ok=1
                    if (
                        _mcr_ok(
                            collateral_e8=pre_state.vault_a.collateral_e8,
                            debt_e8=pre_state.vault_a.debt_e8,
                            price_e8=pre_state.price_e8,
                            mcr_bps=pre_state.mcr_bps,
                        )
                        and _mcr_ok(
                            collateral_e8=pre_state.vault_b.collateral_e8,
                            debt_e8=pre_state.vault_b.debt_e8,
                            price_e8=pre_state.price_e8,
                            mcr_bps=pre_state.mcr_bps,
                        )
                    )
                    else 0,
                ),
            )
        )

    elif cmd.tag == "liquidate":
        pre_coll, pre_debt = _multi_vault_for_cmd(pre_state, cmd)
        (
            collateral_destinations_exact,
            stability_pool_collateral_cap_ok,
            state_delta_ok,
        ) = _multi_liquidation_projection_flags(pre_state, post_state, cmd)
        checks.append(
            (
                ZUSD_LIQUIDATION_GUARD_V3,
                build_zusd_liquidation_guard_v3_step(
                    committed_oracle_initialized=(
                        1
                        if pre_state.oracle_seen and pre_state.price_e8 > 0
                        else 0
                    ),
                    no_uncommitted_report=(
                        1
                        if (
                            pre_state.price_pending_e8 == pre_state.price_e8
                            and pre_state.oracle_pending_update_epoch
                            == pre_state.oracle_last_update_epoch
                        )
                        else 0
                    ),
                    committed_oracle_fresh=1
                    if _is_oracle_fresh(
                        now_epoch=pre_state.now_epoch,
                        last_update_epoch=pre_state.oracle_last_update_epoch,
                        max_staleness_epochs=pre_state.max_oracle_staleness_epochs,
                        oracle_seen=pre_state.oracle_seen,
                    )
                    else 0,
                    positive_debt=1 if pre_debt > 0 else 0,
                    under_mcr_at_committed_price=1
                    if not _mcr_ok(
                        collateral_e8=pre_coll,
                        debt_e8=pre_debt,
                        price_e8=pre_state.price_e8,
                        mcr_bps=pre_state.mcr_bps,
                    )
                    else 0,
                    stability_pool_can_absorb=(
                        1 if pre_state.sp_debt_e8 >= pre_debt else 0
                    ),
                    collateral_destinations_exact=(
                        1 if collateral_destinations_exact else 0
                    ),
                    stability_pool_collateral_cap_ok=(
                        1 if stability_pool_collateral_cap_ok else 0
                    ),
                    state_delta_ok=1 if state_delta_ok else 0,
                ),
            )
        )

    checks.append(
        (
            ZUSD_SUPPLY_CONSERVATION_V3,
            build_zusd_supply_conservation_v3_step(
                pre_conservation_ok=1
                if (
                    pre_state.free_debt_e8 + pre_state.sp_debt_e8
                    == _multi_total_debt(pre_state)
                )
                else 0,
                post_conservation_ok=1
                if (
                    post_state.free_debt_e8 + post_state.sp_debt_e8
                    == _multi_total_debt(post_state)
                )
                else 0,
                transition_delta_ok=1
                if (
                    _multi_total_debt(post_state)
                    - _multi_total_debt(pre_state)
                    == (
                        post_state.free_debt_e8 - pre_state.free_debt_e8
                        + post_state.sp_debt_e8
                        - pre_state.sp_debt_e8
                    )
                )
                else 0,
            ),
        )
    )
    return checks


def validate_zusd_transition(
    *,
    pre_state: ZUSDState,
    cmd: ZUSDCommand,
    post_state: ZUSDState,
    config: ZUSDTauGateConfig = DEFAULT_ZUSD_TAU_GATE_CONFIG,
) -> tuple[bool, Optional[str]]:
    """Validate one successful single-vault zUSD transition with Tau."""
    if not config.enabled:
        return True, None
    try:
        checks = _single_checks(pre_state=pre_state, cmd=cmd, post_state=post_state)
        ok, tau_bin, err = _resolve_tau_bin(config)
        if not ok:
            return False, err
        if tau_bin is None:
            return False, "tau binary resolution failed"
        for spec_ref, step in checks:
            outputs = run_tau_spec_steps(
                tau_bin=tau_bin,
                spec_path=spec_ref.path,
                steps=[step],
                timeout_s=config.timeout_s,
            )
            gate_ok, gate_err = _require_gate_ok(outputs, spec_ref=spec_ref)
            if not gate_ok:
                return False, gate_err
        return True, None
    except Exception as exc:
        return False, f"{type(exc).__name__}: {exc}"


def validate_zusd_multi_transition(
    *,
    pre_state: ZUSDMultiState,
    cmd: ZUSDMultiCommand,
    post_state: ZUSDMultiState,
    config: ZUSDTauGateConfig = DEFAULT_ZUSD_TAU_GATE_CONFIG,
) -> tuple[bool, Optional[str]]:
    """Validate one successful multi-vault zUSD transition with Tau."""
    if not config.enabled:
        return True, None
    try:
        checks = _multi_checks(pre_state=pre_state, cmd=cmd, post_state=post_state)
        ok, tau_bin, err = _resolve_tau_bin(config)
        if not ok:
            return False, err
        if tau_bin is None:
            return False, "tau binary resolution failed"
        for spec_ref, step in checks:
            outputs = run_tau_spec_steps(
                tau_bin=tau_bin,
                spec_path=spec_ref.path,
                steps=[step],
                timeout_s=config.timeout_s,
            )
            gate_ok, gate_err = _require_gate_ok(outputs, spec_ref=spec_ref)
            if not gate_ok:
                return False, gate_err
        return True, None
    except Exception as exc:
        return False, f"{type(exc).__name__}: {exc}"


def step_with_tau(
    state: ZUSDState,
    cmd: ZUSDCommand,
    *,
    config: ZUSDTauGateConfig = DEFAULT_ZUSD_TAU_GATE_CONFIG,
) -> ZUSDStepResult:
    """
    Execute one single-vault zUSD step and then enforce Tau transition checks.

    The core step runs first; Tau can only further reject accepted transitions.
    """
    res = zusd_step(state, cmd)
    if not res.ok or res.state is None or not config.enabled:
        return res
    ok, err = validate_zusd_transition(pre_state=state, cmd=cmd, post_state=res.state, config=config)
    if ok:
        return res
    return ZUSDStepResult(ok=False, error=f"tau_gate_rejected: {err}")


def step_multi_with_tau(
    state: ZUSDMultiState,
    cmd: ZUSDMultiCommand,
    *,
    config: ZUSDTauGateConfig = DEFAULT_ZUSD_TAU_GATE_CONFIG,
) -> ZUSDMultiStepResult:
    """
    Execute one multi-vault zUSD step and then enforce Tau transition checks.

    The core step runs first; Tau can only further reject accepted transitions.
    """
    res = zusd_step_multi(state, cmd)
    if not res.ok or res.state is None or not config.enabled:
        return res
    ok, err = validate_zusd_multi_transition(pre_state=state, cmd=cmd, post_state=res.state, config=config)
    if ok:
        return res
    return ZUSDMultiStepResult(ok=False, error=f"tau_gate_rejected: {err}")
