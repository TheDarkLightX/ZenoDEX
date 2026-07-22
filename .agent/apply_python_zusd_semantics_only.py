#!/usr/bin/env python3
"""Publish the audited single-vault Python zUSD authority semantics explicitly."""

from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PY_ZUSD = ROOT / "src/core/zusd.py"
HARNESS = ROOT / "tools/runtime/zusd_kernel_lib.py"


def replace_once(text: str, old: str, new: str, *, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise SystemExit(f"{label}: expected one exact preimage, found {count}")
    return text.replace(old, new, 1)


def update_error_maps(text: str) -> str:
    text = replace_once(
        text,
        '    "oracle_commit blocked: vault below MCR at pending price": "commit_below_mcr",\n',
        '    "oracle_commit blocked by stale oracle context": "commit_stale_oracle_context",\n',
        label="Oracle commit reject mapping",
    )
    text = replace_once(
        text,
        '    "liquidation requires initialized pending oracle price": "liquidate_oracle_uninitialized",\n'
        '    "no debt to liquidate": "liquidate_no_debt",\n'
        '    "vault not under MCR at pending price": "liquidate_not_under_mcr",\n',
        '    "liquidation requires initialized finalized oracle price": "liquidate_oracle_uninitialized",\n'
        '    "liquidation blocked by oracle pending mismatch": "liquidate_pending_mismatch",\n'
        '    "liquidation blocked by stale finalized oracle": "liquidate_stale_oracle",\n'
        '    "no debt to liquidate": "liquidate_no_debt",\n'
        '    "vault not under MCR at finalized price": "liquidate_not_under_mcr",\n',
        label="liquidation reject mappings",
    )
    return text


def update_python() -> None:
    text = PY_ZUSD.read_text(encoding="utf-8")
    text = update_error_maps(text)

    old_invariants = '''def check_invariants(state: ZUSDState) -> list[str]:
    failed: list[str] = []
    if state.oracle_seen and (state.price_e8 <= 0 or state.price_pending_e8 <= 0):
        failed.append("inv_oracle_seen_positive_prices")
    if state.oracle_seen and state.price_pending_e8 > state.price_e8:
        failed.append("inv_pending_le_active")
    if not state.oracle_seen and (
        state.price_e8 != 0 or state.price_pending_e8 != 0 or state.oracle_last_update_epoch != 0
    ):
        failed.append("inv_oracle_unseen_zeroed")
    if (state.free_debt_e8 + state.sp_debt_e8) != state.debt_e8:
        failed.append("inv_supply_conservation")
    if not _debt_floor_ok(debt_e8=state.debt_e8, min_debt_open_e8=state.min_debt_open_e8):
        failed.append("inv_debt_floor")
    if not _solvent_at_price(
        collateral_e8=state.collateral_e8 + state.sp_coll_e8 + state.protocol_collateral_e8,
        debt_e8=state.debt_e8,
        price_e8=state.price_e8 if state.price_e8 > 0 else E8,
    ):
        failed.append("inv_system_no_bad_debt")
    return failed
'''
    new_invariants = '''def check_invariants(state: ZUSDState) -> list[str]:
    """Return hard accounting and representation invariant failures."""

    failed: list[str] = []
    if state.oracle_seen and (state.price_e8 <= 0 or state.price_pending_e8 <= 0):
        failed.append("inv_oracle_seen_positive_prices")
    if state.oracle_seen and state.price_pending_e8 > state.price_e8:
        failed.append("inv_pending_le_active")
    if not state.oracle_seen and (
        state.price_e8 != 0
        or state.price_pending_e8 != 0
        or state.oracle_last_update_epoch != 0
    ):
        failed.append("inv_oracle_unseen_zeroed")
    if (state.free_debt_e8 + state.sp_debt_e8) != state.debt_e8:
        failed.append("inv_supply_conservation")
    if state.debt_e8 > state.max_debt_supply_e8:
        failed.append("inv_total_debt_cap")
    if not _debt_floor_ok(
        debt_e8=state.debt_e8,
        min_debt_open_e8=state.min_debt_open_e8,
    ):
        failed.append("inv_debt_floor")
    return failed


def check_health_conditions(state: ZUSDState) -> list[str]:
    """Return finalized-price health facts without rejecting representable state."""

    failed: list[str] = []
    if not state.oracle_seen or state.price_e8 <= 0:
        return failed
    if state.debt_e8 > 0 and not _mcr_ok(
        collateral_e8=state.collateral_e8,
        debt_e8=state.debt_e8,
        price_e8=state.price_e8,
        mcr_bps=state.mcr_bps,
    ):
        failed.append("health_vault_below_mcr")
    if not _solvent_at_price(
        collateral_e8=(
            state.collateral_e8
            + state.sp_coll_e8
            + state.protocol_collateral_e8
        ),
        debt_e8=state.debt_e8,
        price_e8=state.price_e8,
    ):
        failed.append("health_system_bad_debt")
    return failed
'''
    text = replace_once(
        text,
        old_invariants,
        new_invariants,
        label="hard invariants and health split",
    )

    old_commit = '''def _zusd_h_oracle_commit(state: ZUSDState, cmd: ZUSDCommand):
    if not state.oracle_seen:
        return ZUSDStepResult(ok=False, error="oracle not bootstrapped")
    if not bool(cmd.args.get("auth_ok", False)):
        return ZUSDStepResult(ok=False, error="oracle_commit requires auth_ok=true")
    # Commit only when vault remains above MCR at pending price.
    if not _mcr_ok(
        collateral_e8=state.collateral_e8,
        debt_e8=state.debt_e8,
        price_e8=state.price_pending_e8,
        mcr_bps=state.mcr_bps,
    ):
        return ZUSDStepResult(
            ok=False, error="oracle_commit blocked: vault below MCR at pending price"
        )
    ns = ZUSDState(
        **{
            **state.__dict__,
            "price_e8": state.price_pending_e8,
            "oracle_last_update_epoch": state.now_epoch,
        }
    )
    return ns, {"event": "oracle_committed", "price_e8": state.price_pending_e8}
'''
    new_commit = '''def _zusd_h_oracle_commit(state: ZUSDState, cmd: ZUSDCommand):
    if not state.oracle_seen:
        return ZUSDStepResult(ok=False, error="oracle not bootstrapped")
    if not bool(cmd.args.get("auth_ok", False)):
        return ZUSDStepResult(ok=False, error="oracle_commit requires auth_ok=true")
    if not _is_oracle_fresh(
        now_epoch=state.now_epoch,
        last_update_epoch=state.oracle_last_update_epoch,
        max_staleness_epochs=state.max_oracle_staleness_epochs,
        oracle_seen=state.oracle_seen,
    ):
        return ZUSDStepResult(
            ok=False,
            error="oracle_commit blocked by stale oracle context",
        )
    ns = ZUSDState(
        **{
            **state.__dict__,
            "price_e8": state.price_pending_e8,
            "oracle_last_update_epoch": state.now_epoch,
        }
    )
    return ns, {"event": "oracle_committed", "price_e8": state.price_pending_e8}
'''
    text = replace_once(text, old_commit, new_commit, label="finalized Oracle commit")

    text = replace_once(
        text,
        "    if (state.free_debt_e8 + debt_delta) > state.max_debt_supply_e8:\n",
        "    if new_debt > state.max_debt_supply_e8:\n",
        label="single-vault total debt cap",
    )

    old_liquidate = '''def _zusd_h_liquidate(state: ZUSDState, cmd: ZUSDCommand):
    if not state.oracle_seen or state.price_pending_e8 <= 0:
        return ZUSDStepResult(
            ok=False, error="liquidation requires initialized pending oracle price"
        )
    if state.debt_e8 <= 0:
        return ZUSDStepResult(ok=False, error="no debt to liquidate")
    under_mcr = not _mcr_ok(
        collateral_e8=state.collateral_e8,
        debt_e8=state.debt_e8,
        price_e8=state.price_pending_e8,
        mcr_bps=state.mcr_bps,
    )
    if not under_mcr:
        return ZUSDStepResult(ok=False, error="vault not under MCR at pending price")
    if state.debt_e8 > state.sp_debt_e8:
        return ZUSDStepResult(ok=False, error="stability pool cannot absorb debt")
    liquidated_debt = state.debt_e8
    liquidated_coll = state.collateral_e8
    variable_comp = _mul_div_up(liquidated_coll, state.liquidation_gas_comp_bps, BPS_SCALE)
    requested_comp = state.liquidation_gas_comp_fixed_collateral_e8 + variable_comp
    liquidator_comp = min(liquidated_coll, requested_comp)
    sp_collateral_gain = liquidated_coll - liquidator_comp
    if (state.sp_coll_e8 + sp_collateral_gain) > state.max_sp_coll_e8:
        return ZUSDStepResult(ok=False, error="stability pool collateral cap exceeded")
    ns = ZUSDState(
        **{
            **state.__dict__,
            "debt_e8": 0,
            "collateral_e8": 0,
            "sp_debt_e8": state.sp_debt_e8 - liquidated_debt,
            "sp_coll_e8": state.sp_coll_e8 + sp_collateral_gain,
            "liquidator_compensation_collateral_cum_e8": (
                state.liquidator_compensation_collateral_cum_e8 + liquidator_comp
            ),
        }
    )
    return ns, {
        "event": "liquidated",
        "liquidated_debt_e8": liquidated_debt,
        "liquidated_collateral_e8": liquidated_coll,
        "sp_collateral_gain_e8": sp_collateral_gain,
        "liquidator_compensation_collateral_e8": liquidator_comp,
        "liquidation_gas_comp_fixed_collateral_e8": state.liquidation_gas_comp_fixed_collateral_e8,
        "liquidation_gas_comp_bps": state.liquidation_gas_comp_bps,
    }
'''
    new_liquidate = '''def _zusd_h_liquidate(state: ZUSDState, cmd: ZUSDCommand):
    if not state.oracle_seen or state.price_e8 <= 0:
        return ZUSDStepResult(
            ok=False,
            error="liquidation requires initialized finalized oracle price",
        )
    if state.price_pending_e8 != state.price_e8:
        return ZUSDStepResult(
            ok=False,
            error="liquidation blocked by oracle pending mismatch",
        )
    if not _is_oracle_fresh(
        now_epoch=state.now_epoch,
        last_update_epoch=state.oracle_last_update_epoch,
        max_staleness_epochs=state.max_oracle_staleness_epochs,
        oracle_seen=state.oracle_seen,
    ):
        return ZUSDStepResult(
            ok=False,
            error="liquidation blocked by stale finalized oracle",
        )
    if state.debt_e8 <= 0:
        return ZUSDStepResult(ok=False, error="no debt to liquidate")
    if _mcr_ok(
        collateral_e8=state.collateral_e8,
        debt_e8=state.debt_e8,
        price_e8=state.price_e8,
        mcr_bps=state.mcr_bps,
    ):
        return ZUSDStepResult(ok=False, error="vault not under MCR at finalized price")
    if state.debt_e8 > state.sp_debt_e8:
        return ZUSDStepResult(ok=False, error="stability pool cannot absorb debt")
    liquidated_debt = state.debt_e8
    liquidated_coll = state.collateral_e8
    variable_comp = _mul_div_up(
        liquidated_coll,
        state.liquidation_gas_comp_bps,
        BPS_SCALE,
    )
    requested_comp = state.liquidation_gas_comp_fixed_collateral_e8 + variable_comp
    liquidator_comp = min(liquidated_coll, requested_comp)
    sp_collateral_gain = liquidated_coll - liquidator_comp
    if (state.sp_coll_e8 + sp_collateral_gain) > state.max_sp_coll_e8:
        return ZUSDStepResult(ok=False, error="stability pool collateral cap exceeded")
    ns = ZUSDState(
        **{
            **state.__dict__,
            "debt_e8": 0,
            "collateral_e8": 0,
            "sp_debt_e8": state.sp_debt_e8 - liquidated_debt,
            "sp_coll_e8": state.sp_coll_e8 + sp_collateral_gain,
            "liquidator_compensation_collateral_cum_e8": (
                state.liquidator_compensation_collateral_cum_e8 + liquidator_comp
            ),
        }
    )
    return ns, {
        "event": "liquidated",
        "liquidated_debt_e8": liquidated_debt,
        "liquidated_collateral_e8": liquidated_coll,
        "sp_collateral_gain_e8": sp_collateral_gain,
        "liquidator_compensation_collateral_e8": liquidator_comp,
        "liquidation_gas_comp_fixed_collateral_e8": state.liquidation_gas_comp_fixed_collateral_e8,
        "liquidation_gas_comp_bps": state.liquidation_gas_comp_bps,
    }
'''
    text = replace_once(
        text,
        old_liquidate,
        new_liquidate,
        label="finalized-price liquidation authority",
    )

    PY_ZUSD.write_text(text, encoding="utf-8")


def update_harness() -> None:
    text = update_error_maps(HARNESS.read_text(encoding="utf-8"))
    HARNESS.write_text(text, encoding="utf-8")


def main() -> None:
    update_python()
    update_harness()
    print("applied tracked Python zUSD audit semantics")


if __name__ == "__main__":
    main()
