"""
Auto-generated Python reference model for: perp_epoch_clearinghouse_2p_v0_1
IR hash: sha256:11530562918cd1aaa048d9e999143f9cf2bb51aa70dc0dfcfece689a89c0ead4

Generated from the YAML kernel spec by the repo's optional spec toolchain (ESSO: Evolutionary State Space Optimizer).

This file is standalone and has no runtime dependency on the generator/toolchain.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Literal, Mapping


@dataclass(frozen=True)
class State:
    """Model state."""

    breaker_active: bool
    breaker_last_trigger_epoch: int
    clearing_price_e8: int
    clearing_price_epoch: int
    clearing_price_seen: bool
    collateral_e8_a: int
    collateral_e8_b: int
    entry_price_e8_a: int
    entry_price_e8_b: int
    fee_pool_e8: int
    index_price_e8: int
    initial_margin_bps: int
    liquidated_this_step: bool
    liquidation_penalty_bps: int
    maintenance_margin_bps: int
    max_oracle_move_bps: int
    max_oracle_staleness_epochs: int
    max_position_abs: int
    net_deposited_e8: int
    now_epoch: int
    oracle_last_update_epoch: int
    oracle_seen: bool
    position_base_a: int
    position_base_b: int


@dataclass(frozen=True)
class Command:
    """Command to execute."""

    tag: Literal(
        "advance_epoch",
        "clear_breaker",
        "deposit_collateral_a",
        "deposit_collateral_b",
        "publish_clearing_price",
        "set_position_pair",
        "settle_epoch",
        "withdraw_collateral_a",
        "withdraw_collateral_b",
    )
    args: Mapping[str, Any]


@dataclass(frozen=True)
class StepResult:
    """Result of a step execution."""

    ok: bool
    state: State | None = None
    effects: Mapping[str, Any] | None = None
    error: str | None = None


def init_state() -> State:
    """Return the initial state."""
    return State(
        breaker_active=False,
        breaker_last_trigger_epoch=0,
        clearing_price_e8=0,
        clearing_price_epoch=0,
        clearing_price_seen=False,
        collateral_e8_a=0,
        collateral_e8_b=0,
        entry_price_e8_a=0,
        entry_price_e8_b=0,
        fee_pool_e8=0,
        index_price_e8=0,
        initial_margin_bps=1000,
        liquidated_this_step=False,
        liquidation_penalty_bps=50,
        maintenance_margin_bps=600,
        max_oracle_move_bps=500,
        max_oracle_staleness_epochs=100,
        max_position_abs=1000000,
        net_deposited_e8=0,
        now_epoch=0,
        oracle_last_update_epoch=0,
        oracle_seen=False,
        position_base_a=0,
        position_base_b=0,
    )


def check_invariants(s: State) -> tuple[bool, str | None]:
    """Check all invariants. Returns (ok, first_failed_id)."""
    if not (isinstance(s.breaker_active, bool)):
        return False, "domain_breaker_active"
    if not (
        isinstance(s.breaker_last_trigger_epoch, int)
        and not isinstance(s.breaker_last_trigger_epoch, bool)
        and 0 <= s.breaker_last_trigger_epoch <= 1000000
    ):
        return False, "domain_breaker_last_trigger_epoch"
    if not (
        isinstance(s.clearing_price_e8, int)
        and not isinstance(s.clearing_price_e8, bool)
        and 0 <= s.clearing_price_e8 <= 1000000000000
    ):
        return False, "domain_clearing_price_e8"
    if not (
        isinstance(s.clearing_price_epoch, int)
        and not isinstance(s.clearing_price_epoch, bool)
        and 0 <= s.clearing_price_epoch <= 1000000
    ):
        return False, "domain_clearing_price_epoch"
    if not (isinstance(s.clearing_price_seen, bool)):
        return False, "domain_clearing_price_seen"
    if not (
        isinstance(s.collateral_e8_a, int)
        and not isinstance(s.collateral_e8_a, bool)
        and 0 <= s.collateral_e8_a <= 1000000000000000000
    ):
        return False, "domain_collateral_e8_a"
    if not (
        isinstance(s.collateral_e8_b, int)
        and not isinstance(s.collateral_e8_b, bool)
        and 0 <= s.collateral_e8_b <= 1000000000000000000
    ):
        return False, "domain_collateral_e8_b"
    if not (
        isinstance(s.entry_price_e8_a, int)
        and not isinstance(s.entry_price_e8_a, bool)
        and 0 <= s.entry_price_e8_a <= 1000000000000
    ):
        return False, "domain_entry_price_e8_a"
    if not (
        isinstance(s.entry_price_e8_b, int)
        and not isinstance(s.entry_price_e8_b, bool)
        and 0 <= s.entry_price_e8_b <= 1000000000000
    ):
        return False, "domain_entry_price_e8_b"
    if not (
        isinstance(s.fee_pool_e8, int)
        and not isinstance(s.fee_pool_e8, bool)
        and 0 <= s.fee_pool_e8 <= 3000000000000000000
    ):
        return False, "domain_fee_pool_e8"
    if not (
        isinstance(s.index_price_e8, int)
        and not isinstance(s.index_price_e8, bool)
        and 0 <= s.index_price_e8 <= 1000000000000
    ):
        return False, "domain_index_price_e8"
    if not (
        isinstance(s.initial_margin_bps, int)
        and not isinstance(s.initial_margin_bps, bool)
        and 0 <= s.initial_margin_bps <= 10000
    ):
        return False, "domain_initial_margin_bps"
    if not (isinstance(s.liquidated_this_step, bool)):
        return False, "domain_liquidated_this_step"
    if not (
        isinstance(s.liquidation_penalty_bps, int)
        and not isinstance(s.liquidation_penalty_bps, bool)
        and 0 <= s.liquidation_penalty_bps <= 10000
    ):
        return False, "domain_liquidation_penalty_bps"
    if not (
        isinstance(s.maintenance_margin_bps, int)
        and not isinstance(s.maintenance_margin_bps, bool)
        and 0 <= s.maintenance_margin_bps <= 10000
    ):
        return False, "domain_maintenance_margin_bps"
    if not (
        isinstance(s.max_oracle_move_bps, int)
        and not isinstance(s.max_oracle_move_bps, bool)
        and 0 <= s.max_oracle_move_bps <= 10000
    ):
        return False, "domain_max_oracle_move_bps"
    if not (
        isinstance(s.max_oracle_staleness_epochs, int)
        and not isinstance(s.max_oracle_staleness_epochs, bool)
        and 1 <= s.max_oracle_staleness_epochs <= 1000000
    ):
        return False, "domain_max_oracle_staleness_epochs"
    if not (
        isinstance(s.max_position_abs, int)
        and not isinstance(s.max_position_abs, bool)
        and 1 <= s.max_position_abs <= 1000000
    ):
        return False, "domain_max_position_abs"
    if not (
        isinstance(s.net_deposited_e8, int)
        and not isinstance(s.net_deposited_e8, bool)
        and 0 <= s.net_deposited_e8 <= 3000000000000000000
    ):
        return False, "domain_net_deposited_e8"
    if not (
        isinstance(s.now_epoch, int)
        and not isinstance(s.now_epoch, bool)
        and 0 <= s.now_epoch <= 1000000
    ):
        return False, "domain_now_epoch"
    if not (
        isinstance(s.oracle_last_update_epoch, int)
        and not isinstance(s.oracle_last_update_epoch, bool)
        and 0 <= s.oracle_last_update_epoch <= 1000000
    ):
        return False, "domain_oracle_last_update_epoch"
    if not (isinstance(s.oracle_seen, bool)):
        return False, "domain_oracle_seen"
    if not (
        isinstance(s.position_base_a, int)
        and not isinstance(s.position_base_a, bool)
        and -1000000 <= s.position_base_a <= 1000000
    ):
        return False, "domain_position_base_a"
    if not (
        isinstance(s.position_base_b, int)
        and not isinstance(s.position_base_b, bool)
        and -1000000 <= s.position_base_b <= 1000000
    ):
        return False, "domain_position_base_b"
    if not ((not (not s.breaker_active)) or (0 == s.breaker_last_trigger_epoch)):
        return False, "inv_breaker_inactive_zeroed"
    if not (s.breaker_last_trigger_epoch <= s.now_epoch):
        return False, "inv_breaker_not_from_future"
    if not (s.clearing_price_epoch <= s.now_epoch):
        return False, "inv_clearing_not_from_future"
    if not (
        (not (not s.clearing_price_seen))
        or ((0 == s.clearing_price_e8) and (0 == s.clearing_price_epoch))
    ):
        return False, "inv_clearing_seen_zeroed"
    if not (
        (not (not (0 == s.position_base_a))) or (s.entry_price_e8_a == s.index_price_e8)
    ):
        return False, "inv_entry_matches_price_when_open_a"
    if not (
        (not (not (0 == s.position_base_b))) or (s.entry_price_e8_b == s.index_price_e8)
    ):
        return False, "inv_entry_matches_price_when_open_b"
    if not ((not (0 == s.position_base_a)) or (0 == s.entry_price_e8_a)):
        return False, "inv_entry_zero_when_flat_a"
    if not ((not (0 == s.position_base_b)) or (0 == s.entry_price_e8_b)):
        return False, "inv_entry_zero_when_flat_b"
    if not (
        (not (not (0 == s.position_base_a)))
        or (
            s.collateral_e8_a
            >= (
                0
                if 10000 == 0
                else (
                    (
                        (
                            9999
                            + (
                                (
                                    (
                                        s.position_base_a
                                        if (s.position_base_a >= 0)
                                        else (0 - s.position_base_a)
                                    )
                                    * s.index_price_e8
                                )
                                * s.maintenance_margin_bps
                            )
                        )
                        // 10000
                    )
                    + (
                        1
                        if (
                            (
                                9999
                                + (
                                    (
                                        (
                                            s.position_base_a
                                            if (s.position_base_a >= 0)
                                            else (0 - s.position_base_a)
                                        )
                                        * s.index_price_e8
                                    )
                                    * s.maintenance_margin_bps
                                )
                            )
                            % 10000
                        )
                        < 0
                        else 0
                    )
                )
            )
        )
    ):
        return False, "inv_maint_margin_ok_a"
    if not (
        (not (not (0 == s.position_base_b)))
        or (
            s.collateral_e8_b
            >= (
                0
                if 10000 == 0
                else (
                    (
                        (
                            9999
                            + (
                                (
                                    (
                                        s.position_base_b
                                        if (s.position_base_b >= 0)
                                        else (0 - s.position_base_b)
                                    )
                                    * s.index_price_e8
                                )
                                * s.maintenance_margin_bps
                            )
                        )
                        // 10000
                    )
                    + (
                        1
                        if (
                            (
                                9999
                                + (
                                    (
                                        (
                                            s.position_base_b
                                            if (s.position_base_b >= 0)
                                            else (0 - s.position_base_b)
                                        )
                                        * s.index_price_e8
                                    )
                                    * s.maintenance_margin_bps
                                )
                            )
                            % 10000
                        )
                        < 0
                        else 0
                    )
                )
            )
        )
    ):
        return False, "inv_maint_margin_ok_b"
    if not (
        (s.maintenance_margin_bps <= s.initial_margin_bps)
        and (s.max_oracle_move_bps <= s.maintenance_margin_bps)
    ):
        return False, "inv_margin_params_ordered"
    if not (0 == (s.position_base_a + s.position_base_b)):
        return False, "inv_net_position_zero"
    if not (s.oracle_last_update_epoch <= s.now_epoch):
        return False, "inv_oracle_not_from_future"
    if not (
        (not (not s.oracle_seen))
        or ((0 == s.index_price_e8) and (0 == s.oracle_last_update_epoch))
    ):
        return False, "inv_oracle_seen_zeroed"
    if not (
        ((s.collateral_e8_a + s.collateral_e8_b) + s.fee_pool_e8) == s.net_deposited_e8
    ):
        return False, "inv_total_conservation_e8"
    return True, None


def step(s: State, cmd: Command) -> StepResult:
    """Execute a step. Returns StepResult."""
    # Check pre-state invariants
    ok, failed = check_invariants(s)
    if not ok:
        return StepResult(ok=False, error=f"pre-invariant violated: {failed}")

    if cmd.tag == "advance_epoch":
        if "delta" not in cmd.args or not (
            isinstance(cmd.args["delta"], int)
            and not isinstance(cmd.args["delta"], bool)
            and 1 <= cmd.args["delta"] <= 10000
        ):
            return StepResult(ok=False, error="invalid param delta")
        if not ((cmd.args["delta"] + s.now_epoch) <= 1000000):
            return StepResult(ok=False, error="guard failed for advance_epoch")
        # Compute updates (simultaneous)
        new_state = State(
            breaker_active=s.breaker_active,
            breaker_last_trigger_epoch=s.breaker_last_trigger_epoch,
            clearing_price_e8=s.clearing_price_e8,
            clearing_price_epoch=s.clearing_price_epoch,
            clearing_price_seen=s.clearing_price_seen,
            collateral_e8_a=s.collateral_e8_a,
            collateral_e8_b=s.collateral_e8_b,
            entry_price_e8_a=s.entry_price_e8_a,
            entry_price_e8_b=s.entry_price_e8_b,
            fee_pool_e8=s.fee_pool_e8,
            index_price_e8=s.index_price_e8,
            initial_margin_bps=s.initial_margin_bps,
            liquidated_this_step=False,
            liquidation_penalty_bps=s.liquidation_penalty_bps,
            maintenance_margin_bps=s.maintenance_margin_bps,
            max_oracle_move_bps=s.max_oracle_move_bps,
            max_oracle_staleness_epochs=s.max_oracle_staleness_epochs,
            max_position_abs=s.max_position_abs,
            net_deposited_e8=s.net_deposited_e8,
            now_epoch=(cmd.args["delta"] + s.now_epoch),
            oracle_last_update_epoch=s.oracle_last_update_epoch,
            oracle_seen=s.oracle_seen,
            position_base_a=s.position_base_a,
            position_base_b=s.position_base_b,
        )
        effects = {
            "collateral_after_a": new_state.collateral_e8_a,
            "collateral_after_b": new_state.collateral_e8_b,
            "event": "EpochAdvanced",
            "fee_pool_after": new_state.fee_pool_e8,
            "liquidated": new_state.liquidated_this_step,
            "oracle_fresh": (
                (
                    (new_state.now_epoch - new_state.oracle_last_update_epoch)
                    <= new_state.max_oracle_staleness_epochs
                )
                and new_state.oracle_seen
            ),
        }
        ok, failed = check_invariants(new_state)
        if not ok:
            return StepResult(ok=False, error=f"post-invariant violated: {failed}")
        return StepResult(ok=True, state=new_state, effects=effects)
    elif cmd.tag == "clear_breaker":
        if "auth_ok" not in cmd.args or not (isinstance(cmd.args["auth_ok"], bool)):
            return StepResult(ok=False, error="invalid param auth_ok")
        if not (
            (True == cmd.args["auth_ok"])
            and (0 == s.position_base_a)
            and (0 == s.position_base_b)
            and s.breaker_active
        ):
            return StepResult(ok=False, error="guard failed for clear_breaker")
        # Compute updates (simultaneous)
        new_state = State(
            breaker_active=False,
            breaker_last_trigger_epoch=0,
            clearing_price_e8=s.clearing_price_e8,
            clearing_price_epoch=s.clearing_price_epoch,
            clearing_price_seen=s.clearing_price_seen,
            collateral_e8_a=s.collateral_e8_a,
            collateral_e8_b=s.collateral_e8_b,
            entry_price_e8_a=s.entry_price_e8_a,
            entry_price_e8_b=s.entry_price_e8_b,
            fee_pool_e8=s.fee_pool_e8,
            index_price_e8=s.index_price_e8,
            initial_margin_bps=s.initial_margin_bps,
            liquidated_this_step=False,
            liquidation_penalty_bps=s.liquidation_penalty_bps,
            maintenance_margin_bps=s.maintenance_margin_bps,
            max_oracle_move_bps=s.max_oracle_move_bps,
            max_oracle_staleness_epochs=s.max_oracle_staleness_epochs,
            max_position_abs=s.max_position_abs,
            net_deposited_e8=s.net_deposited_e8,
            now_epoch=s.now_epoch,
            oracle_last_update_epoch=s.oracle_last_update_epoch,
            oracle_seen=s.oracle_seen,
            position_base_a=s.position_base_a,
            position_base_b=s.position_base_b,
        )
        effects = {
            "collateral_after_a": new_state.collateral_e8_a,
            "collateral_after_b": new_state.collateral_e8_b,
            "event": "BreakerCleared",
            "fee_pool_after": new_state.fee_pool_e8,
            "liquidated": new_state.liquidated_this_step,
            "oracle_fresh": new_state.oracle_seen,
        }
        ok, failed = check_invariants(new_state)
        if not ok:
            return StepResult(ok=False, error=f"post-invariant violated: {failed}")
        return StepResult(ok=True, state=new_state, effects=effects)
    elif cmd.tag == "deposit_collateral_a":
        if "amount_e8" not in cmd.args or not (
            isinstance(cmd.args["amount_e8"], int)
            and not isinstance(cmd.args["amount_e8"], bool)
            and 1 <= cmd.args["amount_e8"] <= 1000000000000000000
        ):
            return StepResult(ok=False, error="invalid param amount_e8")
        if "auth_ok" not in cmd.args or not (isinstance(cmd.args["auth_ok"], bool)):
            return StepResult(ok=False, error="invalid param auth_ok")
        if not (
            ((cmd.args["amount_e8"] + s.collateral_e8_a) <= 1000000000000000000)
            and ((cmd.args["amount_e8"] + s.net_deposited_e8) <= 3000000000000000000)
            and (True == cmd.args["auth_ok"])
        ):
            return StepResult(ok=False, error="guard failed for deposit_collateral_a")
        # Compute updates (simultaneous)
        new_state = State(
            breaker_active=s.breaker_active,
            breaker_last_trigger_epoch=s.breaker_last_trigger_epoch,
            clearing_price_e8=s.clearing_price_e8,
            clearing_price_epoch=s.clearing_price_epoch,
            clearing_price_seen=s.clearing_price_seen,
            collateral_e8_a=(cmd.args["amount_e8"] + s.collateral_e8_a),
            collateral_e8_b=s.collateral_e8_b,
            entry_price_e8_a=s.entry_price_e8_a,
            entry_price_e8_b=s.entry_price_e8_b,
            fee_pool_e8=s.fee_pool_e8,
            index_price_e8=s.index_price_e8,
            initial_margin_bps=s.initial_margin_bps,
            liquidated_this_step=False,
            liquidation_penalty_bps=s.liquidation_penalty_bps,
            maintenance_margin_bps=s.maintenance_margin_bps,
            max_oracle_move_bps=s.max_oracle_move_bps,
            max_oracle_staleness_epochs=s.max_oracle_staleness_epochs,
            max_position_abs=s.max_position_abs,
            net_deposited_e8=(cmd.args["amount_e8"] + s.net_deposited_e8),
            now_epoch=s.now_epoch,
            oracle_last_update_epoch=s.oracle_last_update_epoch,
            oracle_seen=s.oracle_seen,
            position_base_a=s.position_base_a,
            position_base_b=s.position_base_b,
        )
        effects = {
            "collateral_after_a": new_state.collateral_e8_a,
            "collateral_after_b": new_state.collateral_e8_b,
            "event": "CollateralDepositedA",
            "fee_pool_after": new_state.fee_pool_e8,
            "liquidated": new_state.liquidated_this_step,
            "oracle_fresh": new_state.oracle_seen,
        }
        ok, failed = check_invariants(new_state)
        if not ok:
            return StepResult(ok=False, error=f"post-invariant violated: {failed}")
        return StepResult(ok=True, state=new_state, effects=effects)
    elif cmd.tag == "deposit_collateral_b":
        if "amount_e8" not in cmd.args or not (
            isinstance(cmd.args["amount_e8"], int)
            and not isinstance(cmd.args["amount_e8"], bool)
            and 1 <= cmd.args["amount_e8"] <= 1000000000000000000
        ):
            return StepResult(ok=False, error="invalid param amount_e8")
        if "auth_ok" not in cmd.args or not (isinstance(cmd.args["auth_ok"], bool)):
            return StepResult(ok=False, error="invalid param auth_ok")
        if not (
            ((cmd.args["amount_e8"] + s.collateral_e8_b) <= 1000000000000000000)
            and ((cmd.args["amount_e8"] + s.net_deposited_e8) <= 3000000000000000000)
            and (True == cmd.args["auth_ok"])
        ):
            return StepResult(ok=False, error="guard failed for deposit_collateral_b")
        # Compute updates (simultaneous)
        new_state = State(
            breaker_active=s.breaker_active,
            breaker_last_trigger_epoch=s.breaker_last_trigger_epoch,
            clearing_price_e8=s.clearing_price_e8,
            clearing_price_epoch=s.clearing_price_epoch,
            clearing_price_seen=s.clearing_price_seen,
            collateral_e8_a=s.collateral_e8_a,
            collateral_e8_b=(cmd.args["amount_e8"] + s.collateral_e8_b),
            entry_price_e8_a=s.entry_price_e8_a,
            entry_price_e8_b=s.entry_price_e8_b,
            fee_pool_e8=s.fee_pool_e8,
            index_price_e8=s.index_price_e8,
            initial_margin_bps=s.initial_margin_bps,
            liquidated_this_step=False,
            liquidation_penalty_bps=s.liquidation_penalty_bps,
            maintenance_margin_bps=s.maintenance_margin_bps,
            max_oracle_move_bps=s.max_oracle_move_bps,
            max_oracle_staleness_epochs=s.max_oracle_staleness_epochs,
            max_position_abs=s.max_position_abs,
            net_deposited_e8=(cmd.args["amount_e8"] + s.net_deposited_e8),
            now_epoch=s.now_epoch,
            oracle_last_update_epoch=s.oracle_last_update_epoch,
            oracle_seen=s.oracle_seen,
            position_base_a=s.position_base_a,
            position_base_b=s.position_base_b,
        )
        effects = {
            "collateral_after_a": new_state.collateral_e8_a,
            "collateral_after_b": new_state.collateral_e8_b,
            "event": "CollateralDepositedB",
            "fee_pool_after": new_state.fee_pool_e8,
            "liquidated": new_state.liquidated_this_step,
            "oracle_fresh": new_state.oracle_seen,
        }
        ok, failed = check_invariants(new_state)
        if not ok:
            return StepResult(ok=False, error=f"post-invariant violated: {failed}")
        return StepResult(ok=True, state=new_state, effects=effects)
    elif cmd.tag == "publish_clearing_price":
        if "price_e8" not in cmd.args or not (
            isinstance(cmd.args["price_e8"], int)
            and not isinstance(cmd.args["price_e8"], bool)
            and 1 <= cmd.args["price_e8"] <= 1000000000000
        ):
            return StepResult(ok=False, error="invalid param price_e8")
        if not (True and (s.clearing_price_epoch < s.now_epoch)):
            return StepResult(ok=False, error="guard failed for publish_clearing_price")
        # Compute updates (simultaneous)
        new_state = State(
            breaker_active=s.breaker_active,
            breaker_last_trigger_epoch=s.breaker_last_trigger_epoch,
            clearing_price_e8=cmd.args["price_e8"],
            clearing_price_epoch=s.now_epoch,
            clearing_price_seen=True,
            collateral_e8_a=s.collateral_e8_a,
            collateral_e8_b=s.collateral_e8_b,
            entry_price_e8_a=s.entry_price_e8_a,
            entry_price_e8_b=s.entry_price_e8_b,
            fee_pool_e8=s.fee_pool_e8,
            index_price_e8=s.index_price_e8,
            initial_margin_bps=s.initial_margin_bps,
            liquidated_this_step=False,
            liquidation_penalty_bps=s.liquidation_penalty_bps,
            maintenance_margin_bps=s.maintenance_margin_bps,
            max_oracle_move_bps=s.max_oracle_move_bps,
            max_oracle_staleness_epochs=s.max_oracle_staleness_epochs,
            max_position_abs=s.max_position_abs,
            net_deposited_e8=s.net_deposited_e8,
            now_epoch=s.now_epoch,
            oracle_last_update_epoch=s.oracle_last_update_epoch,
            oracle_seen=s.oracle_seen,
            position_base_a=s.position_base_a,
            position_base_b=s.position_base_b,
        )
        effects = {
            "collateral_after_a": new_state.collateral_e8_a,
            "collateral_after_b": new_state.collateral_e8_b,
            "event": "ClearingPricePublished",
            "fee_pool_after": new_state.fee_pool_e8,
            "liquidated": new_state.liquidated_this_step,
            "oracle_fresh": new_state.oracle_seen,
        }
        ok, failed = check_invariants(new_state)
        if not ok:
            return StepResult(ok=False, error=f"post-invariant violated: {failed}")
        return StepResult(ok=True, state=new_state, effects=effects)
    elif cmd.tag == "set_position_pair":
        if "new_position_base_a" not in cmd.args or not (
            isinstance(cmd.args["new_position_base_a"], int)
            and not isinstance(cmd.args["new_position_base_a"], bool)
            and -1000000 <= cmd.args["new_position_base_a"] <= 1000000
        ):
            return StepResult(ok=False, error="invalid param new_position_base_a")
        if "auth_ok" not in cmd.args or not (isinstance(cmd.args["auth_ok"], bool)):
            return StepResult(ok=False, error="invalid param auth_ok")
        if not (
            (
                (
                    cmd.args["new_position_base_a"]
                    if (cmd.args["new_position_base_a"] >= 0)
                    else (0 - cmd.args["new_position_base_a"])
                )
                <= s.max_position_abs
            )
            and (True == cmd.args["auth_ok"])
            and (
                (
                    (
                        cmd.args["new_position_base_a"]
                        if (cmd.args["new_position_base_a"] >= 0)
                        else (0 - cmd.args["new_position_base_a"])
                    )
                    <= (
                        s.position_base_a
                        if (s.position_base_a >= 0)
                        else (0 - s.position_base_a)
                    )
                )
                or (not s.breaker_active)
            )
            and (
                (
                    (
                        (s.now_epoch - s.oracle_last_update_epoch)
                        <= s.max_oracle_staleness_epochs
                    )
                    and (
                        s.collateral_e8_a
                        >= (
                            0
                            if 10000 == 0
                            else (
                                (
                                    (
                                        9999
                                        + (
                                            (
                                                (
                                                    cmd.args["new_position_base_a"]
                                                    if (
                                                        cmd.args["new_position_base_a"]
                                                        >= 0
                                                    )
                                                    else (
                                                        0
                                                        - cmd.args[
                                                            "new_position_base_a"
                                                        ]
                                                    )
                                                )
                                                * s.index_price_e8
                                            )
                                            * s.initial_margin_bps
                                        )
                                    )
                                    // 10000
                                )
                                + (
                                    1
                                    if (
                                        (
                                            9999
                                            + (
                                                (
                                                    (
                                                        cmd.args["new_position_base_a"]
                                                        if (
                                                            cmd.args[
                                                                "new_position_base_a"
                                                            ]
                                                            >= 0
                                                        )
                                                        else (
                                                            0
                                                            - cmd.args[
                                                                "new_position_base_a"
                                                            ]
                                                        )
                                                    )
                                                    * s.index_price_e8
                                                )
                                                * s.initial_margin_bps
                                            )
                                        )
                                        % 10000
                                    )
                                    < 0
                                    else 0
                                )
                            )
                        )
                    )
                    and (
                        s.collateral_e8_b
                        >= (
                            0
                            if 10000 == 0
                            else (
                                (
                                    (
                                        9999
                                        + (
                                            (
                                                (
                                                    cmd.args["new_position_base_a"]
                                                    if (
                                                        cmd.args["new_position_base_a"]
                                                        >= 0
                                                    )
                                                    else (
                                                        0
                                                        - cmd.args[
                                                            "new_position_base_a"
                                                        ]
                                                    )
                                                )
                                                * s.index_price_e8
                                            )
                                            * s.initial_margin_bps
                                        )
                                    )
                                    // 10000
                                )
                                + (
                                    1
                                    if (
                                        (
                                            9999
                                            + (
                                                (
                                                    (
                                                        cmd.args["new_position_base_a"]
                                                        if (
                                                            cmd.args[
                                                                "new_position_base_a"
                                                            ]
                                                            >= 0
                                                        )
                                                        else (
                                                            0
                                                            - cmd.args[
                                                                "new_position_base_a"
                                                            ]
                                                        )
                                                    )
                                                    * s.index_price_e8
                                                )
                                                * s.initial_margin_bps
                                            )
                                        )
                                        % 10000
                                    )
                                    < 0
                                    else 0
                                )
                            )
                        )
                    )
                )
                or s.breaker_active
            )
            and s.oracle_seen
        ):
            return StepResult(ok=False, error="guard failed for set_position_pair")
        # Compute updates (simultaneous)
        new_state = State(
            breaker_active=s.breaker_active,
            breaker_last_trigger_epoch=s.breaker_last_trigger_epoch,
            clearing_price_e8=s.clearing_price_e8,
            clearing_price_epoch=s.clearing_price_epoch,
            clearing_price_seen=s.clearing_price_seen,
            collateral_e8_a=s.collateral_e8_a,
            collateral_e8_b=s.collateral_e8_b,
            entry_price_e8_a=(
                0 if (0 == cmd.args["new_position_base_a"]) else s.index_price_e8
            ),
            entry_price_e8_b=(
                0 if (0 == cmd.args["new_position_base_a"]) else s.index_price_e8
            ),
            fee_pool_e8=s.fee_pool_e8,
            index_price_e8=s.index_price_e8,
            initial_margin_bps=s.initial_margin_bps,
            liquidated_this_step=False,
            liquidation_penalty_bps=s.liquidation_penalty_bps,
            maintenance_margin_bps=s.maintenance_margin_bps,
            max_oracle_move_bps=s.max_oracle_move_bps,
            max_oracle_staleness_epochs=s.max_oracle_staleness_epochs,
            max_position_abs=s.max_position_abs,
            net_deposited_e8=s.net_deposited_e8,
            now_epoch=s.now_epoch,
            oracle_last_update_epoch=s.oracle_last_update_epoch,
            oracle_seen=s.oracle_seen,
            position_base_a=cmd.args["new_position_base_a"],
            position_base_b=(0 - cmd.args["new_position_base_a"]),
        )
        effects = {
            "collateral_after_a": new_state.collateral_e8_a,
            "collateral_after_b": new_state.collateral_e8_b,
            "event": "PositionPairSet",
            "fee_pool_after": new_state.fee_pool_e8,
            "liquidated": new_state.liquidated_this_step,
            "oracle_fresh": new_state.oracle_seen,
        }
        ok, failed = check_invariants(new_state)
        if not ok:
            return StepResult(ok=False, error=f"post-invariant violated: {failed}")
        return StepResult(ok=True, state=new_state, effects=effects)
    elif cmd.tag == "settle_epoch":
        if not (
            (s.oracle_last_update_epoch < s.now_epoch)
            and (
                (
                    (
                        (
                            (
                                (
                                    (
                                        (
                                            0
                                            if 10000 == 0
                                            else (
                                                (
                                                    (
                                                        s.index_price_e8
                                                        * s.max_oracle_move_bps
                                                    )
                                                    // 10000
                                                )
                                                + (
                                                    1
                                                    if (
                                                        (
                                                            s.index_price_e8
                                                            * s.max_oracle_move_bps
                                                        )
                                                        % 10000
                                                    )
                                                    < 0
                                                    else 0
                                                )
                                            )
                                        )
                                        + s.index_price_e8
                                    )
                                    if (s.clearing_price_e8 >= s.index_price_e8)
                                    else (
                                        s.index_price_e8
                                        - (
                                            0
                                            if 10000 == 0
                                            else (
                                                (
                                                    (
                                                        s.index_price_e8
                                                        * s.max_oracle_move_bps
                                                    )
                                                    // 10000
                                                )
                                                + (
                                                    1
                                                    if (
                                                        (
                                                            s.index_price_e8
                                                            * s.max_oracle_move_bps
                                                        )
                                                        % 10000
                                                    )
                                                    < 0
                                                    else 0
                                                )
                                            )
                                        )
                                    )
                                )
                                if (
                                    (
                                        (
                                            10000
                                            * (
                                                (s.clearing_price_e8 - s.index_price_e8)
                                                if (
                                                    s.clearing_price_e8
                                                    >= s.index_price_e8
                                                )
                                                else (
                                                    s.index_price_e8
                                                    - s.clearing_price_e8
                                                )
                                            )
                                        )
                                        > (s.index_price_e8 * s.max_oracle_move_bps)
                                    )
                                    and s.oracle_seen
                                )
                                else s.clearing_price_e8
                            )
                            - s.index_price_e8
                        )
                        * s.position_base_a
                    )
                    + s.collateral_e8_a
                )
                <= 1000000000000000000
            )
            and (
                (
                    (
                        (
                            (
                                (
                                    (
                                        (
                                            0
                                            if 10000 == 0
                                            else (
                                                (
                                                    (
                                                        s.index_price_e8
                                                        * s.max_oracle_move_bps
                                                    )
                                                    // 10000
                                                )
                                                + (
                                                    1
                                                    if (
                                                        (
                                                            s.index_price_e8
                                                            * s.max_oracle_move_bps
                                                        )
                                                        % 10000
                                                    )
                                                    < 0
                                                    else 0
                                                )
                                            )
                                        )
                                        + s.index_price_e8
                                    )
                                    if (s.clearing_price_e8 >= s.index_price_e8)
                                    else (
                                        s.index_price_e8
                                        - (
                                            0
                                            if 10000 == 0
                                            else (
                                                (
                                                    (
                                                        s.index_price_e8
                                                        * s.max_oracle_move_bps
                                                    )
                                                    // 10000
                                                )
                                                + (
                                                    1
                                                    if (
                                                        (
                                                            s.index_price_e8
                                                            * s.max_oracle_move_bps
                                                        )
                                                        % 10000
                                                    )
                                                    < 0
                                                    else 0
                                                )
                                            )
                                        )
                                    )
                                )
                                if (
                                    (
                                        (
                                            10000
                                            * (
                                                (s.clearing_price_e8 - s.index_price_e8)
                                                if (
                                                    s.clearing_price_e8
                                                    >= s.index_price_e8
                                                )
                                                else (
                                                    s.index_price_e8
                                                    - s.clearing_price_e8
                                                )
                                            )
                                        )
                                        > (s.index_price_e8 * s.max_oracle_move_bps)
                                    )
                                    and s.oracle_seen
                                )
                                else s.clearing_price_e8
                            )
                            - s.index_price_e8
                        )
                        * s.position_base_b
                    )
                    + s.collateral_e8_b
                )
                <= 1000000000000000000
            )
            and (s.clearing_price_epoch == s.now_epoch)
            and (
                (
                    (
                        (
                            (
                                (
                                    (
                                        (
                                            0
                                            if 10000 == 0
                                            else (
                                                (
                                                    (
                                                        s.index_price_e8
                                                        * s.max_oracle_move_bps
                                                    )
                                                    // 10000
                                                )
                                                + (
                                                    1
                                                    if (
                                                        (
                                                            s.index_price_e8
                                                            * s.max_oracle_move_bps
                                                        )
                                                        % 10000
                                                    )
                                                    < 0
                                                    else 0
                                                )
                                            )
                                        )
                                        + s.index_price_e8
                                    )
                                    if (s.clearing_price_e8 >= s.index_price_e8)
                                    else (
                                        s.index_price_e8
                                        - (
                                            0
                                            if 10000 == 0
                                            else (
                                                (
                                                    (
                                                        s.index_price_e8
                                                        * s.max_oracle_move_bps
                                                    )
                                                    // 10000
                                                )
                                                + (
                                                    1
                                                    if (
                                                        (
                                                            s.index_price_e8
                                                            * s.max_oracle_move_bps
                                                        )
                                                        % 10000
                                                    )
                                                    < 0
                                                    else 0
                                                )
                                            )
                                        )
                                    )
                                )
                                if (
                                    (
                                        (
                                            10000
                                            * (
                                                (s.clearing_price_e8 - s.index_price_e8)
                                                if (
                                                    s.clearing_price_e8
                                                    >= s.index_price_e8
                                                )
                                                else (
                                                    s.index_price_e8
                                                    - s.clearing_price_e8
                                                )
                                            )
                                        )
                                        > (s.index_price_e8 * s.max_oracle_move_bps)
                                    )
                                    and s.oracle_seen
                                )
                                else s.clearing_price_e8
                            )
                            - s.index_price_e8
                        )
                        * s.position_base_a
                    )
                    + s.collateral_e8_a
                )
                >= 0
            )
            and (
                (
                    (
                        (
                            (
                                (
                                    (
                                        (
                                            0
                                            if 10000 == 0
                                            else (
                                                (
                                                    (
                                                        s.index_price_e8
                                                        * s.max_oracle_move_bps
                                                    )
                                                    // 10000
                                                )
                                                + (
                                                    1
                                                    if (
                                                        (
                                                            s.index_price_e8
                                                            * s.max_oracle_move_bps
                                                        )
                                                        % 10000
                                                    )
                                                    < 0
                                                    else 0
                                                )
                                            )
                                        )
                                        + s.index_price_e8
                                    )
                                    if (s.clearing_price_e8 >= s.index_price_e8)
                                    else (
                                        s.index_price_e8
                                        - (
                                            0
                                            if 10000 == 0
                                            else (
                                                (
                                                    (
                                                        s.index_price_e8
                                                        * s.max_oracle_move_bps
                                                    )
                                                    // 10000
                                                )
                                                + (
                                                    1
                                                    if (
                                                        (
                                                            s.index_price_e8
                                                            * s.max_oracle_move_bps
                                                        )
                                                        % 10000
                                                    )
                                                    < 0
                                                    else 0
                                                )
                                            )
                                        )
                                    )
                                )
                                if (
                                    (
                                        (
                                            10000
                                            * (
                                                (s.clearing_price_e8 - s.index_price_e8)
                                                if (
                                                    s.clearing_price_e8
                                                    >= s.index_price_e8
                                                )
                                                else (
                                                    s.index_price_e8
                                                    - s.clearing_price_e8
                                                )
                                            )
                                        )
                                        > (s.index_price_e8 * s.max_oracle_move_bps)
                                    )
                                    and s.oracle_seen
                                )
                                else s.clearing_price_e8
                            )
                            - s.index_price_e8
                        )
                        * s.position_base_b
                    )
                    + s.collateral_e8_b
                )
                >= 0
            )
            and s.clearing_price_seen
        ):
            return StepResult(ok=False, error="guard failed for settle_epoch")
        # Compute updates (simultaneous)
        new_state = State(
            breaker_active=(
                (
                    (
                        (
                            10000
                            * (
                                (s.clearing_price_e8 - s.index_price_e8)
                                if (s.clearing_price_e8 >= s.index_price_e8)
                                else (s.index_price_e8 - s.clearing_price_e8)
                            )
                        )
                        > (s.index_price_e8 * s.max_oracle_move_bps)
                    )
                    and s.oracle_seen
                )
                or s.breaker_active
            ),
            breaker_last_trigger_epoch=(
                s.now_epoch
                if (
                    (
                        (
                            10000
                            * (
                                (s.clearing_price_e8 - s.index_price_e8)
                                if (s.clearing_price_e8 >= s.index_price_e8)
                                else (s.index_price_e8 - s.clearing_price_e8)
                            )
                        )
                        > (s.index_price_e8 * s.max_oracle_move_bps)
                    )
                    and s.oracle_seen
                )
                else s.breaker_last_trigger_epoch
            ),
            clearing_price_e8=s.clearing_price_e8,
            clearing_price_epoch=s.clearing_price_epoch,
            clearing_price_seen=s.clearing_price_seen,
            collateral_e8_a=(
                (
                    (
                        (
                            (
                                (
                                    (
                                        (
                                            0
                                            if 10000 == 0
                                            else (
                                                (
                                                    (
                                                        s.index_price_e8
                                                        * s.max_oracle_move_bps
                                                    )
                                                    // 10000
                                                )
                                                + (
                                                    1
                                                    if (
                                                        (
                                                            s.index_price_e8
                                                            * s.max_oracle_move_bps
                                                        )
                                                        % 10000
                                                    )
                                                    < 0
                                                    else 0
                                                )
                                            )
                                        )
                                        + s.index_price_e8
                                    )
                                    if (s.clearing_price_e8 >= s.index_price_e8)
                                    else (
                                        s.index_price_e8
                                        - (
                                            0
                                            if 10000 == 0
                                            else (
                                                (
                                                    (
                                                        s.index_price_e8
                                                        * s.max_oracle_move_bps
                                                    )
                                                    // 10000
                                                )
                                                + (
                                                    1
                                                    if (
                                                        (
                                                            s.index_price_e8
                                                            * s.max_oracle_move_bps
                                                        )
                                                        % 10000
                                                    )
                                                    < 0
                                                    else 0
                                                )
                                            )
                                        )
                                    )
                                )
                                if (
                                    (
                                        (
                                            10000
                                            * (
                                                (s.clearing_price_e8 - s.index_price_e8)
                                                if (
                                                    s.clearing_price_e8
                                                    >= s.index_price_e8
                                                )
                                                else (
                                                    s.index_price_e8
                                                    - s.clearing_price_e8
                                                )
                                            )
                                        )
                                        > (s.index_price_e8 * s.max_oracle_move_bps)
                                    )
                                    and s.oracle_seen
                                )
                                else s.clearing_price_e8
                            )
                            - s.index_price_e8
                        )
                        * s.position_base_a
                    )
                    + s.collateral_e8_a
                )
                - (
                    (
                        (
                            0
                            if 10000 == 0
                            else (
                                (
                                    (
                                        9999
                                        + (
                                            (
                                                (
                                                    s.position_base_a
                                                    if (s.position_base_a >= 0)
                                                    else (0 - s.position_base_a)
                                                )
                                                * (
                                                    (
                                                        (
                                                            (
                                                                0
                                                                if 10000 == 0
                                                                else (
                                                                    (
                                                                        (
                                                                            s.index_price_e8
                                                                            * s.max_oracle_move_bps
                                                                        )
                                                                        // 10000
                                                                    )
                                                                    + (
                                                                        1
                                                                        if (
                                                                            (
                                                                                s.index_price_e8
                                                                                * s.max_oracle_move_bps
                                                                            )
                                                                            % 10000
                                                                        )
                                                                        < 0
                                                                        else 0
                                                                    )
                                                                )
                                                            )
                                                            + s.index_price_e8
                                                        )
                                                        if (
                                                            s.clearing_price_e8
                                                            >= s.index_price_e8
                                                        )
                                                        else (
                                                            s.index_price_e8
                                                            - (
                                                                0
                                                                if 10000 == 0
                                                                else (
                                                                    (
                                                                        (
                                                                            s.index_price_e8
                                                                            * s.max_oracle_move_bps
                                                                        )
                                                                        // 10000
                                                                    )
                                                                    + (
                                                                        1
                                                                        if (
                                                                            (
                                                                                s.index_price_e8
                                                                                * s.max_oracle_move_bps
                                                                            )
                                                                            % 10000
                                                                        )
                                                                        < 0
                                                                        else 0
                                                                    )
                                                                )
                                                            )
                                                        )
                                                    )
                                                    if (
                                                        (
                                                            (
                                                                10000
                                                                * (
                                                                    (
                                                                        s.clearing_price_e8
                                                                        - s.index_price_e8
                                                                    )
                                                                    if (
                                                                        s.clearing_price_e8
                                                                        >= s.index_price_e8
                                                                    )
                                                                    else (
                                                                        s.index_price_e8
                                                                        - s.clearing_price_e8
                                                                    )
                                                                )
                                                            )
                                                            > (
                                                                s.index_price_e8
                                                                * s.max_oracle_move_bps
                                                            )
                                                        )
                                                        and s.oracle_seen
                                                    )
                                                    else s.clearing_price_e8
                                                )
                                            )
                                            * s.liquidation_penalty_bps
                                        )
                                    )
                                    // 10000
                                )
                                + (
                                    1
                                    if (
                                        (
                                            9999
                                            + (
                                                (
                                                    (
                                                        s.position_base_a
                                                        if (s.position_base_a >= 0)
                                                        else (0 - s.position_base_a)
                                                    )
                                                    * (
                                                        (
                                                            (
                                                                (
                                                                    0
                                                                    if 10000 == 0
                                                                    else (
                                                                        (
                                                                            (
                                                                                s.index_price_e8
                                                                                * s.max_oracle_move_bps
                                                                            )
                                                                            // 10000
                                                                        )
                                                                        + (
                                                                            1
                                                                            if (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                % 10000
                                                                            )
                                                                            < 0
                                                                            else 0
                                                                        )
                                                                    )
                                                                )
                                                                + s.index_price_e8
                                                            )
                                                            if (
                                                                s.clearing_price_e8
                                                                >= s.index_price_e8
                                                            )
                                                            else (
                                                                s.index_price_e8
                                                                - (
                                                                    0
                                                                    if 10000 == 0
                                                                    else (
                                                                        (
                                                                            (
                                                                                s.index_price_e8
                                                                                * s.max_oracle_move_bps
                                                                            )
                                                                            // 10000
                                                                        )
                                                                        + (
                                                                            1
                                                                            if (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                % 10000
                                                                            )
                                                                            < 0
                                                                            else 0
                                                                        )
                                                                    )
                                                                )
                                                            )
                                                        )
                                                        if (
                                                            (
                                                                (
                                                                    10000
                                                                    * (
                                                                        (
                                                                            s.clearing_price_e8
                                                                            - s.index_price_e8
                                                                        )
                                                                        if (
                                                                            s.clearing_price_e8
                                                                            >= s.index_price_e8
                                                                        )
                                                                        else (
                                                                            s.index_price_e8
                                                                            - s.clearing_price_e8
                                                                        )
                                                                    )
                                                                )
                                                                > (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                            )
                                                            and s.oracle_seen
                                                        )
                                                        else s.clearing_price_e8
                                                    )
                                                )
                                                * s.liquidation_penalty_bps
                                            )
                                        )
                                        % 10000
                                    )
                                    < 0
                                    else 0
                                )
                            )
                        )
                        if (
                            (
                                0
                                if 10000 == 0
                                else (
                                    (
                                        (
                                            9999
                                            + (
                                                (
                                                    (
                                                        s.position_base_a
                                                        if (s.position_base_a >= 0)
                                                        else (0 - s.position_base_a)
                                                    )
                                                    * (
                                                        (
                                                            (
                                                                (
                                                                    0
                                                                    if 10000 == 0
                                                                    else (
                                                                        (
                                                                            (
                                                                                s.index_price_e8
                                                                                * s.max_oracle_move_bps
                                                                            )
                                                                            // 10000
                                                                        )
                                                                        + (
                                                                            1
                                                                            if (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                % 10000
                                                                            )
                                                                            < 0
                                                                            else 0
                                                                        )
                                                                    )
                                                                )
                                                                + s.index_price_e8
                                                            )
                                                            if (
                                                                s.clearing_price_e8
                                                                >= s.index_price_e8
                                                            )
                                                            else (
                                                                s.index_price_e8
                                                                - (
                                                                    0
                                                                    if 10000 == 0
                                                                    else (
                                                                        (
                                                                            (
                                                                                s.index_price_e8
                                                                                * s.max_oracle_move_bps
                                                                            )
                                                                            // 10000
                                                                        )
                                                                        + (
                                                                            1
                                                                            if (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                % 10000
                                                                            )
                                                                            < 0
                                                                            else 0
                                                                        )
                                                                    )
                                                                )
                                                            )
                                                        )
                                                        if (
                                                            (
                                                                (
                                                                    10000
                                                                    * (
                                                                        (
                                                                            s.clearing_price_e8
                                                                            - s.index_price_e8
                                                                        )
                                                                        if (
                                                                            s.clearing_price_e8
                                                                            >= s.index_price_e8
                                                                        )
                                                                        else (
                                                                            s.index_price_e8
                                                                            - s.clearing_price_e8
                                                                        )
                                                                    )
                                                                )
                                                                > (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                            )
                                                            and s.oracle_seen
                                                        )
                                                        else s.clearing_price_e8
                                                    )
                                                )
                                                * s.liquidation_penalty_bps
                                            )
                                        )
                                        // 10000
                                    )
                                    + (
                                        1
                                        if (
                                            (
                                                9999
                                                + (
                                                    (
                                                        (
                                                            s.position_base_a
                                                            if (s.position_base_a >= 0)
                                                            else (0 - s.position_base_a)
                                                        )
                                                        * (
                                                            (
                                                                (
                                                                    (
                                                                        0
                                                                        if 10000 == 0
                                                                        else (
                                                                            (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                // 10000
                                                                            )
                                                                            + (
                                                                                1
                                                                                if (
                                                                                    (
                                                                                        s.index_price_e8
                                                                                        * s.max_oracle_move_bps
                                                                                    )
                                                                                    % 10000
                                                                                )
                                                                                < 0
                                                                                else 0
                                                                            )
                                                                        )
                                                                    )
                                                                    + s.index_price_e8
                                                                )
                                                                if (
                                                                    s.clearing_price_e8
                                                                    >= s.index_price_e8
                                                                )
                                                                else (
                                                                    s.index_price_e8
                                                                    - (
                                                                        0
                                                                        if 10000 == 0
                                                                        else (
                                                                            (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                // 10000
                                                                            )
                                                                            + (
                                                                                1
                                                                                if (
                                                                                    (
                                                                                        s.index_price_e8
                                                                                        * s.max_oracle_move_bps
                                                                                    )
                                                                                    % 10000
                                                                                )
                                                                                < 0
                                                                                else 0
                                                                            )
                                                                        )
                                                                    )
                                                                )
                                                            )
                                                            if (
                                                                (
                                                                    (
                                                                        10000
                                                                        * (
                                                                            (
                                                                                s.clearing_price_e8
                                                                                - s.index_price_e8
                                                                            )
                                                                            if (
                                                                                s.clearing_price_e8
                                                                                >= s.index_price_e8
                                                                            )
                                                                            else (
                                                                                s.index_price_e8
                                                                                - s.clearing_price_e8
                                                                            )
                                                                        )
                                                                    )
                                                                    > (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                )
                                                                and s.oracle_seen
                                                            )
                                                            else s.clearing_price_e8
                                                        )
                                                    )
                                                    * s.liquidation_penalty_bps
                                                )
                                            )
                                            % 10000
                                        )
                                        < 0
                                        else 0
                                    )
                                )
                            )
                            <= (
                                (
                                    (
                                        (
                                            (
                                                (
                                                    (
                                                        0
                                                        if 10000 == 0
                                                        else (
                                                            (
                                                                (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                                // 10000
                                                            )
                                                            + (
                                                                1
                                                                if (
                                                                    (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                    % 10000
                                                                )
                                                                < 0
                                                                else 0
                                                            )
                                                        )
                                                    )
                                                    + s.index_price_e8
                                                )
                                                if (
                                                    s.clearing_price_e8
                                                    >= s.index_price_e8
                                                )
                                                else (
                                                    s.index_price_e8
                                                    - (
                                                        0
                                                        if 10000 == 0
                                                        else (
                                                            (
                                                                (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                                // 10000
                                                            )
                                                            + (
                                                                1
                                                                if (
                                                                    (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                    % 10000
                                                                )
                                                                < 0
                                                                else 0
                                                            )
                                                        )
                                                    )
                                                )
                                            )
                                            if (
                                                (
                                                    (
                                                        10000
                                                        * (
                                                            (
                                                                s.clearing_price_e8
                                                                - s.index_price_e8
                                                            )
                                                            if (
                                                                s.clearing_price_e8
                                                                >= s.index_price_e8
                                                            )
                                                            else (
                                                                s.index_price_e8
                                                                - s.clearing_price_e8
                                                            )
                                                        )
                                                    )
                                                    > (
                                                        s.index_price_e8
                                                        * s.max_oracle_move_bps
                                                    )
                                                )
                                                and s.oracle_seen
                                            )
                                            else s.clearing_price_e8
                                        )
                                        - s.index_price_e8
                                    )
                                    * s.position_base_a
                                )
                                + s.collateral_e8_a
                            )
                        )
                        else (
                            (
                                (
                                    (
                                        (
                                            (
                                                (
                                                    0
                                                    if 10000 == 0
                                                    else (
                                                        (
                                                            (
                                                                s.index_price_e8
                                                                * s.max_oracle_move_bps
                                                            )
                                                            // 10000
                                                        )
                                                        + (
                                                            1
                                                            if (
                                                                (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                                % 10000
                                                            )
                                                            < 0
                                                            else 0
                                                        )
                                                    )
                                                )
                                                + s.index_price_e8
                                            )
                                            if (s.clearing_price_e8 >= s.index_price_e8)
                                            else (
                                                s.index_price_e8
                                                - (
                                                    0
                                                    if 10000 == 0
                                                    else (
                                                        (
                                                            (
                                                                s.index_price_e8
                                                                * s.max_oracle_move_bps
                                                            )
                                                            // 10000
                                                        )
                                                        + (
                                                            1
                                                            if (
                                                                (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                                % 10000
                                                            )
                                                            < 0
                                                            else 0
                                                        )
                                                    )
                                                )
                                            )
                                        )
                                        if (
                                            (
                                                (
                                                    10000
                                                    * (
                                                        (
                                                            s.clearing_price_e8
                                                            - s.index_price_e8
                                                        )
                                                        if (
                                                            s.clearing_price_e8
                                                            >= s.index_price_e8
                                                        )
                                                        else (
                                                            s.index_price_e8
                                                            - s.clearing_price_e8
                                                        )
                                                    )
                                                )
                                                > (
                                                    s.index_price_e8
                                                    * s.max_oracle_move_bps
                                                )
                                            )
                                            and s.oracle_seen
                                        )
                                        else s.clearing_price_e8
                                    )
                                    - s.index_price_e8
                                )
                                * s.position_base_a
                            )
                            + s.collateral_e8_a
                        )
                    )
                    if (
                        (
                            (
                                (
                                    (
                                        (
                                            (
                                                (
                                                    (
                                                        0
                                                        if 10000 == 0
                                                        else (
                                                            (
                                                                (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                                // 10000
                                                            )
                                                            + (
                                                                1
                                                                if (
                                                                    (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                    % 10000
                                                                )
                                                                < 0
                                                                else 0
                                                            )
                                                        )
                                                    )
                                                    + s.index_price_e8
                                                )
                                                if (
                                                    s.clearing_price_e8
                                                    >= s.index_price_e8
                                                )
                                                else (
                                                    s.index_price_e8
                                                    - (
                                                        0
                                                        if 10000 == 0
                                                        else (
                                                            (
                                                                (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                                // 10000
                                                            )
                                                            + (
                                                                1
                                                                if (
                                                                    (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                    % 10000
                                                                )
                                                                < 0
                                                                else 0
                                                            )
                                                        )
                                                    )
                                                )
                                            )
                                            if (
                                                (
                                                    (
                                                        10000
                                                        * (
                                                            (
                                                                s.clearing_price_e8
                                                                - s.index_price_e8
                                                            )
                                                            if (
                                                                s.clearing_price_e8
                                                                >= s.index_price_e8
                                                            )
                                                            else (
                                                                s.index_price_e8
                                                                - s.clearing_price_e8
                                                            )
                                                        )
                                                    )
                                                    > (
                                                        s.index_price_e8
                                                        * s.max_oracle_move_bps
                                                    )
                                                )
                                                and s.oracle_seen
                                            )
                                            else s.clearing_price_e8
                                        )
                                        - s.index_price_e8
                                    )
                                    * s.position_base_a
                                )
                                + s.collateral_e8_a
                            )
                            < (
                                0
                                if 10000 == 0
                                else (
                                    (
                                        (
                                            9999
                                            + (
                                                (
                                                    (
                                                        s.position_base_a
                                                        if (s.position_base_a >= 0)
                                                        else (0 - s.position_base_a)
                                                    )
                                                    * (
                                                        (
                                                            (
                                                                (
                                                                    0
                                                                    if 10000 == 0
                                                                    else (
                                                                        (
                                                                            (
                                                                                s.index_price_e8
                                                                                * s.max_oracle_move_bps
                                                                            )
                                                                            // 10000
                                                                        )
                                                                        + (
                                                                            1
                                                                            if (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                % 10000
                                                                            )
                                                                            < 0
                                                                            else 0
                                                                        )
                                                                    )
                                                                )
                                                                + s.index_price_e8
                                                            )
                                                            if (
                                                                s.clearing_price_e8
                                                                >= s.index_price_e8
                                                            )
                                                            else (
                                                                s.index_price_e8
                                                                - (
                                                                    0
                                                                    if 10000 == 0
                                                                    else (
                                                                        (
                                                                            (
                                                                                s.index_price_e8
                                                                                * s.max_oracle_move_bps
                                                                            )
                                                                            // 10000
                                                                        )
                                                                        + (
                                                                            1
                                                                            if (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                % 10000
                                                                            )
                                                                            < 0
                                                                            else 0
                                                                        )
                                                                    )
                                                                )
                                                            )
                                                        )
                                                        if (
                                                            (
                                                                (
                                                                    10000
                                                                    * (
                                                                        (
                                                                            s.clearing_price_e8
                                                                            - s.index_price_e8
                                                                        )
                                                                        if (
                                                                            s.clearing_price_e8
                                                                            >= s.index_price_e8
                                                                        )
                                                                        else (
                                                                            s.index_price_e8
                                                                            - s.clearing_price_e8
                                                                        )
                                                                    )
                                                                )
                                                                > (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                            )
                                                            and s.oracle_seen
                                                        )
                                                        else s.clearing_price_e8
                                                    )
                                                )
                                                * s.maintenance_margin_bps
                                            )
                                        )
                                        // 10000
                                    )
                                    + (
                                        1
                                        if (
                                            (
                                                9999
                                                + (
                                                    (
                                                        (
                                                            s.position_base_a
                                                            if (s.position_base_a >= 0)
                                                            else (0 - s.position_base_a)
                                                        )
                                                        * (
                                                            (
                                                                (
                                                                    (
                                                                        0
                                                                        if 10000 == 0
                                                                        else (
                                                                            (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                // 10000
                                                                            )
                                                                            + (
                                                                                1
                                                                                if (
                                                                                    (
                                                                                        s.index_price_e8
                                                                                        * s.max_oracle_move_bps
                                                                                    )
                                                                                    % 10000
                                                                                )
                                                                                < 0
                                                                                else 0
                                                                            )
                                                                        )
                                                                    )
                                                                    + s.index_price_e8
                                                                )
                                                                if (
                                                                    s.clearing_price_e8
                                                                    >= s.index_price_e8
                                                                )
                                                                else (
                                                                    s.index_price_e8
                                                                    - (
                                                                        0
                                                                        if 10000 == 0
                                                                        else (
                                                                            (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                // 10000
                                                                            )
                                                                            + (
                                                                                1
                                                                                if (
                                                                                    (
                                                                                        s.index_price_e8
                                                                                        * s.max_oracle_move_bps
                                                                                    )
                                                                                    % 10000
                                                                                )
                                                                                < 0
                                                                                else 0
                                                                            )
                                                                        )
                                                                    )
                                                                )
                                                            )
                                                            if (
                                                                (
                                                                    (
                                                                        10000
                                                                        * (
                                                                            (
                                                                                s.clearing_price_e8
                                                                                - s.index_price_e8
                                                                            )
                                                                            if (
                                                                                s.clearing_price_e8
                                                                                >= s.index_price_e8
                                                                            )
                                                                            else (
                                                                                s.index_price_e8
                                                                                - s.clearing_price_e8
                                                                            )
                                                                        )
                                                                    )
                                                                    > (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                )
                                                                and s.oracle_seen
                                                            )
                                                            else s.clearing_price_e8
                                                        )
                                                    )
                                                    * s.maintenance_margin_bps
                                                )
                                            )
                                            % 10000
                                        )
                                        < 0
                                        else 0
                                    )
                                )
                            )
                        )
                        and (not (0 == s.position_base_a))
                    )
                    else 0
                )
            ),
            collateral_e8_b=(
                (
                    (
                        (
                            (
                                (
                                    (
                                        (
                                            0
                                            if 10000 == 0
                                            else (
                                                (
                                                    (
                                                        s.index_price_e8
                                                        * s.max_oracle_move_bps
                                                    )
                                                    // 10000
                                                )
                                                + (
                                                    1
                                                    if (
                                                        (
                                                            s.index_price_e8
                                                            * s.max_oracle_move_bps
                                                        )
                                                        % 10000
                                                    )
                                                    < 0
                                                    else 0
                                                )
                                            )
                                        )
                                        + s.index_price_e8
                                    )
                                    if (s.clearing_price_e8 >= s.index_price_e8)
                                    else (
                                        s.index_price_e8
                                        - (
                                            0
                                            if 10000 == 0
                                            else (
                                                (
                                                    (
                                                        s.index_price_e8
                                                        * s.max_oracle_move_bps
                                                    )
                                                    // 10000
                                                )
                                                + (
                                                    1
                                                    if (
                                                        (
                                                            s.index_price_e8
                                                            * s.max_oracle_move_bps
                                                        )
                                                        % 10000
                                                    )
                                                    < 0
                                                    else 0
                                                )
                                            )
                                        )
                                    )
                                )
                                if (
                                    (
                                        (
                                            10000
                                            * (
                                                (s.clearing_price_e8 - s.index_price_e8)
                                                if (
                                                    s.clearing_price_e8
                                                    >= s.index_price_e8
                                                )
                                                else (
                                                    s.index_price_e8
                                                    - s.clearing_price_e8
                                                )
                                            )
                                        )
                                        > (s.index_price_e8 * s.max_oracle_move_bps)
                                    )
                                    and s.oracle_seen
                                )
                                else s.clearing_price_e8
                            )
                            - s.index_price_e8
                        )
                        * s.position_base_b
                    )
                    + s.collateral_e8_b
                )
                - (
                    (
                        (
                            0
                            if 10000 == 0
                            else (
                                (
                                    (
                                        9999
                                        + (
                                            (
                                                (
                                                    s.position_base_b
                                                    if (s.position_base_b >= 0)
                                                    else (0 - s.position_base_b)
                                                )
                                                * (
                                                    (
                                                        (
                                                            (
                                                                0
                                                                if 10000 == 0
                                                                else (
                                                                    (
                                                                        (
                                                                            s.index_price_e8
                                                                            * s.max_oracle_move_bps
                                                                        )
                                                                        // 10000
                                                                    )
                                                                    + (
                                                                        1
                                                                        if (
                                                                            (
                                                                                s.index_price_e8
                                                                                * s.max_oracle_move_bps
                                                                            )
                                                                            % 10000
                                                                        )
                                                                        < 0
                                                                        else 0
                                                                    )
                                                                )
                                                            )
                                                            + s.index_price_e8
                                                        )
                                                        if (
                                                            s.clearing_price_e8
                                                            >= s.index_price_e8
                                                        )
                                                        else (
                                                            s.index_price_e8
                                                            - (
                                                                0
                                                                if 10000 == 0
                                                                else (
                                                                    (
                                                                        (
                                                                            s.index_price_e8
                                                                            * s.max_oracle_move_bps
                                                                        )
                                                                        // 10000
                                                                    )
                                                                    + (
                                                                        1
                                                                        if (
                                                                            (
                                                                                s.index_price_e8
                                                                                * s.max_oracle_move_bps
                                                                            )
                                                                            % 10000
                                                                        )
                                                                        < 0
                                                                        else 0
                                                                    )
                                                                )
                                                            )
                                                        )
                                                    )
                                                    if (
                                                        (
                                                            (
                                                                10000
                                                                * (
                                                                    (
                                                                        s.clearing_price_e8
                                                                        - s.index_price_e8
                                                                    )
                                                                    if (
                                                                        s.clearing_price_e8
                                                                        >= s.index_price_e8
                                                                    )
                                                                    else (
                                                                        s.index_price_e8
                                                                        - s.clearing_price_e8
                                                                    )
                                                                )
                                                            )
                                                            > (
                                                                s.index_price_e8
                                                                * s.max_oracle_move_bps
                                                            )
                                                        )
                                                        and s.oracle_seen
                                                    )
                                                    else s.clearing_price_e8
                                                )
                                            )
                                            * s.liquidation_penalty_bps
                                        )
                                    )
                                    // 10000
                                )
                                + (
                                    1
                                    if (
                                        (
                                            9999
                                            + (
                                                (
                                                    (
                                                        s.position_base_b
                                                        if (s.position_base_b >= 0)
                                                        else (0 - s.position_base_b)
                                                    )
                                                    * (
                                                        (
                                                            (
                                                                (
                                                                    0
                                                                    if 10000 == 0
                                                                    else (
                                                                        (
                                                                            (
                                                                                s.index_price_e8
                                                                                * s.max_oracle_move_bps
                                                                            )
                                                                            // 10000
                                                                        )
                                                                        + (
                                                                            1
                                                                            if (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                % 10000
                                                                            )
                                                                            < 0
                                                                            else 0
                                                                        )
                                                                    )
                                                                )
                                                                + s.index_price_e8
                                                            )
                                                            if (
                                                                s.clearing_price_e8
                                                                >= s.index_price_e8
                                                            )
                                                            else (
                                                                s.index_price_e8
                                                                - (
                                                                    0
                                                                    if 10000 == 0
                                                                    else (
                                                                        (
                                                                            (
                                                                                s.index_price_e8
                                                                                * s.max_oracle_move_bps
                                                                            )
                                                                            // 10000
                                                                        )
                                                                        + (
                                                                            1
                                                                            if (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                % 10000
                                                                            )
                                                                            < 0
                                                                            else 0
                                                                        )
                                                                    )
                                                                )
                                                            )
                                                        )
                                                        if (
                                                            (
                                                                (
                                                                    10000
                                                                    * (
                                                                        (
                                                                            s.clearing_price_e8
                                                                            - s.index_price_e8
                                                                        )
                                                                        if (
                                                                            s.clearing_price_e8
                                                                            >= s.index_price_e8
                                                                        )
                                                                        else (
                                                                            s.index_price_e8
                                                                            - s.clearing_price_e8
                                                                        )
                                                                    )
                                                                )
                                                                > (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                            )
                                                            and s.oracle_seen
                                                        )
                                                        else s.clearing_price_e8
                                                    )
                                                )
                                                * s.liquidation_penalty_bps
                                            )
                                        )
                                        % 10000
                                    )
                                    < 0
                                    else 0
                                )
                            )
                        )
                        if (
                            (
                                0
                                if 10000 == 0
                                else (
                                    (
                                        (
                                            9999
                                            + (
                                                (
                                                    (
                                                        s.position_base_b
                                                        if (s.position_base_b >= 0)
                                                        else (0 - s.position_base_b)
                                                    )
                                                    * (
                                                        (
                                                            (
                                                                (
                                                                    0
                                                                    if 10000 == 0
                                                                    else (
                                                                        (
                                                                            (
                                                                                s.index_price_e8
                                                                                * s.max_oracle_move_bps
                                                                            )
                                                                            // 10000
                                                                        )
                                                                        + (
                                                                            1
                                                                            if (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                % 10000
                                                                            )
                                                                            < 0
                                                                            else 0
                                                                        )
                                                                    )
                                                                )
                                                                + s.index_price_e8
                                                            )
                                                            if (
                                                                s.clearing_price_e8
                                                                >= s.index_price_e8
                                                            )
                                                            else (
                                                                s.index_price_e8
                                                                - (
                                                                    0
                                                                    if 10000 == 0
                                                                    else (
                                                                        (
                                                                            (
                                                                                s.index_price_e8
                                                                                * s.max_oracle_move_bps
                                                                            )
                                                                            // 10000
                                                                        )
                                                                        + (
                                                                            1
                                                                            if (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                % 10000
                                                                            )
                                                                            < 0
                                                                            else 0
                                                                        )
                                                                    )
                                                                )
                                                            )
                                                        )
                                                        if (
                                                            (
                                                                (
                                                                    10000
                                                                    * (
                                                                        (
                                                                            s.clearing_price_e8
                                                                            - s.index_price_e8
                                                                        )
                                                                        if (
                                                                            s.clearing_price_e8
                                                                            >= s.index_price_e8
                                                                        )
                                                                        else (
                                                                            s.index_price_e8
                                                                            - s.clearing_price_e8
                                                                        )
                                                                    )
                                                                )
                                                                > (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                            )
                                                            and s.oracle_seen
                                                        )
                                                        else s.clearing_price_e8
                                                    )
                                                )
                                                * s.liquidation_penalty_bps
                                            )
                                        )
                                        // 10000
                                    )
                                    + (
                                        1
                                        if (
                                            (
                                                9999
                                                + (
                                                    (
                                                        (
                                                            s.position_base_b
                                                            if (s.position_base_b >= 0)
                                                            else (0 - s.position_base_b)
                                                        )
                                                        * (
                                                            (
                                                                (
                                                                    (
                                                                        0
                                                                        if 10000 == 0
                                                                        else (
                                                                            (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                // 10000
                                                                            )
                                                                            + (
                                                                                1
                                                                                if (
                                                                                    (
                                                                                        s.index_price_e8
                                                                                        * s.max_oracle_move_bps
                                                                                    )
                                                                                    % 10000
                                                                                )
                                                                                < 0
                                                                                else 0
                                                                            )
                                                                        )
                                                                    )
                                                                    + s.index_price_e8
                                                                )
                                                                if (
                                                                    s.clearing_price_e8
                                                                    >= s.index_price_e8
                                                                )
                                                                else (
                                                                    s.index_price_e8
                                                                    - (
                                                                        0
                                                                        if 10000 == 0
                                                                        else (
                                                                            (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                // 10000
                                                                            )
                                                                            + (
                                                                                1
                                                                                if (
                                                                                    (
                                                                                        s.index_price_e8
                                                                                        * s.max_oracle_move_bps
                                                                                    )
                                                                                    % 10000
                                                                                )
                                                                                < 0
                                                                                else 0
                                                                            )
                                                                        )
                                                                    )
                                                                )
                                                            )
                                                            if (
                                                                (
                                                                    (
                                                                        10000
                                                                        * (
                                                                            (
                                                                                s.clearing_price_e8
                                                                                - s.index_price_e8
                                                                            )
                                                                            if (
                                                                                s.clearing_price_e8
                                                                                >= s.index_price_e8
                                                                            )
                                                                            else (
                                                                                s.index_price_e8
                                                                                - s.clearing_price_e8
                                                                            )
                                                                        )
                                                                    )
                                                                    > (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                )
                                                                and s.oracle_seen
                                                            )
                                                            else s.clearing_price_e8
                                                        )
                                                    )
                                                    * s.liquidation_penalty_bps
                                                )
                                            )
                                            % 10000
                                        )
                                        < 0
                                        else 0
                                    )
                                )
                            )
                            <= (
                                (
                                    (
                                        (
                                            (
                                                (
                                                    (
                                                        0
                                                        if 10000 == 0
                                                        else (
                                                            (
                                                                (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                                // 10000
                                                            )
                                                            + (
                                                                1
                                                                if (
                                                                    (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                    % 10000
                                                                )
                                                                < 0
                                                                else 0
                                                            )
                                                        )
                                                    )
                                                    + s.index_price_e8
                                                )
                                                if (
                                                    s.clearing_price_e8
                                                    >= s.index_price_e8
                                                )
                                                else (
                                                    s.index_price_e8
                                                    - (
                                                        0
                                                        if 10000 == 0
                                                        else (
                                                            (
                                                                (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                                // 10000
                                                            )
                                                            + (
                                                                1
                                                                if (
                                                                    (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                    % 10000
                                                                )
                                                                < 0
                                                                else 0
                                                            )
                                                        )
                                                    )
                                                )
                                            )
                                            if (
                                                (
                                                    (
                                                        10000
                                                        * (
                                                            (
                                                                s.clearing_price_e8
                                                                - s.index_price_e8
                                                            )
                                                            if (
                                                                s.clearing_price_e8
                                                                >= s.index_price_e8
                                                            )
                                                            else (
                                                                s.index_price_e8
                                                                - s.clearing_price_e8
                                                            )
                                                        )
                                                    )
                                                    > (
                                                        s.index_price_e8
                                                        * s.max_oracle_move_bps
                                                    )
                                                )
                                                and s.oracle_seen
                                            )
                                            else s.clearing_price_e8
                                        )
                                        - s.index_price_e8
                                    )
                                    * s.position_base_b
                                )
                                + s.collateral_e8_b
                            )
                        )
                        else (
                            (
                                (
                                    (
                                        (
                                            (
                                                (
                                                    0
                                                    if 10000 == 0
                                                    else (
                                                        (
                                                            (
                                                                s.index_price_e8
                                                                * s.max_oracle_move_bps
                                                            )
                                                            // 10000
                                                        )
                                                        + (
                                                            1
                                                            if (
                                                                (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                                % 10000
                                                            )
                                                            < 0
                                                            else 0
                                                        )
                                                    )
                                                )
                                                + s.index_price_e8
                                            )
                                            if (s.clearing_price_e8 >= s.index_price_e8)
                                            else (
                                                s.index_price_e8
                                                - (
                                                    0
                                                    if 10000 == 0
                                                    else (
                                                        (
                                                            (
                                                                s.index_price_e8
                                                                * s.max_oracle_move_bps
                                                            )
                                                            // 10000
                                                        )
                                                        + (
                                                            1
                                                            if (
                                                                (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                                % 10000
                                                            )
                                                            < 0
                                                            else 0
                                                        )
                                                    )
                                                )
                                            )
                                        )
                                        if (
                                            (
                                                (
                                                    10000
                                                    * (
                                                        (
                                                            s.clearing_price_e8
                                                            - s.index_price_e8
                                                        )
                                                        if (
                                                            s.clearing_price_e8
                                                            >= s.index_price_e8
                                                        )
                                                        else (
                                                            s.index_price_e8
                                                            - s.clearing_price_e8
                                                        )
                                                    )
                                                )
                                                > (
                                                    s.index_price_e8
                                                    * s.max_oracle_move_bps
                                                )
                                            )
                                            and s.oracle_seen
                                        )
                                        else s.clearing_price_e8
                                    )
                                    - s.index_price_e8
                                )
                                * s.position_base_b
                            )
                            + s.collateral_e8_b
                        )
                    )
                    if (
                        (
                            (
                                (
                                    (
                                        (
                                            (
                                                (
                                                    (
                                                        0
                                                        if 10000 == 0
                                                        else (
                                                            (
                                                                (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                                // 10000
                                                            )
                                                            + (
                                                                1
                                                                if (
                                                                    (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                    % 10000
                                                                )
                                                                < 0
                                                                else 0
                                                            )
                                                        )
                                                    )
                                                    + s.index_price_e8
                                                )
                                                if (
                                                    s.clearing_price_e8
                                                    >= s.index_price_e8
                                                )
                                                else (
                                                    s.index_price_e8
                                                    - (
                                                        0
                                                        if 10000 == 0
                                                        else (
                                                            (
                                                                (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                                // 10000
                                                            )
                                                            + (
                                                                1
                                                                if (
                                                                    (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                    % 10000
                                                                )
                                                                < 0
                                                                else 0
                                                            )
                                                        )
                                                    )
                                                )
                                            )
                                            if (
                                                (
                                                    (
                                                        10000
                                                        * (
                                                            (
                                                                s.clearing_price_e8
                                                                - s.index_price_e8
                                                            )
                                                            if (
                                                                s.clearing_price_e8
                                                                >= s.index_price_e8
                                                            )
                                                            else (
                                                                s.index_price_e8
                                                                - s.clearing_price_e8
                                                            )
                                                        )
                                                    )
                                                    > (
                                                        s.index_price_e8
                                                        * s.max_oracle_move_bps
                                                    )
                                                )
                                                and s.oracle_seen
                                            )
                                            else s.clearing_price_e8
                                        )
                                        - s.index_price_e8
                                    )
                                    * s.position_base_b
                                )
                                + s.collateral_e8_b
                            )
                            < (
                                0
                                if 10000 == 0
                                else (
                                    (
                                        (
                                            9999
                                            + (
                                                (
                                                    (
                                                        s.position_base_b
                                                        if (s.position_base_b >= 0)
                                                        else (0 - s.position_base_b)
                                                    )
                                                    * (
                                                        (
                                                            (
                                                                (
                                                                    0
                                                                    if 10000 == 0
                                                                    else (
                                                                        (
                                                                            (
                                                                                s.index_price_e8
                                                                                * s.max_oracle_move_bps
                                                                            )
                                                                            // 10000
                                                                        )
                                                                        + (
                                                                            1
                                                                            if (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                % 10000
                                                                            )
                                                                            < 0
                                                                            else 0
                                                                        )
                                                                    )
                                                                )
                                                                + s.index_price_e8
                                                            )
                                                            if (
                                                                s.clearing_price_e8
                                                                >= s.index_price_e8
                                                            )
                                                            else (
                                                                s.index_price_e8
                                                                - (
                                                                    0
                                                                    if 10000 == 0
                                                                    else (
                                                                        (
                                                                            (
                                                                                s.index_price_e8
                                                                                * s.max_oracle_move_bps
                                                                            )
                                                                            // 10000
                                                                        )
                                                                        + (
                                                                            1
                                                                            if (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                % 10000
                                                                            )
                                                                            < 0
                                                                            else 0
                                                                        )
                                                                    )
                                                                )
                                                            )
                                                        )
                                                        if (
                                                            (
                                                                (
                                                                    10000
                                                                    * (
                                                                        (
                                                                            s.clearing_price_e8
                                                                            - s.index_price_e8
                                                                        )
                                                                        if (
                                                                            s.clearing_price_e8
                                                                            >= s.index_price_e8
                                                                        )
                                                                        else (
                                                                            s.index_price_e8
                                                                            - s.clearing_price_e8
                                                                        )
                                                                    )
                                                                )
                                                                > (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                            )
                                                            and s.oracle_seen
                                                        )
                                                        else s.clearing_price_e8
                                                    )
                                                )
                                                * s.maintenance_margin_bps
                                            )
                                        )
                                        // 10000
                                    )
                                    + (
                                        1
                                        if (
                                            (
                                                9999
                                                + (
                                                    (
                                                        (
                                                            s.position_base_b
                                                            if (s.position_base_b >= 0)
                                                            else (0 - s.position_base_b)
                                                        )
                                                        * (
                                                            (
                                                                (
                                                                    (
                                                                        0
                                                                        if 10000 == 0
                                                                        else (
                                                                            (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                // 10000
                                                                            )
                                                                            + (
                                                                                1
                                                                                if (
                                                                                    (
                                                                                        s.index_price_e8
                                                                                        * s.max_oracle_move_bps
                                                                                    )
                                                                                    % 10000
                                                                                )
                                                                                < 0
                                                                                else 0
                                                                            )
                                                                        )
                                                                    )
                                                                    + s.index_price_e8
                                                                )
                                                                if (
                                                                    s.clearing_price_e8
                                                                    >= s.index_price_e8
                                                                )
                                                                else (
                                                                    s.index_price_e8
                                                                    - (
                                                                        0
                                                                        if 10000 == 0
                                                                        else (
                                                                            (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                // 10000
                                                                            )
                                                                            + (
                                                                                1
                                                                                if (
                                                                                    (
                                                                                        s.index_price_e8
                                                                                        * s.max_oracle_move_bps
                                                                                    )
                                                                                    % 10000
                                                                                )
                                                                                < 0
                                                                                else 0
                                                                            )
                                                                        )
                                                                    )
                                                                )
                                                            )
                                                            if (
                                                                (
                                                                    (
                                                                        10000
                                                                        * (
                                                                            (
                                                                                s.clearing_price_e8
                                                                                - s.index_price_e8
                                                                            )
                                                                            if (
                                                                                s.clearing_price_e8
                                                                                >= s.index_price_e8
                                                                            )
                                                                            else (
                                                                                s.index_price_e8
                                                                                - s.clearing_price_e8
                                                                            )
                                                                        )
                                                                    )
                                                                    > (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                )
                                                                and s.oracle_seen
                                                            )
                                                            else s.clearing_price_e8
                                                        )
                                                    )
                                                    * s.maintenance_margin_bps
                                                )
                                            )
                                            % 10000
                                        )
                                        < 0
                                        else 0
                                    )
                                )
                            )
                        )
                        and (not (0 == s.position_base_b))
                    )
                    else 0
                )
            ),
            entry_price_e8_a=(
                0
                if (
                    (
                        (
                            (
                                (
                                    (
                                        (
                                            (
                                                (
                                                    (
                                                        0
                                                        if 10000 == 0
                                                        else (
                                                            (
                                                                (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                                // 10000
                                                            )
                                                            + (
                                                                1
                                                                if (
                                                                    (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                    % 10000
                                                                )
                                                                < 0
                                                                else 0
                                                            )
                                                        )
                                                    )
                                                    + s.index_price_e8
                                                )
                                                if (
                                                    s.clearing_price_e8
                                                    >= s.index_price_e8
                                                )
                                                else (
                                                    s.index_price_e8
                                                    - (
                                                        0
                                                        if 10000 == 0
                                                        else (
                                                            (
                                                                (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                                // 10000
                                                            )
                                                            + (
                                                                1
                                                                if (
                                                                    (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                    % 10000
                                                                )
                                                                < 0
                                                                else 0
                                                            )
                                                        )
                                                    )
                                                )
                                            )
                                            if (
                                                (
                                                    (
                                                        10000
                                                        * (
                                                            (
                                                                s.clearing_price_e8
                                                                - s.index_price_e8
                                                            )
                                                            if (
                                                                s.clearing_price_e8
                                                                >= s.index_price_e8
                                                            )
                                                            else (
                                                                s.index_price_e8
                                                                - s.clearing_price_e8
                                                            )
                                                        )
                                                    )
                                                    > (
                                                        s.index_price_e8
                                                        * s.max_oracle_move_bps
                                                    )
                                                )
                                                and s.oracle_seen
                                            )
                                            else s.clearing_price_e8
                                        )
                                        - s.index_price_e8
                                    )
                                    * s.position_base_a
                                )
                                + s.collateral_e8_a
                            )
                            < (
                                0
                                if 10000 == 0
                                else (
                                    (
                                        (
                                            9999
                                            + (
                                                (
                                                    (
                                                        s.position_base_a
                                                        if (s.position_base_a >= 0)
                                                        else (0 - s.position_base_a)
                                                    )
                                                    * (
                                                        (
                                                            (
                                                                (
                                                                    0
                                                                    if 10000 == 0
                                                                    else (
                                                                        (
                                                                            (
                                                                                s.index_price_e8
                                                                                * s.max_oracle_move_bps
                                                                            )
                                                                            // 10000
                                                                        )
                                                                        + (
                                                                            1
                                                                            if (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                % 10000
                                                                            )
                                                                            < 0
                                                                            else 0
                                                                        )
                                                                    )
                                                                )
                                                                + s.index_price_e8
                                                            )
                                                            if (
                                                                s.clearing_price_e8
                                                                >= s.index_price_e8
                                                            )
                                                            else (
                                                                s.index_price_e8
                                                                - (
                                                                    0
                                                                    if 10000 == 0
                                                                    else (
                                                                        (
                                                                            (
                                                                                s.index_price_e8
                                                                                * s.max_oracle_move_bps
                                                                            )
                                                                            // 10000
                                                                        )
                                                                        + (
                                                                            1
                                                                            if (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                % 10000
                                                                            )
                                                                            < 0
                                                                            else 0
                                                                        )
                                                                    )
                                                                )
                                                            )
                                                        )
                                                        if (
                                                            (
                                                                (
                                                                    10000
                                                                    * (
                                                                        (
                                                                            s.clearing_price_e8
                                                                            - s.index_price_e8
                                                                        )
                                                                        if (
                                                                            s.clearing_price_e8
                                                                            >= s.index_price_e8
                                                                        )
                                                                        else (
                                                                            s.index_price_e8
                                                                            - s.clearing_price_e8
                                                                        )
                                                                    )
                                                                )
                                                                > (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                            )
                                                            and s.oracle_seen
                                                        )
                                                        else s.clearing_price_e8
                                                    )
                                                )
                                                * s.maintenance_margin_bps
                                            )
                                        )
                                        // 10000
                                    )
                                    + (
                                        1
                                        if (
                                            (
                                                9999
                                                + (
                                                    (
                                                        (
                                                            s.position_base_a
                                                            if (s.position_base_a >= 0)
                                                            else (0 - s.position_base_a)
                                                        )
                                                        * (
                                                            (
                                                                (
                                                                    (
                                                                        0
                                                                        if 10000 == 0
                                                                        else (
                                                                            (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                // 10000
                                                                            )
                                                                            + (
                                                                                1
                                                                                if (
                                                                                    (
                                                                                        s.index_price_e8
                                                                                        * s.max_oracle_move_bps
                                                                                    )
                                                                                    % 10000
                                                                                )
                                                                                < 0
                                                                                else 0
                                                                            )
                                                                        )
                                                                    )
                                                                    + s.index_price_e8
                                                                )
                                                                if (
                                                                    s.clearing_price_e8
                                                                    >= s.index_price_e8
                                                                )
                                                                else (
                                                                    s.index_price_e8
                                                                    - (
                                                                        0
                                                                        if 10000 == 0
                                                                        else (
                                                                            (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                // 10000
                                                                            )
                                                                            + (
                                                                                1
                                                                                if (
                                                                                    (
                                                                                        s.index_price_e8
                                                                                        * s.max_oracle_move_bps
                                                                                    )
                                                                                    % 10000
                                                                                )
                                                                                < 0
                                                                                else 0
                                                                            )
                                                                        )
                                                                    )
                                                                )
                                                            )
                                                            if (
                                                                (
                                                                    (
                                                                        10000
                                                                        * (
                                                                            (
                                                                                s.clearing_price_e8
                                                                                - s.index_price_e8
                                                                            )
                                                                            if (
                                                                                s.clearing_price_e8
                                                                                >= s.index_price_e8
                                                                            )
                                                                            else (
                                                                                s.index_price_e8
                                                                                - s.clearing_price_e8
                                                                            )
                                                                        )
                                                                    )
                                                                    > (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                )
                                                                and s.oracle_seen
                                                            )
                                                            else s.clearing_price_e8
                                                        )
                                                    )
                                                    * s.maintenance_margin_bps
                                                )
                                            )
                                            % 10000
                                        )
                                        < 0
                                        else 0
                                    )
                                )
                            )
                        )
                        and (not (0 == s.position_base_a))
                    )
                    or (
                        (
                            (
                                (
                                    (
                                        (
                                            (
                                                (
                                                    (
                                                        0
                                                        if 10000 == 0
                                                        else (
                                                            (
                                                                (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                                // 10000
                                                            )
                                                            + (
                                                                1
                                                                if (
                                                                    (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                    % 10000
                                                                )
                                                                < 0
                                                                else 0
                                                            )
                                                        )
                                                    )
                                                    + s.index_price_e8
                                                )
                                                if (
                                                    s.clearing_price_e8
                                                    >= s.index_price_e8
                                                )
                                                else (
                                                    s.index_price_e8
                                                    - (
                                                        0
                                                        if 10000 == 0
                                                        else (
                                                            (
                                                                (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                                // 10000
                                                            )
                                                            + (
                                                                1
                                                                if (
                                                                    (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                    % 10000
                                                                )
                                                                < 0
                                                                else 0
                                                            )
                                                        )
                                                    )
                                                )
                                            )
                                            if (
                                                (
                                                    (
                                                        10000
                                                        * (
                                                            (
                                                                s.clearing_price_e8
                                                                - s.index_price_e8
                                                            )
                                                            if (
                                                                s.clearing_price_e8
                                                                >= s.index_price_e8
                                                            )
                                                            else (
                                                                s.index_price_e8
                                                                - s.clearing_price_e8
                                                            )
                                                        )
                                                    )
                                                    > (
                                                        s.index_price_e8
                                                        * s.max_oracle_move_bps
                                                    )
                                                )
                                                and s.oracle_seen
                                            )
                                            else s.clearing_price_e8
                                        )
                                        - s.index_price_e8
                                    )
                                    * s.position_base_b
                                )
                                + s.collateral_e8_b
                            )
                            < (
                                0
                                if 10000 == 0
                                else (
                                    (
                                        (
                                            9999
                                            + (
                                                (
                                                    (
                                                        s.position_base_b
                                                        if (s.position_base_b >= 0)
                                                        else (0 - s.position_base_b)
                                                    )
                                                    * (
                                                        (
                                                            (
                                                                (
                                                                    0
                                                                    if 10000 == 0
                                                                    else (
                                                                        (
                                                                            (
                                                                                s.index_price_e8
                                                                                * s.max_oracle_move_bps
                                                                            )
                                                                            // 10000
                                                                        )
                                                                        + (
                                                                            1
                                                                            if (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                % 10000
                                                                            )
                                                                            < 0
                                                                            else 0
                                                                        )
                                                                    )
                                                                )
                                                                + s.index_price_e8
                                                            )
                                                            if (
                                                                s.clearing_price_e8
                                                                >= s.index_price_e8
                                                            )
                                                            else (
                                                                s.index_price_e8
                                                                - (
                                                                    0
                                                                    if 10000 == 0
                                                                    else (
                                                                        (
                                                                            (
                                                                                s.index_price_e8
                                                                                * s.max_oracle_move_bps
                                                                            )
                                                                            // 10000
                                                                        )
                                                                        + (
                                                                            1
                                                                            if (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                % 10000
                                                                            )
                                                                            < 0
                                                                            else 0
                                                                        )
                                                                    )
                                                                )
                                                            )
                                                        )
                                                        if (
                                                            (
                                                                (
                                                                    10000
                                                                    * (
                                                                        (
                                                                            s.clearing_price_e8
                                                                            - s.index_price_e8
                                                                        )
                                                                        if (
                                                                            s.clearing_price_e8
                                                                            >= s.index_price_e8
                                                                        )
                                                                        else (
                                                                            s.index_price_e8
                                                                            - s.clearing_price_e8
                                                                        )
                                                                    )
                                                                )
                                                                > (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                            )
                                                            and s.oracle_seen
                                                        )
                                                        else s.clearing_price_e8
                                                    )
                                                )
                                                * s.maintenance_margin_bps
                                            )
                                        )
                                        // 10000
                                    )
                                    + (
                                        1
                                        if (
                                            (
                                                9999
                                                + (
                                                    (
                                                        (
                                                            s.position_base_b
                                                            if (s.position_base_b >= 0)
                                                            else (0 - s.position_base_b)
                                                        )
                                                        * (
                                                            (
                                                                (
                                                                    (
                                                                        0
                                                                        if 10000 == 0
                                                                        else (
                                                                            (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                // 10000
                                                                            )
                                                                            + (
                                                                                1
                                                                                if (
                                                                                    (
                                                                                        s.index_price_e8
                                                                                        * s.max_oracle_move_bps
                                                                                    )
                                                                                    % 10000
                                                                                )
                                                                                < 0
                                                                                else 0
                                                                            )
                                                                        )
                                                                    )
                                                                    + s.index_price_e8
                                                                )
                                                                if (
                                                                    s.clearing_price_e8
                                                                    >= s.index_price_e8
                                                                )
                                                                else (
                                                                    s.index_price_e8
                                                                    - (
                                                                        0
                                                                        if 10000 == 0
                                                                        else (
                                                                            (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                // 10000
                                                                            )
                                                                            + (
                                                                                1
                                                                                if (
                                                                                    (
                                                                                        s.index_price_e8
                                                                                        * s.max_oracle_move_bps
                                                                                    )
                                                                                    % 10000
                                                                                )
                                                                                < 0
                                                                                else 0
                                                                            )
                                                                        )
                                                                    )
                                                                )
                                                            )
                                                            if (
                                                                (
                                                                    (
                                                                        10000
                                                                        * (
                                                                            (
                                                                                s.clearing_price_e8
                                                                                - s.index_price_e8
                                                                            )
                                                                            if (
                                                                                s.clearing_price_e8
                                                                                >= s.index_price_e8
                                                                            )
                                                                            else (
                                                                                s.index_price_e8
                                                                                - s.clearing_price_e8
                                                                            )
                                                                        )
                                                                    )
                                                                    > (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                )
                                                                and s.oracle_seen
                                                            )
                                                            else s.clearing_price_e8
                                                        )
                                                    )
                                                    * s.maintenance_margin_bps
                                                )
                                            )
                                            % 10000
                                        )
                                        < 0
                                        else 0
                                    )
                                )
                            )
                        )
                        and (not (0 == s.position_base_b))
                    )
                )
                else (
                    0
                    if (0 == s.position_base_a)
                    else (
                        (
                            (
                                (
                                    0
                                    if 10000 == 0
                                    else (
                                        (
                                            (s.index_price_e8 * s.max_oracle_move_bps)
                                            // 10000
                                        )
                                        + (
                                            1
                                            if (
                                                (
                                                    s.index_price_e8
                                                    * s.max_oracle_move_bps
                                                )
                                                % 10000
                                            )
                                            < 0
                                            else 0
                                        )
                                    )
                                )
                                + s.index_price_e8
                            )
                            if (s.clearing_price_e8 >= s.index_price_e8)
                            else (
                                s.index_price_e8
                                - (
                                    0
                                    if 10000 == 0
                                    else (
                                        (
                                            (s.index_price_e8 * s.max_oracle_move_bps)
                                            // 10000
                                        )
                                        + (
                                            1
                                            if (
                                                (
                                                    s.index_price_e8
                                                    * s.max_oracle_move_bps
                                                )
                                                % 10000
                                            )
                                            < 0
                                            else 0
                                        )
                                    )
                                )
                            )
                        )
                        if (
                            (
                                (
                                    10000
                                    * (
                                        (s.clearing_price_e8 - s.index_price_e8)
                                        if (s.clearing_price_e8 >= s.index_price_e8)
                                        else (s.index_price_e8 - s.clearing_price_e8)
                                    )
                                )
                                > (s.index_price_e8 * s.max_oracle_move_bps)
                            )
                            and s.oracle_seen
                        )
                        else s.clearing_price_e8
                    )
                )
            ),
            entry_price_e8_b=(
                0
                if (
                    (
                        (
                            (
                                (
                                    (
                                        (
                                            (
                                                (
                                                    (
                                                        0
                                                        if 10000 == 0
                                                        else (
                                                            (
                                                                (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                                // 10000
                                                            )
                                                            + (
                                                                1
                                                                if (
                                                                    (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                    % 10000
                                                                )
                                                                < 0
                                                                else 0
                                                            )
                                                        )
                                                    )
                                                    + s.index_price_e8
                                                )
                                                if (
                                                    s.clearing_price_e8
                                                    >= s.index_price_e8
                                                )
                                                else (
                                                    s.index_price_e8
                                                    - (
                                                        0
                                                        if 10000 == 0
                                                        else (
                                                            (
                                                                (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                                // 10000
                                                            )
                                                            + (
                                                                1
                                                                if (
                                                                    (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                    % 10000
                                                                )
                                                                < 0
                                                                else 0
                                                            )
                                                        )
                                                    )
                                                )
                                            )
                                            if (
                                                (
                                                    (
                                                        10000
                                                        * (
                                                            (
                                                                s.clearing_price_e8
                                                                - s.index_price_e8
                                                            )
                                                            if (
                                                                s.clearing_price_e8
                                                                >= s.index_price_e8
                                                            )
                                                            else (
                                                                s.index_price_e8
                                                                - s.clearing_price_e8
                                                            )
                                                        )
                                                    )
                                                    > (
                                                        s.index_price_e8
                                                        * s.max_oracle_move_bps
                                                    )
                                                )
                                                and s.oracle_seen
                                            )
                                            else s.clearing_price_e8
                                        )
                                        - s.index_price_e8
                                    )
                                    * s.position_base_a
                                )
                                + s.collateral_e8_a
                            )
                            < (
                                0
                                if 10000 == 0
                                else (
                                    (
                                        (
                                            9999
                                            + (
                                                (
                                                    (
                                                        s.position_base_a
                                                        if (s.position_base_a >= 0)
                                                        else (0 - s.position_base_a)
                                                    )
                                                    * (
                                                        (
                                                            (
                                                                (
                                                                    0
                                                                    if 10000 == 0
                                                                    else (
                                                                        (
                                                                            (
                                                                                s.index_price_e8
                                                                                * s.max_oracle_move_bps
                                                                            )
                                                                            // 10000
                                                                        )
                                                                        + (
                                                                            1
                                                                            if (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                % 10000
                                                                            )
                                                                            < 0
                                                                            else 0
                                                                        )
                                                                    )
                                                                )
                                                                + s.index_price_e8
                                                            )
                                                            if (
                                                                s.clearing_price_e8
                                                                >= s.index_price_e8
                                                            )
                                                            else (
                                                                s.index_price_e8
                                                                - (
                                                                    0
                                                                    if 10000 == 0
                                                                    else (
                                                                        (
                                                                            (
                                                                                s.index_price_e8
                                                                                * s.max_oracle_move_bps
                                                                            )
                                                                            // 10000
                                                                        )
                                                                        + (
                                                                            1
                                                                            if (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                % 10000
                                                                            )
                                                                            < 0
                                                                            else 0
                                                                        )
                                                                    )
                                                                )
                                                            )
                                                        )
                                                        if (
                                                            (
                                                                (
                                                                    10000
                                                                    * (
                                                                        (
                                                                            s.clearing_price_e8
                                                                            - s.index_price_e8
                                                                        )
                                                                        if (
                                                                            s.clearing_price_e8
                                                                            >= s.index_price_e8
                                                                        )
                                                                        else (
                                                                            s.index_price_e8
                                                                            - s.clearing_price_e8
                                                                        )
                                                                    )
                                                                )
                                                                > (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                            )
                                                            and s.oracle_seen
                                                        )
                                                        else s.clearing_price_e8
                                                    )
                                                )
                                                * s.maintenance_margin_bps
                                            )
                                        )
                                        // 10000
                                    )
                                    + (
                                        1
                                        if (
                                            (
                                                9999
                                                + (
                                                    (
                                                        (
                                                            s.position_base_a
                                                            if (s.position_base_a >= 0)
                                                            else (0 - s.position_base_a)
                                                        )
                                                        * (
                                                            (
                                                                (
                                                                    (
                                                                        0
                                                                        if 10000 == 0
                                                                        else (
                                                                            (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                // 10000
                                                                            )
                                                                            + (
                                                                                1
                                                                                if (
                                                                                    (
                                                                                        s.index_price_e8
                                                                                        * s.max_oracle_move_bps
                                                                                    )
                                                                                    % 10000
                                                                                )
                                                                                < 0
                                                                                else 0
                                                                            )
                                                                        )
                                                                    )
                                                                    + s.index_price_e8
                                                                )
                                                                if (
                                                                    s.clearing_price_e8
                                                                    >= s.index_price_e8
                                                                )
                                                                else (
                                                                    s.index_price_e8
                                                                    - (
                                                                        0
                                                                        if 10000 == 0
                                                                        else (
                                                                            (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                // 10000
                                                                            )
                                                                            + (
                                                                                1
                                                                                if (
                                                                                    (
                                                                                        s.index_price_e8
                                                                                        * s.max_oracle_move_bps
                                                                                    )
                                                                                    % 10000
                                                                                )
                                                                                < 0
                                                                                else 0
                                                                            )
                                                                        )
                                                                    )
                                                                )
                                                            )
                                                            if (
                                                                (
                                                                    (
                                                                        10000
                                                                        * (
                                                                            (
                                                                                s.clearing_price_e8
                                                                                - s.index_price_e8
                                                                            )
                                                                            if (
                                                                                s.clearing_price_e8
                                                                                >= s.index_price_e8
                                                                            )
                                                                            else (
                                                                                s.index_price_e8
                                                                                - s.clearing_price_e8
                                                                            )
                                                                        )
                                                                    )
                                                                    > (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                )
                                                                and s.oracle_seen
                                                            )
                                                            else s.clearing_price_e8
                                                        )
                                                    )
                                                    * s.maintenance_margin_bps
                                                )
                                            )
                                            % 10000
                                        )
                                        < 0
                                        else 0
                                    )
                                )
                            )
                        )
                        and (not (0 == s.position_base_a))
                    )
                    or (
                        (
                            (
                                (
                                    (
                                        (
                                            (
                                                (
                                                    (
                                                        0
                                                        if 10000 == 0
                                                        else (
                                                            (
                                                                (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                                // 10000
                                                            )
                                                            + (
                                                                1
                                                                if (
                                                                    (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                    % 10000
                                                                )
                                                                < 0
                                                                else 0
                                                            )
                                                        )
                                                    )
                                                    + s.index_price_e8
                                                )
                                                if (
                                                    s.clearing_price_e8
                                                    >= s.index_price_e8
                                                )
                                                else (
                                                    s.index_price_e8
                                                    - (
                                                        0
                                                        if 10000 == 0
                                                        else (
                                                            (
                                                                (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                                // 10000
                                                            )
                                                            + (
                                                                1
                                                                if (
                                                                    (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                    % 10000
                                                                )
                                                                < 0
                                                                else 0
                                                            )
                                                        )
                                                    )
                                                )
                                            )
                                            if (
                                                (
                                                    (
                                                        10000
                                                        * (
                                                            (
                                                                s.clearing_price_e8
                                                                - s.index_price_e8
                                                            )
                                                            if (
                                                                s.clearing_price_e8
                                                                >= s.index_price_e8
                                                            )
                                                            else (
                                                                s.index_price_e8
                                                                - s.clearing_price_e8
                                                            )
                                                        )
                                                    )
                                                    > (
                                                        s.index_price_e8
                                                        * s.max_oracle_move_bps
                                                    )
                                                )
                                                and s.oracle_seen
                                            )
                                            else s.clearing_price_e8
                                        )
                                        - s.index_price_e8
                                    )
                                    * s.position_base_b
                                )
                                + s.collateral_e8_b
                            )
                            < (
                                0
                                if 10000 == 0
                                else (
                                    (
                                        (
                                            9999
                                            + (
                                                (
                                                    (
                                                        s.position_base_b
                                                        if (s.position_base_b >= 0)
                                                        else (0 - s.position_base_b)
                                                    )
                                                    * (
                                                        (
                                                            (
                                                                (
                                                                    0
                                                                    if 10000 == 0
                                                                    else (
                                                                        (
                                                                            (
                                                                                s.index_price_e8
                                                                                * s.max_oracle_move_bps
                                                                            )
                                                                            // 10000
                                                                        )
                                                                        + (
                                                                            1
                                                                            if (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                % 10000
                                                                            )
                                                                            < 0
                                                                            else 0
                                                                        )
                                                                    )
                                                                )
                                                                + s.index_price_e8
                                                            )
                                                            if (
                                                                s.clearing_price_e8
                                                                >= s.index_price_e8
                                                            )
                                                            else (
                                                                s.index_price_e8
                                                                - (
                                                                    0
                                                                    if 10000 == 0
                                                                    else (
                                                                        (
                                                                            (
                                                                                s.index_price_e8
                                                                                * s.max_oracle_move_bps
                                                                            )
                                                                            // 10000
                                                                        )
                                                                        + (
                                                                            1
                                                                            if (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                % 10000
                                                                            )
                                                                            < 0
                                                                            else 0
                                                                        )
                                                                    )
                                                                )
                                                            )
                                                        )
                                                        if (
                                                            (
                                                                (
                                                                    10000
                                                                    * (
                                                                        (
                                                                            s.clearing_price_e8
                                                                            - s.index_price_e8
                                                                        )
                                                                        if (
                                                                            s.clearing_price_e8
                                                                            >= s.index_price_e8
                                                                        )
                                                                        else (
                                                                            s.index_price_e8
                                                                            - s.clearing_price_e8
                                                                        )
                                                                    )
                                                                )
                                                                > (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                            )
                                                            and s.oracle_seen
                                                        )
                                                        else s.clearing_price_e8
                                                    )
                                                )
                                                * s.maintenance_margin_bps
                                            )
                                        )
                                        // 10000
                                    )
                                    + (
                                        1
                                        if (
                                            (
                                                9999
                                                + (
                                                    (
                                                        (
                                                            s.position_base_b
                                                            if (s.position_base_b >= 0)
                                                            else (0 - s.position_base_b)
                                                        )
                                                        * (
                                                            (
                                                                (
                                                                    (
                                                                        0
                                                                        if 10000 == 0
                                                                        else (
                                                                            (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                // 10000
                                                                            )
                                                                            + (
                                                                                1
                                                                                if (
                                                                                    (
                                                                                        s.index_price_e8
                                                                                        * s.max_oracle_move_bps
                                                                                    )
                                                                                    % 10000
                                                                                )
                                                                                < 0
                                                                                else 0
                                                                            )
                                                                        )
                                                                    )
                                                                    + s.index_price_e8
                                                                )
                                                                if (
                                                                    s.clearing_price_e8
                                                                    >= s.index_price_e8
                                                                )
                                                                else (
                                                                    s.index_price_e8
                                                                    - (
                                                                        0
                                                                        if 10000 == 0
                                                                        else (
                                                                            (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                // 10000
                                                                            )
                                                                            + (
                                                                                1
                                                                                if (
                                                                                    (
                                                                                        s.index_price_e8
                                                                                        * s.max_oracle_move_bps
                                                                                    )
                                                                                    % 10000
                                                                                )
                                                                                < 0
                                                                                else 0
                                                                            )
                                                                        )
                                                                    )
                                                                )
                                                            )
                                                            if (
                                                                (
                                                                    (
                                                                        10000
                                                                        * (
                                                                            (
                                                                                s.clearing_price_e8
                                                                                - s.index_price_e8
                                                                            )
                                                                            if (
                                                                                s.clearing_price_e8
                                                                                >= s.index_price_e8
                                                                            )
                                                                            else (
                                                                                s.index_price_e8
                                                                                - s.clearing_price_e8
                                                                            )
                                                                        )
                                                                    )
                                                                    > (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                )
                                                                and s.oracle_seen
                                                            )
                                                            else s.clearing_price_e8
                                                        )
                                                    )
                                                    * s.maintenance_margin_bps
                                                )
                                            )
                                            % 10000
                                        )
                                        < 0
                                        else 0
                                    )
                                )
                            )
                        )
                        and (not (0 == s.position_base_b))
                    )
                )
                else (
                    0
                    if (0 == s.position_base_b)
                    else (
                        (
                            (
                                (
                                    0
                                    if 10000 == 0
                                    else (
                                        (
                                            (s.index_price_e8 * s.max_oracle_move_bps)
                                            // 10000
                                        )
                                        + (
                                            1
                                            if (
                                                (
                                                    s.index_price_e8
                                                    * s.max_oracle_move_bps
                                                )
                                                % 10000
                                            )
                                            < 0
                                            else 0
                                        )
                                    )
                                )
                                + s.index_price_e8
                            )
                            if (s.clearing_price_e8 >= s.index_price_e8)
                            else (
                                s.index_price_e8
                                - (
                                    0
                                    if 10000 == 0
                                    else (
                                        (
                                            (s.index_price_e8 * s.max_oracle_move_bps)
                                            // 10000
                                        )
                                        + (
                                            1
                                            if (
                                                (
                                                    s.index_price_e8
                                                    * s.max_oracle_move_bps
                                                )
                                                % 10000
                                            )
                                            < 0
                                            else 0
                                        )
                                    )
                                )
                            )
                        )
                        if (
                            (
                                (
                                    10000
                                    * (
                                        (s.clearing_price_e8 - s.index_price_e8)
                                        if (s.clearing_price_e8 >= s.index_price_e8)
                                        else (s.index_price_e8 - s.clearing_price_e8)
                                    )
                                )
                                > (s.index_price_e8 * s.max_oracle_move_bps)
                            )
                            and s.oracle_seen
                        )
                        else s.clearing_price_e8
                    )
                )
            ),
            fee_pool_e8=(
                (
                    (
                        (
                            (
                                0
                                if 10000 == 0
                                else (
                                    (
                                        (
                                            9999
                                            + (
                                                (
                                                    (
                                                        s.position_base_a
                                                        if (s.position_base_a >= 0)
                                                        else (0 - s.position_base_a)
                                                    )
                                                    * (
                                                        (
                                                            (
                                                                (
                                                                    0
                                                                    if 10000 == 0
                                                                    else (
                                                                        (
                                                                            (
                                                                                s.index_price_e8
                                                                                * s.max_oracle_move_bps
                                                                            )
                                                                            // 10000
                                                                        )
                                                                        + (
                                                                            1
                                                                            if (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                % 10000
                                                                            )
                                                                            < 0
                                                                            else 0
                                                                        )
                                                                    )
                                                                )
                                                                + s.index_price_e8
                                                            )
                                                            if (
                                                                s.clearing_price_e8
                                                                >= s.index_price_e8
                                                            )
                                                            else (
                                                                s.index_price_e8
                                                                - (
                                                                    0
                                                                    if 10000 == 0
                                                                    else (
                                                                        (
                                                                            (
                                                                                s.index_price_e8
                                                                                * s.max_oracle_move_bps
                                                                            )
                                                                            // 10000
                                                                        )
                                                                        + (
                                                                            1
                                                                            if (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                % 10000
                                                                            )
                                                                            < 0
                                                                            else 0
                                                                        )
                                                                    )
                                                                )
                                                            )
                                                        )
                                                        if (
                                                            (
                                                                (
                                                                    10000
                                                                    * (
                                                                        (
                                                                            s.clearing_price_e8
                                                                            - s.index_price_e8
                                                                        )
                                                                        if (
                                                                            s.clearing_price_e8
                                                                            >= s.index_price_e8
                                                                        )
                                                                        else (
                                                                            s.index_price_e8
                                                                            - s.clearing_price_e8
                                                                        )
                                                                    )
                                                                )
                                                                > (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                            )
                                                            and s.oracle_seen
                                                        )
                                                        else s.clearing_price_e8
                                                    )
                                                )
                                                * s.liquidation_penalty_bps
                                            )
                                        )
                                        // 10000
                                    )
                                    + (
                                        1
                                        if (
                                            (
                                                9999
                                                + (
                                                    (
                                                        (
                                                            s.position_base_a
                                                            if (s.position_base_a >= 0)
                                                            else (0 - s.position_base_a)
                                                        )
                                                        * (
                                                            (
                                                                (
                                                                    (
                                                                        0
                                                                        if 10000 == 0
                                                                        else (
                                                                            (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                // 10000
                                                                            )
                                                                            + (
                                                                                1
                                                                                if (
                                                                                    (
                                                                                        s.index_price_e8
                                                                                        * s.max_oracle_move_bps
                                                                                    )
                                                                                    % 10000
                                                                                )
                                                                                < 0
                                                                                else 0
                                                                            )
                                                                        )
                                                                    )
                                                                    + s.index_price_e8
                                                                )
                                                                if (
                                                                    s.clearing_price_e8
                                                                    >= s.index_price_e8
                                                                )
                                                                else (
                                                                    s.index_price_e8
                                                                    - (
                                                                        0
                                                                        if 10000 == 0
                                                                        else (
                                                                            (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                // 10000
                                                                            )
                                                                            + (
                                                                                1
                                                                                if (
                                                                                    (
                                                                                        s.index_price_e8
                                                                                        * s.max_oracle_move_bps
                                                                                    )
                                                                                    % 10000
                                                                                )
                                                                                < 0
                                                                                else 0
                                                                            )
                                                                        )
                                                                    )
                                                                )
                                                            )
                                                            if (
                                                                (
                                                                    (
                                                                        10000
                                                                        * (
                                                                            (
                                                                                s.clearing_price_e8
                                                                                - s.index_price_e8
                                                                            )
                                                                            if (
                                                                                s.clearing_price_e8
                                                                                >= s.index_price_e8
                                                                            )
                                                                            else (
                                                                                s.index_price_e8
                                                                                - s.clearing_price_e8
                                                                            )
                                                                        )
                                                                    )
                                                                    > (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                )
                                                                and s.oracle_seen
                                                            )
                                                            else s.clearing_price_e8
                                                        )
                                                    )
                                                    * s.liquidation_penalty_bps
                                                )
                                            )
                                            % 10000
                                        )
                                        < 0
                                        else 0
                                    )
                                )
                            )
                            if (
                                (
                                    0
                                    if 10000 == 0
                                    else (
                                        (
                                            (
                                                9999
                                                + (
                                                    (
                                                        (
                                                            s.position_base_a
                                                            if (s.position_base_a >= 0)
                                                            else (0 - s.position_base_a)
                                                        )
                                                        * (
                                                            (
                                                                (
                                                                    (
                                                                        0
                                                                        if 10000 == 0
                                                                        else (
                                                                            (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                // 10000
                                                                            )
                                                                            + (
                                                                                1
                                                                                if (
                                                                                    (
                                                                                        s.index_price_e8
                                                                                        * s.max_oracle_move_bps
                                                                                    )
                                                                                    % 10000
                                                                                )
                                                                                < 0
                                                                                else 0
                                                                            )
                                                                        )
                                                                    )
                                                                    + s.index_price_e8
                                                                )
                                                                if (
                                                                    s.clearing_price_e8
                                                                    >= s.index_price_e8
                                                                )
                                                                else (
                                                                    s.index_price_e8
                                                                    - (
                                                                        0
                                                                        if 10000 == 0
                                                                        else (
                                                                            (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                // 10000
                                                                            )
                                                                            + (
                                                                                1
                                                                                if (
                                                                                    (
                                                                                        s.index_price_e8
                                                                                        * s.max_oracle_move_bps
                                                                                    )
                                                                                    % 10000
                                                                                )
                                                                                < 0
                                                                                else 0
                                                                            )
                                                                        )
                                                                    )
                                                                )
                                                            )
                                                            if (
                                                                (
                                                                    (
                                                                        10000
                                                                        * (
                                                                            (
                                                                                s.clearing_price_e8
                                                                                - s.index_price_e8
                                                                            )
                                                                            if (
                                                                                s.clearing_price_e8
                                                                                >= s.index_price_e8
                                                                            )
                                                                            else (
                                                                                s.index_price_e8
                                                                                - s.clearing_price_e8
                                                                            )
                                                                        )
                                                                    )
                                                                    > (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                )
                                                                and s.oracle_seen
                                                            )
                                                            else s.clearing_price_e8
                                                        )
                                                    )
                                                    * s.liquidation_penalty_bps
                                                )
                                            )
                                            // 10000
                                        )
                                        + (
                                            1
                                            if (
                                                (
                                                    9999
                                                    + (
                                                        (
                                                            (
                                                                s.position_base_a
                                                                if (
                                                                    s.position_base_a
                                                                    >= 0
                                                                )
                                                                else (
                                                                    0
                                                                    - s.position_base_a
                                                                )
                                                            )
                                                            * (
                                                                (
                                                                    (
                                                                        (
                                                                            0
                                                                            if 10000
                                                                            == 0
                                                                            else (
                                                                                (
                                                                                    (
                                                                                        s.index_price_e8
                                                                                        * s.max_oracle_move_bps
                                                                                    )
                                                                                    // 10000
                                                                                )
                                                                                + (
                                                                                    1
                                                                                    if (
                                                                                        (
                                                                                            s.index_price_e8
                                                                                            * s.max_oracle_move_bps
                                                                                        )
                                                                                        % 10000
                                                                                    )
                                                                                    < 0
                                                                                    else 0
                                                                                )
                                                                            )
                                                                        )
                                                                        + s.index_price_e8
                                                                    )
                                                                    if (
                                                                        s.clearing_price_e8
                                                                        >= s.index_price_e8
                                                                    )
                                                                    else (
                                                                        s.index_price_e8
                                                                        - (
                                                                            0
                                                                            if 10000
                                                                            == 0
                                                                            else (
                                                                                (
                                                                                    (
                                                                                        s.index_price_e8
                                                                                        * s.max_oracle_move_bps
                                                                                    )
                                                                                    // 10000
                                                                                )
                                                                                + (
                                                                                    1
                                                                                    if (
                                                                                        (
                                                                                            s.index_price_e8
                                                                                            * s.max_oracle_move_bps
                                                                                        )
                                                                                        % 10000
                                                                                    )
                                                                                    < 0
                                                                                    else 0
                                                                                )
                                                                            )
                                                                        )
                                                                    )
                                                                )
                                                                if (
                                                                    (
                                                                        (
                                                                            10000
                                                                            * (
                                                                                (
                                                                                    s.clearing_price_e8
                                                                                    - s.index_price_e8
                                                                                )
                                                                                if (
                                                                                    s.clearing_price_e8
                                                                                    >= s.index_price_e8
                                                                                )
                                                                                else (
                                                                                    s.index_price_e8
                                                                                    - s.clearing_price_e8
                                                                                )
                                                                            )
                                                                        )
                                                                        > (
                                                                            s.index_price_e8
                                                                            * s.max_oracle_move_bps
                                                                        )
                                                                    )
                                                                    and s.oracle_seen
                                                                )
                                                                else s.clearing_price_e8
                                                            )
                                                        )
                                                        * s.liquidation_penalty_bps
                                                    )
                                                )
                                                % 10000
                                            )
                                            < 0
                                            else 0
                                        )
                                    )
                                )
                                <= (
                                    (
                                        (
                                            (
                                                (
                                                    (
                                                        (
                                                            0
                                                            if 10000 == 0
                                                            else (
                                                                (
                                                                    (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                    // 10000
                                                                )
                                                                + (
                                                                    1
                                                                    if (
                                                                        (
                                                                            s.index_price_e8
                                                                            * s.max_oracle_move_bps
                                                                        )
                                                                        % 10000
                                                                    )
                                                                    < 0
                                                                    else 0
                                                                )
                                                            )
                                                        )
                                                        + s.index_price_e8
                                                    )
                                                    if (
                                                        s.clearing_price_e8
                                                        >= s.index_price_e8
                                                    )
                                                    else (
                                                        s.index_price_e8
                                                        - (
                                                            0
                                                            if 10000 == 0
                                                            else (
                                                                (
                                                                    (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                    // 10000
                                                                )
                                                                + (
                                                                    1
                                                                    if (
                                                                        (
                                                                            s.index_price_e8
                                                                            * s.max_oracle_move_bps
                                                                        )
                                                                        % 10000
                                                                    )
                                                                    < 0
                                                                    else 0
                                                                )
                                                            )
                                                        )
                                                    )
                                                )
                                                if (
                                                    (
                                                        (
                                                            10000
                                                            * (
                                                                (
                                                                    s.clearing_price_e8
                                                                    - s.index_price_e8
                                                                )
                                                                if (
                                                                    s.clearing_price_e8
                                                                    >= s.index_price_e8
                                                                )
                                                                else (
                                                                    s.index_price_e8
                                                                    - s.clearing_price_e8
                                                                )
                                                            )
                                                        )
                                                        > (
                                                            s.index_price_e8
                                                            * s.max_oracle_move_bps
                                                        )
                                                    )
                                                    and s.oracle_seen
                                                )
                                                else s.clearing_price_e8
                                            )
                                            - s.index_price_e8
                                        )
                                        * s.position_base_a
                                    )
                                    + s.collateral_e8_a
                                )
                            )
                            else (
                                (
                                    (
                                        (
                                            (
                                                (
                                                    (
                                                        0
                                                        if 10000 == 0
                                                        else (
                                                            (
                                                                (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                                // 10000
                                                            )
                                                            + (
                                                                1
                                                                if (
                                                                    (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                    % 10000
                                                                )
                                                                < 0
                                                                else 0
                                                            )
                                                        )
                                                    )
                                                    + s.index_price_e8
                                                )
                                                if (
                                                    s.clearing_price_e8
                                                    >= s.index_price_e8
                                                )
                                                else (
                                                    s.index_price_e8
                                                    - (
                                                        0
                                                        if 10000 == 0
                                                        else (
                                                            (
                                                                (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                                // 10000
                                                            )
                                                            + (
                                                                1
                                                                if (
                                                                    (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                    % 10000
                                                                )
                                                                < 0
                                                                else 0
                                                            )
                                                        )
                                                    )
                                                )
                                            )
                                            if (
                                                (
                                                    (
                                                        10000
                                                        * (
                                                            (
                                                                s.clearing_price_e8
                                                                - s.index_price_e8
                                                            )
                                                            if (
                                                                s.clearing_price_e8
                                                                >= s.index_price_e8
                                                            )
                                                            else (
                                                                s.index_price_e8
                                                                - s.clearing_price_e8
                                                            )
                                                        )
                                                    )
                                                    > (
                                                        s.index_price_e8
                                                        * s.max_oracle_move_bps
                                                    )
                                                )
                                                and s.oracle_seen
                                            )
                                            else s.clearing_price_e8
                                        )
                                        - s.index_price_e8
                                    )
                                    * s.position_base_a
                                )
                                + s.collateral_e8_a
                            )
                        )
                        if (
                            (
                                (
                                    (
                                        (
                                            (
                                                (
                                                    (
                                                        (
                                                            0
                                                            if 10000 == 0
                                                            else (
                                                                (
                                                                    (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                    // 10000
                                                                )
                                                                + (
                                                                    1
                                                                    if (
                                                                        (
                                                                            s.index_price_e8
                                                                            * s.max_oracle_move_bps
                                                                        )
                                                                        % 10000
                                                                    )
                                                                    < 0
                                                                    else 0
                                                                )
                                                            )
                                                        )
                                                        + s.index_price_e8
                                                    )
                                                    if (
                                                        s.clearing_price_e8
                                                        >= s.index_price_e8
                                                    )
                                                    else (
                                                        s.index_price_e8
                                                        - (
                                                            0
                                                            if 10000 == 0
                                                            else (
                                                                (
                                                                    (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                    // 10000
                                                                )
                                                                + (
                                                                    1
                                                                    if (
                                                                        (
                                                                            s.index_price_e8
                                                                            * s.max_oracle_move_bps
                                                                        )
                                                                        % 10000
                                                                    )
                                                                    < 0
                                                                    else 0
                                                                )
                                                            )
                                                        )
                                                    )
                                                )
                                                if (
                                                    (
                                                        (
                                                            10000
                                                            * (
                                                                (
                                                                    s.clearing_price_e8
                                                                    - s.index_price_e8
                                                                )
                                                                if (
                                                                    s.clearing_price_e8
                                                                    >= s.index_price_e8
                                                                )
                                                                else (
                                                                    s.index_price_e8
                                                                    - s.clearing_price_e8
                                                                )
                                                            )
                                                        )
                                                        > (
                                                            s.index_price_e8
                                                            * s.max_oracle_move_bps
                                                        )
                                                    )
                                                    and s.oracle_seen
                                                )
                                                else s.clearing_price_e8
                                            )
                                            - s.index_price_e8
                                        )
                                        * s.position_base_a
                                    )
                                    + s.collateral_e8_a
                                )
                                < (
                                    0
                                    if 10000 == 0
                                    else (
                                        (
                                            (
                                                9999
                                                + (
                                                    (
                                                        (
                                                            s.position_base_a
                                                            if (s.position_base_a >= 0)
                                                            else (0 - s.position_base_a)
                                                        )
                                                        * (
                                                            (
                                                                (
                                                                    (
                                                                        0
                                                                        if 10000 == 0
                                                                        else (
                                                                            (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                // 10000
                                                                            )
                                                                            + (
                                                                                1
                                                                                if (
                                                                                    (
                                                                                        s.index_price_e8
                                                                                        * s.max_oracle_move_bps
                                                                                    )
                                                                                    % 10000
                                                                                )
                                                                                < 0
                                                                                else 0
                                                                            )
                                                                        )
                                                                    )
                                                                    + s.index_price_e8
                                                                )
                                                                if (
                                                                    s.clearing_price_e8
                                                                    >= s.index_price_e8
                                                                )
                                                                else (
                                                                    s.index_price_e8
                                                                    - (
                                                                        0
                                                                        if 10000 == 0
                                                                        else (
                                                                            (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                // 10000
                                                                            )
                                                                            + (
                                                                                1
                                                                                if (
                                                                                    (
                                                                                        s.index_price_e8
                                                                                        * s.max_oracle_move_bps
                                                                                    )
                                                                                    % 10000
                                                                                )
                                                                                < 0
                                                                                else 0
                                                                            )
                                                                        )
                                                                    )
                                                                )
                                                            )
                                                            if (
                                                                (
                                                                    (
                                                                        10000
                                                                        * (
                                                                            (
                                                                                s.clearing_price_e8
                                                                                - s.index_price_e8
                                                                            )
                                                                            if (
                                                                                s.clearing_price_e8
                                                                                >= s.index_price_e8
                                                                            )
                                                                            else (
                                                                                s.index_price_e8
                                                                                - s.clearing_price_e8
                                                                            )
                                                                        )
                                                                    )
                                                                    > (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                )
                                                                and s.oracle_seen
                                                            )
                                                            else s.clearing_price_e8
                                                        )
                                                    )
                                                    * s.maintenance_margin_bps
                                                )
                                            )
                                            // 10000
                                        )
                                        + (
                                            1
                                            if (
                                                (
                                                    9999
                                                    + (
                                                        (
                                                            (
                                                                s.position_base_a
                                                                if (
                                                                    s.position_base_a
                                                                    >= 0
                                                                )
                                                                else (
                                                                    0
                                                                    - s.position_base_a
                                                                )
                                                            )
                                                            * (
                                                                (
                                                                    (
                                                                        (
                                                                            0
                                                                            if 10000
                                                                            == 0
                                                                            else (
                                                                                (
                                                                                    (
                                                                                        s.index_price_e8
                                                                                        * s.max_oracle_move_bps
                                                                                    )
                                                                                    // 10000
                                                                                )
                                                                                + (
                                                                                    1
                                                                                    if (
                                                                                        (
                                                                                            s.index_price_e8
                                                                                            * s.max_oracle_move_bps
                                                                                        )
                                                                                        % 10000
                                                                                    )
                                                                                    < 0
                                                                                    else 0
                                                                                )
                                                                            )
                                                                        )
                                                                        + s.index_price_e8
                                                                    )
                                                                    if (
                                                                        s.clearing_price_e8
                                                                        >= s.index_price_e8
                                                                    )
                                                                    else (
                                                                        s.index_price_e8
                                                                        - (
                                                                            0
                                                                            if 10000
                                                                            == 0
                                                                            else (
                                                                                (
                                                                                    (
                                                                                        s.index_price_e8
                                                                                        * s.max_oracle_move_bps
                                                                                    )
                                                                                    // 10000
                                                                                )
                                                                                + (
                                                                                    1
                                                                                    if (
                                                                                        (
                                                                                            s.index_price_e8
                                                                                            * s.max_oracle_move_bps
                                                                                        )
                                                                                        % 10000
                                                                                    )
                                                                                    < 0
                                                                                    else 0
                                                                                )
                                                                            )
                                                                        )
                                                                    )
                                                                )
                                                                if (
                                                                    (
                                                                        (
                                                                            10000
                                                                            * (
                                                                                (
                                                                                    s.clearing_price_e8
                                                                                    - s.index_price_e8
                                                                                )
                                                                                if (
                                                                                    s.clearing_price_e8
                                                                                    >= s.index_price_e8
                                                                                )
                                                                                else (
                                                                                    s.index_price_e8
                                                                                    - s.clearing_price_e8
                                                                                )
                                                                            )
                                                                        )
                                                                        > (
                                                                            s.index_price_e8
                                                                            * s.max_oracle_move_bps
                                                                        )
                                                                    )
                                                                    and s.oracle_seen
                                                                )
                                                                else s.clearing_price_e8
                                                            )
                                                        )
                                                        * s.maintenance_margin_bps
                                                    )
                                                )
                                                % 10000
                                            )
                                            < 0
                                            else 0
                                        )
                                    )
                                )
                            )
                            and (not (0 == s.position_base_a))
                        )
                        else 0
                    )
                    + (
                        (
                            (
                                0
                                if 10000 == 0
                                else (
                                    (
                                        (
                                            9999
                                            + (
                                                (
                                                    (
                                                        s.position_base_b
                                                        if (s.position_base_b >= 0)
                                                        else (0 - s.position_base_b)
                                                    )
                                                    * (
                                                        (
                                                            (
                                                                (
                                                                    0
                                                                    if 10000 == 0
                                                                    else (
                                                                        (
                                                                            (
                                                                                s.index_price_e8
                                                                                * s.max_oracle_move_bps
                                                                            )
                                                                            // 10000
                                                                        )
                                                                        + (
                                                                            1
                                                                            if (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                % 10000
                                                                            )
                                                                            < 0
                                                                            else 0
                                                                        )
                                                                    )
                                                                )
                                                                + s.index_price_e8
                                                            )
                                                            if (
                                                                s.clearing_price_e8
                                                                >= s.index_price_e8
                                                            )
                                                            else (
                                                                s.index_price_e8
                                                                - (
                                                                    0
                                                                    if 10000 == 0
                                                                    else (
                                                                        (
                                                                            (
                                                                                s.index_price_e8
                                                                                * s.max_oracle_move_bps
                                                                            )
                                                                            // 10000
                                                                        )
                                                                        + (
                                                                            1
                                                                            if (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                % 10000
                                                                            )
                                                                            < 0
                                                                            else 0
                                                                        )
                                                                    )
                                                                )
                                                            )
                                                        )
                                                        if (
                                                            (
                                                                (
                                                                    10000
                                                                    * (
                                                                        (
                                                                            s.clearing_price_e8
                                                                            - s.index_price_e8
                                                                        )
                                                                        if (
                                                                            s.clearing_price_e8
                                                                            >= s.index_price_e8
                                                                        )
                                                                        else (
                                                                            s.index_price_e8
                                                                            - s.clearing_price_e8
                                                                        )
                                                                    )
                                                                )
                                                                > (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                            )
                                                            and s.oracle_seen
                                                        )
                                                        else s.clearing_price_e8
                                                    )
                                                )
                                                * s.liquidation_penalty_bps
                                            )
                                        )
                                        // 10000
                                    )
                                    + (
                                        1
                                        if (
                                            (
                                                9999
                                                + (
                                                    (
                                                        (
                                                            s.position_base_b
                                                            if (s.position_base_b >= 0)
                                                            else (0 - s.position_base_b)
                                                        )
                                                        * (
                                                            (
                                                                (
                                                                    (
                                                                        0
                                                                        if 10000 == 0
                                                                        else (
                                                                            (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                // 10000
                                                                            )
                                                                            + (
                                                                                1
                                                                                if (
                                                                                    (
                                                                                        s.index_price_e8
                                                                                        * s.max_oracle_move_bps
                                                                                    )
                                                                                    % 10000
                                                                                )
                                                                                < 0
                                                                                else 0
                                                                            )
                                                                        )
                                                                    )
                                                                    + s.index_price_e8
                                                                )
                                                                if (
                                                                    s.clearing_price_e8
                                                                    >= s.index_price_e8
                                                                )
                                                                else (
                                                                    s.index_price_e8
                                                                    - (
                                                                        0
                                                                        if 10000 == 0
                                                                        else (
                                                                            (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                // 10000
                                                                            )
                                                                            + (
                                                                                1
                                                                                if (
                                                                                    (
                                                                                        s.index_price_e8
                                                                                        * s.max_oracle_move_bps
                                                                                    )
                                                                                    % 10000
                                                                                )
                                                                                < 0
                                                                                else 0
                                                                            )
                                                                        )
                                                                    )
                                                                )
                                                            )
                                                            if (
                                                                (
                                                                    (
                                                                        10000
                                                                        * (
                                                                            (
                                                                                s.clearing_price_e8
                                                                                - s.index_price_e8
                                                                            )
                                                                            if (
                                                                                s.clearing_price_e8
                                                                                >= s.index_price_e8
                                                                            )
                                                                            else (
                                                                                s.index_price_e8
                                                                                - s.clearing_price_e8
                                                                            )
                                                                        )
                                                                    )
                                                                    > (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                )
                                                                and s.oracle_seen
                                                            )
                                                            else s.clearing_price_e8
                                                        )
                                                    )
                                                    * s.liquidation_penalty_bps
                                                )
                                            )
                                            % 10000
                                        )
                                        < 0
                                        else 0
                                    )
                                )
                            )
                            if (
                                (
                                    0
                                    if 10000 == 0
                                    else (
                                        (
                                            (
                                                9999
                                                + (
                                                    (
                                                        (
                                                            s.position_base_b
                                                            if (s.position_base_b >= 0)
                                                            else (0 - s.position_base_b)
                                                        )
                                                        * (
                                                            (
                                                                (
                                                                    (
                                                                        0
                                                                        if 10000 == 0
                                                                        else (
                                                                            (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                // 10000
                                                                            )
                                                                            + (
                                                                                1
                                                                                if (
                                                                                    (
                                                                                        s.index_price_e8
                                                                                        * s.max_oracle_move_bps
                                                                                    )
                                                                                    % 10000
                                                                                )
                                                                                < 0
                                                                                else 0
                                                                            )
                                                                        )
                                                                    )
                                                                    + s.index_price_e8
                                                                )
                                                                if (
                                                                    s.clearing_price_e8
                                                                    >= s.index_price_e8
                                                                )
                                                                else (
                                                                    s.index_price_e8
                                                                    - (
                                                                        0
                                                                        if 10000 == 0
                                                                        else (
                                                                            (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                // 10000
                                                                            )
                                                                            + (
                                                                                1
                                                                                if (
                                                                                    (
                                                                                        s.index_price_e8
                                                                                        * s.max_oracle_move_bps
                                                                                    )
                                                                                    % 10000
                                                                                )
                                                                                < 0
                                                                                else 0
                                                                            )
                                                                        )
                                                                    )
                                                                )
                                                            )
                                                            if (
                                                                (
                                                                    (
                                                                        10000
                                                                        * (
                                                                            (
                                                                                s.clearing_price_e8
                                                                                - s.index_price_e8
                                                                            )
                                                                            if (
                                                                                s.clearing_price_e8
                                                                                >= s.index_price_e8
                                                                            )
                                                                            else (
                                                                                s.index_price_e8
                                                                                - s.clearing_price_e8
                                                                            )
                                                                        )
                                                                    )
                                                                    > (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                )
                                                                and s.oracle_seen
                                                            )
                                                            else s.clearing_price_e8
                                                        )
                                                    )
                                                    * s.liquidation_penalty_bps
                                                )
                                            )
                                            // 10000
                                        )
                                        + (
                                            1
                                            if (
                                                (
                                                    9999
                                                    + (
                                                        (
                                                            (
                                                                s.position_base_b
                                                                if (
                                                                    s.position_base_b
                                                                    >= 0
                                                                )
                                                                else (
                                                                    0
                                                                    - s.position_base_b
                                                                )
                                                            )
                                                            * (
                                                                (
                                                                    (
                                                                        (
                                                                            0
                                                                            if 10000
                                                                            == 0
                                                                            else (
                                                                                (
                                                                                    (
                                                                                        s.index_price_e8
                                                                                        * s.max_oracle_move_bps
                                                                                    )
                                                                                    // 10000
                                                                                )
                                                                                + (
                                                                                    1
                                                                                    if (
                                                                                        (
                                                                                            s.index_price_e8
                                                                                            * s.max_oracle_move_bps
                                                                                        )
                                                                                        % 10000
                                                                                    )
                                                                                    < 0
                                                                                    else 0
                                                                                )
                                                                            )
                                                                        )
                                                                        + s.index_price_e8
                                                                    )
                                                                    if (
                                                                        s.clearing_price_e8
                                                                        >= s.index_price_e8
                                                                    )
                                                                    else (
                                                                        s.index_price_e8
                                                                        - (
                                                                            0
                                                                            if 10000
                                                                            == 0
                                                                            else (
                                                                                (
                                                                                    (
                                                                                        s.index_price_e8
                                                                                        * s.max_oracle_move_bps
                                                                                    )
                                                                                    // 10000
                                                                                )
                                                                                + (
                                                                                    1
                                                                                    if (
                                                                                        (
                                                                                            s.index_price_e8
                                                                                            * s.max_oracle_move_bps
                                                                                        )
                                                                                        % 10000
                                                                                    )
                                                                                    < 0
                                                                                    else 0
                                                                                )
                                                                            )
                                                                        )
                                                                    )
                                                                )
                                                                if (
                                                                    (
                                                                        (
                                                                            10000
                                                                            * (
                                                                                (
                                                                                    s.clearing_price_e8
                                                                                    - s.index_price_e8
                                                                                )
                                                                                if (
                                                                                    s.clearing_price_e8
                                                                                    >= s.index_price_e8
                                                                                )
                                                                                else (
                                                                                    s.index_price_e8
                                                                                    - s.clearing_price_e8
                                                                                )
                                                                            )
                                                                        )
                                                                        > (
                                                                            s.index_price_e8
                                                                            * s.max_oracle_move_bps
                                                                        )
                                                                    )
                                                                    and s.oracle_seen
                                                                )
                                                                else s.clearing_price_e8
                                                            )
                                                        )
                                                        * s.liquidation_penalty_bps
                                                    )
                                                )
                                                % 10000
                                            )
                                            < 0
                                            else 0
                                        )
                                    )
                                )
                                <= (
                                    (
                                        (
                                            (
                                                (
                                                    (
                                                        (
                                                            0
                                                            if 10000 == 0
                                                            else (
                                                                (
                                                                    (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                    // 10000
                                                                )
                                                                + (
                                                                    1
                                                                    if (
                                                                        (
                                                                            s.index_price_e8
                                                                            * s.max_oracle_move_bps
                                                                        )
                                                                        % 10000
                                                                    )
                                                                    < 0
                                                                    else 0
                                                                )
                                                            )
                                                        )
                                                        + s.index_price_e8
                                                    )
                                                    if (
                                                        s.clearing_price_e8
                                                        >= s.index_price_e8
                                                    )
                                                    else (
                                                        s.index_price_e8
                                                        - (
                                                            0
                                                            if 10000 == 0
                                                            else (
                                                                (
                                                                    (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                    // 10000
                                                                )
                                                                + (
                                                                    1
                                                                    if (
                                                                        (
                                                                            s.index_price_e8
                                                                            * s.max_oracle_move_bps
                                                                        )
                                                                        % 10000
                                                                    )
                                                                    < 0
                                                                    else 0
                                                                )
                                                            )
                                                        )
                                                    )
                                                )
                                                if (
                                                    (
                                                        (
                                                            10000
                                                            * (
                                                                (
                                                                    s.clearing_price_e8
                                                                    - s.index_price_e8
                                                                )
                                                                if (
                                                                    s.clearing_price_e8
                                                                    >= s.index_price_e8
                                                                )
                                                                else (
                                                                    s.index_price_e8
                                                                    - s.clearing_price_e8
                                                                )
                                                            )
                                                        )
                                                        > (
                                                            s.index_price_e8
                                                            * s.max_oracle_move_bps
                                                        )
                                                    )
                                                    and s.oracle_seen
                                                )
                                                else s.clearing_price_e8
                                            )
                                            - s.index_price_e8
                                        )
                                        * s.position_base_b
                                    )
                                    + s.collateral_e8_b
                                )
                            )
                            else (
                                (
                                    (
                                        (
                                            (
                                                (
                                                    (
                                                        0
                                                        if 10000 == 0
                                                        else (
                                                            (
                                                                (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                                // 10000
                                                            )
                                                            + (
                                                                1
                                                                if (
                                                                    (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                    % 10000
                                                                )
                                                                < 0
                                                                else 0
                                                            )
                                                        )
                                                    )
                                                    + s.index_price_e8
                                                )
                                                if (
                                                    s.clearing_price_e8
                                                    >= s.index_price_e8
                                                )
                                                else (
                                                    s.index_price_e8
                                                    - (
                                                        0
                                                        if 10000 == 0
                                                        else (
                                                            (
                                                                (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                                // 10000
                                                            )
                                                            + (
                                                                1
                                                                if (
                                                                    (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                    % 10000
                                                                )
                                                                < 0
                                                                else 0
                                                            )
                                                        )
                                                    )
                                                )
                                            )
                                            if (
                                                (
                                                    (
                                                        10000
                                                        * (
                                                            (
                                                                s.clearing_price_e8
                                                                - s.index_price_e8
                                                            )
                                                            if (
                                                                s.clearing_price_e8
                                                                >= s.index_price_e8
                                                            )
                                                            else (
                                                                s.index_price_e8
                                                                - s.clearing_price_e8
                                                            )
                                                        )
                                                    )
                                                    > (
                                                        s.index_price_e8
                                                        * s.max_oracle_move_bps
                                                    )
                                                )
                                                and s.oracle_seen
                                            )
                                            else s.clearing_price_e8
                                        )
                                        - s.index_price_e8
                                    )
                                    * s.position_base_b
                                )
                                + s.collateral_e8_b
                            )
                        )
                        if (
                            (
                                (
                                    (
                                        (
                                            (
                                                (
                                                    (
                                                        (
                                                            0
                                                            if 10000 == 0
                                                            else (
                                                                (
                                                                    (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                    // 10000
                                                                )
                                                                + (
                                                                    1
                                                                    if (
                                                                        (
                                                                            s.index_price_e8
                                                                            * s.max_oracle_move_bps
                                                                        )
                                                                        % 10000
                                                                    )
                                                                    < 0
                                                                    else 0
                                                                )
                                                            )
                                                        )
                                                        + s.index_price_e8
                                                    )
                                                    if (
                                                        s.clearing_price_e8
                                                        >= s.index_price_e8
                                                    )
                                                    else (
                                                        s.index_price_e8
                                                        - (
                                                            0
                                                            if 10000 == 0
                                                            else (
                                                                (
                                                                    (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                    // 10000
                                                                )
                                                                + (
                                                                    1
                                                                    if (
                                                                        (
                                                                            s.index_price_e8
                                                                            * s.max_oracle_move_bps
                                                                        )
                                                                        % 10000
                                                                    )
                                                                    < 0
                                                                    else 0
                                                                )
                                                            )
                                                        )
                                                    )
                                                )
                                                if (
                                                    (
                                                        (
                                                            10000
                                                            * (
                                                                (
                                                                    s.clearing_price_e8
                                                                    - s.index_price_e8
                                                                )
                                                                if (
                                                                    s.clearing_price_e8
                                                                    >= s.index_price_e8
                                                                )
                                                                else (
                                                                    s.index_price_e8
                                                                    - s.clearing_price_e8
                                                                )
                                                            )
                                                        )
                                                        > (
                                                            s.index_price_e8
                                                            * s.max_oracle_move_bps
                                                        )
                                                    )
                                                    and s.oracle_seen
                                                )
                                                else s.clearing_price_e8
                                            )
                                            - s.index_price_e8
                                        )
                                        * s.position_base_b
                                    )
                                    + s.collateral_e8_b
                                )
                                < (
                                    0
                                    if 10000 == 0
                                    else (
                                        (
                                            (
                                                9999
                                                + (
                                                    (
                                                        (
                                                            s.position_base_b
                                                            if (s.position_base_b >= 0)
                                                            else (0 - s.position_base_b)
                                                        )
                                                        * (
                                                            (
                                                                (
                                                                    (
                                                                        0
                                                                        if 10000 == 0
                                                                        else (
                                                                            (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                // 10000
                                                                            )
                                                                            + (
                                                                                1
                                                                                if (
                                                                                    (
                                                                                        s.index_price_e8
                                                                                        * s.max_oracle_move_bps
                                                                                    )
                                                                                    % 10000
                                                                                )
                                                                                < 0
                                                                                else 0
                                                                            )
                                                                        )
                                                                    )
                                                                    + s.index_price_e8
                                                                )
                                                                if (
                                                                    s.clearing_price_e8
                                                                    >= s.index_price_e8
                                                                )
                                                                else (
                                                                    s.index_price_e8
                                                                    - (
                                                                        0
                                                                        if 10000 == 0
                                                                        else (
                                                                            (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                // 10000
                                                                            )
                                                                            + (
                                                                                1
                                                                                if (
                                                                                    (
                                                                                        s.index_price_e8
                                                                                        * s.max_oracle_move_bps
                                                                                    )
                                                                                    % 10000
                                                                                )
                                                                                < 0
                                                                                else 0
                                                                            )
                                                                        )
                                                                    )
                                                                )
                                                            )
                                                            if (
                                                                (
                                                                    (
                                                                        10000
                                                                        * (
                                                                            (
                                                                                s.clearing_price_e8
                                                                                - s.index_price_e8
                                                                            )
                                                                            if (
                                                                                s.clearing_price_e8
                                                                                >= s.index_price_e8
                                                                            )
                                                                            else (
                                                                                s.index_price_e8
                                                                                - s.clearing_price_e8
                                                                            )
                                                                        )
                                                                    )
                                                                    > (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                )
                                                                and s.oracle_seen
                                                            )
                                                            else s.clearing_price_e8
                                                        )
                                                    )
                                                    * s.maintenance_margin_bps
                                                )
                                            )
                                            // 10000
                                        )
                                        + (
                                            1
                                            if (
                                                (
                                                    9999
                                                    + (
                                                        (
                                                            (
                                                                s.position_base_b
                                                                if (
                                                                    s.position_base_b
                                                                    >= 0
                                                                )
                                                                else (
                                                                    0
                                                                    - s.position_base_b
                                                                )
                                                            )
                                                            * (
                                                                (
                                                                    (
                                                                        (
                                                                            0
                                                                            if 10000
                                                                            == 0
                                                                            else (
                                                                                (
                                                                                    (
                                                                                        s.index_price_e8
                                                                                        * s.max_oracle_move_bps
                                                                                    )
                                                                                    // 10000
                                                                                )
                                                                                + (
                                                                                    1
                                                                                    if (
                                                                                        (
                                                                                            s.index_price_e8
                                                                                            * s.max_oracle_move_bps
                                                                                        )
                                                                                        % 10000
                                                                                    )
                                                                                    < 0
                                                                                    else 0
                                                                                )
                                                                            )
                                                                        )
                                                                        + s.index_price_e8
                                                                    )
                                                                    if (
                                                                        s.clearing_price_e8
                                                                        >= s.index_price_e8
                                                                    )
                                                                    else (
                                                                        s.index_price_e8
                                                                        - (
                                                                            0
                                                                            if 10000
                                                                            == 0
                                                                            else (
                                                                                (
                                                                                    (
                                                                                        s.index_price_e8
                                                                                        * s.max_oracle_move_bps
                                                                                    )
                                                                                    // 10000
                                                                                )
                                                                                + (
                                                                                    1
                                                                                    if (
                                                                                        (
                                                                                            s.index_price_e8
                                                                                            * s.max_oracle_move_bps
                                                                                        )
                                                                                        % 10000
                                                                                    )
                                                                                    < 0
                                                                                    else 0
                                                                                )
                                                                            )
                                                                        )
                                                                    )
                                                                )
                                                                if (
                                                                    (
                                                                        (
                                                                            10000
                                                                            * (
                                                                                (
                                                                                    s.clearing_price_e8
                                                                                    - s.index_price_e8
                                                                                )
                                                                                if (
                                                                                    s.clearing_price_e8
                                                                                    >= s.index_price_e8
                                                                                )
                                                                                else (
                                                                                    s.index_price_e8
                                                                                    - s.clearing_price_e8
                                                                                )
                                                                            )
                                                                        )
                                                                        > (
                                                                            s.index_price_e8
                                                                            * s.max_oracle_move_bps
                                                                        )
                                                                    )
                                                                    and s.oracle_seen
                                                                )
                                                                else s.clearing_price_e8
                                                            )
                                                        )
                                                        * s.maintenance_margin_bps
                                                    )
                                                )
                                                % 10000
                                            )
                                            < 0
                                            else 0
                                        )
                                    )
                                )
                            )
                            and (not (0 == s.position_base_b))
                        )
                        else 0
                    )
                )
                + s.fee_pool_e8
            ),
            index_price_e8=(
                (
                    (
                        (
                            0
                            if 10000 == 0
                            else (
                                ((s.index_price_e8 * s.max_oracle_move_bps) // 10000)
                                + (
                                    1
                                    if (
                                        (s.index_price_e8 * s.max_oracle_move_bps)
                                        % 10000
                                    )
                                    < 0
                                    else 0
                                )
                            )
                        )
                        + s.index_price_e8
                    )
                    if (s.clearing_price_e8 >= s.index_price_e8)
                    else (
                        s.index_price_e8
                        - (
                            0
                            if 10000 == 0
                            else (
                                ((s.index_price_e8 * s.max_oracle_move_bps) // 10000)
                                + (
                                    1
                                    if (
                                        (s.index_price_e8 * s.max_oracle_move_bps)
                                        % 10000
                                    )
                                    < 0
                                    else 0
                                )
                            )
                        )
                    )
                )
                if (
                    (
                        (
                            10000
                            * (
                                (s.clearing_price_e8 - s.index_price_e8)
                                if (s.clearing_price_e8 >= s.index_price_e8)
                                else (s.index_price_e8 - s.clearing_price_e8)
                            )
                        )
                        > (s.index_price_e8 * s.max_oracle_move_bps)
                    )
                    and s.oracle_seen
                )
                else s.clearing_price_e8
            ),
            initial_margin_bps=s.initial_margin_bps,
            liquidated_this_step=(
                (
                    (
                        (
                            (
                                (
                                    (
                                        (
                                            (
                                                (
                                                    0
                                                    if 10000 == 0
                                                    else (
                                                        (
                                                            (
                                                                s.index_price_e8
                                                                * s.max_oracle_move_bps
                                                            )
                                                            // 10000
                                                        )
                                                        + (
                                                            1
                                                            if (
                                                                (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                                % 10000
                                                            )
                                                            < 0
                                                            else 0
                                                        )
                                                    )
                                                )
                                                + s.index_price_e8
                                            )
                                            if (s.clearing_price_e8 >= s.index_price_e8)
                                            else (
                                                s.index_price_e8
                                                - (
                                                    0
                                                    if 10000 == 0
                                                    else (
                                                        (
                                                            (
                                                                s.index_price_e8
                                                                * s.max_oracle_move_bps
                                                            )
                                                            // 10000
                                                        )
                                                        + (
                                                            1
                                                            if (
                                                                (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                                % 10000
                                                            )
                                                            < 0
                                                            else 0
                                                        )
                                                    )
                                                )
                                            )
                                        )
                                        if (
                                            (
                                                (
                                                    10000
                                                    * (
                                                        (
                                                            s.clearing_price_e8
                                                            - s.index_price_e8
                                                        )
                                                        if (
                                                            s.clearing_price_e8
                                                            >= s.index_price_e8
                                                        )
                                                        else (
                                                            s.index_price_e8
                                                            - s.clearing_price_e8
                                                        )
                                                    )
                                                )
                                                > (
                                                    s.index_price_e8
                                                    * s.max_oracle_move_bps
                                                )
                                            )
                                            and s.oracle_seen
                                        )
                                        else s.clearing_price_e8
                                    )
                                    - s.index_price_e8
                                )
                                * s.position_base_a
                            )
                            + s.collateral_e8_a
                        )
                        < (
                            0
                            if 10000 == 0
                            else (
                                (
                                    (
                                        9999
                                        + (
                                            (
                                                (
                                                    s.position_base_a
                                                    if (s.position_base_a >= 0)
                                                    else (0 - s.position_base_a)
                                                )
                                                * (
                                                    (
                                                        (
                                                            (
                                                                0
                                                                if 10000 == 0
                                                                else (
                                                                    (
                                                                        (
                                                                            s.index_price_e8
                                                                            * s.max_oracle_move_bps
                                                                        )
                                                                        // 10000
                                                                    )
                                                                    + (
                                                                        1
                                                                        if (
                                                                            (
                                                                                s.index_price_e8
                                                                                * s.max_oracle_move_bps
                                                                            )
                                                                            % 10000
                                                                        )
                                                                        < 0
                                                                        else 0
                                                                    )
                                                                )
                                                            )
                                                            + s.index_price_e8
                                                        )
                                                        if (
                                                            s.clearing_price_e8
                                                            >= s.index_price_e8
                                                        )
                                                        else (
                                                            s.index_price_e8
                                                            - (
                                                                0
                                                                if 10000 == 0
                                                                else (
                                                                    (
                                                                        (
                                                                            s.index_price_e8
                                                                            * s.max_oracle_move_bps
                                                                        )
                                                                        // 10000
                                                                    )
                                                                    + (
                                                                        1
                                                                        if (
                                                                            (
                                                                                s.index_price_e8
                                                                                * s.max_oracle_move_bps
                                                                            )
                                                                            % 10000
                                                                        )
                                                                        < 0
                                                                        else 0
                                                                    )
                                                                )
                                                            )
                                                        )
                                                    )
                                                    if (
                                                        (
                                                            (
                                                                10000
                                                                * (
                                                                    (
                                                                        s.clearing_price_e8
                                                                        - s.index_price_e8
                                                                    )
                                                                    if (
                                                                        s.clearing_price_e8
                                                                        >= s.index_price_e8
                                                                    )
                                                                    else (
                                                                        s.index_price_e8
                                                                        - s.clearing_price_e8
                                                                    )
                                                                )
                                                            )
                                                            > (
                                                                s.index_price_e8
                                                                * s.max_oracle_move_bps
                                                            )
                                                        )
                                                        and s.oracle_seen
                                                    )
                                                    else s.clearing_price_e8
                                                )
                                            )
                                            * s.maintenance_margin_bps
                                        )
                                    )
                                    // 10000
                                )
                                + (
                                    1
                                    if (
                                        (
                                            9999
                                            + (
                                                (
                                                    (
                                                        s.position_base_a
                                                        if (s.position_base_a >= 0)
                                                        else (0 - s.position_base_a)
                                                    )
                                                    * (
                                                        (
                                                            (
                                                                (
                                                                    0
                                                                    if 10000 == 0
                                                                    else (
                                                                        (
                                                                            (
                                                                                s.index_price_e8
                                                                                * s.max_oracle_move_bps
                                                                            )
                                                                            // 10000
                                                                        )
                                                                        + (
                                                                            1
                                                                            if (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                % 10000
                                                                            )
                                                                            < 0
                                                                            else 0
                                                                        )
                                                                    )
                                                                )
                                                                + s.index_price_e8
                                                            )
                                                            if (
                                                                s.clearing_price_e8
                                                                >= s.index_price_e8
                                                            )
                                                            else (
                                                                s.index_price_e8
                                                                - (
                                                                    0
                                                                    if 10000 == 0
                                                                    else (
                                                                        (
                                                                            (
                                                                                s.index_price_e8
                                                                                * s.max_oracle_move_bps
                                                                            )
                                                                            // 10000
                                                                        )
                                                                        + (
                                                                            1
                                                                            if (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                % 10000
                                                                            )
                                                                            < 0
                                                                            else 0
                                                                        )
                                                                    )
                                                                )
                                                            )
                                                        )
                                                        if (
                                                            (
                                                                (
                                                                    10000
                                                                    * (
                                                                        (
                                                                            s.clearing_price_e8
                                                                            - s.index_price_e8
                                                                        )
                                                                        if (
                                                                            s.clearing_price_e8
                                                                            >= s.index_price_e8
                                                                        )
                                                                        else (
                                                                            s.index_price_e8
                                                                            - s.clearing_price_e8
                                                                        )
                                                                    )
                                                                )
                                                                > (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                            )
                                                            and s.oracle_seen
                                                        )
                                                        else s.clearing_price_e8
                                                    )
                                                )
                                                * s.maintenance_margin_bps
                                            )
                                        )
                                        % 10000
                                    )
                                    < 0
                                    else 0
                                )
                            )
                        )
                    )
                    and (not (0 == s.position_base_a))
                )
                or (
                    (
                        (
                            (
                                (
                                    (
                                        (
                                            (
                                                (
                                                    0
                                                    if 10000 == 0
                                                    else (
                                                        (
                                                            (
                                                                s.index_price_e8
                                                                * s.max_oracle_move_bps
                                                            )
                                                            // 10000
                                                        )
                                                        + (
                                                            1
                                                            if (
                                                                (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                                % 10000
                                                            )
                                                            < 0
                                                            else 0
                                                        )
                                                    )
                                                )
                                                + s.index_price_e8
                                            )
                                            if (s.clearing_price_e8 >= s.index_price_e8)
                                            else (
                                                s.index_price_e8
                                                - (
                                                    0
                                                    if 10000 == 0
                                                    else (
                                                        (
                                                            (
                                                                s.index_price_e8
                                                                * s.max_oracle_move_bps
                                                            )
                                                            // 10000
                                                        )
                                                        + (
                                                            1
                                                            if (
                                                                (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                                % 10000
                                                            )
                                                            < 0
                                                            else 0
                                                        )
                                                    )
                                                )
                                            )
                                        )
                                        if (
                                            (
                                                (
                                                    10000
                                                    * (
                                                        (
                                                            s.clearing_price_e8
                                                            - s.index_price_e8
                                                        )
                                                        if (
                                                            s.clearing_price_e8
                                                            >= s.index_price_e8
                                                        )
                                                        else (
                                                            s.index_price_e8
                                                            - s.clearing_price_e8
                                                        )
                                                    )
                                                )
                                                > (
                                                    s.index_price_e8
                                                    * s.max_oracle_move_bps
                                                )
                                            )
                                            and s.oracle_seen
                                        )
                                        else s.clearing_price_e8
                                    )
                                    - s.index_price_e8
                                )
                                * s.position_base_b
                            )
                            + s.collateral_e8_b
                        )
                        < (
                            0
                            if 10000 == 0
                            else (
                                (
                                    (
                                        9999
                                        + (
                                            (
                                                (
                                                    s.position_base_b
                                                    if (s.position_base_b >= 0)
                                                    else (0 - s.position_base_b)
                                                )
                                                * (
                                                    (
                                                        (
                                                            (
                                                                0
                                                                if 10000 == 0
                                                                else (
                                                                    (
                                                                        (
                                                                            s.index_price_e8
                                                                            * s.max_oracle_move_bps
                                                                        )
                                                                        // 10000
                                                                    )
                                                                    + (
                                                                        1
                                                                        if (
                                                                            (
                                                                                s.index_price_e8
                                                                                * s.max_oracle_move_bps
                                                                            )
                                                                            % 10000
                                                                        )
                                                                        < 0
                                                                        else 0
                                                                    )
                                                                )
                                                            )
                                                            + s.index_price_e8
                                                        )
                                                        if (
                                                            s.clearing_price_e8
                                                            >= s.index_price_e8
                                                        )
                                                        else (
                                                            s.index_price_e8
                                                            - (
                                                                0
                                                                if 10000 == 0
                                                                else (
                                                                    (
                                                                        (
                                                                            s.index_price_e8
                                                                            * s.max_oracle_move_bps
                                                                        )
                                                                        // 10000
                                                                    )
                                                                    + (
                                                                        1
                                                                        if (
                                                                            (
                                                                                s.index_price_e8
                                                                                * s.max_oracle_move_bps
                                                                            )
                                                                            % 10000
                                                                        )
                                                                        < 0
                                                                        else 0
                                                                    )
                                                                )
                                                            )
                                                        )
                                                    )
                                                    if (
                                                        (
                                                            (
                                                                10000
                                                                * (
                                                                    (
                                                                        s.clearing_price_e8
                                                                        - s.index_price_e8
                                                                    )
                                                                    if (
                                                                        s.clearing_price_e8
                                                                        >= s.index_price_e8
                                                                    )
                                                                    else (
                                                                        s.index_price_e8
                                                                        - s.clearing_price_e8
                                                                    )
                                                                )
                                                            )
                                                            > (
                                                                s.index_price_e8
                                                                * s.max_oracle_move_bps
                                                            )
                                                        )
                                                        and s.oracle_seen
                                                    )
                                                    else s.clearing_price_e8
                                                )
                                            )
                                            * s.maintenance_margin_bps
                                        )
                                    )
                                    // 10000
                                )
                                + (
                                    1
                                    if (
                                        (
                                            9999
                                            + (
                                                (
                                                    (
                                                        s.position_base_b
                                                        if (s.position_base_b >= 0)
                                                        else (0 - s.position_base_b)
                                                    )
                                                    * (
                                                        (
                                                            (
                                                                (
                                                                    0
                                                                    if 10000 == 0
                                                                    else (
                                                                        (
                                                                            (
                                                                                s.index_price_e8
                                                                                * s.max_oracle_move_bps
                                                                            )
                                                                            // 10000
                                                                        )
                                                                        + (
                                                                            1
                                                                            if (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                % 10000
                                                                            )
                                                                            < 0
                                                                            else 0
                                                                        )
                                                                    )
                                                                )
                                                                + s.index_price_e8
                                                            )
                                                            if (
                                                                s.clearing_price_e8
                                                                >= s.index_price_e8
                                                            )
                                                            else (
                                                                s.index_price_e8
                                                                - (
                                                                    0
                                                                    if 10000 == 0
                                                                    else (
                                                                        (
                                                                            (
                                                                                s.index_price_e8
                                                                                * s.max_oracle_move_bps
                                                                            )
                                                                            // 10000
                                                                        )
                                                                        + (
                                                                            1
                                                                            if (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                % 10000
                                                                            )
                                                                            < 0
                                                                            else 0
                                                                        )
                                                                    )
                                                                )
                                                            )
                                                        )
                                                        if (
                                                            (
                                                                (
                                                                    10000
                                                                    * (
                                                                        (
                                                                            s.clearing_price_e8
                                                                            - s.index_price_e8
                                                                        )
                                                                        if (
                                                                            s.clearing_price_e8
                                                                            >= s.index_price_e8
                                                                        )
                                                                        else (
                                                                            s.index_price_e8
                                                                            - s.clearing_price_e8
                                                                        )
                                                                    )
                                                                )
                                                                > (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                            )
                                                            and s.oracle_seen
                                                        )
                                                        else s.clearing_price_e8
                                                    )
                                                )
                                                * s.maintenance_margin_bps
                                            )
                                        )
                                        % 10000
                                    )
                                    < 0
                                    else 0
                                )
                            )
                        )
                    )
                    and (not (0 == s.position_base_b))
                )
            ),
            liquidation_penalty_bps=s.liquidation_penalty_bps,
            maintenance_margin_bps=s.maintenance_margin_bps,
            max_oracle_move_bps=s.max_oracle_move_bps,
            max_oracle_staleness_epochs=s.max_oracle_staleness_epochs,
            max_position_abs=s.max_position_abs,
            net_deposited_e8=s.net_deposited_e8,
            now_epoch=s.now_epoch,
            oracle_last_update_epoch=s.now_epoch,
            oracle_seen=True,
            position_base_a=(
                0
                if (
                    (
                        (
                            (
                                (
                                    (
                                        (
                                            (
                                                (
                                                    (
                                                        0
                                                        if 10000 == 0
                                                        else (
                                                            (
                                                                (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                                // 10000
                                                            )
                                                            + (
                                                                1
                                                                if (
                                                                    (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                    % 10000
                                                                )
                                                                < 0
                                                                else 0
                                                            )
                                                        )
                                                    )
                                                    + s.index_price_e8
                                                )
                                                if (
                                                    s.clearing_price_e8
                                                    >= s.index_price_e8
                                                )
                                                else (
                                                    s.index_price_e8
                                                    - (
                                                        0
                                                        if 10000 == 0
                                                        else (
                                                            (
                                                                (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                                // 10000
                                                            )
                                                            + (
                                                                1
                                                                if (
                                                                    (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                    % 10000
                                                                )
                                                                < 0
                                                                else 0
                                                            )
                                                        )
                                                    )
                                                )
                                            )
                                            if (
                                                (
                                                    (
                                                        10000
                                                        * (
                                                            (
                                                                s.clearing_price_e8
                                                                - s.index_price_e8
                                                            )
                                                            if (
                                                                s.clearing_price_e8
                                                                >= s.index_price_e8
                                                            )
                                                            else (
                                                                s.index_price_e8
                                                                - s.clearing_price_e8
                                                            )
                                                        )
                                                    )
                                                    > (
                                                        s.index_price_e8
                                                        * s.max_oracle_move_bps
                                                    )
                                                )
                                                and s.oracle_seen
                                            )
                                            else s.clearing_price_e8
                                        )
                                        - s.index_price_e8
                                    )
                                    * s.position_base_a
                                )
                                + s.collateral_e8_a
                            )
                            < (
                                0
                                if 10000 == 0
                                else (
                                    (
                                        (
                                            9999
                                            + (
                                                (
                                                    (
                                                        s.position_base_a
                                                        if (s.position_base_a >= 0)
                                                        else (0 - s.position_base_a)
                                                    )
                                                    * (
                                                        (
                                                            (
                                                                (
                                                                    0
                                                                    if 10000 == 0
                                                                    else (
                                                                        (
                                                                            (
                                                                                s.index_price_e8
                                                                                * s.max_oracle_move_bps
                                                                            )
                                                                            // 10000
                                                                        )
                                                                        + (
                                                                            1
                                                                            if (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                % 10000
                                                                            )
                                                                            < 0
                                                                            else 0
                                                                        )
                                                                    )
                                                                )
                                                                + s.index_price_e8
                                                            )
                                                            if (
                                                                s.clearing_price_e8
                                                                >= s.index_price_e8
                                                            )
                                                            else (
                                                                s.index_price_e8
                                                                - (
                                                                    0
                                                                    if 10000 == 0
                                                                    else (
                                                                        (
                                                                            (
                                                                                s.index_price_e8
                                                                                * s.max_oracle_move_bps
                                                                            )
                                                                            // 10000
                                                                        )
                                                                        + (
                                                                            1
                                                                            if (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                % 10000
                                                                            )
                                                                            < 0
                                                                            else 0
                                                                        )
                                                                    )
                                                                )
                                                            )
                                                        )
                                                        if (
                                                            (
                                                                (
                                                                    10000
                                                                    * (
                                                                        (
                                                                            s.clearing_price_e8
                                                                            - s.index_price_e8
                                                                        )
                                                                        if (
                                                                            s.clearing_price_e8
                                                                            >= s.index_price_e8
                                                                        )
                                                                        else (
                                                                            s.index_price_e8
                                                                            - s.clearing_price_e8
                                                                        )
                                                                    )
                                                                )
                                                                > (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                            )
                                                            and s.oracle_seen
                                                        )
                                                        else s.clearing_price_e8
                                                    )
                                                )
                                                * s.maintenance_margin_bps
                                            )
                                        )
                                        // 10000
                                    )
                                    + (
                                        1
                                        if (
                                            (
                                                9999
                                                + (
                                                    (
                                                        (
                                                            s.position_base_a
                                                            if (s.position_base_a >= 0)
                                                            else (0 - s.position_base_a)
                                                        )
                                                        * (
                                                            (
                                                                (
                                                                    (
                                                                        0
                                                                        if 10000 == 0
                                                                        else (
                                                                            (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                // 10000
                                                                            )
                                                                            + (
                                                                                1
                                                                                if (
                                                                                    (
                                                                                        s.index_price_e8
                                                                                        * s.max_oracle_move_bps
                                                                                    )
                                                                                    % 10000
                                                                                )
                                                                                < 0
                                                                                else 0
                                                                            )
                                                                        )
                                                                    )
                                                                    + s.index_price_e8
                                                                )
                                                                if (
                                                                    s.clearing_price_e8
                                                                    >= s.index_price_e8
                                                                )
                                                                else (
                                                                    s.index_price_e8
                                                                    - (
                                                                        0
                                                                        if 10000 == 0
                                                                        else (
                                                                            (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                // 10000
                                                                            )
                                                                            + (
                                                                                1
                                                                                if (
                                                                                    (
                                                                                        s.index_price_e8
                                                                                        * s.max_oracle_move_bps
                                                                                    )
                                                                                    % 10000
                                                                                )
                                                                                < 0
                                                                                else 0
                                                                            )
                                                                        )
                                                                    )
                                                                )
                                                            )
                                                            if (
                                                                (
                                                                    (
                                                                        10000
                                                                        * (
                                                                            (
                                                                                s.clearing_price_e8
                                                                                - s.index_price_e8
                                                                            )
                                                                            if (
                                                                                s.clearing_price_e8
                                                                                >= s.index_price_e8
                                                                            )
                                                                            else (
                                                                                s.index_price_e8
                                                                                - s.clearing_price_e8
                                                                            )
                                                                        )
                                                                    )
                                                                    > (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                )
                                                                and s.oracle_seen
                                                            )
                                                            else s.clearing_price_e8
                                                        )
                                                    )
                                                    * s.maintenance_margin_bps
                                                )
                                            )
                                            % 10000
                                        )
                                        < 0
                                        else 0
                                    )
                                )
                            )
                        )
                        and (not (0 == s.position_base_a))
                    )
                    or (
                        (
                            (
                                (
                                    (
                                        (
                                            (
                                                (
                                                    (
                                                        0
                                                        if 10000 == 0
                                                        else (
                                                            (
                                                                (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                                // 10000
                                                            )
                                                            + (
                                                                1
                                                                if (
                                                                    (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                    % 10000
                                                                )
                                                                < 0
                                                                else 0
                                                            )
                                                        )
                                                    )
                                                    + s.index_price_e8
                                                )
                                                if (
                                                    s.clearing_price_e8
                                                    >= s.index_price_e8
                                                )
                                                else (
                                                    s.index_price_e8
                                                    - (
                                                        0
                                                        if 10000 == 0
                                                        else (
                                                            (
                                                                (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                                // 10000
                                                            )
                                                            + (
                                                                1
                                                                if (
                                                                    (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                    % 10000
                                                                )
                                                                < 0
                                                                else 0
                                                            )
                                                        )
                                                    )
                                                )
                                            )
                                            if (
                                                (
                                                    (
                                                        10000
                                                        * (
                                                            (
                                                                s.clearing_price_e8
                                                                - s.index_price_e8
                                                            )
                                                            if (
                                                                s.clearing_price_e8
                                                                >= s.index_price_e8
                                                            )
                                                            else (
                                                                s.index_price_e8
                                                                - s.clearing_price_e8
                                                            )
                                                        )
                                                    )
                                                    > (
                                                        s.index_price_e8
                                                        * s.max_oracle_move_bps
                                                    )
                                                )
                                                and s.oracle_seen
                                            )
                                            else s.clearing_price_e8
                                        )
                                        - s.index_price_e8
                                    )
                                    * s.position_base_b
                                )
                                + s.collateral_e8_b
                            )
                            < (
                                0
                                if 10000 == 0
                                else (
                                    (
                                        (
                                            9999
                                            + (
                                                (
                                                    (
                                                        s.position_base_b
                                                        if (s.position_base_b >= 0)
                                                        else (0 - s.position_base_b)
                                                    )
                                                    * (
                                                        (
                                                            (
                                                                (
                                                                    0
                                                                    if 10000 == 0
                                                                    else (
                                                                        (
                                                                            (
                                                                                s.index_price_e8
                                                                                * s.max_oracle_move_bps
                                                                            )
                                                                            // 10000
                                                                        )
                                                                        + (
                                                                            1
                                                                            if (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                % 10000
                                                                            )
                                                                            < 0
                                                                            else 0
                                                                        )
                                                                    )
                                                                )
                                                                + s.index_price_e8
                                                            )
                                                            if (
                                                                s.clearing_price_e8
                                                                >= s.index_price_e8
                                                            )
                                                            else (
                                                                s.index_price_e8
                                                                - (
                                                                    0
                                                                    if 10000 == 0
                                                                    else (
                                                                        (
                                                                            (
                                                                                s.index_price_e8
                                                                                * s.max_oracle_move_bps
                                                                            )
                                                                            // 10000
                                                                        )
                                                                        + (
                                                                            1
                                                                            if (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                % 10000
                                                                            )
                                                                            < 0
                                                                            else 0
                                                                        )
                                                                    )
                                                                )
                                                            )
                                                        )
                                                        if (
                                                            (
                                                                (
                                                                    10000
                                                                    * (
                                                                        (
                                                                            s.clearing_price_e8
                                                                            - s.index_price_e8
                                                                        )
                                                                        if (
                                                                            s.clearing_price_e8
                                                                            >= s.index_price_e8
                                                                        )
                                                                        else (
                                                                            s.index_price_e8
                                                                            - s.clearing_price_e8
                                                                        )
                                                                    )
                                                                )
                                                                > (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                            )
                                                            and s.oracle_seen
                                                        )
                                                        else s.clearing_price_e8
                                                    )
                                                )
                                                * s.maintenance_margin_bps
                                            )
                                        )
                                        // 10000
                                    )
                                    + (
                                        1
                                        if (
                                            (
                                                9999
                                                + (
                                                    (
                                                        (
                                                            s.position_base_b
                                                            if (s.position_base_b >= 0)
                                                            else (0 - s.position_base_b)
                                                        )
                                                        * (
                                                            (
                                                                (
                                                                    (
                                                                        0
                                                                        if 10000 == 0
                                                                        else (
                                                                            (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                // 10000
                                                                            )
                                                                            + (
                                                                                1
                                                                                if (
                                                                                    (
                                                                                        s.index_price_e8
                                                                                        * s.max_oracle_move_bps
                                                                                    )
                                                                                    % 10000
                                                                                )
                                                                                < 0
                                                                                else 0
                                                                            )
                                                                        )
                                                                    )
                                                                    + s.index_price_e8
                                                                )
                                                                if (
                                                                    s.clearing_price_e8
                                                                    >= s.index_price_e8
                                                                )
                                                                else (
                                                                    s.index_price_e8
                                                                    - (
                                                                        0
                                                                        if 10000 == 0
                                                                        else (
                                                                            (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                // 10000
                                                                            )
                                                                            + (
                                                                                1
                                                                                if (
                                                                                    (
                                                                                        s.index_price_e8
                                                                                        * s.max_oracle_move_bps
                                                                                    )
                                                                                    % 10000
                                                                                )
                                                                                < 0
                                                                                else 0
                                                                            )
                                                                        )
                                                                    )
                                                                )
                                                            )
                                                            if (
                                                                (
                                                                    (
                                                                        10000
                                                                        * (
                                                                            (
                                                                                s.clearing_price_e8
                                                                                - s.index_price_e8
                                                                            )
                                                                            if (
                                                                                s.clearing_price_e8
                                                                                >= s.index_price_e8
                                                                            )
                                                                            else (
                                                                                s.index_price_e8
                                                                                - s.clearing_price_e8
                                                                            )
                                                                        )
                                                                    )
                                                                    > (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                )
                                                                and s.oracle_seen
                                                            )
                                                            else s.clearing_price_e8
                                                        )
                                                    )
                                                    * s.maintenance_margin_bps
                                                )
                                            )
                                            % 10000
                                        )
                                        < 0
                                        else 0
                                    )
                                )
                            )
                        )
                        and (not (0 == s.position_base_b))
                    )
                )
                else s.position_base_a
            ),
            position_base_b=(
                0
                if (
                    (
                        (
                            (
                                (
                                    (
                                        (
                                            (
                                                (
                                                    (
                                                        0
                                                        if 10000 == 0
                                                        else (
                                                            (
                                                                (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                                // 10000
                                                            )
                                                            + (
                                                                1
                                                                if (
                                                                    (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                    % 10000
                                                                )
                                                                < 0
                                                                else 0
                                                            )
                                                        )
                                                    )
                                                    + s.index_price_e8
                                                )
                                                if (
                                                    s.clearing_price_e8
                                                    >= s.index_price_e8
                                                )
                                                else (
                                                    s.index_price_e8
                                                    - (
                                                        0
                                                        if 10000 == 0
                                                        else (
                                                            (
                                                                (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                                // 10000
                                                            )
                                                            + (
                                                                1
                                                                if (
                                                                    (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                    % 10000
                                                                )
                                                                < 0
                                                                else 0
                                                            )
                                                        )
                                                    )
                                                )
                                            )
                                            if (
                                                (
                                                    (
                                                        10000
                                                        * (
                                                            (
                                                                s.clearing_price_e8
                                                                - s.index_price_e8
                                                            )
                                                            if (
                                                                s.clearing_price_e8
                                                                >= s.index_price_e8
                                                            )
                                                            else (
                                                                s.index_price_e8
                                                                - s.clearing_price_e8
                                                            )
                                                        )
                                                    )
                                                    > (
                                                        s.index_price_e8
                                                        * s.max_oracle_move_bps
                                                    )
                                                )
                                                and s.oracle_seen
                                            )
                                            else s.clearing_price_e8
                                        )
                                        - s.index_price_e8
                                    )
                                    * s.position_base_a
                                )
                                + s.collateral_e8_a
                            )
                            < (
                                0
                                if 10000 == 0
                                else (
                                    (
                                        (
                                            9999
                                            + (
                                                (
                                                    (
                                                        s.position_base_a
                                                        if (s.position_base_a >= 0)
                                                        else (0 - s.position_base_a)
                                                    )
                                                    * (
                                                        (
                                                            (
                                                                (
                                                                    0
                                                                    if 10000 == 0
                                                                    else (
                                                                        (
                                                                            (
                                                                                s.index_price_e8
                                                                                * s.max_oracle_move_bps
                                                                            )
                                                                            // 10000
                                                                        )
                                                                        + (
                                                                            1
                                                                            if (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                % 10000
                                                                            )
                                                                            < 0
                                                                            else 0
                                                                        )
                                                                    )
                                                                )
                                                                + s.index_price_e8
                                                            )
                                                            if (
                                                                s.clearing_price_e8
                                                                >= s.index_price_e8
                                                            )
                                                            else (
                                                                s.index_price_e8
                                                                - (
                                                                    0
                                                                    if 10000 == 0
                                                                    else (
                                                                        (
                                                                            (
                                                                                s.index_price_e8
                                                                                * s.max_oracle_move_bps
                                                                            )
                                                                            // 10000
                                                                        )
                                                                        + (
                                                                            1
                                                                            if (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                % 10000
                                                                            )
                                                                            < 0
                                                                            else 0
                                                                        )
                                                                    )
                                                                )
                                                            )
                                                        )
                                                        if (
                                                            (
                                                                (
                                                                    10000
                                                                    * (
                                                                        (
                                                                            s.clearing_price_e8
                                                                            - s.index_price_e8
                                                                        )
                                                                        if (
                                                                            s.clearing_price_e8
                                                                            >= s.index_price_e8
                                                                        )
                                                                        else (
                                                                            s.index_price_e8
                                                                            - s.clearing_price_e8
                                                                        )
                                                                    )
                                                                )
                                                                > (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                            )
                                                            and s.oracle_seen
                                                        )
                                                        else s.clearing_price_e8
                                                    )
                                                )
                                                * s.maintenance_margin_bps
                                            )
                                        )
                                        // 10000
                                    )
                                    + (
                                        1
                                        if (
                                            (
                                                9999
                                                + (
                                                    (
                                                        (
                                                            s.position_base_a
                                                            if (s.position_base_a >= 0)
                                                            else (0 - s.position_base_a)
                                                        )
                                                        * (
                                                            (
                                                                (
                                                                    (
                                                                        0
                                                                        if 10000 == 0
                                                                        else (
                                                                            (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                // 10000
                                                                            )
                                                                            + (
                                                                                1
                                                                                if (
                                                                                    (
                                                                                        s.index_price_e8
                                                                                        * s.max_oracle_move_bps
                                                                                    )
                                                                                    % 10000
                                                                                )
                                                                                < 0
                                                                                else 0
                                                                            )
                                                                        )
                                                                    )
                                                                    + s.index_price_e8
                                                                )
                                                                if (
                                                                    s.clearing_price_e8
                                                                    >= s.index_price_e8
                                                                )
                                                                else (
                                                                    s.index_price_e8
                                                                    - (
                                                                        0
                                                                        if 10000 == 0
                                                                        else (
                                                                            (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                // 10000
                                                                            )
                                                                            + (
                                                                                1
                                                                                if (
                                                                                    (
                                                                                        s.index_price_e8
                                                                                        * s.max_oracle_move_bps
                                                                                    )
                                                                                    % 10000
                                                                                )
                                                                                < 0
                                                                                else 0
                                                                            )
                                                                        )
                                                                    )
                                                                )
                                                            )
                                                            if (
                                                                (
                                                                    (
                                                                        10000
                                                                        * (
                                                                            (
                                                                                s.clearing_price_e8
                                                                                - s.index_price_e8
                                                                            )
                                                                            if (
                                                                                s.clearing_price_e8
                                                                                >= s.index_price_e8
                                                                            )
                                                                            else (
                                                                                s.index_price_e8
                                                                                - s.clearing_price_e8
                                                                            )
                                                                        )
                                                                    )
                                                                    > (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                )
                                                                and s.oracle_seen
                                                            )
                                                            else s.clearing_price_e8
                                                        )
                                                    )
                                                    * s.maintenance_margin_bps
                                                )
                                            )
                                            % 10000
                                        )
                                        < 0
                                        else 0
                                    )
                                )
                            )
                        )
                        and (not (0 == s.position_base_a))
                    )
                    or (
                        (
                            (
                                (
                                    (
                                        (
                                            (
                                                (
                                                    (
                                                        0
                                                        if 10000 == 0
                                                        else (
                                                            (
                                                                (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                                // 10000
                                                            )
                                                            + (
                                                                1
                                                                if (
                                                                    (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                    % 10000
                                                                )
                                                                < 0
                                                                else 0
                                                            )
                                                        )
                                                    )
                                                    + s.index_price_e8
                                                )
                                                if (
                                                    s.clearing_price_e8
                                                    >= s.index_price_e8
                                                )
                                                else (
                                                    s.index_price_e8
                                                    - (
                                                        0
                                                        if 10000 == 0
                                                        else (
                                                            (
                                                                (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                                // 10000
                                                            )
                                                            + (
                                                                1
                                                                if (
                                                                    (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                    % 10000
                                                                )
                                                                < 0
                                                                else 0
                                                            )
                                                        )
                                                    )
                                                )
                                            )
                                            if (
                                                (
                                                    (
                                                        10000
                                                        * (
                                                            (
                                                                s.clearing_price_e8
                                                                - s.index_price_e8
                                                            )
                                                            if (
                                                                s.clearing_price_e8
                                                                >= s.index_price_e8
                                                            )
                                                            else (
                                                                s.index_price_e8
                                                                - s.clearing_price_e8
                                                            )
                                                        )
                                                    )
                                                    > (
                                                        s.index_price_e8
                                                        * s.max_oracle_move_bps
                                                    )
                                                )
                                                and s.oracle_seen
                                            )
                                            else s.clearing_price_e8
                                        )
                                        - s.index_price_e8
                                    )
                                    * s.position_base_b
                                )
                                + s.collateral_e8_b
                            )
                            < (
                                0
                                if 10000 == 0
                                else (
                                    (
                                        (
                                            9999
                                            + (
                                                (
                                                    (
                                                        s.position_base_b
                                                        if (s.position_base_b >= 0)
                                                        else (0 - s.position_base_b)
                                                    )
                                                    * (
                                                        (
                                                            (
                                                                (
                                                                    0
                                                                    if 10000 == 0
                                                                    else (
                                                                        (
                                                                            (
                                                                                s.index_price_e8
                                                                                * s.max_oracle_move_bps
                                                                            )
                                                                            // 10000
                                                                        )
                                                                        + (
                                                                            1
                                                                            if (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                % 10000
                                                                            )
                                                                            < 0
                                                                            else 0
                                                                        )
                                                                    )
                                                                )
                                                                + s.index_price_e8
                                                            )
                                                            if (
                                                                s.clearing_price_e8
                                                                >= s.index_price_e8
                                                            )
                                                            else (
                                                                s.index_price_e8
                                                                - (
                                                                    0
                                                                    if 10000 == 0
                                                                    else (
                                                                        (
                                                                            (
                                                                                s.index_price_e8
                                                                                * s.max_oracle_move_bps
                                                                            )
                                                                            // 10000
                                                                        )
                                                                        + (
                                                                            1
                                                                            if (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                % 10000
                                                                            )
                                                                            < 0
                                                                            else 0
                                                                        )
                                                                    )
                                                                )
                                                            )
                                                        )
                                                        if (
                                                            (
                                                                (
                                                                    10000
                                                                    * (
                                                                        (
                                                                            s.clearing_price_e8
                                                                            - s.index_price_e8
                                                                        )
                                                                        if (
                                                                            s.clearing_price_e8
                                                                            >= s.index_price_e8
                                                                        )
                                                                        else (
                                                                            s.index_price_e8
                                                                            - s.clearing_price_e8
                                                                        )
                                                                    )
                                                                )
                                                                > (
                                                                    s.index_price_e8
                                                                    * s.max_oracle_move_bps
                                                                )
                                                            )
                                                            and s.oracle_seen
                                                        )
                                                        else s.clearing_price_e8
                                                    )
                                                )
                                                * s.maintenance_margin_bps
                                            )
                                        )
                                        // 10000
                                    )
                                    + (
                                        1
                                        if (
                                            (
                                                9999
                                                + (
                                                    (
                                                        (
                                                            s.position_base_b
                                                            if (s.position_base_b >= 0)
                                                            else (0 - s.position_base_b)
                                                        )
                                                        * (
                                                            (
                                                                (
                                                                    (
                                                                        0
                                                                        if 10000 == 0
                                                                        else (
                                                                            (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                // 10000
                                                                            )
                                                                            + (
                                                                                1
                                                                                if (
                                                                                    (
                                                                                        s.index_price_e8
                                                                                        * s.max_oracle_move_bps
                                                                                    )
                                                                                    % 10000
                                                                                )
                                                                                < 0
                                                                                else 0
                                                                            )
                                                                        )
                                                                    )
                                                                    + s.index_price_e8
                                                                )
                                                                if (
                                                                    s.clearing_price_e8
                                                                    >= s.index_price_e8
                                                                )
                                                                else (
                                                                    s.index_price_e8
                                                                    - (
                                                                        0
                                                                        if 10000 == 0
                                                                        else (
                                                                            (
                                                                                (
                                                                                    s.index_price_e8
                                                                                    * s.max_oracle_move_bps
                                                                                )
                                                                                // 10000
                                                                            )
                                                                            + (
                                                                                1
                                                                                if (
                                                                                    (
                                                                                        s.index_price_e8
                                                                                        * s.max_oracle_move_bps
                                                                                    )
                                                                                    % 10000
                                                                                )
                                                                                < 0
                                                                                else 0
                                                                            )
                                                                        )
                                                                    )
                                                                )
                                                            )
                                                            if (
                                                                (
                                                                    (
                                                                        10000
                                                                        * (
                                                                            (
                                                                                s.clearing_price_e8
                                                                                - s.index_price_e8
                                                                            )
                                                                            if (
                                                                                s.clearing_price_e8
                                                                                >= s.index_price_e8
                                                                            )
                                                                            else (
                                                                                s.index_price_e8
                                                                                - s.clearing_price_e8
                                                                            )
                                                                        )
                                                                    )
                                                                    > (
                                                                        s.index_price_e8
                                                                        * s.max_oracle_move_bps
                                                                    )
                                                                )
                                                                and s.oracle_seen
                                                            )
                                                            else s.clearing_price_e8
                                                        )
                                                    )
                                                    * s.maintenance_margin_bps
                                                )
                                            )
                                            % 10000
                                        )
                                        < 0
                                        else 0
                                    )
                                )
                            )
                        )
                        and (not (0 == s.position_base_b))
                    )
                )
                else s.position_base_b
            ),
        )
        effects = {
            "collateral_after_a": new_state.collateral_e8_a,
            "collateral_after_b": new_state.collateral_e8_b,
            "event": "EpochSettled",
            "fee_pool_after": new_state.fee_pool_e8,
            "liquidated": new_state.liquidated_this_step,
            "oracle_fresh": True,
        }
        ok, failed = check_invariants(new_state)
        if not ok:
            return StepResult(ok=False, error=f"post-invariant violated: {failed}")
        return StepResult(ok=True, state=new_state, effects=effects)
    elif cmd.tag == "withdraw_collateral_a":
        if "amount_e8" not in cmd.args or not (
            isinstance(cmd.args["amount_e8"], int)
            and not isinstance(cmd.args["amount_e8"], bool)
            and 1 <= cmd.args["amount_e8"] <= 1000000000000000000
        ):
            return StepResult(ok=False, error="invalid param amount_e8")
        if "auth_ok" not in cmd.args or not (isinstance(cmd.args["auth_ok"], bool)):
            return StepResult(ok=False, error="invalid param auth_ok")
        if not (
            (cmd.args["amount_e8"] <= s.collateral_e8_a)
            and (True == cmd.args["auth_ok"])
            and (
                (0 == s.position_base_a)
                or (
                    (
                        (s.now_epoch - s.oracle_last_update_epoch)
                        <= s.max_oracle_staleness_epochs
                    )
                    and (
                        (s.collateral_e8_a - cmd.args["amount_e8"])
                        >= (
                            0
                            if 10000 == 0
                            else (
                                (
                                    (
                                        9999
                                        + (
                                            (
                                                (
                                                    s.position_base_a
                                                    if (s.position_base_a >= 0)
                                                    else (0 - s.position_base_a)
                                                )
                                                * s.index_price_e8
                                            )
                                            * s.maintenance_margin_bps
                                        )
                                    )
                                    // 10000
                                )
                                + (
                                    1
                                    if (
                                        (
                                            9999
                                            + (
                                                (
                                                    (
                                                        s.position_base_a
                                                        if (s.position_base_a >= 0)
                                                        else (0 - s.position_base_a)
                                                    )
                                                    * s.index_price_e8
                                                )
                                                * s.maintenance_margin_bps
                                            )
                                        )
                                        % 10000
                                    )
                                    < 0
                                    else 0
                                )
                            )
                        )
                    )
                    and s.oracle_seen
                )
            )
        ):
            return StepResult(ok=False, error="guard failed for withdraw_collateral_a")
        # Compute updates (simultaneous)
        new_state = State(
            breaker_active=s.breaker_active,
            breaker_last_trigger_epoch=s.breaker_last_trigger_epoch,
            clearing_price_e8=s.clearing_price_e8,
            clearing_price_epoch=s.clearing_price_epoch,
            clearing_price_seen=s.clearing_price_seen,
            collateral_e8_a=(s.collateral_e8_a - cmd.args["amount_e8"]),
            collateral_e8_b=s.collateral_e8_b,
            entry_price_e8_a=s.entry_price_e8_a,
            entry_price_e8_b=s.entry_price_e8_b,
            fee_pool_e8=s.fee_pool_e8,
            index_price_e8=s.index_price_e8,
            initial_margin_bps=s.initial_margin_bps,
            liquidated_this_step=False,
            liquidation_penalty_bps=s.liquidation_penalty_bps,
            maintenance_margin_bps=s.maintenance_margin_bps,
            max_oracle_move_bps=s.max_oracle_move_bps,
            max_oracle_staleness_epochs=s.max_oracle_staleness_epochs,
            max_position_abs=s.max_position_abs,
            net_deposited_e8=(s.net_deposited_e8 - cmd.args["amount_e8"]),
            now_epoch=s.now_epoch,
            oracle_last_update_epoch=s.oracle_last_update_epoch,
            oracle_seen=s.oracle_seen,
            position_base_a=s.position_base_a,
            position_base_b=s.position_base_b,
        )
        effects = {
            "collateral_after_a": new_state.collateral_e8_a,
            "collateral_after_b": new_state.collateral_e8_b,
            "event": "CollateralWithdrawnA",
            "fee_pool_after": new_state.fee_pool_e8,
            "liquidated": new_state.liquidated_this_step,
            "oracle_fresh": new_state.oracle_seen,
        }
        ok, failed = check_invariants(new_state)
        if not ok:
            return StepResult(ok=False, error=f"post-invariant violated: {failed}")
        return StepResult(ok=True, state=new_state, effects=effects)
    elif cmd.tag == "withdraw_collateral_b":
        if "amount_e8" not in cmd.args or not (
            isinstance(cmd.args["amount_e8"], int)
            and not isinstance(cmd.args["amount_e8"], bool)
            and 1 <= cmd.args["amount_e8"] <= 1000000000000000000
        ):
            return StepResult(ok=False, error="invalid param amount_e8")
        if "auth_ok" not in cmd.args or not (isinstance(cmd.args["auth_ok"], bool)):
            return StepResult(ok=False, error="invalid param auth_ok")
        if not (
            (cmd.args["amount_e8"] <= s.collateral_e8_b)
            and (True == cmd.args["auth_ok"])
            and (
                (0 == s.position_base_b)
                or (
                    (
                        (s.now_epoch - s.oracle_last_update_epoch)
                        <= s.max_oracle_staleness_epochs
                    )
                    and (
                        (s.collateral_e8_b - cmd.args["amount_e8"])
                        >= (
                            0
                            if 10000 == 0
                            else (
                                (
                                    (
                                        9999
                                        + (
                                            (
                                                (
                                                    s.position_base_b
                                                    if (s.position_base_b >= 0)
                                                    else (0 - s.position_base_b)
                                                )
                                                * s.index_price_e8
                                            )
                                            * s.maintenance_margin_bps
                                        )
                                    )
                                    // 10000
                                )
                                + (
                                    1
                                    if (
                                        (
                                            9999
                                            + (
                                                (
                                                    (
                                                        s.position_base_b
                                                        if (s.position_base_b >= 0)
                                                        else (0 - s.position_base_b)
                                                    )
                                                    * s.index_price_e8
                                                )
                                                * s.maintenance_margin_bps
                                            )
                                        )
                                        % 10000
                                    )
                                    < 0
                                    else 0
                                )
                            )
                        )
                    )
                    and s.oracle_seen
                )
            )
        ):
            return StepResult(ok=False, error="guard failed for withdraw_collateral_b")
        # Compute updates (simultaneous)
        new_state = State(
            breaker_active=s.breaker_active,
            breaker_last_trigger_epoch=s.breaker_last_trigger_epoch,
            clearing_price_e8=s.clearing_price_e8,
            clearing_price_epoch=s.clearing_price_epoch,
            clearing_price_seen=s.clearing_price_seen,
            collateral_e8_a=s.collateral_e8_a,
            collateral_e8_b=(s.collateral_e8_b - cmd.args["amount_e8"]),
            entry_price_e8_a=s.entry_price_e8_a,
            entry_price_e8_b=s.entry_price_e8_b,
            fee_pool_e8=s.fee_pool_e8,
            index_price_e8=s.index_price_e8,
            initial_margin_bps=s.initial_margin_bps,
            liquidated_this_step=False,
            liquidation_penalty_bps=s.liquidation_penalty_bps,
            maintenance_margin_bps=s.maintenance_margin_bps,
            max_oracle_move_bps=s.max_oracle_move_bps,
            max_oracle_staleness_epochs=s.max_oracle_staleness_epochs,
            max_position_abs=s.max_position_abs,
            net_deposited_e8=(s.net_deposited_e8 - cmd.args["amount_e8"]),
            now_epoch=s.now_epoch,
            oracle_last_update_epoch=s.oracle_last_update_epoch,
            oracle_seen=s.oracle_seen,
            position_base_a=s.position_base_a,
            position_base_b=s.position_base_b,
        )
        effects = {
            "collateral_after_a": new_state.collateral_e8_a,
            "collateral_after_b": new_state.collateral_e8_b,
            "event": "CollateralWithdrawnB",
            "fee_pool_after": new_state.fee_pool_e8,
            "liquidated": new_state.liquidated_this_step,
            "oracle_fresh": new_state.oracle_seen,
        }
        ok, failed = check_invariants(new_state)
        if not ok:
            return StepResult(ok=False, error=f"post-invariant violated: {failed}")
        return StepResult(ok=True, state=new_state, effects=effects)
    else:
        return StepResult(ok=False, error=f"unknown action: {cmd.tag}")


# === Hypothesis test scaffolding ===
# Uncomment and install hypothesis to use property-based testing

# from hypothesis import given, strategies as st
# from hypothesis.stateful import RuleBasedStateMachine, rule, initialize
#
# class ModelStateMachine(RuleBasedStateMachine):
#     def __init__(self):
#         super().__init__()
#         self.state = init_state()
#
#     @initialize()
#     def init(self):
#         self.state = init_state()
#         ok, _ = check_invariants(self.state)
#         assert ok, 'init violates invariants'
#
#     # @rule(delta=st.integers())
#     # def advance_epoch(self, delta):
#     #     cmd = Command(tag='advance_epoch', args={'delta': delta})
#     #     result = step(self.state, cmd)
#     #     if result.ok:
#     #         self.state = result.state
#
#     # @rule(auth_ok=st.integers())
#     # def clear_breaker(self, auth_ok):
#     #     cmd = Command(tag='clear_breaker', args={'auth_ok': auth_ok})
#     #     result = step(self.state, cmd)
#     #     if result.ok:
#     #         self.state = result.state
#
#     # @rule(amount_e8=st.integers(), auth_ok=st.integers())
#     # def deposit_collateral_a(self, amount_e8, auth_ok):
#     #     cmd = Command(tag='deposit_collateral_a', args={'amount_e8': amount_e8, 'auth_ok': auth_ok})
#     #     result = step(self.state, cmd)
#     #     if result.ok:
#     #         self.state = result.state
#
#     # @rule(amount_e8=st.integers(), auth_ok=st.integers())
#     # def deposit_collateral_b(self, amount_e8, auth_ok):
#     #     cmd = Command(tag='deposit_collateral_b', args={'amount_e8': amount_e8, 'auth_ok': auth_ok})
#     #     result = step(self.state, cmd)
#     #     if result.ok:
#     #         self.state = result.state
#
#     # @rule(price_e8=st.integers())
#     # def publish_clearing_price(self, price_e8):
#     #     cmd = Command(tag='publish_clearing_price', args={'price_e8': price_e8})
#     #     result = step(self.state, cmd)
#     #     if result.ok:
#     #         self.state = result.state
#
#     # @rule(new_position_base_a=st.integers(), auth_ok=st.integers())
#     # def set_position_pair(self, new_position_base_a, auth_ok):
#     #     cmd = Command(tag='set_position_pair', args={'new_position_base_a': new_position_base_a, 'auth_ok': auth_ok})
#     #     result = step(self.state, cmd)
#     #     if result.ok:
#     #         self.state = result.state
#
#     # @rule()
#     # def settle_epoch(self, ):
#     #     cmd = Command(tag='settle_epoch', args={})
#     #     result = step(self.state, cmd)
#     #     if result.ok:
#     #         self.state = result.state
#
#     # @rule(amount_e8=st.integers(), auth_ok=st.integers())
#     # def withdraw_collateral_a(self, amount_e8, auth_ok):
#     #     cmd = Command(tag='withdraw_collateral_a', args={'amount_e8': amount_e8, 'auth_ok': auth_ok})
#     #     result = step(self.state, cmd)
#     #     if result.ok:
#     #         self.state = result.state
#
#     # @rule(amount_e8=st.integers(), auth_ok=st.integers())
#     # def withdraw_collateral_b(self, amount_e8, auth_ok):
#     #     cmd = Command(tag='withdraw_collateral_b', args={'amount_e8': amount_e8, 'auth_ok': auth_ok})
#     #     result = step(self.state, cmd)
#     #     if result.ok:
#     #         self.state = result.state
#
# TestModel = ModelStateMachine.TestCase


def replay_trace(commands: list[tuple[str, dict[str, Any]]]) -> list[StepResult]:
    """Replay a trace of commands and return results."""
    results: list[StepResult] = []
    s = init_state()
    for tag, args in commands:
        cmd = Command(tag=tag, args=args)
        result = step(s, cmd)
        results.append(result)
        if result.ok and result.state is not None:
            s = result.state
        else:
            break
    return results


if __name__ == "__main__":
    # Quick sanity check
    s0 = init_state()
    ok, failed = check_invariants(s0)
    print(f"Initial state: {s0}")
    print(f"Invariants OK: {ok}")
    if not ok:
        print(f"  Failed: {failed}")
