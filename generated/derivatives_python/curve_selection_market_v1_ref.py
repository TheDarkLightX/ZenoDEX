"""
Auto-generated Python reference model for: curve_selection_market_v1
IR hash: sha256:be93044dc15dfdafb8c13c2fe3a3be1bfd7c4abac1be3b2f4155b142044397c3

Generated from the YAML kernel spec by the repo's optional private toolchain.

This file is standalone and has no runtime dependency on the generator/toolchain.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Literal, Mapping


@dataclass(frozen=True)
class State:
    """Model state."""

    active_curve: int
    epochs_since_start: int
    prediction_epoch: int
    protocol_fee_bps: int
    protocol_fee_pool: int
    revenue_0: int
    revenue_1: int
    revenue_2: int
    revenue_3: int
    revenue_4: int
    settlement_epoch_interval: int
    stakes_0: int
    stakes_1: int
    stakes_2: int
    stakes_3: int
    stakes_4: int
    total_staked: int
    winner_payout_pool: int


@dataclass(frozen=True)
class Command:
    """Command to execute."""

    tag: Literal(
        "admin_set_interval",
        "advance_epoch",
        "settle_prediction",
        "stake_on_curve",
        "unstake",
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
        active_curve=0,
        epochs_since_start=0,
        prediction_epoch=0,
        protocol_fee_bps=200,
        protocol_fee_pool=0,
        revenue_0=0,
        revenue_1=0,
        revenue_2=0,
        revenue_3=0,
        revenue_4=0,
        settlement_epoch_interval=10,
        stakes_0=0,
        stakes_1=0,
        stakes_2=0,
        stakes_3=0,
        stakes_4=0,
        total_staked=0,
        winner_payout_pool=0,
    )


def check_invariants(s: State) -> tuple[bool, str | None]:
    """Check all invariants. Returns (ok, first_failed_id)."""
    if not (
        isinstance(s.active_curve, int)
        and not isinstance(s.active_curve, bool)
        and 0 <= s.active_curve <= 4
    ):
        return False, "domain_active_curve"
    if not (
        isinstance(s.epochs_since_start, int)
        and not isinstance(s.epochs_since_start, bool)
        and 0 <= s.epochs_since_start <= 1000000000
    ):
        return False, "domain_epochs_since_start"
    if not (
        isinstance(s.prediction_epoch, int)
        and not isinstance(s.prediction_epoch, bool)
        and 0 <= s.prediction_epoch <= 1000000000
    ):
        return False, "domain_prediction_epoch"
    if not (
        isinstance(s.protocol_fee_bps, int)
        and not isinstance(s.protocol_fee_bps, bool)
        and 0 <= s.protocol_fee_bps <= 10000
    ):
        return False, "domain_protocol_fee_bps"
    if not (
        isinstance(s.protocol_fee_pool, int)
        and not isinstance(s.protocol_fee_pool, bool)
        and 0 <= s.protocol_fee_pool <= 1000000000000
    ):
        return False, "domain_protocol_fee_pool"
    if not (
        isinstance(s.revenue_0, int)
        and not isinstance(s.revenue_0, bool)
        and 0 <= s.revenue_0 <= 1000000000000
    ):
        return False, "domain_revenue_0"
    if not (
        isinstance(s.revenue_1, int)
        and not isinstance(s.revenue_1, bool)
        and 0 <= s.revenue_1 <= 1000000000000
    ):
        return False, "domain_revenue_1"
    if not (
        isinstance(s.revenue_2, int)
        and not isinstance(s.revenue_2, bool)
        and 0 <= s.revenue_2 <= 1000000000000
    ):
        return False, "domain_revenue_2"
    if not (
        isinstance(s.revenue_3, int)
        and not isinstance(s.revenue_3, bool)
        and 0 <= s.revenue_3 <= 1000000000000
    ):
        return False, "domain_revenue_3"
    if not (
        isinstance(s.revenue_4, int)
        and not isinstance(s.revenue_4, bool)
        and 0 <= s.revenue_4 <= 1000000000000
    ):
        return False, "domain_revenue_4"
    if not (
        isinstance(s.settlement_epoch_interval, int)
        and not isinstance(s.settlement_epoch_interval, bool)
        and 1 <= s.settlement_epoch_interval <= 1000
    ):
        return False, "domain_settlement_epoch_interval"
    if not (
        isinstance(s.stakes_0, int)
        and not isinstance(s.stakes_0, bool)
        and 0 <= s.stakes_0 <= 1000000000000
    ):
        return False, "domain_stakes_0"
    if not (
        isinstance(s.stakes_1, int)
        and not isinstance(s.stakes_1, bool)
        and 0 <= s.stakes_1 <= 1000000000000
    ):
        return False, "domain_stakes_1"
    if not (
        isinstance(s.stakes_2, int)
        and not isinstance(s.stakes_2, bool)
        and 0 <= s.stakes_2 <= 1000000000000
    ):
        return False, "domain_stakes_2"
    if not (
        isinstance(s.stakes_3, int)
        and not isinstance(s.stakes_3, bool)
        and 0 <= s.stakes_3 <= 1000000000000
    ):
        return False, "domain_stakes_3"
    if not (
        isinstance(s.stakes_4, int)
        and not isinstance(s.stakes_4, bool)
        and 0 <= s.stakes_4 <= 1000000000000
    ):
        return False, "domain_stakes_4"
    if not (
        isinstance(s.total_staked, int)
        and not isinstance(s.total_staked, bool)
        and 0 <= s.total_staked <= 1000000000000
    ):
        return False, "domain_total_staked"
    if not (
        isinstance(s.winner_payout_pool, int)
        and not isinstance(s.winner_payout_pool, bool)
        and 0 <= s.winner_payout_pool <= 1000000000000
    ):
        return False, "domain_winner_payout_pool"
    if not ((s.active_curve <= 4) and (s.active_curve >= 0)):
        return False, "inv_curve_valid"
    if not ((s.protocol_fee_pool >= 0) and (s.winner_payout_pool >= 0)):
        return False, "inv_pools_nonneg"
    if not (
        (s.stakes_0 >= 0)
        and (s.stakes_1 >= 0)
        and (s.stakes_2 >= 0)
        and (s.stakes_3 >= 0)
        and (s.stakes_4 >= 0)
    ):
        return False, "inv_stakes_nonneg"
    if not (
        ((((s.stakes_0 + s.stakes_1) + s.stakes_2) + s.stakes_3) + s.stakes_4)
        == s.total_staked
    ):
        return False, "inv_total_staked_consistent"
    return True, None


def step(s: State, cmd: Command) -> StepResult:
    """Execute a step. Returns StepResult."""
    # Check pre-state invariants
    ok, failed = check_invariants(s)
    if not ok:
        return StepResult(ok=False, error=f"pre-invariant violated: {failed}")

    if cmd.tag == "admin_set_interval":
        if "new_interval" not in cmd.args or not (
            isinstance(cmd.args["new_interval"], int)
            and not isinstance(cmd.args["new_interval"], bool)
            and 1 <= cmd.args["new_interval"] <= 1000
        ):
            return StepResult(ok=False, error="invalid param new_interval")
        if "auth_ok" not in cmd.args or not (isinstance(cmd.args["auth_ok"], bool)):
            return StepResult(ok=False, error="invalid param auth_ok")
        if not (cmd.args["auth_ok"]):
            return StepResult(ok=False, error="guard failed for admin_set_interval")
        # Compute updates (simultaneous)
        new_state = State(
            active_curve=s.active_curve,
            epochs_since_start=s.epochs_since_start,
            prediction_epoch=s.prediction_epoch,
            protocol_fee_bps=s.protocol_fee_bps,
            protocol_fee_pool=s.protocol_fee_pool,
            revenue_0=s.revenue_0,
            revenue_1=s.revenue_1,
            revenue_2=s.revenue_2,
            revenue_3=s.revenue_3,
            revenue_4=s.revenue_4,
            settlement_epoch_interval=cmd.args["new_interval"],
            stakes_0=s.stakes_0,
            stakes_1=s.stakes_1,
            stakes_2=s.stakes_2,
            stakes_3=s.stakes_3,
            stakes_4=s.stakes_4,
            total_staked=s.total_staked,
            winner_payout_pool=s.winner_payout_pool,
        )
        effects = {
            "event": "IntervalSet",
            "payout_amount": 0,
            "winning_curve": -1,
        }
        ok, failed = check_invariants(new_state)
        if not ok:
            return StepResult(ok=False, error=f"post-invariant violated: {failed}")
        return StepResult(ok=True, state=new_state, effects=effects)
    elif cmd.tag == "advance_epoch":
        if "revenue_delta_0" not in cmd.args or not (
            isinstance(cmd.args["revenue_delta_0"], int)
            and not isinstance(cmd.args["revenue_delta_0"], bool)
            and 0 <= cmd.args["revenue_delta_0"] <= 1000000000000
        ):
            return StepResult(ok=False, error="invalid param revenue_delta_0")
        if "revenue_delta_1" not in cmd.args or not (
            isinstance(cmd.args["revenue_delta_1"], int)
            and not isinstance(cmd.args["revenue_delta_1"], bool)
            and 0 <= cmd.args["revenue_delta_1"] <= 1000000000000
        ):
            return StepResult(ok=False, error="invalid param revenue_delta_1")
        if "revenue_delta_2" not in cmd.args or not (
            isinstance(cmd.args["revenue_delta_2"], int)
            and not isinstance(cmd.args["revenue_delta_2"], bool)
            and 0 <= cmd.args["revenue_delta_2"] <= 1000000000000
        ):
            return StepResult(ok=False, error="invalid param revenue_delta_2")
        if "revenue_delta_3" not in cmd.args or not (
            isinstance(cmd.args["revenue_delta_3"], int)
            and not isinstance(cmd.args["revenue_delta_3"], bool)
            and 0 <= cmd.args["revenue_delta_3"] <= 1000000000000
        ):
            return StepResult(ok=False, error="invalid param revenue_delta_3")
        if "revenue_delta_4" not in cmd.args or not (
            isinstance(cmd.args["revenue_delta_4"], int)
            and not isinstance(cmd.args["revenue_delta_4"], bool)
            and 0 <= cmd.args["revenue_delta_4"] <= 1000000000000
        ):
            return StepResult(ok=False, error="invalid param revenue_delta_4")
        if not (
            (s.epochs_since_start < 1000000000)
            and ((cmd.args["revenue_delta_0"] + s.revenue_0) <= 1000000000000)
            and ((cmd.args["revenue_delta_1"] + s.revenue_1) <= 1000000000000)
            and ((cmd.args["revenue_delta_2"] + s.revenue_2) <= 1000000000000)
            and ((cmd.args["revenue_delta_3"] + s.revenue_3) <= 1000000000000)
            and ((cmd.args["revenue_delta_4"] + s.revenue_4) <= 1000000000000)
        ):
            return StepResult(ok=False, error="guard failed for advance_epoch")
        # Compute updates (simultaneous)
        new_state = State(
            active_curve=s.active_curve,
            epochs_since_start=(1 + s.epochs_since_start),
            prediction_epoch=s.prediction_epoch,
            protocol_fee_bps=s.protocol_fee_bps,
            protocol_fee_pool=s.protocol_fee_pool,
            revenue_0=(cmd.args["revenue_delta_0"] + s.revenue_0),
            revenue_1=(cmd.args["revenue_delta_1"] + s.revenue_1),
            revenue_2=(cmd.args["revenue_delta_2"] + s.revenue_2),
            revenue_3=(cmd.args["revenue_delta_3"] + s.revenue_3),
            revenue_4=(cmd.args["revenue_delta_4"] + s.revenue_4),
            settlement_epoch_interval=s.settlement_epoch_interval,
            stakes_0=s.stakes_0,
            stakes_1=s.stakes_1,
            stakes_2=s.stakes_2,
            stakes_3=s.stakes_3,
            stakes_4=s.stakes_4,
            total_staked=s.total_staked,
            winner_payout_pool=s.winner_payout_pool,
        )
        effects = {
            "event": "EpochAdvanced",
            "payout_amount": 0,
            "winning_curve": -1,
        }
        ok, failed = check_invariants(new_state)
        if not ok:
            return StepResult(ok=False, error=f"post-invariant violated: {failed}")
        return StepResult(ok=True, state=new_state, effects=effects)
    elif cmd.tag == "settle_prediction":
        if "winning_curve_id" not in cmd.args or not (
            isinstance(cmd.args["winning_curve_id"], int)
            and not isinstance(cmd.args["winning_curve_id"], bool)
            and 0 <= cmd.args["winning_curve_id"] <= 4
        ):
            return StepResult(ok=False, error="invalid param winning_curve_id")
        if "protocol_fee" not in cmd.args or not (
            isinstance(cmd.args["protocol_fee"], int)
            and not isinstance(cmd.args["protocol_fee"], bool)
            and 0 <= cmd.args["protocol_fee"] <= 1000000000000
        ):
            return StepResult(ok=False, error="invalid param protocol_fee")
        if not (
            (s.prediction_epoch < 1000000000)
            and ((cmd.args["protocol_fee"] + s.protocol_fee_pool) <= 1000000000000)
            and (
                cmd.args["protocol_fee"]
                <= (
                    s.total_staked
                    - (
                        s.stakes_0
                        if (0 == cmd.args["winning_curve_id"])
                        else (
                            s.stakes_1
                            if (1 == cmd.args["winning_curve_id"])
                            else (
                                s.stakes_2
                                if (2 == cmd.args["winning_curve_id"])
                                else (
                                    s.stakes_3
                                    if (3 == cmd.args["winning_curve_id"])
                                    else s.stakes_4
                                )
                            )
                        )
                    )
                )
            )
            and (s.epochs_since_start >= s.settlement_epoch_interval)
        ):
            return StepResult(ok=False, error="guard failed for settle_prediction")
        # Compute updates (simultaneous)
        new_state = State(
            active_curve=cmd.args["winning_curve_id"],
            epochs_since_start=0,
            prediction_epoch=(1 + s.prediction_epoch),
            protocol_fee_bps=s.protocol_fee_bps,
            protocol_fee_pool=(cmd.args["protocol_fee"] + s.protocol_fee_pool),
            revenue_0=0,
            revenue_1=0,
            revenue_2=0,
            revenue_3=0,
            revenue_4=0,
            settlement_epoch_interval=s.settlement_epoch_interval,
            stakes_0=(s.stakes_0 if (0 == cmd.args["winning_curve_id"]) else 0),
            stakes_1=(s.stakes_1 if (1 == cmd.args["winning_curve_id"]) else 0),
            stakes_2=(s.stakes_2 if (2 == cmd.args["winning_curve_id"]) else 0),
            stakes_3=(s.stakes_3 if (3 == cmd.args["winning_curve_id"]) else 0),
            stakes_4=(s.stakes_4 if (4 == cmd.args["winning_curve_id"]) else 0),
            total_staked=(
                s.stakes_0
                if (0 == cmd.args["winning_curve_id"])
                else (
                    s.stakes_1
                    if (1 == cmd.args["winning_curve_id"])
                    else (
                        s.stakes_2
                        if (2 == cmd.args["winning_curve_id"])
                        else (
                            s.stakes_3
                            if (3 == cmd.args["winning_curve_id"])
                            else s.stakes_4
                        )
                    )
                )
            ),
            winner_payout_pool=(
                (
                    s.total_staked
                    - (
                        s.stakes_0
                        if (0 == cmd.args["winning_curve_id"])
                        else (
                            s.stakes_1
                            if (1 == cmd.args["winning_curve_id"])
                            else (
                                s.stakes_2
                                if (2 == cmd.args["winning_curve_id"])
                                else (
                                    s.stakes_3
                                    if (3 == cmd.args["winning_curve_id"])
                                    else s.stakes_4
                                )
                            )
                        )
                    )
                )
                - cmd.args["protocol_fee"]
            ),
        )
        effects = {
            "event": "PredictionSettled",
            "payout_amount": 0,
            "winning_curve": cmd.args["winning_curve_id"],
        }
        ok, failed = check_invariants(new_state)
        if not ok:
            return StepResult(ok=False, error=f"post-invariant violated: {failed}")
        return StepResult(ok=True, state=new_state, effects=effects)
    elif cmd.tag == "stake_on_curve":
        if "curve_id" not in cmd.args or not (
            isinstance(cmd.args["curve_id"], int)
            and not isinstance(cmd.args["curve_id"], bool)
            and 0 <= cmd.args["curve_id"] <= 4
        ):
            return StepResult(ok=False, error="invalid param curve_id")
        if "amount" not in cmd.args or not (
            isinstance(cmd.args["amount"], int)
            and not isinstance(cmd.args["amount"], bool)
            and 1 <= cmd.args["amount"] <= 1000000000000
        ):
            return StepResult(ok=False, error="invalid param amount")
        if "auth_ok" not in cmd.args or not (isinstance(cmd.args["auth_ok"], bool)):
            return StepResult(ok=False, error="invalid param auth_ok")
        if not (
            ((cmd.args["amount"] + s.total_staked) <= 1000000000000)
            and cmd.args["auth_ok"]
        ):
            return StepResult(ok=False, error="guard failed for stake_on_curve")
        # Compute updates (simultaneous)
        new_state = State(
            active_curve=s.active_curve,
            epochs_since_start=s.epochs_since_start,
            prediction_epoch=s.prediction_epoch,
            protocol_fee_bps=s.protocol_fee_bps,
            protocol_fee_pool=s.protocol_fee_pool,
            revenue_0=s.revenue_0,
            revenue_1=s.revenue_1,
            revenue_2=s.revenue_2,
            revenue_3=s.revenue_3,
            revenue_4=s.revenue_4,
            settlement_epoch_interval=s.settlement_epoch_interval,
            stakes_0=(
                (cmd.args["amount"] + s.stakes_0)
                if (0 == cmd.args["curve_id"])
                else s.stakes_0
            ),
            stakes_1=(
                (cmd.args["amount"] + s.stakes_1)
                if (1 == cmd.args["curve_id"])
                else s.stakes_1
            ),
            stakes_2=(
                (cmd.args["amount"] + s.stakes_2)
                if (2 == cmd.args["curve_id"])
                else s.stakes_2
            ),
            stakes_3=(
                (cmd.args["amount"] + s.stakes_3)
                if (3 == cmd.args["curve_id"])
                else s.stakes_3
            ),
            stakes_4=(
                (cmd.args["amount"] + s.stakes_4)
                if (4 == cmd.args["curve_id"])
                else s.stakes_4
            ),
            total_staked=(cmd.args["amount"] + s.total_staked),
            winner_payout_pool=s.winner_payout_pool,
        )
        effects = {
            "event": "Staked",
            "payout_amount": 0,
            "winning_curve": -1,
        }
        ok, failed = check_invariants(new_state)
        if not ok:
            return StepResult(ok=False, error=f"post-invariant violated: {failed}")
        return StepResult(ok=True, state=new_state, effects=effects)
    elif cmd.tag == "unstake":
        if "curve_id" not in cmd.args or not (
            isinstance(cmd.args["curve_id"], int)
            and not isinstance(cmd.args["curve_id"], bool)
            and 0 <= cmd.args["curve_id"] <= 4
        ):
            return StepResult(ok=False, error="invalid param curve_id")
        if "amount" not in cmd.args or not (
            isinstance(cmd.args["amount"], int)
            and not isinstance(cmd.args["amount"], bool)
            and 1 <= cmd.args["amount"] <= 1000000000000
        ):
            return StepResult(ok=False, error="invalid param amount")
        if "penalty_amount" not in cmd.args or not (
            isinstance(cmd.args["penalty_amount"], int)
            and not isinstance(cmd.args["penalty_amount"], bool)
            and 0 <= cmd.args["penalty_amount"] <= 1000000000000
        ):
            return StepResult(ok=False, error="invalid param penalty_amount")
        if "auth_ok" not in cmd.args or not (isinstance(cmd.args["auth_ok"], bool)):
            return StepResult(ok=False, error="invalid param auth_ok")
        if not (
            ((cmd.args["penalty_amount"] + s.protocol_fee_pool) <= 1000000000000)
            and (
                cmd.args["amount"]
                <= (
                    s.stakes_0
                    if (0 == cmd.args["curve_id"])
                    else (
                        s.stakes_1
                        if (1 == cmd.args["curve_id"])
                        else (
                            s.stakes_2
                            if (2 == cmd.args["curve_id"])
                            else (
                                s.stakes_3
                                if (3 == cmd.args["curve_id"])
                                else s.stakes_4
                            )
                        )
                    )
                )
            )
            and (cmd.args["penalty_amount"] <= cmd.args["amount"])
            and cmd.args["auth_ok"]
        ):
            return StepResult(ok=False, error="guard failed for unstake")
        # Compute updates (simultaneous)
        new_state = State(
            active_curve=s.active_curve,
            epochs_since_start=s.epochs_since_start,
            prediction_epoch=s.prediction_epoch,
            protocol_fee_bps=s.protocol_fee_bps,
            protocol_fee_pool=(cmd.args["penalty_amount"] + s.protocol_fee_pool),
            revenue_0=s.revenue_0,
            revenue_1=s.revenue_1,
            revenue_2=s.revenue_2,
            revenue_3=s.revenue_3,
            revenue_4=s.revenue_4,
            settlement_epoch_interval=s.settlement_epoch_interval,
            stakes_0=(
                (s.stakes_0 - cmd.args["amount"])
                if (0 == cmd.args["curve_id"])
                else s.stakes_0
            ),
            stakes_1=(
                (s.stakes_1 - cmd.args["amount"])
                if (1 == cmd.args["curve_id"])
                else s.stakes_1
            ),
            stakes_2=(
                (s.stakes_2 - cmd.args["amount"])
                if (2 == cmd.args["curve_id"])
                else s.stakes_2
            ),
            stakes_3=(
                (s.stakes_3 - cmd.args["amount"])
                if (3 == cmd.args["curve_id"])
                else s.stakes_3
            ),
            stakes_4=(
                (s.stakes_4 - cmd.args["amount"])
                if (4 == cmd.args["curve_id"])
                else s.stakes_4
            ),
            total_staked=(s.total_staked - cmd.args["amount"]),
            winner_payout_pool=s.winner_payout_pool,
        )
        effects = {
            "event": "Unstaked",
            "payout_amount": 0,
            "winning_curve": -1,
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
#     # @rule(new_interval=st.integers(), auth_ok=st.integers())
#     # def admin_set_interval(self, new_interval, auth_ok):
#     #     cmd = Command(tag='admin_set_interval', args={'new_interval': new_interval, 'auth_ok': auth_ok})
#     #     result = step(self.state, cmd)
#     #     if result.ok:
#     #         self.state = result.state
#
#     # @rule(revenue_delta_0=st.integers(), revenue_delta_1=st.integers(), revenue_delta_2=st.integers(), revenue_delta_3=st.integers(), revenue_delta_4=st.integers())
#     # def advance_epoch(self, revenue_delta_0, revenue_delta_1, revenue_delta_2, revenue_delta_3, revenue_delta_4):
#     #     cmd = Command(tag='advance_epoch', args={'revenue_delta_0': revenue_delta_0, 'revenue_delta_1': revenue_delta_1, 'revenue_delta_2': revenue_delta_2, 'revenue_delta_3': revenue_delta_3, 'revenue_delta_4': revenue_delta_4})
#     #     result = step(self.state, cmd)
#     #     if result.ok:
#     #         self.state = result.state
#
#     # @rule(winning_curve_id=st.integers(), protocol_fee=st.integers())
#     # def settle_prediction(self, winning_curve_id, protocol_fee):
#     #     cmd = Command(tag='settle_prediction', args={'winning_curve_id': winning_curve_id, 'protocol_fee': protocol_fee})
#     #     result = step(self.state, cmd)
#     #     if result.ok:
#     #         self.state = result.state
#
#     # @rule(curve_id=st.integers(), amount=st.integers(), auth_ok=st.integers())
#     # def stake_on_curve(self, curve_id, amount, auth_ok):
#     #     cmd = Command(tag='stake_on_curve', args={'curve_id': curve_id, 'amount': amount, 'auth_ok': auth_ok})
#     #     result = step(self.state, cmd)
#     #     if result.ok:
#     #         self.state = result.state
#
#     # @rule(curve_id=st.integers(), amount=st.integers(), penalty_amount=st.integers(), auth_ok=st.integers())
#     # def unstake(self, curve_id, amount, penalty_amount, auth_ok):
#     #     cmd = Command(tag='unstake', args={'curve_id': curve_id, 'amount': amount, 'penalty_amount': penalty_amount, 'auth_ok': auth_ok})
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
