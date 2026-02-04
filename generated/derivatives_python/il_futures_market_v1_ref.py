"""
Auto-generated Python reference model for: il_futures_market_v1
IR hash: sha256:c38dc1f0dad42ca94cea745cefaeef111b09b5b2e5dc31848bed63700a1f1266

Generated from the YAML kernel spec by the repo's optional private toolchain.

This file is standalone and has no runtime dependency on the generator/toolchain.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Literal, Mapping


@dataclass(frozen=True)
class State:
    """Model state."""

    coverage_ratio_bps: int
    epoch: int
    long_exposure: int
    margin_pool: int
    max_leverage_bps: int
    pool_snapshot_reserve_x: int
    pool_snapshot_reserve_y: int
    premium_pool: int
    protocol_fee_bps: int
    protocol_fee_pool: int
    realized_il_bps: int
    settled_this_epoch: bool
    short_exposure: int
    snapshot_taken: bool


@dataclass(frozen=True)
class Command:
    """Command to execute."""

    tag: Literal(
        "advance_epoch",
        "close_long",
        "close_short",
        "open_long_il",
        "open_short_il",
        "settle_il_epoch",
        "snapshot_epoch_start",
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
        coverage_ratio_bps=8000,
        epoch=0,
        long_exposure=0,
        margin_pool=0,
        max_leverage_bps=20000,
        pool_snapshot_reserve_x=0,
        pool_snapshot_reserve_y=0,
        premium_pool=0,
        protocol_fee_bps=100,
        protocol_fee_pool=0,
        realized_il_bps=0,
        settled_this_epoch=False,
        short_exposure=0,
        snapshot_taken=False,
    )


def check_invariants(s: State) -> tuple[bool, str | None]:
    """Check all invariants. Returns (ok, first_failed_id)."""
    if not (
        isinstance(s.coverage_ratio_bps, int)
        and not isinstance(s.coverage_ratio_bps, bool)
        and 0 <= s.coverage_ratio_bps <= 10000
    ):
        return False, "domain_coverage_ratio_bps"
    if not (
        isinstance(s.epoch, int)
        and not isinstance(s.epoch, bool)
        and 0 <= s.epoch <= 1000000000
    ):
        return False, "domain_epoch"
    if not (
        isinstance(s.long_exposure, int)
        and not isinstance(s.long_exposure, bool)
        and 0 <= s.long_exposure <= 1000000000000
    ):
        return False, "domain_long_exposure"
    if not (
        isinstance(s.margin_pool, int)
        and not isinstance(s.margin_pool, bool)
        and 0 <= s.margin_pool <= 1000000000000
    ):
        return False, "domain_margin_pool"
    if not (
        isinstance(s.max_leverage_bps, int)
        and not isinstance(s.max_leverage_bps, bool)
        and 1 <= s.max_leverage_bps <= 50000
    ):
        return False, "domain_max_leverage_bps"
    if not (
        isinstance(s.pool_snapshot_reserve_x, int)
        and not isinstance(s.pool_snapshot_reserve_x, bool)
        and 0 <= s.pool_snapshot_reserve_x <= 1000000000000
    ):
        return False, "domain_pool_snapshot_reserve_x"
    if not (
        isinstance(s.pool_snapshot_reserve_y, int)
        and not isinstance(s.pool_snapshot_reserve_y, bool)
        and 0 <= s.pool_snapshot_reserve_y <= 1000000000000
    ):
        return False, "domain_pool_snapshot_reserve_y"
    if not (
        isinstance(s.premium_pool, int)
        and not isinstance(s.premium_pool, bool)
        and 0 <= s.premium_pool <= 1000000000000
    ):
        return False, "domain_premium_pool"
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
        isinstance(s.realized_il_bps, int)
        and not isinstance(s.realized_il_bps, bool)
        and 0 <= s.realized_il_bps <= 10000
    ):
        return False, "domain_realized_il_bps"
    if not (isinstance(s.settled_this_epoch, bool)):
        return False, "domain_settled_this_epoch"
    if not (
        isinstance(s.short_exposure, int)
        and not isinstance(s.short_exposure, bool)
        and 0 <= s.short_exposure <= 1000000000000
    ):
        return False, "domain_short_exposure"
    if not (isinstance(s.snapshot_taken, bool)):
        return False, "domain_snapshot_taken"
    if not ((s.long_exposure >= 0) and (s.short_exposure >= 0)):
        return False, "inv_exposure_nonneg"
    if not (s.margin_pool == s.short_exposure):
        return False, "inv_margin_short_consistent"
    if not (
        (s.margin_pool >= 0) and (s.premium_pool >= 0) and (s.protocol_fee_pool >= 0)
    ):
        return False, "inv_pools_nonneg"
    return True, None


def step(s: State, cmd: Command) -> StepResult:
    """Execute a step. Returns StepResult."""
    # Check pre-state invariants
    ok, failed = check_invariants(s)
    if not ok:
        return StepResult(ok=False, error=f"pre-invariant violated: {failed}")

    if cmd.tag == "advance_epoch":
        if not ((s.epoch < 1000000000) and (True == s.settled_this_epoch)):
            return StepResult(ok=False, error="guard failed for advance_epoch")
        # Compute updates (simultaneous)
        new_state = State(
            coverage_ratio_bps=s.coverage_ratio_bps,
            epoch=(1 + s.epoch),
            long_exposure=s.long_exposure,
            margin_pool=s.margin_pool,
            max_leverage_bps=s.max_leverage_bps,
            pool_snapshot_reserve_x=s.pool_snapshot_reserve_x,
            pool_snapshot_reserve_y=s.pool_snapshot_reserve_y,
            premium_pool=s.premium_pool,
            protocol_fee_bps=s.protocol_fee_bps,
            protocol_fee_pool=s.protocol_fee_pool,
            realized_il_bps=0,
            settled_this_epoch=False,
            short_exposure=s.short_exposure,
            snapshot_taken=False,
        )
        effects = {
            "event": "EpochAdvanced",
            "il_bps_out": 0,
            "payout_out": 0,
        }
        ok, failed = check_invariants(new_state)
        if not ok:
            return StepResult(ok=False, error=f"post-invariant violated: {failed}")
        return StepResult(ok=True, state=new_state, effects=effects)
    elif cmd.tag == "close_long":
        if "amount" not in cmd.args or not (
            isinstance(cmd.args["amount"], int)
            and not isinstance(cmd.args["amount"], bool)
            and 1 <= cmd.args["amount"] <= 1000000000000
        ):
            return StepResult(ok=False, error="invalid param amount")
        if "auth_ok" not in cmd.args or not (isinstance(cmd.args["auth_ok"], bool)):
            return StepResult(ok=False, error="invalid param auth_ok")
        if not (
            (cmd.args["amount"] <= s.long_exposure)
            and ((False == s.snapshot_taken) or (True == s.settled_this_epoch))
            and cmd.args["auth_ok"]
        ):
            return StepResult(ok=False, error="guard failed for close_long")
        # Compute updates (simultaneous)
        new_state = State(
            coverage_ratio_bps=s.coverage_ratio_bps,
            epoch=s.epoch,
            long_exposure=(s.long_exposure - cmd.args["amount"]),
            margin_pool=s.margin_pool,
            max_leverage_bps=s.max_leverage_bps,
            pool_snapshot_reserve_x=s.pool_snapshot_reserve_x,
            pool_snapshot_reserve_y=s.pool_snapshot_reserve_y,
            premium_pool=s.premium_pool,
            protocol_fee_bps=s.protocol_fee_bps,
            protocol_fee_pool=s.protocol_fee_pool,
            realized_il_bps=s.realized_il_bps,
            settled_this_epoch=s.settled_this_epoch,
            short_exposure=s.short_exposure,
            snapshot_taken=s.snapshot_taken,
        )
        effects = {
            "event": "LongClosed",
            "il_bps_out": 0,
            "payout_out": 0,
        }
        ok, failed = check_invariants(new_state)
        if not ok:
            return StepResult(ok=False, error=f"post-invariant violated: {failed}")
        return StepResult(ok=True, state=new_state, effects=effects)
    elif cmd.tag == "close_short":
        if "amount" not in cmd.args or not (
            isinstance(cmd.args["amount"], int)
            and not isinstance(cmd.args["amount"], bool)
            and 1 <= cmd.args["amount"] <= 1000000000000
        ):
            return StepResult(ok=False, error="invalid param amount")
        if "auth_ok" not in cmd.args or not (isinstance(cmd.args["auth_ok"], bool)):
            return StepResult(ok=False, error="invalid param auth_ok")
        if not (
            (cmd.args["amount"] <= s.short_exposure)
            and ((False == s.snapshot_taken) or (True == s.settled_this_epoch))
            and cmd.args["auth_ok"]
        ):
            return StepResult(ok=False, error="guard failed for close_short")
        # Compute updates (simultaneous)
        new_state = State(
            coverage_ratio_bps=s.coverage_ratio_bps,
            epoch=s.epoch,
            long_exposure=s.long_exposure,
            margin_pool=(s.margin_pool - cmd.args["amount"]),
            max_leverage_bps=s.max_leverage_bps,
            pool_snapshot_reserve_x=s.pool_snapshot_reserve_x,
            pool_snapshot_reserve_y=s.pool_snapshot_reserve_y,
            premium_pool=s.premium_pool,
            protocol_fee_bps=s.protocol_fee_bps,
            protocol_fee_pool=s.protocol_fee_pool,
            realized_il_bps=s.realized_il_bps,
            settled_this_epoch=s.settled_this_epoch,
            short_exposure=(s.short_exposure - cmd.args["amount"]),
            snapshot_taken=s.snapshot_taken,
        )
        effects = {
            "event": "ShortClosed",
            "il_bps_out": 0,
            "payout_out": 0,
        }
        ok, failed = check_invariants(new_state)
        if not ok:
            return StepResult(ok=False, error=f"post-invariant violated: {failed}")
        return StepResult(ok=True, state=new_state, effects=effects)
    elif cmd.tag == "open_long_il":
        if "amount" not in cmd.args or not (
            isinstance(cmd.args["amount"], int)
            and not isinstance(cmd.args["amount"], bool)
            and 1 <= cmd.args["amount"] <= 1000000000000
        ):
            return StepResult(ok=False, error="invalid param amount")
        if "premium_amount" not in cmd.args or not (
            isinstance(cmd.args["premium_amount"], int)
            and not isinstance(cmd.args["premium_amount"], bool)
            and 1 <= cmd.args["premium_amount"] <= 100000000
        ):
            return StepResult(ok=False, error="invalid param premium_amount")
        if "auth_ok" not in cmd.args or not (isinstance(cmd.args["auth_ok"], bool)):
            return StepResult(ok=False, error="invalid param auth_ok")
        if not (
            (
                (10000 * (cmd.args["amount"] + s.long_exposure))
                <= (s.max_leverage_bps * s.short_exposure)
            )
            and ((cmd.args["amount"] + s.long_exposure) <= 1000000000000)
            and ((cmd.args["premium_amount"] + s.premium_pool) <= 1000000000000)
            and (False == s.snapshot_taken)
            and (s.short_exposure > 0)
            and cmd.args["auth_ok"]
        ):
            return StepResult(ok=False, error="guard failed for open_long_il")
        # Compute updates (simultaneous)
        new_state = State(
            coverage_ratio_bps=s.coverage_ratio_bps,
            epoch=s.epoch,
            long_exposure=(cmd.args["amount"] + s.long_exposure),
            margin_pool=s.margin_pool,
            max_leverage_bps=s.max_leverage_bps,
            pool_snapshot_reserve_x=s.pool_snapshot_reserve_x,
            pool_snapshot_reserve_y=s.pool_snapshot_reserve_y,
            premium_pool=(cmd.args["premium_amount"] + s.premium_pool),
            protocol_fee_bps=s.protocol_fee_bps,
            protocol_fee_pool=s.protocol_fee_pool,
            realized_il_bps=s.realized_il_bps,
            settled_this_epoch=s.settled_this_epoch,
            short_exposure=s.short_exposure,
            snapshot_taken=s.snapshot_taken,
        )
        effects = {
            "event": "LongOpened",
            "il_bps_out": 0,
            "payout_out": 0,
        }
        ok, failed = check_invariants(new_state)
        if not ok:
            return StepResult(ok=False, error=f"post-invariant violated: {failed}")
        return StepResult(ok=True, state=new_state, effects=effects)
    elif cmd.tag == "open_short_il":
        if "amount" not in cmd.args or not (
            isinstance(cmd.args["amount"], int)
            and not isinstance(cmd.args["amount"], bool)
            and 1 <= cmd.args["amount"] <= 1000000000000
        ):
            return StepResult(ok=False, error="invalid param amount")
        if "auth_ok" not in cmd.args or not (isinstance(cmd.args["auth_ok"], bool)):
            return StepResult(ok=False, error="invalid param auth_ok")
        if not (
            ((cmd.args["amount"] + s.margin_pool) <= 1000000000000)
            and ((cmd.args["amount"] + s.short_exposure) <= 1000000000000)
            and (False == s.snapshot_taken)
            and cmd.args["auth_ok"]
        ):
            return StepResult(ok=False, error="guard failed for open_short_il")
        # Compute updates (simultaneous)
        new_state = State(
            coverage_ratio_bps=s.coverage_ratio_bps,
            epoch=s.epoch,
            long_exposure=s.long_exposure,
            margin_pool=(cmd.args["amount"] + s.margin_pool),
            max_leverage_bps=s.max_leverage_bps,
            pool_snapshot_reserve_x=s.pool_snapshot_reserve_x,
            pool_snapshot_reserve_y=s.pool_snapshot_reserve_y,
            premium_pool=s.premium_pool,
            protocol_fee_bps=s.protocol_fee_bps,
            protocol_fee_pool=s.protocol_fee_pool,
            realized_il_bps=s.realized_il_bps,
            settled_this_epoch=s.settled_this_epoch,
            short_exposure=(cmd.args["amount"] + s.short_exposure),
            snapshot_taken=s.snapshot_taken,
        )
        effects = {
            "event": "ShortOpened",
            "il_bps_out": 0,
            "payout_out": 0,
        }
        ok, failed = check_invariants(new_state)
        if not ok:
            return StepResult(ok=False, error=f"post-invariant violated: {failed}")
        return StepResult(ok=True, state=new_state, effects=effects)
    elif cmd.tag == "settle_il_epoch":
        if "il_bps" not in cmd.args or not (
            isinstance(cmd.args["il_bps"], int)
            and not isinstance(cmd.args["il_bps"], bool)
            and 0 <= cmd.args["il_bps"] <= 10000
        ):
            return StepResult(ok=False, error="invalid param il_bps")
        if "capped_payout" not in cmd.args or not (
            isinstance(cmd.args["capped_payout"], int)
            and not isinstance(cmd.args["capped_payout"], bool)
            and 0 <= cmd.args["capped_payout"] <= 1000000000000
        ):
            return StepResult(ok=False, error="invalid param capped_payout")
        if "protocol_fee" not in cmd.args or not (
            isinstance(cmd.args["protocol_fee"], int)
            and not isinstance(cmd.args["protocol_fee"], bool)
            and 0 <= cmd.args["protocol_fee"] <= 1000000000000
        ):
            return StepResult(ok=False, error="invalid param protocol_fee")
        if "auth_ok" not in cmd.args or not (isinstance(cmd.args["auth_ok"], bool)):
            return StepResult(ok=False, error="invalid param auth_ok")
        if not (
            ((cmd.args["protocol_fee"] + s.protocol_fee_pool) <= 1000000000000)
            and (cmd.args["capped_payout"] <= (s.margin_pool + s.premium_pool))
            and (cmd.args["protocol_fee"] <= cmd.args["capped_payout"])
            and (False == s.settled_this_epoch)
            and (True == s.snapshot_taken)
            and cmd.args["auth_ok"]
        ):
            return StepResult(ok=False, error="guard failed for settle_il_epoch")
        # Compute updates (simultaneous)
        new_state = State(
            coverage_ratio_bps=s.coverage_ratio_bps,
            epoch=s.epoch,
            long_exposure=0,
            margin_pool=(s.margin_pool - min(cmd.args["capped_payout"], s.margin_pool)),
            max_leverage_bps=s.max_leverage_bps,
            pool_snapshot_reserve_x=s.pool_snapshot_reserve_x,
            pool_snapshot_reserve_y=s.pool_snapshot_reserve_y,
            premium_pool=(
                s.premium_pool
                - (
                    cmd.args["capped_payout"]
                    - min(cmd.args["capped_payout"], s.margin_pool)
                )
            ),
            protocol_fee_bps=s.protocol_fee_bps,
            protocol_fee_pool=(cmd.args["protocol_fee"] + s.protocol_fee_pool),
            realized_il_bps=cmd.args["il_bps"],
            settled_this_epoch=True,
            short_exposure=(
                s.margin_pool - min(cmd.args["capped_payout"], s.margin_pool)
            ),
            snapshot_taken=s.snapshot_taken,
        )
        effects = {
            "event": "EpochSettled",
            "il_bps_out": cmd.args["il_bps"],
            "payout_out": (cmd.args["capped_payout"] - cmd.args["protocol_fee"]),
        }
        ok, failed = check_invariants(new_state)
        if not ok:
            return StepResult(ok=False, error=f"post-invariant violated: {failed}")
        return StepResult(ok=True, state=new_state, effects=effects)
    elif cmd.tag == "snapshot_epoch_start":
        if "reserve_x" not in cmd.args or not (
            isinstance(cmd.args["reserve_x"], int)
            and not isinstance(cmd.args["reserve_x"], bool)
            and 1 <= cmd.args["reserve_x"] <= 1000000000000
        ):
            return StepResult(ok=False, error="invalid param reserve_x")
        if "reserve_y" not in cmd.args or not (
            isinstance(cmd.args["reserve_y"], int)
            and not isinstance(cmd.args["reserve_y"], bool)
            and 1 <= cmd.args["reserve_y"] <= 1000000000000
        ):
            return StepResult(ok=False, error="invalid param reserve_y")
        if "auth_ok" not in cmd.args or not (isinstance(cmd.args["auth_ok"], bool)):
            return StepResult(ok=False, error="invalid param auth_ok")
        if not ((False == s.snapshot_taken) and cmd.args["auth_ok"]):
            return StepResult(ok=False, error="guard failed for snapshot_epoch_start")
        # Compute updates (simultaneous)
        new_state = State(
            coverage_ratio_bps=s.coverage_ratio_bps,
            epoch=s.epoch,
            long_exposure=s.long_exposure,
            margin_pool=s.margin_pool,
            max_leverage_bps=s.max_leverage_bps,
            pool_snapshot_reserve_x=cmd.args["reserve_x"],
            pool_snapshot_reserve_y=cmd.args["reserve_y"],
            premium_pool=s.premium_pool,
            protocol_fee_bps=s.protocol_fee_bps,
            protocol_fee_pool=s.protocol_fee_pool,
            realized_il_bps=s.realized_il_bps,
            settled_this_epoch=s.settled_this_epoch,
            short_exposure=s.short_exposure,
            snapshot_taken=True,
        )
        effects = {
            "event": "EpochSnapshotted",
            "il_bps_out": 0,
            "payout_out": 0,
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
#     # @rule()
#     # def advance_epoch(self, ):
#     #     cmd = Command(tag='advance_epoch', args={})
#     #     result = step(self.state, cmd)
#     #     if result.ok:
#     #         self.state = result.state
#
#     # @rule(amount=st.integers(), auth_ok=st.integers())
#     # def close_long(self, amount, auth_ok):
#     #     cmd = Command(tag='close_long', args={'amount': amount, 'auth_ok': auth_ok})
#     #     result = step(self.state, cmd)
#     #     if result.ok:
#     #         self.state = result.state
#
#     # @rule(amount=st.integers(), auth_ok=st.integers())
#     # def close_short(self, amount, auth_ok):
#     #     cmd = Command(tag='close_short', args={'amount': amount, 'auth_ok': auth_ok})
#     #     result = step(self.state, cmd)
#     #     if result.ok:
#     #         self.state = result.state
#
#     # @rule(amount=st.integers(), premium_amount=st.integers(), auth_ok=st.integers())
#     # def open_long_il(self, amount, premium_amount, auth_ok):
#     #     cmd = Command(tag='open_long_il', args={'amount': amount, 'premium_amount': premium_amount, 'auth_ok': auth_ok})
#     #     result = step(self.state, cmd)
#     #     if result.ok:
#     #         self.state = result.state
#
#     # @rule(amount=st.integers(), auth_ok=st.integers())
#     # def open_short_il(self, amount, auth_ok):
#     #     cmd = Command(tag='open_short_il', args={'amount': amount, 'auth_ok': auth_ok})
#     #     result = step(self.state, cmd)
#     #     if result.ok:
#     #         self.state = result.state
#
#     # @rule(il_bps=st.integers(), capped_payout=st.integers(), protocol_fee=st.integers(), auth_ok=st.integers())
#     # def settle_il_epoch(self, il_bps, capped_payout, protocol_fee, auth_ok):
#     #     cmd = Command(tag='settle_il_epoch', args={'il_bps': il_bps, 'capped_payout': capped_payout, 'protocol_fee': protocol_fee, 'auth_ok': auth_ok})
#     #     result = step(self.state, cmd)
#     #     if result.ok:
#     #         self.state = result.state
#
#     # @rule(reserve_x=st.integers(), reserve_y=st.integers(), auth_ok=st.integers())
#     # def snapshot_epoch_start(self, reserve_x, reserve_y, auth_ok):
#     #     cmd = Command(tag='snapshot_epoch_start', args={'reserve_x': reserve_x, 'reserve_y': reserve_y, 'auth_ok': auth_ok})
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
