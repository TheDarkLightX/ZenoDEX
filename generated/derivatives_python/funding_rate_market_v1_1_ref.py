"""
Auto-generated Python reference model for: funding_rate_market_v1_1
IR hash: sha256:1d5fea50d2007ecdbb298464af5a56c8e5e395ca6d532de2fa613d9ec5711903

Generated from the YAML kernel spec by the repo's optional private toolchain.

This file is standalone and has no runtime dependency on the generator/toolchain.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Literal, Mapping


@dataclass(frozen=True)
class State:
    """Model state."""

    frozen: bool
    funding_cap_bps: int
    implied_rate_bps: int
    index_price_e8: int
    long_payout: int
    mark_price_e8: int
    premium_pool: int
    protocol_fee_bps: int
    protocol_fee_pool: int
    rate_long_exposure: int
    rate_market_epoch: int
    rate_short_exposure: int
    realized_rate_bps: int
    settled_this_epoch: bool
    settlement_epoch: int
    short_payout: int


@dataclass(frozen=True)
class Command:
    """Command to execute."""

    tag: Literal(
        "advance_rate_epoch",
        "emergency_freeze",
        "open_rate_long",
        "open_rate_short",
        "settle_rate_epoch",
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
        frozen=False,
        funding_cap_bps=100,
        implied_rate_bps=0,
        index_price_e8=0,
        long_payout=0,
        mark_price_e8=0,
        premium_pool=0,
        protocol_fee_bps=100,
        protocol_fee_pool=0,
        rate_long_exposure=0,
        rate_market_epoch=0,
        rate_short_exposure=0,
        realized_rate_bps=0,
        settled_this_epoch=False,
        settlement_epoch=0,
        short_payout=0,
    )


def check_invariants(s: State) -> tuple[bool, str | None]:
    """Check all invariants. Returns (ok, first_failed_id)."""
    if not (isinstance(s.frozen, bool)):
        return False, "domain_frozen"
    if not (
        isinstance(s.funding_cap_bps, int)
        and not isinstance(s.funding_cap_bps, bool)
        and 1 <= s.funding_cap_bps <= 10000
    ):
        return False, "domain_funding_cap_bps"
    if not (
        isinstance(s.implied_rate_bps, int)
        and not isinstance(s.implied_rate_bps, bool)
        and -10000 <= s.implied_rate_bps <= 10000
    ):
        return False, "domain_implied_rate_bps"
    if not (
        isinstance(s.index_price_e8, int)
        and not isinstance(s.index_price_e8, bool)
        and 0 <= s.index_price_e8 <= 1000000000000
    ):
        return False, "domain_index_price_e8"
    if not (
        isinstance(s.long_payout, int)
        and not isinstance(s.long_payout, bool)
        and 0 <= s.long_payout <= 1000000000000
    ):
        return False, "domain_long_payout"
    if not (
        isinstance(s.mark_price_e8, int)
        and not isinstance(s.mark_price_e8, bool)
        and 0 <= s.mark_price_e8 <= 1000000000000
    ):
        return False, "domain_mark_price_e8"
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
        isinstance(s.rate_long_exposure, int)
        and not isinstance(s.rate_long_exposure, bool)
        and 0 <= s.rate_long_exposure <= 1000000000000
    ):
        return False, "domain_rate_long_exposure"
    if not (
        isinstance(s.rate_market_epoch, int)
        and not isinstance(s.rate_market_epoch, bool)
        and 0 <= s.rate_market_epoch <= 1000000000
    ):
        return False, "domain_rate_market_epoch"
    if not (
        isinstance(s.rate_short_exposure, int)
        and not isinstance(s.rate_short_exposure, bool)
        and 0 <= s.rate_short_exposure <= 1000000000000
    ):
        return False, "domain_rate_short_exposure"
    if not (
        isinstance(s.realized_rate_bps, int)
        and not isinstance(s.realized_rate_bps, bool)
        and -10000 <= s.realized_rate_bps <= 10000
    ):
        return False, "domain_realized_rate_bps"
    if not (isinstance(s.settled_this_epoch, bool)):
        return False, "domain_settled_this_epoch"
    if not (
        isinstance(s.settlement_epoch, int)
        and not isinstance(s.settlement_epoch, bool)
        and 0 <= s.settlement_epoch <= 1000000000
    ):
        return False, "domain_settlement_epoch"
    if not (
        isinstance(s.short_payout, int)
        and not isinstance(s.short_payout, bool)
        and 0 <= s.short_payout <= 1000000000000
    ):
        return False, "domain_short_payout"
    if not ((s.rate_long_exposure >= 0) and (s.rate_short_exposure >= 0)):
        return False, "inv_exposure_nonneg"
    if not (
        (
            (not (False == s.settled_this_epoch))
            or ((s.rate_long_exposure + s.rate_short_exposure) == s.premium_pool)
        )
        and ((not (True == s.settled_this_epoch)) or (0 == s.premium_pool))
    ):
        return False, "inv_pool_consistency"
    if not (
        (s.long_payout >= 0)
        and (s.premium_pool >= 0)
        and (s.protocol_fee_pool >= 0)
        and (s.short_payout >= 0)
    ):
        return False, "inv_pools_nonneg"
    if not (
        (s.implied_rate_bps <= s.funding_cap_bps)
        and (s.implied_rate_bps >= (0 - s.funding_cap_bps))
    ):
        return False, "inv_rate_bounded"
    if not (
        (not (False == s.settled_this_epoch))
        or (
            (0 == s.long_payout)
            and (0 == s.realized_rate_bps)
            and (0 == s.short_payout)
        )
    ):
        return False, "inv_unsettled_fields_zeroed"
    return True, None


def step(s: State, cmd: Command) -> StepResult:
    """Execute a step. Returns StepResult."""
    # Check pre-state invariants
    ok, failed = check_invariants(s)
    if not ok:
        return StepResult(ok=False, error=f"pre-invariant violated: {failed}")

    if cmd.tag == "advance_rate_epoch":
        if not ((s.rate_market_epoch < 1000000000) and (True == s.settled_this_epoch)):
            return StepResult(ok=False, error="guard failed for advance_rate_epoch")
        # Compute updates (simultaneous)
        new_state = State(
            frozen=s.frozen,
            funding_cap_bps=s.funding_cap_bps,
            implied_rate_bps=0,
            index_price_e8=s.index_price_e8,
            long_payout=0,
            mark_price_e8=s.mark_price_e8,
            premium_pool=0,
            protocol_fee_bps=s.protocol_fee_bps,
            protocol_fee_pool=s.protocol_fee_pool,
            rate_long_exposure=0,
            rate_market_epoch=(1 + s.rate_market_epoch),
            rate_short_exposure=0,
            realized_rate_bps=0,
            settled_this_epoch=False,
            settlement_epoch=s.settlement_epoch,
            short_payout=0,
        )
        effects = {
            "event": "RateEpochAdvanced",
            "implied_rate_bps": 0,
            "payout_long": 0,
            "payout_short": 0,
            "realized_rate_bps": 0,
        }
        ok, failed = check_invariants(new_state)
        if not ok:
            return StepResult(ok=False, error=f"post-invariant violated: {failed}")
        return StepResult(ok=True, state=new_state, effects=effects)
    elif cmd.tag == "emergency_freeze":
        if "auth_ok" not in cmd.args or not (isinstance(cmd.args["auth_ok"], bool)):
            return StepResult(ok=False, error="invalid param auth_ok")
        if not ((False == s.frozen) and cmd.args["auth_ok"]):
            return StepResult(ok=False, error="guard failed for emergency_freeze")
        # Compute updates (simultaneous)
        new_state = State(
            frozen=True,
            funding_cap_bps=s.funding_cap_bps,
            implied_rate_bps=s.implied_rate_bps,
            index_price_e8=s.index_price_e8,
            long_payout=s.long_payout,
            mark_price_e8=s.mark_price_e8,
            premium_pool=s.premium_pool,
            protocol_fee_bps=s.protocol_fee_bps,
            protocol_fee_pool=s.protocol_fee_pool,
            rate_long_exposure=s.rate_long_exposure,
            rate_market_epoch=s.rate_market_epoch,
            rate_short_exposure=s.rate_short_exposure,
            realized_rate_bps=s.realized_rate_bps,
            settled_this_epoch=s.settled_this_epoch,
            settlement_epoch=s.settlement_epoch,
            short_payout=s.short_payout,
        )
        effects = {
            "event": "MarketFrozen",
            "implied_rate_bps": 0,
            "payout_long": 0,
            "payout_short": 0,
            "realized_rate_bps": 0,
        }
        ok, failed = check_invariants(new_state)
        if not ok:
            return StepResult(ok=False, error=f"post-invariant violated: {failed}")
        return StepResult(ok=True, state=new_state, effects=effects)
    elif cmd.tag == "open_rate_long":
        if "amount" not in cmd.args or not (
            isinstance(cmd.args["amount"], int)
            and not isinstance(cmd.args["amount"], bool)
            and 1 <= cmd.args["amount"] <= 1000000000000
        ):
            return StepResult(ok=False, error="invalid param amount")
        if "auth_ok" not in cmd.args or not (isinstance(cmd.args["auth_ok"], bool)):
            return StepResult(ok=False, error="invalid param auth_ok")
        if not (
            ((cmd.args["amount"] + s.premium_pool) <= 1000000000000)
            and ((cmd.args["amount"] + s.rate_long_exposure) <= 1000000000000)
            and (False == s.frozen)
            and (False == s.settled_this_epoch)
            and cmd.args["auth_ok"]
        ):
            return StepResult(ok=False, error="guard failed for open_rate_long")
        # Compute updates (simultaneous)
        new_state = State(
            frozen=s.frozen,
            funding_cap_bps=s.funding_cap_bps,
            implied_rate_bps=max(
                (0 - s.funding_cap_bps),
                min(
                    (
                        0
                        if (
                            (cmd.args["amount"] + s.rate_long_exposure)
                            + s.rate_short_exposure
                        )
                        == 0
                        else (
                            (
                                (
                                    (
                                        (cmd.args["amount"] + s.rate_long_exposure)
                                        - s.rate_short_exposure
                                    )
                                    * s.funding_cap_bps
                                )
                                // (
                                    (cmd.args["amount"] + s.rate_long_exposure)
                                    + s.rate_short_exposure
                                )
                            )
                            + (
                                1
                                if (
                                    (
                                        (
                                            (cmd.args["amount"] + s.rate_long_exposure)
                                            - s.rate_short_exposure
                                        )
                                        * s.funding_cap_bps
                                    )
                                    % (
                                        (cmd.args["amount"] + s.rate_long_exposure)
                                        + s.rate_short_exposure
                                    )
                                )
                                < 0
                                else 0
                            )
                        )
                    ),
                    s.funding_cap_bps,
                ),
            ),
            index_price_e8=s.index_price_e8,
            long_payout=s.long_payout,
            mark_price_e8=s.mark_price_e8,
            premium_pool=(cmd.args["amount"] + s.premium_pool),
            protocol_fee_bps=s.protocol_fee_bps,
            protocol_fee_pool=s.protocol_fee_pool,
            rate_long_exposure=(cmd.args["amount"] + s.rate_long_exposure),
            rate_market_epoch=s.rate_market_epoch,
            rate_short_exposure=s.rate_short_exposure,
            realized_rate_bps=s.realized_rate_bps,
            settled_this_epoch=s.settled_this_epoch,
            settlement_epoch=s.settlement_epoch,
            short_payout=s.short_payout,
        )
        effects = {
            "event": "RateLongOpened",
            "implied_rate_bps": new_state.implied_rate_bps,
            "payout_long": 0,
            "payout_short": 0,
            "realized_rate_bps": 0,
        }
        ok, failed = check_invariants(new_state)
        if not ok:
            return StepResult(ok=False, error=f"post-invariant violated: {failed}")
        return StepResult(ok=True, state=new_state, effects=effects)
    elif cmd.tag == "open_rate_short":
        if "amount" not in cmd.args or not (
            isinstance(cmd.args["amount"], int)
            and not isinstance(cmd.args["amount"], bool)
            and 1 <= cmd.args["amount"] <= 1000000000000
        ):
            return StepResult(ok=False, error="invalid param amount")
        if "auth_ok" not in cmd.args or not (isinstance(cmd.args["auth_ok"], bool)):
            return StepResult(ok=False, error="invalid param auth_ok")
        if not (
            ((cmd.args["amount"] + s.premium_pool) <= 1000000000000)
            and ((cmd.args["amount"] + s.rate_short_exposure) <= 1000000000000)
            and (False == s.frozen)
            and (False == s.settled_this_epoch)
            and cmd.args["auth_ok"]
        ):
            return StepResult(ok=False, error="guard failed for open_rate_short")
        # Compute updates (simultaneous)
        new_state = State(
            frozen=s.frozen,
            funding_cap_bps=s.funding_cap_bps,
            implied_rate_bps=max(
                (0 - s.funding_cap_bps),
                min(
                    (
                        0
                        if (
                            (cmd.args["amount"] + s.rate_short_exposure)
                            + s.rate_long_exposure
                        )
                        == 0
                        else (
                            (
                                (
                                    (
                                        s.rate_long_exposure
                                        - (cmd.args["amount"] + s.rate_short_exposure)
                                    )
                                    * s.funding_cap_bps
                                )
                                // (
                                    (cmd.args["amount"] + s.rate_short_exposure)
                                    + s.rate_long_exposure
                                )
                            )
                            + (
                                1
                                if (
                                    (
                                        (
                                            s.rate_long_exposure
                                            - (
                                                cmd.args["amount"]
                                                + s.rate_short_exposure
                                            )
                                        )
                                        * s.funding_cap_bps
                                    )
                                    % (
                                        (cmd.args["amount"] + s.rate_short_exposure)
                                        + s.rate_long_exposure
                                    )
                                )
                                < 0
                                else 0
                            )
                        )
                    ),
                    s.funding_cap_bps,
                ),
            ),
            index_price_e8=s.index_price_e8,
            long_payout=s.long_payout,
            mark_price_e8=s.mark_price_e8,
            premium_pool=(cmd.args["amount"] + s.premium_pool),
            protocol_fee_bps=s.protocol_fee_bps,
            protocol_fee_pool=s.protocol_fee_pool,
            rate_long_exposure=s.rate_long_exposure,
            rate_market_epoch=s.rate_market_epoch,
            rate_short_exposure=(cmd.args["amount"] + s.rate_short_exposure),
            realized_rate_bps=s.realized_rate_bps,
            settled_this_epoch=s.settled_this_epoch,
            settlement_epoch=s.settlement_epoch,
            short_payout=s.short_payout,
        )
        effects = {
            "event": "RateShortOpened",
            "implied_rate_bps": new_state.implied_rate_bps,
            "payout_long": 0,
            "payout_short": 0,
            "realized_rate_bps": 0,
        }
        ok, failed = check_invariants(new_state)
        if not ok:
            return StepResult(ok=False, error=f"post-invariant violated: {failed}")
        return StepResult(ok=True, state=new_state, effects=effects)
    elif cmd.tag == "settle_rate_epoch":
        if "mark_price_e8" not in cmd.args or not (
            isinstance(cmd.args["mark_price_e8"], int)
            and not isinstance(cmd.args["mark_price_e8"], bool)
            and 1 <= cmd.args["mark_price_e8"] <= 1000000000000
        ):
            return StepResult(ok=False, error="invalid param mark_price_e8")
        if "index_price_e8" not in cmd.args or not (
            isinstance(cmd.args["index_price_e8"], int)
            and not isinstance(cmd.args["index_price_e8"], bool)
            and 1 <= cmd.args["index_price_e8"] <= 1000000000000
        ):
            return StepResult(ok=False, error="invalid param index_price_e8")
        if not (
            (s.settlement_epoch < 1000000000)
            and (
                (
                    (
                        0
                        if 10000 == 0
                        else (
                            ((s.premium_pool * s.protocol_fee_bps) // 10000)
                            + (
                                1
                                if ((s.premium_pool * s.protocol_fee_bps) % 10000) < 0
                                else 0
                            )
                        )
                    )
                    + s.protocol_fee_pool
                )
                <= 1000000000000
            )
            and (False == s.frozen)
            and (False == s.settled_this_epoch)
            and ((s.rate_long_exposure + s.rate_short_exposure) > 0)
        ):
            return StepResult(ok=False, error="guard failed for settle_rate_epoch")
        # Compute updates (simultaneous)
        new_state = State(
            frozen=s.frozen,
            funding_cap_bps=s.funding_cap_bps,
            implied_rate_bps=s.implied_rate_bps,
            index_price_e8=cmd.args["index_price_e8"],
            long_payout=(
                0
                if (s.rate_long_exposure + s.rate_short_exposure) == 0
                else (
                    (
                        (
                            (
                                s.rate_long_exposure
                                if (
                                    max(
                                        (0 - s.funding_cap_bps),
                                        min(
                                            (
                                                0
                                                if cmd.args["index_price_e8"] == 0
                                                else (
                                                    (
                                                        (
                                                            10000
                                                            * (
                                                                cmd.args[
                                                                    "mark_price_e8"
                                                                ]
                                                                - cmd.args[
                                                                    "index_price_e8"
                                                                ]
                                                            )
                                                        )
                                                        // cmd.args["index_price_e8"]
                                                    )
                                                    + (
                                                        1
                                                        if (
                                                            (
                                                                10000
                                                                * (
                                                                    cmd.args[
                                                                        "mark_price_e8"
                                                                    ]
                                                                    - cmd.args[
                                                                        "index_price_e8"
                                                                    ]
                                                                )
                                                            )
                                                            % cmd.args["index_price_e8"]
                                                        )
                                                        < 0
                                                        else 0
                                                    )
                                                )
                                            ),
                                            s.funding_cap_bps,
                                        ),
                                    )
                                    >= s.implied_rate_bps
                                )
                                else s.rate_short_exposure
                            )
                            * (
                                s.premium_pool
                                - (
                                    0
                                    if 10000 == 0
                                    else (
                                        ((s.premium_pool * s.protocol_fee_bps) // 10000)
                                        + (
                                            1
                                            if (
                                                (s.premium_pool * s.protocol_fee_bps)
                                                % 10000
                                            )
                                            < 0
                                            else 0
                                        )
                                    )
                                )
                            )
                        )
                        // (s.rate_long_exposure + s.rate_short_exposure)
                    )
                    + (
                        1
                        if (
                            (
                                (
                                    s.rate_long_exposure
                                    if (
                                        max(
                                            (0 - s.funding_cap_bps),
                                            min(
                                                (
                                                    0
                                                    if cmd.args["index_price_e8"] == 0
                                                    else (
                                                        (
                                                            (
                                                                10000
                                                                * (
                                                                    cmd.args[
                                                                        "mark_price_e8"
                                                                    ]
                                                                    - cmd.args[
                                                                        "index_price_e8"
                                                                    ]
                                                                )
                                                            )
                                                            // cmd.args[
                                                                "index_price_e8"
                                                            ]
                                                        )
                                                        + (
                                                            1
                                                            if (
                                                                (
                                                                    10000
                                                                    * (
                                                                        cmd.args[
                                                                            "mark_price_e8"
                                                                        ]
                                                                        - cmd.args[
                                                                            "index_price_e8"
                                                                        ]
                                                                    )
                                                                )
                                                                % cmd.args[
                                                                    "index_price_e8"
                                                                ]
                                                            )
                                                            < 0
                                                            else 0
                                                        )
                                                    )
                                                ),
                                                s.funding_cap_bps,
                                            ),
                                        )
                                        >= s.implied_rate_bps
                                    )
                                    else s.rate_short_exposure
                                )
                                * (
                                    s.premium_pool
                                    - (
                                        0
                                        if 10000 == 0
                                        else (
                                            (
                                                (s.premium_pool * s.protocol_fee_bps)
                                                // 10000
                                            )
                                            + (
                                                1
                                                if (
                                                    (
                                                        s.premium_pool
                                                        * s.protocol_fee_bps
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
                            % (s.rate_long_exposure + s.rate_short_exposure)
                        )
                        < 0
                        else 0
                    )
                )
            ),
            mark_price_e8=cmd.args["mark_price_e8"],
            premium_pool=0,
            protocol_fee_bps=s.protocol_fee_bps,
            protocol_fee_pool=(
                (
                    0
                    if 10000 == 0
                    else (
                        ((s.premium_pool * s.protocol_fee_bps) // 10000)
                        + (
                            1
                            if ((s.premium_pool * s.protocol_fee_bps) % 10000) < 0
                            else 0
                        )
                    )
                )
                + s.protocol_fee_pool
            ),
            rate_long_exposure=s.rate_long_exposure,
            rate_market_epoch=s.rate_market_epoch,
            rate_short_exposure=s.rate_short_exposure,
            realized_rate_bps=max(
                (0 - s.funding_cap_bps),
                min(
                    (
                        0
                        if cmd.args["index_price_e8"] == 0
                        else (
                            (
                                (
                                    10000
                                    * (
                                        cmd.args["mark_price_e8"]
                                        - cmd.args["index_price_e8"]
                                    )
                                )
                                // cmd.args["index_price_e8"]
                            )
                            + (
                                1
                                if (
                                    (
                                        10000
                                        * (
                                            cmd.args["mark_price_e8"]
                                            - cmd.args["index_price_e8"]
                                        )
                                    )
                                    % cmd.args["index_price_e8"]
                                )
                                < 0
                                else 0
                            )
                        )
                    ),
                    s.funding_cap_bps,
                ),
            ),
            settled_this_epoch=True,
            settlement_epoch=(1 + s.settlement_epoch),
            short_payout=(
                (
                    s.premium_pool
                    - (
                        0
                        if 10000 == 0
                        else (
                            ((s.premium_pool * s.protocol_fee_bps) // 10000)
                            + (
                                1
                                if ((s.premium_pool * s.protocol_fee_bps) % 10000) < 0
                                else 0
                            )
                        )
                    )
                )
                - (
                    0
                    if (s.rate_long_exposure + s.rate_short_exposure) == 0
                    else (
                        (
                            (
                                (
                                    s.rate_long_exposure
                                    if (
                                        max(
                                            (0 - s.funding_cap_bps),
                                            min(
                                                (
                                                    0
                                                    if cmd.args["index_price_e8"] == 0
                                                    else (
                                                        (
                                                            (
                                                                10000
                                                                * (
                                                                    cmd.args[
                                                                        "mark_price_e8"
                                                                    ]
                                                                    - cmd.args[
                                                                        "index_price_e8"
                                                                    ]
                                                                )
                                                            )
                                                            // cmd.args[
                                                                "index_price_e8"
                                                            ]
                                                        )
                                                        + (
                                                            1
                                                            if (
                                                                (
                                                                    10000
                                                                    * (
                                                                        cmd.args[
                                                                            "mark_price_e8"
                                                                        ]
                                                                        - cmd.args[
                                                                            "index_price_e8"
                                                                        ]
                                                                    )
                                                                )
                                                                % cmd.args[
                                                                    "index_price_e8"
                                                                ]
                                                            )
                                                            < 0
                                                            else 0
                                                        )
                                                    )
                                                ),
                                                s.funding_cap_bps,
                                            ),
                                        )
                                        >= s.implied_rate_bps
                                    )
                                    else s.rate_short_exposure
                                )
                                * (
                                    s.premium_pool
                                    - (
                                        0
                                        if 10000 == 0
                                        else (
                                            (
                                                (s.premium_pool * s.protocol_fee_bps)
                                                // 10000
                                            )
                                            + (
                                                1
                                                if (
                                                    (
                                                        s.premium_pool
                                                        * s.protocol_fee_bps
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
                            // (s.rate_long_exposure + s.rate_short_exposure)
                        )
                        + (
                            1
                            if (
                                (
                                    (
                                        s.rate_long_exposure
                                        if (
                                            max(
                                                (0 - s.funding_cap_bps),
                                                min(
                                                    (
                                                        0
                                                        if cmd.args["index_price_e8"]
                                                        == 0
                                                        else (
                                                            (
                                                                (
                                                                    10000
                                                                    * (
                                                                        cmd.args[
                                                                            "mark_price_e8"
                                                                        ]
                                                                        - cmd.args[
                                                                            "index_price_e8"
                                                                        ]
                                                                    )
                                                                )
                                                                // cmd.args[
                                                                    "index_price_e8"
                                                                ]
                                                            )
                                                            + (
                                                                1
                                                                if (
                                                                    (
                                                                        10000
                                                                        * (
                                                                            cmd.args[
                                                                                "mark_price_e8"
                                                                            ]
                                                                            - cmd.args[
                                                                                "index_price_e8"
                                                                            ]
                                                                        )
                                                                    )
                                                                    % cmd.args[
                                                                        "index_price_e8"
                                                                    ]
                                                                )
                                                                < 0
                                                                else 0
                                                            )
                                                        )
                                                    ),
                                                    s.funding_cap_bps,
                                                ),
                                            )
                                            >= s.implied_rate_bps
                                        )
                                        else s.rate_short_exposure
                                    )
                                    * (
                                        s.premium_pool
                                        - (
                                            0
                                            if 10000 == 0
                                            else (
                                                (
                                                    (
                                                        s.premium_pool
                                                        * s.protocol_fee_bps
                                                    )
                                                    // 10000
                                                )
                                                + (
                                                    1
                                                    if (
                                                        (
                                                            s.premium_pool
                                                            * s.protocol_fee_bps
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
                                % (s.rate_long_exposure + s.rate_short_exposure)
                            )
                            < 0
                            else 0
                        )
                    )
                )
            ),
        )
        effects = {
            "event": "RateEpochSettled",
            "implied_rate_bps": new_state.implied_rate_bps,
            "payout_long": new_state.long_payout,
            "payout_short": new_state.short_payout,
            "realized_rate_bps": new_state.realized_rate_bps,
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
#     # def advance_rate_epoch(self, ):
#     #     cmd = Command(tag='advance_rate_epoch', args={})
#     #     result = step(self.state, cmd)
#     #     if result.ok:
#     #         self.state = result.state
#
#     # @rule(auth_ok=st.integers())
#     # def emergency_freeze(self, auth_ok):
#     #     cmd = Command(tag='emergency_freeze', args={'auth_ok': auth_ok})
#     #     result = step(self.state, cmd)
#     #     if result.ok:
#     #         self.state = result.state
#
#     # @rule(amount=st.integers(), auth_ok=st.integers())
#     # def open_rate_long(self, amount, auth_ok):
#     #     cmd = Command(tag='open_rate_long', args={'amount': amount, 'auth_ok': auth_ok})
#     #     result = step(self.state, cmd)
#     #     if result.ok:
#     #         self.state = result.state
#
#     # @rule(amount=st.integers(), auth_ok=st.integers())
#     # def open_rate_short(self, amount, auth_ok):
#     #     cmd = Command(tag='open_rate_short', args={'amount': amount, 'auth_ok': auth_ok})
#     #     result = step(self.state, cmd)
#     #     if result.ok:
#     #         self.state = result.state
#
#     # @rule(mark_price_e8=st.integers(), index_price_e8=st.integers())
#     # def settle_rate_epoch(self, mark_price_e8, index_price_e8):
#     #     cmd = Command(tag='settle_rate_epoch', args={'mark_price_e8': mark_price_e8, 'index_price_e8': index_price_e8})
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
