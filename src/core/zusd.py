"""zUSD issuance kernel aligned with SimplexBorrow-style safety semantics.

Model highlights:
- single borrower vault (collateral + debt),
- explicit free debt vs stability-pool debt conservation,
- pending observations are non-authoritative until explicit commit,
- liquidation requires one fresh finalized price with no pending mismatch,
- recovery-mode gating (block mint/withdraw/sp-withdraw when TCR < CCR),
- deterministic liquidation into the stability pool,
- deterministic borrow/redemption fee mechanics with decaying base-rate hooks.

All arithmetic is integer-only.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Literal, Mapping, cast

from ..state.immutable_json import freeze_json_mapping
from .zusd_multi_redeem_selector import select_multi_redeem_vault

E8 = 100_000_000
BPS_SCALE = 10_000
MAX_AMOUNT_E8 = 10**30
_FAIL_CLOSED_ZUSD_ERRORS = (
    TypeError,
    ValueError,
    ArithmeticError,
    LookupError,
    AttributeError,
    RuntimeError,
    AssertionError,
)

ZUSDCommandTag = Literal[
    "advance_epoch",
    "bootstrap_oracle",
    "oracle_report",
    "oracle_commit",
    "deposit_collateral",
    "withdraw_collateral",
    "mint_zusd",
    "repay_zusd",
    "deposit_sp",
    "withdraw_sp",
    "redeem_zusd",
    "liquidate",
]


def _require_pos_int(v: Any, *, name: str) -> int:
    if not isinstance(v, int) or isinstance(v, bool) or v <= 0:
        raise ValueError(f"{name} must be a positive int")
    return int(v)


def _auth_ok(args: Mapping[str, Any]) -> bool:
    return args.get("auth_ok") is True


def _is_oracle_fresh(*, now_epoch: int, last_update_epoch: int, max_staleness_epochs: int, oracle_seen: bool) -> bool:
    if not oracle_seen:
        return False
    if max_staleness_epochs < 0:
        return False
    return (now_epoch - last_update_epoch) <= max_staleness_epochs


def _check_bounded_nonneg(v: int, *, name: str) -> None:
    if v < 0:
        raise ValueError(f"{name} must be non-negative")
    if v > MAX_AMOUNT_E8:
        raise ValueError(f"{name} exceeds MAX_AMOUNT_E8")


def _bounded_add(a: int, b: int, *, name: str) -> int:
    out = a + b
    _check_bounded_nonneg(out, name=name)
    return out


def _mcr_ok(*, collateral_e8: int, debt_e8: int, price_e8: int, mcr_bps: int) -> bool:
    if debt_e8 == 0:
        return True
    # collateral_value * 10000 >= debt * mcr
    # (collateral * price / 1e8) * 10000 >= debt * mcr
    # collateral * price * 10000 >= debt * mcr * 1e8
    return (collateral_e8 * price_e8 * BPS_SCALE) >= (debt_e8 * mcr_bps * E8)


def _mcr_headroom_num(*, collateral_e8: int, debt_e8: int, price_e8: int, mcr_bps: int) -> int:
    # Positive means the vault is above MCR. Lower positive values are closer to MCR.
    return (collateral_e8 * price_e8 * BPS_SCALE) - (debt_e8 * mcr_bps * E8)


def _solvent_at_price(*, collateral_e8: int, debt_e8: int, price_e8: int) -> bool:
    if debt_e8 == 0:
        return True
    # collateral_value >= debt
    return (collateral_e8 * price_e8) >= (debt_e8 * E8)


def _debt_floor_ok(*, debt_e8: int, min_debt_open_e8: int) -> bool:
    return debt_e8 == 0 or debt_e8 >= min_debt_open_e8


def _mul_div_up(a: int, b: int, den: int) -> int:
    if den <= 0:
        raise ValueError("denominator must be positive")
    if a < 0 or b < 0:
        raise ValueError("mul_div_up requires non-negative inputs")
    if a == 0 or b == 0:
        return 0
    return ((a * b) + den - 1) // den


def _decayed_base_rate_bps(*, base_rate_bps: int, now_epoch: int, last_epoch: int, decay_per_epoch_bps: int) -> int:
    if now_epoch < last_epoch:
        raise ValueError("base-rate last epoch cannot be in the future")
    elapsed = now_epoch - last_epoch
    decay = decay_per_epoch_bps * elapsed
    return max(0, base_rate_bps - decay)


def _effective_fee_bps(*, decayed_base_rate_bps: int, floor_bps: int, max_bps: int) -> int:
    fee_bps = floor_bps + decayed_base_rate_bps
    if fee_bps > max_bps:
        fee_bps = max_bps
    if fee_bps > BPS_SCALE:
        fee_bps = BPS_SCALE
    return fee_bps


@dataclass(frozen=True)
class ZUSDState:
    # Time/oracle
    now_epoch: int = 0
    oracle_seen: bool = False
    oracle_last_update_epoch: int = 0
    oracle_pending_report_epoch: int = 0
    price_e8: int = 0
    price_pending_e8: int = 0
    max_oracle_staleness_epochs: int = 100

    # Vault
    collateral_e8: int = 0
    debt_e8: int = 0

    # System debt split (SimplexBorrow convention)
    free_debt_e8: int = 0
    sp_debt_e8: int = 0
    sp_coll_e8: int = 0
    protocol_collateral_e8: int = 0
    protocol_revenue_zusd_cum_e8: int = 0
    liquidator_compensation_collateral_cum_e8: int = 0

    # Parameters
    mcr_bps: int = 11_000  # 110%
    ccr_bps: int = 15_000  # 150%
    min_debt_open_e8: int = 100 * E8
    max_debt_e8: int = 10_000_000 * E8
    max_debt_supply_e8: int = 20_000_000 * E8
    max_sp_coll_e8: int = 20_000_000 * E8
    max_protocol_coll_e8: int = 20_000_000 * E8

    # Fee mechanics (SimplexBorrow-style knobs)
    base_rate_bps: int = 0
    base_rate_last_epoch: int = 0
    base_rate_decay_per_epoch_bps: int = 0
    base_rate_borrow_bump_bps: int = 0
    base_rate_redeem_bump_bps: int = 0
    borrow_fee_floor_bps: int = 0
    borrow_fee_max_bps: int = 1_000
    redemption_fee_floor_bps: int = 0
    redemption_fee_max_bps: int = 1_000
    liquidation_gas_comp_fixed_collateral_e8: int = 0
    liquidation_gas_comp_bps: int = 0

    def __post_init__(self) -> None:
        for name in (
            "now_epoch",
            "oracle_last_update_epoch",
            "oracle_pending_report_epoch",
            "price_e8",
            "price_pending_e8",
            "max_oracle_staleness_epochs",
            "collateral_e8",
            "debt_e8",
            "free_debt_e8",
            "sp_debt_e8",
            "sp_coll_e8",
            "protocol_collateral_e8",
            "protocol_revenue_zusd_cum_e8",
            "liquidator_compensation_collateral_cum_e8",
            "min_debt_open_e8",
            "max_debt_e8",
            "max_debt_supply_e8",
            "max_sp_coll_e8",
            "max_protocol_coll_e8",
            "base_rate_bps",
            "base_rate_last_epoch",
            "base_rate_decay_per_epoch_bps",
            "base_rate_borrow_bump_bps",
            "base_rate_redeem_bump_bps",
            "borrow_fee_floor_bps",
            "borrow_fee_max_bps",
            "redemption_fee_floor_bps",
            "redemption_fee_max_bps",
            "liquidation_gas_comp_fixed_collateral_e8",
            "liquidation_gas_comp_bps",
        ):
            _check_bounded_nonneg(int(getattr(self, name)), name=name)
        if self.oracle_last_update_epoch > self.now_epoch:
            raise ValueError("oracle_last_update_epoch cannot be in the future")
        if self.oracle_pending_report_epoch > self.now_epoch:
            raise ValueError("oracle_pending_report_epoch cannot be in the future")
        if self.base_rate_last_epoch > self.now_epoch:
            raise ValueError("base_rate_last_epoch cannot be in the future")
        if self.oracle_seen:
            if self.price_e8 <= 0 or self.price_pending_e8 <= 0:
                raise ValueError("oracle_seen requires positive active and pending prices")
            if self.price_pending_e8 > self.price_e8:
                raise ValueError("require price_pending_e8 <= price_e8")
        else:
            if (
                self.price_e8 != 0
                or self.price_pending_e8 != 0
                or self.oracle_last_update_epoch != 0
                or self.oracle_pending_report_epoch != 0
            ):
                raise ValueError("oracle-not-seen state must be zeroed")
        if not (0 < self.mcr_bps <= self.ccr_bps):
            raise ValueError("require 0 < mcr_bps <= ccr_bps")
        if self.max_debt_e8 > self.max_debt_supply_e8:
            raise ValueError("max_debt_e8 cannot exceed max_debt_supply_e8")
        if not (0 <= self.base_rate_bps <= BPS_SCALE):
            raise ValueError("base_rate_bps out of bounds")
        if not (0 <= self.base_rate_decay_per_epoch_bps <= BPS_SCALE):
            raise ValueError("base_rate_decay_per_epoch_bps out of bounds")
        if not (0 <= self.base_rate_borrow_bump_bps <= BPS_SCALE):
            raise ValueError("base_rate_borrow_bump_bps out of bounds")
        if not (0 <= self.base_rate_redeem_bump_bps <= BPS_SCALE):
            raise ValueError("base_rate_redeem_bump_bps out of bounds")
        if not (0 <= self.borrow_fee_floor_bps <= self.borrow_fee_max_bps <= BPS_SCALE):
            raise ValueError("borrow_fee bps bounds invalid")
        if not (0 <= self.redemption_fee_floor_bps <= self.redemption_fee_max_bps <= BPS_SCALE):
            raise ValueError("redemption_fee bps bounds invalid")
        if not (0 <= self.liquidation_gas_comp_bps <= BPS_SCALE):
            raise ValueError("liquidation_gas_comp_bps out of bounds")


@dataclass(frozen=True)
class ZUSDCommand:
    tag: ZUSDCommandTag
    args: Mapping[str, Any]

    def __post_init__(self) -> None:
        object.__setattr__(
            self,
            "args",
            freeze_json_mapping(self.args, name="ZUSDCommand.args"),
        )


@dataclass(frozen=True)
class ZUSDStepResult:
    ok: bool
    state: ZUSDState | None = None
    effects: Mapping[str, Any] | None = None
    error: str | None = None


def init_state() -> ZUSDState:
    return ZUSDState()


def _tcr_ok(state: ZUSDState, *, price_e8: int | None = None) -> bool:
    p = int(state.price_e8 if price_e8 is None else price_e8)
    if state.debt_e8 == 0:
        return True
    total_coll_e8 = state.collateral_e8 + state.sp_coll_e8 + state.protocol_collateral_e8
    # TCR >= CCR
    return (total_coll_e8 * p * BPS_SCALE) >= (state.debt_e8 * state.ccr_bps * E8)


def in_recovery_mode(state: ZUSDState) -> bool:
    if not state.oracle_seen or state.price_e8 <= 0:
        return True
    return not _tcr_ok(state, price_e8=state.price_e8)


def check_invariants(state: ZUSDState) -> list[str]:
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
        or state.oracle_pending_report_epoch != 0
    ):
        failed.append("inv_oracle_unseen_zeroed")
    if (state.free_debt_e8 + state.sp_debt_e8) != state.debt_e8:
        failed.append("inv_supply_conservation")
    if state.debt_e8 > state.max_debt_supply_e8:
        failed.append("inv_total_debt_cap")
    if not _debt_floor_ok(debt_e8=state.debt_e8, min_debt_open_e8=state.min_debt_open_e8):
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
        collateral_e8=state.collateral_e8 + state.sp_coll_e8 + state.protocol_collateral_e8,
        debt_e8=state.debt_e8,
        price_e8=state.price_e8,
    ):
        failed.append("health_system_bad_debt")
    return failed


def _risky_ops_allowed(state: ZUSDState) -> bool:
    # Freeze risky operations while pending price differs from active.
    if not state.oracle_seen or state.price_e8 <= 0 or state.price_pending_e8 <= 0:
        return False
    if state.price_pending_e8 != state.price_e8:
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


def step(state: ZUSDState, cmd: ZUSDCommand) -> ZUSDStepResult:
    try:
        tag = str(cmd.tag)
        if tag == "advance_epoch":
            delta = _require_pos_int(cmd.args.get("delta"), name="delta")
            ns = ZUSDState(**{**state.__dict__, "now_epoch": _bounded_add(state.now_epoch, delta, name="now_epoch")})
            eff = {"event": "epoch_advanced", "delta": delta}

        elif tag == "bootstrap_oracle":
            if state.oracle_seen:
                return ZUSDStepResult(ok=False, error="oracle already bootstrapped")
            if not _auth_ok(cmd.args):
                return ZUSDStepResult(ok=False, error="bootstrap_oracle requires auth_ok=true")
            p = _require_pos_int(cmd.args.get("price_e8"), name="price_e8")
            ns = ZUSDState(
                **{
                    **state.__dict__,
                    "oracle_seen": True,
                    "oracle_last_update_epoch": state.now_epoch,
                    "oracle_pending_report_epoch": state.now_epoch,
                    "price_e8": p,
                    "price_pending_e8": p,
                }
            )
            eff = {"event": "oracle_bootstrapped", "price_e8": p}

        elif tag == "oracle_report":
            if not state.oracle_seen:
                return ZUSDStepResult(ok=False, error="oracle not bootstrapped")
            if not _auth_ok(cmd.args):
                return ZUSDStepResult(ok=False, error="oracle_report requires auth_ok=true")
            p = _require_pos_int(cmd.args.get("price_e8"), name="price_e8")
            if p > state.price_pending_e8:
                return ZUSDStepResult(ok=False, error="oracle_report requires non-increasing pending price")
            ns = ZUSDState(
                **{
                    **state.__dict__,
                    "price_pending_e8": p,
                    "oracle_pending_report_epoch": state.now_epoch,
                }
            )
            eff = {
                "event": "oracle_reported",
                "price_pending_e8": p,
                "observed_epoch": state.now_epoch,
            }

        elif tag == "oracle_commit":
            if not state.oracle_seen:
                return ZUSDStepResult(ok=False, error="oracle not bootstrapped")
            if not _auth_ok(cmd.args):
                return ZUSDStepResult(ok=False, error="oracle_commit requires auth_ok=true")
            if not _is_oracle_fresh(
                now_epoch=state.now_epoch,
                last_update_epoch=state.oracle_pending_report_epoch,
                max_staleness_epochs=state.max_oracle_staleness_epochs,
                oracle_seen=state.oracle_seen,
            ):
                return ZUSDStepResult(ok=False, error="oracle_commit blocked: pending observation is stale")
            ns = ZUSDState(
                **{
                    **state.__dict__,
                    "price_e8": state.price_pending_e8,
                    "oracle_last_update_epoch": state.oracle_pending_report_epoch,
                }
            )
            eff = {
                "event": "oracle_committed",
                "price_e8": state.price_pending_e8,
                "observed_epoch": state.oracle_pending_report_epoch,
            }

        elif tag == "deposit_collateral":
            amt = _require_pos_int(cmd.args.get("amount_e8"), name="amount_e8")
            ns = ZUSDState(**{**state.__dict__, "collateral_e8": _bounded_add(state.collateral_e8, amt, name="collateral_e8")})
            eff = {"event": "collateral_deposited", "amount_e8": amt}

        elif tag == "withdraw_collateral":
            amt = _require_pos_int(cmd.args.get("amount_e8"), name="amount_e8")
            if amt > state.collateral_e8:
                return ZUSDStepResult(ok=False, error="insufficient collateral")
            if state.debt_e8 > 0 and not _risky_ops_allowed(state):
                return ZUSDStepResult(ok=False, error="withdraw blocked by oracle freeze/staleness/recovery mode")
            post_coll = state.collateral_e8 - amt
            if not _mcr_ok(
                collateral_e8=post_coll,
                debt_e8=state.debt_e8,
                price_e8=state.price_e8,
                mcr_bps=state.mcr_bps,
            ):
                return ZUSDStepResult(ok=False, error="withdraw would violate MCR")
            ns = ZUSDState(**{**state.__dict__, "collateral_e8": post_coll})
            eff = {"event": "collateral_withdrawn", "amount_e8": amt}

        elif tag == "mint_zusd":
            amt = _require_pos_int(cmd.args.get("amount_e8"), name="amount_e8")
            if not _risky_ops_allowed(state):
                return ZUSDStepResult(ok=False, error="mint blocked by oracle freeze/staleness/recovery mode")
            if state.debt_e8 == 0 and amt < state.min_debt_open_e8:
                return ZUSDStepResult(ok=False, error="mint below min_debt_open_e8")
            decayed_base_rate = _decayed_base_rate_bps(
                base_rate_bps=state.base_rate_bps,
                now_epoch=state.now_epoch,
                last_epoch=state.base_rate_last_epoch,
                decay_per_epoch_bps=state.base_rate_decay_per_epoch_bps,
            )
            fee_bps = _effective_fee_bps(
                decayed_base_rate_bps=decayed_base_rate,
                floor_bps=state.borrow_fee_floor_bps,
                max_bps=state.borrow_fee_max_bps,
            )
            fee_e8 = _mul_div_up(amt, fee_bps, BPS_SCALE)
            debt_delta = amt + fee_e8
            new_debt = state.debt_e8 + debt_delta
            if new_debt > state.max_debt_e8:
                return ZUSDStepResult(ok=False, error="mint exceeds per-vault max_debt_e8")
            if new_debt > state.max_debt_supply_e8:
                return ZUSDStepResult(ok=False, error="mint exceeds max_debt_supply_e8")
            if not _mcr_ok(
                collateral_e8=state.collateral_e8,
                debt_e8=new_debt,
                price_e8=state.price_e8,
                mcr_bps=state.mcr_bps,
            ):
                return ZUSDStepResult(ok=False, error="mint would violate MCR")
            ns = ZUSDState(
                **{
                    **state.__dict__,
                    "debt_e8": new_debt,
                    "free_debt_e8": state.free_debt_e8 + debt_delta,
                    "protocol_revenue_zusd_cum_e8": state.protocol_revenue_zusd_cum_e8 + fee_e8,
                    "base_rate_bps": min(BPS_SCALE, decayed_base_rate + state.base_rate_borrow_bump_bps),
                    "base_rate_last_epoch": state.now_epoch,
                }
            )
            eff = {
                "event": "zusd_minted",
                "principal_e8": amt,
                "mint_fee_e8": fee_e8,
                "mint_fee_bps": fee_bps,
                "debt_delta_e8": debt_delta,
            }

        elif tag == "repay_zusd":
            amt = _require_pos_int(cmd.args.get("amount_e8"), name="amount_e8")
            if amt > state.debt_e8:
                return ZUSDStepResult(ok=False, error="repay exceeds debt")
            if amt > state.free_debt_e8:
                return ZUSDStepResult(ok=False, error="repay exceeds free debt balance")
            post_debt = state.debt_e8 - amt
            if not _debt_floor_ok(debt_e8=post_debt, min_debt_open_e8=state.min_debt_open_e8):
                return ZUSDStepResult(ok=False, error="repay would leave debt below min_debt_open_e8")
            ns = ZUSDState(
                **{
                    **state.__dict__,
                    "debt_e8": post_debt,
                    "free_debt_e8": state.free_debt_e8 - amt,
                }
            )
            eff = {"event": "zusd_repaid", "amount_e8": amt}

        elif tag == "deposit_sp":
            amt = _require_pos_int(cmd.args.get("amount_e8"), name="amount_e8")
            if amt > state.free_debt_e8:
                return ZUSDStepResult(ok=False, error="deposit_sp exceeds free debt balance")
            if (state.sp_debt_e8 + amt) > state.max_debt_supply_e8:
                return ZUSDStepResult(ok=False, error="deposit_sp exceeds max_debt_supply_e8")
            ns = ZUSDState(
                **{
                    **state.__dict__,
                    "free_debt_e8": state.free_debt_e8 - amt,
                    "sp_debt_e8": state.sp_debt_e8 + amt,
                }
            )
            eff = {"event": "sp_deposited", "amount_e8": amt}

        elif tag == "withdraw_sp":
            amt = _require_pos_int(cmd.args.get("amount_e8"), name="amount_e8")
            if amt > state.sp_debt_e8:
                return ZUSDStepResult(ok=False, error="withdraw_sp exceeds sp_debt")
            if not _risky_ops_allowed(state):
                return ZUSDStepResult(ok=False, error="withdraw_sp blocked by oracle freeze/staleness/recovery mode")
            if not _mcr_ok(
                collateral_e8=state.collateral_e8,
                debt_e8=state.debt_e8,
                price_e8=state.price_e8,
                mcr_bps=state.mcr_bps,
            ):
                return ZUSDStepResult(ok=False, error="withdraw_sp blocked: vault not at MCR")
            ns = ZUSDState(
                **{
                    **state.__dict__,
                    "sp_debt_e8": state.sp_debt_e8 - amt,
                    "free_debt_e8": state.free_debt_e8 + amt,
                }
            )
            eff = {"event": "sp_withdrawn", "amount_e8": amt}

        elif tag == "redeem_zusd":
            amt = _require_pos_int(cmd.args.get("amount_e8"), name="amount_e8")
            if not state.oracle_seen or state.price_e8 <= 0 or state.price_pending_e8 <= 0:
                return ZUSDStepResult(ok=False, error="redemption requires initialized oracle")
            if state.price_pending_e8 != state.price_e8:
                return ZUSDStepResult(ok=False, error="redemption blocked by oracle pending mismatch")
            if not _is_oracle_fresh(
                now_epoch=state.now_epoch,
                last_update_epoch=state.oracle_last_update_epoch,
                max_staleness_epochs=state.max_oracle_staleness_epochs,
                oracle_seen=state.oracle_seen,
            ):
                return ZUSDStepResult(ok=False, error="redemption blocked by stale oracle")
            if amt > state.debt_e8:
                return ZUSDStepResult(ok=False, error="redemption exceeds debt")
            if amt > state.free_debt_e8:
                return ZUSDStepResult(ok=False, error="redemption exceeds free debt")

            gross_collateral_e8 = (amt * E8) // state.price_e8
            if gross_collateral_e8 <= 0:
                return ZUSDStepResult(ok=False, error="redemption amount too small at current price")
            if gross_collateral_e8 > state.collateral_e8:
                return ZUSDStepResult(ok=False, error="insufficient vault collateral for redemption")

            decayed_base_rate = _decayed_base_rate_bps(
                base_rate_bps=state.base_rate_bps,
                now_epoch=state.now_epoch,
                last_epoch=state.base_rate_last_epoch,
                decay_per_epoch_bps=state.base_rate_decay_per_epoch_bps,
            )
            fee_bps = _effective_fee_bps(
                decayed_base_rate_bps=decayed_base_rate,
                floor_bps=state.redemption_fee_floor_bps,
                max_bps=state.redemption_fee_max_bps,
            )
            redemption_fee_coll_e8 = _mul_div_up(gross_collateral_e8, fee_bps, BPS_SCALE)
            if redemption_fee_coll_e8 >= gross_collateral_e8:
                return ZUSDStepResult(ok=False, error="redemption fee consumes all collateral")
            if (state.protocol_collateral_e8 + redemption_fee_coll_e8) > state.max_protocol_coll_e8:
                return ZUSDStepResult(ok=False, error="protocol collateral cap exceeded")

            collateral_out_e8 = gross_collateral_e8 - redemption_fee_coll_e8
            post_debt = state.debt_e8 - amt
            post_collateral = state.collateral_e8 - gross_collateral_e8
            if not _debt_floor_ok(debt_e8=post_debt, min_debt_open_e8=state.min_debt_open_e8):
                return ZUSDStepResult(ok=False, error="redemption would leave debt below min_debt_open_e8")
            if not _mcr_ok(
                collateral_e8=post_collateral,
                debt_e8=post_debt,
                price_e8=state.price_e8,
                mcr_bps=state.mcr_bps,
            ):
                return ZUSDStepResult(ok=False, error="redemption would violate MCR")

            ns = ZUSDState(
                **{
                    **state.__dict__,
                    "debt_e8": post_debt,
                    "free_debt_e8": state.free_debt_e8 - amt,
                    "collateral_e8": post_collateral,
                    "protocol_collateral_e8": state.protocol_collateral_e8 + redemption_fee_coll_e8,
                    "base_rate_bps": min(BPS_SCALE, decayed_base_rate + state.base_rate_redeem_bump_bps),
                    "base_rate_last_epoch": state.now_epoch,
                }
            )
            eff = {
                "event": "zusd_redeemed",
                "redeemed_zusd_e8": amt,
                "redeemed_collateral_gross_e8": gross_collateral_e8,
                "redeemed_collateral_out_e8": collateral_out_e8,
                "redemption_fee_collateral_e8": redemption_fee_coll_e8,
                "redemption_fee_bps": fee_bps,
            }

        elif tag == "liquidate":
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
                return ZUSDStepResult(
                    ok=False,
                    error="vault not under MCR at finalized price",
                )
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
            eff = {
                "event": "liquidated",
                "liquidated_debt_e8": liquidated_debt,
                "liquidated_collateral_e8": liquidated_coll,
                "sp_collateral_gain_e8": sp_collateral_gain,
                "liquidator_compensation_collateral_e8": liquidator_comp,
                "liquidation_gas_comp_fixed_collateral_e8": state.liquidation_gas_comp_fixed_collateral_e8,
                "liquidation_gas_comp_bps": state.liquidation_gas_comp_bps,
            }

        else:
            return ZUSDStepResult(ok=False, error=f"unknown action: {tag}")

        failed = check_invariants(ns)
        if failed:
            return ZUSDStepResult(ok=False, error=f"invariant violation: {','.join(failed)}")
        return ZUSDStepResult(ok=True, state=ns, effects=eff)
    except _FAIL_CLOSED_ZUSD_ERRORS as exc:
        return ZUSDStepResult(ok=False, error=str(exc))


# ---------------------------------------------------------------------------
# Multi-vault (a/b) model, aligned with SimplexBorrow two-trove posture.
# ---------------------------------------------------------------------------


VaultId = Literal["a", "b"]


@dataclass(frozen=True)
class ZUSDVault:
    collateral_e8: int = 0
    debt_e8: int = 0

    def __post_init__(self) -> None:
        _check_bounded_nonneg(self.collateral_e8, name="vault.collateral_e8")
        _check_bounded_nonneg(self.debt_e8, name="vault.debt_e8")


@dataclass(frozen=True)
class ZUSDMultiState:
    # Time/oracle
    now_epoch: int = 0
    oracle_seen: bool = False
    oracle_last_update_epoch: int = 0
    oracle_pending_report_epoch: int = 0
    price_e8: int = 0
    price_pending_e8: int = 0
    max_oracle_staleness_epochs: int = 100

    # Two vaults
    vault_a: ZUSDVault = ZUSDVault()
    vault_b: ZUSDVault = ZUSDVault()

    # System debt split
    free_debt_e8: int = 0
    sp_debt_e8: int = 0
    sp_coll_e8: int = 0
    protocol_collateral_e8: int = 0
    protocol_revenue_zusd_cum_e8: int = 0

    # Parameters
    mcr_bps: int = 11_000
    ccr_bps: int = 15_000
    min_debt_open_e8: int = 100 * E8
    max_debt_e8: int = 10_000_000 * E8
    max_debt_supply_e8: int = 20_000_000 * E8
    max_sp_coll_e8: int = 20_000_000 * E8
    max_protocol_coll_e8: int = 20_000_000 * E8

    # Fee mechanics
    base_rate_bps: int = 0
    base_rate_last_epoch: int = 0
    base_rate_decay_per_epoch_bps: int = 0
    base_rate_borrow_bump_bps: int = 0
    base_rate_redeem_bump_bps: int = 0
    borrow_fee_floor_bps: int = 0
    borrow_fee_max_bps: int = 1_000
    redemption_fee_floor_bps: int = 0
    redemption_fee_max_bps: int = 1_000

    def __post_init__(self) -> None:
        for name in (
            "now_epoch",
            "oracle_last_update_epoch",
            "oracle_pending_report_epoch",
            "price_e8",
            "price_pending_e8",
            "max_oracle_staleness_epochs",
            "free_debt_e8",
            "sp_debt_e8",
            "sp_coll_e8",
            "protocol_collateral_e8",
            "protocol_revenue_zusd_cum_e8",
            "min_debt_open_e8",
            "max_debt_e8",
            "max_debt_supply_e8",
            "max_sp_coll_e8",
            "max_protocol_coll_e8",
            "base_rate_bps",
            "base_rate_last_epoch",
            "base_rate_decay_per_epoch_bps",
            "base_rate_borrow_bump_bps",
            "base_rate_redeem_bump_bps",
            "borrow_fee_floor_bps",
            "borrow_fee_max_bps",
            "redemption_fee_floor_bps",
            "redemption_fee_max_bps",
        ):
            _check_bounded_nonneg(int(getattr(self, name)), name=name)
        if self.oracle_last_update_epoch > self.now_epoch:
            raise ValueError("oracle_last_update_epoch cannot be in the future")
        if self.oracle_pending_report_epoch > self.now_epoch:
            raise ValueError("oracle_pending_report_epoch cannot be in the future")
        if self.base_rate_last_epoch > self.now_epoch:
            raise ValueError("base_rate_last_epoch cannot be in the future")
        if self.oracle_seen:
            if self.price_e8 <= 0 or self.price_pending_e8 <= 0:
                raise ValueError("oracle_seen requires positive active and pending prices")
            if self.price_pending_e8 > self.price_e8:
                raise ValueError("require price_pending_e8 <= price_e8")
        else:
            if (
                self.price_e8 != 0
                or self.price_pending_e8 != 0
                or self.oracle_last_update_epoch != 0
                or self.oracle_pending_report_epoch != 0
            ):
                raise ValueError("oracle-not-seen state must be zeroed")
        if not (0 < self.mcr_bps <= self.ccr_bps):
            raise ValueError("require 0 < mcr_bps <= ccr_bps")
        if self.max_debt_e8 > self.max_debt_supply_e8:
            raise ValueError("max_debt_e8 cannot exceed max_debt_supply_e8")
        if not (0 <= self.base_rate_bps <= BPS_SCALE):
            raise ValueError("base_rate_bps out of bounds")
        if not (0 <= self.base_rate_decay_per_epoch_bps <= BPS_SCALE):
            raise ValueError("base_rate_decay_per_epoch_bps out of bounds")
        if not (0 <= self.base_rate_borrow_bump_bps <= BPS_SCALE):
            raise ValueError("base_rate_borrow_bump_bps out of bounds")
        if not (0 <= self.base_rate_redeem_bump_bps <= BPS_SCALE):
            raise ValueError("base_rate_redeem_bump_bps out of bounds")
        if not (0 <= self.borrow_fee_floor_bps <= self.borrow_fee_max_bps <= BPS_SCALE):
            raise ValueError("borrow_fee bps bounds invalid")
        if not (0 <= self.redemption_fee_floor_bps <= self.redemption_fee_max_bps <= BPS_SCALE):
            raise ValueError("redemption_fee bps bounds invalid")


@dataclass(frozen=True)
class ZUSDMultiCommand:
    tag: ZUSDCommandTag
    args: Mapping[str, Any]

    def __post_init__(self) -> None:
        object.__setattr__(
            self,
            "args",
            freeze_json_mapping(self.args, name="ZUSDMultiCommand.args"),
        )


@dataclass(frozen=True)
class ZUSDMultiStepResult:
    ok: bool
    state: ZUSDMultiState | None = None
    effects: Mapping[str, Any] | None = None
    error: str | None = None


def init_multi_state() -> ZUSDMultiState:
    return ZUSDMultiState()


def _get_vault(state: ZUSDMultiState, vault: VaultId) -> ZUSDVault:
    return state.vault_a if vault == "a" else state.vault_b


def _set_vault(state: ZUSDMultiState, vault: VaultId, v: ZUSDVault) -> ZUSDMultiState:
    if vault == "a":
        return ZUSDMultiState(**{**state.__dict__, "vault_a": v})
    return ZUSDMultiState(**{**state.__dict__, "vault_b": v})


def _parse_vault_id(args: Mapping[str, Any]) -> VaultId:
    raw = args.get("vault")
    if raw not in ("a", "b"):
        raise ValueError("vault must be 'a' or 'b'")
    return cast(VaultId, raw)


def _total_debt(state: ZUSDMultiState) -> int:
    return state.vault_a.debt_e8 + state.vault_b.debt_e8


def _total_collateral(state: ZUSDMultiState) -> int:
    return state.vault_a.collateral_e8 + state.vault_b.collateral_e8


def _multi_tcr_ok(state: ZUSDMultiState, *, price_e8: int | None = None) -> bool:
    p = int(state.price_e8 if price_e8 is None else price_e8)
    td = _total_debt(state)
    if td == 0:
        return True
    total_coll_e8 = _total_collateral(state) + state.sp_coll_e8 + state.protocol_collateral_e8
    return (total_coll_e8 * p * BPS_SCALE) >= (td * state.ccr_bps * E8)


def in_multi_recovery_mode(state: ZUSDMultiState) -> bool:
    if not state.oracle_seen or state.price_e8 <= 0:
        return True
    return not _multi_tcr_ok(state, price_e8=state.price_e8)


def check_multi_invariants(state: ZUSDMultiState) -> list[str]:
    """Return hard multi-vault accounting and representation failures."""

    failed: list[str] = []
    if state.oracle_seen and (state.price_e8 <= 0 or state.price_pending_e8 <= 0):
        failed.append("inv_oracle_seen_positive_prices")
    if state.oracle_seen and state.price_pending_e8 > state.price_e8:
        failed.append("inv_pending_le_active")
    if not state.oracle_seen and (
        state.price_e8 != 0
        or state.price_pending_e8 != 0
        or state.oracle_last_update_epoch != 0
        or state.oracle_pending_report_epoch != 0
    ):
        failed.append("inv_oracle_unseen_zeroed")

    td = _total_debt(state)
    if (state.free_debt_e8 + state.sp_debt_e8) != td:
        failed.append("inv_supply_conservation")
    if td > state.max_debt_supply_e8:
        failed.append("inv_total_debt_cap")
    if not _debt_floor_ok(debt_e8=state.vault_a.debt_e8, min_debt_open_e8=state.min_debt_open_e8):
        failed.append("inv_debt_floor_a")
    if not _debt_floor_ok(debt_e8=state.vault_b.debt_e8, min_debt_open_e8=state.min_debt_open_e8):
        failed.append("inv_debt_floor_b")
    return failed


def check_multi_health_conditions(state: ZUSDMultiState) -> list[str]:
    """Return finalized-price multi-vault health facts as data."""

    failed: list[str] = []
    if not state.oracle_seen or state.price_e8 <= 0:
        return failed
    for label, vault in (("a", state.vault_a), ("b", state.vault_b)):
        if vault.debt_e8 > 0 and not _mcr_ok(
            collateral_e8=vault.collateral_e8,
            debt_e8=vault.debt_e8,
            price_e8=state.price_e8,
            mcr_bps=state.mcr_bps,
        ):
            failed.append(f"health_vault_{label}_below_mcr")
        if not _solvent_at_price(
            collateral_e8=vault.collateral_e8,
            debt_e8=vault.debt_e8,
            price_e8=state.price_e8,
        ):
            failed.append(f"health_vault_{label}_bad_debt")

    if not _solvent_at_price(
        collateral_e8=_total_collateral(state) + state.sp_coll_e8 + state.protocol_collateral_e8,
        debt_e8=_total_debt(state),
        price_e8=state.price_e8,
    ):
        failed.append("health_system_bad_debt")
    return failed


def _multi_risky_ops_allowed(state: ZUSDMultiState) -> bool:
    if not state.oracle_seen or state.price_e8 <= 0 or state.price_pending_e8 <= 0:
        return False
    if state.price_pending_e8 != state.price_e8:
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


def step_multi(state: ZUSDMultiState, cmd: ZUSDMultiCommand) -> ZUSDMultiStepResult:
    try:
        tag = str(cmd.tag)
        if tag == "advance_epoch":
            delta = _require_pos_int(cmd.args.get("delta"), name="delta")
            ns = ZUSDMultiState(**{**state.__dict__, "now_epoch": _bounded_add(state.now_epoch, delta, name="now_epoch")})
            eff = {"event": "epoch_advanced", "delta": delta}

        elif tag == "bootstrap_oracle":
            if state.oracle_seen:
                return ZUSDMultiStepResult(ok=False, error="oracle already bootstrapped")
            if not _auth_ok(cmd.args):
                return ZUSDMultiStepResult(ok=False, error="bootstrap_oracle requires auth_ok=true")
            p = _require_pos_int(cmd.args.get("price_e8"), name="price_e8")
            ns = ZUSDMultiState(
                **{
                    **state.__dict__,
                    "oracle_seen": True,
                    "oracle_last_update_epoch": state.now_epoch,
                    "oracle_pending_report_epoch": state.now_epoch,
                    "price_e8": p,
                    "price_pending_e8": p,
                }
            )
            eff = {"event": "oracle_bootstrapped", "price_e8": p}

        elif tag == "oracle_report":
            if not state.oracle_seen:
                return ZUSDMultiStepResult(ok=False, error="oracle not bootstrapped")
            if not _auth_ok(cmd.args):
                return ZUSDMultiStepResult(ok=False, error="oracle_report requires auth_ok=true")
            p = _require_pos_int(cmd.args.get("price_e8"), name="price_e8")
            if p > state.price_pending_e8:
                return ZUSDMultiStepResult(ok=False, error="oracle_report requires non-increasing pending price")
            ns = ZUSDMultiState(
                **{
                    **state.__dict__,
                    "price_pending_e8": p,
                    "oracle_pending_report_epoch": state.now_epoch,
                }
            )
            eff = {
                "event": "oracle_reported",
                "price_pending_e8": p,
                "observed_epoch": state.now_epoch,
            }

        elif tag == "oracle_commit":
            if not state.oracle_seen:
                return ZUSDMultiStepResult(ok=False, error="oracle not bootstrapped")
            if not _auth_ok(cmd.args):
                return ZUSDMultiStepResult(ok=False, error="oracle_commit requires auth_ok=true")
            if not _is_oracle_fresh(
                now_epoch=state.now_epoch,
                last_update_epoch=state.oracle_pending_report_epoch,
                max_staleness_epochs=state.max_oracle_staleness_epochs,
                oracle_seen=state.oracle_seen,
            ):
                return ZUSDMultiStepResult(ok=False, error="oracle_commit blocked: pending observation is stale")
            ns = ZUSDMultiState(
                **{
                    **state.__dict__,
                    "price_e8": state.price_pending_e8,
                    "oracle_last_update_epoch": state.oracle_pending_report_epoch,
                }
            )
            eff = {
                "event": "oracle_committed",
                "price_e8": state.price_pending_e8,
                "observed_epoch": state.oracle_pending_report_epoch,
            }

        elif tag == "deposit_collateral":
            amt = _require_pos_int(cmd.args.get("amount_e8"), name="amount_e8")
            vid = _parse_vault_id(cmd.args)
            v = _get_vault(state, vid)
            nv = ZUSDVault(collateral_e8=_bounded_add(v.collateral_e8, amt, name="vault.collateral_e8"), debt_e8=v.debt_e8)
            ns = _set_vault(state, vid, nv)
            eff = {"event": "collateral_deposited", "vault": vid, "amount_e8": amt}

        elif tag == "withdraw_collateral":
            amt = _require_pos_int(cmd.args.get("amount_e8"), name="amount_e8")
            vid = _parse_vault_id(cmd.args)
            v = _get_vault(state, vid)
            if amt > v.collateral_e8:
                return ZUSDMultiStepResult(ok=False, error="insufficient collateral")
            if v.debt_e8 > 0 and not _multi_risky_ops_allowed(state):
                return ZUSDMultiStepResult(ok=False, error="withdraw blocked by oracle freeze/staleness/recovery mode")
            new_coll = v.collateral_e8 - amt
            if not _mcr_ok(
                collateral_e8=new_coll,
                debt_e8=v.debt_e8,
                price_e8=state.price_e8,
                mcr_bps=state.mcr_bps,
            ):
                return ZUSDMultiStepResult(ok=False, error="withdraw would violate MCR")
            ns = _set_vault(state, vid, ZUSDVault(collateral_e8=new_coll, debt_e8=v.debt_e8))
            eff = {"event": "collateral_withdrawn", "vault": vid, "amount_e8": amt}

        elif tag == "mint_zusd":
            amt = _require_pos_int(cmd.args.get("amount_e8"), name="amount_e8")
            vid = _parse_vault_id(cmd.args)
            v = _get_vault(state, vid)
            if not _multi_risky_ops_allowed(state):
                return ZUSDMultiStepResult(ok=False, error="mint blocked by oracle freeze/staleness/recovery mode")
            if v.debt_e8 == 0 and amt < state.min_debt_open_e8:
                return ZUSDMultiStepResult(ok=False, error="mint below min_debt_open_e8")
            decayed_base_rate = _decayed_base_rate_bps(
                base_rate_bps=state.base_rate_bps,
                now_epoch=state.now_epoch,
                last_epoch=state.base_rate_last_epoch,
                decay_per_epoch_bps=state.base_rate_decay_per_epoch_bps,
            )
            fee_bps = _effective_fee_bps(
                decayed_base_rate_bps=decayed_base_rate,
                floor_bps=state.borrow_fee_floor_bps,
                max_bps=state.borrow_fee_max_bps,
            )
            fee_e8 = _mul_div_up(amt, fee_bps, BPS_SCALE)
            debt_delta = amt + fee_e8
            new_debt = v.debt_e8 + debt_delta
            if new_debt > state.max_debt_e8:
                return ZUSDMultiStepResult(ok=False, error="mint exceeds per-vault max_debt_e8")
            if (_total_debt(state) + debt_delta) > state.max_debt_supply_e8:
                return ZUSDMultiStepResult(ok=False, error="mint exceeds max_debt_supply_e8")
            if not _mcr_ok(
                collateral_e8=v.collateral_e8,
                debt_e8=new_debt,
                price_e8=state.price_e8,
                mcr_bps=state.mcr_bps,
            ):
                return ZUSDMultiStepResult(ok=False, error="mint would violate MCR")
            ns0 = _set_vault(state, vid, ZUSDVault(collateral_e8=v.collateral_e8, debt_e8=new_debt))
            ns = ZUSDMultiState(
                **{
                    **ns0.__dict__,
                    "free_debt_e8": state.free_debt_e8 + debt_delta,
                    "protocol_revenue_zusd_cum_e8": state.protocol_revenue_zusd_cum_e8 + fee_e8,
                    "base_rate_bps": min(BPS_SCALE, decayed_base_rate + state.base_rate_borrow_bump_bps),
                    "base_rate_last_epoch": state.now_epoch,
                }
            )
            eff = {
                "event": "zusd_minted",
                "vault": vid,
                "principal_e8": amt,
                "mint_fee_e8": fee_e8,
                "mint_fee_bps": fee_bps,
                "debt_delta_e8": debt_delta,
            }

        elif tag == "repay_zusd":
            amt = _require_pos_int(cmd.args.get("amount_e8"), name="amount_e8")
            vid = _parse_vault_id(cmd.args)
            v = _get_vault(state, vid)
            if amt > v.debt_e8:
                return ZUSDMultiStepResult(ok=False, error="repay exceeds vault debt")
            if amt > state.free_debt_e8:
                return ZUSDMultiStepResult(ok=False, error="repay exceeds free debt balance")
            post_debt = v.debt_e8 - amt
            if not _debt_floor_ok(debt_e8=post_debt, min_debt_open_e8=state.min_debt_open_e8):
                return ZUSDMultiStepResult(ok=False, error="repay would leave vault debt below min_debt_open_e8")
            ns0 = _set_vault(state, vid, ZUSDVault(collateral_e8=v.collateral_e8, debt_e8=post_debt))
            ns = ZUSDMultiState(**{**ns0.__dict__, "free_debt_e8": state.free_debt_e8 - amt})
            eff = {"event": "zusd_repaid", "vault": vid, "amount_e8": amt}

        elif tag == "deposit_sp":
            amt = _require_pos_int(cmd.args.get("amount_e8"), name="amount_e8")
            if amt > state.free_debt_e8:
                return ZUSDMultiStepResult(ok=False, error="deposit_sp exceeds free debt balance")
            if (state.sp_debt_e8 + amt) > state.max_debt_supply_e8:
                return ZUSDMultiStepResult(ok=False, error="deposit_sp exceeds max_debt_supply_e8")
            ns = ZUSDMultiState(
                **{
                    **state.__dict__,
                    "free_debt_e8": state.free_debt_e8 - amt,
                    "sp_debt_e8": state.sp_debt_e8 + amt,
                }
            )
            eff = {"event": "sp_deposited", "amount_e8": amt}

        elif tag == "withdraw_sp":
            amt = _require_pos_int(cmd.args.get("amount_e8"), name="amount_e8")
            if amt > state.sp_debt_e8:
                return ZUSDMultiStepResult(ok=False, error="withdraw_sp exceeds sp_debt")
            if not _multi_risky_ops_allowed(state):
                return ZUSDMultiStepResult(ok=False, error="withdraw_sp blocked by oracle freeze/staleness/recovery mode")
            if not _mcr_ok(
                collateral_e8=state.vault_a.collateral_e8,
                debt_e8=state.vault_a.debt_e8,
                price_e8=state.price_e8,
                mcr_bps=state.mcr_bps,
            ):
                return ZUSDMultiStepResult(ok=False, error="withdraw_sp blocked: vault a not at MCR")
            if not _mcr_ok(
                collateral_e8=state.vault_b.collateral_e8,
                debt_e8=state.vault_b.debt_e8,
                price_e8=state.price_e8,
                mcr_bps=state.mcr_bps,
            ):
                return ZUSDMultiStepResult(ok=False, error="withdraw_sp blocked: vault b not at MCR")
            ns = ZUSDMultiState(
                **{
                    **state.__dict__,
                    "sp_debt_e8": state.sp_debt_e8 - amt,
                    "free_debt_e8": state.free_debt_e8 + amt,
                }
            )
            eff = {"event": "sp_withdrawn", "amount_e8": amt}

        elif tag == "redeem_zusd":
            amt = _require_pos_int(cmd.args.get("amount_e8"), name="amount_e8")
            if not state.oracle_seen or state.price_e8 <= 0 or state.price_pending_e8 <= 0:
                return ZUSDMultiStepResult(ok=False, error="redemption requires initialized oracle")
            if state.price_pending_e8 != state.price_e8:
                return ZUSDMultiStepResult(ok=False, error="redemption blocked by oracle pending mismatch")
            if not _is_oracle_fresh(
                now_epoch=state.now_epoch,
                last_update_epoch=state.oracle_last_update_epoch,
                max_staleness_epochs=state.max_oracle_staleness_epochs,
                oracle_seen=state.oracle_seen,
            ):
                return ZUSDMultiStepResult(ok=False, error="redemption blocked by stale oracle")
            if amt > state.free_debt_e8:
                return ZUSDMultiStepResult(ok=False, error="redemption exceeds free debt")

            gross_collateral_e8 = (amt * E8) // state.price_e8
            if gross_collateral_e8 <= 0:
                return ZUSDMultiStepResult(ok=False, error="redemption amount too small at current price")

            decayed_base_rate = _decayed_base_rate_bps(
                base_rate_bps=state.base_rate_bps,
                now_epoch=state.now_epoch,
                last_epoch=state.base_rate_last_epoch,
                decay_per_epoch_bps=state.base_rate_decay_per_epoch_bps,
            )
            fee_bps = _effective_fee_bps(
                decayed_base_rate_bps=decayed_base_rate,
                floor_bps=state.redemption_fee_floor_bps,
                max_bps=state.redemption_fee_max_bps,
            )
            redemption_fee_coll_e8 = _mul_div_up(gross_collateral_e8, fee_bps, BPS_SCALE)
            if redemption_fee_coll_e8 >= gross_collateral_e8:
                return ZUSDMultiStepResult(ok=False, error="redemption fee consumes all collateral")
            if (state.protocol_collateral_e8 + redemption_fee_coll_e8) > state.max_protocol_coll_e8:
                return ZUSDMultiStepResult(ok=False, error="protocol collateral cap exceeded")

            explicit_vault = cmd.args.get("vault")
            auto_selected = explicit_vault is None
            if explicit_vault in ("a", "b"):
                vid = explicit_vault
                v = _get_vault(state, vid)
                if amt > v.debt_e8:
                    return ZUSDMultiStepResult(ok=False, error="redemption exceeds vault debt")
                if gross_collateral_e8 > v.collateral_e8:
                    return ZUSDMultiStepResult(ok=False, error="insufficient vault collateral for redemption")
                post_debt = v.debt_e8 - amt
                post_collateral = v.collateral_e8 - gross_collateral_e8
                if not _mcr_ok(
                    collateral_e8=post_collateral,
                    debt_e8=post_debt,
                    price_e8=state.price_e8,
                    mcr_bps=state.mcr_bps,
                ):
                    return ZUSDMultiStepResult(ok=False, error="redemption would violate MCR")
            elif explicit_vault is None:
                selection = select_multi_redeem_vault(
                    amount_e8=amt,
                    price_e8=state.price_e8,
                    mcr_bps=state.mcr_bps,
                    vault_a_collateral_e8=state.vault_a.collateral_e8,
                    vault_a_debt_e8=state.vault_a.debt_e8,
                    vault_b_collateral_e8=state.vault_b.collateral_e8,
                    vault_b_debt_e8=state.vault_b.debt_e8,
                    min_debt_open_e8=state.min_debt_open_e8,
                )
                if selection.selected_vault is None:
                    return ZUSDMultiStepResult(ok=False, error="no redeemable vault for amount under policy")
                vid = selection.selected_vault
                if selection.selected_post_collateral_e8 is None or selection.selected_post_debt_e8 is None:
                    return ZUSDMultiStepResult(ok=False, error="redeem selection missing post-state")
                post_collateral = int(selection.selected_post_collateral_e8)
                post_debt = int(selection.selected_post_debt_e8)
            else:
                return ZUSDMultiStepResult(ok=False, error="vault must be 'a' or 'b'")

            if not _debt_floor_ok(debt_e8=post_debt, min_debt_open_e8=state.min_debt_open_e8):
                return ZUSDMultiStepResult(ok=False, error="redemption would leave vault debt below min_debt_open_e8")

            collateral_out_e8 = gross_collateral_e8 - redemption_fee_coll_e8

            ns0 = _set_vault(state, vid, ZUSDVault(collateral_e8=post_collateral, debt_e8=post_debt))
            ns = ZUSDMultiState(
                **{
                    **ns0.__dict__,
                    "free_debt_e8": state.free_debt_e8 - amt,
                    "protocol_collateral_e8": state.protocol_collateral_e8 + redemption_fee_coll_e8,
                    "base_rate_bps": min(BPS_SCALE, decayed_base_rate + state.base_rate_redeem_bump_bps),
                    "base_rate_last_epoch": state.now_epoch,
                }
            )
            eff = {
                "event": "zusd_redeemed",
                "vault": vid,
                "redeemed_zusd_e8": amt,
                "redeemed_collateral_gross_e8": gross_collateral_e8,
                "redeemed_collateral_out_e8": collateral_out_e8,
                "redemption_fee_collateral_e8": redemption_fee_coll_e8,
                "redemption_fee_bps": fee_bps,
                "selection_policy": "closest_to_mcr" if auto_selected else "explicit_vault",
            }

        elif tag == "liquidate":
            if not state.oracle_seen or state.price_e8 <= 0:
                return ZUSDMultiStepResult(
                    ok=False,
                    error="liquidation requires initialized finalized oracle price",
                )
            if state.price_pending_e8 != state.price_e8:
                return ZUSDMultiStepResult(
                    ok=False,
                    error="liquidation blocked by oracle pending mismatch",
                )
            if not _is_oracle_fresh(
                now_epoch=state.now_epoch,
                last_update_epoch=state.oracle_last_update_epoch,
                max_staleness_epochs=state.max_oracle_staleness_epochs,
                oracle_seen=state.oracle_seen,
            ):
                return ZUSDMultiStepResult(
                    ok=False,
                    error="liquidation blocked by stale finalized oracle",
                )
            vid = _parse_vault_id(cmd.args)
            v = _get_vault(state, vid)
            if v.debt_e8 <= 0:
                return ZUSDMultiStepResult(ok=False, error="no vault debt to liquidate")
            if _mcr_ok(
                collateral_e8=v.collateral_e8,
                debt_e8=v.debt_e8,
                price_e8=state.price_e8,
                mcr_bps=state.mcr_bps,
            ):
                return ZUSDMultiStepResult(
                    ok=False,
                    error="vault not under MCR at finalized price",
                )
            if v.debt_e8 > state.sp_debt_e8:
                return ZUSDMultiStepResult(ok=False, error="stability pool cannot absorb debt")
            if (state.sp_coll_e8 + v.collateral_e8) > state.max_sp_coll_e8:
                return ZUSDMultiStepResult(ok=False, error="stability pool collateral cap exceeded")
            ns0 = _set_vault(state, vid, ZUSDVault(collateral_e8=0, debt_e8=0))
            ns = ZUSDMultiState(
                **{
                    **ns0.__dict__,
                    "sp_debt_e8": state.sp_debt_e8 - v.debt_e8,
                    "sp_coll_e8": state.sp_coll_e8 + v.collateral_e8,
                }
            )
            eff = {
                "event": "liquidated",
                "vault": vid,
                "liquidated_debt_e8": v.debt_e8,
                "liquidated_collateral_e8": v.collateral_e8,
            }

        else:
            return ZUSDMultiStepResult(ok=False, error=f"unknown action: {tag}")

        failed = check_multi_invariants(ns)
        if failed:
            return ZUSDMultiStepResult(ok=False, error=f"invariant violation: {','.join(failed)}")
        return ZUSDMultiStepResult(ok=True, state=ns, effects=eff)
    except _FAIL_CLOSED_ZUSD_ERRORS as exc:
        return ZUSDMultiStepResult(ok=False, error=str(exc))
