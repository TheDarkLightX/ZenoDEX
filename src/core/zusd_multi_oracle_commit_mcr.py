from __future__ import annotations

from dataclasses import dataclass


BPS_SCALE = 10_000
E8 = 100_000_000


@dataclass(frozen=True)
class ZUSDMultiOracleCommitMCROutcome:
    price_pending_e8: int
    mcr_bps: int
    vault_a_mcr_ok: bool
    vault_b_mcr_ok: bool
    mcr_ok_at_pending: bool


def _require_pos_int(value: int, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value <= 0:
        raise ValueError(f"{name} must be a positive int")
    return int(value)


def _require_non_negative_int(value: int, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise ValueError(f"{name} must be a non-negative int")
    return int(value)


def _mcr_ok(*, collateral_e8: int, debt_e8: int, price_e8: int, mcr_bps: int) -> bool:
    if debt_e8 == 0:
        return True
    return (collateral_e8 * price_e8 * BPS_SCALE) >= (debt_e8 * mcr_bps * E8)


def check_multi_oracle_commit_mcr(
    *,
    price_pending_e8: int,
    mcr_bps: int,
    vault_a_collateral_e8: int,
    vault_a_debt_e8: int,
    vault_b_collateral_e8: int,
    vault_b_debt_e8: int,
) -> ZUSDMultiOracleCommitMCROutcome:
    pending = _require_non_negative_int(price_pending_e8, name="price_pending_e8")
    mcr = _require_pos_int(mcr_bps, name="mcr_bps")
    coll_a = _require_non_negative_int(vault_a_collateral_e8, name="vault_a_collateral_e8")
    debt_a = _require_non_negative_int(vault_a_debt_e8, name="vault_a_debt_e8")
    coll_b = _require_non_negative_int(vault_b_collateral_e8, name="vault_b_collateral_e8")
    debt_b = _require_non_negative_int(vault_b_debt_e8, name="vault_b_debt_e8")

    vault_a_mcr_ok = _mcr_ok(
        collateral_e8=coll_a,
        debt_e8=debt_a,
        price_e8=pending,
        mcr_bps=mcr,
    )
    vault_b_mcr_ok = _mcr_ok(
        collateral_e8=coll_b,
        debt_e8=debt_b,
        price_e8=pending,
        mcr_bps=mcr,
    )
    return ZUSDMultiOracleCommitMCROutcome(
        price_pending_e8=pending,
        mcr_bps=mcr,
        vault_a_mcr_ok=vault_a_mcr_ok,
        vault_b_mcr_ok=vault_b_mcr_ok,
        mcr_ok_at_pending=bool(vault_a_mcr_ok and vault_b_mcr_ok),
    )
