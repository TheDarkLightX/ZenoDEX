from __future__ import annotations

from dataclasses import dataclass
from typing import Literal, Optional

E8 = 100_000_000
BPS_SCALE = 10_000
VaultId = Literal["a", "b"]


@dataclass(frozen=True)
class ZUSDMultiRedeemSelectorOutcome:
    amount_e8: int
    price_e8: int
    gross_collateral_e8: int
    candidate_a_ok: bool
    candidate_b_ok: bool
    headroom_a_before_e8: int
    headroom_b_before_e8: int
    selected_vault: Optional[VaultId]
    selected_post_collateral_e8: Optional[int]
    selected_post_debt_e8: Optional[int]


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


def _debt_floor_ok(*, debt_e8: int, min_debt_open_e8: int) -> bool:
    return debt_e8 == 0 or debt_e8 >= min_debt_open_e8


def _mcr_headroom_num(*, collateral_e8: int, debt_e8: int, price_e8: int, mcr_bps: int) -> int:
    return (collateral_e8 * price_e8 * BPS_SCALE) - (debt_e8 * mcr_bps * E8)


def select_multi_redeem_vault(
    *,
    amount_e8: int,
    price_e8: int,
    mcr_bps: int,
    vault_a_collateral_e8: int,
    vault_a_debt_e8: int,
    vault_b_collateral_e8: int,
    vault_b_debt_e8: int,
    min_debt_open_e8: int = 0,
) -> ZUSDMultiRedeemSelectorOutcome:
    amount = _require_pos_int(amount_e8, name="amount_e8")
    price = _require_pos_int(price_e8, name="price_e8")
    mcr = _require_pos_int(mcr_bps, name="mcr_bps")
    min_debt = _require_non_negative_int(min_debt_open_e8, name="min_debt_open_e8")
    coll_a = _require_non_negative_int(vault_a_collateral_e8, name="vault_a_collateral_e8")
    debt_a = _require_non_negative_int(vault_a_debt_e8, name="vault_a_debt_e8")
    coll_b = _require_non_negative_int(vault_b_collateral_e8, name="vault_b_collateral_e8")
    debt_b = _require_non_negative_int(vault_b_debt_e8, name="vault_b_debt_e8")

    gross_collateral_e8 = (amount * E8) // price
    if gross_collateral_e8 <= 0:
        raise ValueError("redemption amount too small at current price")

    post_coll_a = coll_a - gross_collateral_e8
    post_coll_b = coll_b - gross_collateral_e8
    post_debt_a = debt_a - amount
    post_debt_b = debt_b - amount

    candidate_a_ok = bool(
        amount <= debt_a
        and gross_collateral_e8 <= coll_a
        and _debt_floor_ok(debt_e8=post_debt_a, min_debt_open_e8=min_debt)
        and _mcr_ok(
            collateral_e8=post_coll_a,
            debt_e8=post_debt_a,
            price_e8=price,
            mcr_bps=mcr,
        )
    )
    candidate_b_ok = bool(
        amount <= debt_b
        and gross_collateral_e8 <= coll_b
        and _debt_floor_ok(debt_e8=post_debt_b, min_debt_open_e8=min_debt)
        and _mcr_ok(
            collateral_e8=post_coll_b,
            debt_e8=post_debt_b,
            price_e8=price,
            mcr_bps=mcr,
        )
    )
    headroom_a = _mcr_headroom_num(collateral_e8=coll_a, debt_e8=debt_a, price_e8=price, mcr_bps=mcr)
    headroom_b = _mcr_headroom_num(collateral_e8=coll_b, debt_e8=debt_b, price_e8=price, mcr_bps=mcr)

    selected_vault: Optional[VaultId]
    selected_post_collateral_e8: Optional[int]
    selected_post_debt_e8: Optional[int]
    if candidate_a_ok and candidate_b_ok:
        if headroom_a <= headroom_b:
            selected_vault = "a"
            selected_post_collateral_e8 = post_coll_a
            selected_post_debt_e8 = post_debt_a
        else:
            selected_vault = "b"
            selected_post_collateral_e8 = post_coll_b
            selected_post_debt_e8 = post_debt_b
    elif candidate_a_ok:
        selected_vault = "a"
        selected_post_collateral_e8 = post_coll_a
        selected_post_debt_e8 = post_debt_a
    elif candidate_b_ok:
        selected_vault = "b"
        selected_post_collateral_e8 = post_coll_b
        selected_post_debt_e8 = post_debt_b
    else:
        selected_vault = None
        selected_post_collateral_e8 = None
        selected_post_debt_e8 = None

    return ZUSDMultiRedeemSelectorOutcome(
        amount_e8=amount,
        price_e8=price,
        gross_collateral_e8=gross_collateral_e8,
        candidate_a_ok=candidate_a_ok,
        candidate_b_ok=candidate_b_ok,
        headroom_a_before_e8=headroom_a,
        headroom_b_before_e8=headroom_b,
        selected_vault=selected_vault,
        selected_post_collateral_e8=selected_post_collateral_e8,
        selected_post_debt_e8=selected_post_debt_e8,
    )
