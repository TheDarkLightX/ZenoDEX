from __future__ import annotations

from typing import Any


def _parse_settlement_proof_flags_payload(payload: object) -> Any:
    from src.integration.settlement_strong_certificate import (  # pylint: disable=import-outside-toplevel
        SettlementProofFlags,
    )

    if not isinstance(payload, dict):
        raise ValueError("proof_flags must be an object")
    names = (
        "cpmm_ok",
        "balance_ok",
        "token_ok",
        "buyback_floor_ok",
        "buyback_floor_fixedpoint_ok",
        "rebate_ok",
        "lock_weight_ok",
        "proof_ok",
        "binding_ok",
    )
    values: dict[str, int] = {}
    for name in names:
        raw = payload.get(name)
        if not isinstance(raw, int) or isinstance(raw, bool) or raw not in (0, 1):
            raise ValueError(f"proof_flags.{name} must be 0 or 1")
        values[name] = int(raw)
    return SettlementProofFlags(**values)


def _parse_price_history_payload(payload: object) -> tuple[int, int, int]:
    if not isinstance(payload, (list, tuple)) or len(payload) != 3:
        raise ValueError("price_history must be a 3-item array: [price_pp, price_prev, price_curr]")
    values: list[int] = []
    for idx, raw in enumerate(payload):
        if not isinstance(raw, int) or isinstance(raw, bool) or raw < 0:
            raise ValueError(f"price_history[{idx}] must be a non-negative int")
        values.append(int(raw))
    return (values[0], values[1], values[2])


def _parse_settlement_feature_extension_inputs_payload(payload: object) -> Any:
    from src.integration.settlement_feature_extension_packet import (  # pylint: disable=import-outside-toplevel
        SettlementFeatureExtensionInputs,
    )

    if not isinstance(payload, dict):
        raise ValueError("feature_extension_inputs must be an object")
    return SettlementFeatureExtensionInputs.from_dict(payload)


def _parse_balance_table_payload(payload: object) -> Any:
    from src.state import BalanceTable  # pylint: disable=import-outside-toplevel

    if not isinstance(payload, list):
        raise ValueError("balances must be a list")
    balances = BalanceTable()
    seen: set[tuple[str, str]] = set()
    for entry in payload:
        if not isinstance(entry, dict):
            raise ValueError("balances entries must be objects")
        pubkey = str(entry.get("pubkey", "")).strip()
        asset = str(entry.get("asset", "")).strip()
        amount = entry.get("amount")
        if not pubkey:
            raise ValueError("balance pubkey must be a non-empty string")
        if not asset:
            raise ValueError("balance asset must be a non-empty string")
        if not isinstance(amount, int) or isinstance(amount, bool) or amount < 0:
            raise ValueError("balance amount must be a non-negative int")
        key = (pubkey, asset)
        if key in seen:
            raise ValueError("duplicate balance entry")
        seen.add(key)
        balances.set(pubkey, asset, int(amount))
    return balances


def _parse_lp_balances_payload(payload: object) -> Any:
    from src.state import LPTable  # pylint: disable=import-outside-toplevel

    if payload is None:
        return LPTable()
    if not isinstance(payload, list):
        raise ValueError("lp_balances must be a list")
    lp_balances = LPTable()
    seen: set[tuple[str, str]] = set()
    for entry in payload:
        if not isinstance(entry, dict):
            raise ValueError("lp_balances entries must be objects")
        pubkey = str(entry.get("pubkey", "")).strip()
        pool_id = str(entry.get("pool_id", "")).strip()
        amount = entry.get("amount")
        if not pubkey:
            raise ValueError("lp balance pubkey must be a non-empty string")
        if not pool_id:
            raise ValueError("lp balance pool_id must be a non-empty string")
        if not isinstance(amount, int) or isinstance(amount, bool) or amount < 0:
            raise ValueError("lp balance amount must be a non-negative int")
        key = (pubkey, pool_id)
        if key in seen:
            raise ValueError("duplicate lp balance entry")
        seen.add(key)
        lp_balances.set(pubkey, pool_id, int(amount))
    return lp_balances


def _parse_lp_unit_values_payload(payload: object) -> dict[str, int] | None:
    if payload is None:
        return None
    if not isinstance(payload, dict) or not payload:
        raise ValueError("bad_lp_unit_values")
    lp_unit_values: dict[str, int] = {}
    for raw_pool_id, raw_unit_value in payload.items():
        pool_id = str(raw_pool_id).strip()
        if not pool_id:
            raise ValueError("lp_unit_values keys must be non-empty strings")
        if not isinstance(raw_unit_value, int) or isinstance(raw_unit_value, bool) or raw_unit_value < 0:
            raise ValueError(f"lp unit value must be a non-negative int for {pool_id}")
        lp_unit_values[pool_id] = int(raw_unit_value)
    return lp_unit_values
