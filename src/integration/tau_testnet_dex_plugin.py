"""
Tau Testnet Alpha app-bridge plugin for the TauSwap DEX (this repo).

This module implements the generic `external/tau-testnet/app_bridge.py` plugin API:
  apply_app_tx(...)

It applies DEX operations from a Tau transaction's `operations` dict:
  - "2": intents (list)
  - "3": settlement (object) [optional if allow_missing_settlement]
  - "4": faucet (object) [optional, test-only; requires TAU_DEX_FAUCET=1]
  - "5": perps (list) [optional; isolated markets require an operator key for admin actions]
"""

from __future__ import annotations

import json
import os
import hashlib
from dataclasses import replace
from typing import Any, Dict, Optional, Tuple

from ..core.dex import DexState
from ..state.balances import BalanceTable, NATIVE_ASSET
from ..state.lp import LPTable
from .dex_engine import DexEngineConfig, apply_ops
from .dex_snapshot import snapshot_from_state, state_from_snapshot
from .perp_engine import PerpEngineConfig, apply_perp_ops


def _bool_env(name: str, *, default: bool) -> bool:
    raw = os.environ.get(name)
    if raw is None:
        return bool(default)
    v = raw.strip().lower()
    if v in {"1", "true", "yes", "on"}:
        return True
    if v in {"0", "false", "no", "off"}:
        return False
    return bool(default)


def _copy_balance_table(balances: BalanceTable) -> BalanceTable:
    copied = BalanceTable()
    for (pubkey, asset), amount in balances.get_all_balances().items():
        copied.set(pubkey, asset, int(amount))
    return copied


def _load_state(app_state_json: str) -> DexState:
    raw = (app_state_json or "").strip()
    if not raw:
        return DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    try:
        obj = json.loads(raw)
    except Exception as exc:
        raise ValueError(f"invalid app_state_json: {exc}") from exc
    try:
        return state_from_snapshot(obj)
    except Exception as exc:
        raise ValueError(f"invalid app_state snapshot: {exc}") from exc


def _parse_faucet_mint_entry(entry: Any, *, index: int) -> Tuple[Optional[Tuple[str, str, int]], Optional[str]]:
    pk: Any
    asset: Any
    amount: Any

    if isinstance(entry, (list, tuple)):
        if len(entry) != 3:
            return None, f"faucet.mint[{index}] must have length 3"
        pk, asset, amount = entry
    elif isinstance(entry, dict):
        pk = entry.get("pubkey")
        asset = entry.get("asset")
        amount = entry.get("amount")
    else:
        return None, f"faucet.mint[{index}] must be a list or object"

    if not isinstance(pk, str) or not pk or len(pk) > 512:
        return None, f"faucet.mint[{index}] invalid pubkey"
    if not isinstance(asset, str) or not asset or len(asset) > 256:
        return None, f"faucet.mint[{index}] invalid asset"
    if asset == NATIVE_ASSET:
        return None, "faucet cannot mint native asset"
    if not isinstance(amount, int) or isinstance(amount, bool) or amount <= 0:
        return None, f"faucet.mint[{index}] amount must be a positive int"

    return (pk, asset, int(amount)), None


def _sync_native_balances(state: DexState, *, chain_balances: Dict[str, int]) -> DexState:
    balances_copy = _copy_balance_table(state.balances)

    # Drop any existing native entries from stored snapshot.
    for (pk, asset), _amount in list(balances_copy.get_all_balances().items()):
        if asset == NATIVE_ASSET:
            balances_copy.set(pk, asset, 0)

    for pk, amount in chain_balances.items():
        try:
            amt_i = int(amount)
        except Exception:
            continue
        if amt_i <= 0:
            continue
        balances_copy.set(str(pk), NATIVE_ASSET, amt_i)

    return DexState(
        balances=balances_copy,
        pools=state.pools,
        lp_balances=state.lp_balances,
        nonces=state.nonces,
        vault=state.vault,
        oracle=state.oracle,
        fee_accumulator=state.fee_accumulator,
        perps=state.perps,
    )


def _apply_faucet(
    state: DexState,
    faucet_op: Any,
    *,
    allow: bool,
) -> Tuple[bool, DexState, Optional[str]]:
    if faucet_op is None:
        return True, state, None
    if not allow:
        return False, state, "faucet disabled (set TAU_DEX_FAUCET=1)"
    if not isinstance(faucet_op, dict):
        return False, state, "faucet op must be an object"
    mint = faucet_op.get("mint")
    if not isinstance(mint, list):
        return False, state, "faucet.mint must be a list"

    balances_copy = _copy_balance_table(state.balances)
    for i, entry in enumerate(mint):
        parsed, err = _parse_faucet_mint_entry(entry, index=i)
        if err is not None:
            return False, state, err
        assert parsed is not None  # internal: err would be set
        pk, asset, amount = parsed

        current = balances_copy.get(pk, asset)
        balances_copy.set(pk, asset, int(current) + int(amount))

    next_state = replace(state, balances=balances_copy)
    return True, next_state, None


def _balances_patch_for_native(*, before: Dict[str, int], after_state: DexState) -> Dict[str, int]:
    out: Dict[str, int] = {}
    keys = set(before.keys())
    # Include any addresses that appear in the DEX snapshot (native).
    for (pk, asset), _amount in after_state.balances.get_all_balances().items():
        if asset == NATIVE_ASSET:
            keys.add(pk)

    for pk in keys:
        old = int(before.get(pk, 0))
        new = int(after_state.balances.get(pk, NATIVE_ASSET))
        if new != old:
            out[pk] = new
    return out


def apply_app_tx(
    *,
    app_state_json: str,
    chain_balances: Dict[str, int],
    operations: Dict[str, object],
    tx_sender_pubkey: str,
    block_timestamp: int,
) -> Tuple[bool, str, str, Optional[Dict[str, int]], Optional[str]]:
    allow_faucet = _bool_env("TAU_DEX_FAUCET", default=False)
    allow_missing_settlement = _bool_env("TAU_DEX_ALLOW_MISSING_SETTLEMENT", default=True)
    require_intent_sigs = _bool_env("TAU_DEX_REQUIRE_INTENT_SIGS", default=True)
    chain_id = os.environ.get("TAU_DEX_CHAIN_ID", "").strip() or os.environ.get("TAU_NETWORK_ID", "").strip() or "tau-local"

    try:
        state = _load_state(app_state_json)
    except Exception as exc:
        return False, app_state_json, "", None, str(exc)
    state = _sync_native_balances(state, chain_balances=chain_balances)

    faucet_op = operations.get("4")
    ok, state, err = _apply_faucet(state, faucet_op, allow=allow_faucet)
    if not ok:
        return False, app_state_json, "", None, err

    dex_ops: Dict[str, Any] = {}
    if "2" in operations:
        dex_ops["2"] = operations.get("2")
    if "3" in operations:
        dex_ops["3"] = operations.get("3")

    perp_ops: Dict[str, Any] = {}
    if "5" in operations:
        perp_ops["5"] = operations.get("5")

    # Sync-only call: no ops, but we still update the snapshot/hash so native balances stay consistent.
    if not dex_ops and not perp_ops:
        snap = snapshot_from_state(state)
        canonical = snap.canonical_bytes()
        return True, canonical.decode("utf-8"), hashlib.sha256(canonical).hexdigest(), None, None

    next_state = state
    if dex_ops:
        engine_cfg = DexEngineConfig(
            allow_missing_settlement=bool(allow_missing_settlement),
            require_intent_signatures=bool(require_intent_sigs),
            chain_id=chain_id,
        )
        res = apply_ops(
            config=engine_cfg,
            state=next_state,
            operations=dex_ops,
            block_timestamp=int(block_timestamp),
            tx_sender_pubkey=tx_sender_pubkey,
        )
        if not res.ok or res.state is None:
            return False, app_state_json, "", None, res.error or "DEX rejected"
        next_state = res.state

    if perp_ops:
        operator_pubkey = os.environ.get("TAU_DEX_OPERATOR_PUBKEY") or os.environ.get("TAU_DEX_PERP_OPERATOR_PUBKEY")
        oracle_pubkey = os.environ.get("TAU_DEX_PERP_ORACLE_PUBKEY") or os.environ.get("TAU_DEX_ORACLE_PUBKEY")
        allow_isolated = _bool_env("TAU_DEX_ALLOW_ISOLATED_PERPS", default=False)
        perp_cfg = PerpEngineConfig(
            operator_pubkey=(operator_pubkey or "").strip() or None,
            chain_id=chain_id,
            oracle_pubkey=(oracle_pubkey or "").strip() or None,
            allow_isolated_markets=bool(allow_isolated),
        )
        perp_res = apply_perp_ops(
            config=perp_cfg,
            state=next_state,
            operations=perp_ops,
            tx_sender_pubkey=tx_sender_pubkey,
            block_timestamp=int(block_timestamp),
        )
        if not perp_res.ok or perp_res.state is None:
            return False, app_state_json, "", None, perp_res.error or "PERP rejected"
        next_state = perp_res.state

    balances_patch = _balances_patch_for_native(before=chain_balances, after_state=next_state)
    snap = snapshot_from_state(next_state)
    canonical = snap.canonical_bytes()
    return True, canonical.decode("utf-8"), hashlib.sha256(canonical).hexdigest(), balances_patch, None
