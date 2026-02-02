"""
Perpetuals execution adapter for Tau Net-style transactions.

This module applies operation group "5" (perps) to `DexState` in a deterministic,
fail-closed way. It is intentionally conservative:
- user actions require tx_sender_pubkey == account_pubkey
- operator actions require an explicit operator pubkey configured
- unknown fields/actions are rejected

Perp risk logic is delegated to the ESSO kernel wrapper in `src/core/perp_epoch.py`.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Any, Dict, List, Mapping, Optional

from ..core.dex import DexState
from ..core.perp_epoch import (
    PerpStepResult,
    perp_epoch_isolated_default_apply,
    perp_epoch_isolated_default_fee_pool_max_quote,
    perp_epoch_isolated_default_initial_state,
)
from ..core.perps import (
    PERP_ACCOUNT_KEYS,
    PERP_GLOBAL_KEYS,
    PERPS_STATE_VERSION,
    PerpAccountState,
    PerpMarketState,
    PerpsState,
)
from ..state.balances import BalanceTable
from ..state.canonical import bounded_json_utf8_size


PERP_OP_MODULE = "TauPerp"
PERP_OP_VERSION = "0.1"


@dataclass(frozen=True)
class PerpEngineConfig:
    operator_pubkey: Optional[str] = None
    max_ops: int = 256
    max_op_bytes: int = 64_000
    max_total_ops_bytes: int = 512_000


@dataclass(frozen=True)
class PerpOp:
    market_id: str
    action: str
    data: Dict[str, Any]


@dataclass(frozen=True)
class PerpTxResult:
    ok: bool
    state: Optional[DexState] = None
    effects: Optional[List[Dict[str, Any]]] = None
    error: Optional[str] = None


def _require_str(value: Any, *, name: str, non_empty: bool = True, max_len: int = 4096) -> str:
    if not isinstance(value, str):
        raise ValueError(f"{name} must be a string")
    if non_empty and not value:
        raise ValueError(f"{name} must be non-empty")
    if max_len > 0 and len(value) > max_len:
        raise ValueError(f"{name} too large")
    return value


def _require_int(value: Any, *, name: str, non_negative: bool = False) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValueError(f"{name} must be an int")
    if non_negative and value < 0:
        raise ValueError(f"{name} must be non-negative")
    return int(value)


def _copy_balance_table(balances: BalanceTable) -> BalanceTable:
    copied = BalanceTable()
    for (pubkey, asset), amount in balances.get_all_balances().items():
        copied.set(pubkey, asset, int(amount))
    return copied


def parse_perp_ops(
    operations: Mapping[str, Any],
    *,
    max_ops: int = 256,
    max_op_bytes: int = 64_000,
    max_total_ops_bytes: int = 512_000,
) -> List[PerpOp]:
    if not isinstance(operations, Mapping):
        raise ValueError(f"operations must be an object, got {type(operations)}")

    raw = operations.get("5")
    if raw is None:
        return []
    if not isinstance(raw, list):
        raise ValueError("operations['5'] must be a list")
    if len(raw) > max_ops:
        raise ValueError(f"too many perps ops: {len(raw)} > {max_ops}")

    total_bytes = 0
    out: List[PerpOp] = []
    for i, entry in enumerate(raw):
        if not isinstance(entry, Mapping):
            raise ValueError(f"perps op {i} must be an object")
        op_obj = dict(entry)
        try:
            op_bytes = bounded_json_utf8_size(op_obj, max_bytes=max_op_bytes)
        except ValueError:
            raise ValueError(f"perps op {i} too large") from None
        except Exception as exc:
            raise ValueError(f"invalid perps op {i}: {exc}") from exc
        total_bytes += op_bytes
        if total_bytes > max_total_ops_bytes:
            raise ValueError("perps ops too large (total bytes limit)")

        module = _require_str(op_obj.get("module"), name="perps.module", non_empty=True, max_len=64)
        if module != PERP_OP_MODULE:
            raise ValueError(f"invalid perps module: {module}")
        version = _require_str(op_obj.get("version"), name="perps.version", non_empty=True, max_len=64)
        if version != PERP_OP_VERSION:
            raise ValueError(f"invalid perps version: {version}")

        market_id = _require_str(op_obj.get("market_id"), name="perps.market_id", non_empty=True, max_len=256)
        action = _require_str(op_obj.get("action"), name="perps.action", non_empty=True, max_len=64)

        out.append(PerpOp(market_id=market_id, action=action, data=op_obj))
    return out


def _kernel_initial_global_state() -> Dict[str, Any]:
    st = perp_epoch_isolated_default_initial_state()
    return {k: st[k] for k in sorted(PERP_GLOBAL_KEYS)}


def _kernel_initial_account_state() -> PerpAccountState:
    st = perp_epoch_isolated_default_initial_state()
    return PerpAccountState(
        position_base=int(st.get("position_base", 0)),
        entry_price_e8=int(st.get("entry_price_e8", 0)),
        collateral_quote=int(st.get("collateral_quote", 0)),
    )


def _split_kernel_state(state: Mapping[str, Any]) -> tuple[Dict[str, Any], PerpAccountState]:
    global_state = {k: state[k] for k in sorted(PERP_GLOBAL_KEYS)}
    acct = PerpAccountState(
        position_base=int(state.get("position_base", 0)),
        entry_price_e8=int(state.get("entry_price_e8", 0)),
        collateral_quote=int(state.get("collateral_quote", 0)),
    )
    return global_state, acct


def _require_operator(config: PerpEngineConfig, *, tx_sender_pubkey: str) -> Optional[str]:
    operator = (config.operator_pubkey or "").strip()
    if not operator:
        return "operator disabled (set TAU_DEX_OPERATOR_PUBKEY)"
    if tx_sender_pubkey != operator:
        return "operator only"
    return None


def apply_perp_ops(
    *,
    config: PerpEngineConfig,
    state: DexState,
    operations: Mapping[str, Any],
    tx_sender_pubkey: str,
) -> PerpTxResult:
    try:
        ops = parse_perp_ops(
            operations,
            max_ops=config.max_ops,
            max_op_bytes=config.max_op_bytes,
            max_total_ops_bytes=config.max_total_ops_bytes,
        )
    except Exception as exc:
        return PerpTxResult(ok=False, error=str(exc))

    if not ops:
        return PerpTxResult(ok=True, state=state, effects=[])

    # Work on copies; only commit to `DexState` if everything succeeds.
    balances = _copy_balance_table(state.balances)

    perps = state.perps
    if perps is None:
        perps = PerpsState(version=PERPS_STATE_VERSION, markets={})

    markets = dict(perps.markets)
    effects: List[Dict[str, Any]] = []

    for i, op in enumerate(ops):
        action = op.action
        market_id = op.market_id
        data = op.data

        if action == "init_market":
            err = _require_operator(config, tx_sender_pubkey=tx_sender_pubkey)
            if err is not None:
                return PerpTxResult(ok=False, error=err)
            if market_id in markets:
                return PerpTxResult(ok=False, error="market already exists")

            quote_asset = _require_str(data.get("quote_asset"), name="quote_asset", non_empty=True, max_len=256)
            allowed = {"module", "version", "market_id", "action", "quote_asset"}
            extra = set(data.keys()) - allowed
            if extra:
                return PerpTxResult(ok=False, error="init_market has unknown fields")

            markets[market_id] = PerpMarketState(
                quote_asset=quote_asset,
                global_state=_kernel_initial_global_state(),
                accounts={},
            )
            effects.append({"i": i, "market_id": market_id, "action": action})
            continue

        market = markets.get(market_id)
        if market is None:
            return PerpTxResult(ok=False, error="unknown market_id")

        if action in ("advance_epoch", "publish_clearing_price", "settle_epoch", "clear_breaker"):
            err = _require_operator(config, tx_sender_pubkey=tx_sender_pubkey)
            if err is not None:
                return PerpTxResult(ok=False, error=err)

        if action == "advance_epoch":
            allowed = {"module", "version", "market_id", "action", "delta"}
            if set(data.keys()) - allowed:
                return PerpTxResult(ok=False, error="advance_epoch has unknown fields")
            if int(market.global_state.get("oracle_last_update_epoch", 0)) != int(market.global_state.get("now_epoch", 0)):
                return PerpTxResult(ok=False, error="cannot advance epoch before settling current epoch")
            delta = _require_int(data.get("delta"), name="delta", non_negative=True)

            dummy = _kernel_initial_account_state()
            res = perp_epoch_isolated_default_apply(
                state=market.kernel_state_for_account(dummy),
                action="advance_epoch",
                params={"delta": delta},
            )
            if not res.ok or res.state is None:
                return PerpTxResult(ok=False, error=res.error or "advance_epoch rejected")
            new_global, new_dummy = _split_kernel_state(res.state)
            if new_dummy != dummy:
                return PerpTxResult(ok=False, error="internal error: global op mutated account state")
            markets[market_id] = PerpMarketState(
                quote_asset=market.quote_asset,
                global_state=new_global,
                accounts=dict(market.accounts),
            )
            effects.append({"i": i, "market_id": market_id, "action": action, "effects": dict(res.effects or {})})
            continue

        if action == "publish_clearing_price":
            allowed = {"module", "version", "market_id", "action", "price_e8"}
            if set(data.keys()) - allowed:
                return PerpTxResult(ok=False, error="publish_clearing_price has unknown fields")
            price_e8 = _require_int(data.get("price_e8"), name="price_e8", non_negative=True)

            dummy = _kernel_initial_account_state()
            res = perp_epoch_isolated_default_apply(
                state=market.kernel_state_for_account(dummy),
                action="publish_clearing_price",
                params={"price_e8": price_e8},
            )
            if not res.ok or res.state is None:
                return PerpTxResult(ok=False, error=res.error or "publish_clearing_price rejected")
            new_global, new_dummy = _split_kernel_state(res.state)
            if new_dummy != dummy:
                return PerpTxResult(ok=False, error="internal error: global op mutated account state")
            markets[market_id] = PerpMarketState(
                quote_asset=market.quote_asset,
                global_state=new_global,
                accounts=dict(market.accounts),
            )
            effects.append({"i": i, "market_id": market_id, "action": action, "effects": dict(res.effects or {})})
            continue

        if action == "settle_epoch":
            allowed = {"module", "version", "market_id", "action"}
            if set(data.keys()) - allowed:
                return PerpTxResult(ok=False, error="settle_epoch has unknown fields")

            pre_market = market
            pre_fee_pool = int(pre_market.global_state.get("fee_pool_quote", 0))

            # Phase 1: compute the post-epoch *global* update that must be identical across all accounts
            # (oracle/index, breaker flags, clearing-price bookkeeping). This is computed against a dummy
            # account so it cannot depend on account-specific liquidation events.
            dummy = _kernel_initial_account_state()
            res0 = perp_epoch_isolated_default_apply(
                state=pre_market.kernel_state_for_account(dummy),
                action="settle_epoch",
                params={},
            )
            if not res0.ok or res0.state is None:
                return PerpTxResult(ok=False, error=res0.error or "settle_epoch rejected")
            base_global, new_dummy = _split_kernel_state(res0.state)
            if new_dummy != dummy:
                return PerpTxResult(ok=False, error="internal error: settle_epoch mutated dummy account state")

            # Phase 2: settle each account against the *same* pre-global state, but accumulate the
            # liquidation penalty deltas into the global fee pool deterministically (sorted account keys).
            expected_global_no_pool = dict(base_global)
            expected_global_no_pool["fee_pool_quote"] = pre_fee_pool

            total_fee_pool_delta = 0
            new_accounts: Dict[str, PerpAccountState] = {}
            for pk in sorted(pre_market.accounts.keys()):
                acct = pre_market.accounts[pk]
                res = perp_epoch_isolated_default_apply(
                    state=pre_market.kernel_state_for_account(acct),
                    action="settle_epoch",
                    params={},
                )
                if not res.ok or res.state is None:
                    return PerpTxResult(
                        ok=False,
                        error=f"settle_epoch rejected for account {pk}: {res.error or ''}".strip(),
                    )
                post_global, post_acct = _split_kernel_state(res.state)

                # All global fields except fee_pool_quote must match the dummy-derived post-global.
                post_global_no_pool = dict(post_global)
                post_global_no_pool["fee_pool_quote"] = pre_fee_pool
                if post_global_no_pool != expected_global_no_pool:
                    return PerpTxResult(ok=False, error="internal error: global settle depended on account state")

                post_fee_pool = int(post_global.get("fee_pool_quote", 0))
                delta = post_fee_pool - pre_fee_pool
                if delta < 0:
                    return PerpTxResult(ok=False, error="internal error: fee pool decreased during settle_epoch")
                total_fee_pool_delta += delta
                new_accounts[str(pk)] = post_acct

            # Fail-closed on fee-pool overflow beyond the kernel's finite-domain bound.
            next_fee_pool = pre_fee_pool + total_fee_pool_delta
            if next_fee_pool > perp_epoch_isolated_default_fee_pool_max_quote():
                return PerpTxResult(ok=False, error="fee pool overflow (post-settle)")

            expected_global_no_pool["fee_pool_quote"] = int(next_fee_pool)
            markets[market_id] = PerpMarketState(
                quote_asset=market.quote_asset,
                global_state=expected_global_no_pool,
                accounts=new_accounts,
            )
            effects.append(
                {
                    "i": i,
                    "market_id": market_id,
                    "action": action,
                    "fee_pool_delta": int(total_fee_pool_delta),
                    "effects": dict(res0.effects or {}),
                }
            )
            continue

        if action == "clear_breaker":
            allowed = {"module", "version", "market_id", "action"}
            if set(data.keys()) - allowed:
                return PerpTxResult(ok=False, error="clear_breaker has unknown fields")
            if any(int(acct.position_base) != 0 for acct in market.accounts.values()):
                return PerpTxResult(ok=False, error="cannot clear breaker while positions are open")

            dummy = _kernel_initial_account_state()
            res = perp_epoch_isolated_default_apply(
                state=market.kernel_state_for_account(dummy),
                action="clear_breaker",
                params={"auth_ok": True},
            )
            if not res.ok or res.state is None:
                return PerpTxResult(ok=False, error=res.error or "clear_breaker rejected")
            new_global, new_dummy = _split_kernel_state(res.state)
            if new_dummy != dummy:
                return PerpTxResult(ok=False, error="internal error: clear_breaker mutated dummy account state")

            markets[market_id] = PerpMarketState(
                quote_asset=market.quote_asset,
                global_state=new_global,
                accounts=dict(market.accounts),
            )
            effects.append({"i": i, "market_id": market_id, "action": action, "effects": dict(res.effects or {})})
            continue

        if action in ("deposit_collateral", "withdraw_collateral", "set_position"):
            allowed_common = {"module", "version", "market_id", "action", "account_pubkey"}
            if action in ("deposit_collateral", "withdraw_collateral"):
                allowed = allowed_common | {"amount"}
            else:
                allowed = allowed_common | {"new_position_base"}
            if set(data.keys()) - allowed:
                return PerpTxResult(ok=False, error=f"{action} has unknown fields")

            account_pubkey = _require_str(data.get("account_pubkey"), name="account_pubkey", non_empty=True, max_len=512)
            if account_pubkey != tx_sender_pubkey:
                return PerpTxResult(ok=False, error="account_pubkey must match tx sender")

            accounts = dict(market.accounts)
            acct = accounts.get(account_pubkey) or _kernel_initial_account_state()

            if action == "deposit_collateral":
                amount = _require_int(data.get("amount"), name="amount", non_negative=True)
                if balances.get(account_pubkey, market.quote_asset) < amount:
                    return PerpTxResult(ok=False, error="insufficient balance for deposit")

                res = perp_epoch_isolated_default_apply(
                    state=market.kernel_state_for_account(acct),
                    action="deposit_collateral",
                    params={"amount": amount, "auth_ok": True},
                )
                if not res.ok or res.state is None:
                    return PerpTxResult(ok=False, error=res.error or "deposit_collateral rejected")
                post_global, post_acct = _split_kernel_state(res.state)
                if post_global != market.global_state:
                    return PerpTxResult(ok=False, error="internal error: deposit mutated global state")
                balances.subtract(account_pubkey, market.quote_asset, amount)
                accounts[account_pubkey] = post_acct
                markets[market_id] = PerpMarketState(
                    quote_asset=market.quote_asset,
                    global_state=dict(market.global_state),
                    accounts=accounts,
                )
                effects.append(
                    {
                        "i": i,
                        "market_id": market_id,
                        "action": action,
                        "account_pubkey": account_pubkey,
                        "effects": dict(res.effects or {}),
                    }
                )
                continue

            if action == "withdraw_collateral":
                amount = _require_int(data.get("amount"), name="amount", non_negative=True)
                res = perp_epoch_isolated_default_apply(
                    state=market.kernel_state_for_account(acct),
                    action="withdraw_collateral",
                    params={"amount": amount, "auth_ok": True},
                )
                if not res.ok or res.state is None:
                    return PerpTxResult(ok=False, error=res.error or "withdraw_collateral rejected")
                post_global, post_acct = _split_kernel_state(res.state)
                if post_global != market.global_state:
                    return PerpTxResult(ok=False, error="internal error: withdraw mutated global state")
                balances.add(account_pubkey, market.quote_asset, amount)
                accounts[account_pubkey] = post_acct
                markets[market_id] = PerpMarketState(
                    quote_asset=market.quote_asset,
                    global_state=dict(market.global_state),
                    accounts=accounts,
                )
                effects.append(
                    {
                        "i": i,
                        "market_id": market_id,
                        "action": action,
                        "account_pubkey": account_pubkey,
                        "effects": dict(res.effects or {}),
                    }
                )
                continue

            if action == "set_position":
                new_pos = _require_int(data.get("new_position_base"), name="new_position_base", non_negative=False)
                res = perp_epoch_isolated_default_apply(
                    state=market.kernel_state_for_account(acct),
                    action="set_position",
                    params={"new_position_base": new_pos, "auth_ok": True},
                )
                if not res.ok or res.state is None:
                    return PerpTxResult(ok=False, error=res.error or "set_position rejected")
                post_global, post_acct = _split_kernel_state(res.state)
                if post_global != market.global_state:
                    return PerpTxResult(ok=False, error="internal error: set_position mutated global state")
                accounts[account_pubkey] = post_acct
                markets[market_id] = PerpMarketState(
                    quote_asset=market.quote_asset,
                    global_state=dict(market.global_state),
                    accounts=accounts,
                )
                effects.append(
                    {
                        "i": i,
                        "market_id": market_id,
                        "action": action,
                        "account_pubkey": account_pubkey,
                        "effects": dict(res.effects or {}),
                    }
                )
                continue

        return PerpTxResult(ok=False, error=f"unknown perps action: {action}")

    next_perps = PerpsState(version=perps.version, markets=markets) if markets else None
    next_state = replace(state, balances=balances, perps=next_perps)
    return PerpTxResult(ok=True, state=next_state, effects=effects)
