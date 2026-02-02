"""
Perpetuals execution adapter for Tau Net-style transactions.

This module applies operation group "5" (perps) to `DexState` in a deterministic,
fail-closed way. It is intentionally conservative:
- user actions require tx_sender_pubkey == account_pubkey
- operator actions require an explicit operator pubkey configured
- unknown fields/actions are rejected

Two perps operation versions are supported:
- v0.1: isolated-margin per-account execution (default posture).
- v1.0 (and legacy v0.2): a minimal 2-party clearinghouse posture with enforced net-zero exposure.
  - Markets are namespaced with a `perp:ch2p:` prefix to avoid mixing semantics.
  - Position updates are operator-authorized and must be set as a matched pair.
  - Settlement uses a deterministic dust allocator to preserve net-zero PnL under integer division.

Per-account risk checks (guards/limits) reuse the epoch-perp risk kernel wrapper in
`src/core/perp_epoch.py` (native Python implementation by default). The optional
kernel-spec verification/codegen toolchain is used for evidence and parity testing,
not required at runtime.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Any, Dict, List, Mapping, Optional

from ..core.dex import DexState
from ..core.perp_epoch import (
    perp_epoch_isolated_default_apply,
    perp_epoch_isolated_default_fee_pool_max_quote,
    perp_epoch_isolated_default_initial_state,
)
from ..core.perp_rounding import largest_remainder_adjust_net_zero
from ..core.perp_v2.math import (
    MAX_COLLATERAL,
    PRICE_SCALE,
    is_liquidatable,
    liq_penalty_capped,
)
from ..core.perps import (
    PERP_GLOBAL_KEYS,
    PERPS_STATE_VERSION,
    PerpAccountState,
    PerpMarketState,
    PerpsState,
)
from ..state.balances import BalanceTable
from ..state.canonical import bounded_json_utf8_size


PERP_OP_MODULE = "TauPerp"
PERP_OP_VERSION_V0_1 = "0.1"
# Clearinghouse (2-party) posture versions:
# - 0.2: initial rollout (kept for compatibility)
# - 1.0: "production" tag for the same semantics
PERP_OP_VERSION_CH2P_V0_2 = "0.2"
PERP_OP_VERSION_CH2P_V1_0 = "1.0"

# v0.2 markets are explicitly namespaced to avoid mixing semantics without a snapshot schema change.
# This is a fail-closed API convention, not a security boundary.
PERP_CH2P_MARKET_PREFIX = "perp:ch2p:"


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
    version: str
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
        if version not in (PERP_OP_VERSION_V0_1, PERP_OP_VERSION_CH2P_V0_2, PERP_OP_VERSION_CH2P_V1_0):
            raise ValueError(f"invalid perps version: {version}")

        market_id = _require_str(op_obj.get("market_id"), name="perps.market_id", non_empty=True, max_len=256)
        is_ch2p = version in (PERP_OP_VERSION_CH2P_V0_2, PERP_OP_VERSION_CH2P_V1_0)
        if is_ch2p and not market_id.startswith(PERP_CH2P_MARKET_PREFIX):
            raise ValueError(f"clearinghouse markets must start with {PERP_CH2P_MARKET_PREFIX!r}")
        if not is_ch2p and market_id.startswith(PERP_CH2P_MARKET_PREFIX):
            raise ValueError(f"v0.1 markets cannot start with {PERP_CH2P_MARKET_PREFIX!r}")

        action = _require_str(op_obj.get("action"), name="perps.action", non_empty=True, max_len=64)

        out.append(PerpOp(market_id=market_id, action=action, version=version, data=op_obj))
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
        funding_paid_cumulative=int(st.get("funding_paid_cumulative", 0)),
        funding_last_applied_epoch=int(st.get("funding_last_applied_epoch", 0)),
        liquidated_this_step=bool(st.get("liquidated_this_step", False)),
    )


def _split_kernel_state(state: Mapping[str, Any]) -> tuple[Dict[str, Any], PerpAccountState]:
    global_state = {k: state[k] for k in sorted(PERP_GLOBAL_KEYS)}
    acct = PerpAccountState(
        position_base=int(state.get("position_base", 0)),
        entry_price_e8=int(state.get("entry_price_e8", 0)),
        collateral_quote=int(state.get("collateral_quote", 0)),
        funding_paid_cumulative=int(state.get("funding_paid_cumulative", 0)),
        funding_last_applied_epoch=int(state.get("funding_last_applied_epoch", 0)),
        liquidated_this_step=bool(state.get("liquidated_this_step", False)),
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
        version = op.version
        data = op.data

        if action == "init_market":
            if version != PERP_OP_VERSION_V0_1:
                return PerpTxResult(ok=False, error="init_market requires perps.version=0.1")
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

        if action == "init_market_2p":
            if version not in (PERP_OP_VERSION_CH2P_V0_2, PERP_OP_VERSION_CH2P_V1_0):
                return PerpTxResult(ok=False, error="init_market_2p requires perps.version=0.2 or 1.0")
            err = _require_operator(config, tx_sender_pubkey=tx_sender_pubkey)
            if err is not None:
                return PerpTxResult(ok=False, error=err)
            if market_id in markets:
                return PerpTxResult(ok=False, error="market already exists")

            quote_asset = _require_str(data.get("quote_asset"), name="quote_asset", non_empty=True, max_len=256)
            account_a_pubkey = _require_str(
                data.get("account_a_pubkey"), name="account_a_pubkey", non_empty=True, max_len=512
            )
            account_b_pubkey = _require_str(
                data.get("account_b_pubkey"), name="account_b_pubkey", non_empty=True, max_len=512
            )
            if account_a_pubkey == account_b_pubkey:
                return PerpTxResult(ok=False, error="accounts must be distinct")

            allowed = {"module", "version", "market_id", "action", "quote_asset", "account_a_pubkey", "account_b_pubkey"}
            extra = set(data.keys()) - allowed
            if extra:
                return PerpTxResult(ok=False, error="init_market_2p has unknown fields")

            accounts: Dict[str, PerpAccountState] = {
                account_a_pubkey: _kernel_initial_account_state(),
                account_b_pubkey: _kernel_initial_account_state(),
            }
            markets[market_id] = PerpMarketState(
                quote_asset=quote_asset,
                global_state=_kernel_initial_global_state(),
                accounts=accounts,
            )
            effects.append(
                {
                    "i": i,
                    "market_id": market_id,
                    "action": action,
                    "account_a_pubkey": account_a_pubkey,
                    "account_b_pubkey": account_b_pubkey,
                }
            )
            continue

        market = markets.get(market_id)
        if market is None:
            return PerpTxResult(ok=False, error="unknown market_id")

        if action in ("advance_epoch", "publish_clearing_price", "settle_epoch", "clear_breaker", "set_position_pair"):
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

            if version in (PERP_OP_VERSION_CH2P_V0_2, PERP_OP_VERSION_CH2P_V1_0):
                if len(market.accounts) != 2:
                    return PerpTxResult(ok=False, error="clearinghouse_2p requires exactly 2 accounts")

                pks = sorted(market.accounts.keys())
                acct0 = market.accounts[pks[0]]
                acct1 = market.accounts[pks[1]]
                pos0 = int(acct0.position_base)
                pos1 = int(acct1.position_base)
                if pos0 + pos1 != 0:
                    return PerpTxResult(ok=False, error="clearinghouse_2p requires net position == 0")

                pre_market = market
                pre_fee_pool = int(pre_market.global_state.get("fee_pool_quote", 0))
                pre_fee_income = int(pre_market.global_state.get("fee_income", 0))
                pre_initial_insurance = int(pre_market.global_state.get("initial_insurance", 0))
                pre_claims_paid = int(pre_market.global_state.get("claims_paid", 0))

                # Phase 1: compute the post-epoch global update (oracle/index/clamp/breaker bookkeeping)
                # against a dummy account so it cannot depend on account-specific liquidation.
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

                pre_index_e8 = int(pre_market.global_state.get("index_price_e8", 0))
                sp = int(base_global.get("index_price_e8", 0))
                delta_e8 = sp - pre_index_e8

                # Phase 2: net-zero settlement across the 2 accounts.
                # We compute xs_i = pos_i * ΔP_e8, then allocate PnL in quote units as:
                # pnl_i := (xs_i div 1e8) with deterministic dust allocation that enforces Σpnl = 0.
                xs = [pos0 * delta_e8, pos1 * delta_e8]
                pnls = largest_remainder_adjust_net_zero(xs=xs, keys=pks, d=PRICE_SCALE)

                coll0_after_pnl = int(acct0.collateral_quote) + pnls[0]
                coll1_after_pnl = int(acct1.collateral_quote) + pnls[1]
                if coll0_after_pnl < 0 or coll1_after_pnl < 0:
                    return PerpTxResult(ok=False, error="collateral negative (post-pnl)")
                if coll0_after_pnl > MAX_COLLATERAL or coll1_after_pnl > MAX_COLLATERAL:
                    return PerpTxResult(ok=False, error="collateral overflow (post-pnl)")

                maint_bps = int(pre_market.global_state.get("maintenance_margin_bps", 0))
                depeg_bps = int(pre_market.global_state.get("depeg_buffer_bps", 0))
                liq_penalty_bps = int(pre_market.global_state.get("liquidation_penalty_bps", 0))
                min_notional_for_bounty = int(pre_market.global_state.get("min_notional_for_bounty", 0))

                liq0 = is_liquidatable(pos0, coll0_after_pnl, sp, maint_bps, depeg_bps)
                liq1 = is_liquidatable(pos1, coll1_after_pnl, sp, maint_bps, depeg_bps)
                any_liq = liq0 or liq1

                total_penalty_delta = 0
                if any_liq:
                    if liq0 and pos0 != 0:
                        penalty0 = liq_penalty_capped(
                            coll0_after_pnl, pos0, sp, liq_penalty_bps, min_notional_for_bounty
                        )
                        coll0_after_pnl -= penalty0
                        total_penalty_delta += int(penalty0)
                    if liq1 and pos1 != 0:
                        penalty1 = liq_penalty_capped(
                            coll1_after_pnl, pos1, sp, liq_penalty_bps, min_notional_for_bounty
                        )
                        coll1_after_pnl -= penalty1
                        total_penalty_delta += int(penalty1)

                # Update global fee/insurance accumulators deterministically.
                max_fee_pool = perp_epoch_isolated_default_fee_pool_max_quote()
                next_fee_pool = pre_fee_pool + total_penalty_delta
                next_fee_income = pre_fee_income + total_penalty_delta
                next_insurance = pre_initial_insurance + next_fee_income - pre_claims_paid
                if next_fee_pool > max_fee_pool or next_fee_income > max_fee_pool or next_insurance > max_fee_pool:
                    return PerpTxResult(ok=False, error="fee/insurance overflow (post-settle)")
                if next_insurance < 0:
                    return PerpTxResult(ok=False, error="insurance negative (post-settle)")

                next_global = dict(base_global)
                next_global["fee_pool_quote"] = int(next_fee_pool)
                next_global["fee_income"] = int(next_fee_income)
                next_global["insurance_balance"] = int(next_insurance)

                # Positions: keep matched pair open when both are maintenance-safe; otherwise close both.
                if any_liq:
                    post_pos0 = 0
                    post_pos1 = 0
                    post_entry0 = 0
                    post_entry1 = 0
                else:
                    post_pos0 = pos0
                    post_pos1 = pos1
                    post_entry0 = 0 if pos0 == 0 else sp
                    post_entry1 = 0 if pos1 == 0 else sp

                new_accounts = dict(pre_market.accounts)
                new_accounts[pks[0]] = replace(
                    acct0,
                    collateral_quote=int(coll0_after_pnl),
                    position_base=int(post_pos0),
                    entry_price_e8=int(post_entry0),
                    liquidated_this_step=bool(any_liq),
                )
                new_accounts[pks[1]] = replace(
                    acct1,
                    collateral_quote=int(coll1_after_pnl),
                    position_base=int(post_pos1),
                    entry_price_e8=int(post_entry1),
                    liquidated_this_step=bool(any_liq),
                )
                markets[market_id] = PerpMarketState(
                    quote_asset=market.quote_asset,
                    global_state=next_global,
                    accounts=new_accounts,
                )
                effects.append(
                    {
                        "i": i,
                        "market_id": market_id,
                        "action": action,
                        "version": version,
                        "pnl_quote": {pks[0]: int(pnls[0]), pks[1]: int(pnls[1])},
                        "fee_pool_delta": int(total_penalty_delta),
                        "liquidated": bool(any_liq),
                        "effects": dict(res0.effects or {}),
                    }
                )
                continue

            pre_market = market
            pre_fee_pool = int(pre_market.global_state.get("fee_pool_quote", 0))
            pre_fee_income = int(pre_market.global_state.get("fee_income", 0))
            pre_initial_insurance = int(pre_market.global_state.get("initial_insurance", 0))
            pre_claims_paid = int(pre_market.global_state.get("claims_paid", 0))
            pre_insurance_balance = int(pre_market.global_state.get("insurance_balance", 0))

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
            # liquidation penalty deltas into the global fee/insurance state deterministically
            # (sorted account keys).
            expected_global_no_accum = dict(base_global)
            expected_global_no_accum["fee_pool_quote"] = pre_fee_pool
            expected_global_no_accum["fee_income"] = pre_fee_income
            expected_global_no_accum["insurance_balance"] = pre_insurance_balance

            total_penalty_delta = 0
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

                # All global fields except fee/insurance accumulators must match the dummy-derived post-global.
                post_global_no_accum = dict(post_global)
                post_global_no_accum["fee_pool_quote"] = pre_fee_pool
                post_global_no_accum["fee_income"] = pre_fee_income
                post_global_no_accum["insurance_balance"] = pre_insurance_balance
                if post_global_no_accum != expected_global_no_accum:
                    return PerpTxResult(ok=False, error="internal error: global settle depended on account state")

                post_fee_pool = int(post_global.get("fee_pool_quote", 0))
                post_fee_income = int(post_global.get("fee_income", 0))
                post_insurance = int(post_global.get("insurance_balance", 0))

                fee_pool_delta = post_fee_pool - pre_fee_pool
                fee_income_delta = post_fee_income - pre_fee_income
                insurance_delta = post_insurance - pre_insurance_balance

                if fee_pool_delta < 0 or fee_income_delta < 0 or insurance_delta < 0:
                    return PerpTxResult(ok=False, error="internal error: fee pool decreased during settle_epoch")
                if fee_pool_delta != fee_income_delta or fee_pool_delta != insurance_delta:
                    return PerpTxResult(ok=False, error="internal error: fee/insurance deltas inconsistent")

                total_penalty_delta += fee_pool_delta
                new_accounts[str(pk)] = post_acct

            # Fail-closed on fee-pool overflow beyond the kernel's finite-domain bound.
            max_fee_pool = perp_epoch_isolated_default_fee_pool_max_quote()
            next_fee_pool = pre_fee_pool + total_penalty_delta
            next_fee_income = pre_fee_income + total_penalty_delta
            next_insurance = pre_initial_insurance + next_fee_income - pre_claims_paid
            if next_fee_pool > max_fee_pool or next_fee_income > max_fee_pool or next_insurance > max_fee_pool:
                return PerpTxResult(ok=False, error="fee/insurance overflow (post-settle)")
            if next_insurance < 0:
                return PerpTxResult(ok=False, error="insurance negative (post-settle)")

            expected_global_no_accum["fee_pool_quote"] = int(next_fee_pool)
            expected_global_no_accum["fee_income"] = int(next_fee_income)
            expected_global_no_accum["insurance_balance"] = int(next_insurance)
            markets[market_id] = PerpMarketState(
                quote_asset=market.quote_asset,
                global_state=expected_global_no_accum,
                accounts=new_accounts,
            )
            effects.append(
                {
                    "i": i,
                    "market_id": market_id,
                    "action": action,
                    "fee_pool_delta": int(total_penalty_delta),
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

        if action in ("deposit_collateral", "withdraw_collateral"):
            allowed_common = {"module", "version", "market_id", "action", "account_pubkey"}
            allowed = allowed_common | {"amount"}
            if set(data.keys()) - allowed:
                return PerpTxResult(ok=False, error=f"{action} has unknown fields")

            account_pubkey = _require_str(data.get("account_pubkey"), name="account_pubkey", non_empty=True, max_len=512)
            if account_pubkey != tx_sender_pubkey:
                return PerpTxResult(ok=False, error="account_pubkey must match tx sender")

            accounts = dict(market.accounts)
            if version in (PERP_OP_VERSION_CH2P_V0_2, PERP_OP_VERSION_CH2P_V1_0) and account_pubkey not in accounts:
                return PerpTxResult(ok=False, error="unknown account_pubkey for this clearinghouse_2p market")
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
            if version != PERP_OP_VERSION_V0_1:
                return PerpTxResult(ok=False, error="set_position requires perps.version=0.1")

            allowed = {"module", "version", "market_id", "action", "account_pubkey", "new_position_base"}
            if set(data.keys()) - allowed:
                return PerpTxResult(ok=False, error="set_position has unknown fields")

            account_pubkey = _require_str(data.get("account_pubkey"), name="account_pubkey", non_empty=True, max_len=512)
            if account_pubkey != tx_sender_pubkey:
                return PerpTxResult(ok=False, error="account_pubkey must match tx sender")

            accounts = dict(market.accounts)
            acct = accounts.get(account_pubkey) or _kernel_initial_account_state()

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

        if action == "set_position_pair":
            if version not in (PERP_OP_VERSION_CH2P_V0_2, PERP_OP_VERSION_CH2P_V1_0):
                return PerpTxResult(ok=False, error="set_position_pair requires perps.version=0.2 or 1.0")
            if len(market.accounts) != 2:
                return PerpTxResult(ok=False, error="clearinghouse_2p requires exactly 2 accounts")

            allowed = {
                "module",
                "version",
                "market_id",
                "action",
                "account_a_pubkey",
                "account_b_pubkey",
                "new_position_base_a",
                "new_position_base_b",
            }
            if set(data.keys()) - allowed:
                return PerpTxResult(ok=False, error="set_position_pair has unknown fields")

            account_a_pubkey = _require_str(
                data.get("account_a_pubkey"), name="account_a_pubkey", non_empty=True, max_len=512
            )
            account_b_pubkey = _require_str(
                data.get("account_b_pubkey"), name="account_b_pubkey", non_empty=True, max_len=512
            )
            if account_a_pubkey == account_b_pubkey:
                return PerpTxResult(ok=False, error="accounts must be distinct")
            if set(market.accounts.keys()) != {account_a_pubkey, account_b_pubkey}:
                return PerpTxResult(ok=False, error="accounts do not match this market")

            new_a = _require_int(data.get("new_position_base_a"), name="new_position_base_a", non_negative=False)
            new_b = _require_int(data.get("new_position_base_b"), name="new_position_base_b", non_negative=False)
            if new_a + new_b != 0:
                return PerpTxResult(ok=False, error="clearinghouse_2p requires net position == 0")

            accounts = dict(market.accounts)
            acct_a = accounts[account_a_pubkey]
            acct_b = accounts[account_b_pubkey]

            res_a = perp_epoch_isolated_default_apply(
                state=market.kernel_state_for_account(acct_a),
                action="set_position",
                params={"new_position_base": new_a, "auth_ok": True},
            )
            if not res_a.ok or res_a.state is None:
                return PerpTxResult(ok=False, error=res_a.error or "set_position_pair rejected (a)")
            res_b = perp_epoch_isolated_default_apply(
                state=market.kernel_state_for_account(acct_b),
                action="set_position",
                params={"new_position_base": new_b, "auth_ok": True},
            )
            if not res_b.ok or res_b.state is None:
                return PerpTxResult(ok=False, error=res_b.error or "set_position_pair rejected (b)")

            post_global_a, post_acct_a = _split_kernel_state(res_a.state)
            post_global_b, post_acct_b = _split_kernel_state(res_b.state)
            if post_global_a != market.global_state or post_global_b != market.global_state:
                return PerpTxResult(ok=False, error="internal error: set_position_pair mutated global state")

            accounts[account_a_pubkey] = post_acct_a
            accounts[account_b_pubkey] = post_acct_b
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
                    "account_a_pubkey": account_a_pubkey,
                    "account_b_pubkey": account_b_pubkey,
                    "effects_a": dict(res_a.effects or {}),
                    "effects_b": dict(res_b.effects or {}),
                }
            )
            continue

        return PerpTxResult(ok=False, error=f"unknown perps action: {action}")

    next_perps = PerpsState(version=perps.version, markets=markets) if markets else None
    next_state = replace(state, balances=balances, perps=next_perps)
    return PerpTxResult(ok=True, state=next_state, effects=effects)
