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
  - Clearinghouse collateral is tracked internally in quote-e8 units so epoch PnL is exact and conserved.
  - The clearinghouse state transition is spec-driven: the persistent market state stores a kernel-state dict.

Per-account risk checks (guards/limits) reuse the epoch-perp risk kernel wrapper in
`src/core/perp_epoch.py` (native Python implementation by default). The optional
kernel-spec verification/codegen toolchain is used for evidence and parity testing,
not required at runtime.
"""

from __future__ import annotations

from dataclasses import dataclass, fields, replace
from functools import lru_cache
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
import sys
from typing import Any, Dict, List, Mapping, Optional

from ..core.dex import DexState
from ..core.perp_epoch import (
    perp_epoch_isolated_default_apply,
    perp_epoch_isolated_default_fee_pool_max_quote,
    perp_epoch_isolated_default_initial_state,
)
from ..core.perps import (
    PERP_CLEARINGHOUSE_2P_STATE_KEYS,
    PERP_GLOBAL_KEYS,
    PERPS_STATE_VERSION,
    PERPS_STATE_VERSION_V5,
    PerpClearinghouse2pMarketState,
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

_E8_SCALE = 100_000_000


@lru_cache
def _load_ch2p_ref_model():
    """Load the generated Python reference model for the clearinghouse kernel.

    This is a deterministic, dependency-free reference implementation generated
    from the YAML kernel spec and committed into this repo under `generated/`.
    We load it by file path so this module does not depend on any packaging or
    import-path configuration.
    """

    root = Path(__file__).resolve().parents[2]
    ref_path = root / "generated" / "perp_python" / "perp_epoch_clearinghouse_2p_v0_1_ref.py"
    if not ref_path.is_file():
        raise FileNotFoundError(
            f"missing generated clearinghouse ref model at {ref_path}; run tools/export_kernel_artifacts.py"
        )
    spec = spec_from_file_location("perp_epoch_clearinghouse_2p_v0_1_ref", ref_path)
    if spec is None or spec.loader is None:
        raise ImportError(f"failed to load module spec for {ref_path}")
    module = module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)

    field_names = [f.name for f in fields(module.State)]
    if set(field_names) != set(PERP_CLEARINGHOUSE_2P_STATE_KEYS):
        raise RuntimeError(
            "clearinghouse ref model state fields do not match PERP_CLEARINGHOUSE_2P_STATE_KEYS; "
            "regenerate artifacts and update src/core/perps.py"
        )
    return module


def _ch2p_state_from_dict(state: Mapping[str, Any]):
    ref = _load_ch2p_ref_model()
    kwargs = {name: state[name] for name in (f.name for f in fields(ref.State))}
    s = ref.State(**kwargs)
    ok, failed = ref.check_invariants(s)
    if not ok:
        raise ValueError(f"invalid clearinghouse state (invariant {failed})")
    return s


def _ch2p_state_to_dict(state) -> Dict[str, Any]:
    ref = _load_ch2p_ref_model()
    return {f.name: getattr(state, f.name) for f in fields(ref.State)}


def _ch2p_init_state_dict() -> Dict[str, Any]:
    ref = _load_ch2p_ref_model()
    return _ch2p_state_to_dict(ref.init_state())


def _ch2p_step(state_dict: Mapping[str, Any], *, tag: str, args: Mapping[str, Any]) -> tuple[Dict[str, Any], Dict[str, Any]]:
    ref = _load_ch2p_ref_model()
    cmd = ref.Command(tag=tag, args=dict(args))
    res = ref.step(_ch2p_state_from_dict(state_dict), cmd)
    if not res.ok or res.state is None:
        raise ValueError(res.error or f"{tag} rejected")
    ok, failed = ref.check_invariants(res.state)
    if not ok:
        raise ValueError(f"post-invariant violated: {failed}")
    return _ch2p_state_to_dict(res.state), dict(res.effects or {})


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
    perps_version = PERPS_STATE_VERSION
    if perps is None:
        perps = PerpsState(version=PERPS_STATE_VERSION, markets={})
    else:
        perps_version = int(perps.version)

    markets = dict(perps.markets)
    # Perps state v5 is a strict superset of v4 (adds per-market kind tags). If
    # any op uses the clearinghouse posture, upgrade in-memory to v5.
    if any(op.version in (PERP_OP_VERSION_CH2P_V0_2, PERP_OP_VERSION_CH2P_V1_0) for op in ops):
        perps_version = max(perps_version, PERPS_STATE_VERSION_V5)
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

            # Clearinghouse markets require perps state v5+ (market kind tags).
            perps_version = max(perps_version, PERPS_STATE_VERSION_V5)
            try:
                init_state = _ch2p_init_state_dict()
            except Exception as exc:
                return PerpTxResult(ok=False, error=str(exc))
            markets[market_id] = PerpClearinghouse2pMarketState(
                quote_asset=quote_asset,
                account_a_pubkey=account_a_pubkey,
                account_b_pubkey=account_b_pubkey,
                state=init_state,
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

        market_any = markets.get(market_id)
        if market_any is None:
            return PerpTxResult(ok=False, error="unknown market_id")

        if action in ("advance_epoch", "publish_clearing_price", "settle_epoch", "clear_breaker", "set_position_pair"):
            err = _require_operator(config, tx_sender_pubkey=tx_sender_pubkey)
            if err is not None:
                return PerpTxResult(ok=False, error=err)

        is_ch2p = version in (PERP_OP_VERSION_CH2P_V0_2, PERP_OP_VERSION_CH2P_V1_0)
        if is_ch2p:
            if not isinstance(market_any, PerpClearinghouse2pMarketState):
                return PerpTxResult(ok=False, error="market kind mismatch for clearinghouse operation")
            ch2p_market = market_any
        else:
            if not isinstance(market_any, PerpMarketState):
                return PerpTxResult(ok=False, error="market kind mismatch for isolated operation")
            market = market_any

        if is_ch2p and action == "advance_epoch":
            allowed = {"module", "version", "market_id", "action", "delta"}
            if set(data.keys()) - allowed:
                return PerpTxResult(ok=False, error="advance_epoch has unknown fields")
            # Scheduler rule: only advance when the current epoch is settled.
            if int(ch2p_market.state.get("oracle_last_update_epoch", 0)) != int(ch2p_market.state.get("now_epoch", 0)):
                return PerpTxResult(ok=False, error="cannot advance epoch before settling current epoch")
            delta = _require_int(data.get("delta"), name="delta", non_negative=True)
            try:
                next_state, eff = _ch2p_step(ch2p_market.state, tag="advance_epoch", args={"delta": delta})
            except Exception as exc:
                return PerpTxResult(ok=False, error=str(exc))
            markets[market_id] = PerpClearinghouse2pMarketState(
                quote_asset=ch2p_market.quote_asset,
                account_a_pubkey=ch2p_market.account_a_pubkey,
                account_b_pubkey=ch2p_market.account_b_pubkey,
                state=next_state,
            )
            effects.append({"i": i, "market_id": market_id, "action": action, "effects": eff})
            continue

        if is_ch2p and action == "publish_clearing_price":
            allowed = {"module", "version", "market_id", "action", "price_e8"}
            if set(data.keys()) - allowed:
                return PerpTxResult(ok=False, error="publish_clearing_price has unknown fields")
            price_e8 = _require_int(data.get("price_e8"), name="price_e8", non_negative=True)
            try:
                next_state, eff = _ch2p_step(ch2p_market.state, tag="publish_clearing_price", args={"price_e8": price_e8})
            except Exception as exc:
                return PerpTxResult(ok=False, error=str(exc))
            markets[market_id] = PerpClearinghouse2pMarketState(
                quote_asset=ch2p_market.quote_asset,
                account_a_pubkey=ch2p_market.account_a_pubkey,
                account_b_pubkey=ch2p_market.account_b_pubkey,
                state=next_state,
            )
            effects.append({"i": i, "market_id": market_id, "action": action, "effects": eff})
            continue

        if is_ch2p and action == "settle_epoch":
            allowed = {"module", "version", "market_id", "action"}
            if set(data.keys()) - allowed:
                return PerpTxResult(ok=False, error="settle_epoch has unknown fields")
            try:
                next_state, eff = _ch2p_step(ch2p_market.state, tag="settle_epoch", args={})
            except Exception as exc:
                return PerpTxResult(ok=False, error=str(exc))
            markets[market_id] = PerpClearinghouse2pMarketState(
                quote_asset=ch2p_market.quote_asset,
                account_a_pubkey=ch2p_market.account_a_pubkey,
                account_b_pubkey=ch2p_market.account_b_pubkey,
                state=next_state,
            )
            effects.append({"i": i, "market_id": market_id, "action": action, "effects": eff})
            continue

        if is_ch2p and action == "clear_breaker":
            allowed = {"module", "version", "market_id", "action"}
            if set(data.keys()) - allowed:
                return PerpTxResult(ok=False, error="clear_breaker has unknown fields")
            if int(ch2p_market.state.get("position_base_a", 0)) != 0 or int(ch2p_market.state.get("position_base_b", 0)) != 0:
                return PerpTxResult(ok=False, error="cannot clear breaker while positions are open")
            try:
                next_state, eff = _ch2p_step(ch2p_market.state, tag="clear_breaker", args={"auth_ok": True})
            except Exception as exc:
                return PerpTxResult(ok=False, error=str(exc))
            markets[market_id] = PerpClearinghouse2pMarketState(
                quote_asset=ch2p_market.quote_asset,
                account_a_pubkey=ch2p_market.account_a_pubkey,
                account_b_pubkey=ch2p_market.account_b_pubkey,
                state=next_state,
            )
            effects.append({"i": i, "market_id": market_id, "action": action, "effects": eff})
            continue

        if is_ch2p and action in ("deposit_collateral", "withdraw_collateral"):
            allowed_common = {"module", "version", "market_id", "action", "account_pubkey"}
            allowed = allowed_common | {"amount"}
            if set(data.keys()) - allowed:
                return PerpTxResult(ok=False, error=f"{action} has unknown fields")

            account_pubkey = _require_str(data.get("account_pubkey"), name="account_pubkey", non_empty=True, max_len=512)
            if account_pubkey != tx_sender_pubkey:
                return PerpTxResult(ok=False, error="account_pubkey must match tx sender")

            role = ch2p_market.role_for_pubkey(account_pubkey)
            if role is None:
                return PerpTxResult(ok=False, error="unknown account_pubkey for this clearinghouse_2p market")

            amount = _require_int(data.get("amount"), name="amount", non_negative=True)
            # Protocol balances are in quote units; the clearinghouse kernel tracks quote-e8 for exact PnL.
            amount_e8 = int(amount) * _E8_SCALE

            if action == "deposit_collateral":
                if balances.get(account_pubkey, ch2p_market.quote_asset) < amount:
                    return PerpTxResult(ok=False, error="insufficient balance for deposit")
                tag = "deposit_collateral_a" if role == "a" else "deposit_collateral_b"
                try:
                    next_state, eff = _ch2p_step(
                        ch2p_market.state,
                        tag=tag,
                        args={"amount_e8": amount_e8, "auth_ok": True},
                    )
                except Exception as exc:
                    return PerpTxResult(ok=False, error=str(exc))
                balances.subtract(account_pubkey, ch2p_market.quote_asset, amount)
            else:
                tag = "withdraw_collateral_a" if role == "a" else "withdraw_collateral_b"
                try:
                    next_state, eff = _ch2p_step(
                        ch2p_market.state,
                        tag=tag,
                        args={"amount_e8": amount_e8, "auth_ok": True},
                    )
                except Exception as exc:
                    return PerpTxResult(ok=False, error=str(exc))
                balances.add(account_pubkey, ch2p_market.quote_asset, amount)

            markets[market_id] = PerpClearinghouse2pMarketState(
                quote_asset=ch2p_market.quote_asset,
                account_a_pubkey=ch2p_market.account_a_pubkey,
                account_b_pubkey=ch2p_market.account_b_pubkey,
                state=next_state,
            )
            effects.append({"i": i, "market_id": market_id, "action": action, "account_pubkey": account_pubkey, "effects": eff})
            continue

        if is_ch2p and action == "set_position_pair":
            if version not in (PERP_OP_VERSION_CH2P_V0_2, PERP_OP_VERSION_CH2P_V1_0):
                return PerpTxResult(ok=False, error="set_position_pair requires perps.version=0.2 or 1.0")

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
            if account_a_pubkey != ch2p_market.account_a_pubkey or account_b_pubkey != ch2p_market.account_b_pubkey:
                return PerpTxResult(ok=False, error="accounts do not match this market")

            new_a = _require_int(data.get("new_position_base_a"), name="new_position_base_a", non_negative=False)
            new_b = _require_int(data.get("new_position_base_b"), name="new_position_base_b", non_negative=False)
            if new_b != -new_a:
                return PerpTxResult(ok=False, error="clearinghouse_2p requires net position == 0")

            try:
                next_state, eff = _ch2p_step(
                    ch2p_market.state,
                    tag="set_position_pair",
                    args={"new_position_base_a": new_a, "auth_ok": True},
                )
            except Exception as exc:
                return PerpTxResult(ok=False, error=str(exc))

            markets[market_id] = PerpClearinghouse2pMarketState(
                quote_asset=ch2p_market.quote_asset,
                account_a_pubkey=ch2p_market.account_a_pubkey,
                account_b_pubkey=ch2p_market.account_b_pubkey,
                state=next_state,
            )
            effects.append({"i": i, "market_id": market_id, "action": action, "effects": eff})
            continue

        if is_ch2p:
            return PerpTxResult(ok=False, error=f"unknown perps action: {action}")

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

    next_perps = PerpsState(version=perps_version, markets=markets) if markets else None
    next_state = replace(state, balances=balances, perps=next_perps)
    return PerpTxResult(ok=True, state=next_state, effects=effects)
