"""Live zUSD monetary bridge for Tau app-state transactions.

This adapter binds the pure single-vault zUSD kernel to Tau app-state balances:

- collateral deposits and withdrawals move native balance entries;
- zUSD mint/repay/redeem moves transferable zUSD balance entries;
- stability-pool deposits are held in a deterministic zUSD escrow account;
- liquidation burns escrowed zUSD and assigns collateral gains to SP accounts.

The pure kernel uses E8 monetary amounts. The existing token/perps transport uses
whole quote units, so this bridge only exposes whole-zUSD balance movements and
rejects non-whole zUSD amounts at the app boundary.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass, replace
from typing import Any, Mapping, Optional, Tuple

from ..core.dex import DexState
from ..core.zusd import BPS_SCALE, E8, ZUSDCommand, ZUSDState, check_invariants, init_state, step
from ..state.balances import BalanceTable, NATIVE_ASSET
from ..state.canonical import bounded_json_utf8_size, canonical_hex_fixed_allow_0x, canonical_json_bytes
from ..state.nonces import NonceTable
from .zeno_oracle_authorization import RuntimeActionFacts, check_critical_consumer_authorization, semantic_hash
from .zusd_tau_token import derive_zusd_tau_asset_id


ZUSD_MONETARY_SCHEMA = "zenodex/zusd_monetary_state/v1"
ZUSD_MONETARY_MODULE = "ZUSDFinance"
ZUSD_MONETARY_VERSION = "0.1"

_U32_MAX = 0xFFFFFFFF
_MAX_OPS = 128
_MAX_OP_BYTES = 64_000
_MAX_TOTAL_OPS_BYTES = 512_000
_ORACLE_CONSUMER_PROFILE_SCHEMA = "zenodex.oracle.consumer_profile.v1"
_ORACLE_ZUSD_COLLATERAL_QUERY_ID = (
    "sha256:" + hashlib.sha256(b"zenodex.oracle.query.zusd.collateral_price_e8").hexdigest()
)
_ZUSD_ORACLE_ADAPTER_ACTIONS = {"mint_zusd": "mint", "liquidate": "liquidate_vault"}
_ZUSD_ORACLE_AUTH_ACTIONS = frozenset({"mint_zusd", "liquidate"})
_ORACLE_AUTHORIZATION_FIELD = "oracle_authorization"


@dataclass(frozen=True)
class ZUSDMonetaryConfig:
    chain_id: str = "tau-local"
    oracle_pubkey: Optional[str] = None
    asset_id: Optional[str] = None
    liquidation_gas_comp_fixed_collateral_e8: int = 0
    liquidation_gas_comp_bps: int = 0
    require_oracle_authorization: bool = False

    @property
    def zusd_asset(self) -> str:
        if self.asset_id is not None:
            return _canonical_asset(self.asset_id, name="asset_id")
        return derive_zusd_tau_asset_id(chain_id=self.chain_id)


@dataclass(frozen=True)
class ZUSDMonetaryState:
    core: ZUSDState
    vault_owner_pubkey: Optional[str] = None
    sp_deposits_e8: Mapping[str, int] | None = None
    sp_collateral_claims_e8: Mapping[str, int] | None = None

    def __post_init__(self) -> None:
        if self.vault_owner_pubkey is not None:
            _canonical_pubkey(self.vault_owner_pubkey, name="vault_owner_pubkey")
        deposits = dict(self.sp_deposits_e8 or {})
        claims = dict(self.sp_collateral_claims_e8 or {})
        for table_name, table in (("sp_deposits_e8", deposits), ("sp_collateral_claims_e8", claims)):
            for pk, amount in table.items():
                _canonical_pubkey(pk, name=f"{table_name}.pubkey")
                _require_nonnegative_int(amount, name=f"{table_name}[{pk}]")
        object.__setattr__(self, "sp_deposits_e8", deposits)
        object.__setattr__(self, "sp_collateral_claims_e8", claims)


@dataclass(frozen=True)
class ZUSDMonetaryTxResult:
    ok: bool
    state: Optional[DexState] = None
    zusd_state: Optional[ZUSDMonetaryState] = None
    effects: Optional[list[dict[str, Any]]] = None
    error: Optional[str] = None


def init_monetary_state(config: ZUSDMonetaryConfig | None = None) -> ZUSDMonetaryState:
    core = init_state()
    if config is not None:
        core = ZUSDState(
            **{
                **core.__dict__,
                "liquidation_gas_comp_fixed_collateral_e8": _require_nonnegative_int(
                    config.liquidation_gas_comp_fixed_collateral_e8,
                    name="liquidation_gas_comp_fixed_collateral_e8",
                ),
                "liquidation_gas_comp_bps": _require_int(
                    config.liquidation_gas_comp_bps,
                    name="liquidation_gas_comp_bps",
                    minimum=0,
                    maximum=BPS_SCALE,
                ),
            }
        )
    return ZUSDMonetaryState(core=core, sp_deposits_e8={}, sp_collateral_claims_e8={})


def stability_pool_pubkey(*, chain_id: str) -> str:
    if not isinstance(chain_id, str) or not chain_id.strip():
        raise ValueError("chain_id must be a non-empty string")
    payload = b"zenodex:zusd:stability_pool:v1\x00" + chain_id.strip().encode("utf-8")
    return "0x" + hashlib.sha384(payload).hexdigest()


def zusd_monetary_sender_nonce_key(sender_pubkey: str) -> str:
    sender = _canonical_pubkey(sender_pubkey, name="sender_pubkey")
    payload = b"zenodex:zusd_monetary_nonce:v1\x00" + sender.encode("ascii")
    return "0x" + hashlib.sha384(payload).hexdigest()


def zusd_monetary_state_to_obj(state: ZUSDMonetaryState) -> dict[str, Any]:
    deposits = [
        {"pubkey": pk, "amount_e8": int(amount)}
        for pk, amount in sorted(dict(state.sp_deposits_e8 or {}).items())
        if int(amount) > 0
    ]
    claims = [
        {"pubkey": pk, "amount_e8": int(amount)}
        for pk, amount in sorted(dict(state.sp_collateral_claims_e8 or {}).items())
        if int(amount) > 0
    ]
    return {
        "schema": ZUSD_MONETARY_SCHEMA,
        "version": 1,
        "core": dict(state.core.__dict__),
        "vault_owner_pubkey": state.vault_owner_pubkey,
        "sp_deposits": deposits,
        "sp_collateral_claims": claims,
    }


def zusd_monetary_state_from_obj(obj: Mapping[str, Any]) -> ZUSDMonetaryState:
    if not isinstance(obj, Mapping):
        raise TypeError("zusd_monetary must be an object")
    _reject_unknown_fields(
        obj,
        allowed={"schema", "version", "core", "vault_owner_pubkey", "sp_deposits", "sp_collateral_claims"},
        name="zusd_monetary",
    )
    schema = _require_str(obj.get("schema"), name="zusd_monetary.schema")
    if schema != ZUSD_MONETARY_SCHEMA:
        raise ValueError(f"unsupported zusd_monetary schema: {schema!r}")
    version = _require_int(obj.get("version"), name="zusd_monetary.version", minimum=1)
    if version != 1:
        raise ValueError(f"unsupported zusd_monetary version: {version}")
    core_obj = obj.get("core")
    if not isinstance(core_obj, Mapping):
        raise TypeError("zusd_monetary.core must be an object")
    core = ZUSDState(**dict(core_obj))
    owner_raw = obj.get("vault_owner_pubkey")
    owner = None if owner_raw is None else _canonical_pubkey(owner_raw, name="zusd_monetary.vault_owner_pubkey")
    deposits = _parse_account_amount_entries(obj.get("sp_deposits"), name="zusd_monetary.sp_deposits")
    claims = _parse_account_amount_entries(obj.get("sp_collateral_claims"), name="zusd_monetary.sp_collateral_claims")
    state = ZUSDMonetaryState(
        core=core,
        vault_owner_pubkey=owner,
        sp_deposits_e8=deposits,
        sp_collateral_claims_e8=claims,
    )
    err = _state_invariant_error(state)
    if err is not None:
        raise ValueError(err)
    return state


def apply_zusd_monetary_ops(
    *,
    config: ZUSDMonetaryConfig,
    state: DexState,
    zusd_state: ZUSDMonetaryState | None,
    operations: Any,
    tx_sender_pubkey: str,
    block_timestamp: int,
) -> ZUSDMonetaryTxResult:
    try:
        ops = _parse_ops(operations)
        if not ops:
            return ZUSDMonetaryTxResult(ok=True, state=state, zusd_state=zusd_state, effects=[])

        raw_sender, sender_had_0x = _raw_pubkey_key(tx_sender_pubkey)
        sender = _canonical_pubkey(tx_sender_pubkey, name="tx_sender_pubkey")
        balances = _copy_balance_table(state.balances)
        nonces = _copy_nonce_table(state.nonces)
        working = zusd_state or init_monetary_state(config)
        effects: list[dict[str, Any]] = []
        zusd_asset = config.zusd_asset
        sp_pubkey = stability_pool_pubkey(chain_id=config.chain_id)
        native_sender = _native_sender_key(
            balances,
            sender=sender,
            raw_sender=raw_sender,
            sender_had_0x=sender_had_0x,
        )

        _assert_sp_escrow_matches(balances, working, zusd_asset=zusd_asset, sp_pubkey=sp_pubkey)

        nonce_key = zusd_monetary_sender_nonce_key(sender)
        for i, op in enumerate(ops):
            action = _require_action(op, index=i)
            nonce = _require_int(op.get("nonce"), name=f"zusd op[{i}].nonce", minimum=1, maximum=_U32_MAX)
            expected = int(nonces.get_last(nonce_key)) + 1
            if nonce != expected:
                return ZUSDMonetaryTxResult(
                    ok=False,
                    error=f"zusd op[{i}] nonce invalid (expected {expected}, got {nonce})",
                )
            deadline_err = _deadline_error(op=op, block_timestamp=block_timestamp, index=i)
            if deadline_err is not None:
                return ZUSDMonetaryTxResult(ok=False, error=deadline_err)

            allowed = _allowed_fields_for_action(action)
            extra = set(op.keys()) - allowed
            if extra:
                return ZUSDMonetaryTxResult(ok=False, error=f"zusd op[{i}] unknown fields: {sorted(extra)}")

            oracle_error = _oracle_authorization_error(config=config, zusd_state=working, action=action, op=op)
            if oracle_error is not None:
                return ZUSDMonetaryTxResult(ok=False, error=f"zusd op[{i}] {oracle_error}")

            try:
                working, balance_effect = _apply_one(
                    config=config,
                    balances=balances,
                    monetary_state=working,
                    op=op,
                    action=action,
                    sender=sender,
                    native_sender=native_sender,
                    zusd_asset=zusd_asset,
                    sp_pubkey=sp_pubkey,
                )
            except Exception as exc:
                return ZUSDMonetaryTxResult(ok=False, error=f"zusd op[{i}] {exc}")

            nonces.set_last(nonce_key, nonce)
            effect = {"i": i, "action": action, "effects": balance_effect}
            effects.append(effect)
            _assert_sp_escrow_matches(balances, working, zusd_asset=zusd_asset, sp_pubkey=sp_pubkey)

        next_state = replace(state, balances=balances, nonces=nonces)
        return ZUSDMonetaryTxResult(ok=True, state=next_state, zusd_state=working, effects=effects)
    except Exception as exc:
        return ZUSDMonetaryTxResult(ok=False, error=_safe_error_str(exc))


def _apply_one(
    *,
    config: ZUSDMonetaryConfig,
    balances: BalanceTable,
    monetary_state: ZUSDMonetaryState,
    op: Mapping[str, Any],
    action: str,
    sender: str,
    native_sender: str,
    zusd_asset: str,
    sp_pubkey: str,
) -> tuple[ZUSDMonetaryState, dict[str, Any]]:
    core = monetary_state.core
    owner = monetary_state.vault_owner_pubkey
    deposits = dict(monetary_state.sp_deposits_e8 or {})
    claims = dict(monetary_state.sp_collateral_claims_e8 or {})

    if action in {"bootstrap_oracle", "oracle_report", "oracle_commit"}:
        _require_oracle_sender(config, sender=sender)
        args: dict[str, Any] = {"auth_ok": True}
        if action in {"bootstrap_oracle", "oracle_report"}:
            args["price_e8"] = _require_int(op.get("price_e8"), name=f"{action}.price_e8", minimum=1)
        result = step(core, ZUSDCommand(tag=action, args=args))
        if not result.ok or result.state is None:
            raise ValueError(result.error or f"{action} rejected")
        next_state = ZUSDMonetaryState(core=result.state, vault_owner_pubkey=owner, sp_deposits_e8=deposits, sp_collateral_claims_e8=claims)
        _raise_if_bad_state(next_state)
        return next_state, dict(result.effects or {})

    if action == "advance_epoch":
        delta = _require_int(op.get("delta"), name="advance_epoch.delta", minimum=1)
        result = step(core, ZUSDCommand(tag=action, args={"delta": delta}))
        if not result.ok or result.state is None:
            raise ValueError(result.error or "advance_epoch rejected")
        next_state = ZUSDMonetaryState(core=result.state, vault_owner_pubkey=owner, sp_deposits_e8=deposits, sp_collateral_claims_e8=claims)
        _raise_if_bad_state(next_state)
        return next_state, dict(result.effects or {})

    if action in {"deposit_collateral", "withdraw_collateral", "mint_zusd", "repay_zusd"}:
        op_owner = _canonical_pubkey(op.get("owner_pubkey", sender), name=f"{action}.owner_pubkey")
        if op_owner != sender:
            raise ValueError("owner_pubkey mismatch")
        if owner is None:
            if action not in {"deposit_collateral"}:
                raise ValueError("vault owner not initialized")
            owner = sender
        elif owner != sender:
            raise ValueError("vault owner mismatch")

    if action == "deposit_collateral":
        amount_e8 = _require_int(op.get("amount_e8"), name="deposit_collateral.amount_e8", minimum=1)
        if balances.get(native_sender, NATIVE_ASSET) < amount_e8:
            raise ValueError("insufficient native collateral balance")
        result = step(core, ZUSDCommand(tag=action, args={"amount_e8": amount_e8}))
        if not result.ok or result.state is None:
            raise ValueError(result.error or "deposit_collateral rejected")
        balances.subtract(native_sender, NATIVE_ASSET, amount_e8)
        next_state = ZUSDMonetaryState(core=result.state, vault_owner_pubkey=owner, sp_deposits_e8=deposits, sp_collateral_claims_e8=claims)
        _raise_if_bad_state(next_state)
        return next_state, {**dict(result.effects or {}), "native_balance_delta_e8": -amount_e8}

    if action == "withdraw_collateral":
        amount_e8 = _require_int(op.get("amount_e8"), name="withdraw_collateral.amount_e8", minimum=1)
        result = step(core, ZUSDCommand(tag=action, args={"amount_e8": amount_e8}))
        if not result.ok or result.state is None:
            raise ValueError(result.error or "withdraw_collateral rejected")
        balances.add(native_sender, NATIVE_ASSET, amount_e8)
        next_state = ZUSDMonetaryState(core=result.state, vault_owner_pubkey=owner, sp_deposits_e8=deposits, sp_collateral_claims_e8=claims)
        _raise_if_bad_state(next_state)
        return next_state, {**dict(result.effects or {}), "native_balance_delta_e8": amount_e8}

    if action == "mint_zusd":
        amount_e8 = _require_whole_zusd_amount(op.get("amount_e8"), name="mint_zusd.amount_e8")
        result = step(core, ZUSDCommand(tag=action, args={"amount_e8": amount_e8}))
        if not result.ok or result.state is None:
            raise ValueError(result.error or "mint_zusd rejected")
        minted_units = _e8_to_whole_units(int((result.effects or {}).get("principal_e8", amount_e8)), name="mint_zusd.principal_e8")
        balances.add(sender, zusd_asset, minted_units)
        next_state = ZUSDMonetaryState(core=result.state, vault_owner_pubkey=owner, sp_deposits_e8=deposits, sp_collateral_claims_e8=claims)
        _raise_if_bad_state(next_state)
        return next_state, {**dict(result.effects or {}), "zusd_balance_delta": minted_units}

    if action == "repay_zusd":
        amount_e8 = _require_whole_zusd_amount(op.get("amount_e8"), name="repay_zusd.amount_e8")
        units = _e8_to_whole_units(amount_e8, name="repay_zusd.amount_e8")
        if balances.get(sender, zusd_asset) < units:
            raise ValueError("insufficient zUSD balance")
        result = step(core, ZUSDCommand(tag=action, args={"amount_e8": amount_e8}))
        if not result.ok or result.state is None:
            raise ValueError(result.error or "repay_zusd rejected")
        balances.subtract(sender, zusd_asset, units)
        next_state = ZUSDMonetaryState(core=result.state, vault_owner_pubkey=owner, sp_deposits_e8=deposits, sp_collateral_claims_e8=claims)
        _raise_if_bad_state(next_state)
        return next_state, {**dict(result.effects or {}), "zusd_balance_delta": -units}

    if action == "deposit_sp":
        account = _sender_account(op, sender=sender, action=action)
        amount_e8 = _require_whole_zusd_amount(op.get("amount_e8"), name="deposit_sp.amount_e8")
        units = _e8_to_whole_units(amount_e8, name="deposit_sp.amount_e8")
        if balances.get(account, zusd_asset) < units:
            raise ValueError("insufficient zUSD balance")
        result = step(core, ZUSDCommand(tag=action, args={"amount_e8": amount_e8}))
        if not result.ok or result.state is None:
            raise ValueError(result.error or "deposit_sp rejected")
        balances.subtract(account, zusd_asset, units)
        balances.add(sp_pubkey, zusd_asset, units)
        deposits[account] = int(deposits.get(account, 0)) + amount_e8
        next_state = ZUSDMonetaryState(core=result.state, vault_owner_pubkey=owner, sp_deposits_e8=deposits, sp_collateral_claims_e8=claims)
        _raise_if_bad_state(next_state)
        return next_state, {**dict(result.effects or {}), "zusd_balance_delta": -units, "sp_escrow_delta": units}

    if action == "withdraw_sp":
        account = _sender_account(op, sender=sender, action=action)
        amount_e8 = _require_whole_zusd_amount(op.get("amount_e8"), name="withdraw_sp.amount_e8")
        current = int(deposits.get(account, 0))
        if amount_e8 > current:
            raise ValueError("withdraw_sp exceeds account deposit")
        units = _e8_to_whole_units(amount_e8, name="withdraw_sp.amount_e8")
        if balances.get(sp_pubkey, zusd_asset) < units:
            raise ValueError("stability pool escrow balance too low")
        result = step(core, ZUSDCommand(tag=action, args={"amount_e8": amount_e8}))
        if not result.ok or result.state is None:
            raise ValueError(result.error or "withdraw_sp rejected")
        balances.subtract(sp_pubkey, zusd_asset, units)
        balances.add(account, zusd_asset, units)
        deposits = _set_or_drop(deposits, account, current - amount_e8)
        next_state = ZUSDMonetaryState(core=result.state, vault_owner_pubkey=owner, sp_deposits_e8=deposits, sp_collateral_claims_e8=claims)
        _raise_if_bad_state(next_state)
        return next_state, {**dict(result.effects or {}), "zusd_balance_delta": units, "sp_escrow_delta": -units}

    if action == "redeem_zusd":
        account = _sender_account(op, sender=sender, action=action)
        amount_e8 = _require_whole_zusd_amount(op.get("amount_e8"), name="redeem_zusd.amount_e8")
        units = _e8_to_whole_units(amount_e8, name="redeem_zusd.amount_e8")
        if balances.get(account, zusd_asset) < units:
            raise ValueError("insufficient zUSD balance")
        result = step(core, ZUSDCommand(tag=action, args={"amount_e8": amount_e8}))
        if not result.ok or result.state is None or result.effects is None:
            raise ValueError(result.error or "redeem_zusd rejected")
        collateral_out = _require_int(result.effects.get("redeemed_collateral_out_e8"), name="redeemed_collateral_out_e8", minimum=0)
        balances.subtract(account, zusd_asset, units)
        native_account = native_sender if account == sender else account
        balances.add(native_account, NATIVE_ASSET, collateral_out)
        next_state = ZUSDMonetaryState(core=result.state, vault_owner_pubkey=owner, sp_deposits_e8=deposits, sp_collateral_claims_e8=claims)
        _raise_if_bad_state(next_state)
        return next_state, {**dict(result.effects or {}), "zusd_balance_delta": -units, "native_balance_delta_e8": collateral_out}

    if action == "liquidate":
        pre_deposits = dict(deposits)
        result = step(core, ZUSDCommand(tag=action, args={}))
        if not result.ok or result.state is None or result.effects is None:
            raise ValueError(result.error or "liquidate rejected")
        liquidated_debt = _require_whole_zusd_amount(result.effects.get("liquidated_debt_e8"), name="liquidated_debt_e8")
        liquidated_coll = _require_int(
            result.effects.get("sp_collateral_gain_e8", result.effects.get("liquidated_collateral_e8")),
            name="sp_collateral_gain_e8",
            minimum=0,
        )
        liquidator_comp = _require_int(
            result.effects.get("liquidator_compensation_collateral_e8", 0),
            name="liquidator_compensation_collateral_e8",
            minimum=0,
        )
        debt_units = _e8_to_whole_units(liquidated_debt, name="liquidated_debt_e8")
        if balances.get(sp_pubkey, zusd_asset) < debt_units:
            raise ValueError("stability pool escrow balance too low")
        balances.subtract(sp_pubkey, zusd_asset, debt_units)
        if liquidator_comp > 0:
            balances.add(native_sender, NATIVE_ASSET, liquidator_comp)
        deposits, coll_gains = _allocate_liquidation(pre_deposits, debt_e8=liquidated_debt, collateral_e8=liquidated_coll)
        for pk, gain in coll_gains.items():
            claims[pk] = int(claims.get(pk, 0)) + int(gain)
        next_state = ZUSDMonetaryState(core=result.state, vault_owner_pubkey=owner, sp_deposits_e8=deposits, sp_collateral_claims_e8=claims)
        _raise_if_bad_state(next_state)
        return next_state, {
            **dict(result.effects or {}),
            "sp_escrow_delta": -debt_units,
            "native_balance_delta_e8": liquidator_comp,
            "sp_collateral_claims_e8": coll_gains,
        }

    if action == "claim_sp_collateral":
        account = _sender_account(op, sender=sender, action=action)
        amount_e8 = _require_int(op.get("amount_e8"), name="claim_sp_collateral.amount_e8", minimum=1)
        current = int(claims.get(account, 0))
        if amount_e8 > current:
            raise ValueError("claim exceeds account collateral gain")
        if amount_e8 > core.sp_coll_e8:
            raise ValueError("claim exceeds stability-pool collateral")
        next_core = ZUSDState(**{**core.__dict__, "sp_coll_e8": int(core.sp_coll_e8) - amount_e8})
        failures = check_invariants(next_core)
        if failures:
            raise ValueError(f"invariant violation: {','.join(failures)}")
        native_account = native_sender if account == sender else account
        balances.add(native_account, NATIVE_ASSET, amount_e8)
        claims = _set_or_drop(claims, account, current - amount_e8)
        next_state = ZUSDMonetaryState(core=next_core, vault_owner_pubkey=owner, sp_deposits_e8=deposits, sp_collateral_claims_e8=claims)
        _raise_if_bad_state(next_state)
        return next_state, {"event": "sp_collateral_claimed", "amount_e8": amount_e8, "native_balance_delta_e8": amount_e8}

    raise ValueError(f"unknown action: {action}")


def _parse_ops(raw_ops: Any) -> list[Mapping[str, Any]]:
    if raw_ops is None:
        return []
    if not isinstance(raw_ops, list):
        raise TypeError("zusd monetary op stream must be a list")
    if len(raw_ops) > _MAX_OPS:
        raise ValueError(f"too many zusd ops: {len(raw_ops)} > {_MAX_OPS}")
    total_bytes = 0
    out: list[Mapping[str, Any]] = []
    for i, raw in enumerate(raw_ops):
        if not isinstance(raw, Mapping):
            raise TypeError(f"zusd op[{i}] must be an object")
        op = dict(raw)
        size = bounded_json_utf8_size(op, max_bytes=_MAX_OP_BYTES)
        total_bytes += size
        if total_bytes > _MAX_TOTAL_OPS_BYTES:
            raise ValueError("zusd op stream too large")
        out.append(op)
    return out


def _require_action(op: Mapping[str, Any], *, index: int) -> str:
    module = str(op.get("module", ZUSD_MONETARY_MODULE))
    if module != ZUSD_MONETARY_MODULE:
        raise ValueError(f"zusd op[{index}] module must be {ZUSD_MONETARY_MODULE}")
    version = str(op.get("version", ZUSD_MONETARY_VERSION))
    if version != ZUSD_MONETARY_VERSION:
        raise ValueError(f"zusd op[{index}] version unsupported: {version!r}")
    action = str(op.get("action", "")).strip().lower()
    if action not in {
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
        "claim_sp_collateral",
    }:
        raise ValueError(f"zusd op[{index}] action unsupported: {action!r}")
    return action


def _allowed_fields_for_action(action: str) -> set[str]:
    base = {"module", "version", "action", "nonce", "deadline"}
    if action == "advance_epoch":
        return base | {"delta"}
    if action in {"bootstrap_oracle", "oracle_report"}:
        return base | {"price_e8"}
    if action == "oracle_commit":
        return base
    if action in {"deposit_collateral", "withdraw_collateral", "mint_zusd", "repay_zusd"}:
        fields = base | {"owner_pubkey", "amount_e8"}
        if action == "mint_zusd":
            return fields | {_ORACLE_AUTHORIZATION_FIELD}
        return fields
    if action in {"deposit_sp", "withdraw_sp", "redeem_zusd", "claim_sp_collateral"}:
        return base | {"account_pubkey", "amount_e8"}
    if action == "liquidate":
        return base | {_ORACLE_AUTHORIZATION_FIELD}
    return base


def _oracle_consumer_profile_id(*, action_kind: str, max_freshness_window_epochs: int) -> str:
    payload = {
        "schema": _ORACLE_CONSUMER_PROFILE_SCHEMA,
        "consumer_module": "zenodex.zusd",
        "action_kind": action_kind,
        "query_id": _ORACLE_ZUSD_COLLATERAL_QUERY_ID,
        "required_evidence_floor": "O3",
        "max_freshness_window_epochs": int(max_freshness_window_epochs),
        "critical": True,
    }
    return "sha256:" + hashlib.sha256(canonical_json_bytes(payload)).hexdigest()


_ZUSD_ORACLE_CONSUMER_PROFILE_IDS = {
    "mint": _oracle_consumer_profile_id(action_kind="mint", max_freshness_window_epochs=2),
    "liquidate_vault": _oracle_consumer_profile_id(
        action_kind="liquidate_vault",
        max_freshness_window_epochs=1,
    ),
}


def _operation_bound_args(operation: Mapping[str, Any]) -> dict[str, Any]:
    # DbC: authorization payloads are transport proofs, not business action facts.
    return {str(key): value for key, value in operation.items() if key != _ORACLE_AUTHORIZATION_FIELD}


def _oracle_action_kind(action: str) -> str:
    return _ZUSD_ORACLE_ADAPTER_ACTIONS.get(action, action)


def _oracle_runtime_value_e8(zusd_state: ZUSDMonetaryState, *, action: str, operation: Mapping[str, Any]) -> int | None:
    core = zusd_state.core
    if action == "mint_zusd":
        return int(core.price_e8) if int(core.price_e8) > 0 else None
    if action == "liquidate":
        return int(core.price_pending_e8) if int(core.price_pending_e8) > 0 else None
    return None


def _oracle_pre_state_hash(zusd_state: ZUSDMonetaryState) -> str:
    return semantic_hash("zenodex.zusd_monetary.pre_state.v1", {"state": zusd_monetary_state_to_obj(zusd_state)})


def _oracle_action_facts_hash(
    *,
    zusd_state: ZUSDMonetaryState,
    action: str,
    action_kind: str,
    operation: Mapping[str, Any],
    query_id: str,
    runtime_value_e8: int,
) -> str:
    core = zusd_state.core
    return semantic_hash(
        "zenodex.zusd_monetary.critical_action_facts.v1",
        {
            "action": action,
            "action_kind": action_kind,
            "operation": _operation_bound_args(operation),
            "now_epoch": int(core.now_epoch),
            "oracle_last_update_epoch": int(core.oracle_last_update_epoch),
            "price_e8": int(core.price_e8),
            "price_pending_e8": int(core.price_pending_e8),
            "query_id": query_id,
            "runtime_value_e8": int(runtime_value_e8),
            "vault_owner_pubkey": zusd_state.vault_owner_pubkey,
        },
    )


def _oracle_action_id(*, action_facts_hash: str, pre_state_hash: str, query_id: str, runtime_value_e8: int) -> str:
    return semantic_hash(
        "zenodex.zusd_monetary.action_id.v1",
        {
            "action_facts_hash": action_facts_hash,
            "pre_state_hash": pre_state_hash,
            "query_id": query_id,
            "runtime_value_e8": int(runtime_value_e8),
        },
    )


def _max_freshness_window_epochs_for_action(action_kind: str) -> int:
    if action_kind == "liquidate_vault":
        return 1
    return 2


def _oracle_profile_id_for_action(action_kind: str) -> str:
    return _ZUSD_ORACLE_CONSUMER_PROFILE_IDS.get(action_kind, "critical-zusd-v1")


def _oracle_runtime_facts(
    *,
    zusd_state: ZUSDMonetaryState,
    action: str,
    operation: Mapping[str, Any],
) -> RuntimeActionFacts | None:
    if action not in _ZUSD_ORACLE_AUTH_ACTIONS:
        return None
    runtime_value_e8 = _oracle_runtime_value_e8(zusd_state, action=action, operation=operation)
    if runtime_value_e8 is None:
        return None
    action_kind = _oracle_action_kind(action)
    query_id = _ORACLE_ZUSD_COLLATERAL_QUERY_ID
    pre_state_hash = _oracle_pre_state_hash(zusd_state)
    action_facts_hash = _oracle_action_facts_hash(
        zusd_state=zusd_state,
        action=action,
        action_kind=action_kind,
        operation=operation,
        query_id=query_id,
        runtime_value_e8=runtime_value_e8,
    )
    return RuntimeActionFacts(
        consumer_module="zenodex.zusd",
        action_kind=action_kind,
        action_id=_oracle_action_id(
            action_facts_hash=action_facts_hash,
            pre_state_hash=pre_state_hash,
            query_id=query_id,
            runtime_value_e8=runtime_value_e8,
        ),
        action_facts_hash=action_facts_hash,
        pre_state_hash=pre_state_hash,
        profile_id=_oracle_profile_id_for_action(action_kind),
        query_id=query_id,
        runtime_value_e8=int(runtime_value_e8),
        now_epoch=int(zusd_state.core.now_epoch),
        max_freshness_window_epochs=_max_freshness_window_epochs_for_action(action_kind),
    )


def _oracle_authorization_error(
    *,
    config: ZUSDMonetaryConfig,
    zusd_state: ZUSDMonetaryState,
    action: str,
    op: Mapping[str, Any],
) -> str | None:
    runtime = _oracle_runtime_facts(zusd_state=zusd_state, action=action, operation=op)
    if runtime is None:
        return None
    auth_obj = op.get(_ORACLE_AUTHORIZATION_FIELD)
    if auth_obj is None:
        return "oracle_authorization_required" if config.require_oracle_authorization else None
    if not isinstance(auth_obj, Mapping):
        return "oracle_authorization must be an object"
    try:
        result = check_critical_consumer_authorization(
            auth_obj,
            consumer_module=runtime.consumer_module,
            action_kind=runtime.action_kind,
            action_id=runtime.action_id,
            action_facts_hash=runtime.action_facts_hash,
            pre_state_hash=runtime.pre_state_hash,
            profile_id=runtime.profile_id,
            query_id=runtime.query_id,
            runtime_value_e8=runtime.runtime_value_e8,
            now_epoch=runtime.now_epoch,
            runtime_notional_value_e8=runtime.runtime_notional_value_e8,
            max_freshness_window_epochs=runtime.max_freshness_window_epochs,
            require_receipt_graph=True,
        )
    except Exception as exc:
        return f"oracle_authorization_rejected: {type(exc).__name__}: {exc}"
    if result.get("typed_ok") is True:
        return None
    errors = result.get("typed_errors")
    if isinstance(errors, list) and errors:
        detail = ",".join(str(error) for error in errors)
    else:
        detail = "typed authorization rejected"
    return f"oracle_authorization_rejected:{detail}"


def _require_str(value: Any, *, name: str, non_empty: bool = True, max_len: int = 4096) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a string")
    if non_empty and not value:
        raise ValueError(f"{name} must be non-empty")
    if max_len > 0 and len(value) > max_len:
        raise ValueError(f"{name} too large")
    return value


def _require_int(value: Any, *, name: str, minimum: int = 0, maximum: int | None = None) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValueError(f"{name} must be an int")
    out = int(value)
    if out < minimum:
        raise ValueError(f"{name} must be >= {minimum}")
    if maximum is not None and out > maximum:
        raise ValueError(f"{name} must be <= {maximum}")
    return out


def _require_nonnegative_int(value: Any, *, name: str) -> int:
    return _require_int(value, name=name, minimum=0)


def _raw_pubkey_key(value: Any) -> tuple[str, bool]:
    if not isinstance(value, str):
        return "", False
    raw = value.strip().lower()
    had_0x = raw.startswith("0x")
    return (raw[2:] if had_0x else raw), had_0x


def _native_sender_key(
    balances: BalanceTable,
    *,
    sender: str,
    raw_sender: str,
    sender_had_0x: bool,
) -> str:
    if raw_sender and raw_sender != sender and (not sender_had_0x or balances.get(raw_sender, NATIVE_ASSET) > 0):
        return raw_sender
    return sender


def _require_whole_zusd_amount(value: Any, *, name: str) -> int:
    amount = _require_int(value, name=name, minimum=1)
    if amount % E8 != 0:
        raise ValueError(f"{name} must be a whole zUSD amount in E8")
    return amount


def _e8_to_whole_units(amount_e8: int, *, name: str) -> int:
    amount = _require_whole_zusd_amount(amount_e8, name=name)
    return amount // E8


def _canonical_pubkey(value: Any, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a 48-byte hex pubkey string")
    return canonical_hex_fixed_allow_0x(value, nbytes=48, name=name)


def _canonical_asset(value: Any, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a 32-byte hex asset string")
    asset = canonical_hex_fixed_allow_0x(value, nbytes=32, name=name)
    if asset == NATIVE_ASSET:
        raise ValueError("zUSD asset cannot be native asset")
    return asset


def _copy_balance_table(balances: BalanceTable) -> BalanceTable:
    copied = BalanceTable()
    for (pubkey, asset), amount in balances.get_all_balances().items():
        copied.set(pubkey, asset, int(amount))
    return copied


def _copy_nonce_table(nonces: NonceTable) -> NonceTable:
    copied = NonceTable()
    for pk, last in nonces.get_all().items():
        copied.set_last(pk, int(last))
    return copied


def _parse_account_amount_entries(value: Any, *, name: str) -> dict[str, int]:
    if value is None:
        return {}
    if not isinstance(value, list):
        raise TypeError(f"{name} must be a list")
    out: dict[str, int] = {}
    for i, entry in enumerate(value):
        if not isinstance(entry, Mapping):
            raise TypeError(f"{name}[{i}] must be an object")
        _reject_unknown_fields(entry, allowed={"pubkey", "amount_e8"}, name=f"{name}[{i}]")
        pk = _canonical_pubkey(entry.get("pubkey"), name=f"{name}[{i}].pubkey")
        amount = _require_nonnegative_int(entry.get("amount_e8"), name=f"{name}[{i}].amount_e8")
        if amount == 0:
            continue
        if pk in out:
            raise ValueError(f"{name}[{i}] duplicate pubkey")
        out[pk] = int(amount)
    return out


def _reject_unknown_fields(obj: Mapping[str, Any], *, allowed: set[str], name: str) -> None:
    extra = sorted(set(obj.keys()) - set(allowed))
    if extra:
        raise ValueError(f"{name} unknown fields: {extra}")


def _deadline_error(*, op: Mapping[str, Any], block_timestamp: int, index: int) -> str | None:
    raw = op.get("deadline")
    if raw is None:
        return None
    deadline = _require_int(raw, name=f"zusd op[{index}].deadline", minimum=1, maximum=_U32_MAX)
    if int(block_timestamp) > int(deadline):
        return f"zusd op[{index}].deadline expired"
    return None


def _require_oracle_sender(config: ZUSDMonetaryConfig, *, sender: str) -> None:
    oracle = (config.oracle_pubkey or "").strip()
    if not oracle:
        raise ValueError("zUSD oracle signer not configured")
    if sender != _canonical_pubkey(oracle, name="oracle_pubkey"):
        raise ValueError("zUSD oracle action requires oracle sender")


def _sender_account(op: Mapping[str, Any], *, sender: str, action: str) -> str:
    account = _canonical_pubkey(op.get("account_pubkey", sender), name=f"{action}.account_pubkey")
    if account != sender:
        raise ValueError("account_pubkey mismatch")
    return account


def _set_or_drop(table: dict[str, int], key: str, value: int) -> dict[str, int]:
    out = dict(table)
    if value <= 0:
        out.pop(key, None)
    else:
        out[key] = int(value)
    return out


def _state_invariant_error(state: ZUSDMonetaryState) -> str | None:
    failed = check_invariants(state.core)
    if failed:
        return f"invariant violation: {','.join(failed)}"
    deposits = {pk: int(amount) for pk, amount in dict(state.sp_deposits_e8 or {}).items() if int(amount) > 0}
    claims = {pk: int(amount) for pk, amount in dict(state.sp_collateral_claims_e8 or {}).items() if int(amount) > 0}
    if sum(deposits.values()) != int(state.core.sp_debt_e8):
        return "stability pool account deposits do not match core sp_debt_e8"
    if sum(claims.values()) > int(state.core.sp_coll_e8):
        return "stability pool collateral claims exceed core sp_coll_e8"
    if state.vault_owner_pubkey is None and (state.core.collateral_e8 > 0 or state.core.debt_e8 > 0):
        return "non-empty vault requires vault_owner_pubkey"
    return None


def _raise_if_bad_state(state: ZUSDMonetaryState) -> None:
    err = _state_invariant_error(state)
    if err is not None:
        raise ValueError(err)


def _assert_sp_escrow_matches(
    balances: BalanceTable,
    state: ZUSDMonetaryState,
    *,
    zusd_asset: str,
    sp_pubkey: str,
) -> None:
    expected = _e8_to_whole_units(int(state.core.sp_debt_e8), name="sp_debt_e8") if state.core.sp_debt_e8 else 0
    actual = int(balances.get(sp_pubkey, zusd_asset))
    if actual != expected:
        raise ValueError(f"stability pool escrow mismatch (expected {expected}, got {actual})")


def _allocate_liquidation(
    deposits: Mapping[str, int],
    *,
    debt_e8: int,
    collateral_e8: int,
) -> tuple[dict[str, int], dict[str, int]]:
    total = sum(int(v) for v in deposits.values())
    if total <= 0:
        raise ValueError("stability pool has no account deposits")
    if debt_e8 > total:
        raise ValueError("liquidation debt exceeds account deposits")

    rows = [(pk, int(amount)) for pk, amount in sorted(deposits.items()) if int(amount) > 0]
    debt_losses: dict[str, int] = {}
    coll_gains: dict[str, int] = {}
    assigned_debt = 0
    assigned_coll = 0
    for pk, amount in rows:
        loss = (debt_e8 * amount) // total
        gain = (collateral_e8 * amount) // total if collateral_e8 > 0 else 0
        debt_losses[pk] = int(loss)
        coll_gains[pk] = int(gain)
        assigned_debt += int(loss)
        assigned_coll += int(gain)

    debt_rem = int(debt_e8) - assigned_debt
    for pk, _amount in sorted(rows, key=lambda item: (-item[1], item[0])):
        if debt_rem <= 0:
            break
        available = int(deposits[pk]) - int(debt_losses.get(pk, 0))
        if available <= 0:
            continue
        take = min(available, debt_rem)
        debt_losses[pk] = int(debt_losses.get(pk, 0)) + take
        debt_rem -= take
    if debt_rem != 0:
        raise ValueError("failed to allocate liquidation debt exactly")

    coll_rem = int(collateral_e8) - assigned_coll
    for pk, _amount in sorted(rows, key=lambda item: (-item[1], item[0])):
        if coll_rem <= 0:
            break
        coll_gains[pk] = int(coll_gains.get(pk, 0)) + 1
        coll_rem -= 1
    if coll_rem != 0:
        raise ValueError("failed to allocate liquidation collateral exactly")

    next_deposits: dict[str, int] = {}
    for pk, amount in rows:
        remaining = amount - int(debt_losses.get(pk, 0))
        if remaining > 0:
            next_deposits[pk] = int(remaining)
    coll_gains = {pk: int(amount) for pk, amount in coll_gains.items() if int(amount) > 0}
    return next_deposits, coll_gains


def _safe_error_str(exc: Exception) -> str:
    if isinstance(exc, (ValueError, TypeError, KeyError)):
        msg = str(exc)
    else:
        msg = f"internal error: {type(exc).__name__}"
    msg = " ".join((msg or "").split())
    if not msg:
        msg = "internal error"
    if len(msg) > 512:
        msg = msg[:512]
    return msg
