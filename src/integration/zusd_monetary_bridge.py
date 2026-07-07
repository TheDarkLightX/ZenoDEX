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
from typing import Any, Mapping, Optional

from ..core.dex import DexState
from ..core.perps import (
    PerpClearinghouse2pMarketState,
    PerpClearinghouse3pTransferMarketState,
    PerpClearinghouseNpMarketState,
    PerpMarketState,
)
from ..core.zusd import BPS_SCALE, E8, ZUSDCommand, ZUSDState, check_invariants, init_state, step
from ..state.balances import NATIVE_ASSET, BalanceTable
from ..state.canonical import bounded_json_utf8_size, canonical_hex_fixed_allow_0x
from ..state.nonces import NonceTable
from .zusd_tau_token import derive_zusd_tau_asset_id

ZUSD_MONETARY_SCHEMA = "zenodex/zusd_monetary_state/v1"
ZUSD_MONETARY_MODULE = "ZUSDFinance"
ZUSD_MONETARY_VERSION = "0.1"

_U32_MAX = 0xFFFFFFFF
_MAX_OPS = 128
_MAX_OP_BYTES = 64_000
_MAX_TOTAL_OPS_BYTES = 512_000
_FEE_ACC_SCALE = 1_000_000


@dataclass(frozen=True)
class ZUSDMonetaryConfig:
    chain_id: str = "tau-local"
    oracle_pubkey: Optional[str] = None
    asset_id: Optional[str] = None
    liquidation_gas_comp_fixed_collateral_e8: int = 0
    liquidation_gas_comp_bps: int = 0
    borrow_fee_floor_bps: int = 0
    borrow_fee_max_bps: int = 1_000
    host_protocol_fee_share_bps: int = 0
    fee_stake_asset_id: Optional[str] = None
    staking_activation_delay_epochs: int = 1

    def __post_init__(self) -> None:
        _require_int(self.borrow_fee_floor_bps, name="borrow_fee_floor_bps", minimum=0, maximum=BPS_SCALE)
        _require_int(self.borrow_fee_max_bps, name="borrow_fee_max_bps", minimum=0, maximum=BPS_SCALE)
        if int(self.borrow_fee_floor_bps) > int(self.borrow_fee_max_bps):
            raise ValueError("borrow_fee bps bounds invalid")
        _require_int(
            self.host_protocol_fee_share_bps,
            name="host_protocol_fee_share_bps",
            minimum=0,
            maximum=BPS_SCALE,
        )
        _require_nonnegative_int(self.staking_activation_delay_epochs, name="staking_activation_delay_epochs")
        if self.fee_stake_asset_id is not None:
            _canonical_asset(self.fee_stake_asset_id, name="fee_stake_asset_id")

    @property
    def zusd_asset(self) -> str:
        if self.asset_id is not None:
            return _canonical_asset(self.asset_id, name="asset_id")
        return derive_zusd_tau_asset_id(chain_id=self.chain_id)

    @property
    def fee_stake_asset(self) -> str | None:
        if self.fee_stake_asset_id is None:
            return None
        return _canonical_asset(self.fee_stake_asset_id, name="fee_stake_asset_id")


@dataclass(frozen=True)
class ZUSDMonetaryState:
    core: ZUSDState
    vault_owner_pubkey: Optional[str] = None
    sp_deposits_e8: Mapping[str, int] | None = None
    sp_collateral_claims_e8: Mapping[str, int] | None = None
    protocol_zusd_fee_reserve_e8: int = 0
    staking_zusd_fee_pool_e8: int = 0
    staking_zusd_fee_acc_per_share_e8: int = 0
    host_zusd_fee_pool_e8: int = 0
    host_zusd_fee_cum_e8: int = 0
    host_zusd_fees_e8: Mapping[str, int] | None = None
    active_fee_stakes: Mapping[str, int] | None = None
    pending_fee_stakes: Mapping[str, int] | None = None
    pending_fee_stake_activation_epochs: Mapping[str, int] | None = None
    fee_stake_reward_debt_e8: Mapping[str, int] | None = None

    def __post_init__(self) -> None:
        if self.vault_owner_pubkey is not None:
            _canonical_pubkey(self.vault_owner_pubkey, name="vault_owner_pubkey")
        deposits = dict(self.sp_deposits_e8 or {})
        claims = dict(self.sp_collateral_claims_e8 or {})
        host_fees = dict(self.host_zusd_fees_e8 or {})
        active_stakes = dict(self.active_fee_stakes or {})
        pending_stakes = dict(self.pending_fee_stakes or {})
        pending_epochs = dict(self.pending_fee_stake_activation_epochs or {})
        reward_debt = dict(self.fee_stake_reward_debt_e8 or {})
        for field_name in (
            "protocol_zusd_fee_reserve_e8",
            "staking_zusd_fee_pool_e8",
            "staking_zusd_fee_acc_per_share_e8",
            "host_zusd_fee_pool_e8",
            "host_zusd_fee_cum_e8",
        ):
            _require_nonnegative_int(getattr(self, field_name), name=field_name)
        for table_name, table in (
            ("sp_deposits_e8", deposits),
            ("sp_collateral_claims_e8", claims),
            ("host_zusd_fees_e8", host_fees),
            ("active_fee_stakes", active_stakes),
            ("pending_fee_stakes", pending_stakes),
            ("fee_stake_reward_debt_e8", reward_debt),
        ):
            for pk, amount in table.items():
                _canonical_pubkey(pk, name=f"{table_name}.pubkey")
                _require_nonnegative_int(amount, name=f"{table_name}[{pk}]")
        for pk, epoch in pending_epochs.items():
            _canonical_pubkey(pk, name="pending_fee_stake_activation_epochs.pubkey")
            _require_nonnegative_int(epoch, name=f"pending_fee_stake_activation_epochs[{pk}]")
        if set(pending_epochs) != set(pending_stakes):
            raise ValueError("pending fee stake activation keys mismatch")
        object.__setattr__(self, "sp_deposits_e8", deposits)
        object.__setattr__(self, "sp_collateral_claims_e8", claims)
        object.__setattr__(self, "host_zusd_fees_e8", {pk: amount for pk, amount in host_fees.items() if amount > 0})
        object.__setattr__(self, "active_fee_stakes", {pk: amount for pk, amount in active_stakes.items() if amount > 0})
        object.__setattr__(self, "pending_fee_stakes", {pk: amount for pk, amount in pending_stakes.items() if amount > 0})
        object.__setattr__(self, "pending_fee_stake_activation_epochs", pending_epochs)
        object.__setattr__(
            self,
            "fee_stake_reward_debt_e8",
            {pk: amount for pk, amount in reward_debt.items() if amount > 0},
        )


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
                "borrow_fee_floor_bps": _require_int(
                    config.borrow_fee_floor_bps,
                    name="borrow_fee_floor_bps",
                    minimum=0,
                    maximum=BPS_SCALE,
                ),
                "borrow_fee_max_bps": _require_int(
                    config.borrow_fee_max_bps,
                    name="borrow_fee_max_bps",
                    minimum=0,
                    maximum=BPS_SCALE,
                ),
            }
        )
    return ZUSDMonetaryState(
        core=core,
        sp_deposits_e8={},
        sp_collateral_claims_e8={},
        host_zusd_fees_e8={},
        active_fee_stakes={},
        pending_fee_stakes={},
        pending_fee_stake_activation_epochs={},
        fee_stake_reward_debt_e8={},
    )


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
    host_fees = _account_amount_entries(state.host_zusd_fees_e8, amount_key="amount_e8")
    active_stakes = _account_amount_entries(state.active_fee_stakes, amount_key="amount")
    pending_stakes = [
        {
            "pubkey": pk,
            "amount": int(amount),
            "activation_epoch": int(dict(state.pending_fee_stake_activation_epochs or {}).get(pk, 0)),
        }
        for pk, amount in sorted(dict(state.pending_fee_stakes or {}).items())
        if int(amount) > 0
    ]
    reward_debt = _account_amount_entries(state.fee_stake_reward_debt_e8, amount_key="amount_e8")
    return {
        "schema": ZUSD_MONETARY_SCHEMA,
        "version": 1,
        "core": dict(state.core.__dict__),
        "vault_owner_pubkey": state.vault_owner_pubkey,
        "sp_deposits": deposits,
        "sp_collateral_claims": claims,
        "protocol_zusd_fee_reserve_e8": int(state.protocol_zusd_fee_reserve_e8),
        "staking_zusd_fee_pool_e8": int(state.staking_zusd_fee_pool_e8),
        "staking_zusd_fee_acc_per_share_e8": int(state.staking_zusd_fee_acc_per_share_e8),
        "host_zusd_fee_pool_e8": int(state.host_zusd_fee_pool_e8),
        "host_zusd_fee_cum_e8": int(state.host_zusd_fee_cum_e8),
        "host_zusd_fees": host_fees,
        "active_fee_stakes": active_stakes,
        "pending_fee_stakes": pending_stakes,
        "fee_stake_reward_debt": reward_debt,
    }


def zusd_monetary_state_from_obj(obj: Mapping[str, Any]) -> ZUSDMonetaryState:
    if not isinstance(obj, Mapping):
        raise TypeError("zusd_monetary must be an object")
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
    pending_stakes, pending_epochs = _parse_pending_fee_stake_entries(obj.get("pending_fee_stakes"))
    state = ZUSDMonetaryState(
        core=core,
        vault_owner_pubkey=owner,
        sp_deposits_e8=deposits,
        sp_collateral_claims_e8=claims,
        protocol_zusd_fee_reserve_e8=_require_nonnegative_int(
            obj.get("protocol_zusd_fee_reserve_e8", 0),
            name="zusd_monetary.protocol_zusd_fee_reserve_e8",
        ),
        staking_zusd_fee_pool_e8=_require_nonnegative_int(
            obj.get("staking_zusd_fee_pool_e8", 0),
            name="zusd_monetary.staking_zusd_fee_pool_e8",
        ),
        staking_zusd_fee_acc_per_share_e8=_require_nonnegative_int(
            obj.get("staking_zusd_fee_acc_per_share_e8", 0),
            name="zusd_monetary.staking_zusd_fee_acc_per_share_e8",
        ),
        host_zusd_fee_pool_e8=_require_nonnegative_int(
            obj.get("host_zusd_fee_pool_e8", 0),
            name="zusd_monetary.host_zusd_fee_pool_e8",
        ),
        host_zusd_fee_cum_e8=_require_nonnegative_int(
            obj.get("host_zusd_fee_cum_e8", 0),
            name="zusd_monetary.host_zusd_fee_cum_e8",
        ),
        host_zusd_fees_e8=_parse_account_amount_entries(
            obj.get("host_zusd_fees"),
            name="zusd_monetary.host_zusd_fees",
        ),
        active_fee_stakes=_parse_account_amount_entries(
            obj.get("active_fee_stakes"),
            name="zusd_monetary.active_fee_stakes",
            amount_key="amount",
        ),
        pending_fee_stakes=pending_stakes,
        pending_fee_stake_activation_epochs=pending_epochs,
        fee_stake_reward_debt_e8=_parse_account_amount_entries(
            obj.get("fee_stake_reward_debt"),
            name="zusd_monetary.fee_stake_reward_debt",
        ),
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
        perps_zusd_liability_e8 = _perps_quote_liability_e8(state, zusd_asset=zusd_asset)
        native_sender = _native_sender_key(
            balances,
            sender=sender,
            raw_sender=raw_sender,
            sender_had_0x=sender_had_0x,
        )

        _assert_sp_escrow_matches(balances, working, zusd_asset=zusd_asset, sp_pubkey=sp_pubkey)
        _assert_free_debt_liability_cover(
            balances,
            working,
            zusd_asset=zusd_asset,
            sp_pubkey=sp_pubkey,
            perps_zusd_liability_e8=perps_zusd_liability_e8,
        )

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
            _assert_free_debt_liability_cover(
                balances,
                working,
                zusd_asset=zusd_asset,
                sp_pubkey=sp_pubkey,
                perps_zusd_liability_e8=perps_zusd_liability_e8,
            )

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
    fee_fields = _fee_state_fields(monetary_state)

    if action in {"bootstrap_oracle", "oracle_report", "oracle_commit"}:
        _require_oracle_sender(config, sender=sender)
        args: dict[str, Any] = {"auth_ok": True}
        if action in {"bootstrap_oracle", "oracle_report"}:
            args["price_e8"] = _require_int(op.get("price_e8"), name=f"{action}.price_e8", minimum=1)
        result = step(core, ZUSDCommand(tag=action, args=args))
        if not result.ok or result.state is None:
            raise ValueError(result.error or f"{action} rejected")
        next_state = ZUSDMonetaryState(
            core=result.state,
            vault_owner_pubkey=owner,
            sp_deposits_e8=deposits,
            sp_collateral_claims_e8=claims,
            **fee_fields,
        )
        _raise_if_bad_state(next_state)
        return next_state, dict(result.effects or {})

    if action == "advance_epoch":
        delta = _require_int(op.get("delta"), name="advance_epoch.delta", minimum=1)
        result = step(core, ZUSDCommand(tag=action, args={"delta": delta}))
        if not result.ok or result.state is None:
            raise ValueError(result.error or "advance_epoch rejected")
        fee_fields = _activate_ready_fee_stakes(fee_fields, now_epoch=int(result.state.now_epoch))
        next_state = ZUSDMonetaryState(
            core=result.state,
            vault_owner_pubkey=owner,
            sp_deposits_e8=deposits,
            sp_collateral_claims_e8=claims,
            **fee_fields,
        )
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
        next_state = ZUSDMonetaryState(
            core=result.state,
            vault_owner_pubkey=owner,
            sp_deposits_e8=deposits,
            sp_collateral_claims_e8=claims,
            **fee_fields,
        )
        _raise_if_bad_state(next_state)
        return next_state, {**dict(result.effects or {}), "native_balance_delta_e8": -amount_e8}

    if action == "withdraw_collateral":
        amount_e8 = _require_int(op.get("amount_e8"), name="withdraw_collateral.amount_e8", minimum=1)
        result = step(core, ZUSDCommand(tag=action, args={"amount_e8": amount_e8}))
        if not result.ok or result.state is None:
            raise ValueError(result.error or "withdraw_collateral rejected")
        balances.add(native_sender, NATIVE_ASSET, amount_e8)
        next_state = ZUSDMonetaryState(
            core=result.state,
            vault_owner_pubkey=owner,
            sp_deposits_e8=deposits,
            sp_collateral_claims_e8=claims,
            **fee_fields,
        )
        _raise_if_bad_state(next_state)
        return next_state, {**dict(result.effects or {}), "native_balance_delta_e8": amount_e8}

    if action == "mint_zusd":
        amount_e8 = _require_whole_zusd_amount(op.get("amount_e8"), name="mint_zusd.amount_e8")
        result = step(core, ZUSDCommand(tag=action, args={"amount_e8": amount_e8}))
        if not result.ok or result.state is None:
            raise ValueError(result.error or "mint_zusd rejected")
        effects = dict(result.effects or {})
        minted_units = _e8_to_whole_units(int(effects.get("principal_e8", amount_e8)), name="mint_zusd.principal_e8")
        balances.add(sender, zusd_asset, minted_units)
        fee_fields, fee_effects = _route_mint_fee(
            config=config,
            fee_fields=fee_fields,
            mint_fee_e8=int(effects.get("mint_fee_e8", 0)),
            host_pubkey=op.get("host_pubkey"),
        )
        next_state = ZUSDMonetaryState(
            core=result.state,
            vault_owner_pubkey=owner,
            sp_deposits_e8=deposits,
            sp_collateral_claims_e8=claims,
            **fee_fields,
        )
        _raise_if_bad_state(next_state)
        return next_state, {**effects, **fee_effects, "zusd_balance_delta": minted_units}

    if action == "repay_zusd":
        amount_e8 = _require_whole_zusd_amount(op.get("amount_e8"), name="repay_zusd.amount_e8")
        units = _e8_to_whole_units(amount_e8, name="repay_zusd.amount_e8")
        if balances.get(sender, zusd_asset) < units:
            raise ValueError("insufficient zUSD balance")
        result = step(core, ZUSDCommand(tag=action, args={"amount_e8": amount_e8}))
        if not result.ok or result.state is None:
            raise ValueError(result.error or "repay_zusd rejected")
        balances.subtract(sender, zusd_asset, units)
        next_state = ZUSDMonetaryState(
            core=result.state,
            vault_owner_pubkey=owner,
            sp_deposits_e8=deposits,
            sp_collateral_claims_e8=claims,
            **fee_fields,
        )
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
        next_state = ZUSDMonetaryState(
            core=result.state,
            vault_owner_pubkey=owner,
            sp_deposits_e8=deposits,
            sp_collateral_claims_e8=claims,
            **fee_fields,
        )
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
        next_state = ZUSDMonetaryState(
            core=result.state,
            vault_owner_pubkey=owner,
            sp_deposits_e8=deposits,
            sp_collateral_claims_e8=claims,
            **fee_fields,
        )
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
        next_state = ZUSDMonetaryState(
            core=result.state,
            vault_owner_pubkey=owner,
            sp_deposits_e8=deposits,
            sp_collateral_claims_e8=claims,
            **fee_fields,
        )
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
        next_state = ZUSDMonetaryState(
            core=result.state,
            vault_owner_pubkey=owner,
            sp_deposits_e8=deposits,
            sp_collateral_claims_e8=claims,
            **fee_fields,
        )
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
        next_state = ZUSDMonetaryState(
            core=next_core,
            vault_owner_pubkey=owner,
            sp_deposits_e8=deposits,
            sp_collateral_claims_e8=claims,
            **fee_fields,
        )
        _raise_if_bad_state(next_state)
        return next_state, {"event": "sp_collateral_claimed", "amount_e8": amount_e8, "native_balance_delta_e8": amount_e8}

    if action == "stake_fee_shares":
        stake_asset = config.fee_stake_asset
        if stake_asset is None:
            raise ValueError("fee staking asset not configured")
        amount = _require_int(op.get("amount"), name="stake_fee_shares.amount", minimum=1)
        if balances.get(sender, stake_asset) < amount:
            raise ValueError("insufficient fee stake balance")
        balances.subtract(sender, stake_asset, amount)
        pending = dict(fee_fields["pending_fee_stakes"])
        pending_epochs = dict(fee_fields["pending_fee_stake_activation_epochs"])
        activation_epoch = int(core.now_epoch) + int(config.staking_activation_delay_epochs)
        pending[sender] = int(pending.get(sender, 0)) + amount
        pending_epochs[sender] = max(int(pending_epochs.get(sender, 0)), activation_epoch)
        fee_fields = {**fee_fields, "pending_fee_stakes": pending, "pending_fee_stake_activation_epochs": pending_epochs}
        next_state = ZUSDMonetaryState(
            core=core,
            vault_owner_pubkey=owner,
            sp_deposits_e8=deposits,
            sp_collateral_claims_e8=claims,
            **fee_fields,
        )
        _raise_if_bad_state(next_state)
        return next_state, {
            "event": "fee_shares_staked_pending",
            "amount": amount,
            "activation_epoch": activation_epoch,
        }

    if action == "unstake_fee_shares":
        stake_asset = config.fee_stake_asset
        if stake_asset is None:
            raise ValueError("fee staking asset not configured")
        amount = _require_int(op.get("amount"), name="unstake_fee_shares.amount", minimum=1)
        active = dict(fee_fields["active_fee_stakes"])
        current = int(active.get(sender, 0))
        if amount > current:
            raise ValueError("unstake_fee_shares exceeds active stake")
        if _fee_stake_claimable_e8(fee_fields, sender) > 0:
            raise ValueError("claim staking fees before unstake")
        active = _set_or_drop(active, sender, current - amount)
        reward_debt = dict(fee_fields["fee_stake_reward_debt_e8"])
        if sender in active:
            reward_debt[sender] = _fee_stake_debt_for(active[sender], int(fee_fields["staking_zusd_fee_acc_per_share_e8"]))
        else:
            reward_debt.pop(sender, None)
        balances.add(sender, stake_asset, amount)
        fee_fields = {**fee_fields, "active_fee_stakes": active, "fee_stake_reward_debt_e8": reward_debt}
        next_state = ZUSDMonetaryState(
            core=core,
            vault_owner_pubkey=owner,
            sp_deposits_e8=deposits,
            sp_collateral_claims_e8=claims,
            **fee_fields,
        )
        _raise_if_bad_state(next_state)
        return next_state, {"event": "fee_shares_unstaked", "amount": amount}

    if action == "claim_host_fees":
        amount_e8 = _optional_whole_zusd_amount(op.get("amount_e8"), name="claim_host_fees.amount_e8")
        host_fees = dict(fee_fields["host_zusd_fees_e8"])
        current = int(host_fees.get(sender, 0))
        claim_e8 = current if amount_e8 is None else amount_e8
        if claim_e8 <= 0:
            raise ValueError("no host fees claimable")
        if claim_e8 > current:
            raise ValueError("claim_host_fees exceeds host claim")
        units = _e8_to_whole_units(claim_e8, name="claim_host_fees.amount_e8")
        balances.add(sender, zusd_asset, units)
        fee_fields = {
            **fee_fields,
            "host_zusd_fee_pool_e8": int(fee_fields["host_zusd_fee_pool_e8"]) - claim_e8,
            "host_zusd_fees_e8": _set_or_drop(host_fees, sender, current - claim_e8),
        }
        next_state = ZUSDMonetaryState(
            core=core,
            vault_owner_pubkey=owner,
            sp_deposits_e8=deposits,
            sp_collateral_claims_e8=claims,
            **fee_fields,
        )
        _raise_if_bad_state(next_state)
        return next_state, {"event": "host_zusd_fees_claimed", "amount_e8": claim_e8, "zusd_balance_delta": units}

    if action == "claim_staking_fees":
        claimable_e8 = _fee_stake_claimable_e8(fee_fields, sender)
        amount_e8 = _optional_whole_zusd_amount(op.get("amount_e8"), name="claim_staking_fees.amount_e8")
        claim_e8 = claimable_e8 if amount_e8 is None else amount_e8
        if claim_e8 <= 0:
            raise ValueError("no staking fees claimable")
        if claim_e8 > claimable_e8:
            raise ValueError("claim_staking_fees exceeds claimable fees")
        units = _e8_to_whole_units(claim_e8, name="claim_staking_fees.amount_e8")
        balances.add(sender, zusd_asset, units)
        reward_debt = dict(fee_fields["fee_stake_reward_debt_e8"])
        reward_debt[sender] = int(reward_debt.get(sender, 0)) + claim_e8
        fee_fields = {
            **fee_fields,
            "staking_zusd_fee_pool_e8": int(fee_fields["staking_zusd_fee_pool_e8"]) - claim_e8,
            "fee_stake_reward_debt_e8": reward_debt,
        }
        next_state = ZUSDMonetaryState(
            core=core,
            vault_owner_pubkey=owner,
            sp_deposits_e8=deposits,
            sp_collateral_claims_e8=claims,
            **fee_fields,
        )
        _raise_if_bad_state(next_state)
        return next_state, {"event": "staking_zusd_fees_claimed", "amount_e8": claim_e8, "zusd_balance_delta": units}

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
        "stake_fee_shares",
        "unstake_fee_shares",
        "claim_host_fees",
        "claim_staking_fees",
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
    if action == "mint_zusd":
        return base | {"owner_pubkey", "amount_e8", "host_pubkey"}
    if action in {"deposit_collateral", "withdraw_collateral", "repay_zusd"}:
        return base | {"owner_pubkey", "amount_e8"}
    if action in {"deposit_sp", "withdraw_sp", "redeem_zusd", "claim_sp_collateral"}:
        return base | {"account_pubkey", "amount_e8"}
    if action in {"stake_fee_shares", "unstake_fee_shares"}:
        return base | {"amount"}
    if action in {"claim_host_fees", "claim_staking_fees"}:
        return base | {"amount_e8"}
    if action == "liquidate":
        return base
    return base


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


def _optional_whole_zusd_amount(value: Any, *, name: str) -> int | None:
    if value is None:
        return None
    return _require_whole_zusd_amount(value, name=name)


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


def _account_amount_entries(value: Mapping[str, int] | None, *, amount_key: str) -> list[dict[str, Any]]:
    return [
        {"pubkey": pk, amount_key: int(amount)}
        for pk, amount in sorted(dict(value or {}).items())
        if int(amount) > 0
    ]


def _parse_account_amount_entries(value: Any, *, name: str, amount_key: str = "amount_e8") -> dict[str, int]:
    if value is None:
        return {}
    if not isinstance(value, list):
        raise TypeError(f"{name} must be a list")
    out: dict[str, int] = {}
    for i, entry in enumerate(value):
        if not isinstance(entry, Mapping):
            raise TypeError(f"{name}[{i}] must be an object")
        pk = _canonical_pubkey(entry.get("pubkey"), name=f"{name}[{i}].pubkey")
        amount = _require_nonnegative_int(entry.get(amount_key), name=f"{name}[{i}].{amount_key}")
        if amount == 0:
            continue
        if pk in out:
            raise ValueError(f"{name}[{i}] duplicate pubkey")
        out[pk] = int(amount)
    return out


def _parse_pending_fee_stake_entries(value: Any) -> tuple[dict[str, int], dict[str, int]]:
    if value is None:
        return {}, {}
    if not isinstance(value, list):
        raise TypeError("zusd_monetary.pending_fee_stakes must be a list")
    stakes: dict[str, int] = {}
    epochs: dict[str, int] = {}
    for i, entry in enumerate(value):
        if not isinstance(entry, Mapping):
            raise TypeError(f"zusd_monetary.pending_fee_stakes[{i}] must be an object")
        pk = _canonical_pubkey(entry.get("pubkey"), name=f"zusd_monetary.pending_fee_stakes[{i}].pubkey")
        amount = _require_nonnegative_int(
            entry.get("amount"),
            name=f"zusd_monetary.pending_fee_stakes[{i}].amount",
        )
        activation_epoch = _require_nonnegative_int(
            entry.get("activation_epoch"),
            name=f"zusd_monetary.pending_fee_stakes[{i}].activation_epoch",
        )
        if amount == 0:
            continue
        if pk in stakes:
            raise ValueError(f"zusd_monetary.pending_fee_stakes[{i}] duplicate pubkey")
        stakes[pk] = amount
        epochs[pk] = activation_epoch
    return stakes, epochs


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


def _fee_state_fields(state: ZUSDMonetaryState) -> dict[str, Any]:
    return {
        "protocol_zusd_fee_reserve_e8": int(state.protocol_zusd_fee_reserve_e8),
        "staking_zusd_fee_pool_e8": int(state.staking_zusd_fee_pool_e8),
        "staking_zusd_fee_acc_per_share_e8": int(state.staking_zusd_fee_acc_per_share_e8),
        "host_zusd_fee_pool_e8": int(state.host_zusd_fee_pool_e8),
        "host_zusd_fee_cum_e8": int(state.host_zusd_fee_cum_e8),
        "host_zusd_fees_e8": dict(state.host_zusd_fees_e8 or {}),
        "active_fee_stakes": dict(state.active_fee_stakes or {}),
        "pending_fee_stakes": dict(state.pending_fee_stakes or {}),
        "pending_fee_stake_activation_epochs": dict(state.pending_fee_stake_activation_epochs or {}),
        "fee_stake_reward_debt_e8": dict(state.fee_stake_reward_debt_e8 or {}),
    }


def _fee_stake_debt_for(shares: int, acc_per_share_e8: int) -> int:
    return (int(shares) * int(acc_per_share_e8)) // _FEE_ACC_SCALE


def _fee_stake_claimable_e8(fee_fields: Mapping[str, Any], account: str) -> int:
    active = dict(fee_fields["active_fee_stakes"])
    reward_debt = dict(fee_fields["fee_stake_reward_debt_e8"])
    shares = int(active.get(account, 0))
    if shares <= 0:
        return 0
    accrued = _fee_stake_debt_for(shares, int(fee_fields["staking_zusd_fee_acc_per_share_e8"]))
    return max(0, accrued - int(reward_debt.get(account, 0)))


def _activate_ready_fee_stakes(fee_fields: Mapping[str, Any], *, now_epoch: int) -> dict[str, Any]:
    out = dict(fee_fields)
    active = dict(out["active_fee_stakes"])
    pending = dict(out["pending_fee_stakes"])
    pending_epochs = dict(out["pending_fee_stake_activation_epochs"])
    reward_debt = dict(out["fee_stake_reward_debt_e8"])
    acc = int(out["staking_zusd_fee_acc_per_share_e8"])
    for pk, amount in sorted(list(pending.items())):
        activation_epoch = int(pending_epochs.get(pk, 0))
        if activation_epoch > now_epoch:
            continue
        active[pk] = int(active.get(pk, 0)) + int(amount)
        reward_debt[pk] = int(reward_debt.get(pk, 0)) + _fee_stake_debt_for(int(amount), acc)
        pending.pop(pk, None)
        pending_epochs.pop(pk, None)
    out["active_fee_stakes"] = active
    out["pending_fee_stakes"] = pending
    out["pending_fee_stake_activation_epochs"] = pending_epochs
    out["fee_stake_reward_debt_e8"] = reward_debt
    return out


def _route_mint_fee(
    *,
    config: ZUSDMonetaryConfig,
    fee_fields: Mapping[str, Any],
    mint_fee_e8: int,
    host_pubkey: Any,
) -> tuple[dict[str, Any], dict[str, Any]]:
    fee_e8 = _require_nonnegative_int(mint_fee_e8, name="mint_fee_e8")
    out = dict(fee_fields)
    if fee_e8 == 0:
        return out, {"mint_fee_host_e8": 0, "mint_fee_staking_e8": 0, "mint_fee_protocol_e8": 0}

    host_fee_e8 = 0
    host: str | None = None
    if host_pubkey is not None:
        host = _canonical_pubkey(host_pubkey, name="mint_zusd.host_pubkey")
        host_fee_e8 = (fee_e8 * int(config.host_protocol_fee_share_bps)) // BPS_SCALE
    non_host_fee_e8 = fee_e8 - host_fee_e8

    if host is not None and host_fee_e8 > 0:
        host_fees = dict(out["host_zusd_fees_e8"])
        host_fees[host] = int(host_fees.get(host, 0)) + host_fee_e8
        out["host_zusd_fees_e8"] = host_fees
        out["host_zusd_fee_pool_e8"] = int(out["host_zusd_fee_pool_e8"]) + host_fee_e8
        out["host_zusd_fee_cum_e8"] = int(out["host_zusd_fee_cum_e8"]) + host_fee_e8

    active_total = sum(int(v) for v in dict(out["active_fee_stakes"]).values())
    staking_fee_e8 = 0
    protocol_fee_e8 = 0
    if active_total > 0 and non_host_fee_e8 > 0:
        staking_fee_e8 = non_host_fee_e8
        out["staking_zusd_fee_pool_e8"] = int(out["staking_zusd_fee_pool_e8"]) + staking_fee_e8
        out["staking_zusd_fee_acc_per_share_e8"] = int(out["staking_zusd_fee_acc_per_share_e8"]) + (
            staking_fee_e8 * _FEE_ACC_SCALE
        ) // active_total
    else:
        protocol_fee_e8 = non_host_fee_e8
        out["protocol_zusd_fee_reserve_e8"] = int(out["protocol_zusd_fee_reserve_e8"]) + protocol_fee_e8

    return out, {
        "mint_fee_host_e8": host_fee_e8,
        "mint_fee_staking_e8": staking_fee_e8,
        "mint_fee_protocol_e8": protocol_fee_e8,
    }


def _state_invariant_error(state: ZUSDMonetaryState) -> str | None:
    failed = check_invariants(state.core)
    if failed:
        return f"invariant violation: {','.join(failed)}"
    deposits = {pk: int(amount) for pk, amount in dict(state.sp_deposits_e8 or {}).items() if int(amount) > 0}
    claims = {pk: int(amount) for pk, amount in dict(state.sp_collateral_claims_e8 or {}).items() if int(amount) > 0}
    host_fees = {pk: int(amount) for pk, amount in dict(state.host_zusd_fees_e8 or {}).items() if int(amount) > 0}
    active_stakes = {pk: int(amount) for pk, amount in dict(state.active_fee_stakes or {}).items() if int(amount) > 0}
    pending_stakes = {pk: int(amount) for pk, amount in dict(state.pending_fee_stakes or {}).items() if int(amount) > 0}
    pending_epochs = dict(state.pending_fee_stake_activation_epochs or {})
    if sum(deposits.values()) != int(state.core.sp_debt_e8):
        return "stability pool account deposits do not match core sp_debt_e8"
    if sum(claims.values()) > int(state.core.sp_coll_e8):
        return "stability pool collateral claims exceed core sp_coll_e8"
    if sum(host_fees.values()) != int(state.host_zusd_fee_pool_e8):
        return "host zUSD fee claims do not match host_zusd_fee_pool_e8"
    if int(state.host_zusd_fee_pool_e8) > int(state.host_zusd_fee_cum_e8):
        return "host_zusd_fee_pool_e8 exceeds host_zusd_fee_cum_e8"
    if set(pending_epochs) != set(pending_stakes):
        return "pending fee stake activation keys mismatch"
    fee_fields = _fee_state_fields(state)
    total_claimable = sum(_fee_stake_claimable_e8(fee_fields, pk) for pk in active_stakes)
    if total_claimable > int(state.staking_zusd_fee_pool_e8):
        return "staking zUSD fee claimables exceed staking_zusd_fee_pool_e8"
    if state.vault_owner_pubkey is None and (state.core.collateral_e8 > 0 or state.core.debt_e8 > 0):
        return "non-empty vault requires vault_owner_pubkey"
    return None


def _raise_if_bad_state(state: ZUSDMonetaryState) -> None:
    err = _state_invariant_error(state)
    if err is not None:
        raise ValueError(err)


def _perps_quote_liability_e8(state: DexState, *, zusd_asset: str) -> int:
    perps = state.perps
    if perps is None:
        return 0

    total = 0
    for market in perps.markets.values():
        if market.quote_asset != zusd_asset:
            continue
        if isinstance(market, PerpMarketState):
            total += sum(int(account.collateral_quote) for account in market.accounts.values()) * E8
            total += int(market.global_state.get("fee_pool_quote", 0)) * E8
            total += int(market.global_state.get("insurance_balance", 0)) * E8
        elif isinstance(market, (PerpClearinghouse2pMarketState, PerpClearinghouse3pTransferMarketState)):
            total += int(market.state.get("net_deposited_e8", 0))
        elif isinstance(market, PerpClearinghouseNpMarketState):
            total += int(market.global_state.get("net_deposited_e8", 0))
            total += int(market.global_state.get("insurance_ext_e8", 0))
    return total


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


def _assert_free_debt_liability_cover(
    balances: BalanceTable,
    state: ZUSDMonetaryState,
    *,
    zusd_asset: str,
    sp_pubkey: str,
    perps_zusd_liability_e8: int,
) -> None:
    external_free_e8 = 0
    for (pubkey, asset), amount in balances.get_all_balances().items():
        if asset == zusd_asset and pubkey != sp_pubkey:
            external_free_e8 += int(amount) * E8
    internal_liabilities_e8 = (
        int(state.protocol_zusd_fee_reserve_e8)
        + int(state.staking_zusd_fee_pool_e8)
        + int(state.host_zusd_fee_pool_e8)
    )
    expected = external_free_e8 + perps_zusd_liability_e8 + internal_liabilities_e8
    actual = int(state.core.free_debt_e8)
    if actual != expected:
        raise ValueError(f"free debt liability cover mismatch (expected {expected}, got {actual})")


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
