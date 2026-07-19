"""
DEX state snapshot encoding for Tau Net integration.

Goals:
- Deterministic JSON serialization for hashing / snapshot distribution.
- Round-trippable into the functional-core `DexState` types.
- Explicit versioning for future proof-carrying formats.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from typing import Any, Dict, Mapping, Optional

from ..core.dex import DexState
from ..core.fees import FeeAccumulatorState
from ..core.oracle import OracleState
from ..core.perps import (
    PERP_MARKET_KIND_CLEARINGHOUSE_2P_V1,
    PERP_MARKET_KIND_CLEARINGHOUSE_3P_TRANSFER_V1,
    PERP_MARKET_KIND_ISOLATED_V2,
    PERPS_STATE_VERSION_V5,
    PerpAccountState,
    PerpAnyMarketState,
    PerpClearinghouse2pMarketState,
    PerpClearinghouse3pTransferMarketState,
    PerpMarketState,
    PerpsState,
    _infer_epoch_phase,
)
from ..core.vault import VaultState
from ..state.balances import BalanceTable
from ..state.canonical import (
    bounded_json_utf8_size,
    canonical_hex_fixed_allow_0x,
    canonical_json_bytes,
    domain_sep_bytes,
    sha256_hex,
)
from ..state.lp import LPTable
from ..state.nonces import NonceTable
from ..state.pools import PoolState, PoolStatus

DEX_SNAPSHOT_VERSION = 4


def _require_str(value: Any, *, name: str, non_empty: bool = True, max_len: int = 4096) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a string")
    if non_empty and not value:
        raise ValueError(f"{name} must be non-empty")
    if max_len > 0 and len(value) > max_len:
        raise ValueError(f"{name} too large")
    return value


def _require_int(value: Any, *, name: str, non_negative: bool = True) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    if non_negative and value < 0:
        raise ValueError(f"{name} must be non-negative")
    return int(value)


def _require_bool(value: Any, *, name: str) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be a bool")
    return bool(value)


@dataclass(frozen=True)
class DexSnapshot:
    """
    Deterministic, versioned snapshot of `DexState`.

    The commitment is *not* included inside `data` to avoid self-reference.
    """

    version: int
    data: Dict[str, Any]

    def canonical_bytes(self) -> bytes:
        return canonical_json_bytes(self.data)

    def commitment_bytes(self) -> bytes:
        payload = domain_sep_bytes("dex_snapshot", version=self.version) + self.canonical_bytes()
        return hashlib.sha256(payload).digest()

    def commitment_hex(self) -> str:
        payload = domain_sep_bytes("dex_snapshot", version=self.version) + self.canonical_bytes()
        return sha256_hex(payload)


def snapshot_from_state(state: DexState, *, version: int = DEX_SNAPSHOT_VERSION) -> DexSnapshot:
    if not isinstance(version, int) or isinstance(version, bool) or version <= 0:
        raise ValueError("version must be a positive int")

    balances_entries = [
        {"pubkey": pk, "asset": asset, "amount": int(amount)}
        for (pk, asset), amount in state.balances.get_all_balances().items()
    ]
    balances_entries.sort(key=lambda e: (e["pubkey"], e["asset"]))

    pools_entries = []
    for pool_id, pool in state.pools.items():
        pools_entries.append(
            {
                "pool_id": pool_id,
                "asset0": pool.asset0,
                "asset1": pool.asset1,
                "reserve0": int(pool.reserve0),
                "reserve1": int(pool.reserve1),
                "fee_bps": int(pool.fee_bps),
                "lp_supply": int(pool.lp_supply),
                "status": pool.status.value,
                "created_at": int(pool.created_at),
                "curve_tag": pool.curve_tag,
                "curve_params": pool.curve_params,
            }
        )
    pools_entries.sort(key=lambda e: e["pool_id"])

    lp_entries = [
        {"pubkey": pk, "pool_id": pool_id, "amount": int(amount)}
        for (pk, pool_id), amount in state.lp_balances.get_all_balances().items()
    ]
    lp_entries.sort(key=lambda e: (e["pubkey"], e["pool_id"]))

    lp_mint_timestamp_entries = [
        {"pubkey": pk, "pool_id": pool_id, "last_mint_timestamp": int(timestamp)}
        for (pk, pool_id), timestamp in state.lp_balances.get_all_last_mint_timestamps().items()
    ]
    lp_mint_timestamp_entries.sort(key=lambda e: (e["pubkey"], e["pool_id"]))

    lp_duration_risk_entries = []
    for (pk, pool_id), metadata in state.lp_balances.get_all_duration_risk_metadata().items():
        lp_duration_risk_entries.append(
            {
                "pubkey": pk,
                "pool_id": pool_id,
                "last_remove_timestamp": metadata.last_remove_timestamp,
                "churn_tier": int(metadata.churn_tier),
                "last_churn_update_timestamp": metadata.last_churn_update_timestamp,
            }
        )
    lp_duration_risk_entries.sort(key=lambda e: (e["pubkey"], e["pool_id"]))

    nonce_entries = [{"pubkey": pk, "last_nonce": int(last)} for pk, last in state.nonces.get_all().items()]
    nonce_entries.sort(key=lambda e: e["pubkey"])

    fee_acc = state.fee_accumulator
    fee_acc_obj: Dict[str, Any] = {"dust": int(getattr(fee_acc, "dust", 0))}

    vault_obj: Optional[Dict[str, Any]] = None
    if state.vault is not None:
        v = state.vault
        vault_obj = {
            "acc_reward_per_share": int(v.acc_reward_per_share),
            "last_update_acc": int(v.last_update_acc),
            "pending_rewards": int(v.pending_rewards),
            "reward_balance": int(v.reward_balance),
            "staked_lp_shares": int(v.staked_lp_shares),
        }

    oracle_obj: Optional[Dict[str, Any]] = None
    if state.oracle is not None:
        o = state.oracle
        oracle_obj = {"price_timestamp": int(o.price_timestamp), "max_staleness_seconds": int(o.max_staleness_seconds)}

    perps_obj: Optional[Dict[str, Any]] = None
    if int(version) >= 2 and state.perps is not None:
        perps = state.perps
        markets_entries = []
        for market_id, market in perps.markets.items():
            if isinstance(market, PerpMarketState):
                acct_entries = []
                for pk, acct in market.accounts.items():
                    acct_entries.append(
                        {
                            "pubkey": str(pk),
                            "position_base": int(acct.position_base),
                            "entry_price_e8": int(acct.entry_price_e8),
                            "collateral_quote": int(acct.collateral_quote),
                            "funding_paid_cumulative": int(acct.funding_paid_cumulative),
                            "funding_last_applied_epoch": int(acct.funding_last_applied_epoch),
                            "liquidated_this_step": bool(acct.liquidated_this_step),
                        }
                    )
                acct_entries.sort(key=lambda e: str(e["pubkey"]))
                out_entry: Dict[str, Any] = {
                    "market_id": str(market_id),
                    "quote_asset": str(market.quote_asset),
                    "global_state": dict(market.global_state),
                    "accounts": acct_entries,
                }
                if int(perps.version) >= PERPS_STATE_VERSION_V5:
                    out_entry["kind"] = str(getattr(market, "kind", PERP_MARKET_KIND_ISOLATED_V2))
                    pending_roots = tuple(getattr(market, "pending_funding_closeout_root_hashes", ()))
                    if pending_roots:
                        out_entry["pending_funding_closeout_root_hashes"] = [str(root) for root in pending_roots]
                    pending_source_roots = tuple(
                        getattr(market, "pending_funding_closeout_source_availability_hashes", ())
                    )
                    if pending_source_roots:
                        out_entry["pending_funding_closeout_source_availability_hashes"] = [
                            str(root) for root in pending_source_roots
                        ]
                    pending_carried_roots = tuple(
                        getattr(market, "pending_funding_closeout_carried_liability_hashes", ())
                    )
                    if pending_carried_roots:
                        out_entry["pending_funding_closeout_carried_liability_hashes"] = [
                            str(root) for root in pending_carried_roots
                        ]
                    policy_ledger_roots = tuple(
                        getattr(market, "funding_closeout_policy_ledger_hashes", ())
                    )
                    if policy_ledger_roots:
                        out_entry["funding_closeout_policy_ledger_hashes"] = [
                            str(root) for root in policy_ledger_roots
                        ]
                    sink_claimant_balances = tuple(
                        getattr(
                            market,
                            "funding_closeout_sink_claimant_balances_quote",
                            (),
                        )
                    )
                    if sink_claimant_balances:
                        out_entry["funding_closeout_sink_claimant_balances_quote"] = [
                            {
                                "claimant": str(claimant),
                                "balance_quote": int(balance_quote),
                            }
                            for claimant, balance_quote in sink_claimant_balances
                        ]
                    receiver_claim_balances = tuple(
                        getattr(
                            market,
                            "funding_closeout_receiver_claim_balances_quote",
                            (),
                        )
                    )
                    if receiver_claim_balances:
                        out_entry["funding_closeout_receiver_claim_balances_quote"] = [
                            {
                                "account_pubkey": str(account_pubkey),
                                "balance_quote": int(balance_quote),
                            }
                            for account_pubkey, balance_quote in receiver_claim_balances
                        ]
                    receiver_claim_lots = tuple(
                        getattr(
                            market,
                            "funding_closeout_receiver_claim_lots_quote",
                            (),
                        )
                    )
                    if receiver_claim_lots:
                        out_entry["funding_closeout_receiver_claim_lots_quote"] = [
                            {
                                "account_pubkey": str(account_pubkey),
                                "lot_id": str(lot_id),
                                "balance_quote": int(balance_quote),
                                "expires_at_epoch": int(expires_at_epoch),
                            }
                            for (
                                account_pubkey,
                                lot_id,
                                balance_quote,
                                expires_at_epoch,
                            ) in receiver_claim_lots
                        ]
                markets_entries.append(out_entry)
                continue

            if isinstance(market, PerpClearinghouse2pMarketState):
                out_entry = {
                    "market_id": str(market_id),
                    "kind": str(getattr(market, "kind", PERP_MARKET_KIND_CLEARINGHOUSE_2P_V1)),
                    "quote_asset": str(market.quote_asset),
                    "account_a_pubkey": str(market.account_a_pubkey),
                    "account_b_pubkey": str(market.account_b_pubkey),
                    "state": dict(market.state),
                }
                markets_entries.append(out_entry)
                continue

            if isinstance(market, PerpClearinghouse3pTransferMarketState):
                out_entry = {
                    "market_id": str(market_id),
                    "kind": str(getattr(market, "kind", PERP_MARKET_KIND_CLEARINGHOUSE_3P_TRANSFER_V1)),
                    "quote_asset": str(market.quote_asset),
                    "account_a_pubkey": str(market.account_a_pubkey),
                    "account_b_pubkey": str(market.account_b_pubkey),
                    "account_c_pubkey": str(market.account_c_pubkey),
                    "state": dict(market.state),
                }
                markets_entries.append(out_entry)
                continue

            raise TypeError(f"unsupported perps market type: {type(market)}")
        markets_entries.sort(key=lambda e: e["market_id"])
        perps_obj = {"version": int(perps.version), "markets": markets_entries}

    data: Dict[str, Any] = {
        "version": int(version),
        "balances": balances_entries,
        "pools": pools_entries,
        "lp_balances": lp_entries,
        "lp_mint_timestamps": lp_mint_timestamp_entries,
        "lp_duration_risk": lp_duration_risk_entries,
        "nonces": nonce_entries,
        "fee_accumulator": fee_acc_obj,
        "vault": vault_obj,
        "oracle": oracle_obj,
    }
    if int(version) >= 2:
        data["perps"] = perps_obj
    return DexSnapshot(version=version, data=data)


def snapshot_with_legacy_lp_metadata_defaults(snapshot: Mapping[str, Any]) -> Dict[str, Any]:
    """Backfill optional LP metadata rails for legacy live app-state snapshots.

    ``state_from_snapshot`` remains strict for persisted snapshot artifacts:
    version 3+ snapshots must contain ``lp_mint_timestamps`` and version 4
    snapshots must contain ``lp_duration_risk``. Some live Tau app-state views
    predate those rails but are still used by non-LP surfaces such as perps and
    zUSD status. Those callers can use this boundary helper before parsing.
    """
    if not isinstance(snapshot, Mapping):
        raise TypeError("snapshot must be a mapping")
    normalized = dict(snapshot)
    version = normalized.get("version", DEX_SNAPSHOT_VERSION)
    if isinstance(version, int) and not isinstance(version, bool):
        if version >= 3 and "lp_mint_timestamps" not in normalized:
            normalized["lp_mint_timestamps"] = []
        if version >= 4 and "lp_duration_risk" not in normalized:
            normalized["lp_duration_risk"] = []
    return normalized


def state_from_snapshot(
    snapshot: Mapping[str, Any],
    *,
    max_snapshot_bytes: int = 4_000_000,
    max_balances: int = 200_000,
    max_pools: int = 50_000,
    max_lp_balances: int = 200_000,
    max_nonces: int = 200_000,
    max_perp_markets: int = 10_000,
    max_perp_accounts: int = 200_000,
    max_str_len: int = 4096,
    require_lp_mint_timestamps: bool = False,
) -> DexState:
    if not isinstance(snapshot, Mapping):
        raise TypeError("snapshot must be a mapping")
    if not isinstance(snapshot, dict):
        snapshot = dict(snapshot)

    for name, v in (
        ("max_snapshot_bytes", max_snapshot_bytes),
        ("max_balances", max_balances),
        ("max_pools", max_pools),
        ("max_lp_balances", max_lp_balances),
        ("max_nonces", max_nonces),
        ("max_perp_markets", max_perp_markets),
        ("max_perp_accounts", max_perp_accounts),
        ("max_str_len", max_str_len),
    ):
        if not isinstance(v, int) or isinstance(v, bool) or v <= 0:
            raise ValueError(f"{name} must be a positive int")

    try:
        bounded_json_utf8_size(snapshot, max_bytes=max_snapshot_bytes)
    except ValueError as exc:
        raise ValueError("snapshot too large") from exc

    version = snapshot.get("version", DEX_SNAPSHOT_VERSION)
    if not isinstance(version, int) or isinstance(version, bool) or version <= 0:
        raise ValueError("snapshot.version must be a positive int")
    if version not in (1, 2, 3, 4):
        raise ValueError(f"unsupported snapshot version: {version}")

    balances = BalanceTable()
    balances_entries = snapshot.get("balances")
    if balances_entries is None:
        balances_entries = []
    if not isinstance(balances_entries, list):
        raise TypeError("snapshot.balances must be a list")
    if len(balances_entries) > max_balances:
        raise ValueError(f"too many balances entries: {len(balances_entries)} > {max_balances}")
    seen_balances: set[tuple[str, str]] = set()
    for entry in balances_entries:
        if not isinstance(entry, Mapping):
            raise TypeError("snapshot.balances entries must be objects")
        pk = entry.get("pubkey")
        asset = entry.get("asset")
        amount = entry.get("amount")
        pk_s = _require_str(pk, name="balance.pubkey", non_empty=True, max_len=min(512, max_str_len))
        asset_s = _require_str(asset, name="balance.asset", non_empty=True, max_len=min(256, max_str_len))
        if not isinstance(amount, int) or isinstance(amount, bool) or amount < 0:
            raise ValueError("invalid balance entry (amount)")
        key = (pk_s, asset_s)
        if key in seen_balances:
            raise ValueError("duplicate balance entry (pubkey, asset)")
        seen_balances.add(key)
        balances.set(pk_s, asset_s, amount)

    pools: Dict[str, PoolState] = {}
    pools_entries = snapshot.get("pools")
    if pools_entries is None:
        pools_entries = []
    if not isinstance(pools_entries, list):
        raise TypeError("snapshot.pools must be a list")
    if len(pools_entries) > max_pools:
        raise ValueError(f"too many pools entries: {len(pools_entries)} > {max_pools}")
    for entry in pools_entries:
        if not isinstance(entry, Mapping):
            raise TypeError("snapshot.pools entries must be objects")
        pool_id = _require_str(entry.get("pool_id"), name="pool.pool_id", non_empty=True, max_len=min(256, max_str_len))
        if pool_id in pools:
            raise ValueError("duplicate pool entry (pool_id)")
        asset0 = entry.get("asset0")
        asset1 = entry.get("asset1")
        asset0_s = _require_str(asset0, name="pool.asset0", non_empty=True, max_len=min(256, max_str_len))
        asset1_s = _require_str(asset1, name="pool.asset1", non_empty=True, max_len=min(256, max_str_len))
        status_raw = entry.get("status", PoolStatus.ACTIVE.value)
        try:
            status = PoolStatus(str(status_raw))
        except ValueError as exc:
            raise ValueError(f"invalid pool status: {status_raw}") from exc
        fee_bps = _require_int(entry.get("fee_bps", 0), name="fee_bps")
        if fee_bps > 10_000:
            raise ValueError(f"fee_bps out of range for pool {pool_id}: {fee_bps}")
        pools[pool_id] = PoolState(
            pool_id=pool_id,
            asset0=asset0_s,
            asset1=asset1_s,
            reserve0=_require_int(entry.get("reserve0", 0), name="reserve0"),
            reserve1=_require_int(entry.get("reserve1", 0), name="reserve1"),
            fee_bps=fee_bps,
            lp_supply=_require_int(entry.get("lp_supply", 0), name="lp_supply"),
            status=status,
            created_at=_require_int(entry.get("created_at", 0), name="created_at"),
            curve_tag=_require_str(entry.get("curve_tag", "CPMM"), name="pool.curve_tag", non_empty=True, max_len=min(256, max_str_len)),
            curve_params=_require_str(entry.get("curve_params", ""), name="pool.curve_params", non_empty=False, max_len=min(max_snapshot_bytes, max_str_len)),
        )

    lp_balances = LPTable()
    lp_entries = snapshot.get("lp_balances")
    if lp_entries is None:
        lp_entries = []
    if not isinstance(lp_entries, list):
        raise TypeError("snapshot.lp_balances must be a list")
    if len(lp_entries) > max_lp_balances:
        raise ValueError(f"too many lp_balances entries: {len(lp_entries)} > {max_lp_balances}")
    seen_lp: set[tuple[str, str]] = set()
    for entry in lp_entries:
        if not isinstance(entry, Mapping):
            raise TypeError("snapshot.lp_balances entries must be objects")
        pk = entry.get("pubkey")
        pool_id_raw = entry.get("pool_id")
        amount = entry.get("amount")
        pk_s = _require_str(pk, name="lp.pubkey", non_empty=True, max_len=min(512, max_str_len))
        pool_id_s = _require_str(pool_id_raw, name="lp.pool_id", non_empty=True, max_len=min(256, max_str_len))
        if not isinstance(amount, int) or isinstance(amount, bool) or amount < 0:
            raise ValueError("invalid lp entry (amount)")
        key = (pk_s, pool_id_s)
        if key in seen_lp:
            raise ValueError("duplicate lp entry (pubkey, pool_id)")
        seen_lp.add(key)
        lp_balances.set(pk_s, pool_id_s, amount)

    lp_mint_timestamp_entries = snapshot.get("lp_mint_timestamps")
    if version >= 3 and lp_mint_timestamp_entries is None:
        raise ValueError("snapshot.lp_mint_timestamps is required for snapshot v3+")
    if lp_mint_timestamp_entries is None:
        lp_mint_timestamp_entries = []
    if not isinstance(lp_mint_timestamp_entries, list):
        raise TypeError("snapshot.lp_mint_timestamps must be a list")
    if len(lp_mint_timestamp_entries) > max_lp_balances:
        raise ValueError(
            f"too many lp_mint_timestamps entries: {len(lp_mint_timestamp_entries)} > {max_lp_balances}"
        )
    seen_lp_mint: set[tuple[str, str]] = set()
    for entry in lp_mint_timestamp_entries:
        if not isinstance(entry, Mapping):
            raise TypeError("snapshot.lp_mint_timestamps entries must be objects")
        pk = entry.get("pubkey")
        pool_id_raw = entry.get("pool_id")
        timestamp = entry.get("last_mint_timestamp")
        pk_s = _require_str(pk, name="lp_mint.pubkey", non_empty=True, max_len=min(512, max_str_len))
        pool_id_s = _require_str(
            pool_id_raw,
            name="lp_mint.pool_id",
            non_empty=True,
            max_len=min(256, max_str_len),
        )
        if not isinstance(timestamp, int) or isinstance(timestamp, bool) or timestamp < 0:
            raise ValueError("invalid lp_mint_timestamps entry (last_mint_timestamp)")
        key = (pk_s, pool_id_s)
        if key in seen_lp_mint:
            raise ValueError("duplicate lp_mint_timestamps entry (pubkey, pool_id)")
        seen_lp_mint.add(key)
        lp_balances.set_last_mint_timestamp(pk_s, pool_id_s, timestamp)

    lp_duration_risk_entries = snapshot.get("lp_duration_risk")
    if version >= 4 and lp_duration_risk_entries is None:
        raise ValueError("snapshot.lp_duration_risk is required for snapshot v4")
    if lp_duration_risk_entries is None:
        lp_duration_risk_entries = []
    if not isinstance(lp_duration_risk_entries, list):
        raise TypeError("snapshot.lp_duration_risk must be a list")
    if len(lp_duration_risk_entries) > max_lp_balances:
        raise ValueError(f"too many lp_duration_risk entries: {len(lp_duration_risk_entries)} > {max_lp_balances}")
    seen_lp_duration: set[tuple[str, str]] = set()
    for entry in lp_duration_risk_entries:
        if not isinstance(entry, Mapping):
            raise TypeError("snapshot.lp_duration_risk entries must be objects")
        pk = entry.get("pubkey")
        pool_id_raw = entry.get("pool_id")
        pk_s = _require_str(pk, name="lp_duration.pubkey", non_empty=True, max_len=min(512, max_str_len))
        pool_id_s = _require_str(
            pool_id_raw,
            name="lp_duration.pool_id",
            non_empty=True,
            max_len=min(256, max_str_len),
        )
        key = (pk_s, pool_id_s)
        if key in seen_lp_duration:
            raise ValueError("duplicate lp_duration_risk entry (pubkey, pool_id)")
        seen_lp_duration.add(key)
        last_remove = entry.get("last_remove_timestamp")
        if last_remove is not None:
            lp_balances.set_last_remove_timestamp(
                pk_s,
                pool_id_s,
                _require_int(last_remove, name="lp_duration.last_remove_timestamp"),
            )
        churn_tier = _require_int(entry.get("churn_tier", 0), name="lp_duration.churn_tier")
        lp_balances.set_churn_tier(pk_s, pool_id_s, churn_tier)
        last_churn_update = entry.get("last_churn_update_timestamp")
        if last_churn_update is not None:
            lp_balances.set_last_churn_update_timestamp(
                pk_s,
                pool_id_s,
                _require_int(last_churn_update, name="lp_duration.last_churn_update_timestamp"),
            )

    if require_lp_mint_timestamps:
        missing_lp_age = [
            (pk, pool_id)
            for (pk, pool_id), amount in lp_balances.get_all_balances().items()
            if amount > 0 and lp_balances.get_last_mint_timestamp(pk, pool_id) is None
        ]
        if missing_lp_age:
            pk, pool_id = sorted(missing_lp_age)[0]
            raise ValueError(f"missing lp_mint_timestamps entry for positive LP balance: {pk}:{pool_id}")

    nonces = NonceTable()
    nonce_entries = snapshot.get("nonces")
    if nonce_entries is None:
        nonce_entries = []
    if not isinstance(nonce_entries, list):
        raise TypeError("snapshot.nonces must be a list")
    if len(nonce_entries) > max_nonces:
        raise ValueError(f"too many nonces entries: {len(nonce_entries)} > {max_nonces}")
    seen_nonce_pks: set[str] = set()
    for entry in nonce_entries:
        if not isinstance(entry, Mapping):
            raise TypeError("snapshot.nonces entries must be objects")
        raw_pk = _require_str(
            entry.get("pubkey"),
            name="nonce.pubkey",
            non_empty=True,
            max_len=min(512, max_str_len),
        )
        pk = canonical_hex_fixed_allow_0x(raw_pk, nbytes=48, name="nonce.pubkey")
        last_nonce = entry.get("last_nonce", 0)
        if not isinstance(last_nonce, int) or isinstance(last_nonce, bool) or last_nonce < 0:
            raise ValueError("invalid nonce entry (last_nonce)")
        if last_nonce > 0xFFFFFFFF:
            raise ValueError("invalid nonce entry (last_nonce out of u32 range)")
        if pk in seen_nonce_pks:
            raise ValueError("duplicate decoded nonce entry (pubkey)")
        seen_nonce_pks.add(pk)
        nonces.set_last(pk, int(last_nonce))

    missing = object()
    fee_acc_obj = snapshot.get("fee_accumulator", missing)
    if fee_acc_obj is missing:
        raise ValueError("snapshot.fee_accumulator is required")
    if not isinstance(fee_acc_obj, Mapping):
        raise TypeError("snapshot.fee_accumulator must be an object")
    dust = fee_acc_obj.get("dust", 0)
    fee_acc = FeeAccumulatorState(dust=_require_int(dust, name="fee_accumulator.dust"))

    vault = None
    vault_obj = snapshot.get("vault")
    if vault_obj is not None:
        if not isinstance(vault_obj, Mapping):
            raise TypeError("snapshot.vault must be an object or null")
        vault = VaultState(
            acc_reward_per_share=_require_int(vault_obj.get("acc_reward_per_share", 0), name="vault.acc_reward_per_share"),
            last_update_acc=_require_int(vault_obj.get("last_update_acc", 0), name="vault.last_update_acc"),
            pending_rewards=_require_int(vault_obj.get("pending_rewards", 0), name="vault.pending_rewards"),
            reward_balance=_require_int(vault_obj.get("reward_balance", 0), name="vault.reward_balance"),
            staked_lp_shares=_require_int(vault_obj.get("staked_lp_shares", 0), name="vault.staked_lp_shares"),
        )

    oracle = None
    oracle_obj = snapshot.get("oracle")
    if oracle_obj is not None:
        if not isinstance(oracle_obj, Mapping):
            raise TypeError("snapshot.oracle must be an object or null")
        oracle = OracleState(
            price_timestamp=_require_int(oracle_obj.get("price_timestamp", 0), name="oracle.price_timestamp"),
            max_staleness_seconds=_require_int(oracle_obj.get("max_staleness_seconds", 300), name="oracle.max_staleness_seconds"),
        )

    perps = None
    if version >= 2:
        perps_obj = snapshot.get("perps")
        if perps_obj is not None:
            if not isinstance(perps_obj, Mapping):
                raise TypeError("snapshot.perps must be an object or null")
            perps_version = perps_obj.get("version", 0)
            if not isinstance(perps_version, int) or isinstance(perps_version, bool) or perps_version <= 0:
                raise ValueError("snapshot.perps.version must be a positive int")

            markets_entries = perps_obj.get("markets")
            if markets_entries is None:
                markets_entries = []
            if not isinstance(markets_entries, list):
                raise TypeError("snapshot.perps.markets must be a list")
            if len(markets_entries) > max_perp_markets:
                raise ValueError(f"too many perps markets: {len(markets_entries)} > {max_perp_markets}")

            markets: Dict[str, PerpAnyMarketState] = {}
            for entry in markets_entries:
                if not isinstance(entry, Mapping):
                    raise TypeError("snapshot.perps.markets entries must be objects")
                market_id = _require_str(entry.get("market_id"), name="perps.market_id", non_empty=True, max_len=min(256, max_str_len))
                if market_id in markets:
                    raise ValueError("duplicate perps market_id")
                if int(perps_version) < PERPS_STATE_VERSION_V5:
                    # v4 snapshot: isolated markets only, legacy schema without `kind`.
                    quote_asset = _require_str(entry.get("quote_asset"), name="perps.quote_asset", non_empty=True, max_len=min(256, max_str_len))
                    global_state = entry.get("global_state")
                    if not isinstance(global_state, Mapping):
                        raise TypeError("perps.global_state must be an object")
                    global_state_dict: Dict[str, Any] = dict(global_state)
                    # Backward compat: infer epoch_phase from existing state fields.
                    if "epoch_phase" not in global_state_dict:
                        global_state_dict["epoch_phase"] = _infer_epoch_phase(global_state_dict)

                    acct_entries = entry.get("accounts")
                    if acct_entries is None:
                        acct_entries = []
                    if not isinstance(acct_entries, list):
                        raise TypeError("perps.accounts must be a list")
                    if len(acct_entries) > max_perp_accounts:
                        raise ValueError(
                            f"too many perps accounts in market {market_id}: {len(acct_entries)} > {max_perp_accounts}"
                        )

                    accounts: Dict[str, PerpAccountState] = {}
                    for acct in acct_entries:
                        if not isinstance(acct, Mapping):
                            raise TypeError("perps.accounts entries must be objects")
                        pk = _require_str(
                            acct.get("pubkey"), name="perps.account.pubkey", non_empty=True, max_len=min(512, max_str_len)
                        )
                        if pk in accounts:
                            raise ValueError("duplicate perps account pubkey in market")
                        accounts[pk] = PerpAccountState(
                            position_base=_require_int(
                                acct.get("position_base", 0), name="perps.account.position_base", non_negative=False
                            ),
                            entry_price_e8=_require_int(acct.get("entry_price_e8", 0), name="perps.account.entry_price_e8"),
                            collateral_quote=_require_int(
                                acct.get("collateral_quote", 0), name="perps.account.collateral_quote"
                            ),
                            funding_paid_cumulative=_require_int(
                                acct.get("funding_paid_cumulative", 0),
                                name="perps.account.funding_paid_cumulative",
                                non_negative=False,
                            ),
                            funding_last_applied_epoch=_require_int(
                                acct.get("funding_last_applied_epoch", 0),
                                name="perps.account.funding_last_applied_epoch",
                                non_negative=True,
                            ),
                            liquidated_this_step=_require_bool(
                                acct.get("liquidated_this_step", False), name="perps.account.liquidated_this_step"
                            ),
                        )

                    markets[market_id] = PerpMarketState(
                        kind=PERP_MARKET_KIND_ISOLATED_V2,
                        quote_asset=quote_asset,
                        global_state=global_state_dict,
                        accounts=accounts,
                    )
                    continue

                # v5 snapshot: per-market kind tags.
                kind = _require_str(entry.get("kind"), name="perps.market.kind", non_empty=True, max_len=64)
                if kind == PERP_MARKET_KIND_ISOLATED_V2:
                    quote_asset = _require_str(entry.get("quote_asset"), name="perps.quote_asset", non_empty=True, max_len=min(256, max_str_len))
                    global_state = entry.get("global_state")
                    if not isinstance(global_state, Mapping):
                        raise TypeError("perps.global_state must be an object")
                    global_state_dict = dict(global_state)
                    # Backward compat: infer epoch_phase from existing state fields.
                    if "epoch_phase" not in global_state_dict:
                        global_state_dict["epoch_phase"] = _infer_epoch_phase(global_state_dict)

                    acct_entries = entry.get("accounts")
                    if acct_entries is None:
                        acct_entries = []
                    if not isinstance(acct_entries, list):
                        raise TypeError("perps.accounts must be a list")
                    if len(acct_entries) > max_perp_accounts:
                        raise ValueError(
                            f"too many perps accounts in market {market_id}: {len(acct_entries)} > {max_perp_accounts}"
                        )

                    accounts = {}
                    for acct in acct_entries:
                        if not isinstance(acct, Mapping):
                            raise TypeError("perps.accounts entries must be objects")
                        pk = _require_str(
                            acct.get("pubkey"), name="perps.account.pubkey", non_empty=True, max_len=min(512, max_str_len)
                        )
                        if pk in accounts:
                            raise ValueError("duplicate perps account pubkey in market")
                        accounts[pk] = PerpAccountState(
                            position_base=_require_int(
                                acct.get("position_base", 0), name="perps.account.position_base", non_negative=False
                            ),
                            entry_price_e8=_require_int(acct.get("entry_price_e8", 0), name="perps.account.entry_price_e8"),
                            collateral_quote=_require_int(
                                acct.get("collateral_quote", 0), name="perps.account.collateral_quote"
                            ),
                            funding_paid_cumulative=_require_int(
                                acct.get("funding_paid_cumulative", 0),
                                name="perps.account.funding_paid_cumulative",
                                non_negative=False,
                            ),
                            funding_last_applied_epoch=_require_int(
                                acct.get("funding_last_applied_epoch", 0),
                                name="perps.account.funding_last_applied_epoch",
                                non_negative=True,
                            ),
                            liquidated_this_step=_require_bool(
                                acct.get("liquidated_this_step", False), name="perps.account.liquidated_this_step"
                            ),
                        )

                    pending_root_entries = entry.get("pending_funding_closeout_root_hashes")
                    if pending_root_entries is None:
                        pending_root_hashes = ()
                    else:
                        if not isinstance(pending_root_entries, list):
                            raise TypeError("perps.pending_funding_closeout_root_hashes must be a list")
                        pending_root_hashes = tuple(
                            _require_str(
                                root_hash,
                                name="perps.pending_funding_closeout_root_hash",
                                non_empty=True,
                                max_len=len("sha256:") + 64,
                            )
                            for root_hash in pending_root_entries
                        )

                    pending_source_root_entries = entry.get(
                        "pending_funding_closeout_source_availability_hashes"
                    )
                    if pending_source_root_entries is None:
                        pending_source_root_hashes = ()
                    else:
                        if not isinstance(pending_source_root_entries, list):
                            raise TypeError(
                                "perps.pending_funding_closeout_source_availability_hashes must be a list"
                            )
                        pending_source_root_hashes = tuple(
                            _require_str(
                                root_hash,
                                name="perps.pending_funding_closeout_source_availability_hash",
                                non_empty=True,
                                max_len=len("sha256:") + 64,
                            )
                            for root_hash in pending_source_root_entries
                        )

                    pending_carried_root_entries = entry.get(
                        "pending_funding_closeout_carried_liability_hashes"
                    )
                    if pending_carried_root_entries is None:
                        pending_carried_root_hashes = ()
                    else:
                        if not isinstance(pending_carried_root_entries, list):
                            raise TypeError(
                                "perps.pending_funding_closeout_carried_liability_hashes must be a list"
                            )
                        pending_carried_root_hashes = tuple(
                            _require_str(
                                root_hash,
                                name="perps.pending_funding_closeout_carried_liability_hash",
                                non_empty=True,
                                max_len=len("sha256:") + 64,
                            )
                            for root_hash in pending_carried_root_entries
                        )

                    policy_ledger_root_entries = entry.get(
                        "funding_closeout_policy_ledger_hashes"
                    )
                    if policy_ledger_root_entries is None:
                        policy_ledger_hashes = ()
                    else:
                        if not isinstance(policy_ledger_root_entries, list):
                            raise TypeError(
                                "perps.funding_closeout_policy_ledger_hashes must be a list"
                            )
                        policy_ledger_hashes = tuple(
                            _require_str(
                                root_hash,
                                name="perps.funding_closeout_policy_ledger_hash",
                                non_empty=True,
                                max_len=len("sha256:") + 64,
                            )
                            for root_hash in policy_ledger_root_entries
                        )

                    sink_claimant_balance_entries = entry.get(
                        "funding_closeout_sink_claimant_balances_quote"
                    )
                    if sink_claimant_balance_entries is None:
                        sink_claimant_balances = ()
                    else:
                        if not isinstance(sink_claimant_balance_entries, list):
                            raise TypeError(
                                "perps.funding_closeout_sink_claimant_balances_quote must be a list"
                            )
                        sink_claimant_balances_list = []
                        for row in sink_claimant_balance_entries:
                            if not isinstance(row, Mapping):
                                raise TypeError(
                                    "perps.funding_closeout_sink_claimant_balances_quote entries must be objects"
                                )
                            sink_claimant_balances_list.append(
                                (
                                    _require_str(
                                        row.get("claimant"),
                                        name="perps.funding_closeout_sink_claimant",
                                        non_empty=True,
                                        max_len=min(256, max_str_len),
                                    ),
                                    _require_int(
                                        row.get("balance_quote", 0),
                                        name="perps.funding_closeout_sink_claimant.balance_quote",
                                    ),
                                )
                            )
                        sink_claimant_balances = tuple(sink_claimant_balances_list)

                    receiver_claim_balance_entries = entry.get(
                        "funding_closeout_receiver_claim_balances_quote"
                    )
                    if receiver_claim_balance_entries is None:
                        receiver_claim_balances = ()
                    else:
                        if not isinstance(receiver_claim_balance_entries, list):
                            raise TypeError(
                                "perps.funding_closeout_receiver_claim_balances_quote must be a list"
                            )
                        receiver_claim_balances_list = []
                        for row in receiver_claim_balance_entries:
                            if not isinstance(row, Mapping):
                                raise TypeError(
                                    "perps.funding_closeout_receiver_claim_balances_quote entries must be objects"
                                )
                            receiver_claim_balances_list.append(
                                (
                                    _require_str(
                                        row.get("account_pubkey"),
                                        name="perps.funding_closeout_receiver_claim_account",
                                        non_empty=True,
                                        max_len=min(512, max_str_len),
                                    ),
                                    _require_int(
                                        row.get("balance_quote", 0),
                                        name="perps.funding_closeout_receiver_claim.balance_quote",
                                    ),
                                )
                            )
                        receiver_claim_balances = tuple(receiver_claim_balances_list)

                    receiver_claim_lot_entries = entry.get(
                        "funding_closeout_receiver_claim_lots_quote"
                    )
                    if receiver_claim_lot_entries is None:
                        receiver_claim_lots = ()
                    else:
                        if not isinstance(receiver_claim_lot_entries, list):
                            raise TypeError(
                                "perps.funding_closeout_receiver_claim_lots_quote must be a list"
                            )
                        receiver_claim_lots_list = []
                        for row in receiver_claim_lot_entries:
                            if not isinstance(row, Mapping):
                                raise TypeError(
                                    "perps.funding_closeout_receiver_claim_lots_quote entries must be objects"
                                )
                            receiver_claim_lots_list.append(
                                (
                                    _require_str(
                                        row.get("account_pubkey"),
                                        name="perps.funding_closeout_receiver_claim_lot.account_pubkey",
                                        non_empty=True,
                                        max_len=min(512, max_str_len),
                                    ),
                                    _require_str(
                                        row.get("lot_id"),
                                        name="perps.funding_closeout_receiver_claim_lot.lot_id",
                                        non_empty=True,
                                        max_len=min(256, max_str_len),
                                    ),
                                    _require_int(
                                        row.get("balance_quote", 0),
                                        name="perps.funding_closeout_receiver_claim_lot.balance_quote",
                                    ),
                                    _require_int(
                                        row.get("expires_at_epoch", 0),
                                        name="perps.funding_closeout_receiver_claim_lot.expires_at_epoch",
                                    ),
                                )
                            )
                        receiver_claim_lots = tuple(receiver_claim_lots_list)

                    markets[market_id] = PerpMarketState(
                        kind=PERP_MARKET_KIND_ISOLATED_V2,
                        quote_asset=quote_asset,
                        global_state=global_state_dict,
                        accounts=accounts,
                        pending_funding_closeout_root_hashes=pending_root_hashes,
                        pending_funding_closeout_source_availability_hashes=(
                            pending_source_root_hashes
                        ),
                        pending_funding_closeout_carried_liability_hashes=(
                            pending_carried_root_hashes
                        ),
                        funding_closeout_policy_ledger_hashes=policy_ledger_hashes,
                        funding_closeout_sink_claimant_balances_quote=(
                            sink_claimant_balances
                        ),
                        funding_closeout_receiver_claim_balances_quote=(
                            receiver_claim_balances
                        ),
                        funding_closeout_receiver_claim_lots_quote=(
                            receiver_claim_lots
                        ),
                    )
                    continue

                if kind == PERP_MARKET_KIND_CLEARINGHOUSE_2P_V1:
                    quote_asset = _require_str(entry.get("quote_asset"), name="perps.quote_asset", non_empty=True, max_len=min(256, max_str_len))
                    account_a = _require_str(
                        entry.get("account_a_pubkey"),
                        name="perps.ch2p.account_a_pubkey",
                        non_empty=True,
                        max_len=min(512, max_str_len),
                    )
                    account_b = _require_str(
                        entry.get("account_b_pubkey"),
                        name="perps.ch2p.account_b_pubkey",
                        non_empty=True,
                        max_len=min(512, max_str_len),
                    )
                    state_obj = entry.get("state")
                    if not isinstance(state_obj, Mapping):
                        raise TypeError("perps.ch2p.state must be an object")
                    state_dict = dict(state_obj)
                    markets[market_id] = PerpClearinghouse2pMarketState(
                        kind=PERP_MARKET_KIND_CLEARINGHOUSE_2P_V1,
                        quote_asset=quote_asset,
                        account_a_pubkey=account_a,
                        account_b_pubkey=account_b,
                        state=state_dict,
                    )
                    continue

                if kind == PERP_MARKET_KIND_CLEARINGHOUSE_3P_TRANSFER_V1:
                    quote_asset = _require_str(entry.get("quote_asset"), name="perps.quote_asset", non_empty=True, max_len=min(256, max_str_len))
                    account_a = _require_str(
                        entry.get("account_a_pubkey"),
                        name="perps.ch3p.account_a_pubkey",
                        non_empty=True,
                        max_len=min(512, max_str_len),
                    )
                    account_b = _require_str(
                        entry.get("account_b_pubkey"),
                        name="perps.ch3p.account_b_pubkey",
                        non_empty=True,
                        max_len=min(512, max_str_len),
                    )
                    account_c = _require_str(
                        entry.get("account_c_pubkey"),
                        name="perps.ch3p.account_c_pubkey",
                        non_empty=True,
                        max_len=min(512, max_str_len),
                    )
                    state_obj = entry.get("state")
                    if not isinstance(state_obj, Mapping):
                        raise TypeError("perps.ch3p.state must be an object")
                    state_dict = dict(state_obj)
                    markets[market_id] = PerpClearinghouse3pTransferMarketState(
                        kind=PERP_MARKET_KIND_CLEARINGHOUSE_3P_TRANSFER_V1,
                        quote_asset=quote_asset,
                        account_a_pubkey=account_a,
                        account_b_pubkey=account_b,
                        account_c_pubkey=account_c,
                        state=state_dict,
                    )
                    continue

                raise ValueError(f"unsupported perps market kind: {kind}")

            perps = PerpsState(version=int(perps_version), markets=markets)

    return DexState(
        balances=balances,
        pools=pools,
        lp_balances=lp_balances,
        nonces=nonces,
        vault=vault,
        oracle=oracle,
        fee_accumulator=fee_acc,
        perps=perps,
    )
