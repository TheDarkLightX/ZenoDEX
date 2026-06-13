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
    PERP_MARKET_KIND_CLEARINGHOUSE_NP_V1,
    PERP_MARKET_KIND_ISOLATED_V2,
    PERPS_STATE_VERSION_V5,
    PerpAccountState,
    PerpAnyMarketState,
    PerpClearinghouse2pMarketState,
    PerpClearinghouse3pTransferMarketState,
    PerpClearinghouseNpAccount,
    PerpClearinghouseNpMarketState,
    PerpClearinghouseNpPendingIntent,
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


def _snapshot_identity_key(value: str, *, nbytes: int, name: str) -> tuple[str, str]:
    """Key used only for duplicate detection at snapshot boundaries.

    Explicit ``0x`` fixed-width hex identifiers are compared by their decoded
    identity (represented by canonical lowercase hex), matching the state-root
    encoder. Symbolic dev/test identifiers and raw hex strings keep their raw
    spelling for compatibility with local snapshot paths.
    """

    if not value.startswith("0x"):
        return ("raw", value)
    try:
        return ("hex", canonical_hex_fixed_allow_0x(value, nbytes=nbytes, name=name))
    except (TypeError, ValueError):
        return ("raw", value)


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

            if isinstance(market, PerpClearinghouseNpMarketState):
                acct_entries = [
                    {
                        "pubkey": str(acct.pubkey),
                        "position_base": int(acct.position_base),
                        "entry_price_e8": int(acct.entry_price_e8),
                        "collateral_e8": int(acct.collateral_e8),
                        "funding_paid_cum_e8": int(acct.funding_paid_cum_e8),
                        "nonce": int(acct.nonce),
                    }
                    for acct in market.accounts
                ]
                acct_entries.sort(key=lambda e: str(e["pubkey"]))
                pending_entries = [
                    {
                        "pubkey": str(intent.pubkey),
                        "target_base": int(intent.target_base),
                        "limit_price_e8": int(intent.limit_price_e8),
                        "min_fill_base": int(intent.min_fill_base),
                        "expiry_epoch": int(intent.expiry_epoch),
                        "nonce": int(intent.nonce),
                    }
                    for intent in market.pending_intents
                ]
                pending_entries.sort(key=lambda e: str(e["pubkey"]))
                out_entry = {
                    "market_id": str(market_id),
                    "kind": str(getattr(market, "kind", PERP_MARKET_KIND_CLEARINGHOUSE_NP_V1)),
                    "quote_asset": str(market.quote_asset),
                    "global_state": dict(market.global_state),
                    "accounts": acct_entries,
                    "pending_intents": pending_entries,
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


def _parse_balances(snapshot: Mapping[str, Any], *, max_balances: int, max_str_len: int) -> BalanceTable:
    """Parse the ``balances`` snapshot section into a ``BalanceTable``.

    Behavior is identical to the inline parser: list-only container, object
    entries, non-negative int amounts (bool rejected), and decoded-identity
    duplicate detection over ``(pubkey, asset)``.
    """
    balances = BalanceTable()
    balances_entries = snapshot.get("balances")
    if balances_entries is None:
        balances_entries = []
    if not isinstance(balances_entries, list):
        raise TypeError("snapshot.balances must be a list")
    if len(balances_entries) > max_balances:
        raise ValueError(f"too many balances entries: {len(balances_entries)} > {max_balances}")
    seen_balances: set[tuple[tuple[str, str], tuple[str, str]]] = set()
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
        key = (
            _snapshot_identity_key(pk_s, nbytes=48, name="balance.pubkey"),
            _snapshot_identity_key(asset_s, nbytes=32, name="balance.asset"),
        )
        if key in seen_balances:
            raise ValueError("duplicate decoded balance entry (pubkey, asset)")
        seen_balances.add(key)
        balances.set(pk_s, asset_s, amount)
    return balances


def _parse_pools(
    snapshot: Mapping[str, Any], *, max_pools: int, max_str_len: int, max_snapshot_bytes: int
) -> Dict[str, PoolState]:
    """Parse the ``pools`` snapshot section into a ``pool_id -> PoolState`` map.

    Preserves the inline parser exactly: pool_id duplicate detection by decoded
    identity, status enum validation, ``fee_bps`` <= 10_000, and the default
    ``curve_tag`` (``"CPMM"``) / ``curve_params`` (``""``, empty allowed).
    """
    pools: Dict[str, PoolState] = {}
    pools_entries = snapshot.get("pools")
    if pools_entries is None:
        pools_entries = []
    if not isinstance(pools_entries, list):
        raise TypeError("snapshot.pools must be a list")
    if len(pools_entries) > max_pools:
        raise ValueError(f"too many pools entries: {len(pools_entries)} > {max_pools}")
    seen_pool_ids: set[tuple[str, str]] = set()
    for entry in pools_entries:
        if not isinstance(entry, Mapping):
            raise TypeError("snapshot.pools entries must be objects")
        pool_id = _require_str(entry.get("pool_id"), name="pool.pool_id", non_empty=True, max_len=min(256, max_str_len))
        pool_key = _snapshot_identity_key(pool_id, nbytes=32, name="pool.pool_id")
        if pool_key in seen_pool_ids:
            raise ValueError("duplicate decoded pool entry (pool_id)")
        seen_pool_ids.add(pool_key)
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
    return pools


def _parse_lp_balances_section(
    lp_balances: LPTable, snapshot: Mapping[str, Any], *, max_lp_balances: int, max_str_len: int
) -> None:
    """Parse ``lp_balances`` into the shared ``LPTable`` (mutates in place)."""
    lp_entries = snapshot.get("lp_balances")
    if lp_entries is None:
        lp_entries = []
    if not isinstance(lp_entries, list):
        raise TypeError("snapshot.lp_balances must be a list")
    if len(lp_entries) > max_lp_balances:
        raise ValueError(f"too many lp_balances entries: {len(lp_entries)} > {max_lp_balances}")
    seen_lp: set[tuple[tuple[str, str], tuple[str, str]]] = set()
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
        key = (
            _snapshot_identity_key(pk_s, nbytes=48, name="lp.pubkey"),
            _snapshot_identity_key(pool_id_s, nbytes=32, name="lp.pool_id"),
        )
        if key in seen_lp:
            raise ValueError("duplicate decoded lp entry (pubkey, pool_id)")
        seen_lp.add(key)
        lp_balances.set(pk_s, pool_id_s, amount)


def _parse_lp_mint_timestamps_section(
    lp_balances: LPTable, snapshot: Mapping[str, Any], *, version: int, max_lp_balances: int, max_str_len: int
) -> None:
    """Parse ``lp_mint_timestamps`` into the shared ``LPTable``.

    Required (when absent) for snapshot v3+; mutates the table in place.
    """
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
    seen_lp_mint: set[tuple[tuple[str, str], tuple[str, str]]] = set()
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
        key = (
            _snapshot_identity_key(pk_s, nbytes=48, name="lp_mint.pubkey"),
            _snapshot_identity_key(pool_id_s, nbytes=32, name="lp_mint.pool_id"),
        )
        if key in seen_lp_mint:
            raise ValueError("duplicate decoded lp_mint_timestamps entry (pubkey, pool_id)")
        seen_lp_mint.add(key)
        lp_balances.set_last_mint_timestamp(pk_s, pool_id_s, timestamp)


def _parse_lp_duration_risk_section(
    lp_balances: LPTable, snapshot: Mapping[str, Any], *, version: int, max_lp_balances: int, max_str_len: int
) -> None:
    """Parse ``lp_duration_risk`` into the shared ``LPTable``.

    Required (when absent) for snapshot v4; mutates the table in place. The
    ``last_remove_timestamp`` and ``last_churn_update_timestamp`` fields are
    optional (``None`` -> skip), ``churn_tier`` defaults to 0.
    """
    lp_duration_risk_entries = snapshot.get("lp_duration_risk")
    if version >= 4 and lp_duration_risk_entries is None:
        raise ValueError("snapshot.lp_duration_risk is required for snapshot v4")
    if lp_duration_risk_entries is None:
        lp_duration_risk_entries = []
    if not isinstance(lp_duration_risk_entries, list):
        raise TypeError("snapshot.lp_duration_risk must be a list")
    if len(lp_duration_risk_entries) > max_lp_balances:
        raise ValueError(f"too many lp_duration_risk entries: {len(lp_duration_risk_entries)} > {max_lp_balances}")
    seen_lp_duration: set[tuple[tuple[str, str], tuple[str, str]]] = set()
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
        key = (
            _snapshot_identity_key(pk_s, nbytes=48, name="lp_duration.pubkey"),
            _snapshot_identity_key(pool_id_s, nbytes=32, name="lp_duration.pool_id"),
        )
        if key in seen_lp_duration:
            raise ValueError("duplicate decoded lp_duration_risk entry (pubkey, pool_id)")
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


def _parse_lp_tables(
    snapshot: Mapping[str, Any],
    *,
    version: int,
    max_lp_balances: int,
    max_str_len: int,
    require_lp_mint_timestamps: bool,
) -> LPTable:
    """Parse the three LP snapshot sub-sections into one ``LPTable``.

    The ``lp_balances``, ``lp_mint_timestamps`` and ``lp_duration_risk``
    sub-sections all mutate the same table, in that order, and the cross-section
    ``require_lp_mint_timestamps`` post-check runs after ``lp_duration_risk``
    (its original position, before nonces). Order and reject messages are
    preserved exactly.
    """
    lp_balances = LPTable()
    _parse_lp_balances_section(
        lp_balances, snapshot, max_lp_balances=max_lp_balances, max_str_len=max_str_len
    )
    _parse_lp_mint_timestamps_section(
        lp_balances, snapshot, version=version, max_lp_balances=max_lp_balances, max_str_len=max_str_len
    )
    _parse_lp_duration_risk_section(
        lp_balances, snapshot, version=version, max_lp_balances=max_lp_balances, max_str_len=max_str_len
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
    return lp_balances


def _parse_nonces(snapshot: Mapping[str, Any], *, max_nonces: int, max_str_len: int) -> NonceTable:
    """Parse the ``nonces`` snapshot section into a ``NonceTable``.

    Preserves the inline parser: non-negative ``last_nonce`` (bool rejected),
    u32 range bound, and decoded-identity duplicate detection over the pubkey.
    """
    nonces = NonceTable()
    nonce_entries = snapshot.get("nonces")
    if nonce_entries is None:
        nonce_entries = []
    if not isinstance(nonce_entries, list):
        raise TypeError("snapshot.nonces must be a list")
    if len(nonce_entries) > max_nonces:
        raise ValueError(f"too many nonces entries: {len(nonce_entries)} > {max_nonces}")
    seen_nonce_pks: set[tuple[str, str]] = set()
    for entry in nonce_entries:
        if not isinstance(entry, Mapping):
            raise TypeError("snapshot.nonces entries must be objects")
        pk = _require_str(entry.get("pubkey"), name="nonce.pubkey", non_empty=True, max_len=min(512, max_str_len))
        last_nonce = entry.get("last_nonce", 0)
        if not isinstance(last_nonce, int) or isinstance(last_nonce, bool) or last_nonce < 0:
            raise ValueError("invalid nonce entry (last_nonce)")
        if last_nonce > 0xFFFFFFFF:
            raise ValueError("invalid nonce entry (last_nonce out of u32 range)")
        nonce_key = _snapshot_identity_key(pk, nbytes=48, name="nonce.pubkey")
        if nonce_key in seen_nonce_pks:
            raise ValueError("duplicate decoded nonce entry (pubkey)")
        seen_nonce_pks.add(nonce_key)
        nonces.set_last(pk, int(last_nonce))
    return nonces


def _parse_fee_accumulator(snapshot: Mapping[str, Any]) -> FeeAccumulatorState:
    """Parse the required ``fee_accumulator`` section.

    The ``missing`` sentinel distinguishes an absent key (required reject) from a
    present-but-empty object; both behaviors are preserved.
    """
    missing = object()
    fee_acc_obj = snapshot.get("fee_accumulator", missing)
    if fee_acc_obj is missing:
        raise ValueError("snapshot.fee_accumulator is required")
    if not isinstance(fee_acc_obj, Mapping):
        raise TypeError("snapshot.fee_accumulator must be an object")
    dust = fee_acc_obj.get("dust", 0)
    return FeeAccumulatorState(dust=_require_int(dust, name="fee_accumulator.dust"))


def _parse_vault(snapshot: Mapping[str, Any]) -> Optional[VaultState]:
    """Parse the optional ``vault`` section (``None`` when absent/null)."""
    vault_obj = snapshot.get("vault")
    if vault_obj is None:
        return None
    if not isinstance(vault_obj, Mapping):
        raise TypeError("snapshot.vault must be an object or null")
    return VaultState(
        acc_reward_per_share=_require_int(vault_obj.get("acc_reward_per_share", 0), name="vault.acc_reward_per_share"),
        last_update_acc=_require_int(vault_obj.get("last_update_acc", 0), name="vault.last_update_acc"),
        pending_rewards=_require_int(vault_obj.get("pending_rewards", 0), name="vault.pending_rewards"),
        reward_balance=_require_int(vault_obj.get("reward_balance", 0), name="vault.reward_balance"),
        staked_lp_shares=_require_int(vault_obj.get("staked_lp_shares", 0), name="vault.staked_lp_shares"),
    )


def _parse_oracle(snapshot: Mapping[str, Any]) -> Optional[OracleState]:
    """Parse the optional ``oracle`` section.

    ``None`` when absent/null. ``max_staleness_seconds`` default is 300.
    """
    oracle_obj = snapshot.get("oracle")
    if oracle_obj is None:
        return None
    if not isinstance(oracle_obj, Mapping):
        raise TypeError("snapshot.oracle must be an object or null")
    return OracleState(
        price_timestamp=_require_int(oracle_obj.get("price_timestamp", 0), name="oracle.price_timestamp"),
        max_staleness_seconds=_require_int(oracle_obj.get("max_staleness_seconds", 300), name="oracle.max_staleness_seconds"),
    )


def _parse_isolated_account(acct: Mapping[str, Any], *, max_str_len: int) -> tuple[str, PerpAccountState]:
    """Parse one isolated-perp account entry into ``(pubkey, PerpAccountState)``.

    Shared by the v4-legacy and the v5 ``kind == isolated`` paths, which had
    byte-identical account bodies. Signed fields (``position_base``,
    ``funding_paid_cumulative``) keep ``non_negative=False``.
    """
    pk = _require_str(acct.get("pubkey"), name="perps.account.pubkey", non_empty=True, max_len=min(512, max_str_len))
    account = PerpAccountState(
        position_base=_require_int(
            acct.get("position_base", 0), name="perps.account.position_base", non_negative=False
        ),
        entry_price_e8=_require_int(acct.get("entry_price_e8", 0), name="perps.account.entry_price_e8"),
        collateral_quote=_require_int(acct.get("collateral_quote", 0), name="perps.account.collateral_quote"),
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
    return pk, account


def _parse_isolated_market(
    entry: Mapping[str, Any], *, market_id: str, max_perp_accounts: int, max_str_len: int
) -> PerpMarketState:
    """Parse an isolated-perp market (``PERP_MARKET_KIND_ISOLATED_V2``).

    Used for both v4-legacy (no ``kind``) and v5 ``kind == isolated`` entries;
    the inline bodies were identical. Preserves the ``epoch_phase`` backward-
    compat inference and the in-loop duplicate-pubkey reject.
    """
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
        pk, account = _parse_isolated_account(acct, max_str_len=max_str_len)
        if pk in accounts:
            raise ValueError("duplicate perps account pubkey in market")
        accounts[pk] = account

    return PerpMarketState(
        kind=PERP_MARKET_KIND_ISOLATED_V2,
        quote_asset=quote_asset,
        global_state=global_state_dict,
        accounts=accounts,
    )


def _parse_ch2p_market(entry: Mapping[str, Any], *, max_str_len: int) -> PerpClearinghouse2pMarketState:
    """Parse a 2-party clearinghouse market. Conservation is enforced by the
    ``PerpClearinghouse2pMarketState`` validator (not here)."""
    quote_asset = _require_str(entry.get("quote_asset"), name="perps.quote_asset", non_empty=True, max_len=min(256, max_str_len))
    account_a = _require_str(
        entry.get("account_a_pubkey"), name="perps.ch2p.account_a_pubkey", non_empty=True, max_len=min(512, max_str_len)
    )
    account_b = _require_str(
        entry.get("account_b_pubkey"), name="perps.ch2p.account_b_pubkey", non_empty=True, max_len=min(512, max_str_len)
    )
    state_obj = entry.get("state")
    if not isinstance(state_obj, Mapping):
        raise TypeError("perps.ch2p.state must be an object")
    state_dict = dict(state_obj)
    return PerpClearinghouse2pMarketState(
        kind=PERP_MARKET_KIND_CLEARINGHOUSE_2P_V1,
        quote_asset=quote_asset,
        account_a_pubkey=account_a,
        account_b_pubkey=account_b,
        state=state_dict,
    )


def _parse_ch3p_market(entry: Mapping[str, Any], *, max_str_len: int) -> PerpClearinghouse3pTransferMarketState:
    """Parse a 3-party transfer clearinghouse market. Conservation is enforced
    by the ``PerpClearinghouse3pTransferMarketState`` validator (not here)."""
    quote_asset = _require_str(entry.get("quote_asset"), name="perps.quote_asset", non_empty=True, max_len=min(256, max_str_len))
    account_a = _require_str(
        entry.get("account_a_pubkey"), name="perps.ch3p.account_a_pubkey", non_empty=True, max_len=min(512, max_str_len)
    )
    account_b = _require_str(
        entry.get("account_b_pubkey"), name="perps.ch3p.account_b_pubkey", non_empty=True, max_len=min(512, max_str_len)
    )
    account_c = _require_str(
        entry.get("account_c_pubkey"), name="perps.ch3p.account_c_pubkey", non_empty=True, max_len=min(512, max_str_len)
    )
    state_obj = entry.get("state")
    if not isinstance(state_obj, Mapping):
        raise TypeError("perps.ch3p.state must be an object")
    state_dict = dict(state_obj)
    return PerpClearinghouse3pTransferMarketState(
        kind=PERP_MARKET_KIND_CLEARINGHOUSE_3P_TRANSFER_V1,
        quote_asset=quote_asset,
        account_a_pubkey=account_a,
        account_b_pubkey=account_b,
        account_c_pubkey=account_c,
        state=state_dict,
    )


def _parse_chnp_account(acct: Mapping[str, Any], *, max_str_len: int) -> PerpClearinghouseNpAccount:
    """Parse one N-party clearinghouse account entry."""
    return PerpClearinghouseNpAccount(
        pubkey=_require_str(
            acct.get("pubkey"), name="perps.chnp.account.pubkey", non_empty=True, max_len=min(512, max_str_len)
        ),
        position_base=_require_int(
            acct.get("position_base", 0), name="perps.chnp.account.position_base", non_negative=False
        ),
        entry_price_e8=_require_int(acct.get("entry_price_e8", 0), name="perps.chnp.account.entry_price_e8"),
        collateral_e8=_require_int(acct.get("collateral_e8", 0), name="perps.chnp.account.collateral_e8"),
        funding_paid_cum_e8=_require_int(
            acct.get("funding_paid_cum_e8", 0), name="perps.chnp.account.funding_paid_cum_e8", non_negative=False
        ),
        nonce=_require_int(acct.get("nonce", 0), name="perps.chnp.account.nonce"),
    )


def _parse_chnp_pending_intent(
    intent: Mapping[str, Any], *, max_str_len: int
) -> PerpClearinghouseNpPendingIntent:
    """Parse one N-party pending intent.

    ``expiry_epoch`` defaults to ``1 << 62`` when absent; ``nonce`` has no
    default (absent -> ``_require_int(None)`` -> TypeError), preserving its
    required-ness.
    """
    return PerpClearinghouseNpPendingIntent(
        pubkey=_require_str(
            intent.get("pubkey"), name="perps.chnp.pending_intent.pubkey", non_empty=True, max_len=min(512, max_str_len)
        ),
        target_base=_require_int(
            intent.get("target_base", 0), name="perps.chnp.pending_intent.target_base", non_negative=False
        ),
        limit_price_e8=_require_int(intent.get("limit_price_e8", 0), name="perps.chnp.pending_intent.limit_price_e8"),
        min_fill_base=_require_int(intent.get("min_fill_base", 0), name="perps.chnp.pending_intent.min_fill_base"),
        expiry_epoch=_require_int(intent.get("expiry_epoch", 1 << 62), name="perps.chnp.pending_intent.expiry_epoch"),
        nonce=_require_int(intent.get("nonce"), name="perps.chnp.pending_intent.nonce"),
    )


def _parse_chnp_market(
    entry: Mapping[str, Any], *, market_id: str, max_perp_accounts: int, max_str_len: int
) -> PerpClearinghouseNpMarketState:
    """Parse an N-party clearinghouse market (accounts + pending intents).

    Cross-account/intent invariants (membership, net-zero) are enforced by the
    ``PerpClearinghouseNpMarketState`` validator, not here.
    """
    quote_asset = _require_str(
        entry.get("quote_asset"), name="perps.quote_asset", non_empty=True, max_len=min(256, max_str_len)
    )
    global_state = entry.get("global_state")
    if not isinstance(global_state, Mapping):
        raise TypeError("perps.chnp.global_state must be an object")
    global_state_dict: Dict[str, Any] = dict(global_state)

    acct_entries = entry.get("accounts")
    if acct_entries is None:
        acct_entries = []
    if not isinstance(acct_entries, list):
        raise TypeError("perps.chnp.accounts must be a list")
    if len(acct_entries) > max_perp_accounts:
        raise ValueError(
            f"too many perps accounts in market {market_id}: {len(acct_entries)} > {max_perp_accounts}"
        )
    np_accounts: list[PerpClearinghouseNpAccount] = []
    for acct in acct_entries:
        if not isinstance(acct, Mapping):
            raise TypeError("perps.chnp.accounts entries must be objects")
        np_accounts.append(_parse_chnp_account(acct, max_str_len=max_str_len))

    pending_entries = entry.get("pending_intents")
    if pending_entries is None:
        pending_entries = []
    if not isinstance(pending_entries, list):
        raise TypeError("perps.chnp.pending_intents must be a list")
    if len(pending_entries) > max_perp_accounts:
        raise ValueError(
            "too many perps pending intents in market "
            f"{market_id}: {len(pending_entries)} > {max_perp_accounts}"
        )
    pending_intents: list[PerpClearinghouseNpPendingIntent] = []
    for intent in pending_entries:
        if not isinstance(intent, Mapping):
            raise TypeError("perps.chnp.pending_intents entries must be objects")
        pending_intents.append(_parse_chnp_pending_intent(intent, max_str_len=max_str_len))

    return PerpClearinghouseNpMarketState(
        kind=PERP_MARKET_KIND_CLEARINGHOUSE_NP_V1,
        quote_asset=quote_asset,
        global_state=global_state_dict,
        accounts=tuple(np_accounts),
        pending_intents=tuple(pending_intents),
    )


def _parse_perps_market(
    entry: Mapping[str, Any],
    *,
    market_id: str,
    perps_version: int,
    max_perp_accounts: int,
    max_str_len: int,
) -> PerpAnyMarketState:
    """Dispatch one perps market entry to its kind-specific parser.

    v4 snapshots (``perps_version < V5``) carry isolated markets only with the
    legacy schema (no ``kind``); v5 snapshots carry a per-market ``kind`` tag.
    """
    if int(perps_version) < PERPS_STATE_VERSION_V5:
        # v4 snapshot: isolated markets only, legacy schema without `kind`.
        return _parse_isolated_market(
            entry, market_id=market_id, max_perp_accounts=max_perp_accounts, max_str_len=max_str_len
        )

    # v5 snapshot: per-market kind tags.
    kind = _require_str(entry.get("kind"), name="perps.market.kind", non_empty=True, max_len=64)
    if kind == PERP_MARKET_KIND_ISOLATED_V2:
        return _parse_isolated_market(
            entry, market_id=market_id, max_perp_accounts=max_perp_accounts, max_str_len=max_str_len
        )
    if kind == PERP_MARKET_KIND_CLEARINGHOUSE_2P_V1:
        return _parse_ch2p_market(entry, max_str_len=max_str_len)
    if kind == PERP_MARKET_KIND_CLEARINGHOUSE_3P_TRANSFER_V1:
        return _parse_ch3p_market(entry, max_str_len=max_str_len)
    if kind == PERP_MARKET_KIND_CLEARINGHOUSE_NP_V1:
        return _parse_chnp_market(
            entry, market_id=market_id, max_perp_accounts=max_perp_accounts, max_str_len=max_str_len
        )
    raise ValueError(f"unsupported perps market kind: {kind}")


def _parse_perps(
    snapshot: Mapping[str, Any],
    *,
    version: int,
    max_perp_markets: int,
    max_perp_accounts: int,
    max_str_len: int,
) -> Optional[PerpsState]:
    """Parse the optional ``perps`` section (snapshot v2+).

    Returns ``None`` for v1 snapshots or when ``perps`` is absent/null. Market
    duplicate detection (raw ``market_id``) and per-kind dispatch are preserved.
    """
    if version < 2:
        return None
    perps_obj = snapshot.get("perps")
    if perps_obj is None:
        return None
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
        markets[market_id] = _parse_perps_market(
            entry,
            market_id=market_id,
            perps_version=int(perps_version),
            max_perp_accounts=max_perp_accounts,
            max_str_len=max_str_len,
        )

    return PerpsState(version=int(perps_version), markets=markets)


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

    balances = _parse_balances(snapshot, max_balances=max_balances, max_str_len=max_str_len)
    pools = _parse_pools(
        snapshot, max_pools=max_pools, max_str_len=max_str_len, max_snapshot_bytes=max_snapshot_bytes
    )
    lp_balances = _parse_lp_tables(
        snapshot,
        version=version,
        max_lp_balances=max_lp_balances,
        max_str_len=max_str_len,
        require_lp_mint_timestamps=require_lp_mint_timestamps,
    )
    nonces = _parse_nonces(snapshot, max_nonces=max_nonces, max_str_len=max_str_len)
    fee_acc = _parse_fee_accumulator(snapshot)
    vault = _parse_vault(snapshot)
    oracle = _parse_oracle(snapshot)

    perps = _parse_perps(
        snapshot,
        version=version,
        max_perp_markets=max_perp_markets,
        max_perp_accounts=max_perp_accounts,
        max_str_len=max_str_len,
    )

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
