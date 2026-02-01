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
from ..core.vault import VaultState
from ..state.balances import BalanceTable
from ..state.canonical import bounded_json_utf8_size, canonical_json_bytes, domain_sep_bytes, sha256_hex
from ..state.lp import LPTable
from ..state.nonces import NonceTable
from ..state.pools import PoolState, PoolStatus


DEX_SNAPSHOT_VERSION = 1


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
            }
        )
    pools_entries.sort(key=lambda e: e["pool_id"])

    lp_entries = [
        {"pubkey": pk, "pool_id": pool_id, "amount": int(amount)}
        for (pk, pool_id), amount in state.lp_balances.get_all_balances().items()
    ]
    lp_entries.sort(key=lambda e: (e["pubkey"], e["pool_id"]))

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

    data: Dict[str, Any] = {
        "version": int(version),
        "balances": balances_entries,
        "pools": pools_entries,
        "lp_balances": lp_entries,
        "nonces": nonce_entries,
        "fee_accumulator": fee_acc_obj,
        "vault": vault_obj,
        "oracle": oracle_obj,
    }
    return DexSnapshot(version=version, data=data)


def state_from_snapshot(
    snapshot: Mapping[str, Any],
    *,
    max_snapshot_bytes: int = 4_000_000,
    max_balances: int = 200_000,
    max_pools: int = 50_000,
    max_lp_balances: int = 200_000,
    max_nonces: int = 200_000,
    max_str_len: int = 4096,
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
    if version != DEX_SNAPSHOT_VERSION:
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
        pool_id = entry.get("pool_id")
        amount = entry.get("amount")
        pk_s = _require_str(pk, name="lp.pubkey", non_empty=True, max_len=min(512, max_str_len))
        pool_id_s = _require_str(pool_id, name="lp.pool_id", non_empty=True, max_len=min(256, max_str_len))
        if not isinstance(amount, int) or isinstance(amount, bool) or amount < 0:
            raise ValueError("invalid lp entry (amount)")
        key = (pk_s, pool_id_s)
        if key in seen_lp:
            raise ValueError("duplicate lp entry (pubkey, pool_id)")
        seen_lp.add(key)
        lp_balances.set(pk_s, pool_id_s, amount)

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
        pk = _require_str(entry.get("pubkey"), name="nonce.pubkey", non_empty=True, max_len=min(512, max_str_len))
        last_nonce = entry.get("last_nonce", 0)
        if not isinstance(last_nonce, int) or isinstance(last_nonce, bool) or last_nonce < 0:
            raise ValueError("invalid nonce entry (last_nonce)")
        if last_nonce > 0xFFFFFFFF:
            raise ValueError("invalid nonce entry (last_nonce out of u32 range)")
        if pk in seen_nonce_pks:
            raise ValueError("duplicate nonce entry (pubkey)")
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

    return DexState(
        balances=balances,
        pools=pools,
        lp_balances=lp_balances,
        nonces=nonces,
        vault=vault,
        oracle=oracle,
        fee_accumulator=fee_acc,
    )
