"""Restricted, exact Spot application-state to ZenoLedger-root bridge.

The legacy RISC0 Spot journal commits a canonical ``DexSnapshotV1`` hash and a
separate legacy nonce root.  ZenoLedger headers commit state-root-v5 over the
runtime tables.  Direct equality between those domains is invalid.  This
module derives both representations from the same exact ``DexState`` pair and
accepts only the closed compatibility profile implemented by the Rust bridge.

The returned type is private and carries only state-domain authority.  It does
not establish receipt validity, finality, data availability, settlement, or
production authority.  The strict verifier adapter is responsible for joining
it to an already authenticated receipt result.
"""

from __future__ import annotations

import hashlib
from enum import Enum
from typing import Any, Mapping, NoReturn, Sequence, final

from src.core.dex import DexState
from src.core.fees import FeeAccumulatorState
from src.state.balances import NATIVE_ASSET, BalanceTable
from src.state.canonical import canonical_hex_fixed_allow_0x, canonical_json_bytes
from src.state.lp import LPTable
from src.state.nonces import NonceTable
from src.state.pools import CURVE_TAG_CPMM, PoolState, PoolStatus, compute_pool_id
from src.state.state_root import _compute_state_root_python

RESTRICTED_SPOT_STATE_DOMAIN_BRIDGE_SCHEMA_V1 = (
    "zenodex.zeno_ledger.restricted_spot_state_domain_bridge.v1"
)
RESTRICTED_SPOT_STATE_DOMAIN_COMPATIBILITY_PROFILE_ID_V1 = (
    "0xc702e1e2f07cddbc5fccbfaeb39a2612d9ed6fb5fd6489a1d70c39f21d786404"
)
RESTRICTED_SPOT_STATE_ROOT_SCHEME_ID_V5 = (
    "0x0e7bd17d69eebebdd30cf3b3901afd5e821050a808d2eef73b0835a4176396a6"
)

_MAX_SECTION_ENTRIES = 16_384
_MAX_U32 = (1 << 32) - 1
_MAX_U64 = (1 << 64) - 1
_MAX_U128 = (1 << 128) - 1


class SpotStateDomainBridgeRejectReasonV1(str, Enum):
    """Stable rejection families for the closed compatibility bridge."""

    INPUT_TYPE_INVALID = "spot_state_domain_bridge.input_type_invalid"
    TRANSACTION_DOMAIN_INVALID = "spot_state_domain_bridge.transaction_domain_invalid"
    STATE_PROFILE_UNSUPPORTED = "spot_state_domain_bridge.state_profile_unsupported"
    SOURCE_COMMITMENT_MISMATCH = "spot_state_domain_bridge.source_commitment_mismatch"
    LEDGER_ROOT_MISMATCH = "spot_state_domain_bridge.ledger_root_mismatch"


class SpotStateDomainBridgeErrorV1(ValueError):
    """Fail-closed restricted state-domain bridge rejection."""

    def __init__(self, reason: SpotStateDomainBridgeRejectReasonV1, detail: str) -> None:
        self.reason = reason
        super().__init__(f"{reason.value}: {detail}")


_AUTHENTICATED_STATE_DOMAIN_BRIDGE_SEAL = object()


@final
class _AuthenticatedSpotLedgerStateDomainBridgeV1:
    """Private immutable proof that both root domains encode one state pair."""

    __slots__ = (
        "_compatibility_profile_id",
        "_ingress_nonce",
        "_ledger_post_state_root",
        "_ledger_pre_state_root",
        "_schema",
        "_seal",
        "_sender_pubkey",
        "_source_and_ledger_roots_verified",
        "_source_post_app_hash",
        "_source_post_nonce_root",
        "_source_pre_app_hash",
        "_source_pre_nonce_root",
        "_state_root_scheme_id",
    )

    def __init__(
        self,
        *,
        sender_pubkey: str,
        ingress_nonce: int,
        source_pre_app_hash: str,
        source_post_app_hash: str,
        source_pre_nonce_root: str,
        source_post_nonce_root: str,
        ledger_pre_state_root: str,
        ledger_post_state_root: str,
        seal: object,
    ) -> None:
        if seal is not _AUTHENTICATED_STATE_DOMAIN_BRIDGE_SEAL:
            raise TypeError("Spot state-domain bridge requires the private seal")
        values = {
            "_schema": RESTRICTED_SPOT_STATE_DOMAIN_BRIDGE_SCHEMA_V1,
            "_compatibility_profile_id": (
                RESTRICTED_SPOT_STATE_DOMAIN_COMPATIBILITY_PROFILE_ID_V1
            ),
            "_state_root_scheme_id": RESTRICTED_SPOT_STATE_ROOT_SCHEME_ID_V5,
            "_sender_pubkey": sender_pubkey,
            "_ingress_nonce": ingress_nonce,
            "_source_pre_app_hash": source_pre_app_hash,
            "_source_post_app_hash": source_post_app_hash,
            "_source_pre_nonce_root": source_pre_nonce_root,
            "_source_post_nonce_root": source_post_nonce_root,
            "_ledger_pre_state_root": ledger_pre_state_root,
            "_ledger_post_state_root": ledger_post_state_root,
            "_source_and_ledger_roots_verified": True,
            "_seal": seal,
        }
        for name, value in values.items():
            object.__setattr__(self, name, value)

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("authenticated Spot state-domain bridge cannot be subclassed")

    def _has_private_seal(self) -> bool:
        """Reject nominal instances that did not pass the private constructor."""

        return getattr(self, "_seal", None) is _AUTHENTICATED_STATE_DOMAIN_BRIDGE_SEAL

    def __setattr__(self, _name: str, _value: object) -> None:
        raise AttributeError("authenticated Spot state-domain bridge is immutable")

    def __copy__(self) -> NoReturn:
        raise TypeError("authenticated Spot state-domain bridge cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("authenticated Spot state-domain bridge cannot be copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("authenticated Spot state-domain bridge cannot be serialized")


def _derive_authenticated_spot_ledger_state_domain_bridge_v1(
    *,
    pre_state: DexState,
    post_state: DexState,
    transactions: Sequence[object],
    source_pre_app_hash: str,
    source_post_app_hash: str,
    source_pre_nonce_root: str,
    source_post_nonce_root: str,
    ledger_pre_state_root: str,
    ledger_post_state_root: str,
) -> _AuthenticatedSpotLedgerStateDomainBridgeV1:
    """Derive both root domains and mint the private bridge on exact equality."""

    try:
        sender, ingress_nonce = _parse_single_ingress(transactions)
        pre_snapshot = _restricted_legacy_snapshot_v1(pre_state, state_name="pre_state")
        post_snapshot = _restricted_legacy_snapshot_v1(post_state, state_name="post_state")
        _validate_runtime_nonce_transition(
            pre_state=pre_state,
            post_state=post_state,
            sender=sender,
            ingress_nonce=ingress_nonce,
        )
        derived = {
            "source_pre_app_hash": _legacy_app_hash(pre_snapshot),
            "source_post_app_hash": _legacy_app_hash(post_snapshot),
            "source_pre_nonce_root": _legacy_nonce_root(sender, ingress_nonce),
            "source_post_nonce_root": _legacy_nonce_root(sender, ingress_nonce + 1),
            "ledger_pre_state_root": _restricted_runtime_state_root_v5(pre_state),
            "ledger_post_state_root": _restricted_runtime_state_root_v5(post_state),
        }
        proposed = {
            "source_pre_app_hash": _require_root(
                source_pre_app_hash,
                name="source_pre_app_hash",
            ),
            "source_post_app_hash": _require_root(
                source_post_app_hash,
                name="source_post_app_hash",
            ),
            "source_pre_nonce_root": _require_root(
                source_pre_nonce_root,
                name="source_pre_nonce_root",
            ),
            "source_post_nonce_root": _require_root(
                source_post_nonce_root,
                name="source_post_nonce_root",
            ),
            "ledger_pre_state_root": _require_root(
                ledger_pre_state_root,
                name="ledger_pre_state_root",
            ),
            "ledger_post_state_root": _require_root(
                ledger_post_state_root,
                name="ledger_post_state_root",
            ),
        }
        for field_name, actual in derived.items():
            if proposed[field_name] != actual:
                reason = (
                    SpotStateDomainBridgeRejectReasonV1.SOURCE_COMMITMENT_MISMATCH
                    if field_name.startswith("source_")
                    else SpotStateDomainBridgeRejectReasonV1.LEDGER_ROOT_MISMATCH
                )
                raise SpotStateDomainBridgeErrorV1(
                    reason,
                    f"{field_name} does not match the exact derived state",
                )
        return _AuthenticatedSpotLedgerStateDomainBridgeV1(
            sender_pubkey=sender,
            ingress_nonce=ingress_nonce,
            source_pre_app_hash=derived["source_pre_app_hash"],
            source_post_app_hash=derived["source_post_app_hash"],
            source_pre_nonce_root=derived["source_pre_nonce_root"],
            source_post_nonce_root=derived["source_post_nonce_root"],
            ledger_pre_state_root=derived["ledger_pre_state_root"],
            ledger_post_state_root=derived["ledger_post_state_root"],
            seal=_AUTHENTICATED_STATE_DOMAIN_BRIDGE_SEAL,
        )
    except SpotStateDomainBridgeErrorV1:
        raise
    except (KeyError, TypeError, ValueError) as exc:
        raise SpotStateDomainBridgeErrorV1(
            SpotStateDomainBridgeRejectReasonV1.INPUT_TYPE_INVALID,
            "state-domain bridge input is not canonical",
        ) from exc


def _parse_single_ingress(transactions: Sequence[object]) -> tuple[str, int]:
    if type(transactions) not in (list, tuple) or len(transactions) != 1:
        raise SpotStateDomainBridgeErrorV1(
            SpotStateDomainBridgeRejectReasonV1.TRANSACTION_DOMAIN_INVALID,
            "restricted bridge requires exactly one transaction",
        )
    tx = transactions[0]
    if type(tx) is not dict:
        raise SpotStateDomainBridgeErrorV1(
            SpotStateDomainBridgeRejectReasonV1.TRANSACTION_DOMAIN_INVALID,
            "restricted transaction must be an exact object",
        )
    tx_obj = tx
    primary = tx_obj.get("tx_sender_pubkey")
    legacy = tx_obj.get("sender_pubkey")
    if primary is None:
        primary = legacy
    elif legacy is not None and legacy != primary:
        raise SpotStateDomainBridgeErrorV1(
            SpotStateDomainBridgeRejectReasonV1.TRANSACTION_DOMAIN_INVALID,
            "transaction sender aliases disagree",
        )
    sender = _require_identifier(primary, nbytes=48, name="transaction sender")
    ingress_nonce = tx_obj.get("nonce")
    if (
        not isinstance(ingress_nonce, int)
        or isinstance(ingress_nonce, bool)
        or ingress_nonce <= 0
        or ingress_nonce > _MAX_U32
    ):
        raise SpotStateDomainBridgeErrorV1(
            SpotStateDomainBridgeRejectReasonV1.TRANSACTION_DOMAIN_INVALID,
            "transaction nonce must be in 1..u32::MAX",
        )
    return sender, ingress_nonce


def _restricted_legacy_snapshot_v1(state: DexState, *, state_name: str) -> dict[str, Any]:
    _validate_state_container_types(state, state_name=state_name)
    if state.vault is not None or state.oracle is not None or state.perps is not None:
        raise SpotStateDomainBridgeErrorV1(
            SpotStateDomainBridgeRejectReasonV1.STATE_PROFILE_UNSUPPORTED,
            f"{state_name} contains a module outside the restricted Spot profile",
        )
    if state.lp_balances.get_all_duration_risk_metadata():
        raise SpotStateDomainBridgeErrorV1(
            SpotStateDomainBridgeRejectReasonV1.STATE_PROFILE_UNSUPPORTED,
            f"{state_name}.lp_duration_risk must be empty",
        )
    balances = _restricted_balances(state, state_name=state_name)
    pools = _restricted_pools(state, state_name=state_name)
    lp_balances = _restricted_lp_balances(state, state_name=state_name)
    dust = _require_uint(
        state.fee_accumulator.dust,
        max_value=_MAX_U128,
        name=f"{state_name}.fee_accumulator.dust",
    )
    return {
        "version": 1,
        "balances": balances,
        "pools": pools,
        "lp_balances": lp_balances,
        "fee_accumulator": {"dust": dust},
        "vault": None,
        "oracle": None,
    }


def _validate_state_container_types(state: DexState, *, state_name: str) -> None:
    expected = (
        (state, DexState, state_name),
        (getattr(state, "balances", None), BalanceTable, f"{state_name}.balances"),
        (getattr(state, "pools", None), dict, f"{state_name}.pools"),
        (getattr(state, "lp_balances", None), LPTable, f"{state_name}.lp_balances"),
        (getattr(state, "nonces", None), NonceTable, f"{state_name}.nonces"),
        (
            getattr(state, "fee_accumulator", None),
            FeeAccumulatorState,
            f"{state_name}.fee_accumulator",
        ),
    )
    for value, expected_type, name in expected:
        if type(value) is not expected_type:
            raise SpotStateDomainBridgeErrorV1(
                SpotStateDomainBridgeRejectReasonV1.INPUT_TYPE_INVALID,
                f"{name} must be exactly {expected_type.__name__}",
            )


def _restricted_balances(state: DexState, *, state_name: str) -> list[dict[str, Any]]:
    entries = state.balances.get_all_balances()
    _require_section_bound(entries, name=f"{state_name}.balances")
    output: list[dict[str, Any]] = []
    for (pubkey, asset), amount in entries.items():
        canonical_pubkey = _require_identifier(
            pubkey,
            nbytes=48,
            name=f"{state_name}.balance.pubkey",
        )
        canonical_asset = _require_identifier(
            asset,
            nbytes=32,
            name=f"{state_name}.balance.asset",
        )
        if canonical_asset == NATIVE_ASSET:
            raise SpotStateDomainBridgeErrorV1(
                SpotStateDomainBridgeRejectReasonV1.STATE_PROFILE_UNSUPPORTED,
                f"{state_name}.balance.asset cannot be native",
            )
        output.append(
            {
                "pubkey": canonical_pubkey,
                "asset": canonical_asset,
                "amount": _require_uint(
                    amount,
                    min_value=1,
                    max_value=_MAX_U128,
                    name=f"{state_name}.balance.amount",
                ),
            }
        )
    output.sort(key=lambda entry: (entry["pubkey"], entry["asset"]))
    return output


def _restricted_pools(state: DexState, *, state_name: str) -> list[dict[str, Any]]:
    _require_section_bound(state.pools, name=f"{state_name}.pools")
    output: list[dict[str, Any]] = []
    for map_pool_id, pool in state.pools.items():
        if type(pool) is not PoolState:
            raise SpotStateDomainBridgeErrorV1(
                SpotStateDomainBridgeRejectReasonV1.INPUT_TYPE_INVALID,
                f"{state_name}.pool must be exactly PoolState",
            )
        pool_id = _require_identifier(
            pool.pool_id,
            nbytes=32,
            name=f"{state_name}.pool.pool_id",
        )
        if map_pool_id != pool_id:
            raise SpotStateDomainBridgeErrorV1(
                SpotStateDomainBridgeRejectReasonV1.STATE_PROFILE_UNSUPPORTED,
                f"{state_name}.pool mapping key does not match pool_id",
            )
        asset0 = _require_identifier(
            pool.asset0,
            nbytes=32,
            name=f"{state_name}.pool.asset0",
        )
        asset1 = _require_identifier(
            pool.asset1,
            nbytes=32,
            name=f"{state_name}.pool.asset1",
        )
        if asset0 == NATIVE_ASSET or asset1 == NATIVE_ASSET or bytes.fromhex(
            asset0[2:]
        ) >= bytes.fromhex(asset1[2:]):
            raise SpotStateDomainBridgeErrorV1(
                SpotStateDomainBridgeRejectReasonV1.STATE_PROFILE_UNSUPPORTED,
                f"{state_name}.pool assets are outside the restricted profile",
            )
        fee_bps = _require_uint(
            pool.fee_bps,
            max_value=10_000,
            name=f"{state_name}.pool.fee_bps",
        )
        if (
            pool.curve_tag != CURVE_TAG_CPMM
            or pool.curve_params != ""
            or pool.status is not PoolStatus.ACTIVE
            or compute_pool_id(asset0, asset1, fee_bps) != pool_id
        ):
            raise SpotStateDomainBridgeErrorV1(
                SpotStateDomainBridgeRejectReasonV1.STATE_PROFILE_UNSUPPORTED,
                f"{state_name}.pool configuration is outside the restricted profile",
            )
        output.append(
            {
                "pool_id": pool_id,
                "asset0": asset0,
                "asset1": asset1,
                "reserve0": _require_uint(
                    pool.reserve0,
                    max_value=_MAX_U128,
                    name=f"{state_name}.pool.reserve0",
                ),
                "reserve1": _require_uint(
                    pool.reserve1,
                    max_value=_MAX_U128,
                    name=f"{state_name}.pool.reserve1",
                ),
                "fee_bps": fee_bps,
                "lp_supply": _require_uint(
                    pool.lp_supply,
                    max_value=_MAX_U128,
                    name=f"{state_name}.pool.lp_supply",
                ),
                "status": "ACTIVE",
                "created_at": _require_uint(
                    pool.created_at,
                    max_value=_MAX_U64,
                    name=f"{state_name}.pool.created_at",
                ),
            }
        )
    output.sort(key=lambda entry: entry["pool_id"])
    return output


def _restricted_lp_balances(state: DexState, *, state_name: str) -> list[dict[str, Any]]:
    entries = state.lp_balances.get_all_balances()
    _require_section_bound(entries, name=f"{state_name}.lp_balances")
    output: list[dict[str, Any]] = []
    for (pubkey, pool_id), amount in entries.items():
        canonical_pool_id = _require_identifier(
            pool_id,
            nbytes=32,
            name=f"{state_name}.lp_balance.pool_id",
        )
        if canonical_pool_id not in state.pools:
            raise SpotStateDomainBridgeErrorV1(
                SpotStateDomainBridgeRejectReasonV1.STATE_PROFILE_UNSUPPORTED,
                f"{state_name}.lp_balance references an unknown pool",
            )
        output.append(
            {
                "pubkey": _require_identifier(
                    pubkey,
                    nbytes=48,
                    name=f"{state_name}.lp_balance.pubkey",
                ),
                "pool_id": canonical_pool_id,
                "amount": _require_uint(
                    amount,
                    min_value=1,
                    max_value=_MAX_U128,
                    name=f"{state_name}.lp_balance.amount",
                ),
            }
        )
    output.sort(key=lambda entry: (entry["pubkey"], entry["pool_id"]))
    return output


def _validate_runtime_nonce_transition(
    *,
    pre_state: DexState,
    post_state: DexState,
    sender: str,
    ingress_nonce: int,
) -> None:
    expected_pre = {} if ingress_nonce == 1 else {sender: ingress_nonce - 1}
    expected_post = {sender: ingress_nonce}
    if pre_state.nonces.get_all() != expected_pre:
        raise SpotStateDomainBridgeErrorV1(
            SpotStateDomainBridgeRejectReasonV1.STATE_PROFILE_UNSUPPORTED,
            "runtime pre nonce set is outside the restricted singleton mapping",
        )
    if post_state.nonces.get_all() != expected_post:
        raise SpotStateDomainBridgeErrorV1(
            SpotStateDomainBridgeRejectReasonV1.STATE_PROFILE_UNSUPPORTED,
            "runtime post nonce set is outside the restricted singleton mapping",
        )


def _legacy_app_hash(snapshot: Mapping[str, Any]) -> str:
    return "0x" + hashlib.sha256(canonical_json_bytes(dict(snapshot))).hexdigest()


def _legacy_nonce_root(sender: str, next_nonce: int) -> str:
    sender_bytes = sender.encode("utf-8")
    preimage = bytearray(b"tau_state_proof_nonce_root_v1:")
    preimage.extend((1).to_bytes(4, "big"))
    preimage.extend(len(sender_bytes).to_bytes(4, "big"))
    preimage.extend(sender_bytes)
    preimage.extend(next_nonce.to_bytes(8, "big"))
    return "0x" + hashlib.sha256(bytes(preimage)).hexdigest()


def _restricted_runtime_state_root_v5(state: DexState) -> str:
    return _compute_state_root_python(
        balances=state.balances,
        pools=state.pools,
        lp_balances=state.lp_balances,
        nonces=state.nonces,
        fee_accumulator=state.fee_accumulator,
    )


def _require_section_bound(value: Mapping[object, object], *, name: str) -> None:
    if len(value) > _MAX_SECTION_ENTRIES:
        raise SpotStateDomainBridgeErrorV1(
            SpotStateDomainBridgeRejectReasonV1.STATE_PROFILE_UNSUPPORTED,
            f"{name} exceeds {_MAX_SECTION_ENTRIES} entries",
        )


def _require_identifier(value: object, *, nbytes: int, name: str) -> str:
    if not isinstance(value, str):
        raise SpotStateDomainBridgeErrorV1(
            SpotStateDomainBridgeRejectReasonV1.INPUT_TYPE_INVALID,
            f"{name} must be a string",
        )
    try:
        canonical = canonical_hex_fixed_allow_0x(value, nbytes=nbytes, name=name)
    except (TypeError, ValueError) as exc:
        raise SpotStateDomainBridgeErrorV1(
            SpotStateDomainBridgeRejectReasonV1.STATE_PROFILE_UNSUPPORTED,
            f"{name} is not a canonical identifier",
        ) from exc
    if value != canonical:
        raise SpotStateDomainBridgeErrorV1(
            SpotStateDomainBridgeRejectReasonV1.STATE_PROFILE_UNSUPPORTED,
            f"{name} must use canonical lowercase 0x encoding",
        )
    return canonical


def _require_root(value: object, *, name: str) -> str:
    return _require_identifier(value, nbytes=32, name=name)


def _require_uint(
    value: object,
    *,
    max_value: int,
    name: str,
    min_value: int = 0,
) -> int:
    if (
        not isinstance(value, int)
        or isinstance(value, bool)
        or value < min_value
        or value > max_value
    ):
        raise SpotStateDomainBridgeErrorV1(
            SpotStateDomainBridgeRejectReasonV1.STATE_PROFILE_UNSUPPORTED,
            f"{name} is outside the restricted integer range",
        )
    return value
