"""
Tau Testnet Alpha app-bridge plugin for ZenoDEX.

This module implements the generic `external/tau-testnet/app_bridge.py` plugin API:
  apply_app_tx(...)

It applies DEX operations from a Tau transaction's `operations` dict:
  - "5": intents (list)
  - "6": settlement (object) [optional if allow_missing_settlement]
  - "7": faucet (object) [optional, test-only; requires TAU_DEX_FAUCET=1]
  - "8": perps (list) [optional; isolated markets require an operator key for admin actions]
  - "9": token ops (list) [optional; managed assets may forbid generic supply changes]
  - "10": proof mining claim (object) [optional; bound to verified DEX proof context]
  - "11": zUSD monetary ops (list) [optional; collateral, mint/repay, stability pool]

Legacy key aliases are also accepted when invoking the plugin directly:
  - "2" -> intents, "3" -> settlement, "4" -> faucet, "5" -> perps
"""

from __future__ import annotations

import hashlib
import json
import math
import os
from dataclasses import replace
from typing import Any, Dict, Mapping, Optional, Tuple

from ..core.dex import DexState
from ..core.fixed_width import U256_MAX
from ..core.managed_asset_policy import (
    AssetOperationV1,
    ManagedAssetPolicyV1,
    build_zusd_managed_asset_policy,
    check_managed_asset_operation,
)
from ..core.perp_tau_ingress_stream import evaluate_perp_tau_ingress_stream
from ..state.balances import NATIVE_ASSET, BalanceTable
from ..state.canonical import canonical_hex_fixed_allow_0x, canonical_json_bytes
from ..state.lp import LPTable
from ..state.nonces import NonceTable
from .dex_engine import DexEngineConfig, apply_ops
from .dex_snapshot import snapshot_from_state, state_from_snapshot
from .perp_engine import PerpEngineConfig, apply_perp_ops
from .proof_mining_runtime import (
    ProofMiningRuntimeState,
    apply_proof_mining_claim,
    initialize_proof_mining_runtime_state,
    proof_mining_runtime_state_from_obj,
    proof_mining_runtime_state_to_obj,
    sync_proof_mining_runtime_balance,
)
from .proof_verifier import ProofVerifierConfig
from .zusd_monetary_bridge import (
    ZUSDMonetaryConfig,
    ZUSDMonetaryState,
    apply_zusd_monetary_ops,
    zusd_monetary_state_from_obj,
    zusd_monetary_state_to_obj,
)

_DEX_INTENTS_KEY = "5"
_DEX_SETTLEMENT_KEY = "6"
_DEX_FAUCET_KEY = "7"
_PERP_OPS_KEY = "8"
_TOKEN_OPS_KEY = "9"
_PROOF_MINING_OPS_KEY = "10"
_ZUSD_MONETARY_OPS_KEY = "11"

_LEGACY_DEX_INTENTS_KEY = "2"
_LEGACY_DEX_SETTLEMENT_KEY = "3"
_LEGACY_DEX_FAUCET_KEY = "4"
_LEGACY_PERP_OPS_KEY = "5"

_APP_STATE_SCHEMA = "zenodex/tau_app_state/v1"
_APP_STATE_VERSION = 1
_MAX_APP_STATE_JSON_BYTES = 6_000_000


def _canonical_state_and_hash(
    state: DexState,
    *,
    proof_mining_state: Optional[ProofMiningRuntimeState] = None,
    zusd_monetary_state: Optional[ZUSDMonetaryState] = None,
) -> Tuple[str, str]:
    snap = snapshot_from_state(state)
    if proof_mining_state is None and zusd_monetary_state is None:
        canonical = snap.canonical_bytes()
        return canonical.decode("utf-8"), hashlib.sha256(canonical).hexdigest()
    payload = {
        "schema": _APP_STATE_SCHEMA,
        "version": _APP_STATE_VERSION,
        "dex_state": snap.data,
        "proof_mining": None if proof_mining_state is None else proof_mining_runtime_state_to_obj(proof_mining_state),
        "zusd_monetary": (
            None if zusd_monetary_state is None else zusd_monetary_state_to_obj(zusd_monetary_state)
        ),
    }
    canonical = canonical_json_bytes(payload)
    return canonical.decode("utf-8"), hashlib.sha256(canonical).hexdigest()


def _bool_env(name: str, *, default: bool) -> bool:
    raw = os.environ.get(name)
    if raw is None or not raw.strip():
        return bool(default)
    v = raw.strip().lower()
    if v in {"1", "true", "yes", "on"}:
        return True
    if v in {"0", "false", "no", "off"}:
        return False
    raise ValueError(
        f"{name} must be one of 1,true,yes,on,0,false,no,off; got {raw!r}"
    )


def _float_env(name: str, *, default: float, minimum: float, maximum: float) -> float:
    raw = os.environ.get(name, "").strip()
    if not raw:
        out = float(default)
    else:
        try:
            out = float(raw)
        except ValueError as exc:
            raise ValueError(f"{name} must be a finite float") from exc
    if not math.isfinite(out):
        raise ValueError(f"{name} must be finite")
    if out < minimum:
        raise ValueError(f"{name} must be >= {minimum}")
    if out > maximum:
        raise ValueError(f"{name} must be <= {maximum}")
    return float(out)


def _int_env(name: str, *, default: int, minimum: int = 0, maximum: Optional[int] = None) -> int:
    raw = os.environ.get(name, "").strip()
    if not raw:
        return int(default)
    try:
        out = int(raw)
    except Exception as exc:
        raise ValueError(f"{name} must be an integer") from exc
    if out < minimum:
        raise ValueError(f"{name} must be >= {minimum}")
    if maximum is not None and out > maximum:
        raise ValueError(f"{name} must be <= {maximum}")
    return out


def _int_env_alias(primary: str, fallback: str, *, default: int, minimum: int = 0, maximum: Optional[int] = None) -> int:
    if os.environ.get(primary, "").strip():
        return _int_env(primary, default=default, minimum=minimum, maximum=maximum)
    return _int_env(fallback, default=default, minimum=minimum, maximum=maximum)


def _maybe_decode_custom_stream_value(value: Any) -> Any:
    """
    Upstream tau-testnet restricts custom operation streams (keys beyond 0/1) to
    `str|int` (or lists thereof). Our client encodes structured ops as canonical
    JSON strings; this helper decodes those strings back to objects.
    """
    if isinstance(value, list):
        return [_maybe_decode_custom_stream_value(entry) for entry in value]
    if not isinstance(value, str):
        return value
    raw = value.strip()
    if not raw:
        return value
    if raw[0] not in "{[":
        return value
    try:
        parsed = json.loads(raw)
    except Exception:
        return value
    if isinstance(parsed, (dict, list)):
        return parsed
    return value


def _copy_balance_table(balances: BalanceTable) -> BalanceTable:
    copied = BalanceTable()
    for (pubkey, asset), amount in balances.get_all_balances().items():
        copied.set(pubkey, asset, int(amount))
    return copied


def _copy_nonce_table(nonces: NonceTable) -> NonceTable:
    copied = NonceTable()
    for pubkey, last_nonce in nonces.get_all().items():
        copied.set_last(pubkey, int(last_nonce))
    return copied


def _require_mapping(value: Any, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be an object")
    return value


def _reject_unknown_fields(obj: Mapping[str, Any], *, allowed: set[str], name: str) -> None:
    extra = sorted(set(obj.keys()) - set(allowed))
    if extra:
        raise ValueError(f"{name} unknown fields: {extra}")


def _parse_cmd_json_env(name: str) -> Optional[list[str]]:
    raw = os.environ.get(name, "").strip()
    if not raw:
        return None
    obj = json.loads(raw)
    if not isinstance(obj, list) or not obj:
        raise ValueError(f"{name} must be a non-empty JSON array")
    cmd: list[str] = []
    for idx, entry in enumerate(obj):
        if not isinstance(entry, str) or not entry:
            raise ValueError(f"{name}[{idx}] must be a non-empty string")
        cmd.append(str(entry))
    return cmd


def _build_proof_verifier_config() -> ProofVerifierConfig:
    cmd = _parse_cmd_json_env("TAU_DEX_PROOF_VERIFIER_CMD_JSON")
    timeout_s = _float_env(
        "TAU_DEX_PROOF_VERIFIER_TIMEOUT_S",
        default=10.0,
        minimum=0.1,
        maximum=120.0,
    )
    allow_path_lookup = _bool_env("TAU_DEX_PROOF_VERIFIER_ALLOW_PATH_LOOKUP", default=False)
    return ProofVerifierConfig(
        enabled=bool(cmd),
        verifier_cmd=cmd,
        allow_path_lookup=bool(allow_path_lookup),
        timeout_s=float(timeout_s),
    )


def _load_state(app_state_json: str) -> Tuple[DexState, Optional[ProofMiningRuntimeState], Optional[ZUSDMonetaryState]]:
    raw = (app_state_json or "").strip()
    if not raw:
        return DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable()), None, None
    if len(raw.encode("utf-8")) > _MAX_APP_STATE_JSON_BYTES:
        raise ValueError("app_state_json too large")
    try:
        obj = json.loads(raw)
    except Exception as exc:
        raise ValueError(f"invalid app_state_json: {exc}") from exc
    try:
        if isinstance(obj, Mapping) and any(key in obj for key in ("schema", "dex_state", "proof_mining")):
            _reject_unknown_fields(
                obj,
                allowed={"schema", "version", "dex_state", "proof_mining", "zusd_monetary"},
                name="app_state",
            )
            schema = obj.get("schema")
            if schema != _APP_STATE_SCHEMA:
                raise ValueError(f"unsupported app_state schema: {schema!r}")
            version = obj.get("version", _APP_STATE_VERSION)
            if not isinstance(version, int) or isinstance(version, bool) or version <= 0:
                raise ValueError("app_state.version must be a positive int")
            if version != _APP_STATE_VERSION:
                raise ValueError(f"unsupported app_state version: {version}")
            dex_state = state_from_snapshot(_require_mapping(obj.get("dex_state"), name="app_state.dex_state"))
            proof_obj = obj.get("proof_mining")
            proof_state = (
                None
                if proof_obj is None
                else proof_mining_runtime_state_from_obj(_require_mapping(proof_obj, name="app_state.proof_mining"))
            )
            zusd_obj = obj.get("zusd_monetary")
            zusd_state = (
                None
                if zusd_obj is None
                else zusd_monetary_state_from_obj(_require_mapping(zusd_obj, name="app_state.zusd_monetary"))
            )
            return dex_state, proof_state, zusd_state
        return state_from_snapshot(obj), None, None
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
    if not isinstance(amount, int) or isinstance(amount, bool) or amount <= 0:
        return None, f"faucet.mint[{index}] amount must be a positive int"
    try:
        decoded_pk = _canonical_pubkey(pk, name=f"faucet.mint[{index}].pubkey")
        decoded_asset = canonical_hex_fixed_allow_0x(asset, nbytes=32, name=f"faucet.mint[{index}].asset")
    except Exception as exc:
        return None, str(exc)
    if decoded_asset == NATIVE_ASSET:
        return None, "faucet cannot mint native asset"

    return (decoded_pk, decoded_asset, int(amount)), None


def _validate_chain_balances(chain_balances: Dict[str, int]) -> None:
    """Reject ambiguous or non-exact host-native custody inputs."""

    seen: set[str] = set()
    for external_pubkey, amount in chain_balances.items():
        canonical_pubkey = _canonical_pubkey(
            external_pubkey,
            name="chain_balances pubkey",
        )
        if canonical_pubkey in seen:
            raise ValueError("chain_balances contains duplicate decoded pubkey identity")
        seen.add(canonical_pubkey)
        if type(amount) is not int:
            raise TypeError("chain_balances amount must be an exact int")
        if amount < 0 or amount > U256_MAX:
            raise ValueError("chain_balances amount must be within U256")


def _sync_native_balances(state: DexState, *, chain_balances: Dict[str, int]) -> DexState:
    balances_copy = _copy_balance_table(state.balances)

    # Drop any existing native entries from stored snapshot.
    for (pk, asset), _amount in list(balances_copy.get_all_balances().items()):
        if asset == NATIVE_ASSET:
            balances_copy.set(pk, asset, 0)

    for pk in sorted(chain_balances):
        amount = chain_balances[pk]
        canonical_pk = _canonical_pubkey(pk, name="chain_balances pubkey")
        if amount == 0:
            continue
        balances_copy.set(canonical_pk, NATIVE_ASSET, amount)

    return replace(state, balances=balances_copy)


def _apply_faucet(
    state: DexState,
    faucet_op: Any,
    *,
    allow: bool,
    managed_asset_policy: ManagedAssetPolicyV1,
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
        if parsed is None:
            return False, state, f"internal faucet parse error at index {i}"
        pk, asset, amount = parsed
        managed_asset_reject = check_managed_asset_operation(
            policy=managed_asset_policy,
            asset_id=asset,
            operation=AssetOperationV1.FAUCET_MINT,
        )
        if managed_asset_reject is not None:
            return False, state, managed_asset_reject.message()

        current = balances_copy.get(pk, asset)
        balances_copy.set(pk, asset, int(current) + int(amount))

    next_state = replace(state, balances=balances_copy)
    return True, next_state, None


def _balances_patch_for_native(*, before: Dict[str, int], after_state: DexState) -> Dict[str, int]:
    _validate_chain_balances(before)
    out: Dict[str, int] = {}
    external_key_by_canonical: Dict[str, str] = {}
    for pk in sorted(before):
        canonical_pk = _canonical_pubkey(pk, name="chain_balances pubkey")
        external_key_by_canonical[canonical_pk] = pk

    keys = set(before.keys())
    # Include any addresses that appear in the DEX snapshot (native).
    for (pk, asset), _amount in after_state.balances.get_all_balances().items():
        if asset == NATIVE_ASSET:
            keys.add(external_key_by_canonical.get(pk, pk))

    for pk in sorted(keys):
        old = before.get(pk, 0)
        lookup_pk = _canonical_pubkey(pk, name="chain_balances pubkey")
        new = int(after_state.balances.get(lookup_pk, NATIVE_ASSET))
        if new != old:
            out[pk] = new
    return out


def _canonical_pubkey(value: Any, *, name: str) -> str:
    if not isinstance(value, str):
        raise ValueError(f"{name} must be a 48-byte hex pubkey string")
    return canonical_hex_fixed_allow_0x(value, nbytes=48, name=name)


def _canonical_token_asset(value: Any, *, name: str) -> str:
    if not isinstance(value, str):
        raise ValueError(f"{name} must be a 32-byte hex asset string")
    asset = canonical_hex_fixed_allow_0x(value, nbytes=32, name=name)
    if asset == NATIVE_ASSET:
        raise ValueError("token stream does not support native asset")
    return asset


def _canonical_tx_sender_pubkey_for_engine(value: Any) -> str:
    if value == "":
        return ""
    return _canonical_pubkey(value, name="tx_sender_pubkey")


def _require_u32_positive(value: Any, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value <= 0:
        raise ValueError(f"{name} must be a positive int")
    if value > 0xFFFFFFFF:
        raise ValueError(f"{name} must fit in u32")
    return int(value)


def _token_sender_nonce_key(sender_pubkey: str) -> str:
    # Domain-separated pseudopubkey avoids nonce coupling with DEX/perps streams.
    payload = b"zenodex:tau_token_nonce:v1\x00" + sender_pubkey.encode("ascii")
    return "0x" + hashlib.sha384(payload).hexdigest()


def _resolve_token_operator_pubkey() -> Optional[str]:
    raw = os.environ.get("TAU_DEX_TOKEN_OPERATOR_PUBKEY", "").strip()
    if not raw:
        raw = os.environ.get("TAU_DEX_OPERATOR_PUBKEY", "").strip()
    if not raw:
        return None
    return _canonical_pubkey(raw, name="TAU_DEX_TOKEN_OPERATOR_PUBKEY")


def _resolve_proof_mining_pool_pubkey() -> Optional[str]:
    raw = os.environ.get("TAU_DEX_PROOF_MINING_POOL_PUBKEY", "").strip()
    if not raw:
        return None
    return _canonical_pubkey(raw, name="TAU_DEX_PROOF_MINING_POOL_PUBKEY")


def _enforce_deadline(*, op: Mapping[str, Any], block_timestamp: int, op_name: str) -> Optional[str]:
    deadline_raw = op.get("deadline")
    if deadline_raw is None:
        return None
    try:
        deadline = _require_u32_positive(deadline_raw, name=f"{op_name}.deadline")
    except Exception as exc:
        return str(exc)
    if int(block_timestamp) > int(deadline):
        return f"{op_name}.deadline expired"
    return None


def _apply_token_ops(
    state: DexState,
    token_ops: Any,
    *,
    tx_sender_pubkey: str,
    block_timestamp: int,
    managed_asset_policy: ManagedAssetPolicyV1,
) -> Tuple[bool, DexState, Optional[str]]:
    if token_ops is None:
        return True, state, None
    if not isinstance(token_ops, list):
        return False, state, "token op stream must be a list"
    if not token_ops:
        return True, state, None

    try:
        sender = _canonical_pubkey(tx_sender_pubkey, name="tx_sender_pubkey")
    except Exception as exc:
        return False, state, str(exc)

    balances = _copy_balance_table(state.balances)
    nonces = _copy_nonce_table(state.nonces)
    nonce_key = _token_sender_nonce_key(sender)

    for i, raw in enumerate(token_ops):
        if not isinstance(raw, Mapping):
            return False, state, f"token op[{i}] must be an object"
        op = dict(raw)
        module = str(op.get("module", "TauToken"))
        if module != "TauToken":
            return False, state, f"token op[{i}] module must be TauToken"
        action = str(op.get("action", "")).strip().lower()
        if action not in {"transfer", "mint", "burn"}:
            return False, state, f"token op[{i}] action unsupported: {action!r}"

        try:
            nonce = _require_u32_positive(op.get("nonce"), name=f"token op[{i}].nonce")
        except Exception as exc:
            return False, state, str(exc)
        expected = int(nonces.get_last(nonce_key)) + 1
        if nonce != expected:
            return False, state, f"token op[{i}] nonce invalid (expected {expected}, got {nonce})"

        deadline_err = _enforce_deadline(op=op, block_timestamp=int(block_timestamp), op_name=f"token op[{i}]")
        if deadline_err is not None:
            return False, state, deadline_err

        if action == "transfer":
            allowed = {
                "module",
                "version",
                "action",
                "asset",
                "to_pubkey",
                "amount",
                "nonce",
                "deadline",
                "sender_pubkey",
            }
            extra = set(op.keys()) - allowed
            if extra:
                return False, state, f"token op[{i}] unknown fields: {sorted(extra)}"
            sender_raw = op.get("sender_pubkey")
            if sender_raw is not None:
                try:
                    sender_in_op = _canonical_pubkey(sender_raw, name=f"token op[{i}].sender_pubkey")
                except Exception as exc:
                    return False, state, str(exc)
                if sender_in_op != sender:
                    return False, state, f"token op[{i}] sender_pubkey mismatch"
            try:
                asset = _canonical_token_asset(op.get("asset"), name=f"token op[{i}].asset")
                to_pubkey = _canonical_pubkey(op.get("to_pubkey"), name=f"token op[{i}].to_pubkey")
                amount = _require_u32_positive(op.get("amount"), name=f"token op[{i}].amount")
            except Exception as exc:
                return False, state, str(exc)
            managed_asset_reject = check_managed_asset_operation(
                policy=managed_asset_policy,
                asset_id=asset,
                operation=AssetOperationV1.TRANSFER,
            )
            if managed_asset_reject is not None:
                return False, state, managed_asset_reject.message()
            sender_balance = int(balances.get(sender, asset))
            if sender_balance < amount:
                return False, state, f"token op[{i}] insufficient balance"
            balances.set(sender, asset, sender_balance - amount)
            recipient_balance = int(balances.get(to_pubkey, asset))
            balances.set(to_pubkey, asset, recipient_balance + amount)

        elif action == "mint":
            allowed = {
                "module",
                "version",
                "action",
                "asset",
                "to_pubkey",
                "amount",
                "nonce",
                "deadline",
                "operator_pubkey",
            }
            extra = set(op.keys()) - allowed
            if extra:
                return False, state, f"token op[{i}] unknown fields: {sorted(extra)}"
            operator_pk = _resolve_token_operator_pubkey()
            if operator_pk is None:
                return False, state, "token mint disabled (set TAU_DEX_TOKEN_OPERATOR_PUBKEY)"
            if sender != operator_pk:
                return False, state, "token mint requires operator sender"
            operator_in_op = op.get("operator_pubkey")
            if operator_in_op is not None:
                try:
                    op_pk = _canonical_pubkey(operator_in_op, name=f"token op[{i}].operator_pubkey")
                except Exception as exc:
                    return False, state, str(exc)
                if op_pk != sender:
                    return False, state, f"token op[{i}] operator_pubkey mismatch"
            try:
                asset = _canonical_token_asset(op.get("asset"), name=f"token op[{i}].asset")
                to_pubkey = _canonical_pubkey(op.get("to_pubkey"), name=f"token op[{i}].to_pubkey")
                amount = _require_u32_positive(op.get("amount"), name=f"token op[{i}].amount")
            except Exception as exc:
                return False, state, str(exc)
            managed_asset_reject = check_managed_asset_operation(
                policy=managed_asset_policy,
                asset_id=asset,
                operation=AssetOperationV1.GENERIC_MINT,
            )
            if managed_asset_reject is not None:
                return False, state, managed_asset_reject.message()
            recipient_balance = int(balances.get(to_pubkey, asset))
            balances.set(to_pubkey, asset, recipient_balance + amount)

        else:
            allowed = {
                "module",
                "version",
                "action",
                "asset",
                "amount",
                "nonce",
                "deadline",
                "sender_pubkey",
            }
            extra = set(op.keys()) - allowed
            if extra:
                return False, state, f"token op[{i}] unknown fields: {sorted(extra)}"
            sender_raw = op.get("sender_pubkey")
            if sender_raw is not None:
                try:
                    sender_in_op = _canonical_pubkey(sender_raw, name=f"token op[{i}].sender_pubkey")
                except Exception as exc:
                    return False, state, str(exc)
                if sender_in_op != sender:
                    return False, state, f"token op[{i}] sender_pubkey mismatch"
            try:
                asset = _canonical_token_asset(op.get("asset"), name=f"token op[{i}].asset")
                amount = _require_u32_positive(op.get("amount"), name=f"token op[{i}].amount")
            except Exception as exc:
                return False, state, str(exc)
            managed_asset_reject = check_managed_asset_operation(
                policy=managed_asset_policy,
                asset_id=asset,
                operation=AssetOperationV1.GENERIC_BURN,
            )
            if managed_asset_reject is not None:
                return False, state, managed_asset_reject.message()
            sender_balance = int(balances.get(sender, asset))
            if sender_balance < amount:
                return False, state, f"token op[{i}] insufficient balance"
            balances.set(sender, asset, sender_balance - amount)

        nonces.set_last(nonce_key, nonce)

    return True, replace(state, balances=balances, nonces=nonces), None


def _looks_like_dex_intents(raw: Any) -> bool:
    if not isinstance(raw, list):
        return False
    if not raw:
        return True

    first = raw[0]
    candidate: Any = None
    if isinstance(first, dict):
        candidate = first
    elif isinstance(first, (list, tuple)) and first and isinstance(first[0], dict):
        candidate = first[0]
    if not isinstance(candidate, dict):
        return False

    module = candidate.get("module")
    if module is None:
        return "kind" in candidate
    return str(module) == "TauSwap"


def _looks_like_perp_ops(raw: Any) -> bool:
    if not isinstance(raw, list):
        return False
    if not raw:
        return True
    first = raw[0]
    if not isinstance(first, dict):
        return False
    module = first.get("module")
    if module is None:
        return "action" in first
    return str(module) == "TauPerp"


def _select_dex_ops(operations: Mapping[str, Any]) -> Dict[str, Any]:
    out: Dict[str, Any] = {}
    if _LEGACY_DEX_INTENTS_KEY in operations:
        out[_LEGACY_DEX_INTENTS_KEY] = operations.get(_LEGACY_DEX_INTENTS_KEY)
    elif _DEX_INTENTS_KEY in operations and _looks_like_dex_intents(operations.get(_DEX_INTENTS_KEY)):
        # Remap upstream-safe stream "5" to the internal DEX adapter schema.
        out[_LEGACY_DEX_INTENTS_KEY] = operations.get(_DEX_INTENTS_KEY)

    if _LEGACY_DEX_SETTLEMENT_KEY in operations:
        out[_LEGACY_DEX_SETTLEMENT_KEY] = operations.get(_LEGACY_DEX_SETTLEMENT_KEY)
    elif _DEX_SETTLEMENT_KEY in operations:
        # Remap upstream-safe stream "6" to the internal DEX adapter schema.
        out[_LEGACY_DEX_SETTLEMENT_KEY] = operations.get(_DEX_SETTLEMENT_KEY)
    return out


def _select_perp_ops(operations: Mapping[str, Any]) -> Dict[str, Any]:
    out: Dict[str, Any] = {}
    legacy_candidate = operations.get(_LEGACY_PERP_OPS_KEY)
    selection = evaluate_perp_tau_ingress_stream(
        upstream_stream_present=_PERP_OPS_KEY in operations,
        legacy_stream_present=_LEGACY_PERP_OPS_KEY in operations,
        legacy_dex_stream_present=_LEGACY_DEX_INTENTS_KEY in operations,
        legacy_candidate_dex_like=_looks_like_dex_intents(legacy_candidate),
        legacy_candidate_perp_like=_looks_like_perp_ops(legacy_candidate),
    )
    if selection.upstream_stream_selected:
        out[_LEGACY_PERP_OPS_KEY] = operations.get(_PERP_OPS_KEY)
        return out
    if selection.legacy_fallback_used:
        # Legacy fallback for direct plugin tests/tooling that still use stream "5" for perps.
        out[_LEGACY_PERP_OPS_KEY] = legacy_candidate
    return out


def _select_token_ops(operations: Mapping[str, Any]) -> Dict[str, Any]:
    out: Dict[str, Any] = {}
    if _TOKEN_OPS_KEY in operations:
        out[_TOKEN_OPS_KEY] = operations.get(_TOKEN_OPS_KEY)
    return out


def _select_proof_mining_ops(operations: Mapping[str, Any]) -> Dict[str, Any]:
    out: Dict[str, Any] = {}
    if _PROOF_MINING_OPS_KEY in operations:
        out[_PROOF_MINING_OPS_KEY] = operations.get(_PROOF_MINING_OPS_KEY)
    return out


def _select_zusd_monetary_ops(operations: Mapping[str, Any]) -> Dict[str, Any]:
    out: Dict[str, Any] = {}
    if _ZUSD_MONETARY_OPS_KEY in operations:
        out[_ZUSD_MONETARY_OPS_KEY] = operations.get(_ZUSD_MONETARY_OPS_KEY)
    return out


def _reserved_stream_selection_error(operations: Mapping[str, Any]) -> Optional[str]:
    if _LEGACY_DEX_INTENTS_KEY in operations and _DEX_INTENTS_KEY in operations:
        if _looks_like_dex_intents(operations.get(_DEX_INTENTS_KEY)):
            return "ambiguous DEX intent streams: both 2 and 5 are present"
    if _LEGACY_DEX_SETTLEMENT_KEY in operations and _DEX_SETTLEMENT_KEY in operations:
        return "ambiguous DEX settlement streams: both 3 and 6 are present"
    if _LEGACY_DEX_FAUCET_KEY in operations and _DEX_FAUCET_KEY in operations:
        return "ambiguous faucet streams: both 4 and 7 are present"

    if _DEX_INTENTS_KEY not in operations:
        return None
    stream5 = operations.get(_DEX_INTENTS_KEY)
    if _looks_like_dex_intents(stream5):
        return None
    if _looks_like_perp_ops(stream5):
        if _LEGACY_DEX_INTENTS_KEY in operations and _PERP_OPS_KEY not in operations:
            return "legacy stream 5 perps conflict with legacy DEX stream 2"
        return None
    return "stream 5 must contain TauSwap intents or legacy TauPerp ops"


def _apply_proof_mining_op(
    *,
    state: DexState,
    proof_mining_state: Optional[ProofMiningRuntimeState],
    proof_mining_op: Any,
    proof_mining_context: Any,
    tx_sender_pubkey: str,
    chain_balances: Mapping[str, int],
) -> Tuple[bool, DexState, Optional[ProofMiningRuntimeState], Optional[str]]:
    if proof_mining_op is None:
        return True, state, proof_mining_state, None
    if proof_mining_context is None:
        return False, state, proof_mining_state, "proof mining claim requires verified DEX proof context"
    if not isinstance(proof_mining_op, Mapping):
        return False, state, proof_mining_state, "proof mining op must be an object"
    op = dict(proof_mining_op)
    module = str(op.get("module", "ZenoProofMining"))
    action = str(op.get("action", "")).strip().lower()
    if module != "ZenoProofMining":
        return False, state, proof_mining_state, "proof mining op module must be ZenoProofMining"
    if action != "submit_proof":
        return False, state, proof_mining_state, "proof mining op action unsupported"
    extra = set(op.keys()) - {"module", "version", "action", "claim", "recipient_pubkey"}
    if extra:
        return False, state, proof_mining_state, f"proof mining op unknown fields: {sorted(extra)}"
    claim_artifact = op.get("claim")
    if not isinstance(claim_artifact, Mapping):
        return False, state, proof_mining_state, "proof mining op claim must be an object"
    reward_pool_pubkey = _resolve_proof_mining_pool_pubkey()
    if reward_pool_pubkey is None:
        return False, state, proof_mining_state, "proof mining disabled (set TAU_DEX_PROOF_MINING_POOL_PUBKEY)"
    try:
        sender = _canonical_pubkey(tx_sender_pubkey, name="tx_sender_pubkey")
    except Exception as exc:
        return False, state, proof_mining_state, str(exc)
    recipient_raw = op.get("recipient_pubkey")
    if recipient_raw is not None:
        try:
            recipient = _canonical_pubkey(recipient_raw, name="proof mining recipient_pubkey")
        except Exception as exc:
            return False, state, proof_mining_state, str(exc)
        if recipient != sender:
            return False, state, proof_mining_state, "proof mining recipient_pubkey mismatch"
    try:
        claim_body = _require_mapping(claim_artifact.get("body"), name="proof mining claim.body")
        winner = _require_mapping(claim_body.get("winner"), name="proof mining claim.body.winner")
    except Exception as exc:
        return False, state, proof_mining_state, str(exc)
    try:
        winner_pubkey = _canonical_pubkey(winner.get("miner_id"), name="proof mining claim winner.miner_id")
    except Exception as exc:
        return False, state, proof_mining_state, f"proof mining reward requires canonical winner.miner_id: {exc}"
    if winner_pubkey != sender:
        return False, state, proof_mining_state, "proof mining winner.miner_id mismatch"
    claim_proposal_hash = str(claim_body.get("proposal_hash", ""))
    if claim_proposal_hash != str(getattr(proof_mining_context, "proposal_hash", "")):
        return False, state, proof_mining_state, "proof mining claim proposal_hash mismatch"
    actual_pool_balance = int(chain_balances.get(reward_pool_pubkey, 0))
    if actual_pool_balance < 0:
        return False, state, proof_mining_state, "reward pool chain balance must be non-negative"
    runtime_state = proof_mining_state
    if runtime_state is None:
        try:
            runtime_state = initialize_proof_mining_runtime_state(
                reward_pool_pubkey=reward_pool_pubkey,
                reward_pool_balance=actual_pool_balance,
                claim_artifact=claim_artifact,
            )
        except Exception as exc:
            return False, state, proof_mining_state, str(exc)
    if runtime_state.reward_pool_pubkey != reward_pool_pubkey:
        return False, state, proof_mining_state, "proof mining reward pool pubkey mismatch"
    try:
        runtime_state = sync_proof_mining_runtime_balance(
            runtime_state=runtime_state,
            actual_reward_pool_balance=actual_pool_balance,
        )
    except Exception as exc:
        return False, state, proof_mining_state, str(exc)
    try:
        next_runtime_state, result = apply_proof_mining_claim(
            runtime_state=runtime_state,
            claim_artifact=claim_artifact,
            actual_reward_pool_balance=actual_pool_balance,
            proof_mining_context=proof_mining_context,
        )
    except Exception as exc:
        return False, state, proof_mining_state, str(exc)
    if not result.ok or result.effects is None:
        return False, state, proof_mining_state, result.error_message or "proof mining manager rejected"
    reward_amount = int(result.effects.get("reward_amount", 0))
    if reward_amount <= 0:
        return False, state, proof_mining_state, "proof mining reward_amount invalid"
    balances = _copy_balance_table(state.balances)
    pool_balance = int(balances.get(reward_pool_pubkey, NATIVE_ASSET))
    if pool_balance != actual_pool_balance:
        return False, state, proof_mining_state, "reward pool native balance out of sync"
    recipient_balance = int(balances.get(sender, NATIVE_ASSET))
    if pool_balance < reward_amount:
        return False, state, proof_mining_state, "reward pool insufficient native balance"
    balances.set(reward_pool_pubkey, NATIVE_ASSET, pool_balance - reward_amount)
    balances.set(sender, NATIVE_ASSET, recipient_balance + reward_amount)
    return True, replace(state, balances=balances), next_runtime_state, None


def _build_perp_engine_config(*, chain_id: str) -> PerpEngineConfig:
    operator_pubkey = os.environ.get("TAU_DEX_OPERATOR_PUBKEY") or os.environ.get("TAU_DEX_PERP_OPERATOR_PUBKEY")
    oracle_pubkey = os.environ.get("TAU_DEX_PERP_ORACLE_PUBKEY") or os.environ.get("TAU_DEX_ORACLE_PUBKEY")
    allow_isolated = _bool_env("TAU_DEX_ALLOW_ISOLATED_PERPS", default=False)

    def _oracle_adapter_bridge_verifier(bridge):
        from tools.zenodex_oracle_aggregate_adapter import (  # pylint: disable=import-outside-toplevel
            verify_aggregate_adapter_bridge,
        )

        return verify_aggregate_adapter_bridge(bridge)

    return PerpEngineConfig(
        operator_pubkey=(operator_pubkey or "").strip() or None,
        chain_id=chain_id,
        oracle_pubkey=(oracle_pubkey or "").strip() or None,
        allow_isolated_markets=bool(allow_isolated),
        oracle_adapter_bridge_verifier=_oracle_adapter_bridge_verifier,
        require_oracle_adapter_for_clearinghouse_settle_epoch=_bool_env(
            "TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH",
            default=False,
        ),
        require_oracle_authorization_for_clearinghouse_settle_epoch=_bool_env(
            "TAU_DEX_REQUIRE_ORACLE_AUTHORIZATION_FOR_CLEARINGHOUSE_SETTLE_EPOCH",
            default=False,
        ),
        require_oracle_adapter_for_isolated_settle_epoch=_bool_env(
            "TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_ISOLATED_SETTLE_EPOCH",
            default=False,
        ),
        require_oracle_adapter_for_isolated_partial_liquidate=_bool_env(
            "TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_ISOLATED_PARTIAL_LIQUIDATE",
            default=False,
        ),
        require_oracle_authorization_for_isolated_settle_epoch=_bool_env(
            "TAU_DEX_REQUIRE_ORACLE_AUTHORIZATION_FOR_ISOLATED_SETTLE_EPOCH",
            default=False,
        ),
    )


def _build_zusd_monetary_config(*, chain_id: str) -> ZUSDMonetaryConfig:
    oracle_pubkey = os.environ.get("TAU_DEX_ZUSD_ORACLE_PUBKEY") or os.environ.get("TAU_DEX_ORACLE_PUBKEY")
    asset_id = os.environ.get("TAU_DEX_ZUSD_ASSET_ID", "").strip() or None
    return ZUSDMonetaryConfig(
        chain_id=chain_id,
        oracle_pubkey=(oracle_pubkey or "").strip() or None,
        asset_id=asset_id,
        liquidation_gas_comp_fixed_collateral_e8=_int_env_alias(
            "TAU_DEX_ZUSD_LIQUIDATION_FEE_COMP_FIXED_COLLATERAL_E8",
            "TAU_DEX_ZUSD_LIQUIDATION_GAS_COMP_FIXED_COLLATERAL_E8",
            default=0,
        ),
        liquidation_gas_comp_bps=_int_env_alias(
            "TAU_DEX_ZUSD_LIQUIDATION_FEE_COMP_BPS",
            "TAU_DEX_ZUSD_LIQUIDATION_GAS_COMP_BPS",
            default=0,
            maximum=10_000,
        ),
    )


def apply_app_tx(
    *,
    app_state_json: str,
    chain_balances: Any,
    operations: Any,
    tx_sender_pubkey: str,
    block_timestamp: int,
) -> Tuple[bool, str, str, Optional[Dict[str, int]], Optional[str]]:
    if not isinstance(operations, dict):
        return False, app_state_json, "", None, "operations must be an object"
    if not isinstance(chain_balances, dict):
        return False, app_state_json, "", None, "chain_balances must be an object"
    try:
        _validate_chain_balances(chain_balances)
    except (TypeError, ValueError) as exc:
        return False, app_state_json, "", None, str(exc)

    decoded_ops: Dict[str, Any] = {}
    for k, v in operations.items():
        key = str(k)
        if key in ("0", "1"):
            decoded_ops[key] = v
        else:
            decoded_ops[key] = _maybe_decode_custom_stream_value(v)
    operations = decoded_ops

    try:
        allow_faucet = _bool_env("TAU_DEX_FAUCET", default=False)
        allow_missing_settlement = _bool_env("TAU_DEX_ALLOW_MISSING_SETTLEMENT", default=True)
        require_intent_sigs = _bool_env("TAU_DEX_REQUIRE_INTENT_SIGS", default=True)
        allow_external_tools = _bool_env("TAU_DEX_ALLOW_EXTERNAL_TOOLS", default=False)
        consensus_mode = _bool_env("TAU_DEX_CONSENSUS_MODE", default=True)
    except ValueError as exc:
        return False, app_state_json, "", None, str(exc)
    chain_id = os.environ.get("TAU_DEX_CHAIN_ID", "").strip() or os.environ.get("TAU_NETWORK_ID", "").strip() or "tau-local"
    try:
        zusd_cfg = _build_zusd_monetary_config(chain_id=chain_id)
        managed_asset_policy = build_zusd_managed_asset_policy(zusd_cfg.zusd_asset)
    except Exception as exc:
        return False, app_state_json, "", None, str(exc)

    stream_selection_error = _reserved_stream_selection_error(operations)
    if stream_selection_error is not None:
        return False, app_state_json, "", None, stream_selection_error

    try:
        state, proof_mining_state, zusd_monetary_state = _load_state(app_state_json)
    except Exception as exc:
        return False, app_state_json, "", None, str(exc)
    state = _sync_native_balances(state, chain_balances=chain_balances)
    if proof_mining_state is not None:
        actual_reward_pool_balance = int(chain_balances.get(proof_mining_state.reward_pool_pubkey, 0))
        if actual_reward_pool_balance < 0:
            return False, app_state_json, "", None, "reward pool chain balance must be non-negative"
        try:
            proof_mining_state = sync_proof_mining_runtime_balance(
                runtime_state=proof_mining_state,
                actual_reward_pool_balance=actual_reward_pool_balance,
            )
        except Exception as exc:
            return False, app_state_json, "", None, str(exc)

    faucet_op = operations.get(_DEX_FAUCET_KEY, operations.get(_LEGACY_DEX_FAUCET_KEY))
    ok, state, err = _apply_faucet(
        state,
        faucet_op,
        allow=allow_faucet,
        managed_asset_policy=managed_asset_policy,
    )
    if not ok:
        return False, app_state_json, "", None, err

    dex_ops = _select_dex_ops(operations)
    perp_ops = _select_perp_ops(operations)
    token_ops = _select_token_ops(operations)
    proof_mining_ops = _select_proof_mining_ops(operations)
    zusd_monetary_ops = _select_zusd_monetary_ops(operations)

    # Sync-only call: no ops, but we still update the snapshot/hash so native balances stay consistent.
    if not dex_ops and not perp_ops and not token_ops and not proof_mining_ops and not zusd_monetary_ops:
        canonical, app_hash = _canonical_state_and_hash(
            state,
            proof_mining_state=proof_mining_state,
            zusd_monetary_state=zusd_monetary_state,
        )
        return True, canonical, app_hash, None, None

    try:
        canonical_tx_sender_pubkey = _canonical_tx_sender_pubkey_for_engine(tx_sender_pubkey)
    except ValueError as exc:
        return False, app_state_json, "", None, str(exc)

    next_state = state
    if token_ops:
        ok, next_state, token_err = _apply_token_ops(
            next_state,
            token_ops.get(_TOKEN_OPS_KEY),
            tx_sender_pubkey=canonical_tx_sender_pubkey,
            block_timestamp=int(block_timestamp),
            managed_asset_policy=managed_asset_policy,
        )
        if not ok:
            return False, app_state_json, "", None, token_err or "token op rejected"

    if zusd_monetary_ops:
        zusd_res = apply_zusd_monetary_ops(
            config=zusd_cfg,
            state=next_state,
            zusd_state=zusd_monetary_state,
            operations=zusd_monetary_ops.get(_ZUSD_MONETARY_OPS_KEY),
            tx_sender_pubkey=canonical_tx_sender_pubkey,
            block_timestamp=int(block_timestamp),
        )
        if not zusd_res.ok or zusd_res.state is None or zusd_res.zusd_state is None:
            return False, app_state_json, "", None, zusd_res.error or "zUSD monetary op rejected"
        next_state = zusd_res.state
        zusd_monetary_state = zusd_res.zusd_state

    try:
        proof_verifier_config = _build_proof_verifier_config()
    except Exception as exc:
        return False, app_state_json, "", None, str(exc)

    dex_result = None
    if dex_ops:
        engine_cfg = DexEngineConfig(
            allow_missing_settlement=bool(allow_missing_settlement),
            require_intent_signatures=bool(require_intent_sigs),
            chain_id=chain_id,
            allow_external_tools=bool(allow_external_tools),
            consensus_mode=bool(consensus_mode),
            proof_config=proof_verifier_config,
        )
        dex_result = apply_ops(
            config=engine_cfg,
            state=next_state,
            operations=dex_ops,
            block_timestamp=int(block_timestamp),
            tx_sender_pubkey=canonical_tx_sender_pubkey,
        )
        if not dex_result.ok or dex_result.state is None:
            return False, app_state_json, "", None, dex_result.error or "DEX rejected"
        next_state = dex_result.state

    if proof_mining_ops:
        if perp_ops:
            return False, app_state_json, "", None, "proof mining claim cannot be combined with perps"
        proof_mining_op = proof_mining_ops.get(_PROOF_MINING_OPS_KEY)
        ok, next_state, proof_mining_state, proof_err = _apply_proof_mining_op(
            state=next_state,
            proof_mining_state=proof_mining_state,
            proof_mining_op=proof_mining_op,
            proof_mining_context=None if dex_result is None else dex_result.proof_mining_context,
            tx_sender_pubkey=canonical_tx_sender_pubkey,
            chain_balances=chain_balances,
        )
        if not ok:
            return False, app_state_json, "", None, proof_err or "proof mining rejected"

    if perp_ops:
        try:
            perp_cfg = _build_perp_engine_config(chain_id=chain_id)
        except Exception as exc:
            return False, app_state_json, "", None, str(exc)
        perp_res = apply_perp_ops(
            config=perp_cfg,
            state=next_state,
            operations=perp_ops,
            tx_sender_pubkey=canonical_tx_sender_pubkey,
            block_timestamp=int(block_timestamp),
        )
        if not perp_res.ok or perp_res.state is None:
            return False, app_state_json, "", None, perp_res.error or "PERP rejected"
        next_state = perp_res.state

    balances_patch = _balances_patch_for_native(before=chain_balances, after_state=next_state)
    canonical, app_hash = _canonical_state_and_hash(
        next_state,
        proof_mining_state=proof_mining_state,
        zusd_monetary_state=zusd_monetary_state,
    )
    return True, canonical, app_hash, balances_patch, None
