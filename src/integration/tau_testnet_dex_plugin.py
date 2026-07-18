"""
Tau Testnet Alpha app-bridge plugin for ZenoDEX.

This module implements the generic `external/tau-testnet/app_bridge.py` plugin API:
  apply_app_tx(...)

It applies DEX operations from a Tau transaction's `operations` dict:
  - "5": intents (list)
  - "6": settlement (object) [optional if allow_missing_settlement]
  - "7": faucet (object) [optional, test-only; requires TAU_DEX_FAUCET=1]
  - "8": perps (list) [optional; isolated markets require an operator key for admin actions]
  - "9": token ops (list) [optional; transfer/mint/burn for non-native assets]
  - "10": proof mining claim (object) [optional; bound to verified DEX proof context]
  - "11": zUSD monetary ops (list) [optional; collateral, mint/repay, stability pool]

Legacy key aliases are also accepted when invoking the plugin directly:
  - "2" -> intents, "3" -> settlement, "4" -> faucet, "5" -> perps
"""

from __future__ import annotations

import hashlib
import json
import os
from dataclasses import replace
from typing import Any, Dict, Mapping, Optional, Tuple

from ..core.dex import DexState
from ..core.generic_token_authority import (
    GenericTokenAuthorityState,
    GenericTokenSupplyAction,
    GenericTokenSupplyCommand,
    apply_generic_token_supply_command,
)
from ..core.perp_tau_ingress_stream import evaluate_perp_tau_ingress_stream
from ..core.proof_mining_payout import (
    ProofMiningPayoutPlan,
    plan_proof_mining_payout,
)
from ..core.zusd_generic_token_admission import GenericTokenAction
from ..state.balances import NATIVE_ASSET, BalanceTable
from ..state.canonical import canonical_hex_fixed_allow_0x, canonical_json_bytes
from ..state.lp import LPTable
from ..state.nonces import NonceTable
from .dex_engine import DexEngineConfig, apply_ops
from .dex_snapshot import snapshot_from_state, state_from_snapshot
from .generic_token_accounting import generic_token_accounting_error
from .generic_token_authority_bridge import (
    generic_token_authority_from_obj,
    generic_token_authority_to_obj,
)
from .perp_engine import PerpEngineConfig, apply_perp_ops
from .perp_source_admission_cli_verifier import (
    build_tau_source_authority_policy_receipt_cli_verifier,
)
from .proof_mining_runtime import (
    ProofMiningRuntimeState,
    apply_proof_mining_claim,
    initialize_proof_mining_runtime_state,
    proof_mining_runtime_state_from_obj,
    proof_mining_runtime_state_to_obj,
    sync_proof_mining_runtime_balance,
)
from .proof_verifier import ProofVerifierConfig
from .tau_native_identity import (
    TauNativeBalanceSnapshot,
    canonical_tau_pubkey,
    tau_egress_pubkey,
)
from .tau_state_principal_migration import canonicalize_legacy_tau_state_principals
from .zusd_generic_token_admission_bridge import (
    evaluate_live_generic_token_writer_admission,
    generic_token_admission_reject_code,
)
from .zusd_monetary_bridge import (
    ZUSDMonetaryConfig,
    ZUSDMonetaryState,
    apply_zusd_monetary_ops,
    init_monetary_state,
    zusd_global_ledger_consistency_error,
    zusd_monetary_config_from_policy_binding,
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

_APP_STATE_SCHEMA_V1 = "zenodex/tau_app_state/v1"
_APP_STATE_SCHEMA_V2 = "zenodex/tau_app_state/v2"
_APP_STATE_VERSION = 2
_APP_STATE_LEGACY_VERSION = 1
_MAX_APP_STATE_JSON_BYTES = 6_000_000


def _canonical_state_and_hash(
    state: DexState,
    *,
    proof_mining_state: Optional[ProofMiningRuntimeState] = None,
    zusd_monetary_state: Optional[ZUSDMonetaryState] = None,
    generic_token_authority: GenericTokenAuthorityState | None = None,
) -> Tuple[str, str]:
    if generic_token_authority is not None and zusd_monetary_state is None:
        raise ValueError(
            "generic token authority requires committed zUSD monetary policy"
        )
    snap = snapshot_from_state(state)
    if (
        proof_mining_state is None
        and zusd_monetary_state is None
        and generic_token_authority is None
    ):
        canonical = snap.canonical_bytes()
        return canonical.decode("utf-8"), hashlib.sha256(canonical).hexdigest()
    is_v2 = generic_token_authority is not None
    payload = {
        "schema": _APP_STATE_SCHEMA_V2 if is_v2 else _APP_STATE_SCHEMA_V1,
        "version": _APP_STATE_VERSION if is_v2 else _APP_STATE_LEGACY_VERSION,
        "dex_state": snap.data,
        "proof_mining": None
        if proof_mining_state is None
        else proof_mining_runtime_state_to_obj(proof_mining_state),
        "zusd_monetary": (
            None if zusd_monetary_state is None else zusd_monetary_state_to_obj(zusd_monetary_state)
        ),
    }
    if generic_token_authority is not None:
        payload["generic_token_authority"] = generic_token_authority_to_obj(
            generic_token_authority
        )
    canonical = canonical_json_bytes(payload)
    return canonical.decode("utf-8"), hashlib.sha256(canonical).hexdigest()


def build_zusd_policy_bound_genesis_app_state(
    *,
    config: ZUSDMonetaryConfig,
    state: DexState | None = None,
    generic_token_authority: GenericTokenAuthorityState | None = None,
) -> Tuple[str, str]:
    """Build a deterministic genesis snapshot with zUSD policy in authority.

    This constructor is intentionally outside ``apply_app_tx``.  Deployment
    must choose the policy explicitly before transaction replay begins; an
    ambient process environment cannot create or alter consensus policy.
    """

    if not isinstance(config, ZUSDMonetaryConfig):
        raise TypeError("config must be a ZUSDMonetaryConfig")
    dex_state = state or DexState(
        balances=BalanceTable(),
        pools={},
        lp_balances=LPTable(),
    )
    if not isinstance(dex_state, DexState):
        raise TypeError("state must be a DexState")
    monetary_state = init_monetary_state(config)
    authority_state = generic_token_authority or GenericTokenAuthorityState()
    accounting_error = generic_token_accounting_error(
        authority_state=authority_state,
        dex_state=dex_state,
        monetary_state=monetary_state,
        canonical_zusd_asset=config.zusd_asset,
    )
    if accounting_error is not None:
        raise ValueError(
            "generic token genesis accounting failed: " + accounting_error
        )
    return _canonical_state_and_hash(
        dex_state,
        zusd_monetary_state=monetary_state,
        generic_token_authority=authority_state,
    )


def _bool_env(name: str, *, default: bool) -> bool:
    raw = os.environ.get(name)
    if raw is None:
        return bool(default)
    v = raw.strip().lower()
    if v in {"1", "true", "yes", "on"}:
        return True
    if v in {"0", "false", "no", "off"}:
        return False
    return bool(default)


def _str_env(name: str, *, default: str = "") -> str:
    raw = os.environ.get(name)
    if raw is None:
        return default
    value = raw.strip()
    return value if value else default


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


def _int_env_alias(
    primary: str, fallback: str, *, default: int, minimum: int = 0, maximum: Optional[int] = None
) -> int:
    if os.environ.get(primary, "").strip():
        return _int_env(primary, default=default, minimum=minimum, maximum=maximum)
    return _int_env(fallback, default=default, minimum=minimum, maximum=maximum)


def _maybe_decode_custom_stream_value(value: Any) -> Any:
    """
    Upstream tau-testnet restricts custom operation streams (keys beyond 0/1) to
    `str|int` (or lists thereof). Our client encodes structured ops as canonical
    JSON strings; this helper decodes those strings back to objects.
    """
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
    timeout_raw = os.environ.get("TAU_DEX_PROOF_VERIFIER_TIMEOUT_S", "").strip()
    timeout_s = 10.0
    if timeout_raw:
        timeout_s = float(timeout_raw)
    allow_path_lookup = _bool_env("TAU_DEX_PROOF_VERIFIER_ALLOW_PATH_LOOKUP", default=False)
    return ProofVerifierConfig(
        enabled=bool(cmd),
        verifier_cmd=cmd,
        allow_path_lookup=bool(allow_path_lookup),
        timeout_s=float(timeout_s),
    )


def _load_state(
    app_state_json: str,
) -> Tuple[
    DexState,
    Optional[ProofMiningRuntimeState],
    Optional[ZUSDMonetaryState],
    GenericTokenAuthorityState | None,
]:
    raw = (app_state_json or "").strip()
    if not raw:
        return (
            DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable()),
            None,
            None,
            None,
        )
    if len(raw.encode("utf-8")) > _MAX_APP_STATE_JSON_BYTES:
        raise ValueError("app_state_json too large")
    try:
        obj = json.loads(raw)
    except Exception as exc:
        raise ValueError(f"invalid app_state_json: {exc}") from exc
    try:
        if isinstance(obj, Mapping) and any(
            key in obj for key in ("schema", "dex_state", "proof_mining")
        ):
            schema = obj.get("schema")
            version = obj.get("version", _APP_STATE_LEGACY_VERSION)
            if not isinstance(version, int) or isinstance(version, bool) or version <= 0:
                raise ValueError("app_state.version must be a positive int")
            if version not in {_APP_STATE_LEGACY_VERSION, _APP_STATE_VERSION}:
                raise ValueError(f"unsupported app_state version: {version}")
            expected_schema = (
                _APP_STATE_SCHEMA_V1
                if version == _APP_STATE_LEGACY_VERSION
                else _APP_STATE_SCHEMA_V2
            )
            if schema != expected_schema:
                raise ValueError(
                    "app_state schema/version mismatch: "
                    f"expected {expected_schema!r} for version {version}"
                )
            expected_fields = {
                "schema",
                "version",
                "dex_state",
                "proof_mining",
                "zusd_monetary",
            }
            if version == _APP_STATE_VERSION:
                expected_fields.add("generic_token_authority")
            if set(obj) != expected_fields:
                raise ValueError(
                    f"app_state fields must match the v{version} schema exactly"
                )
            dex_state = state_from_snapshot(
                _require_mapping(obj.get("dex_state"), name="app_state.dex_state")
            )
            proof_obj = obj.get("proof_mining")
            proof_state = (
                None
                if proof_obj is None
                else proof_mining_runtime_state_from_obj(
                    _require_mapping(proof_obj, name="app_state.proof_mining")
                )
            )
            zusd_obj = obj.get("zusd_monetary")
            zusd_state = (
                None
                if zusd_obj is None
                else zusd_monetary_state_from_obj(
                    _require_mapping(zusd_obj, name="app_state.zusd_monetary")
                )
            )
            generic_authority = (
                None
                if version == _APP_STATE_LEGACY_VERSION
                else generic_token_authority_from_obj(
                    obj.get("generic_token_authority")
                )
            )
            return dex_state, proof_state, zusd_state, generic_authority
        return state_from_snapshot(obj), None, None, None
    except Exception as exc:
        raise ValueError(f"invalid app_state snapshot: {exc}") from exc


def _parse_faucet_mint_entry(
    entry: Any, *, index: int
) -> Tuple[Optional[Tuple[str, str, int]], Optional[str]]:
    pk: Any
    asset: Any
    amount: Any

    if isinstance(entry, (list, tuple)):
        if len(entry) != 3:
            return None, f"faucet.mint[{index}] must have length 3"
        pk, asset, amount = entry
    elif isinstance(entry, dict):
        if set(entry) != {"pubkey", "asset", "amount"}:
            return None, f"faucet.mint[{index}] fields must match exactly"
        pk = entry.get("pubkey")
        asset = entry.get("asset")
        amount = entry.get("amount")
    else:
        return None, f"faucet.mint[{index}] must be a list or object"

    try:
        pk = _canonical_token_actor(
            pk,
            name=f"faucet.mint[{index}].pubkey",
        )
        asset = _canonical_token_asset(
            asset,
            name=f"faucet.mint[{index}].asset",
        )
        amount = _require_u32_positive(
            amount,
            name=f"faucet.mint[{index}].amount",
        )
    except (TypeError, ValueError) as exc:
        return None, str(exc)

    return (pk, asset, amount), None


def _sync_native_balances(
    state: DexState,
    *,
    native_balances: TauNativeBalanceSnapshot,
) -> DexState:
    balances_copy = _copy_balance_table(state.balances)
    for (pubkey, asset), _amount in list(balances_copy.get_all_balances().items()):
        if asset == NATIVE_ASSET:
            balances_copy.set(pubkey, asset, 0)

    for binding in native_balances.entries:
        if binding.balance > 0:
            balances_copy.set(binding.canonical_pubkey, NATIVE_ASSET, binding.balance)

    return replace(state, balances=balances_copy)


def _apply_faucet(
    state: DexState,
    authority_state: GenericTokenAuthorityState,
    faucet_op: Any,
    *,
    allow: bool,
    chain_id: str,
    canonical_zusd_asset: str,
    tx_sender_pubkey: str,
) -> Tuple[bool, DexState, GenericTokenAuthorityState, Optional[str]]:
    if faucet_op is None:
        return True, state, authority_state, None
    if not allow:
        return False, state, authority_state, "faucet disabled (set TAU_DEX_FAUCET=1)"
    if not isinstance(faucet_op, dict):
        return False, state, authority_state, "faucet op must be an object"
    if set(faucet_op) != {"mint"}:
        return False, state, authority_state, "faucet op fields must match exactly"
    mint = faucet_op.get("mint")
    if not isinstance(mint, list):
        return False, state, authority_state, "faucet.mint must be a list"
    try:
        sender = _canonical_pubkey(tx_sender_pubkey, name="tx_sender_pubkey")
    except (TypeError, ValueError) as exc:
        return False, state, authority_state, str(exc)

    balances_copy = _copy_balance_table(state.balances)
    working_authority = authority_state
    for i, entry in enumerate(mint):
        parsed, err = _parse_faucet_mint_entry(entry, index=i)
        if err is not None:
            return False, state, authority_state, err
        if parsed is None:
            return (
                False,
                state,
                authority_state,
                f"internal faucet parse error at index {i}",
            )
        pk, asset, amount = parsed

        authority_error = _generic_token_authority_error(
            op_name=f"faucet.mint[{i}]",
            chain_id=chain_id,
            canonical_zusd_asset=canonical_zusd_asset,
            action=GenericTokenAction.MINT,
            asset=asset,
            recipient_pubkey=pk,
        )
        if authority_error is not None:
            return False, state, authority_state, authority_error

        supply_decision = apply_generic_token_supply_command(
            working_authority,
            GenericTokenSupplyCommand(
                action=GenericTokenSupplyAction.MINT,
                asset_id=asset,
                actor_pubkey=sender,
                amount_units=amount,
            ),
        )
        if not supply_decision.accepted or supply_decision.next_state is None:
            reject_code = (
                "unknown"
                if supply_decision.reject_code is None
                else supply_decision.reject_code.value
            )
            return (
                False,
                state,
                authority_state,
                f"faucet.mint[{i}] authority transition rejected: {reject_code}",
            )
        current = balances_copy.get(pk, asset)
        try:
            next_balance = _checked_u32_balance_add(
                current,
                amount,
                name=f"faucet.mint[{i}].recipient_balance",
            )
        except ValueError as exc:
            return False, state, authority_state, str(exc)
        balances_copy.set(pk, asset, next_balance)
        working_authority = supply_decision.next_state

    next_state = replace(state, balances=balances_copy)
    return True, next_state, working_authority, None


def _balances_patch_for_native(
    *,
    before: TauNativeBalanceSnapshot,
    after_state: DexState,
) -> Dict[str, int]:
    out: Dict[str, int] = {}
    before_by_canonical = {binding.canonical_pubkey: binding for binding in before.entries}
    after_by_canonical: dict[str, int] = {}
    for (pubkey, asset), amount in after_state.balances.get_all_balances().items():
        if asset == NATIVE_ASSET:
            canonical = _canonical_pubkey(pubkey, name="native post-state pubkey")
            if canonical != pubkey:
                raise ValueError("native post-state pubkeys must be canonical")
            after_by_canonical[canonical] = int(amount)

    for canonical in sorted(set(before_by_canonical) | set(after_by_canonical)):
        prior = before_by_canonical.get(canonical)
        old = 0 if prior is None else prior.balance
        new = after_by_canonical.get(canonical, 0)
        if new != old:
            chain_key = (
                prior.chain_key
                if prior is not None
                else tau_egress_pubkey(canonical, name="native patch principal")
            )
            out[chain_key] = new
    return out


def _canonical_pubkey(value: Any, *, name: str) -> str:
    if not isinstance(value, str):
        raise ValueError(f"{name} must be a 48-byte hex pubkey string")
    return canonical_hex_fixed_allow_0x(value, nbytes=48, name=name)


def _canonical_token_asset(value: Any, *, name: str) -> str:
    if not isinstance(value, str):
        raise ValueError(f"{name} must be a 32-byte hex asset string")
    asset = canonical_hex_fixed_allow_0x(value, nbytes=32, name=name)
    if asset != value:
        raise ValueError(f"{name} must use canonical lowercase wire form")
    if asset == NATIVE_ASSET:
        raise ValueError("token stream does not support native asset")
    return asset


def _canonical_token_actor(value: Any, *, name: str) -> str:
    actor = _canonical_pubkey(value, name=name)
    if actor != value:
        raise ValueError(f"{name} must use canonical lowercase wire form")
    return actor


def _require_u32_positive(value: Any, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value <= 0:
        raise ValueError(f"{name} must be a positive int")
    if value > 0xFFFFFFFF:
        raise ValueError(f"{name} must fit in u32")
    return int(value)


def _require_u32_balance(value: Any, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise ValueError(f"{name} must be a nonnegative int")
    if value > 0xFFFFFFFF:
        raise ValueError(f"{name} must fit in u32")
    return int(value)


def _checked_u32_balance_add(current: Any, delta: int, *, name: str) -> int:
    bounded_current = _require_u32_balance(current, name=name)
    bounded_delta = _require_u32_positive(delta, name=f"{name} delta")
    if bounded_current > 0xFFFFFFFF - bounded_delta:
        raise ValueError(f"{name} overflow")
    return bounded_current + bounded_delta


def _token_sender_nonce_key(sender_pubkey: str) -> str:
    # Domain-separated pseudopubkey avoids nonce coupling with DEX/perps streams.
    payload = b"zenodex:tau_token_nonce:v1\x00" + sender_pubkey.encode("ascii")
    return "0x" + hashlib.sha384(payload).hexdigest()


def _resolve_proof_mining_pool_pubkey() -> Optional[str]:
    raw = os.environ.get("TAU_DEX_PROOF_MINING_POOL_PUBKEY", "").strip()
    if not raw:
        return None
    return _canonical_pubkey(raw, name="TAU_DEX_PROOF_MINING_POOL_PUBKEY")


def _enforce_deadline(
    *, op: Mapping[str, Any], block_timestamp: int, op_name: str
) -> Optional[str]:
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


def _generic_token_authority_error(
    *,
    op_name: str,
    chain_id: str,
    canonical_zusd_asset: str,
    action: GenericTokenAction,
    asset: str,
    recipient_pubkey: str | None,
) -> str | None:
    decision = evaluate_live_generic_token_writer_admission(
        chain_id=chain_id,
        canonical_zusd_asset=canonical_zusd_asset,
        action=action,
        asset=asset,
        recipient_pubkey=recipient_pubkey,
    )
    reject_code = generic_token_admission_reject_code(decision)
    if reject_code is None:
        return None
    return f"{op_name} rejected by zUSD authority policy: {reject_code}"


def _apply_token_ops(
    state: DexState,
    authority_state: GenericTokenAuthorityState,
    token_ops: Any,
    *,
    chain_id: str,
    canonical_zusd_asset: str,
    tx_sender_pubkey: str,
    block_timestamp: int,
) -> Tuple[bool, DexState, GenericTokenAuthorityState, Optional[str]]:
    def rejected(
        error: str,
    ) -> Tuple[bool, DexState, GenericTokenAuthorityState, Optional[str]]:
        return False, state, authority_state, error

    if token_ops is None:
        return True, state, authority_state, None
    if not isinstance(token_ops, list):
        return rejected("token op stream must be a list")
    if not token_ops:
        return True, state, authority_state, None

    try:
        sender = _canonical_token_actor(
            tx_sender_pubkey,
            name="tx_sender_pubkey",
        )
    except (TypeError, ValueError) as exc:
        return rejected(str(exc))

    balances = _copy_balance_table(state.balances)
    nonces = _copy_nonce_table(state.nonces)
    working_authority = authority_state
    nonce_key = _token_sender_nonce_key(sender)

    for i, raw in enumerate(token_ops):
        op_name = f"token op[{i}]"
        if not isinstance(raw, dict):
            return rejected(f"{op_name} must be an object")
        op = dict(raw)
        action = op.get("action")
        if type(action) is not str or action not in {"transfer", "mint", "burn"}:
            return rejected(f"{op_name} action unsupported: {action!r}")

        expected_fields = {
            "module",
            "version",
            "action",
            "asset",
            "amount",
            "nonce",
            "deadline",
            "operator_pubkey" if action == "mint" else "sender_pubkey",
        }
        if action in {"transfer", "mint"}:
            expected_fields.add("to_pubkey")
        if set(op) != expected_fields:
            return rejected(
                f"{op_name} fields must match the {action} schema exactly"
            )
        if op.get("module") != "TauToken":
            return rejected(f"{op_name} module must be TauToken")
        if op.get("version") != "0.1":
            return rejected(f"{op_name} version must be 0.1")

        try:
            nonce = _require_u32_positive(
                op.get("nonce"),
                name=f"{op_name}.nonce",
            )
            amount = _require_u32_positive(
                op.get("amount"),
                name=f"{op_name}.amount",
            )
            asset = _canonical_token_asset(
                op.get("asset"),
                name=f"{op_name}.asset",
            )
        except (TypeError, ValueError) as exc:
            return rejected(str(exc))
        expected = int(nonces.get_last(nonce_key)) + 1
        if nonce != expected:
            return rejected(
                f"{op_name} nonce invalid (expected {expected}, got {nonce})"
            )

        deadline_err = _enforce_deadline(
            op=op,
            block_timestamp=int(block_timestamp),
            op_name=op_name,
        )
        if deadline_err is not None:
            return rejected(deadline_err)

        if action == "transfer":
            try:
                sender_in_op = _canonical_token_actor(
                    op.get("sender_pubkey"),
                    name=f"{op_name}.sender_pubkey",
                )
                to_pubkey = _canonical_token_actor(
                    op.get("to_pubkey"),
                    name=f"{op_name}.to_pubkey",
                )
            except (TypeError, ValueError) as exc:
                return rejected(str(exc))
            if sender_in_op != sender:
                return rejected(f"{op_name} sender_pubkey mismatch")
            authority_error = _generic_token_authority_error(
                op_name=op_name,
                chain_id=chain_id,
                canonical_zusd_asset=canonical_zusd_asset,
                action=GenericTokenAction.TRANSFER,
                asset=asset,
                recipient_pubkey=to_pubkey,
            )
            if authority_error is not None:
                return rejected(authority_error)
            next_authority = working_authority
            if asset != canonical_zusd_asset:
                supply_decision = apply_generic_token_supply_command(
                    working_authority,
                    GenericTokenSupplyCommand(
                        action=GenericTokenSupplyAction.TRANSFER,
                        asset_id=asset,
                        actor_pubkey=sender,
                        amount_units=amount,
                        recipient_pubkey=to_pubkey,
                    ),
                )
                if (
                    not supply_decision.accepted
                    or supply_decision.next_state is None
                ):
                    reject_code = (
                        "unknown"
                        if supply_decision.reject_code is None
                        else supply_decision.reject_code.value
                    )
                    return rejected(
                        f"{op_name} authority transition rejected: {reject_code}"
                    )
                next_authority = supply_decision.next_state
            try:
                sender_balance = _require_u32_balance(
                    balances.get(sender, asset),
                    name=f"{op_name}.sender_balance",
                )
            except ValueError as exc:
                return rejected(str(exc))
            if sender_balance < amount:
                return rejected(f"{op_name} insufficient balance")
            try:
                recipient_balance = _checked_u32_balance_add(
                    balances.get(to_pubkey, asset),
                    amount,
                    name=f"{op_name}.recipient_balance",
                )
            except ValueError as exc:
                return rejected(str(exc))
            balances.set(sender, asset, sender_balance - amount)
            balances.set(to_pubkey, asset, recipient_balance)
            working_authority = next_authority

        elif action == "mint":
            try:
                operator_in_op = _canonical_token_actor(
                    op.get("operator_pubkey"),
                    name=f"{op_name}.operator_pubkey",
                )
                to_pubkey = _canonical_token_actor(
                    op.get("to_pubkey"),
                    name=f"{op_name}.to_pubkey",
                )
            except (TypeError, ValueError) as exc:
                return rejected(str(exc))
            if operator_in_op != sender:
                return rejected(f"{op_name} operator_pubkey mismatch")
            authority_error = _generic_token_authority_error(
                op_name=op_name,
                chain_id=chain_id,
                canonical_zusd_asset=canonical_zusd_asset,
                action=GenericTokenAction.MINT,
                asset=asset,
                recipient_pubkey=to_pubkey,
            )
            if authority_error is not None:
                return rejected(authority_error)
            supply_decision = apply_generic_token_supply_command(
                working_authority,
                GenericTokenSupplyCommand(
                    action=GenericTokenSupplyAction.MINT,
                    asset_id=asset,
                    actor_pubkey=sender,
                    amount_units=amount,
                    recipient_pubkey=to_pubkey,
                ),
            )
            if not supply_decision.accepted or supply_decision.next_state is None:
                reject_code = (
                    "unknown"
                    if supply_decision.reject_code is None
                    else supply_decision.reject_code.value
                )
                return rejected(
                    f"{op_name} authority transition rejected: {reject_code}"
                )
            try:
                recipient_balance = _checked_u32_balance_add(
                    balances.get(to_pubkey, asset),
                    amount,
                    name=f"{op_name}.recipient_balance",
                )
            except ValueError as exc:
                return rejected(str(exc))
            balances.set(to_pubkey, asset, recipient_balance)
            working_authority = supply_decision.next_state

        else:
            try:
                sender_in_op = _canonical_token_actor(
                    op.get("sender_pubkey"),
                    name=f"{op_name}.sender_pubkey",
                )
            except (TypeError, ValueError) as exc:
                return rejected(str(exc))
            if sender_in_op != sender:
                return rejected(f"{op_name} sender_pubkey mismatch")
            authority_error = _generic_token_authority_error(
                op_name=op_name,
                chain_id=chain_id,
                canonical_zusd_asset=canonical_zusd_asset,
                action=GenericTokenAction.BURN,
                asset=asset,
                recipient_pubkey=None,
            )
            if authority_error is not None:
                return rejected(authority_error)
            supply_decision = apply_generic_token_supply_command(
                working_authority,
                GenericTokenSupplyCommand(
                    action=GenericTokenSupplyAction.BURN,
                    asset_id=asset,
                    actor_pubkey=sender,
                    amount_units=amount,
                ),
            )
            if not supply_decision.accepted or supply_decision.next_state is None:
                reject_code = (
                    "unknown"
                    if supply_decision.reject_code is None
                    else supply_decision.reject_code.value
                )
                return rejected(
                    f"{op_name} authority transition rejected: {reject_code}"
                )
            try:
                sender_balance = _require_u32_balance(
                    balances.get(sender, asset),
                    name=f"{op_name}.sender_balance",
                )
            except ValueError as exc:
                return rejected(str(exc))
            if sender_balance < amount:
                return rejected(f"{op_name} insufficient balance")
            balances.set(sender, asset, sender_balance - amount)
            working_authority = supply_decision.next_state

        nonces.set_last(nonce_key, nonce)

    return (
        True,
        replace(state, balances=balances, nonces=nonces),
        working_authority,
        None,
    )

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
    elif _DEX_INTENTS_KEY in operations and _looks_like_dex_intents(
        operations.get(_DEX_INTENTS_KEY)
    ):
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


def _apply_proof_mining_op(
    *,
    state: DexState,
    proof_mining_state: Optional[ProofMiningRuntimeState],
    proof_mining_op: Any,
    proof_mining_context: Any,
    tx_sender_pubkey: str,
    native_balances: TauNativeBalanceSnapshot,
) -> Tuple[bool, DexState, Optional[ProofMiningRuntimeState], Optional[str]]:
    if proof_mining_op is None:
        return True, state, proof_mining_state, None
    if proof_mining_context is None:
        return (
            False,
            state,
            proof_mining_state,
            "proof mining claim requires verified DEX proof context",
        )
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
        return (
            False,
            state,
            proof_mining_state,
            "proof mining disabled (set TAU_DEX_PROOF_MINING_POOL_PUBKEY)",
        )
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
        winner_pubkey = _canonical_pubkey(
            winner.get("miner_id"), name="proof mining claim winner.miner_id"
        )
    except Exception as exc:
        return (
            False,
            state,
            proof_mining_state,
            f"proof mining reward requires canonical winner.miner_id: {exc}",
        )
    if winner_pubkey != sender:
        return False, state, proof_mining_state, "proof mining winner.miner_id mismatch"
    if sender == reward_pool_pubkey:
        return (
            False,
            state,
            proof_mining_state,
            "proof mining reward recipient must differ from reward pool",
        )
    claim_proposal_hash = str(claim_body.get("proposal_hash", ""))
    if claim_proposal_hash != str(getattr(proof_mining_context, "proposal_hash", "")):
        return False, state, proof_mining_state, "proof mining claim proposal_hash mismatch"
    try:
        reward_pool_binding = native_balances.binding_for(
            reward_pool_pubkey,
            preferred_chain_key=os.environ.get("TAU_DEX_PROOF_MINING_POOL_PUBKEY", "").strip(),
            name="proof mining reward pool",
        )
        recipient_binding = native_balances.binding_for(
            sender,
            preferred_chain_key=tx_sender_pubkey,
            name="proof mining reward recipient",
        )
    except (TypeError, ValueError) as exc:
        return False, state, proof_mining_state, str(exc)
    actual_pool_balance = reward_pool_binding.balance
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
        return (
            False,
            state,
            proof_mining_state,
            result.error_message or "proof mining manager rejected",
        )
    reward_amount = int(result.effects.get("reward_amount", 0))
    if reward_amount <= 0:
        return False, state, proof_mining_state, "proof mining reward_amount invalid"
    balances = _copy_balance_table(state.balances)
    pool_balance = int(balances.get(reward_pool_binding.canonical_pubkey, NATIVE_ASSET))
    if pool_balance != actual_pool_balance:
        return False, state, proof_mining_state, "reward pool native balance out of sync"
    recipient_balance = int(balances.get(recipient_binding.canonical_pubkey, NATIVE_ASSET))
    payout_decision = plan_proof_mining_payout(
        reward_pool_pubkey=reward_pool_pubkey,
        recipient_pubkey=sender,
        reward_amount_base_units=reward_amount,
        reward_pool_balance_base_units=pool_balance,
        recipient_balance_base_units=recipient_balance,
    )
    if not isinstance(payout_decision, ProofMiningPayoutPlan):
        return False, state, proof_mining_state, payout_decision.message
    for effect in payout_decision.effects:
        balance_before = int(balances.get(effect.pubkey, NATIVE_ASSET))
        balances.set(effect.pubkey, NATIVE_ASSET, balance_before + effect.delta_base_units)
    return True, replace(state, balances=balances), next_runtime_state, None


def _build_perp_engine_config(*, chain_id: str) -> PerpEngineConfig:
    operator_pubkey = os.environ.get("TAU_DEX_OPERATOR_PUBKEY") or os.environ.get(
        "TAU_DEX_PERP_OPERATOR_PUBKEY"
    )
    oracle_pubkey = os.environ.get("TAU_DEX_PERP_ORACLE_PUBKEY") or os.environ.get(
        "TAU_DEX_ORACLE_PUBKEY"
    )
    allow_isolated = _bool_env("TAU_DEX_ALLOW_ISOLATED_PERPS", default=False)

    def _oracle_adapter_bridge_verifier(bridge):
        from tools.zenodex_oracle_aggregate_adapter import (  # pylint: disable=import-outside-toplevel
            verify_aggregate_adapter_bridge,
        )

        return verify_aggregate_adapter_bridge(bridge)

    def _tau_source_authority_policy_receipt_verifier():
        verifier_path = _str_env("TAU_DEX_TAU_SOURCE_AUTHORITY_POLICY_RECEIPT_VERIFIER")
        if not verifier_path:
            return None
        return build_tau_source_authority_policy_receipt_cli_verifier(
            verifier_path=verifier_path,
            timeout_s=float(
                _int_env(
                    "TAU_DEX_TAU_SOURCE_AUTHORITY_POLICY_RECEIPT_VERIFIER_TIMEOUT_S",
                    default=5,
                    minimum=1,
                    maximum=60,
                )
            ),
        )

    return PerpEngineConfig(
        operator_pubkey=(operator_pubkey or "").strip() or None,
        chain_id=chain_id,
        canonicalize_authenticated_bls_principals=True,
        oracle_pubkey=(oracle_pubkey or "").strip() or None,
        allow_isolated_markets=bool(allow_isolated),
        oracle_adapter_bridge_verifier=_oracle_adapter_bridge_verifier,
        require_oracle_adapter_for_clearinghouse_settle_epoch=_bool_env(
            "TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH",
            default=False,
        ),
        require_oracle_adapter_for_isolated_partial_liquidate=_bool_env(
            "TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_ISOLATED_PARTIAL_LIQUIDATE",
            default=False,
        ),
        require_tau_source_binding_for_isolated_partial_liquidate=_bool_env(
            "TAU_DEX_REQUIRE_TAU_SOURCE_BINDING_FOR_ISOLATED_PARTIAL_LIQUIDATE",
            default=False,
        ),
        require_tau_source_state_root_binding_for_isolated_partial_liquidate=_bool_env(
            "TAU_DEX_REQUIRE_TAU_SOURCE_STATE_ROOT_BINDING_FOR_ISOLATED_PARTIAL_LIQUIDATE",
            default=False,
        ),
        require_tau_source_membership_proof_for_isolated_partial_liquidate=_bool_env(
            "TAU_DEX_REQUIRE_TAU_SOURCE_MEMBERSHIP_PROOF_FOR_ISOLATED_PARTIAL_LIQUIDATE",
            default=False,
        ),
        require_tau_source_root_authority_for_isolated_partial_liquidate=_bool_env(
            "TAU_DEX_REQUIRE_TAU_SOURCE_ROOT_AUTHORITY_FOR_ISOLATED_PARTIAL_LIQUIDATE",
            default=False,
        ),
        require_tau_source_admission_envelope_for_isolated_partial_liquidate=_bool_env(
            "TAU_DEX_REQUIRE_TAU_SOURCE_ADMISSION_ENVELOPE_FOR_ISOLATED_PARTIAL_LIQUIDATE",
            default=False,
        ),
        require_tau_source_authority_policy_receipt_for_isolated_partial_liquidate=_bool_env(
            "TAU_DEX_REQUIRE_TAU_SOURCE_AUTHORITY_POLICY_RECEIPT_FOR_ISOLATED_PARTIAL_LIQUIDATE",
            default=False,
        ),
        tau_source_authority_policy_receipt_verifier=(
            _tau_source_authority_policy_receipt_verifier()
        ),
    )


def _build_zusd_monetary_config(*, chain_id: str) -> ZUSDMonetaryConfig:
    oracle_pubkey = os.environ.get("TAU_DEX_ZUSD_ORACLE_PUBKEY") or os.environ.get(
        "TAU_DEX_ORACLE_PUBKEY"
    )
    asset_id = os.environ.get("TAU_DEX_ZUSD_ASSET_ID", "").strip() or None
    fee_stake_asset_id = os.environ.get("TAU_DEX_ZUSD_FEE_STAKE_ASSET_ID", "").strip() or None
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
        borrow_fee_floor_bps=_int_env_alias(
            "TAU_DEX_ZUSD_BORROW_FEE_FLOOR_BPS", "", default=0, maximum=10_000
        ),
        borrow_fee_max_bps=_int_env_alias(
            "TAU_DEX_ZUSD_BORROW_FEE_MAX_BPS", "", default=1_000, maximum=10_000
        ),
        host_protocol_fee_share_bps=_int_env_alias(
            "TAU_DEX_ZUSD_HOST_PROTOCOL_FEE_SHARE_BPS",
            "",
            default=0,
            maximum=10_000,
        ),
        fee_stake_asset_id=fee_stake_asset_id,
        staking_activation_delay_epochs=_int_env_alias(
            "TAU_DEX_ZUSD_STAKING_ACTIVATION_DELAY_EPOCHS",
            "",
            default=1,
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

    decoded_ops: Dict[str, Any] = {}
    for k, v in operations.items():
        key = str(k)
        if key in ("0", "1"):
            decoded_ops[key] = v
        else:
            decoded_ops[key] = _maybe_decode_custom_stream_value(v)
    operations = decoded_ops

    allow_faucet = _bool_env("TAU_DEX_FAUCET", default=False)
    allow_missing_settlement = _bool_env("TAU_DEX_ALLOW_MISSING_SETTLEMENT", default=True)
    require_intent_sigs = _bool_env("TAU_DEX_REQUIRE_INTENT_SIGS", default=True)
    allow_external_tools = _bool_env("TAU_DEX_ALLOW_EXTERNAL_TOOLS", default=False)
    consensus_mode = _bool_env("TAU_DEX_CONSENSUS_MODE", default=True)
    chain_id = (
        os.environ.get("TAU_DEX_CHAIN_ID", "").strip()
        or os.environ.get("TAU_NETWORK_ID", "").strip()
        or "tau-local"
    )
    try:
        native_balances = TauNativeBalanceSnapshot.from_chain_balances(chain_balances)
    except (TypeError, ValueError) as exc:
        return False, app_state_json, "", None, str(exc)
    canonical_tx_sender_pubkey = ""
    if tx_sender_pubkey:
        try:
            canonical_tx_sender_pubkey = canonical_tau_pubkey(
                tx_sender_pubkey,
                name="tx_sender_pubkey",
            )
        except (TypeError, ValueError) as exc:
            return False, app_state_json, "", None, str(exc)
    try:
        (
            state,
            proof_mining_state,
            zusd_monetary_state,
            generic_token_authority,
        ) = _load_state(app_state_json)
    except Exception as exc:
        return False, app_state_json, "", None, str(exc)
    try:
        state = canonicalize_legacy_tau_state_principals(state)
    except (TypeError, ValueError) as exc:
        return False, app_state_json, "", None, str(exc)
    state = _sync_native_balances(state, native_balances=native_balances)
    if proof_mining_state is not None:
        try:
            reward_pool_binding = native_balances.binding_for(
                proof_mining_state.reward_pool_pubkey,
                preferred_chain_key=proof_mining_state.reward_pool_pubkey,
                name="proof mining reward pool",
            )
        except (TypeError, ValueError) as exc:
            return False, app_state_json, "", None, str(exc)
        actual_reward_pool_balance = reward_pool_binding.balance
        try:
            proof_mining_state = sync_proof_mining_runtime_balance(
                runtime_state=proof_mining_state,
                actual_reward_pool_balance=actual_reward_pool_balance,
            )
        except Exception as exc:
            return False, app_state_json, "", None, str(exc)

    faucet_op = operations.get(_DEX_FAUCET_KEY, operations.get(_LEGACY_DEX_FAUCET_KEY))
    try:
        dex_ops = _select_dex_ops(operations)
        perp_ops = _select_perp_ops(operations)
        token_ops = _select_token_ops(operations)
        proof_mining_ops = _select_proof_mining_ops(operations)
        zusd_monetary_ops = _select_zusd_monetary_ops(operations)
    except (TypeError, ValueError) as exc:
        return False, app_state_json, "", None, str(exc)

    policy_sensitive_ops_present = (
        faucet_op is not None or bool(token_ops) or bool(zusd_monetary_ops)
    )
    if zusd_monetary_state is None and policy_sensitive_ops_present:
        return (
            False,
            app_state_json,
            "",
            None,
            "zUSD monetary policy is absent from authoritative state; "
            "install a policy-bound genesis or governed migration first",
        )

    if generic_token_authority is None and (
        faucet_op is not None or bool(token_ops)
    ):
        return (
            False,
            app_state_json,
            "",
            None,
            "generic token authority is absent from app state; "
            "install a v2 genesis or governed migration first",
        )

    zusd_cfg = (
        None
        if zusd_monetary_state is None
        else zusd_monetary_config_from_policy_binding(zusd_monetary_state.policy_binding)
    )
    if zusd_cfg is not None:
        zusd_precheck_error = zusd_global_ledger_consistency_error(
            config=zusd_cfg,
            state=state,
            monetary_state=zusd_monetary_state,
        )
        if zusd_precheck_error is not None:
            return (
                False,
                app_state_json,
                "",
                None,
                f"zUSD global ledger precheck failed: {zusd_precheck_error}",
            )
    if generic_token_authority is not None:
        if zusd_cfg is None:
            return (
                False,
                app_state_json,
                "",
                None,
                "generic token authority requires committed zUSD policy",
            )
        generic_precheck_error = generic_token_accounting_error(
            authority_state=generic_token_authority,
            dex_state=state,
            monetary_state=zusd_monetary_state,
            canonical_zusd_asset=zusd_cfg.zusd_asset,
        )
        if generic_precheck_error is not None:
            return (
                False,
                app_state_json,
                "",
                None,
                "generic token accounting precheck failed: "
                + generic_precheck_error,
            )

    if faucet_op is not None:
        if zusd_cfg is None:
            return False, app_state_json, "", None, "committed zUSD policy unavailable"
        if generic_token_authority is None:
            return (
                False,
                app_state_json,
                "",
                None,
                "generic token authority unavailable",
            )
        ok, state, generic_token_authority, err = _apply_faucet(
            state,
            generic_token_authority,
            faucet_op,
            allow=allow_faucet,
            chain_id=zusd_cfg.chain_id,
            canonical_zusd_asset=zusd_cfg.zusd_asset,
            tx_sender_pubkey=canonical_tx_sender_pubkey,
        )
        if not ok:
            return False, app_state_json, "", None, err

    # Sync-only call: no ops, but we still update the snapshot/hash so native balances stay consistent.
    if (
        faucet_op is None
        and not dex_ops
        and not perp_ops
        and not token_ops
        and not proof_mining_ops
        and not zusd_monetary_ops
    ):
        canonical, app_hash = _canonical_state_and_hash(
            state,
            proof_mining_state=proof_mining_state,
            zusd_monetary_state=zusd_monetary_state,
            generic_token_authority=generic_token_authority,
        )
        return True, canonical, app_hash, None, None

    next_state = state
    if token_ops:
        if zusd_cfg is None:
            return False, app_state_json, "", None, "committed zUSD policy unavailable"
        if generic_token_authority is None:
            return (
                False,
                app_state_json,
                "",
                None,
                "generic token authority unavailable",
            )
        ok, next_state, generic_token_authority, token_err = _apply_token_ops(
            next_state,
            generic_token_authority,
            token_ops.get(_TOKEN_OPS_KEY),
            chain_id=zusd_cfg.chain_id,
            canonical_zusd_asset=zusd_cfg.zusd_asset,
            tx_sender_pubkey=canonical_tx_sender_pubkey,
            block_timestamp=int(block_timestamp),
        )
        if not ok:
            return False, app_state_json, "", None, token_err or "token op rejected"

    if zusd_monetary_ops:
        if zusd_cfg is None:
            return False, app_state_json, "", None, "committed zUSD policy unavailable"
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
            canonicalize_authenticated_bls_principals=True,
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
            return (
                False,
                app_state_json,
                "",
                None,
                "proof mining claim cannot be combined with perps",
            )
        proof_mining_op = proof_mining_ops.get(_PROOF_MINING_OPS_KEY)
        ok, next_state, proof_mining_state, proof_err = _apply_proof_mining_op(
            state=next_state,
            proof_mining_state=proof_mining_state,
            proof_mining_op=proof_mining_op,
            proof_mining_context=None if dex_result is None else dex_result.proof_mining_context,
            tx_sender_pubkey=tx_sender_pubkey,
            native_balances=native_balances,
        )
        if not ok:
            return False, app_state_json, "", None, proof_err or "proof mining rejected"

    if perp_ops:
        perp_cfg = _build_perp_engine_config(chain_id=chain_id)
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

    if zusd_cfg is not None:
        zusd_postcheck_error = zusd_global_ledger_consistency_error(
            config=zusd_cfg,
            state=next_state,
            monetary_state=zusd_monetary_state,
        )
        if zusd_postcheck_error is not None:
            return (
                False,
                app_state_json,
                "",
                None,
                f"zUSD global ledger postcheck failed: {zusd_postcheck_error}",
            )
    if generic_token_authority is not None:
        if zusd_cfg is None:
            return (
                False,
                app_state_json,
                "",
                None,
                "generic token authority requires committed zUSD policy",
            )
        generic_postcheck_error = generic_token_accounting_error(
            authority_state=generic_token_authority,
            dex_state=next_state,
            monetary_state=zusd_monetary_state,
            canonical_zusd_asset=zusd_cfg.zusd_asset,
        )
        if generic_postcheck_error is not None:
            return (
                False,
                app_state_json,
                "",
                None,
                "generic token accounting postcheck failed: "
                + generic_postcheck_error,
            )

    balances_patch = _balances_patch_for_native(
        before=native_balances,
        after_state=next_state,
    )
    canonical, app_hash = _canonical_state_and_hash(
        next_state,
        proof_mining_state=proof_mining_state,
        zusd_monetary_state=zusd_monetary_state,
        generic_token_authority=generic_token_authority,
    )
    return True, canonical, app_hash, balances_patch, None
