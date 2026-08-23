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
from dataclasses import dataclass, replace
from typing import Any, Dict, Mapping, Optional, Tuple

from ..core.consensus_time import VerifiedExecutionClockV1
from ..core.dex import DexState
from ..core.perp_tau_ingress_stream import evaluate_perp_tau_ingress_stream
from ..core.proof_mining_claimability_gate import (
    REJECT_CODE_TO_ERROR as PROOF_MINING_REJECT_CODE_TO_ERROR,
)
from ..core.proof_mining_claimability_gate import (
    evaluate_proof_mining_claimability_gate,
    evaluate_proof_mining_recipient_gate,
)
from ..core.zusd_generic_token_admission import (
    CanonicalZUSDCustodyClass,
    CanonicalZUSDCustodyRegistry,
    GenericTokenAction,
    GenericTokenAdmissionCode,
    GenericTokenAdmissionCommand,
    TokenAssetClass,
    TokenWriterRole,
    evaluate_generic_token_admission,
)
from ..core.zusd_oracle_ingress_admission import ZUSDOracleEvidenceProfile
from ..state.balances import NATIVE_ASSET, BalanceTable
from ..state.canonical import canonical_hex_fixed_allow_0x, canonical_json_bytes
from ..state.lp import LPTable
from ..state.nonces import NonceTable
from .dex_engine import DexEngineConfig, apply_ops
from .dex_snapshot import snapshot_from_state, state_from_snapshot
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
from .zeno_ledger_v0 import hash_v0
from .zusd_custody_registry import build_live_canonical_zusd_custody_registry
from .zusd_monetary_bridge import (
    ZUSDMonetaryConfig,
    ZUSDMonetaryState,
    apply_zusd_monetary_ops,
    assert_zusd_global_liability_cover,
    zusd_monetary_state_from_obj,
    zusd_monetary_state_to_obj,
)
from .zusd_tau_token import derive_zusd_tau_asset_id

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


@dataclass(frozen=True, slots=True)
class TauAppTxProposalV1:
    """Immutable proposal returned by the legacy Tau application adapter.

    The native balance patch stores absolute post-state balances, not deltas.
    This value is a proposal only: it does not persist application state,
    mutate ``chain_balances``, or authorize an M6 commit-port publication.
    """

    accepted: bool
    app_state_json: str
    app_hash: str
    native_balance_patch: tuple[tuple[str, int], ...] | None
    error: str | None

    @classmethod
    def from_legacy_result(cls, result: object) -> "TauAppTxProposalV1":
        if type(result) is not tuple or len(result) != 5:
            raise TypeError("legacy app-tx result must be a five-tuple")
        accepted, app_state_json, app_hash, patch, error = result
        if type(accepted) is not bool:
            raise TypeError("legacy app-tx accepted flag must be bool")
        if not isinstance(app_state_json, str) or not isinstance(app_hash, str):
            raise TypeError("legacy app-tx state and hash must be strings")
        if error is not None and not isinstance(error, str):
            raise TypeError("legacy app-tx error must be a string or None")
        if accepted and error is not None:
            raise ValueError("accepted app-tx proposal cannot carry an error")
        if not accepted and error is None:
            raise ValueError("rejected app-tx proposal requires an error")
        if not accepted and patch is not None:
            raise ValueError("rejected app-tx proposal cannot carry a balance patch")

        normalized_patch: tuple[tuple[str, int], ...] | None = None
        if patch is not None:
            if not isinstance(patch, Mapping):
                raise TypeError("legacy app-tx balance patch must be a mapping or None")
            rows: list[tuple[str, int]] = []
            for pubkey, amount in patch.items():
                if not isinstance(pubkey, str):
                    raise TypeError("legacy app-tx balance patch keys must be strings")
                if type(amount) is not int or amount < 0:
                    raise TypeError("legacy app-tx balance patch amounts must be non-negative ints")
                rows.append((pubkey, amount))
            normalized_patch = tuple(sorted(rows))

        return cls(
            accepted=accepted,
            app_state_json=app_state_json,
            app_hash=app_hash,
            native_balance_patch=normalized_patch,
            error=error,
        )

    def to_legacy_result_v1(self) -> Tuple[bool, str, str, Optional[Dict[str, int]], Optional[str]]:
        """Return a compatibility tuple with a fresh patch mapping."""

        patch = None if self.native_balance_patch is None else dict(self.native_balance_patch)
        return self.accepted, self.app_state_json, self.app_hash, patch, self.error


def _canonical_state_and_hash(
    state: DexState,
    *,
    proof_mining_state: Optional[ProofMiningRuntimeState] = None,
    zusd_monetary_state: Optional[ZUSDMonetaryState] = None,
) -> Tuple[str, str]:
    snap = snapshot_from_state(state, require_lp_supply_conservation=True)
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


def _int_env_alias(primary: str, fallback: str, *, default: int, minimum: int = 0, maximum: Optional[int] = None) -> int:
    if os.environ.get(primary, "").strip():
        return _int_env(primary, default=default, minimum=minimum, maximum=maximum)
    return _int_env(fallback, default=default, minimum=minimum, maximum=maximum)


def _require_neutral_legacy_ce067_env(name: str, *, expected: int) -> None:
    raw = os.environ.get(name, "").strip()
    if not raw:
        return
    try:
        value = int(raw)
    except ValueError as exc:
        raise ValueError(
            f"CE067 legacy config {name} must be an integer"
        ) from exc
    if value != expected:
        raise ValueError(
            "CE067 explicit profile migration required for non-neutral "
            f"legacy config: {name}"
        )


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


def _asset_identity(value: str, *, name: str) -> str:
    stripped = value.strip()
    body = stripped[2:] if stripped.lower().startswith("0x") else stripped
    if len(body) != 64 or any(character not in "0123456789abcdefABCDEF" for character in body):
        return value
    return canonical_hex_fixed_allow_0x(stripped, nbytes=32, name=name)


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
            schema = obj.get("schema")
            if schema != _APP_STATE_SCHEMA:
                raise ValueError(f"unsupported app_state schema: {schema!r}")
            version = obj.get("version", _APP_STATE_VERSION)
            if not isinstance(version, int) or isinstance(version, bool) or version <= 0:
                raise ValueError("app_state.version must be a positive int")
            if version != _APP_STATE_VERSION:
                raise ValueError(f"unsupported app_state version: {version}")
            dex_state = state_from_snapshot(
                _require_mapping(obj.get("dex_state"), name="app_state.dex_state"),
                require_lp_supply_conservation=True,
            )
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
        return (
            state_from_snapshot(obj, require_lp_supply_conservation=True),
            None,
            None,
        )
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
    if asset == NATIVE_ASSET:
        return None, "faucet cannot mint native asset"
    if not isinstance(amount, int) or isinstance(amount, bool) or amount <= 0:
        return None, f"faucet.mint[{index}] amount must be a positive int"

    return (pk, asset, int(amount)), None


def _sync_native_balances(state: DexState, *, chain_balances: Dict[str, int]) -> DexState:
    balances_copy = _copy_balance_table(state.balances)

    # Drop any existing native entries from stored snapshot.
    for (pk, asset), _amount in list(balances_copy.get_all_balances().items()):
        if asset == NATIVE_ASSET:
            balances_copy.set(pk, asset, 0)

    for pk, amount in chain_balances.items():
        try:
            amt_i = int(amount)
        except Exception:
            continue
        if amt_i <= 0:
            continue
        balances_copy.set(str(pk), NATIVE_ASSET, amt_i)

    return replace(state, balances=balances_copy)


def _apply_faucet(
    state: DexState,
    faucet_op: Any,
    *,
    allow: bool,
    reserved_protocol_token_asset_id: str,
    reserved_zusd_asset_id: str,
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
        canonical_asset = _asset_identity(
            asset,
            name=f"faucet.mint[{i}].asset",
        )
        if canonical_asset == _asset_identity(
            reserved_protocol_token_asset_id,
            name="reserved_protocol_token_asset_id",
        ):
            return False, state, "faucet cannot mint protocol token"
        if canonical_asset == _asset_identity(
            reserved_zusd_asset_id,
            name="reserved_zusd_asset_id",
        ):
            return False, state, "faucet cannot mint canonical zUSD"

        current = balances_copy.get(pk, canonical_asset)
        balances_copy.set(pk, canonical_asset, int(current) + int(amount))

    next_state = replace(state, balances=balances_copy)
    return True, next_state, None


def _balances_patch_for_native(*, before: Dict[str, int], after_state: DexState) -> Dict[str, int]:
    out: Dict[str, int] = {}
    keys = set(before.keys())
    # Include any addresses that appear in the DEX snapshot (native).
    for (pk, asset), _amount in after_state.balances.get_all_balances().items():
        if asset == NATIVE_ASSET:
            keys.add(pk)

    for pk in keys:
        old = int(before.get(pk, 0))
        new = int(after_state.balances.get(pk, NATIVE_ASSET))
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


def _require_u32_positive(value: Any, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value <= 0:
        raise ValueError(f"{name} must be a positive int")
    if value > 0xFFFFFFFF:
        raise ValueError(f"{name} must fit in u32")
    return int(value)


def _token_asset_supply_in_u32_domain(
    balances: BalanceTable,
    *,
    asset: str,
    op_index: int,
) -> int:
    supply = 0
    for (pubkey, balance_asset), amount in sorted(
        balances.get_all_balances().items(),
        key=lambda item: (item[0][1], item[0][0]),
    ):
        if balance_asset != asset:
            continue
        if not isinstance(amount, int) or isinstance(amount, bool) or amount < 0:
            raise ValueError(f"token op[{op_index}] invalid balance for {pubkey}")
        if amount > 0xFFFFFFFF:
            raise ValueError(
                f"token op[{op_index}] pre-state balance exceeds u32 max 4294967295"
            )
        supply += amount
        if supply > 0xFFFFFFFF:
            raise ValueError(
                f"token op[{op_index}] pre-state supply exceeds u32 max 4294967295"
            )
    return supply


def _token_sender_nonce_key(sender_pubkey: str) -> str:
    # Domain-separated pseudopubkey avoids nonce coupling with DEX/perps streams.
    payload = b"zenodex:tau_token_nonce:v1\x00" + sender_pubkey.encode("ascii")
    return "0x" + hashlib.sha384(payload).hexdigest()


def _generic_token_admission_error(
    *,
    op_index: int,
    action: str,
    asset: str,
    canonical_zusd_asset: str,
    recipient_pubkey: str | None,
    custody_registry: CanonicalZUSDCustodyRegistry,
) -> str | None:
    recipient_class = (
        CanonicalZUSDCustodyClass.ORDINARY_ACCOUNT
        if recipient_pubkey is None
        else custody_registry.classify(recipient_pubkey)
    )
    decision = evaluate_generic_token_admission(
        GenericTokenAdmissionCommand(
            action=GenericTokenAction(action),
            asset_class=(
                TokenAssetClass.CANONICAL_ZUSD
                if asset == canonical_zusd_asset
                else TokenAssetClass.OTHER
            ),
            writer_role=TokenWriterRole.GENERIC_TOKEN_WRITER,
            recipient_custody_class=recipient_class,
        )
    )
    if decision.admitted:
        return None
    if (
        decision.code
        is GenericTokenAdmissionCode.CANONICAL_ZUSD_MINT_REQUIRES_MONETARY_AUTHORITY
    ):
        return f"token op[{op_index}] canonical zUSD mint requires the monetary authority"
    if (
        decision.code
        is GenericTokenAdmissionCode.CANONICAL_ZUSD_BURN_REQUIRES_MONETARY_AUTHORITY
    ):
        return f"token op[{op_index}] canonical zUSD burn requires the monetary authority"
    if recipient_class is CanonicalZUSDCustodyClass.STABILITY_POOL_ESCROW:
        return (
            f"token op[{op_index}] canonical zUSD transfer to the reserved Stability "
            "Pool address requires the monetary authority"
        )
    return (
        f"token op[{op_index}] canonical zUSD transfer to a reserved monetary-module "
        "address requires the monetary authority"
    )


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
    chain_id: str,
    tx_sender_pubkey: str,
    block_timestamp: int,
) -> Tuple[bool, DexState, Optional[str]]:
    if token_ops is None:
        return True, state, None
    if not isinstance(token_ops, list):
        return False, state, "token op stream must be a list"
    if not token_ops:
        return True, state, None

    try:
        sender = _canonical_pubkey(tx_sender_pubkey, name="tx_sender_pubkey")
        canonical_zusd_asset = derive_zusd_tau_asset_id(chain_id=chain_id)
        custody_registry = build_live_canonical_zusd_custody_registry(
            chain_id=chain_id
        )
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
                _token_asset_supply_in_u32_domain(balances, asset=asset, op_index=i)
            except Exception as exc:
                return False, state, str(exc)
            admission_error = _generic_token_admission_error(
                op_index=i,
                action=action,
                asset=asset,
                canonical_zusd_asset=canonical_zusd_asset,
                recipient_pubkey=to_pubkey,
                custody_registry=custody_registry,
            )
            if admission_error is not None:
                return False, state, admission_error
            if to_pubkey == sender:
                return False, state, f"token op[{i}] requires distinct sender and recipient"
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
                asset_supply = _token_asset_supply_in_u32_domain(
                    balances,
                    asset=asset,
                    op_index=i,
                )
            except Exception as exc:
                return False, state, str(exc)
            admission_error = _generic_token_admission_error(
                op_index=i,
                action=action,
                asset=asset,
                canonical_zusd_asset=canonical_zusd_asset,
                recipient_pubkey=to_pubkey,
                custody_registry=custody_registry,
            )
            if admission_error is not None:
                return False, state, admission_error
            recipient_balance = int(balances.get(to_pubkey, asset))
            if asset_supply + amount > 0xFFFFFFFF:
                return False, state, f"token op[{i}] supply exceeds u32 max 4294967295"
            if recipient_balance + amount > 0xFFFFFFFF:
                return False, state, f"token op[{i}] recipient balance exceeds u32 max 4294967295"
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
                _token_asset_supply_in_u32_domain(balances, asset=asset, op_index=i)
            except Exception as exc:
                return False, state, str(exc)
            admission_error = _generic_token_admission_error(
                op_index=i,
                action=action,
                asset=asset,
                canonical_zusd_asset=canonical_zusd_asset,
                recipient_pubkey=None,
                custody_registry=custody_registry,
            )
            if admission_error is not None:
                return False, state, admission_error
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
    recipient_gate = evaluate_proof_mining_recipient_gate(
        recipient_distinct_from_reward_pool=sender != reward_pool_pubkey,
    )
    if not recipient_gate.admitted:
        return (
            False,
            state,
            proof_mining_state,
            PROOF_MINING_REJECT_CODE_TO_ERROR[recipient_gate.reject_code],
        )
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
    runtime_state_was_present = proof_mining_state is not None
    runtime_state = proof_mining_state
    runtime_pubkey_matches = False
    runtime_balance_matches = False
    if runtime_state is not None:
        runtime_pubkey_matches = runtime_state.reward_pool_pubkey == reward_pool_pubkey
        runtime_balance_matches = bool(
            runtime_pubkey_matches
            and int(runtime_state.snapshot.reward_pool_balance) == actual_pool_balance
        )
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
    gate = evaluate_proof_mining_claimability_gate(
        reward_pool_configured=True,
        winner_matches_sender=winner_pubkey == sender,
        recipient_distinct_from_reward_pool=sender != reward_pool_pubkey,
        proposal_hash_matches_context=(
            claim_proposal_hash
            == str(getattr(proof_mining_context, "proposal_hash", ""))
        ),
        reward_pool_balance_non_negative=actual_pool_balance >= 0,
        runtime_state_present=runtime_state_was_present,
        reward_pool_pubkey_matches_state=runtime_pubkey_matches,
        reward_pool_balance_matches_state=runtime_balance_matches,
        manager_ok=True,
        reward_amount=reward_amount,
        reward_pool_before=actual_pool_balance,
        reward_pool_after=int(next_runtime_state.snapshot.reward_pool_balance),
    )
    if not gate.claimable:
        return (
            False,
            state,
            proof_mining_state,
            PROOF_MINING_REJECT_CODE_TO_ERROR.get(
                gate.reject_code,
                "proof mining claimability gate rejected",
            ),
        )
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
        oracle_pubkey=(oracle_pubkey or "").strip() or None,
        allow_isolated_markets=bool(allow_isolated),
        oracle_adapter_bridge_verifier=_oracle_adapter_bridge_verifier,
        require_oracle_adapter_for_clearinghouse_settle_epoch=_bool_env(
            "TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_CLEARINGHOUSE_SETTLE_EPOCH",
            default=True,
        ),
        require_oracle_adapter_for_isolated_partial_liquidate=_bool_env(
            "TAU_DEX_REQUIRE_ORACLE_ADAPTER_FOR_ISOLATED_PARTIAL_LIQUIDATE",
            default=True,
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
    _require_neutral_legacy_ce067_env(
        "TAU_DEX_ZUSD_REDEMPTION_SHUTDOWN_TCR_BPS",
        expected=11_000,
    )
    _require_neutral_legacy_ce067_env(
        "TAU_DEX_ZUSD_REDEMPTION_MIN_POST_TCR_BPS",
        expected=0,
    )
    _require_neutral_legacy_ce067_env(
        "TAU_DEX_ZUSD_MAX_EPOCH_REDEMPTION_FRACTION_BPS",
        expected=10_000,
    )
    oracle_pubkey = os.environ.get("TAU_DEX_ZUSD_ORACLE_PUBKEY") or os.environ.get("TAU_DEX_ORACLE_PUBKEY")
    epoch_operator_pubkey = os.environ.get(
        "TAU_DEX_ZUSD_EPOCH_OPERATOR_PUBKEY"
    ) or os.environ.get("TAU_DEX_OPERATOR_PUBKEY")
    protocol_fee_recipient_pubkey = os.environ.get(
        "TAU_DEX_ZUSD_PROTOCOL_FEE_RECIPIENT_PUBKEY"
    )
    asset_id = os.environ.get("TAU_DEX_ZUSD_ASSET_ID", "").strip() or None
    fee_stake_asset_id = os.environ.get("TAU_DEX_ZUSD_FEE_STAKE_ASSET_ID", "").strip() or None
    oracle_evidence_profile_raw = os.environ.get(
        "TAU_DEX_ZUSD_ORACLE_EVIDENCE_PROFILE",
        ZUSDOracleEvidenceProfile.FINALIZED_O3_V1.value,
    ).strip()
    try:
        oracle_evidence_profile = ZUSDOracleEvidenceProfile(
            oracle_evidence_profile_raw
        )
    except ValueError as exc:
        raise ValueError(
            "TAU_DEX_ZUSD_ORACLE_EVIDENCE_PROFILE must be an exact "
            "allowlisted profile value"
        ) from exc
    oracle_authorization_root = (
        os.environ.get(
            "TAU_DEX_ZUSD_ORACLE_AUTHORIZATION_RECEIPT_GRAPH_ROOT",
            "",
        ).strip()
        or None
    )
    return ZUSDMonetaryConfig(
        chain_id=chain_id,
        oracle_pubkey=(oracle_pubkey or "").strip() or None,
        epoch_operator_pubkey=(
            (epoch_operator_pubkey or "").strip() or None
        ),
        protocol_fee_recipient_pubkey=(
            (protocol_fee_recipient_pubkey or "").strip() or None
        ),
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
        borrow_fee_floor_bps=_int_env_alias("TAU_DEX_ZUSD_BORROW_FEE_FLOOR_BPS", "", default=0, maximum=10_000),
        borrow_fee_max_bps=_int_env_alias("TAU_DEX_ZUSD_BORROW_FEE_MAX_BPS", "", default=1_000, maximum=10_000),
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
        oracle_evidence_profile=oracle_evidence_profile,
        oracle_authorization_receipt_graph_root=oracle_authorization_root,
        shutdown_extension_profile=None,
    )


def _compute_app_tx_proposal_legacy_v1(
    *,
    app_state_json: str,
    chain_balances: Any,
    operations: Any,
    tx_sender_pubkey: str,
    block_timestamp: int,
    execution_clock: VerifiedExecutionClockV1 | None = None,
) -> Tuple[bool, str, str, Optional[Dict[str, int]], Optional[str]]:
    """Compute the legacy Tau application proposal representation.

    The returned native-balance mapping contains absolute post-state balances
    for the imperative shell to validate and commit.  This function does not
    persist application state or apply that returned patch itself.  Existing
    configured verifier adapters may still run as part of legacy validation;
    neither their evidence nor this proposal grants M6 commit-port or finality
    authority.  ``propose_app_tx_v1`` owns the typed boundary around this
    internal representation.  This function does not constitute an M6 commit
    port.
    """

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
    chain_id = os.environ.get("TAU_DEX_CHAIN_ID", "").strip() or os.environ.get("TAU_NETWORK_ID", "").strip() or "tau-local"
    canonical_zusd_asset_id = derive_zusd_tau_asset_id(chain_id=chain_id)
    token_symbol = os.environ.get("TAU_DEX_TOKEN_SYMBOL", "ZDEX").strip() or "ZDEX"
    configured_protocol_token_asset_id = os.environ.get(
        "TAU_DEX_PROTOCOL_TOKEN_ASSET_ID",
        "",
    ).strip()
    canonical_protocol_token_asset_id = configured_protocol_token_asset_id or hash_v0(
        "testnet_bundle_token_asset",
        {"chain_id": chain_id, "symbol": token_symbol},
    )

    try:
        state, proof_mining_state, zusd_monetary_state = _load_state(app_state_json)
    except Exception as exc:
        return False, app_state_json, "", None, str(exc)
    state = _sync_native_balances(state, chain_balances=chain_balances)
    try:
        assert_zusd_global_liability_cover(
            state=state,
            zusd_state=zusd_monetary_state,
            expected_zusd_asset_id=canonical_zusd_asset_id,
        )
    except Exception as exc:
        return False, app_state_json, "", None, str(exc)
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
        reserved_protocol_token_asset_id=canonical_protocol_token_asset_id,
        reserved_zusd_asset_id=canonical_zusd_asset_id,
    )
    if not ok:
        return False, app_state_json, "", None, err

    dex_ops = _select_dex_ops(operations)
    perp_ops = _select_perp_ops(operations)
    token_ops = _select_token_ops(operations)
    proof_mining_ops = _select_proof_mining_ops(operations)
    zusd_monetary_ops = _select_zusd_monetary_ops(operations)

    # A state carrying zUSD must pass through consensus epoch admission even
    # when this block has no user zUSD operation.
    if (
        not dex_ops
        and not perp_ops
        and not token_ops
        and not proof_mining_ops
        and not zusd_monetary_ops
        and zusd_monetary_state is None
    ):
        try:
            assert_zusd_global_liability_cover(
                state=state,
                zusd_state=zusd_monetary_state,
                expected_zusd_asset_id=canonical_zusd_asset_id,
            )
        except Exception as exc:
            return False, app_state_json, "", None, str(exc)
        canonical, app_hash = _canonical_state_and_hash(
            state,
            proof_mining_state=proof_mining_state,
            zusd_monetary_state=zusd_monetary_state,
        )
        return True, canonical, app_hash, None, None

    next_state = state
    if token_ops:
        ok, next_state, token_err = _apply_token_ops(
            next_state,
            token_ops.get(_TOKEN_OPS_KEY),
            chain_id=chain_id,
            tx_sender_pubkey=tx_sender_pubkey,
            block_timestamp=int(block_timestamp),
        )
        if not ok:
            return False, app_state_json, "", None, token_err or "token op rejected"

    if zusd_monetary_ops or zusd_monetary_state is not None:
        zusd_cfg = _build_zusd_monetary_config(chain_id=chain_id)
        mounted_zusd_ops = (
            zusd_monetary_ops.get(_ZUSD_MONETARY_OPS_KEY)
            if zusd_monetary_ops
            else []
        )
        zusd_res = apply_zusd_monetary_ops(
            config=zusd_cfg,
            state=next_state,
            zusd_state=zusd_monetary_state,
            operations=mounted_zusd_ops,
            tx_sender_pubkey=tx_sender_pubkey,
            block_timestamp=int(block_timestamp),
            execution_clock=execution_clock,
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
            tx_sender_pubkey=tx_sender_pubkey,
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
            tx_sender_pubkey=tx_sender_pubkey,
            chain_balances=chain_balances,
        )
        if not ok:
            return False, app_state_json, "", None, proof_err or "proof mining rejected"

    if perp_ops:
        perp_cfg = _build_perp_engine_config(chain_id=chain_id)
        perp_res = apply_perp_ops(
            config=perp_cfg,
            state=next_state,
            operations=perp_ops,
            tx_sender_pubkey=tx_sender_pubkey,
            block_timestamp=int(block_timestamp),
        )
        if not perp_res.ok or perp_res.state is None:
            return False, app_state_json, "", None, perp_res.error or "PERP rejected"
        next_state = perp_res.state

    try:
        assert_zusd_global_liability_cover(
            state=next_state,
            zusd_state=zusd_monetary_state,
            expected_zusd_asset_id=canonical_zusd_asset_id,
        )
    except Exception as exc:
        return False, app_state_json, "", None, str(exc)

    balances_patch = _balances_patch_for_native(before=chain_balances, after_state=next_state)
    canonical, app_hash = _canonical_state_and_hash(
        next_state,
        proof_mining_state=proof_mining_state,
        zusd_monetary_state=zusd_monetary_state,
    )
    return True, canonical, app_hash, balances_patch, None


def propose_app_tx_v1(
    *,
    app_state_json: str,
    chain_balances: Any,
    operations: Any,
    tx_sender_pubkey: str,
    block_timestamp: int,
    execution_clock: VerifiedExecutionClockV1 | None = None,
) -> TauAppTxProposalV1:
    """Return the typed, proposal-only form of the legacy Tau adapter result."""

    return TauAppTxProposalV1.from_legacy_result(
        _compute_app_tx_proposal_legacy_v1(
            app_state_json=app_state_json,
            chain_balances=chain_balances,
            operations=operations,
            tx_sender_pubkey=tx_sender_pubkey,
            block_timestamp=block_timestamp,
            execution_clock=execution_clock,
        )
    )


def apply_app_tx(
    *,
    app_state_json: str,
    chain_balances: Any,
    operations: Any,
    tx_sender_pubkey: str,
    block_timestamp: int,
    execution_clock: VerifiedExecutionClockV1 | None = None,
) -> Tuple[bool, str, str, Optional[Dict[str, int]], Optional[str]]:
    """Return the legacy tuple compatibility view of a typed proposal.

    The typed proposal boundary is the implementation path.  This adapter
    preserves the historical caller contract and never commits a proposal or
    grants M6 finality authority.
    """

    return propose_app_tx_v1(
        app_state_json=app_state_json,
        chain_balances=chain_balances,
        operations=operations,
        tx_sender_pubkey=tx_sender_pubkey,
        block_timestamp=block_timestamp,
        execution_clock=execution_clock,
    ).to_legacy_result_v1()
