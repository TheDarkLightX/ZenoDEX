"""Tau-native zUSD transfer helpers and replayable proof lane.

zUSD supply changes belong to the collateralized monetary kernel.  The generic
TauToken constructor remains available for non-managed assets, while this zUSD
transport surface admits transfers only.
"""

from __future__ import annotations

import hashlib
import os
from dataclasses import dataclass
from typing import Any, Literal

from ..core.managed_asset_policy import (
    AssetOperationV1,
    build_zusd_managed_asset_policy,
    check_managed_asset_operation,
)
from ..state.canonical import canonical_hex_fixed_allow_0x, domain_sep_bytes
from .tau_net_client import bls_pubkey_hex_from_privkey, build_signed_tau_transaction
from .tau_runner import find_tau_bin, run_tau_spec_steps
from .tau_witness import (
    PROTOCOL_TOKEN_V1,
    ZUSD_TRANSFER_GUARD_V1,
    build_protocol_token_v1_step,
    build_zusd_transfer_guard_v1_step,
)

TokenAction = Literal["transfer", "mint", "burn"]
ZUSDTransportAction = Literal["transfer"]
_TOKEN_OPS_KEY = "9"
_U32_MAX = 0xFFFFFFFF


@dataclass(frozen=True)
class ZUSDTauTokenConfig:
    enabled: bool = False
    timeout_s: float = 2.0
    tau_bin: str | None = None
    allow_path_lookup: bool = False


@dataclass(frozen=True)
class TokenTauReceipt:
    spec_id: str
    gate_output: str
    steps: tuple[dict[str, int], ...]
    expected_ok: bool = True


@dataclass(frozen=True)
class ZUSDTauTokenReport:
    action: TokenAction
    asset_id: str
    nonce_key: str
    nonce_before: int
    nonce_after: int
    operation: dict[str, Any]
    operations: dict[str, Any]
    sender_balance_after: int
    recipient_balance_after: int
    supply_after: int
    tau_receipts: tuple[TokenTauReceipt, ...] = ()
    tau_tx_payload: dict[str, Any] | None = None


def _require_u32(name: str, value: object, *, minimum: int = 0) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    out = int(value)
    if out < minimum or out > _U32_MAX:
        raise ValueError(f"{name} out of u32 range: {out}")
    return out


def _canonical_pubkey(value: str, *, name: str) -> str:
    return canonical_hex_fixed_allow_0x(value, nbytes=48, name=name)


def _canonical_asset_id(value: str, *, name: str) -> str:
    return canonical_hex_fixed_allow_0x(value, nbytes=32, name=name)


def derive_zusd_tau_asset_id(*, chain_id: str = "tau-net-alpha", symbol: str = "zUSD") -> str:
    if not isinstance(chain_id, str) or not chain_id.strip():
        raise ValueError("chain_id must be a non-empty string")
    if not isinstance(symbol, str) or not symbol.strip():
        raise ValueError("symbol must be a non-empty string")
    payload = domain_sep_bytes("dex_asset_id", version=1) + symbol.strip().encode("utf-8") + chain_id.strip().encode("utf-8")
    return "0x" + hashlib.sha256(payload).hexdigest()


def token_sender_nonce_key(sender_pubkey: str) -> str:
    sender = _canonical_pubkey(sender_pubkey, name="sender_pubkey")
    payload = b"zenodex:tau_token_nonce:v1\x00" + sender.encode("ascii")
    return "0x" + hashlib.sha384(payload).hexdigest()


def create_tau_token_operation(
    *,
    action: object,
    asset_id: str,
    nonce: int,
    amount: int,
    deadline: int,
    sender_pubkey: str | None = None,
    to_pubkey: str | None = None,
    operator_pubkey: str | None = None,
) -> dict[str, Any]:
    if type(action) is not str or action not in {"transfer", "mint", "burn"}:
        raise ValueError("action must be transfer, mint, or burn")
    nonce = _require_u32("nonce", nonce, minimum=1)
    amount = _require_u32("amount", amount, minimum=1)
    deadline = _require_u32("deadline", deadline, minimum=1)
    asset = _canonical_asset_id(asset_id, name="asset_id")
    op: dict[str, Any] = {
        "module": "TauToken",
        "version": "0.1",
        "action": action,
        "asset": asset,
        "amount": amount,
        "nonce": nonce,
        "deadline": deadline,
    }
    if action == "transfer":
        if sender_pubkey is None or to_pubkey is None:
            raise ValueError("transfer requires sender_pubkey and to_pubkey")
        op["sender_pubkey"] = _canonical_pubkey(sender_pubkey, name="sender_pubkey")
        op["to_pubkey"] = _canonical_pubkey(to_pubkey, name="to_pubkey")
    elif action == "mint":
        if operator_pubkey is None or to_pubkey is None:
            raise ValueError("mint requires operator_pubkey and to_pubkey")
        op["operator_pubkey"] = _canonical_pubkey(operator_pubkey, name="operator_pubkey")
        op["to_pubkey"] = _canonical_pubkey(to_pubkey, name="to_pubkey")
    else:
        if sender_pubkey is None:
            raise ValueError("burn requires sender_pubkey")
        op["sender_pubkey"] = _canonical_pubkey(sender_pubkey, name="sender_pubkey")
    return op


def require_zusd_tau_transport_action(
    *,
    action: object,
    asset_id: str,
) -> ZUSDTransportAction:
    """Return the sole zUSD token-transport action or raise a typed-policy error."""

    if type(action) is not str or action not in {"transfer", "mint", "burn"}:
        raise ValueError("action must be transfer, mint, or burn")
    asset = _canonical_asset_id(asset_id, name="asset_id")
    if action == "transfer":
        return "transfer"
    operation = (
        AssetOperationV1.GENERIC_MINT
        if action == "mint"
        else AssetOperationV1.GENERIC_BURN
    )
    reject = check_managed_asset_operation(
        policy=build_zusd_managed_asset_policy(asset),
        asset_id=asset,
        operation=operation,
    )
    if reject is None:
        raise RuntimeError("managed zUSD supply policy failed to reject generic operation")
    raise ValueError(reject.message())


def _resolve_tau_bin(config: ZUSDTauTokenConfig) -> tuple[bool, str | None, str | None]:
    if config.tau_bin:
        tau_bin = str(config.tau_bin)
        if not config.allow_path_lookup:
            if not os.path.isabs(tau_bin):
                return False, None, "tau_bin must be an absolute path when allow_path_lookup=False"
            if not (os.path.isfile(tau_bin) and os.access(tau_bin, os.X_OK)):
                return False, None, f"tau_bin is not an executable file: {tau_bin}"
        return True, tau_bin, None
    if config.allow_path_lookup:
        tau_bin = find_tau_bin()
        if tau_bin:
            return True, tau_bin, None
        return False, None, "tau binary not found (fail-closed)"
    return False, None, "tau_bin not configured (set ZUSDTauTokenConfig.tau_bin)"


def _verify_tau_receipt(
    *,
    tau_bin: str,
    config: ZUSDTauTokenConfig,
    receipt: TokenTauReceipt,
) -> str | None:
    spec_path = PROTOCOL_TOKEN_V1.path if receipt.spec_id == PROTOCOL_TOKEN_V1.spec_id else ZUSD_TRANSFER_GUARD_V1.path
    try:
        outputs = run_tau_spec_steps(
            tau_bin=tau_bin,
            spec_path=spec_path,
            steps=list(receipt.steps),
            timeout_s=config.timeout_s,
        )
    except Exception as exc:
        return f"tau_token_runner_error:{type(exc).__name__}:{exc}"
    tau_gate_value = outputs.get(0, {}).get(receipt.gate_output)
    if tau_gate_value is None:
        return f"tau_token_missing_output:{receipt.gate_output}"
    tau_ok = int(tau_gate_value) == 1
    if tau_ok != receipt.expected_ok:
        return f"tau_token_mismatch:{receipt.spec_id}:local={int(receipt.expected_ok)},tau={int(tau_ok)}"
    return None


def prepare_zusd_tau_token_operation(
    *,
    action: TokenAction,
    amount: int,
    deadline: int,
    last_used_nonce: int,
    total_supply_before: int,
    sender_balance_before: int = 0,
    recipient_balance_before: int = 0,
    sender_pubkey: str | None = None,
    recipient_pubkey: str | None = None,
    operator_pubkey: str | None = None,
    paused: bool = False,
    auth_ok: bool = True,
    asset_id: str | None = None,
    chain_id: str = "tau-net-alpha",
    tau_config: ZUSDTauTokenConfig | None = None,
    signer_privkey: str | int | bytes | bytearray | None = None,
    tx_sequence_number: int | None = None,
    tx_expiration_time: int | None = None,
    tx_fee_limit: str | int = "0",
) -> ZUSDTauTokenReport:
    amount = _require_u32("amount", amount, minimum=1)
    deadline = _require_u32("deadline", deadline, minimum=1)
    nonce_before = _require_u32("last_used_nonce", last_used_nonce, minimum=0)
    supply_before = _require_u32("total_supply_before", total_supply_before, minimum=0)
    sender_before = _require_u32("sender_balance_before", sender_balance_before, minimum=0)
    recipient_before = _require_u32("recipient_balance_before", recipient_balance_before, minimum=0)
    if (tx_sequence_number is None) != (tx_expiration_time is None):
        raise ValueError("tx_sequence_number and tx_expiration_time must be provided together")

    asset = (
        _canonical_asset_id(asset_id, name="asset_id")
        if asset_id is not None
        else derive_zusd_tau_asset_id(chain_id=chain_id)
    )
    action = require_zusd_tau_transport_action(action=action, asset_id=asset)
    nonce = nonce_before + 1
    if nonce > _U32_MAX:
        raise ValueError("next token nonce exceeds u32")

    if sender_pubkey is None or recipient_pubkey is None:
        raise ValueError("transfer requires sender_pubkey and recipient_pubkey")
    sender = _canonical_pubkey(sender_pubkey, name="sender_pubkey")
    recipient = _canonical_pubkey(recipient_pubkey, name="recipient_pubkey")
    if sender_before < amount:
        raise ValueError("sender_balance_before insufficient for transfer")
    if recipient_before + amount > _U32_MAX:
        raise ValueError("recipient balance overflow")
    sender_after = sender_before - amount
    recipient_after = recipient_before + amount
    supply_after = supply_before
    actor_pubkey = sender

    if signer_privkey is not None:
        signer_pubkey = _canonical_pubkey(
            "0x" + bls_pubkey_hex_from_privkey(signer_privkey),
            name="signer_pubkey",
        )
        if signer_pubkey != actor_pubkey:
            raise ValueError("signer_privkey does not match token actor pubkey")

    operation = create_tau_token_operation(
        action="transfer",
        asset_id=asset,
        nonce=nonce,
        amount=amount,
        deadline=deadline,
        sender_pubkey=sender,
        to_pubkey=recipient,
    )
    operations = {_TOKEN_OPS_KEY: [operation]}

    tau_receipts: list[TokenTauReceipt] = [
        TokenTauReceipt(
            spec_id=ZUSD_TRANSFER_GUARD_V1.spec_id,
            gate_output=ZUSD_TRANSFER_GUARD_V1.gate_output,
            steps=(
                build_zusd_transfer_guard_v1_step(
                    amount_positive=1,
                    sender_has_balance=1 if sender_before >= amount else 0,
                    transfer_deltas_match=(
                        1
                        if sender_after + amount == sender_before
                        and recipient_after - amount == recipient_before
                        else 0
                    ),
                    sender_auth_ok=1 if auth_ok else 0,
                    recipient_valid=1,
                    paused=1 if paused else 0,
                ),
            ),
            expected_ok=(not paused) and bool(auth_ok),
        ),
        TokenTauReceipt(
            spec_id=PROTOCOL_TOKEN_V1.spec_id,
            gate_output=PROTOCOL_TOKEN_V1.gate_output,
            steps=(
                build_protocol_token_v1_step(
                    from_before=sender_before,
                    to_before=recipient_before,
                    supply_before=supply_before,
                    amount=amount,
                    from_after=sender_after,
                    to_after=recipient_after,
                    supply_after=supply_after,
                    do_transfer=1,
                    do_mint=0,
                    do_burn=0,
                ),
            ),
            expected_ok=True,
        ),
    ]

    resolved_tau_config = tau_config or ZUSDTauTokenConfig()
    if resolved_tau_config.enabled:
        ok, tau_bin, err = _resolve_tau_bin(resolved_tau_config)
        if not ok or tau_bin is None:
            raise ValueError(f"tau_tool_unavailable:{err}")
        for receipt in tau_receipts:
            tau_error = _verify_tau_receipt(tau_bin=tau_bin, config=resolved_tau_config, receipt=receipt)
            if tau_error is not None:
                raise ValueError(tau_error)

    tau_tx_payload: dict[str, Any] | None = None
    if tx_sequence_number is not None and tx_expiration_time is not None:
        if signer_privkey is None:
            raise ValueError("signer_privkey is required when building a Tau transaction payload")
        tau_tx_payload = build_signed_tau_transaction(
            privkey=signer_privkey,
            sequence_number=_require_u32("tx_sequence_number", tx_sequence_number, minimum=0),
            expiration_time=_require_u32("tx_expiration_time", tx_expiration_time, minimum=1),
            operations=operations,
            fee_limit=tx_fee_limit,
        )

    return ZUSDTauTokenReport(
        action=action,
        asset_id=asset,
        nonce_key=token_sender_nonce_key(actor_pubkey),
        nonce_before=nonce_before,
        nonce_after=nonce,
        operation=operation,
        operations=operations,
        sender_balance_after=sender_after,
        recipient_balance_after=recipient_after,
        supply_after=supply_after,
        tau_receipts=tuple(tau_receipts),
        tau_tx_payload=tau_tx_payload,
    )
