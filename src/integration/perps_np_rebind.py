"""Production RebindFn for `perps_np.deposit_collateral` (WS2 gate-8/9 mirror).

Recomputes the binding hashes the client expects in a VERIFIED journal from the
operation the client REQUESTED — never from anything the host sent. This is the
canonical-encoder mirror of `zk/state_proof_risc0/shared/src/surfaces.rs`:

  operation_hash           == perps_np_operation_hash_v1([DepositCollateral{..}])
  collateral_binding_hash  == perps_np_collateral_bindings_hash_v1(actions)
  oracle_binding_hash      == perps_np_oracle_bindings_hash_v1(actions)  (empty for deposit-only)

Parity is pinned by tests against real guest journals (see
tests/integration/test_perps_np_rebind_parity.py); any drift here is the
"client rejects every proof" bug class, so the encodings below cite the exact
Rust source they mirror.

Fail-closed contract: this rebind is a TOTAL function. Any input outside the
encoder domain returns {} (no raise), which `decide_admission` gate 8 turns into
REFUSE_OPERATION_MISMATCH. bool is explicitly excluded from int fields
(isinstance(True, int) is True; the repo-standard `type(x) is int` gate).
"""

from __future__ import annotations

import hashlib
from typing import Any, Mapping

from src.integration.client_admission_decision import RequestedOperation

_OPERATION_DOMAIN = b"zenodex.perps_np.operation.v1:"
_DEPOSIT_BINDING_DOMAIN = b"zenodex.perps_np.collateral_deposit_binding.v1:"
_COLLATERAL_BINDINGS_DOMAIN = b"zenodex.perps_np.collateral_bindings.v1:"
_ORACLE_BINDINGS_DOMAIN = b"zenodex.oracle_bindings.v1:"

# Mirrors surfaces.rs PROOF_TYPE_ZUSD / default_zusd_asset() / the action tag byte
# for PerpsNpActionV1::DepositCollateral.
_ZUSD_PROOF_TYPE = "risc0.zenodex_zusd_transition.v1"
_ZUSD_ASSET = "zUSD"
_DEPOSIT_ACTION_TAG = b"\x01"

_I128_MIN = -(1 << 127)
_I128_MAX = (1 << 127) - 1
_U64_MAX = (1 << 64) - 1
_U32_MAX = (1 << 32) - 1

_COLLATERAL_BINDING_KEYS = (
    "source_proof_type",
    "source_state_hash",
    "balance_root_hash",
    "balance_delta_hash",
)


def _is_str(value: Any) -> bool:
    return type(value) is str


def _is_int(value: Any) -> bool:
    return type(value) is int


def _u32(n: int) -> bytes:
    return n.to_bytes(4, "big")


def _u64(n: int) -> bytes:
    return n.to_bytes(8, "big")


def _i128(n: int) -> bytes:
    return n.to_bytes(16, "big", signed=True)


def _str_enc(s: str) -> bytes:
    raw = s.encode("utf-8")
    return _u32(len(raw)) + raw


def _normalized_hex32_text(value: str) -> str:
    # Mirrors surfaces.rs normalized_hex32_text: strip one 0x prefix, lowercase.
    raw = value[2:] if value.startswith("0x") else value
    return raw.lower()


def _is_valid_hex32_text(value: str) -> bool:
    raw = _normalized_hex32_text(value)
    if len(raw) != 64:
        return False
    try:
        bytes.fromhex(raw)
    except ValueError:
        return False
    return True


def _valid_collateral_binding(binding: Mapping[str, Any]) -> bool:
    # Mirrors surfaces.rs validate_collateral_binding (closed shape added here:
    # an extra key cannot change the hash, but accepting one would mask caller bugs).
    if set(binding.keys()) != set(_COLLATERAL_BINDING_KEYS):
        return False
    if not all(_is_str(binding[k]) for k in _COLLATERAL_BINDING_KEYS):
        return False
    if binding["source_proof_type"] != _ZUSD_PROOF_TYPE:
        return False
    return all(
        _is_valid_hex32_text(binding[k])
        for k in ("source_state_hash", "balance_root_hash", "balance_delta_hash")
    )


def _encode_optional_collateral_binding(binding: Mapping[str, Any] | None) -> bytes:
    # Mirrors surfaces.rs hash_optional_collateral_binding.
    if binding is None:
        return b"\x00"
    return (
        b"\x01"
        + _str_enc(binding["source_proof_type"])
        + _str_enc(_normalized_hex32_text(binding["source_state_hash"]))
        + _str_enc(_normalized_hex32_text(binding["balance_root_hash"]))
        + _str_enc(_normalized_hex32_text(binding["balance_delta_hash"]))
    )


def _deposit_fields_valid(fields: Mapping[str, Any]) -> bool:
    required = {"pubkey", "asset", "amount_e8", "nonce"}
    allowed = required | {"collateral_binding"}
    keys = set(fields.keys())
    if not required.issubset(keys) or not keys.issubset(allowed):
        return False
    if not _is_str(fields["pubkey"]) or not fields["pubkey"]:
        return False
    if not _is_str(fields["asset"]) or not fields["asset"]:
        return False
    if not _is_int(fields["amount_e8"]) or not (_I128_MIN <= fields["amount_e8"] <= _I128_MAX):
        return False
    if not _is_int(fields["nonce"]) or not (0 <= fields["nonce"] <= _U64_MAX):
        return False
    binding = fields.get("collateral_binding")
    if binding is not None:
        if not isinstance(binding, Mapping) or not _valid_collateral_binding(binding):
            return False
    # Mirrors perps_collateral_deposit_binding_hash_v1: zUSD collateral REQUIRES
    # an explicit binding (a bare zUSD amount has no provenance).
    if fields["asset"] == _ZUSD_ASSET and binding is None:
        return False
    return True


def _deposit_action_encoding(fields: Mapping[str, Any]) -> bytes:
    return (
        _DEPOSIT_ACTION_TAG
        + _str_enc(fields["pubkey"])
        + _str_enc(fields["asset"])
        + _i128(fields["amount_e8"])
        + _u64(fields["nonce"])
        + _encode_optional_collateral_binding(fields.get("collateral_binding"))
    )


def deposit_operation_hash(fields: Mapping[str, Any]) -> bytes:
    """perps_np_operation_hash_v1 over the single-action list [DepositCollateral]."""
    h = hashlib.sha256()
    h.update(_OPERATION_DOMAIN)
    h.update(_u32(1))
    h.update(_deposit_action_encoding(fields))
    return h.digest()


def deposit_collateral_bindings_hash(fields: Mapping[str, Any]) -> bytes:
    """perps_np_collateral_bindings_hash_v1 over the single deposit action."""
    inner = hashlib.sha256()
    inner.update(_DEPOSIT_BINDING_DOMAIN)
    inner.update(_str_enc(fields["pubkey"]))
    inner.update(_str_enc(fields["asset"]))
    inner.update(_i128(fields["amount_e8"]))
    inner.update(_u64(fields["nonce"]))
    inner.update(_encode_optional_collateral_binding(fields.get("collateral_binding")))
    outer = hashlib.sha256()
    outer.update(_COLLATERAL_BINDINGS_DOMAIN)
    outer.update(_u32(1))
    outer.update(inner.digest())
    return outer.digest()


def empty_oracle_bindings_hash() -> bytes:
    """perps_np_oracle_bindings_hash_v1 for an action list with no RunEpoch."""
    h = hashlib.sha256()
    h.update(_ORACLE_BINDINGS_DOMAIN)
    h.update(_u32(0))
    return h.digest()


def perps_np_deposit_rebind(operation: RequestedOperation) -> Mapping[str, bytes]:
    """The production RebindFn for (perps_np, deposit_collateral).

    Returns {} (-> REFUSE at gate 8) for anything outside the encoder domain;
    never raises, never reads host data.
    """
    if operation.surface != "perps_np" or operation.operation != "deposit_collateral":
        return {}
    fields = operation.fields
    if not isinstance(fields, Mapping) or not _deposit_fields_valid(fields):
        return {}
    return {
        "operation_hash": deposit_operation_hash(fields),
        "collateral_binding_hash": deposit_collateral_bindings_hash(fields),
        "oracle_binding_hash": empty_oracle_bindings_hash(),
    }
