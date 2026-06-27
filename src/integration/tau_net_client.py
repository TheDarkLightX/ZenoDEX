"""
Tau Net Testnet RPC client helpers (local node).

This module talks to the Tau Testnet Alpha node's TCP command interface
(`external/tau-testnet/server.py`) and constructs properly signed `sendtx`
payloads.
"""

from __future__ import annotations

import hashlib
import json
import re
import socket
import time
from dataclasses import dataclass
from typing import Any, Dict, Mapping, Optional

from ..core.dex_intent_auth_message import hash_dex_intent_auth_message_v1
from ..core.perp_submission_auth_message import hash_perp_op_auth_message_v1
from ..state.canonical import canonical_json_bytes

try:
    from py_ecc.bls import G2Basic

    _BLS_AVAILABLE = True
except ImportError:  # pragma: no cover - optional dependency
    G2Basic = None
    _BLS_AVAILABLE = False

try:
    # Used only for secret-key validation (range checks).
    from py_ecc.optimized_bls12_381 import curve_order as _BLS12_381_CURVE_ORDER
except ImportError:  # pragma: no cover - optional dependency
    _BLS12_381_CURVE_ORDER = None

try:
    from blake3 import blake3 as _blake3

    _BLAKE3_AVAILABLE = True
except ImportError:  # pragma: no cover - optional dependency
    _blake3 = None
    _BLAKE3_AVAILABLE = False


class TauNetRpcError(RuntimeError):
    pass


@dataclass(frozen=True)
class TauNetTcpConfig:
    host: str = "127.0.0.1"
    port: int = 65432
    timeout_s: float = 3.0
    recv_max_bytes: int = 1_048_576


_DEFAULT_TAU_NET_TCP_CONFIG = TauNetTcpConfig()


def _require_bls() -> Any:
    if not _BLS_AVAILABLE or G2Basic is None:
        raise TauNetRpcError("py_ecc.bls is required for Tau tx signing (install py-ecc)")
    return G2Basic


def _coerce_nonnegative_int(value: object, *, label: str) -> int:
    if isinstance(value, bool):
        raise ValueError(f"{label} must be a non-negative integer")
    if not isinstance(value, (int, float, str, bytes, bytearray)):
        raise ValueError(f"{label} must be a non-negative integer")
    try:
        parsed = int(value)
    except (OverflowError, TypeError, ValueError) as exc:
        raise ValueError(f"{label} must be a non-negative integer") from exc
    if isinstance(value, float) and not value.is_integer():
        raise ValueError(f"{label} must be a non-negative integer")
    if parsed < 0:
        raise ValueError(f"{label} must be a non-negative integer")
    return parsed


def _coerce_positive_int(value: object, *, label: str) -> int:
    parsed = _coerce_nonnegative_int(value, label=label)
    if parsed <= 0:
        raise ValueError(f"{label} must be a positive integer")
    return parsed


def _parse_privkey_int(privkey: int) -> int:
    sk = int(privkey)
    if sk <= 0:
        raise ValueError("privkey must be positive")
    if _BLS12_381_CURVE_ORDER is not None and sk >= int(_BLS12_381_CURVE_ORDER):
        raise ValueError("privkey out of range (must be < BLS12-381 curve order)")
    return sk


def _parse_privkey_bytes(privkey: bytes | bytearray) -> int:
    raw = bytes(privkey)
    if len(raw) != 32:
        raise ValueError("privkey bytes must be length 32")
    sk = int.from_bytes(raw, byteorder="big", signed=False)
    return _parse_privkey_int(sk)


def _parse_privkey_hex_32_bytes(hex_str: str, *, label: str) -> bytes:
    if not re.fullmatch(r"[0-9a-fA-F]+", hex_str or ""):
        raise ValueError(f"{label} must contain only 0-9a-f")
    raw = bytes.fromhex(hex_str)
    if len(raw) != 32:
        raise ValueError(f"{label} must decode to 32 bytes, got {len(raw)}")
    return raw


def _parse_privkey_str(privkey: str) -> int:
    s = privkey.strip()
    if not s:
        raise ValueError("privkey must be non-empty")

    if s.lower().startswith("0x"):
        raw = _parse_privkey_hex_32_bytes(s[2:], label="privkey hex")
        return _parse_privkey_int(int.from_bytes(raw, byteorder="big", signed=False))

    # Accept bare 32-byte hex (64 chars), including digit-only keys.
    if len(s) == 64 and re.fullmatch(r"[0-9a-fA-F]+", s):
        return _parse_privkey_int(int.from_bytes(bytes.fromhex(s), byteorder="big", signed=False))

    if re.fullmatch(r"[0-9]+", s):
        return _parse_privkey_int(int(s, 10))

    raise ValueError("privkey must be 32-byte hex (0x... or 64 hex chars) or a positive integer string")


def _parse_privkey_to_int(privkey: str | int | bytes | bytearray) -> int:
    if isinstance(privkey, int):
        return _parse_privkey_int(privkey)
    if isinstance(privkey, (bytes, bytearray)):
        return _parse_privkey_bytes(privkey)
    if isinstance(privkey, str):
        return _parse_privkey_str(privkey)
    raise TypeError("privkey must be str|int|bytes")


def bls_pubkey_hex_from_privkey(privkey: str | int | bytes | bytearray) -> str:
    bls = _require_bls()
    sk_int = _parse_privkey_to_int(privkey)
    return bls.SkToPk(sk_int).hex()


def _tx_signing_message_bytes(payload: Mapping[str, Any]) -> bytes:
    signing_dict = {
        "sender_pubkey": payload["sender_pubkey"],
        "sequence_number": payload["sequence_number"],
        "expiration_time": payload["expiration_time"],
        "operations": payload["operations"],
        "fee_limit": payload["fee_limit"],
    }
    return canonical_json_bytes(signing_dict)


def sign_tau_transaction_payload(payload_wo_sig: Dict[str, Any], *, privkey: str | int | bytes | bytearray) -> str:
    bls = _require_bls()
    sk_int = _parse_privkey_to_int(privkey)
    msg_bytes = _tx_signing_message_bytes(payload_wo_sig)
    msg_hash = hashlib.sha256(msg_bytes).digest()
    sig_bytes = bls.Sign(sk_int, msg_hash)
    return sig_bytes.hex()


def encode_tau_operations_for_wire(operations: Mapping[str, Any]) -> Dict[str, Any]:
    """
    Encode Tau operation streams into the exact wire format expected by tau-testnet.

    Custom streams must be `str|int` (or lists thereof) at the transport boundary,
    so structured JSON payloads are canonicalized into strings.
    """
    encoded_ops: Dict[str, Any] = {}
    for k, v in dict(operations).items():
        if k in ("0", "1"):
            encoded_ops[k] = v
            continue
        if isinstance(v, bool):
            raise ValueError(f"operation stream {k!r}: bool values are not allowed")
        if isinstance(v, (str, int)):
            encoded_ops[k] = v
            continue
        encoded_ops[k] = canonical_json_bytes(v).decode("utf-8")
    return encoded_ops


def verify_tau_transaction_payload_signature(payload: Mapping[str, Any]) -> bool:
    """
    Verify a signed Tau transaction payload.

    Returns False on malformed payloads or invalid signatures.
    """
    if not _BLS_AVAILABLE or G2Basic is None:
        return False
    try:
        sender_pubkey = payload["sender_pubkey"]
        signature = payload["signature"]
        if not isinstance(sender_pubkey, str) or not isinstance(signature, str):
            return False
        msg_bytes = _tx_signing_message_bytes(payload)
        msg_hash = hashlib.sha256(msg_bytes).digest()
        pubkey_bytes = bytes.fromhex(sender_pubkey)
        sig_bytes = bytes.fromhex(signature)
        return bool(G2Basic.Verify(pubkey_bytes, msg_hash, sig_bytes))
    except Exception:
        return False


def tau_rpc_response_is_success(response: object) -> bool:
    if not isinstance(response, str):
        return False
    text = response.strip()
    if not text or "\x00" in text:
        return False
    normalized = text.upper()
    if normalized == "SUCCESS":
        return True
    if not normalized.startswith("SUCCESS"):
        return False
    suffix = normalized[len("SUCCESS") :]
    return bool(suffix) and suffix[0] in {":", " ", "\t"}


def tau_rpc_invalid_sequence_numbers(response: object) -> tuple[int, int] | None:
    """Parse Tau's invalid-sequence response as ``(expected, got)`` when present."""

    if not isinstance(response, str):
        return None
    match = re.search(
        r"invalid\s+sequence\s+number\s*:\s*expected\s+([0-9]+)\s*,\s*got\s+([0-9]+)",
        response,
        flags=re.IGNORECASE,
    )
    if match is None:
        return None
    return int(match.group(1)), int(match.group(2))


def build_signed_tau_transaction(
    *,
    privkey: str | int | bytes | bytearray,
    sequence_number: int,
    expiration_time: int,
    operations: Dict[str, Any],
    fee_limit: str | int = "0",
) -> Dict[str, Any]:
    _require_bls()
    sender_pubkey = bls_pubkey_hex_from_privkey(privkey)
    encoded_ops = encode_tau_operations_for_wire(operations)

    payload: Dict[str, Any] = {
        "sender_pubkey": sender_pubkey,
        "sequence_number": _coerce_nonnegative_int(sequence_number, label="sequence_number"),
        "expiration_time": _coerce_nonnegative_int(expiration_time, label="expiration_time"),
        "operations": encoded_ops,
        "fee_limit": str(fee_limit),
    }
    payload["signature"] = sign_tau_transaction_payload(payload, privkey=privkey)
    return payload


def sign_dex_intent_for_engine(
    intent_dict: Mapping[str, Any],
    *,
    privkey: str | int | bytes | bytearray,
    chain_id: str,
) -> str:
    """
    Sign an intent according to `src.integration.dex_engine` signature policy.

    Returns a hex signature string with a `0x` prefix.
    """
    bls = _require_bls()
    sk_int = _parse_privkey_to_int(privkey)
    msg_hash = hash_dex_intent_auth_message_v1(intent_dict, chain_id=chain_id)
    sig_bytes = bls.Sign(sk_int, msg_hash)
    return "0x" + sig_bytes.hex()


def sign_perp_op_for_engine(
    op_dict: Mapping[str, Any],
    *,
    privkey: str | int | bytes | bytearray,
    chain_id: str,
    signer_pubkey: str,
    nonce: int,
) -> str:
    """
    Sign a perps operation according to `src.integration.perp_engine` signature policy.

    The per-op signature is used for peer-to-peer authorization in clearinghouse markets
    (e.g. joint market init, matched position updates, oracle-authorized price publication).

    The signed message is:
    - domain-separated by `chain_id` (prevents cross-network replay),
    - encoded as canonical JSON (stable hash),
    - bound to `signer_pubkey` and a monotone `nonce` (replay protection).

    The exact fields included in the signed payload depend on `op_dict["action"]`
    and are defined by the shared perps auth-message contract. This helper uses
    the same pure builder as the engine so the signed preimage stays in sync.

    Returns a hex signature string with a `0x` prefix.
    """
    bls = _require_bls()
    sk_int = _parse_privkey_to_int(privkey)
    if not isinstance(signer_pubkey, str) or not signer_pubkey:
        raise ValueError("signer_pubkey must be a non-empty string")
    if not isinstance(nonce, int) or isinstance(nonce, bool) or nonce <= 0:
        raise ValueError("nonce must be a positive int")

    msg_hash = hash_perp_op_auth_message_v1(
        op_dict,
        chain_id=chain_id,
        signer_pubkey=signer_pubkey,
        nonce=int(nonce),
    )
    sig_bytes = bls.Sign(sk_int, msg_hash)
    return "0x" + sig_bytes.hex()


@dataclass(frozen=True)
class TauNetAppStateView:
    app_hash: str
    app_state: Any


@dataclass(frozen=True)
class TauNetStateProofView:
    state_hash: str
    present: bool
    proof_type: str | None = None
    proof_bytes: int | None = None
    proof_sha256: str | None = None
    error: str | None = None


@dataclass(frozen=True)
class TauNetTauStateView:
    state_hash: str
    rules: str
    accounts_hash: str
    app_hash: str


def _coerce_mapping_json_response(raw: str, *, label: str) -> Mapping[str, Any]:
    try:
        payload = json.loads(raw)
    except json.JSONDecodeError as exc:
        raise TauNetRpcError(f"{label} returned invalid JSON: {exc}; raw={raw!r}") from exc
    if not isinstance(payload, Mapping):
        raise TauNetRpcError(f"{label} returned non-object JSON: type={type(payload).__name__}, raw={raw!r}")
    return payload


def _coerce_hex_32_noprefix(value: object, *, label: str) -> str:
    if not isinstance(value, str) or not re.fullmatch(r"[0-9a-fA-F]{64}", value.strip()):
        raise TauNetRpcError(f"{label} must be a 64-hex string, got {value!r}")
    return value.strip().lower()


def compute_tau_state_commitment_hash_hex(*, rules: str, accounts_hash: str, app_hash: str = "") -> str:
    if not _BLAKE3_AVAILABLE or _blake3 is None:
        raise TauNetRpcError("blake3 is required for Tau state commitment validation (install blake3)")
    if not isinstance(rules, str):
        raise TauNetRpcError(f"tau_state rules must be a string, got {rules!r}")
    normalized_accounts_hash = _coerce_hex_32_noprefix(accounts_hash, label="tau_state accounts_hash")
    normalized_app_hash = ""
    if app_hash not in ("", None):
        normalized_app_hash = _coerce_hex_32_noprefix(app_hash, label="tau_state app_hash")

    hasher = _blake3()
    hasher.update(rules.encode("utf-8"))
    hasher.update(bytes.fromhex(normalized_accounts_hash))
    if normalized_app_hash:
        hasher.update(bytes.fromhex(normalized_app_hash))
    return hasher.hexdigest()


class TauNetTcpClient:
    def __init__(self, config: TauNetTcpConfig = _DEFAULT_TAU_NET_TCP_CONFIG) -> None:
        if not isinstance(config.port, int) or not (0 <= config.port <= 65535):
            raise ValueError("invalid port")
        if not isinstance(config.timeout_s, (int, float)) or config.timeout_s <= 0:
            raise ValueError("timeout_s must be positive")
        if not isinstance(config.recv_max_bytes, int) or config.recv_max_bytes <= 0:
            raise ValueError("recv_max_bytes must be positive")
        self._cfg = config

    def rpc(self, cmd: str) -> str:
        if not isinstance(cmd, str) or not cmd.strip():
            raise ValueError("cmd must be a non-empty string")
        wire = cmd.strip().removesuffix("\r\n") + "\r\n"
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as sock:
            sock.settimeout(self._cfg.timeout_s)
            try:
                sock.connect((self._cfg.host, self._cfg.port))
                sock.sendall(wire.encode("utf-8"))
            except socket.timeout as exc:
                raise TauNetRpcError(
                    f"rpc timed out after {self._cfg.timeout_s}s connecting or sending request"
                ) from exc
            except OSError as exc:
                raise TauNetRpcError(f"rpc connection failed: {exc}") from exc
            buf = bytearray()
            remaining = self._cfg.recv_max_bytes
            while remaining > 0:
                try:
                    chunk = sock.recv(min(65536, remaining))
                except socket.timeout as exc:
                    raise TauNetRpcError(f"rpc timed out after {self._cfg.timeout_s}s waiting for response") from exc
                except OSError as exc:
                    raise TauNetRpcError(f"rpc connection failed while waiting for response: {exc}") from exc
                if not chunk:
                    break
                buf += chunk
                remaining -= len(chunk)
                if b"\n" in buf:
                    break

        # Tau Testnet's TCP server terminates each response with a newline.
        # Treat a close before that terminator as a truncated frame, since callers
        # may otherwise mistake partial `sendtx` bytes for an accepted transaction.
        if b"\n" in buf:
            line, _, _rest = bytes(buf).partition(b"\n")
            line = line.rstrip(b"\r")
            return line.decode("utf-8", errors="replace")
        if buf:
            raise TauNetRpcError("rpc connection closed before response terminator")
        raise TauNetRpcError("rpc connection closed without response")

    def get_sequence(self, sender_pubkey_hex: str) -> int:
        resp = self.rpc(f"getsequence {sender_pubkey_hex}").strip()
        if resp.startswith("SEQUENCE:"):
            _, v = resp.split(":", 1)
            return int(v.strip())
        raise TauNetRpcError(f"unexpected getsequence response: {resp!r}")

    def get_balance(self, address_hex: str) -> int:
        resp = self.rpc(f"getbalance {address_hex}").strip()
        if resp.startswith("BALANCE:"):
            _, v = resp.split(":", 1)
            return int(v.strip())
        raise TauNetRpcError(f"unexpected getbalance response: {resp!r}")

    def sendtx(self, payload: Mapping[str, Any]) -> str:
        blob = json.dumps(dict(payload), separators=(",", ":"), sort_keys=True)
        # Upstream tau-testnet expects `sendtx <json_payload>` with no shell quoting.
        return self.rpc(f"sendtx {blob}").strip()

    def createblock(self) -> str:
        return self.rpc("createblock").strip()

    def getappstate(self, *, full: bool = False) -> str:
        return self.rpc("getappstate full" if full else "getappstate").strip()

    def getdexstate(self, *, full: bool = False) -> str:
        # Back-compat alias; Tau Testnet now exposes `getappstate`.
        return self.getappstate(full=full)

    def getstateproof(self, *, full: bool = False) -> str:
        return self.rpc("getstateproof full" if full else "getstateproof").strip()

    def getappstate_view(self) -> TauNetAppStateView:
        payload = _coerce_mapping_json_response(self.getappstate(full=True), label="getappstate full")
        app_hash = payload.get("app_hash", "")
        if app_hash in ("", None):
            normalized_app_hash = ""
        else:
            normalized_app_hash = _coerce_hex_32_noprefix(app_hash, label="getappstate full app_hash")
        return TauNetAppStateView(
            app_hash=normalized_app_hash,
            app_state=payload.get("app_state"),
        )

    def getstateproof_view(self) -> TauNetStateProofView:
        payload = _coerce_mapping_json_response(self.getstateproof(full=True), label="getstateproof full")
        state_hash = payload.get("state_hash", "")
        present = payload.get("present")
        if not isinstance(present, bool):
            raise TauNetRpcError(f"getstateproof full present must be a bool, got {present!r}")
        if state_hash in ("", None):
            if present:
                raise TauNetRpcError("getstateproof full state_hash must be a 64-hex string when present=true")
            normalized_state_hash = ""
        else:
            normalized_state_hash = _coerce_hex_32_noprefix(state_hash, label="getstateproof full state_hash")
        proof_type = payload.get("proof_type")
        if proof_type is not None and (not isinstance(proof_type, str) or not proof_type.strip()):
            raise TauNetRpcError(f"getstateproof full proof_type must be a non-empty string when present, got {proof_type!r}")
        proof_bytes = payload.get("proof_bytes")
        if proof_bytes is not None:
            proof_bytes = _coerce_nonnegative_int(proof_bytes, label="getstateproof full proof_bytes")
        proof_sha256 = payload.get("proof_sha256")
        if proof_sha256 is not None:
            proof_sha256 = _coerce_hex_32_noprefix(proof_sha256, label="getstateproof full proof_sha256")
        error = payload.get("error")
        if error is not None and not isinstance(error, str):
            raise TauNetRpcError(f"getstateproof full error must be a string when present, got {error!r}")
        return TauNetStateProofView(
            state_hash=normalized_state_hash,
            present=present,
            proof_type=proof_type.strip() if isinstance(proof_type, str) else None,
            proof_bytes=proof_bytes,
            proof_sha256=proof_sha256,
            error=error,
        )

    def gettaustate(self, state_hash: str) -> str:
        normalized_state_hash = _coerce_hex_32_noprefix(state_hash, label="gettaustate state_hash")
        return self.rpc(f"gettaustate {normalized_state_hash}").strip()

    def gettaustate_view(self, state_hash: str) -> TauNetTauStateView:
        normalized_state_hash = _coerce_hex_32_noprefix(state_hash, label="gettaustate state_hash")
        payload = _coerce_mapping_json_response(
            self.gettaustate(normalized_state_hash),
            label=f"gettaustate {normalized_state_hash}",
        )
        returned_state_hash = payload.get("state_hash", "")
        if returned_state_hash in ("", None):
            normalized_returned_state_hash = ""
        else:
            normalized_returned_state_hash = _coerce_hex_32_noprefix(
                returned_state_hash,
                label=f"gettaustate {normalized_state_hash} returned state_hash",
            )
            if normalized_returned_state_hash != normalized_state_hash:
                raise TauNetRpcError(
                    f"gettaustate {normalized_state_hash} returned state_hash does not match requested state_hash"
                )
        present = payload.get("present")
        if present is not None and not isinstance(present, bool):
            raise TauNetRpcError(
                f"gettaustate {normalized_state_hash} present must be a bool when provided, got {present!r}"
            )
        error = payload.get("error")
        if error is not None and not isinstance(error, str):
            raise TauNetRpcError(
                f"gettaustate {normalized_state_hash} error must be a string when provided, got {error!r}"
            )
        if present is False:
            raise TauNetRpcError(
                f"gettaustate {normalized_state_hash} reported no committed tau_state payload"
                + (f": {error}" if error else "")
            )
        if isinstance(error, str) and error.strip():
            raise TauNetRpcError(f"gettaustate {normalized_state_hash} returned an error: {error.strip()}")
        rules = payload.get("rules")
        if not isinstance(rules, str):
            raise TauNetRpcError(f"gettaustate {normalized_state_hash} rules must be a string, got {rules!r}")
        accounts_hash = _coerce_hex_32_noprefix(
            payload.get("accounts_hash", ""),
            label=f"gettaustate {normalized_state_hash} accounts_hash",
        )
        raw_app_hash = payload.get("app_hash", "")
        if raw_app_hash in ("", None):
            normalized_app_hash = ""
        else:
            normalized_app_hash = _coerce_hex_32_noprefix(
                raw_app_hash,
                label=f"gettaustate {normalized_state_hash} app_hash",
            )
        computed_state_hash = compute_tau_state_commitment_hash_hex(
            rules=rules,
            accounts_hash=accounts_hash,
            app_hash=normalized_app_hash,
        )
        if computed_state_hash != normalized_state_hash:
            raise TauNetRpcError(f"gettaustate {normalized_state_hash} payload does not hash to requested state_hash")
        return TauNetTauStateView(
            state_hash=normalized_returned_state_hash or normalized_state_hash,
            rules=rules,
            accounts_hash=accounts_hash,
            app_hash=normalized_app_hash,
        )

    def send_signed_tx(
        self,
        *,
        privkey: str | int | bytes | bytearray,
        operations: Dict[str, Any],
        fee_limit: str | int = "0",
        expiration_seconds: int = 3600,
        sequence_number: Optional[int] = None,
    ) -> str:
        freshness_window_s = _coerce_positive_int(expiration_seconds, label="expiration_seconds")
        sender = bls_pubkey_hex_from_privkey(privkey)
        seq = (
            _coerce_nonnegative_int(sequence_number, label="sequence_number")
            if sequence_number is not None
            else self.get_sequence(sender)
        )
        expiry = int(time.time()) + freshness_window_s
        payload = build_signed_tau_transaction(
            privkey=privkey,
            sequence_number=seq,
            expiration_time=expiry,
            operations=operations,
            fee_limit=fee_limit,
        )
        return self.sendtx(payload)
