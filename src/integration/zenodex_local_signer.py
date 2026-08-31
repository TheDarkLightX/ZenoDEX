"""Local encrypted signer for ZenoDEX self-custody keys.

This module is intentionally browser-independent. It owns key generation,
encrypted local vault storage, and signing receipts. Browser code may receive
public receipts and signatures, but raw private key material and passphrases stay
inside the local signer process.
"""

from __future__ import annotations

import base64
import hmac
import json
import os
import stat
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping, Sequence

from cryptography.exceptions import InvalidTag
from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from cryptography.hazmat.primitives.kdf.scrypt import Scrypt

from src.core.dex_intent_auth_message import build_dex_intent_signing_dict_v1
from src.integration.bls_intent_signing import sign_dex_intent_for_engine
from src.integration.dex_engine import _verify_intent_signature_bytes
from src.integration.zeno_key_manager import (
    IMPORTED_EXISTING_KEY_KEYGEN_METHOD_V0,
    TAU_TESTNET_COMPATIBLE_KEYGEN_METHOD_V0,
    LocalInMemoryBlsSigner,
    validate_tau_bls_public_key,
)
from src.integration.zeno_ledger_v0 import canonical_json_bytes_v0, hash_v0
from src.state.canonical import canonical_hex_fixed_allow_0x

LOCAL_SIGNER_VAULT_SCHEMA_V0 = "zenodex/local_signer/vault/v0"
LOCAL_SIGNER_PUBLIC_RECEIPT_SCHEMA_V0 = "zenodex/local_signer/public_receipt/v0"
LOCAL_SIGNER_DEX_SIGNATURE_RECEIPT_SCHEMA_V0 = "zenodex/local_signer/dex_signature_receipt/v0"
LOCAL_SIGNER_STORAGE_BACKEND_SCRYPT_AESGCM_V0 = "encrypted-local-vault-scrypt-aesgcm-v0"
LOCAL_SIGNER_PROVIDER_V0 = "zenodex-local-signer-v0"
RETIRED_TAU_TRANSACTION_SIGNING_ROUTE_ERROR = (
    "RETIRED_TAU_TRANSACTION_SIGNING_ROUTE"
)

DEFAULT_SCRYPT_N = 2**14
DEFAULT_SCRYPT_R = 8
DEFAULT_SCRYPT_P = 1
DEFAULT_SCRYPT_LENGTH = 32
MIN_PASSPHRASE_BYTES = 12
MAX_VAULT_BYTES = 64_000

_VAULT_PUBLIC_KEYS_V0 = frozenset(
    {
        "schema",
        "version",
        "provider",
        "key_id",
        "public_key",
        "algorithm",
        "chain_id",
        "allowed_chain_ids",
        "created_at_epoch",
        "keygen_method",
        "storage_backend",
        "browser_generated",
        "zenodex_custody",
        "encrypted_payload_hash",
    }
)
_VAULT_TOP_LEVEL_KEYS_V0 = _VAULT_PUBLIC_KEYS_V0 | frozenset({"encrypted_payload", "vault_hash"})
_ENCRYPTED_PAYLOAD_KEYS_V0 = frozenset({"kdf", "salt", "nonce", "ciphertext"})
_KDF_KEYS_V0 = frozenset({"name", "n", "r", "p", "length"})
_PUBLIC_RECEIPT_KEYS_V0 = frozenset(
    {
        "schema",
        "provider",
        "vault_hash",
        "vault",
        "approval_mode",
        "signer_user_approval_required",
        "browser_bridge_auth_required",
        "browser_generated",
        "zenodex_custody",
        "receipt_hash",
    }
)
_DEX_SIGNATURE_RECEIPT_KEYS_V0 = frozenset(
    {
        "schema",
        "provider",
        "vault_hash",
        "key_id",
        "public_key",
        "chain_id",
        "intent_signing_dict_hash",
        "intent_payload_hash",
        "signature",
        "browser_generated",
        "zenodex_custody",
        "receipt_hash",
    }
)
_PUBLIC_RECEIPT_APPROVAL_MODES_V0 = frozenset({"offline-cli", "prompt", "unattended"})


class LocalSignerError(RuntimeError):
    pass


class RetiredTauTransactionSigningRouteError(LocalSignerError):
    """Exact refusal for the historical Tau transaction signing surface."""


def _require_str(value: object, *, name: str) -> str:
    if not isinstance(value, str) or value == "":
        raise ValueError(f"{name} must be a non-empty string")
    return value


def _require_bool(value: object, *, name: str) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be bool")
    return value


def _require_nonnegative_int(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise ValueError(f"{name} must be a non-negative int")
    return int(value)


def _require_string_sequence(value: object, *, name: str) -> tuple[str, ...]:
    if not isinstance(value, Sequence) or isinstance(value, (str, bytes, bytearray)):
        raise TypeError(f"{name} must be a sequence of strings")
    out: list[str] = []
    for index, item in enumerate(value):
        out.append(_require_str(item, name=f"{name}[{index}]"))
    if not out:
        raise ValueError(f"{name} must not be empty")
    if len(set(out)) != len(out):
        raise ValueError(f"{name} must not contain duplicates")
    return tuple(out)


def _require_passphrase_bytes(passphrase: str | bytes | bytearray) -> bytes:
    if isinstance(passphrase, str):
        raw = passphrase.encode("utf-8")
    elif isinstance(passphrase, (bytes, bytearray)):
        raw = bytes(passphrase)
    else:
        raise TypeError("passphrase must be str or bytes")
    if len(raw) < MIN_PASSPHRASE_BYTES:
        raise ValueError(f"passphrase must be at least {MIN_PASSPHRASE_BYTES} bytes")
    return raw


def _b64(raw: bytes) -> str:
    return base64.b64encode(raw).decode("ascii")


def _unb64(value: object, *, name: str, nbytes: int | None = None) -> bytes:
    text = _require_str(value, name=name)
    try:
        raw = base64.b64decode(text.encode("ascii"), validate=True)
    except Exception as exc:
        raise ValueError(f"{name} must be base64") from exc
    if nbytes is not None and len(raw) != nbytes:
        raise ValueError(f"{name} must decode to {nbytes} bytes")
    return raw


def _derive_key(passphrase: bytes, *, salt: bytes, kdf: Mapping[str, Any]) -> bytes:
    if set(kdf.keys()) != _KDF_KEYS_V0:
        raise ValueError("unsupported vault kdf shape")
    if kdf.get("name") != "scrypt":
        raise ValueError("unsupported vault kdf")
    n = _require_nonnegative_int(kdf.get("n"), name="kdf.n")
    r = _require_nonnegative_int(kdf.get("r"), name="kdf.r")
    p = _require_nonnegative_int(kdf.get("p"), name="kdf.p")
    length = _require_nonnegative_int(kdf.get("length"), name="kdf.length")
    if n < 2**14 or n & (n - 1) != 0:
        raise ValueError("kdf.n must be a power of two and at least 2^14")
    if r <= 0 or p <= 0 or length != DEFAULT_SCRYPT_LENGTH:
        raise ValueError("invalid scrypt parameters")
    return Scrypt(salt=salt, length=length, n=n, r=r, p=p).derive(passphrase)


def _public_vault_body(vault: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "schema": vault["schema"],
        "version": vault["version"],
        "provider": vault["provider"],
        "key_id": vault["key_id"],
        "public_key": vault["public_key"],
        "algorithm": vault["algorithm"],
        "chain_id": vault["chain_id"],
        "allowed_chain_ids": list(vault["allowed_chain_ids"]),
        "created_at_epoch": vault["created_at_epoch"],
        "keygen_method": vault["keygen_method"],
        "storage_backend": vault["storage_backend"],
        "browser_generated": vault["browser_generated"],
        "zenodex_custody": vault["zenodex_custody"],
        "encrypted_payload_hash": vault["encrypted_payload_hash"],
    }


def _vault_aad_body(vault: Mapping[str, Any]) -> dict[str, Any]:
    return {
        key: value
        for key, value in _public_vault_body(vault).items()
        if key != "encrypted_payload_hash"
    }


def _validate_public_vault_fields(vault: Mapping[str, Any]) -> None:
    if vault.get("schema") != LOCAL_SIGNER_VAULT_SCHEMA_V0:
        raise ValueError("local signer vault schema mismatch")
    if vault.get("version") != 1:
        raise ValueError("local signer vault version mismatch")
    if vault.get("provider") != LOCAL_SIGNER_PROVIDER_V0:
        raise ValueError("local signer provider mismatch")
    _require_str(vault.get("key_id"), name="key_id")
    validate_tau_bls_public_key(_require_str(vault.get("public_key"), name="public_key"))
    if vault.get("algorithm") != "bls12-381-g2-basic-release-v0":
        raise ValueError("local signer algorithm mismatch")
    chain_id = _require_str(vault.get("chain_id"), name="chain_id")
    allowed = _require_string_sequence(vault.get("allowed_chain_ids"), name="allowed_chain_ids")
    if chain_id not in allowed:
        raise ValueError("chain_id must be allowed")
    _require_nonnegative_int(vault.get("created_at_epoch"), name="created_at_epoch")
    if vault.get("keygen_method") not in (
        TAU_TESTNET_COMPATIBLE_KEYGEN_METHOD_V0,
        IMPORTED_EXISTING_KEY_KEYGEN_METHOD_V0,
    ):
        raise ValueError("keygen method mismatch")
    if vault.get("storage_backend") != LOCAL_SIGNER_STORAGE_BACKEND_SCRYPT_AESGCM_V0:
        raise ValueError("storage backend mismatch")
    if _require_bool(vault.get("browser_generated"), name="browser_generated") is not False:
        raise ValueError("local signer vault must not be browser generated")
    if _require_bool(vault.get("zenodex_custody"), name="zenodex_custody") is not False:
        raise ValueError("local signer vault must not claim ZenoDEX custody")
    canonical_hex_fixed_allow_0x(
        _require_str(vault.get("encrypted_payload_hash"), name="encrypted_payload_hash"),
        nbytes=32,
        name="encrypted_payload_hash",
    )


def _validate_vault(vault: Mapping[str, Any]) -> None:
    if set(vault.keys()) != _VAULT_TOP_LEVEL_KEYS_V0:
        raise ValueError("local signer vault contains unsupported fields")
    _validate_public_vault_fields(vault)
    encrypted = vault.get("encrypted_payload")
    if not isinstance(encrypted, Mapping):
        raise ValueError("encrypted_payload must be a JSON object")
    if set(encrypted.keys()) != _ENCRYPTED_PAYLOAD_KEYS_V0:
        raise ValueError("encrypted_payload contains unsupported fields")
    _unb64(encrypted.get("salt"), name="encrypted_payload.salt", nbytes=16)
    _unb64(encrypted.get("nonce"), name="encrypted_payload.nonce", nbytes=12)
    _unb64(encrypted.get("ciphertext"), name="encrypted_payload.ciphertext")
    kdf = encrypted.get("kdf")
    if not isinstance(kdf, Mapping):
        raise ValueError("encrypted_payload.kdf must be a JSON object")
    expected_hash = hash_v0("local_signer_encrypted_payload_v0", encrypted)
    if not hmac.compare_digest(expected_hash, str(vault.get("encrypted_payload_hash"))):
        raise ValueError("encrypted payload hash mismatch")
    expected_vault_hash = hash_v0("local_signer_public_vault_v0", _public_vault_body(vault))
    if not hmac.compare_digest(expected_vault_hash, str(vault.get("vault_hash"))):
        raise ValueError("vault hash mismatch")


@dataclass(frozen=True)
class LocalSignerVault:
    payload: Mapping[str, Any]

    def __post_init__(self) -> None:
        _validate_vault(self.payload)

    @property
    def key_id(self) -> str:
        return str(self.payload["key_id"])

    @property
    def public_key(self) -> str:
        return str(self.payload["public_key"])

    @property
    def chain_id(self) -> str:
        return str(self.payload["chain_id"])

    @property
    def allowed_chain_ids(self) -> tuple[str, ...]:
        return tuple(str(item) for item in self.payload["allowed_chain_ids"])

    def public_receipt(
        self,
        *,
        approval_mode: str = "offline-cli",
        signer_user_approval_required: bool = False,
        browser_bridge_auth_required: bool = False,
    ) -> dict[str, Any]:
        mode = _require_str(approval_mode, name="approval_mode")
        if mode not in _PUBLIC_RECEIPT_APPROVAL_MODES_V0:
            raise ValueError("approval_mode unsupported")
        approval_required = _require_bool(
            signer_user_approval_required,
            name="signer_user_approval_required",
        )
        bridge_auth_required = _require_bool(
            browser_bridge_auth_required,
            name="browser_bridge_auth_required",
        )
        if approval_required and mode != "prompt":
            raise ValueError("signer user approval requires prompt approval mode")
        public_vault = _public_vault_body(self.payload)
        body = {
            "schema": LOCAL_SIGNER_PUBLIC_RECEIPT_SCHEMA_V0,
            "provider": LOCAL_SIGNER_PROVIDER_V0,
            "vault_hash": self.payload["vault_hash"],
            "vault": public_vault,
            "approval_mode": mode,
            "signer_user_approval_required": approval_required,
            "browser_bridge_auth_required": bridge_auth_required,
            "browser_generated": False,
            "zenodex_custody": False,
        }
        return {**body, "receipt_hash": hash_v0("local_signer_public_receipt_v0", body)}

    def _unlock_private_key_hex(self, passphrase: str | bytes | bytearray) -> str:
        encrypted = self.payload["encrypted_payload"]
        salt = _unb64(encrypted["salt"], name="encrypted_payload.salt", nbytes=16)
        nonce = _unb64(encrypted["nonce"], name="encrypted_payload.nonce", nbytes=12)
        ciphertext = _unb64(encrypted["ciphertext"], name="encrypted_payload.ciphertext")
        key = _derive_key(_require_passphrase_bytes(passphrase), salt=salt, kdf=encrypted["kdf"])
        aad = canonical_json_bytes_v0(_vault_aad_body(self.payload))
        try:
            plaintext = AESGCM(key).decrypt(nonce, ciphertext, aad)
        except InvalidTag as exc:
            raise LocalSignerError("vault unlock failed") from exc
        obj = json.loads(plaintext.decode("utf-8"))
        if not isinstance(obj, Mapping):
            raise LocalSignerError("vault plaintext is invalid")
        if obj.get("schema") != "zenodex/local_signer/private_payload/v0":
            raise LocalSignerError("vault private payload schema mismatch")
        if obj.get("key_id") != self.key_id:
            raise LocalSignerError("vault private payload key_id mismatch")
        if obj.get("public_key") != self.public_key:
            raise LocalSignerError("vault private payload public_key mismatch")
        private_key_hex = _require_str(obj.get("private_key_hex"), name="private_key_hex")
        signer = LocalInMemoryBlsSigner.from_private_key_hex(
            key_id=self.key_id,
            private_key_hex=private_key_hex,
            metadata={"source": "zenodex-local-signer-unlock-check"},
        )
        if signer.key_ref.public_key != self.public_key:
            raise LocalSignerError("vault public key binding mismatch")
        return private_key_hex

    def sign_dex_intent(
        self,
        *,
        passphrase: str | bytes | bytearray,
        intent: Mapping[str, Any],
        chain_id: str,
    ) -> dict[str, Any]:
        chain = _require_str(chain_id, name="chain_id")
        if chain not in self.allowed_chain_ids:
            raise PermissionError("chain_id_not_allowed")
        if not isinstance(intent, Mapping):
            raise TypeError("intent must be a JSON object")
        if intent.get("sender_pubkey") != self.public_key:
            raise PermissionError("intent_sender_pubkey_mismatch")
        signing_dict = build_dex_intent_signing_dict_v1(intent)
        signing_payload = canonical_json_bytes_v0(signing_dict)
        private_key_hex = self._unlock_private_key_hex(passphrase)
        signature = sign_dex_intent_for_engine(intent, privkey=private_key_hex, chain_id=chain)
        ok, err = _verify_intent_signature_bytes(
            sender_pubkey_hex=self.public_key,
            signature_hex=signature,
            signing_payload_bytes=signing_payload,
            chain_id=chain,
        )
        if not ok:
            raise LocalSignerError(f"self-verification failed: {err}")
        body = {
            "schema": LOCAL_SIGNER_DEX_SIGNATURE_RECEIPT_SCHEMA_V0,
            "provider": LOCAL_SIGNER_PROVIDER_V0,
            "vault_hash": self.payload["vault_hash"],
            "key_id": self.key_id,
            "public_key": self.public_key,
            "chain_id": chain,
            "intent_signing_dict_hash": hash_v0("local_signer_dex_intent_signing_dict_v0", signing_dict),
            "intent_payload_hash": hash_v0("local_signer_dex_intent_payload_v0", signing_payload),
            "signature": signature,
            "browser_generated": False,
            "zenodex_custody": False,
        }
        return {**body, "receipt_hash": hash_v0("local_signer_dex_signature_receipt_v0", body)}

    def sign_tau_transaction_payload(
        self,
        *,
        passphrase: str | bytes | bytearray,
        payload: Mapping[str, Any],
        chain_id: str,
    ) -> dict[str, Any]:
        raise RetiredTauTransactionSigningRouteError(
            RETIRED_TAU_TRANSACTION_SIGNING_ROUTE_ERROR
        )

    def require_valid_passphrase(
        self,
        passphrase: str | bytes | bytearray,
    ) -> None:
        """Unlock once without constructing a historical Tau transaction."""

        self._unlock_private_key_hex(passphrase)


def create_local_signer_vault(
    *,
    key_id: str,
    passphrase: str | bytes | bytearray,
    chain_id: str,
    allowed_chain_ids: Sequence[str] | None = None,
    label: str | None = None,
    created_at_epoch: int | None = None,
    private_key_hex: str | None = None,
) -> LocalSignerVault:
    passphrase_bytes = _require_passphrase_bytes(passphrase)
    key = _require_str(key_id, name="key_id")
    chain = _require_str(chain_id, name="chain_id")
    allowed = (
        (chain,)
        if allowed_chain_ids is None
        else _require_string_sequence(allowed_chain_ids, name="allowed_chain_ids")
    )
    if chain not in allowed:
        raise ValueError("chain_id must be present in allowed_chain_ids")
    created = (
        int(time.time())
        if created_at_epoch is None
        else _require_nonnegative_int(created_at_epoch, name="created_at_epoch")
    )
    if private_key_hex is not None:
        signer = LocalInMemoryBlsSigner.from_private_key_hex(
            key_id=key,
            private_key_hex=private_key_hex,
            metadata={"label": label} if label else None,
        )
        keygen_method = IMPORTED_EXISTING_KEY_KEYGEN_METHOD_V0
    else:
        signer, private_key_hex = LocalInMemoryBlsSigner.generate_tau_testnet_compatible(
            key_id=key,
            metadata={"label": label} if label else None,
        )
        keygen_method = TAU_TESTNET_COMPATIBLE_KEYGEN_METHOD_V0
    public_body = {
        "schema": LOCAL_SIGNER_VAULT_SCHEMA_V0,
        "version": 1,
        "provider": LOCAL_SIGNER_PROVIDER_V0,
        "key_id": key,
        "public_key": signer.key_ref.public_key,
        "algorithm": signer.key_ref.algorithm,
        "chain_id": chain,
        "allowed_chain_ids": list(allowed),
        "created_at_epoch": created,
        "keygen_method": keygen_method,
        "storage_backend": LOCAL_SIGNER_STORAGE_BACKEND_SCRYPT_AESGCM_V0,
        "browser_generated": False,
        "zenodex_custody": False,
    }
    plaintext = canonical_json_bytes_v0(
        {
            "schema": "zenodex/local_signer/private_payload/v0",
            "key_id": key,
            "public_key": signer.key_ref.public_key,
            "private_key_hex": private_key_hex,
        }
    )
    salt = os.urandom(16)
    nonce = os.urandom(12)
    kdf = {
        "name": "scrypt",
        "n": DEFAULT_SCRYPT_N,
        "r": DEFAULT_SCRYPT_R,
        "p": DEFAULT_SCRYPT_P,
        "length": DEFAULT_SCRYPT_LENGTH,
    }
    derived = _derive_key(passphrase_bytes, salt=salt, kdf=kdf)
    aad = canonical_json_bytes_v0(public_body)
    encrypted_payload = {
        "kdf": kdf,
        "salt": _b64(salt),
        "nonce": _b64(nonce),
        "ciphertext": _b64(AESGCM(derived).encrypt(nonce, plaintext, aad)),
    }
    vault = {
        **public_body,
        "encrypted_payload_hash": hash_v0("local_signer_encrypted_payload_v0", encrypted_payload),
        "encrypted_payload": encrypted_payload,
    }
    vault["vault_hash"] = hash_v0("local_signer_public_vault_v0", _public_vault_body(vault))
    return LocalSignerVault(vault)


def verify_local_signer_public_receipt(receipt: object) -> tuple[bool, str | None]:
    if not isinstance(receipt, Mapping):
        return False, "receipt must be a JSON object"
    if set(receipt.keys()) != _PUBLIC_RECEIPT_KEYS_V0:
        return False, "receipt contains unsupported fields"
    body = dict(receipt)
    receipt_hash = body.pop("receipt_hash", None)
    expected_hash = hash_v0("local_signer_public_receipt_v0", body)
    if not isinstance(receipt_hash, str) or not hmac.compare_digest(expected_hash, receipt_hash):
        return False, "receipt_hash mismatch"
    if body.get("schema") != LOCAL_SIGNER_PUBLIC_RECEIPT_SCHEMA_V0:
        return False, "receipt schema mismatch"
    if body.get("provider") != LOCAL_SIGNER_PROVIDER_V0:
        return False, "receipt provider mismatch"
    mode = body.get("approval_mode")
    if not isinstance(mode, str) or mode not in _PUBLIC_RECEIPT_APPROVAL_MODES_V0:
        return False, "receipt approval_mode mismatch"
    approval_required = body.get("signer_user_approval_required")
    if not isinstance(approval_required, bool):
        return False, "receipt signer_user_approval_required must be bool"
    bridge_auth_required = body.get("browser_bridge_auth_required")
    if not isinstance(bridge_auth_required, bool):
        return False, "receipt browser_bridge_auth_required must be bool"
    if approval_required and mode != "prompt":
        return False, "receipt approval posture mismatch"
    if body.get("browser_generated") is not False or body.get("zenodex_custody") is not False:
        return False, "receipt custody posture mismatch"
    vault_body = body.get("vault")
    if not isinstance(vault_body, Mapping):
        return False, "receipt vault must be a JSON object"
    try:
        _validate_public_vault_fields(vault_body)
        expected_vault_hash = hash_v0("local_signer_public_vault_v0", _public_vault_body(vault_body))
    except Exception as exc:
        return False, f"receipt vault invalid: {exc}"
    if not isinstance(body.get("vault_hash"), str) or not hmac.compare_digest(expected_vault_hash, body["vault_hash"]):
        return False, "receipt vault_hash mismatch"
    return True, None


def verify_local_signer_dex_signature_receipt(
    receipt: object,
    *,
    intent: Mapping[str, Any],
) -> tuple[bool, str | None]:
    if not isinstance(receipt, Mapping):
        return False, "receipt must be a JSON object"
    if set(receipt.keys()) != _DEX_SIGNATURE_RECEIPT_KEYS_V0:
        return False, "receipt contains unsupported fields"
    body = dict(receipt)
    receipt_hash = body.pop("receipt_hash", None)
    expected_hash = hash_v0("local_signer_dex_signature_receipt_v0", body)
    if not isinstance(receipt_hash, str) or not hmac.compare_digest(expected_hash, receipt_hash):
        return False, "receipt_hash mismatch"
    if body.get("schema") != LOCAL_SIGNER_DEX_SIGNATURE_RECEIPT_SCHEMA_V0:
        return False, "receipt schema mismatch"
    if body.get("provider") != LOCAL_SIGNER_PROVIDER_V0:
        return False, "receipt provider mismatch"
    if body.get("browser_generated") is not False or body.get("zenodex_custody") is not False:
        return False, "receipt custody posture mismatch"
    try:
        _require_str(body.get("key_id"), name="key_id")
        canonical_hex_fixed_allow_0x(
            _require_str(body.get("vault_hash"), name="vault_hash"),
            nbytes=32,
            name="vault_hash",
        )
        public_key = _require_str(body.get("public_key"), name="public_key")
        validate_tau_bls_public_key(public_key)
        if intent.get("sender_pubkey") != public_key:
            return False, "intent sender mismatch"
        chain_id = _require_str(body.get("chain_id"), name="chain_id")
        signature = _require_str(body.get("signature"), name="signature")
        signing_dict = build_dex_intent_signing_dict_v1(intent)
        signing_payload = canonical_json_bytes_v0(signing_dict)
        if body.get("intent_signing_dict_hash") != hash_v0("local_signer_dex_intent_signing_dict_v0", signing_dict):
            return False, "intent_signing_dict_hash mismatch"
        if body.get("intent_payload_hash") != hash_v0("local_signer_dex_intent_payload_v0", signing_payload):
            return False, "intent_payload_hash mismatch"
        ok, err = _verify_intent_signature_bytes(
            sender_pubkey_hex=public_key,
            signature_hex=signature,
            signing_payload_bytes=signing_payload,
            chain_id=chain_id,
        )
        if not ok:
            return False, err or "invalid intent signature"
    except Exception as exc:
        return False, f"receipt invalid: {exc}"
    return True, None


def load_local_signer_vault(payload: Mapping[str, Any]) -> LocalSignerVault:
    return LocalSignerVault(payload)


def read_local_signer_vault(path: Path | str) -> LocalSignerVault:
    p = Path(path)
    fd = os.open(p, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0))
    try:
        info = os.fstat(fd)
        if not stat.S_ISREG(info.st_mode):
            raise ValueError("vault path must be a regular file")
        if info.st_size > MAX_VAULT_BYTES:
            raise ValueError("vault file exceeds max size")
        with os.fdopen(fd, "rb") as handle:
            fd = -1
            data = handle.read(MAX_VAULT_BYTES + 1)
    finally:
        if fd != -1:
            os.close(fd)
    if len(data) > MAX_VAULT_BYTES:
        raise ValueError("vault file exceeds max size")
    return load_local_signer_vault(json.loads(data.decode("utf-8")))


def write_local_signer_vault(path: Path | str, vault: LocalSignerVault, *, overwrite: bool = False) -> None:
    p = Path(path)
    flags = os.O_WRONLY | os.O_CREAT | getattr(os, "O_NOFOLLOW", 0)
    flags |= os.O_TRUNC if overwrite else os.O_EXCL
    data = canonical_json_bytes_v0(vault.payload) + b"\n"
    fd = os.open(p, flags, 0o600)
    with os.fdopen(fd, "wb") as handle:
        handle.write(data)
        handle.flush()
        os.fsync(handle.fileno())
    p.chmod(stat.S_IRUSR | stat.S_IWUSR)
