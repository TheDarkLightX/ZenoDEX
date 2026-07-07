"""Local self-custody key management helpers for ZenoLedger/ZenoDEX.

This module is intentionally local-only. It has no network client, no custody
server integration, and no persisted private-key representation. Persisted state
is limited to public key references and policy metadata.
"""

from __future__ import annotations

import hashlib
import re
from dataclasses import dataclass, field
from typing import Any, Mapping, Sequence

from src.integration.zeno_ledger_signature import SIGNED_ARTIFACT_ALGORITHM_BLS12_381_G2_BASIC_V0
from src.integration.zeno_ledger_v0 import canonical_json_bytes_v0, hash_v0
from src.state.canonical import canonical_hex_fixed_allow_0x, hex_to_bytes_fixed

try:
    from py_ecc.bls import G2Basic
    from py_ecc.optimized_bls12_381 import curve_order as _BLS12_381_CURVE_ORDER

    _BLS_AVAILABLE = True
except Exception:  # pragma: no cover - optional dependency
    G2Basic = None
    _BLS12_381_CURVE_ORDER = None
    _BLS_AVAILABLE = False


KEY_MANAGER_SCHEMA_V0 = "zenodex/zeno_key_manager/v0"
KEY_REF_SCHEMA_V0 = "zenodex/zeno_key_manager/key_ref/v0"
SOCIAL_RECOVERY_POLICY_SCHEMA_V0 = "zenodex/zeno_key_manager/social_recovery_policy/v0"
RECOVERY_EVALUATION_SCHEMA_V0 = "zenodex/zeno_key_manager/recovery_evaluation/v0"
TAU_NET_KEY_IMPORT_EVIDENCE_SCHEMA_V0 = "zenodex/zeno_key_manager/tau_net_key_import_evidence/v0"
TAU_TESTNET_COMPATIBLE_KEYGEN_METHOD_V0 = "tau-testnet-console-wallet-py-ecc-g2basic-keygen-v0"
IMPORTED_EXISTING_KEY_KEYGEN_METHOD_V0 = "imported-existing-tau-testnet-key-v0"

KEY_STATUS_ACTIVE = "active"
KEY_STATUS_REVOKED = "revoked"
KEY_STATUS_ROTATED = "rotated"
SUPPORTED_KEY_STATUSES = frozenset({KEY_STATUS_ACTIVE, KEY_STATUS_REVOKED, KEY_STATUS_ROTATED})

KEY_ORIGIN_LOCAL_MEMORY = "local_memory"
KEY_ORIGIN_TAU_NET_IMPORT = "tau_net_import"
SUPPORTED_KEY_ORIGINS = frozenset({KEY_ORIGIN_LOCAL_MEMORY, KEY_ORIGIN_TAU_NET_IMPORT})

KEY_ENVIRONMENT_LOCAL_PROCESS = "local_process"
KEY_ENVIRONMENT_PHONE_SECURE_HARDWARE = "phone_secure_hardware"
KEY_ENVIRONMENT_TEE_ATTESTED = "tee_attested"
SUPPORTED_KEY_ENVIRONMENTS = frozenset(
    {
        KEY_ENVIRONMENT_LOCAL_PROCESS,
        KEY_ENVIRONMENT_PHONE_SECURE_HARDWARE,
        KEY_ENVIRONMENT_TEE_ATTESTED,
    }
)

SECRET_FIELD_NAMES = frozenset(
    {
        "access_token",
        "accesstoken",
        "api_key",
        "apikey",
        "auth_token",
        "authtoken",
        "bearer_token",
        "bearertoken",
        "mnemonic",
        "private_key",
        "private_key_hex",
        "privatekey",
        "privatekeyhex",
        "privkey",
        "privkey_hex",
        "privkeyhex",
        "secret",
        "secret_hex",
        "secretkey",
        "secret_key",
        "secretkeyhex",
        "secret_key_hex",
        "seed",
        "seed_phrase",
        "seedphrase",
    }
)
SECRET_FIELD_NORMALIZED_NAMES = frozenset(
    "".join(ch for ch in name.lower() if ch.isalnum()) for name in SECRET_FIELD_NAMES
)
SECRET_FIELD_NORMALIZED_PUBLIC_POSTURE_NAMES = frozenset(
    {
        "nolivesecrets",
        "norawprivatekeyexposure",
        "rawprivatekeyimported",
        "secretscan",
        "secretscanfindingcount",
        "secretscanok",
    }
)
SECRET_FIELD_TOKEN_NAMES = frozenset({"mnemonic", "secret", "seed"})
SECRET_FIELD_TOKEN_PAIRS = frozenset(
    {
        ("access", "token"),
        ("api", "key"),
        ("auth", "token"),
        ("bearer", "token"),
        ("private", "key"),
        ("priv", "key"),
        ("secret", "key"),
        ("seed", "phrase"),
    }
)
_CAMEL_CASE_BOUNDARY_RE = re.compile(r"(?<=[a-z0-9])(?=[A-Z])")
_FIELD_TOKEN_SPLIT_RE = re.compile(r"[^A-Za-z0-9]+")


def _field_name_tokens(key: object) -> tuple[str, ...]:
    text = _CAMEL_CASE_BOUNDARY_RE.sub("_", str(key).strip())
    return tuple(token.lower() for token in _FIELD_TOKEN_SPLIT_RE.split(text) if token)


def is_secret_field_name(key: object) -> bool:
    raw_text = str(key).strip()
    text = raw_text.lower()
    if text in SECRET_FIELD_NAMES:
        return True
    normalized = "".join(ch for ch in text if ch.isalnum())
    if not normalized:
        return False
    if normalized in SECRET_FIELD_NORMALIZED_PUBLIC_POSTURE_NAMES:
        return False
    if normalized in SECRET_FIELD_NORMALIZED_NAMES:
        return True
    tokens = _field_name_tokens(raw_text)
    if any(token in SECRET_FIELD_TOKEN_NAMES for token in tokens):
        return True
    return any(pair in zip(tokens, tokens[1:]) for pair in SECRET_FIELD_TOKEN_PAIRS)


def _require_str(value: object, *, name: str) -> str:
    if not isinstance(value, str) or value == "":
        raise ValueError(f"{name} must be a non-empty string")
    return value


def _require_positive_int(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value <= 0:
        raise ValueError(f"{name} must be a positive int")
    return int(value)


def _require_nonnegative_int(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise ValueError(f"{name} must be a non-negative int")
    return int(value)


def _require_string_sequence(value: object, *, name: str, allow_empty: bool = False) -> tuple[str, ...]:
    if not isinstance(value, Sequence) or isinstance(value, (str, bytes, bytearray)):
        raise TypeError(f"{name} must be a sequence of strings")
    out: list[str] = []
    for index, item in enumerate(value):
        out.append(_require_str(item, name=f"{name}[{index}]"))
    if not allow_empty and not out:
        raise ValueError(f"{name} must not be empty")
    return tuple(out)


def _require_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be a JSON object")
    return value


def _reject_secret_fields(value: object, *, name: str = "metadata") -> None:
    if isinstance(value, Mapping):
        for key, item in value.items():
            if str(key).lower() in SECRET_FIELD_NAMES:
                raise ValueError(f"{name} must not contain private key material")
            _reject_secret_fields(item, name=f"{name}.{key}")
        return
    if isinstance(value, Sequence) and not isinstance(value, (str, bytes, bytearray)):
        for index, item in enumerate(value):
            _reject_secret_fields(item, name=f"{name}[{index}]")


def _require_bls() -> None:
    if not _BLS_AVAILABLE:
        raise RuntimeError("py_ecc.bls is required for local BLS signing")


def _require_g2basic() -> Any:
    _require_bls()
    if G2Basic is None:
        raise RuntimeError("py_ecc.bls G2Basic is required for local BLS signing")
    return G2Basic


def _parse_private_key_hex(private_key_hex: str) -> int:
    canonical = canonical_hex_fixed_allow_0x(private_key_hex, nbytes=32, name="private_key_hex")
    if private_key_hex != canonical:
        raise ValueError("private_key_hex must be canonical lowercase 0x-prefixed hex")
    raw = hex_to_bytes_fixed(canonical, nbytes=32, name="private_key_hex")
    sk = int.from_bytes(raw, byteorder="big", signed=False)
    if sk <= 0:
        raise ValueError("private_key_hex must be positive")
    if _BLS12_381_CURVE_ORDER is not None and sk >= int(_BLS12_381_CURVE_ORDER):
        raise ValueError("private_key_hex out of range")
    return sk


def validate_tau_bls_public_key(public_key: str, *, name: str = "public_key") -> str:
    """Return a canonical ZenoLedger-facing BLS public key for Tau-like metadata."""

    canonical = canonical_hex_fixed_allow_0x(public_key, nbytes=48, name=name)
    if canonical == "0x" + ("00" * 48):
        raise ValueError(f"{name} must not be the all-zero public key")
    return canonical


def _validate_root_hash(value: str, *, name: str) -> str:
    return canonical_hex_fixed_allow_0x(value, nbytes=32, name=name)


def _signature_message_digest(payload: Mapping[str, Any]) -> bytes:
    return hashlib.sha256(
        canonical_json_bytes_v0(
            {
                "domain": "zenodex.zeno_key_manager.local_signing.v0",
                "payload": dict(payload),
            }
        )
    ).digest()


@dataclass(frozen=True)
class KeyRef:
    key_id: str
    public_key: str
    algorithm: str = SIGNED_ARTIFACT_ALGORITHM_BLS12_381_G2_BASIC_V0
    status: str = KEY_STATUS_ACTIVE
    origin: str = KEY_ORIGIN_LOCAL_MEMORY
    version: int = 1
    replaces_key_id: str | None = None
    recovery_policy_id: str | None = None
    metadata: Mapping[str, Any] = field(default_factory=dict)

    def __post_init__(self) -> None:
        _require_str(self.key_id, name="key_id")
        if self.algorithm != SIGNED_ARTIFACT_ALGORITHM_BLS12_381_G2_BASIC_V0:
            raise ValueError("algorithm is not supported")
        validate_tau_bls_public_key(self.public_key)
        if self.status not in SUPPORTED_KEY_STATUSES:
            raise ValueError("key status is not supported")
        if self.origin not in SUPPORTED_KEY_ORIGINS:
            raise ValueError("key origin is not supported")
        _require_positive_int(self.version, name="version")
        if self.replaces_key_id is not None:
            _require_str(self.replaces_key_id, name="replaces_key_id")
        if self.recovery_policy_id is not None:
            _require_str(self.recovery_policy_id, name="recovery_policy_id")
        _reject_secret_fields(_require_mapping(self.metadata, name="metadata"))

    def public_dict(self) -> dict[str, Any]:
        body: dict[str, Any] = {
            "schema": KEY_REF_SCHEMA_V0,
            "key_id": self.key_id,
            "algorithm": self.algorithm,
            "public_key": validate_tau_bls_public_key(self.public_key),
            "status": self.status,
            "origin": self.origin,
            "version": self.version,
            "metadata": dict(self.metadata),
        }
        if self.replaces_key_id is not None:
            body["replaces_key_id"] = self.replaces_key_id
        if self.recovery_policy_id is not None:
            body["recovery_policy_id"] = self.recovery_policy_id
        return {**body, "key_ref_hash": hash_v0("zeno_key_ref_v0", body)}

    @classmethod
    def from_public_dict(cls, payload: Mapping[str, Any]) -> "KeyRef":
        obj = _require_mapping(payload, name="key_ref")
        if obj.get("schema") != KEY_REF_SCHEMA_V0:
            raise ValueError("key_ref schema mismatch")
        allowed = {
            "schema",
            "key_id",
            "algorithm",
            "public_key",
            "status",
            "origin",
            "version",
            "replaces_key_id",
            "recovery_policy_id",
            "metadata",
            "key_ref_hash",
        }
        if set(obj.keys()) - allowed:
            raise ValueError("key_ref contains unsupported fields")
        ref = cls(
            key_id=_require_str(obj.get("key_id"), name="key_id"),
            algorithm=_require_str(obj.get("algorithm"), name="algorithm"),
            public_key=validate_tau_bls_public_key(_require_str(obj.get("public_key"), name="public_key")),
            status=_require_str(obj.get("status"), name="status"),
            origin=_require_str(obj.get("origin"), name="origin"),
            version=_require_positive_int(obj.get("version"), name="version"),
            replaces_key_id=obj.get("replaces_key_id") if obj.get("replaces_key_id") is not None else None,
            recovery_policy_id=obj.get("recovery_policy_id") if obj.get("recovery_policy_id") is not None else None,
            metadata=dict(_require_mapping(obj.get("metadata", {}), name="metadata")),
        )
        if dict(obj) != ref.public_dict():
            raise ValueError("key_ref binding mismatch")
        return ref


@dataclass(frozen=True)
class SignRequestContext:
    payload_kind: str
    chain_id: str
    purpose: str
    current_epoch: int

    def __post_init__(self) -> None:
        _require_str(self.payload_kind, name="payload_kind")
        _require_str(self.chain_id, name="chain_id")
        _require_str(self.purpose, name="purpose")
        _require_nonnegative_int(self.current_epoch, name="current_epoch")


@dataclass(frozen=True)
class KeyExecutionEnvironment:
    """Public evidence that a local device/TEE path already verified upstream."""

    environment_id: str
    environment_kind: str
    chain_id: str
    policy_hash: str
    challenge_hash: str
    issued_at_epoch: int
    expires_at_epoch: int
    attestation_hash: str | None = None
    tee_measurement_hash: str | None = None
    local_user_presence_confirmed: bool = False
    rollback_protection_confirmed: bool = False

    def __post_init__(self) -> None:
        _require_str(self.environment_id, name="environment_id")
        if self.environment_kind not in SUPPORTED_KEY_ENVIRONMENTS:
            raise ValueError("environment_kind is not supported")
        _require_str(self.chain_id, name="chain_id")
        _validate_root_hash(self.policy_hash, name="policy_hash")
        _validate_root_hash(self.challenge_hash, name="challenge_hash")
        _require_nonnegative_int(self.issued_at_epoch, name="issued_at_epoch")
        _require_nonnegative_int(self.expires_at_epoch, name="expires_at_epoch")
        if self.expires_at_epoch < self.issued_at_epoch:
            raise ValueError("expires_at_epoch must be >= issued_at_epoch")
        if self.attestation_hash is not None:
            _validate_root_hash(self.attestation_hash, name="attestation_hash")
        if self.tee_measurement_hash is not None:
            _validate_root_hash(self.tee_measurement_hash, name="tee_measurement_hash")
        if not isinstance(self.local_user_presence_confirmed, bool):
            raise TypeError("local_user_presence_confirmed must be bool")
        if not isinstance(self.rollback_protection_confirmed, bool):
            raise TypeError("rollback_protection_confirmed must be bool")

    def public_dict(self) -> dict[str, Any]:
        body: dict[str, Any] = {
            "environment_id": self.environment_id,
            "environment_kind": self.environment_kind,
            "chain_id": self.chain_id,
            "policy_hash": _validate_root_hash(self.policy_hash, name="policy_hash"),
            "challenge_hash": _validate_root_hash(self.challenge_hash, name="challenge_hash"),
            "issued_at_epoch": self.issued_at_epoch,
            "expires_at_epoch": self.expires_at_epoch,
            "local_user_presence_confirmed": self.local_user_presence_confirmed,
            "rollback_protection_confirmed": self.rollback_protection_confirmed,
        }
        if self.attestation_hash is not None:
            body["attestation_hash"] = _validate_root_hash(self.attestation_hash, name="attestation_hash")
        if self.tee_measurement_hash is not None:
            body["tee_measurement_hash"] = _validate_root_hash(self.tee_measurement_hash, name="tee_measurement_hash")
        return {**body, "environment_hash": hash_v0("zeno_key_execution_environment_v0", body)}


@dataclass(frozen=True)
class KeyEnvironmentPolicy:
    allowed_environment_kinds: tuple[str, ...] = (KEY_ENVIRONMENT_LOCAL_PROCESS,)
    expected_chain_id: str | None = None
    expected_policy_hash: str | None = None
    expected_challenge_hash: str | None = None
    require_attestation: bool = False
    require_tee_measurement: bool = False
    require_user_presence: bool = True
    require_rollback_protection: bool = True

    def __post_init__(self) -> None:
        kinds = _require_string_sequence(self.allowed_environment_kinds, name="allowed_environment_kinds")
        for kind in kinds:
            if kind not in SUPPORTED_KEY_ENVIRONMENTS:
                raise ValueError("allowed_environment_kinds contains unsupported environment")
        if self.expected_chain_id is not None:
            _require_str(self.expected_chain_id, name="expected_chain_id")
        if self.expected_policy_hash is not None:
            _validate_root_hash(self.expected_policy_hash, name="expected_policy_hash")
        if self.expected_challenge_hash is not None:
            _validate_root_hash(self.expected_challenge_hash, name="expected_challenge_hash")
        for name, value in (
            ("require_attestation", self.require_attestation),
            ("require_tee_measurement", self.require_tee_measurement),
            ("require_user_presence", self.require_user_presence),
            ("require_rollback_protection", self.require_rollback_protection),
        ):
            if not isinstance(value, bool):
                raise TypeError(f"{name} must be bool")

    def evaluate(self, *, environment: KeyExecutionEnvironment, current_epoch: int) -> "PolicyDecision":
        _require_nonnegative_int(current_epoch, name="current_epoch")
        errors: list[str] = []
        if environment.environment_kind not in self.allowed_environment_kinds:
            errors.append("environment_kind_not_allowed")
        if self.expected_chain_id is not None and environment.chain_id != self.expected_chain_id:
            errors.append("environment_chain_id_mismatch")
        if self.expected_policy_hash is not None and environment.policy_hash != self.expected_policy_hash:
            errors.append("environment_policy_hash_mismatch")
        if self.expected_challenge_hash is not None and environment.challenge_hash != self.expected_challenge_hash:
            errors.append("environment_challenge_hash_mismatch")
        if current_epoch < environment.issued_at_epoch:
            errors.append("environment_not_yet_valid")
        if current_epoch > environment.expires_at_epoch:
            errors.append("environment_expired")
        if self.require_attestation and environment.attestation_hash is None:
            errors.append("environment_attestation_missing")
        if self.require_tee_measurement and environment.tee_measurement_hash is None:
            errors.append("tee_measurement_missing")
        if self.require_user_presence and not environment.local_user_presence_confirmed:
            errors.append("local_user_presence_missing")
        if self.require_rollback_protection and not environment.rollback_protection_confirmed:
            errors.append("rollback_protection_missing")
        return PolicyDecision(ok=not errors, errors=tuple(errors))


@dataclass(frozen=True)
class KeyUsePolicy:
    allowed_payload_kinds: tuple[str, ...]
    allowed_chain_ids: tuple[str, ...]
    allowed_purposes: tuple[str, ...] = ("sign",)
    valid_from_epoch: int = 0
    valid_until_epoch: int | None = None
    allow_rotated_keys: bool = False

    def __post_init__(self) -> None:
        _require_string_sequence(self.allowed_payload_kinds, name="allowed_payload_kinds")
        _require_string_sequence(self.allowed_chain_ids, name="allowed_chain_ids")
        _require_string_sequence(self.allowed_purposes, name="allowed_purposes")
        _require_nonnegative_int(self.valid_from_epoch, name="valid_from_epoch")
        if self.valid_until_epoch is not None:
            _require_nonnegative_int(self.valid_until_epoch, name="valid_until_epoch")
            if self.valid_until_epoch < self.valid_from_epoch:
                raise ValueError("valid_until_epoch must be >= valid_from_epoch")

    def evaluate(self, *, key_ref: KeyRef, context: SignRequestContext) -> "PolicyDecision":
        errors: list[str] = []
        if key_ref.status == KEY_STATUS_REVOKED:
            errors.append("key_revoked")
        if key_ref.status == KEY_STATUS_ROTATED and not self.allow_rotated_keys:
            errors.append("key_rotated")
        if context.payload_kind not in self.allowed_payload_kinds:
            errors.append("payload_kind_not_allowed")
        if context.chain_id not in self.allowed_chain_ids:
            errors.append("chain_id_not_allowed")
        if context.purpose not in self.allowed_purposes:
            errors.append("purpose_not_allowed")
        if context.current_epoch < self.valid_from_epoch:
            errors.append("policy_window_not_open")
        if self.valid_until_epoch is not None and context.current_epoch > self.valid_until_epoch:
            errors.append("policy_expired")
        return PolicyDecision(ok=not errors, errors=tuple(errors))


@dataclass(frozen=True)
class PolicyDecision:
    ok: bool
    errors: tuple[str, ...] = ()

    def require_ok(self) -> None:
        if not self.ok:
            raise PermissionError("key policy rejected signing request: " + ",".join(self.errors))


@dataclass(frozen=True)
class TauNetKeyImportEvidence:
    """Host-checked facts for importing a Tau-like public key into local policy."""

    key_id: str
    tau_public_key: str
    tau_chain_id: str
    challenge_hash: str
    challenge_signature_hash: str
    policy_hash: str
    verified_at_epoch: int
    expires_at_epoch: int
    tau_account_id: str | None = None
    format_ok: bool = True
    pubkey_derives_ok: bool = True
    challenge_signature_ok: bool = True
    chain_binding_ok: bool = True
    policy_attached: bool = True

    def __post_init__(self) -> None:
        _require_str(self.key_id, name="key_id")
        validate_tau_bls_public_key(self.tau_public_key, name="tau_public_key")
        _require_str(self.tau_chain_id, name="tau_chain_id")
        _validate_root_hash(self.challenge_hash, name="challenge_hash")
        _validate_root_hash(self.challenge_signature_hash, name="challenge_signature_hash")
        _validate_root_hash(self.policy_hash, name="policy_hash")
        _require_nonnegative_int(self.verified_at_epoch, name="verified_at_epoch")
        _require_nonnegative_int(self.expires_at_epoch, name="expires_at_epoch")
        if self.expires_at_epoch < self.verified_at_epoch:
            raise ValueError("expires_at_epoch must be >= verified_at_epoch")
        if self.tau_account_id is not None:
            _require_str(self.tau_account_id, name="tau_account_id")
        for name, value in (
            ("format_ok", self.format_ok),
            ("pubkey_derives_ok", self.pubkey_derives_ok),
            ("challenge_signature_ok", self.challenge_signature_ok),
            ("chain_binding_ok", self.chain_binding_ok),
            ("policy_attached", self.policy_attached),
        ):
            if not isinstance(value, bool):
                raise TypeError(f"{name} must be bool")

    def evaluate(self, *, current_epoch: int) -> PolicyDecision:
        _require_nonnegative_int(current_epoch, name="current_epoch")
        errors: list[str] = []
        if not self.format_ok:
            errors.append("tau_import_format_not_verified")
        if not self.pubkey_derives_ok:
            errors.append("tau_import_pubkey_derivation_not_verified")
        if not self.challenge_signature_ok:
            errors.append("tau_import_challenge_signature_not_verified")
        if not self.chain_binding_ok:
            errors.append("tau_import_chain_binding_not_verified")
        if not self.policy_attached:
            errors.append("tau_import_policy_missing")
        if current_epoch < self.verified_at_epoch:
            errors.append("tau_import_evidence_not_yet_valid")
        if current_epoch > self.expires_at_epoch:
            errors.append("tau_import_evidence_expired")
        return PolicyDecision(ok=not errors, errors=tuple(errors))

    def public_dict(self) -> dict[str, Any]:
        body: dict[str, Any] = {
            "schema": TAU_NET_KEY_IMPORT_EVIDENCE_SCHEMA_V0,
            "key_id": self.key_id,
            "tau_public_key": validate_tau_bls_public_key(self.tau_public_key, name="tau_public_key"),
            "tau_chain_id": self.tau_chain_id,
            "challenge_hash": _validate_root_hash(self.challenge_hash, name="challenge_hash"),
            "challenge_signature_hash": _validate_root_hash(
                self.challenge_signature_hash,
                name="challenge_signature_hash",
            ),
            "policy_hash": _validate_root_hash(self.policy_hash, name="policy_hash"),
            "verified_at_epoch": self.verified_at_epoch,
            "expires_at_epoch": self.expires_at_epoch,
            "format_ok": self.format_ok,
            "pubkey_derives_ok": self.pubkey_derives_ok,
            "challenge_signature_ok": self.challenge_signature_ok,
            "chain_binding_ok": self.chain_binding_ok,
            "policy_attached": self.policy_attached,
        }
        if self.tau_account_id is not None:
            body["tau_account_id"] = self.tau_account_id
        return {**body, "evidence_hash": hash_v0("zeno_tau_net_key_import_evidence_v0", body)}


@dataclass(frozen=True)
class RecoveryGuardian:
    guardian_id: str
    public_key: str
    weight: int = 1
    status: str = KEY_STATUS_ACTIVE

    def __post_init__(self) -> None:
        _require_str(self.guardian_id, name="guardian_id")
        validate_tau_bls_public_key(self.public_key, name="guardian_public_key")
        _require_positive_int(self.weight, name="guardian_weight")
        if self.status not in {KEY_STATUS_ACTIVE, KEY_STATUS_REVOKED}:
            raise ValueError("guardian status must be active or revoked")

    def public_dict(self) -> dict[str, Any]:
        body = {
            "guardian_id": self.guardian_id,
            "public_key": validate_tau_bls_public_key(self.public_key, name="guardian_public_key"),
            "weight": self.weight,
            "status": self.status,
        }
        return {**body, "guardian_hash": hash_v0("zeno_recovery_guardian_v0", body)}


@dataclass(frozen=True)
class SocialRecoveryPolicy:
    policy_id: str
    subject_key_id: str
    threshold: int
    guardians: tuple[RecoveryGuardian, ...]
    delay_epochs: int = 0

    def __post_init__(self) -> None:
        _require_str(self.policy_id, name="policy_id")
        _require_str(self.subject_key_id, name="subject_key_id")
        _require_positive_int(self.threshold, name="threshold")
        _require_nonnegative_int(self.delay_epochs, name="delay_epochs")
        if not self.guardians:
            raise ValueError("recovery policy requires at least one guardian")
        seen: set[str] = set()
        active_weight = 0
        for guardian in self.guardians:
            if not isinstance(guardian, RecoveryGuardian):
                raise TypeError("guardians must be RecoveryGuardian values")
            if guardian.guardian_id in seen:
                raise ValueError("duplicate guardian_id")
            seen.add(guardian.guardian_id)
            if guardian.status == KEY_STATUS_ACTIVE:
                active_weight += guardian.weight
        if self.threshold > active_weight:
            raise ValueError("recovery threshold exceeds active guardian weight")

    def public_dict(self) -> dict[str, Any]:
        body = {
            "schema": SOCIAL_RECOVERY_POLICY_SCHEMA_V0,
            "policy_id": self.policy_id,
            "subject_key_id": self.subject_key_id,
            "threshold": self.threshold,
            "delay_epochs": self.delay_epochs,
            "guardians": [guardian.public_dict() for guardian in sorted(self.guardians, key=lambda item: item.guardian_id)],
        }
        return {**body, "policy_hash": hash_v0("zeno_social_recovery_policy_v0", body)}

    def evaluate(
        self,
        *,
        approvals: Sequence[str],
        requested_at_epoch: int,
        current_epoch: int,
    ) -> dict[str, Any]:
        _require_nonnegative_int(requested_at_epoch, name="requested_at_epoch")
        _require_nonnegative_int(current_epoch, name="current_epoch")
        approval_ids = _require_string_sequence(approvals, name="approvals", allow_empty=True)
        if len(set(approval_ids)) != len(approval_ids):
            raise ValueError("duplicate recovery approvals")
        active = {guardian.guardian_id: guardian for guardian in self.guardians if guardian.status == KEY_STATUS_ACTIVE}
        accepted: list[dict[str, Any]] = []
        accepted_weight = 0
        rejected: list[str] = []
        for guardian_id in approval_ids:
            guardian = active.get(guardian_id)
            if guardian is None:
                rejected.append(guardian_id)
                continue
            accepted_weight += guardian.weight
            accepted.append({"guardian_id": guardian.guardian_id, "weight": guardian.weight})
        delay_ok = current_epoch >= requested_at_epoch + self.delay_epochs
        threshold_ok = accepted_weight >= self.threshold
        body = {
            "schema": RECOVERY_EVALUATION_SCHEMA_V0,
            "policy_hash": self.public_dict()["policy_hash"],
            "subject_key_id": self.subject_key_id,
            "requested_at_epoch": requested_at_epoch,
            "current_epoch": current_epoch,
            "delay_ok": delay_ok,
            "threshold": self.threshold,
            "accepted_weight": accepted_weight,
            "threshold_ok": threshold_ok,
            "accepted_approvals": accepted,
            "rejected_approvals": rejected,
        }
        return {**body, "ok": bool(delay_ok and threshold_ok), "evaluation_hash": hash_v0("zeno_recovery_evaluation_v0", body)}


class LocalInMemoryBlsSigner:
    """Self-custody BLS signer. Private key material stays in process memory."""

    def __init__(self, *, key_ref: KeyRef, private_key_hex: str) -> None:
        g2basic = _require_g2basic()
        sk = _parse_private_key_hex(private_key_hex)
        public_key = "0x" + g2basic.SkToPk(sk).hex()
        if validate_tau_bls_public_key(key_ref.public_key) != public_key:
            raise ValueError("private_key_hex does not match key_ref.public_key")
        if key_ref.origin != KEY_ORIGIN_LOCAL_MEMORY:
            raise ValueError("local signer requires local_memory key origin")
        self.key_ref = key_ref
        self._sk = sk

    @classmethod
    def from_private_key_hex(
        cls,
        *,
        key_id: str,
        private_key_hex: str,
        metadata: Mapping[str, Any] | None = None,
        recovery_policy_id: str | None = None,
    ) -> "LocalInMemoryBlsSigner":
        g2basic = _require_g2basic()
        sk = _parse_private_key_hex(private_key_hex)
        ref = KeyRef(
            key_id=key_id,
            public_key="0x" + g2basic.SkToPk(sk).hex(),
            origin=KEY_ORIGIN_LOCAL_MEMORY,
            recovery_policy_id=recovery_policy_id,
            metadata=dict(metadata or {}),
        )
        return cls(key_ref=ref, private_key_hex=private_key_hex)

    def sign(self, payload: Mapping[str, Any], *, policy: KeyUsePolicy, context: SignRequestContext) -> dict[str, Any]:
        decision = policy.evaluate(key_ref=self.key_ref, context=context)
        decision.require_ok()
        _reject_secret_fields(payload, name="payload")
        g2basic = _require_g2basic()
        signature = "0x" + g2basic.Sign(self._sk, _signature_message_digest(payload)).hex()
        body = {
            "key_ref": self.key_ref.public_dict(),
            "payload_hash": hash_v0("zeno_key_manager_signing_payload_v0", dict(payload)),
            "context": {
                "payload_kind": context.payload_kind,
                "chain_id": context.chain_id,
                "purpose": context.purpose,
                "current_epoch": context.current_epoch,
            },
            "algorithm": self.key_ref.algorithm,
            "signature": signature,
        }
        return {**body, "signature_record_hash": hash_v0("zeno_key_manager_signature_record_v0", body)}


class ZenoKeyManager:
    def __init__(self, *, key_refs: Sequence[KeyRef] = (), recovery_policies: Sequence[SocialRecoveryPolicy] = ()) -> None:
        self._key_refs: dict[str, KeyRef] = {}
        self._recovery_policies: dict[str, SocialRecoveryPolicy] = {}
        for key_ref in key_refs:
            self.add_key_ref(key_ref)
        for policy in recovery_policies:
            self.add_recovery_policy(policy)

    def add_key_ref(self, key_ref: KeyRef) -> None:
        if key_ref.key_id in self._key_refs:
            raise ValueError("duplicate key_id")
        self._key_refs[key_ref.key_id] = key_ref

    def add_recovery_policy(self, policy: SocialRecoveryPolicy) -> None:
        if policy.policy_id in self._recovery_policies:
            raise ValueError("duplicate recovery policy_id")
        self._recovery_policies[policy.policy_id] = policy

    def key_ref(self, key_id: str) -> KeyRef:
        key = self._key_refs.get(_require_str(key_id, name="key_id"))
        if key is None:
            raise KeyError("unknown key_id")
        return key

    def revoke_key(self, key_id: str) -> KeyRef:
        old = self.key_ref(key_id)
        revoked = KeyRef(
            key_id=old.key_id,
            public_key=old.public_key,
            algorithm=old.algorithm,
            status=KEY_STATUS_REVOKED,
            origin=old.origin,
            version=old.version,
            replaces_key_id=old.replaces_key_id,
            recovery_policy_id=old.recovery_policy_id,
            metadata=old.metadata,
        )
        self._key_refs[key_id] = revoked
        return revoked

    def rotate_key(self, *, old_key_id: str, new_key_ref: KeyRef) -> tuple[KeyRef, KeyRef]:
        old = self.key_ref(old_key_id)
        if new_key_ref.replaces_key_id != old.key_id:
            raise ValueError("new key_ref must bind replaces_key_id to old key_id")
        rotated_old = KeyRef(
            key_id=old.key_id,
            public_key=old.public_key,
            algorithm=old.algorithm,
            status=KEY_STATUS_ROTATED,
            origin=old.origin,
            version=old.version,
            replaces_key_id=old.replaces_key_id,
            recovery_policy_id=old.recovery_policy_id,
            metadata=old.metadata,
        )
        self._key_refs[old.key_id] = rotated_old
        self.add_key_ref(new_key_ref)
        return rotated_old, new_key_ref

    def public_dict(self) -> dict[str, Any]:
        body = {
            "schema": KEY_MANAGER_SCHEMA_V0,
            "key_refs": [ref.public_dict() for ref in sorted(self._key_refs.values(), key=lambda item: item.key_id)],
            "recovery_policies": [
                policy.public_dict() for policy in sorted(self._recovery_policies.values(), key=lambda item: item.policy_id)
            ],
        }
        return {**body, "manager_hash": hash_v0("zeno_key_manager_v0", body)}


def import_tau_net_key_ref(
    *,
    key_id: str,
    tau_public_key: str,
    tau_account_id: str | None = None,
    metadata: Mapping[str, Any] | None = None,
) -> KeyRef:
    """Import public Tau Net key metadata without importing private key material."""

    merged_metadata: dict[str, Any] = dict(metadata or {})
    if tau_account_id is not None:
        merged_metadata["tau_account_id"] = _require_str(tau_account_id, name="tau_account_id")
    merged_metadata["import_mode"] = "public_key_only"
    return KeyRef(
        key_id=key_id,
        public_key=validate_tau_bls_public_key(tau_public_key, name="tau_public_key"),
        origin=KEY_ORIGIN_TAU_NET_IMPORT,
        metadata=merged_metadata,
    )


def import_tau_net_key_ref_with_evidence(
    *,
    evidence: TauNetKeyImportEvidence,
    current_epoch: int,
    metadata: Mapping[str, Any] | None = None,
) -> KeyRef:
    """Import Tau-like public key metadata after host-checked challenge evidence."""

    evidence.evaluate(current_epoch=current_epoch).require_ok()
    evidence_record = evidence.public_dict()
    merged_metadata: dict[str, Any] = dict(metadata or {})
    if evidence.tau_account_id is not None:
        merged_metadata["tau_account_id"] = evidence.tau_account_id
    merged_metadata.update(
        {
            "import_mode": "challenge_bound_public_key",
            "tau_chain_id": evidence.tau_chain_id,
            "challenge_hash": evidence_record["challenge_hash"],
            "policy_hash": evidence_record["policy_hash"],
            "tau_import_evidence_hash": evidence_record["evidence_hash"],
        }
    )
    return KeyRef(
        key_id=evidence.key_id,
        public_key=validate_tau_bls_public_key(evidence.tau_public_key, name="tau_public_key"),
        origin=KEY_ORIGIN_TAU_NET_IMPORT,
        metadata=merged_metadata,
    )
