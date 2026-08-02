"""Typed authenticated-genesis relation for the unmounted FCIS M6 lane.

F05 binds the initial state, configuration, authority profile, history schema,
proof-context policy, and migration policy into one genesis value. A separate
deployment-pinned pin must match every governed field before the relation is
accepted. Neither value construction nor relation acceptance mounts runtime
authority; a production verifier must own the pin and revalidate the relation
at the command boundary.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Final, TypeAlias, cast

from ..state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex

FCIS_M6_F05_AUTHENTICATED_GENESIS_SCHEMA_V1: Final[str] = (
    "zenodex/fcis/m6/f05/authenticated-genesis/v1"
)
FCIS_M6_F05_GENESIS_PIN_SCHEMA_V1: Final[str] = "zenodex/fcis/m6/f05/genesis-pin/v1"
FCIS_M6_F05_MAX_TEXT_BYTES_V1: Final[int] = 256
FCIS_M6_F05_MAX_U64_V1: Final[int] = (1 << 64) - 1

_ROOT_HEX: Final[frozenset[str]] = frozenset("0123456789abcdef")


class F05GenesisCodeV1(Enum):
    """Stable typed outcomes for the F05 genesis relation."""

    WRONG_EXACT_TYPE = "wrong_exact_type"
    INVALID_TEXT = "invalid_text"
    INVALID_ROOT = "invalid_root"
    INVALID_EPOCH = "invalid_epoch"
    GENESIS_ROOT_MISMATCH = "genesis_root_mismatch"
    PIN_ROOT_MISMATCH = "pin_root_mismatch"
    CHAIN_MISMATCH = "chain_mismatch"
    DEPLOYMENT_MISMATCH = "deployment_mismatch"
    STATE_MISMATCH = "state_mismatch"
    CONFIGURATION_MISMATCH = "configuration_mismatch"
    AUTHORITY_PROFILE_MISMATCH = "authority_profile_mismatch"
    HISTORY_SCHEMA_MISMATCH = "history_schema_mismatch"
    PROOF_POLICY_MISMATCH = "proof_policy_mismatch"
    MIGRATION_POLICY_MISMATCH = "migration_policy_mismatch"
    GENESIS_PIN_MISMATCH = "genesis_pin_mismatch"


class F05GenesisError(ValueError):
    """Raised when an F05 value is outside its closed schema."""


def _text(value: object, name: str) -> str:
    if type(value) is not str or not value:
        raise F05GenesisError(f"{name} must be nonempty exact text")
    try:
        encoded = value.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise F05GenesisError(f"{name} must be valid UTF-8") from exc
    if len(encoded) > FCIS_M6_F05_MAX_TEXT_BYTES_V1:
        raise F05GenesisError(f"{name} exceeds its byte bound")
    if any(ord(character) < 0x20 or ord(character) == 0x7F for character in value):
        raise F05GenesisError(f"{name} contains a control character")
    return value


def _root(value: object, name: str) -> str:
    if (
        type(value) is not str
        or len(value) != 66
        or not value.startswith("0x")
        or value != value.lower()
        or any(character not in _ROOT_HEX for character in value[2:])
    ):
        raise F05GenesisError(f"{name} must be a lowercase 32-byte root")
    return value


def _u64(value: object, name: str) -> int:
    if type(value) is not int or value < 0 or value > FCIS_M6_F05_MAX_U64_V1:
        raise F05GenesisError(f"{name} is outside its closed u64 domain")
    return value


def _genesis_root_payload(value: "F05GenesisV1") -> dict[str, object]:
    return {
        "schema": FCIS_M6_F05_AUTHENTICATED_GENESIS_SCHEMA_V1,
        "chain_id": value.chain_id,
        "deployment_id": value.deployment_id,
        "initial_state_root": value.initial_state_root,
        "initial_configuration_root": value.initial_configuration_root,
        "initial_authority_profile_id": value.initial_authority_profile_id,
        "initial_authority_profile_root": value.initial_authority_profile_root,
        "history_schema": value.history_schema,
        "proof_context_policy_id": value.proof_context_policy_id,
        "proof_context_policy_root": value.proof_context_policy_root,
        "migration_policy_id": value.migration_policy_id,
        "migration_policy_root": value.migration_policy_root,
    }


def _derive_genesis_root_payload(payload: dict[str, object]) -> str:
    return cast(
        str,
        sha256_hex(
            domain_sep_bytes("zenodex/fcis/m6/f05/authenticated-genesis", version=1)
            + canonical_json_bytes(payload)
        ),
    )


@dataclass(frozen=True, slots=True)
class F05GenesisV1:
    """Immutable genesis value; construction grants no authority."""

    chain_id: str
    deployment_id: str
    initial_state_root: str
    initial_configuration_root: str
    initial_authority_profile_id: str
    initial_authority_profile_root: str
    history_schema: str
    proof_context_policy_id: str
    proof_context_policy_root: str
    migration_policy_id: str
    migration_policy_root: str
    genesis_root: str

    def __post_init__(self) -> None:
        for name in (
            "chain_id",
            "deployment_id",
            "initial_authority_profile_id",
            "history_schema",
            "proof_context_policy_id",
            "migration_policy_id",
        ):
            _text(object.__getattribute__(self, name), name)
        for name in (
            "initial_state_root",
            "initial_configuration_root",
            "initial_authority_profile_root",
            "proof_context_policy_root",
            "migration_policy_root",
            "genesis_root",
        ):
            _root(object.__getattribute__(self, name), name)
        expected = _derive_genesis_root_payload(_genesis_root_payload(self))
        if self.genesis_root != expected:
            raise F05GenesisError("genesis_root does not rederive")

    @property
    def recomputed_root(self) -> str:
        return _derive_genesis_root_payload(_genesis_root_payload(self))

    def to_wire(self) -> dict[str, object]:
        self.__post_init__()
        return {
            "schema": FCIS_M6_F05_AUTHENTICATED_GENESIS_SCHEMA_V1,
            "value": {
                **_genesis_root_payload(self),
                "genesis_root": self.genesis_root,
            },
        }


def build_f05_genesis_v1(
    *,
    chain_id: str,
    deployment_id: str,
    initial_state_root: str,
    initial_configuration_root: str,
    initial_authority_profile_id: str,
    initial_authority_profile_root: str,
    history_schema: str,
    proof_context_policy_id: str,
    proof_context_policy_root: str,
    migration_policy_id: str,
    migration_policy_root: str,
) -> F05GenesisV1:
    """Build one genesis value with a root derived from all governed fields."""

    payload: dict[str, object] = {
        "schema": FCIS_M6_F05_AUTHENTICATED_GENESIS_SCHEMA_V1,
        "chain_id": chain_id,
        "deployment_id": deployment_id,
        "initial_state_root": initial_state_root,
        "initial_configuration_root": initial_configuration_root,
        "initial_authority_profile_id": initial_authority_profile_id,
        "initial_authority_profile_root": initial_authority_profile_root,
        "history_schema": history_schema,
        "proof_context_policy_id": proof_context_policy_id,
        "proof_context_policy_root": proof_context_policy_root,
        "migration_policy_id": migration_policy_id,
        "migration_policy_root": migration_policy_root,
    }
    genesis_root = _derive_genesis_root_payload(payload)
    return F05GenesisV1(
        chain_id=chain_id,
        deployment_id=deployment_id,
        initial_state_root=initial_state_root,
        initial_configuration_root=initial_configuration_root,
        initial_authority_profile_id=initial_authority_profile_id,
        initial_authority_profile_root=initial_authority_profile_root,
        history_schema=history_schema,
        proof_context_policy_id=proof_context_policy_id,
        proof_context_policy_root=proof_context_policy_root,
        migration_policy_id=migration_policy_id,
        migration_policy_root=migration_policy_root,
        genesis_root=genesis_root,
    )


def _pin_root_payload(value: "F05GenesisPinV1") -> dict[str, object]:
    return {
        "schema": FCIS_M6_F05_GENESIS_PIN_SCHEMA_V1,
        "chain_id": value.chain_id,
        "deployment_id": value.deployment_id,
        "expected_genesis_root": value.expected_genesis_root,
        "expected_initial_state_root": value.expected_initial_state_root,
        "expected_configuration_root": value.expected_configuration_root,
        "expected_authority_profile_id": value.expected_authority_profile_id,
        "expected_authority_profile_root": value.expected_authority_profile_root,
        "expected_history_schema": value.expected_history_schema,
        "expected_proof_context_policy_id": value.expected_proof_context_policy_id,
        "expected_proof_context_policy_root": value.expected_proof_context_policy_root,
        "expected_migration_policy_id": value.expected_migration_policy_id,
        "expected_migration_policy_root": value.expected_migration_policy_root,
        "activation_epoch": value.activation_epoch,
    }


def _derive_pin_root_payload(payload: dict[str, object]) -> str:
    return cast(
        str,
        sha256_hex(
            domain_sep_bytes("zenodex/fcis/m6/f05/genesis-pin", version=1)
            + canonical_json_bytes(payload)
        ),
    )


@dataclass(frozen=True, slots=True)
class F05GenesisPinV1:
    """Deployment configuration value that pins one expected genesis."""

    chain_id: str
    deployment_id: str
    expected_genesis_root: str
    expected_initial_state_root: str
    expected_configuration_root: str
    expected_authority_profile_id: str
    expected_authority_profile_root: str
    expected_history_schema: str
    expected_proof_context_policy_id: str
    expected_proof_context_policy_root: str
    expected_migration_policy_id: str
    expected_migration_policy_root: str
    activation_epoch: int
    pin_root: str

    def __post_init__(self) -> None:
        for name in (
            "chain_id",
            "deployment_id",
            "expected_authority_profile_id",
            "expected_history_schema",
            "expected_proof_context_policy_id",
            "expected_migration_policy_id",
        ):
            _text(object.__getattribute__(self, name), name)
        for name in (
            "expected_genesis_root",
            "expected_initial_state_root",
            "expected_configuration_root",
            "expected_authority_profile_root",
            "expected_proof_context_policy_root",
            "expected_migration_policy_root",
            "pin_root",
        ):
            _root(object.__getattribute__(self, name), name)
        _u64(self.activation_epoch, "activation_epoch")
        expected = _derive_pin_root_payload(_pin_root_payload(self))
        if self.pin_root != expected:
            raise F05GenesisError("pin_root does not rederive")

    @property
    def recomputed_root(self) -> str:
        return _derive_pin_root_payload(_pin_root_payload(self))

    def to_wire(self) -> dict[str, object]:
        self.__post_init__()
        return {
            "schema": FCIS_M6_F05_GENESIS_PIN_SCHEMA_V1,
            "value": {
                **_pin_root_payload(self),
                "pin_root": self.pin_root,
            },
        }


def build_f05_genesis_pin_v1(
    *,
    chain_id: str,
    deployment_id: str,
    expected_genesis_root: str,
    expected_initial_state_root: str,
    expected_configuration_root: str,
    expected_authority_profile_id: str,
    expected_authority_profile_root: str,
    expected_history_schema: str,
    expected_proof_context_policy_id: str,
    expected_proof_context_policy_root: str,
    expected_migration_policy_id: str,
    expected_migration_policy_root: str,
    activation_epoch: int,
) -> F05GenesisPinV1:
    """Build one deployment pin with a root derived from all pin fields."""

    payload = {
        "schema": FCIS_M6_F05_GENESIS_PIN_SCHEMA_V1,
        "chain_id": chain_id,
        "deployment_id": deployment_id,
        "expected_genesis_root": expected_genesis_root,
        "expected_initial_state_root": expected_initial_state_root,
        "expected_configuration_root": expected_configuration_root,
        "expected_authority_profile_id": expected_authority_profile_id,
        "expected_authority_profile_root": expected_authority_profile_root,
        "expected_history_schema": expected_history_schema,
        "expected_proof_context_policy_id": expected_proof_context_policy_id,
        "expected_proof_context_policy_root": expected_proof_context_policy_root,
        "expected_migration_policy_id": expected_migration_policy_id,
        "expected_migration_policy_root": expected_migration_policy_root,
        "activation_epoch": activation_epoch,
    }
    pin_root = _derive_pin_root_payload(payload)
    return F05GenesisPinV1(
        chain_id=chain_id,
        deployment_id=deployment_id,
        expected_genesis_root=expected_genesis_root,
        expected_initial_state_root=expected_initial_state_root,
        expected_configuration_root=expected_configuration_root,
        expected_authority_profile_id=expected_authority_profile_id,
        expected_authority_profile_root=expected_authority_profile_root,
        expected_history_schema=expected_history_schema,
        expected_proof_context_policy_id=expected_proof_context_policy_id,
        expected_proof_context_policy_root=expected_proof_context_policy_root,
        expected_migration_policy_id=expected_migration_policy_id,
        expected_migration_policy_root=expected_migration_policy_root,
        activation_epoch=activation_epoch,
        pin_root=pin_root,
    )


@dataclass(frozen=True, slots=True)
class F05GenesisAcceptanceV1:
    """Checked genesis/pin relation; this value grants no runtime authority."""

    genesis: F05GenesisV1
    pin: F05GenesisPinV1
    admission_root: str

    def __post_init__(self) -> None:
        checked_genesis = validate_f05_genesis_value(self.genesis)
        checked_pin = validate_f05_genesis_pin_value(self.pin)
        if type(checked_genesis) is not F05GenesisV1:
            raise F05GenesisError("acceptance contains an invalid genesis")
        if type(checked_pin) is not F05GenesisPinV1:
            raise F05GenesisError("acceptance contains an invalid pin")
        _root(self.admission_root, "admission_root")
        if not _genesis_matches_pin(self.genesis, self.pin):
            raise F05GenesisError("genesis does not match the deployment pin")
        expected = _derive_admission_root(self.genesis, self.pin)
        if self.admission_root != expected:
            raise F05GenesisError("admission_root does not rederive")


@dataclass(frozen=True, slots=True)
class F05GenesisRejectV1:
    code: F05GenesisCodeV1
    path: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.code) is not F05GenesisCodeV1:
            raise F05GenesisError("F05 rejection code has the wrong exact type")
        if type(self.path) is not tuple or any(type(part) is not str for part in self.path):
            raise F05GenesisError("F05 rejection path must be an exact string tuple")


F05GenesisResultV1: TypeAlias = F05GenesisAcceptanceV1 | F05GenesisRejectV1


def _derive_admission_root(genesis: F05GenesisV1, pin: F05GenesisPinV1) -> str:
    return _derive_root_payload(
        "zenodex/fcis/m6/f05/admission",
        {"genesis_root": genesis.genesis_root, "pin_root": pin.pin_root},
    )


def _derive_root_payload(domain: str, payload: dict[str, object]) -> str:
    return cast(
        str,
        sha256_hex(domain_sep_bytes(domain, version=1) + canonical_json_bytes(payload)),
    )


def validate_f05_genesis_value(value: object) -> F05GenesisV1 | F05GenesisRejectV1:
    """Revalidate an untrusted genesis value and return typed rejection."""

    if type(value) is not F05GenesisV1:
        return F05GenesisRejectV1(F05GenesisCodeV1.WRONG_EXACT_TYPE, ("genesis",))
    try:
        value.__post_init__()
    except (F05GenesisError, AttributeError, TypeError, ValueError, ArithmeticError) as exc:
        message = str(exc)
        if "root" in message:
            code = F05GenesisCodeV1.GENESIS_ROOT_MISMATCH
        elif "text" in message or "string" in message:
            code = F05GenesisCodeV1.INVALID_TEXT
        else:
            code = F05GenesisCodeV1.INVALID_ROOT
        return F05GenesisRejectV1(code, ("genesis",))
    return value


def validate_f05_genesis_pin_value(value: object) -> F05GenesisPinV1 | F05GenesisRejectV1:
    """Revalidate an untrusted deployment pin and return typed rejection."""

    if type(value) is not F05GenesisPinV1:
        return F05GenesisRejectV1(F05GenesisCodeV1.WRONG_EXACT_TYPE, ("pin",))
    try:
        value.__post_init__()
    except (F05GenesisError, AttributeError, TypeError, ValueError, ArithmeticError) as exc:
        message = str(exc)
        if "pin_root" in message:
            code = F05GenesisCodeV1.PIN_ROOT_MISMATCH
        elif "epoch" in message:
            code = F05GenesisCodeV1.INVALID_EPOCH
        elif "text" in message or "string" in message:
            code = F05GenesisCodeV1.INVALID_TEXT
        else:
            code = F05GenesisCodeV1.INVALID_ROOT
        return F05GenesisRejectV1(code, ("pin",))
    return value


def _genesis_matches_pin(genesis: F05GenesisV1, pin: F05GenesisPinV1) -> bool:
    return (
        genesis.chain_id == pin.chain_id
        and genesis.deployment_id == pin.deployment_id
        and genesis.genesis_root == pin.expected_genesis_root
        and genesis.initial_state_root == pin.expected_initial_state_root
        and genesis.initial_configuration_root == pin.expected_configuration_root
        and genesis.initial_authority_profile_id == pin.expected_authority_profile_id
        and genesis.initial_authority_profile_root == pin.expected_authority_profile_root
        and genesis.history_schema == pin.expected_history_schema
        and genesis.proof_context_policy_id == pin.expected_proof_context_policy_id
        and genesis.proof_context_policy_root == pin.expected_proof_context_policy_root
        and genesis.migration_policy_id == pin.expected_migration_policy_id
        and genesis.migration_policy_root == pin.expected_migration_policy_root
    )


def authenticate_f05_genesis_v1(
    genesis: object, pin: object
) -> F05GenesisAcceptanceV1 | F05GenesisRejectV1:
    """Check a genesis value against the exact deployment-pinned relation."""

    checked_genesis = validate_f05_genesis_value(genesis)
    if type(checked_genesis) is F05GenesisRejectV1:
        return checked_genesis
    checked_pin = validate_f05_genesis_pin_value(pin)
    if type(checked_pin) is F05GenesisRejectV1:
        return checked_pin
    genesis_value = cast(F05GenesisV1, checked_genesis)
    pin_value = cast(F05GenesisPinV1, checked_pin)
    if genesis_value.chain_id != pin_value.chain_id:
        return F05GenesisRejectV1(F05GenesisCodeV1.CHAIN_MISMATCH, ("chain_id",))
    if genesis_value.deployment_id != pin_value.deployment_id:
        return F05GenesisRejectV1(F05GenesisCodeV1.DEPLOYMENT_MISMATCH, ("deployment_id",))
    if genesis_value.initial_state_root != pin_value.expected_initial_state_root:
        return F05GenesisRejectV1(F05GenesisCodeV1.STATE_MISMATCH, ("initial_state_root",))
    if genesis_value.initial_configuration_root != pin_value.expected_configuration_root:
        return F05GenesisRejectV1(
            F05GenesisCodeV1.CONFIGURATION_MISMATCH, ("initial_configuration_root",)
        )
    if genesis_value.initial_authority_profile_id != pin_value.expected_authority_profile_id:
        return F05GenesisRejectV1(
            F05GenesisCodeV1.AUTHORITY_PROFILE_MISMATCH,
            ("initial_authority_profile_id",),
        )
    if genesis_value.initial_authority_profile_root != pin_value.expected_authority_profile_root:
        return F05GenesisRejectV1(
            F05GenesisCodeV1.AUTHORITY_PROFILE_MISMATCH,
            ("initial_authority_profile_root",),
        )
    if genesis_value.history_schema != pin_value.expected_history_schema:
        return F05GenesisRejectV1(F05GenesisCodeV1.HISTORY_SCHEMA_MISMATCH, ("history_schema",))
    if (
        genesis_value.proof_context_policy_id != pin_value.expected_proof_context_policy_id
        or genesis_value.proof_context_policy_root != pin_value.expected_proof_context_policy_root
    ):
        return F05GenesisRejectV1(
            F05GenesisCodeV1.PROOF_POLICY_MISMATCH,
            ("proof_context_policy",),
        )
    if (
        genesis_value.migration_policy_id != pin_value.expected_migration_policy_id
        or genesis_value.migration_policy_root != pin_value.expected_migration_policy_root
    ):
        return F05GenesisRejectV1(
            F05GenesisCodeV1.MIGRATION_POLICY_MISMATCH,
            ("migration_policy",),
        )
    if genesis_value.genesis_root != pin_value.expected_genesis_root:
        return F05GenesisRejectV1(F05GenesisCodeV1.GENESIS_PIN_MISMATCH, ("genesis_root",))
    return F05GenesisAcceptanceV1(
        genesis=genesis_value,
        pin=pin_value,
        admission_root=_derive_admission_root(genesis_value, pin_value),
    )


__all__ = (
    "FCIS_M6_F05_AUTHENTICATED_GENESIS_SCHEMA_V1",
    "FCIS_M6_F05_GENESIS_PIN_SCHEMA_V1",
    "F05GenesisAcceptanceV1",
    "F05GenesisCodeV1",
    "F05GenesisError",
    "F05GenesisPinV1",
    "F05GenesisRejectV1",
    "F05GenesisResultV1",
    "F05GenesisV1",
    "authenticate_f05_genesis_v1",
    "build_f05_genesis_pin_v1",
    "build_f05_genesis_v1",
    "validate_f05_genesis_pin_value",
    "validate_f05_genesis_value",
)
