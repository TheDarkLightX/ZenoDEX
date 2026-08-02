"""Typed FCIS M6 proof-context values for the unmounted research lane.

G01 defines an immutable context value and its self-derived identity.  The
value is evidence supplied to a later verifier boundary; constructing one does
not create a verified proof witness or select a production verifier.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Final, TypeAlias, cast

from ..state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex
from .fcis_m6_profile_ids import PROOF_CONTEXT_VERSION_V1

FCIS_M6_G01_PROOF_CONTEXT_SCHEMA_V1: Final[str] = PROOF_CONTEXT_VERSION_V1
FCIS_M6_G01_MAX_TEXT_BYTES_V1: Final[int] = 256
FCIS_M6_G01_MAX_EPOCH_V1: Final[int] = (1 << 64) - 1


class G01ProofContextCodeV1(Enum):
    """Stable typed outcomes for G01 context validation."""

    WRONG_EXACT_TYPE = "wrong_exact_type"
    INVALID_TEXT = "invalid_text"
    INVALID_ROOT = "invalid_root"
    INVALID_EPOCH = "invalid_epoch"
    INVALID_EXPIRY = "invalid_expiry"
    CONTEXT_ROOT_MISMATCH = "context_root_mismatch"
    NOT_ACTIVE = "not_active"


class G01ProofContextError(ValueError):
    """Raised when a context value violates its closed typed contract."""


@dataclass(frozen=True, slots=True)
class G01ProofContextRejectV1:
    """Typed rejection returned at the untrusted proof-context boundary."""

    code: G01ProofContextCodeV1
    path: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.code) is not G01ProofContextCodeV1:
            raise G01ProofContextError("proof-context code has the wrong exact type")
        if type(self.path) is not tuple or any(type(part) is not str for part in self.path):
            raise G01ProofContextError("proof-context path must be an exact string tuple")


def _text(value: object, name: str) -> str:
    if type(value) is not str or not value:
        raise G01ProofContextError(f"{name} must be nonempty exact text")
    try:
        encoded = value.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise G01ProofContextError(f"{name} must be valid UTF-8") from exc
    if len(encoded) > FCIS_M6_G01_MAX_TEXT_BYTES_V1:
        raise G01ProofContextError(f"{name} exceeds its byte bound")
    if any(ord(character) < 0x20 or ord(character) == 0x7F for character in value):
        raise G01ProofContextError(f"{name} contains a control character")
    return value


def _root(value: object, name: str) -> str:
    if (
        type(value) is not str
        or len(value) != 66
        or not value.startswith("0x")
        or value != value.lower()
        or any(character not in "0123456789abcdef" for character in value[2:])
    ):
        raise G01ProofContextError(f"{name} must be a lowercase 32-byte root")
    return value


def _epoch(value: object, name: str) -> int:
    if type(value) is not int or value < 0 or value > FCIS_M6_G01_MAX_EPOCH_V1:
        raise G01ProofContextError(f"{name} is outside the closed u64 domain")
    return value


def _root_payload(context: "G01ProofContextV1") -> dict[str, object]:
    return {
        "schema": FCIS_M6_G01_PROOF_CONTEXT_SCHEMA_V1,
        "chain_id": context.chain_id,
        "deployment_id": context.deployment_id,
        "state_root": context.state_root,
        "configuration_root": context.configuration_root,
        "protocol_version": context.protocol_version,
        "language_runtime_version": context.language_runtime_version,
        "verifier_implementation_id": context.verifier_implementation_id,
        "verification_key_digest": context.verification_key_digest,
        "statement_schema_id": context.statement_schema_id,
        "algorithm_profile_id": context.algorithm_profile_id,
        "history_genesis_authority_root": context.history_genesis_authority_root,
        "authority_epoch": context.authority_epoch,
        "not_before_epoch": context.not_before_epoch,
        "expires_at_epoch": context.expires_at_epoch,
    }


def derive_g01_proof_context_root_v1(context: "G01ProofContextV1") -> str:
    """Derive the context identity from every governed field."""

    return _derive_root_payload(_root_payload(context))


def _derive_root_payload(payload: dict[str, object]) -> str:
    return cast(
        str,
        sha256_hex(
            domain_sep_bytes("zenodex/fcis/m6/g01/proof-context", version=1)
            + canonical_json_bytes(payload)
        ),
    )


@dataclass(frozen=True, slots=True)
class G01ProofContextV1:
    """Immutable proof-context value; construction grants no authority."""

    chain_id: str
    deployment_id: str
    state_root: str
    configuration_root: str
    protocol_version: str
    language_runtime_version: str
    verifier_implementation_id: str
    verification_key_digest: str
    statement_schema_id: str
    algorithm_profile_id: str
    history_genesis_authority_root: str
    authority_epoch: int
    not_before_epoch: int
    expires_at_epoch: int | None
    context_root: str

    def __post_init__(self) -> None:
        for name in (
            "chain_id",
            "deployment_id",
            "protocol_version",
            "language_runtime_version",
            "verifier_implementation_id",
            "statement_schema_id",
            "algorithm_profile_id",
        ):
            _text(object.__getattribute__(self, name), name)
        for name in (
            "state_root",
            "configuration_root",
            "verification_key_digest",
            "history_genesis_authority_root",
            "context_root",
        ):
            _root(object.__getattribute__(self, name), name)
        _epoch(self.authority_epoch, "authority_epoch")
        _epoch(self.not_before_epoch, "not_before_epoch")
        if self.expires_at_epoch is not None:
            _epoch(self.expires_at_epoch, "expires_at_epoch")
            if self.expires_at_epoch < self.not_before_epoch:
                raise G01ProofContextError("expires_at_epoch precedes not_before_epoch")
        if self.context_root != self.recomputed_root:
            raise G01ProofContextError("context_root does not rederive")

    @property
    def recomputed_root(self) -> str:
        return derive_g01_proof_context_root_v1(self)

    def is_active_at(self, epoch: object) -> bool:
        """Return whether this context is active at one exact epoch."""

        try:
            checked = _epoch(epoch, "check_epoch")
        except G01ProofContextError:
            return False
        return checked >= self.not_before_epoch and (
            self.expires_at_epoch is None or checked <= self.expires_at_epoch
        )

    def to_wire(self) -> dict[str, object]:
        """Return the closed value projection used by the later G02 codec."""

        self.__post_init__()
        value = _root_payload(self)
        value["context_root"] = self.context_root
        return {"schema": FCIS_M6_G01_PROOF_CONTEXT_SCHEMA_V1, "value": value}


G01ProofContextResultV1: TypeAlias = G01ProofContextV1 | G01ProofContextRejectV1


def build_g01_proof_context_v1(
    *,
    chain_id: str,
    deployment_id: str,
    state_root: str,
    configuration_root: str,
    protocol_version: str,
    language_runtime_version: str,
    verifier_implementation_id: str,
    verification_key_digest: str,
    statement_schema_id: str,
    algorithm_profile_id: str,
    history_genesis_authority_root: str,
    authority_epoch: int,
    not_before_epoch: int,
    expires_at_epoch: int | None,
) -> G01ProofContextV1:
    """Build one value while deriving its root from the exact input fields."""

    payload = {
        "schema": FCIS_M6_G01_PROOF_CONTEXT_SCHEMA_V1,
        "chain_id": chain_id,
        "deployment_id": deployment_id,
        "state_root": state_root,
        "configuration_root": configuration_root,
        "protocol_version": protocol_version,
        "language_runtime_version": language_runtime_version,
        "verifier_implementation_id": verifier_implementation_id,
        "verification_key_digest": verification_key_digest,
        "statement_schema_id": statement_schema_id,
        "algorithm_profile_id": algorithm_profile_id,
        "history_genesis_authority_root": history_genesis_authority_root,
        "authority_epoch": authority_epoch,
        "not_before_epoch": not_before_epoch,
        "expires_at_epoch": expires_at_epoch,
    }
    return G01ProofContextV1(
        chain_id=chain_id,
        deployment_id=deployment_id,
        state_root=state_root,
        configuration_root=configuration_root,
        protocol_version=protocol_version,
        language_runtime_version=language_runtime_version,
        verifier_implementation_id=verifier_implementation_id,
        verification_key_digest=verification_key_digest,
        statement_schema_id=statement_schema_id,
        algorithm_profile_id=algorithm_profile_id,
        history_genesis_authority_root=history_genesis_authority_root,
        authority_epoch=authority_epoch,
        not_before_epoch=not_before_epoch,
        expires_at_epoch=expires_at_epoch,
        context_root=_derive_root_payload(payload),
    )


def _reject(code: G01ProofContextCodeV1, *path: str) -> G01ProofContextRejectV1:
    return G01ProofContextRejectV1(code=code, path=path)


def validate_g01_proof_context_v1(
    value: object, *, at_epoch: object | None = None
) -> G01ProofContextResultV1:
    """Revalidate an untrusted context value and optionally apply epoch rules."""

    if type(value) is not G01ProofContextV1:
        return _reject(G01ProofContextCodeV1.WRONG_EXACT_TYPE, "context")
    context = value
    try:
        context.__post_init__()
    except (G01ProofContextError, AttributeError, TypeError, ValueError, ArithmeticError) as exc:
        message = str(exc)
        if "root" in message or "digest" in message:
            code = (
                G01ProofContextCodeV1.CONTEXT_ROOT_MISMATCH
                if "does not rederive" in message
                else G01ProofContextCodeV1.INVALID_ROOT
            )
        elif "epoch" in message or "expiry" in message:
            code = G01ProofContextCodeV1.INVALID_EXPIRY
        else:
            code = G01ProofContextCodeV1.INVALID_TEXT
        return _reject(code, "context")
    if at_epoch is not None:
        try:
            _epoch(at_epoch, "check_epoch")
        except G01ProofContextError:
            return _reject(G01ProofContextCodeV1.INVALID_EPOCH, "check_epoch")
        if not context.is_active_at(at_epoch):
            return _reject(G01ProofContextCodeV1.NOT_ACTIVE, "check_epoch")
    return context


__all__ = (
    "FCIS_M6_G01_MAX_EPOCH_V1",
    "FCIS_M6_G01_MAX_TEXT_BYTES_V1",
    "FCIS_M6_G01_PROOF_CONTEXT_SCHEMA_V1",
    "G01ProofContextCodeV1",
    "G01ProofContextError",
    "G01ProofContextRejectV1",
    "G01ProofContextResultV1",
    "G01ProofContextV1",
    "build_g01_proof_context_v1",
    "derive_g01_proof_context_root_v1",
    "validate_g01_proof_context_v1",
)
