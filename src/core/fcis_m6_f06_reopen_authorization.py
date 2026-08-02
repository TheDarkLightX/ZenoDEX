"""Fresh reopen-head authorization for the unmounted FCIS M6 lane.

F06 consumes the F03 canonical reopen result and an F05 genesis value. It
binds the exact durable head, current state, authority state/epoch, deployment
configuration, genesis root, and an external authorization root into one
token. The external verifier is called when the token is issued and again at
every operation use. The token is therefore a checked value, not a caller-
mintable authority primitive.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Callable, Final, Protocol, TypeAlias, cast

from ..state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex
from .fcis_m6_f03_reopen import (
    F03ReopenSuccessV1,
    reopen_layout_bytes,
)
from .fcis_m6_f05_authenticated_genesis import (
    F05GenesisRejectV1,
    F05GenesisV1,
    validate_f05_genesis_value,
)

FCIS_M6_F06_REOPEN_AUTHORIZATION_SCHEMA_V1: Final[str] = (
    "zenodex/fcis/m6/f06/reopen-authorization/v1"
)
FCIS_M6_F06_MAX_U64_V1: Final[int] = (1 << 64) - 1
_ROOT_HEX: Final[frozenset[str]] = frozenset("0123456789abcdef")


class F06AuthorizationCodeV1(Enum):
    """Stable fail-closed F06 outcomes."""

    WRONG_EXACT_TYPE = "wrong_exact_type"
    REOPEN_REJECTED = "reopen_rejected"
    GENESIS_REJECTED = "genesis_rejected"
    INVALID_ROOT = "invalid_root"
    INVALID_EPOCH = "invalid_epoch"
    INVALID_WINDOW = "invalid_window"
    EVIDENCE_REJECTED = "evidence_rejected"
    EVIDENCE_MISMATCH = "evidence_mismatch"
    HEAD_MISMATCH = "head_mismatch"
    GENESIS_MISMATCH = "genesis_mismatch"
    EXTERNAL_REJECTED = "external_rejected"
    TOKEN_REJECTED = "token_rejected"
    AUTHORIZATION_EXPIRED = "authorization_expired"
    INVALID_OPERATION = "invalid_operation"


class F06OperationV1(Enum):
    """Every value-moving post-reopen operation needs the exact head token."""

    COMMIT = "commit"
    ACK_PUBLICATION = "ack_publication"
    MIGRATION = "migration"


class F06AuthorizationError(ValueError):
    """Raised when an F06 value is outside its closed schema."""


def _root(value: object, name: str) -> str:
    if (
        type(value) is not str
        or len(value) != 66
        or not value.startswith("0x")
        or value != value.lower()
        or any(character not in _ROOT_HEX for character in value[2:])
    ):
        raise F06AuthorizationError(f"{name} must be a lowercase 32-byte root")
    return value


def _u64(value: object, name: str) -> int:
    if type(value) is not int or value < 0 or value > FCIS_M6_F06_MAX_U64_V1:
        raise F06AuthorizationError(f"{name} is outside its closed u64 domain")
    return value


def _active(epoch: int, activation: int, expiration: int | None) -> bool:
    return epoch >= activation and (expiration is None or epoch < expiration)


def _derive_root(domain: str, payload: dict[str, object]) -> str:
    return cast(
        str,
        sha256_hex(domain_sep_bytes(domain, version=1) + canonical_json_bytes(payload)),
    )


@dataclass(frozen=True, slots=True)
class F06ReopenHeadV1:
    """Exact head projection obtained only after canonical F03 reopen."""

    genesis_root: str
    snapshot_root: str
    current_state_root: str
    authority_state_root: str
    authority_epoch: int
    deployment_config_root: str
    external_authorization_root: str
    head_root: str

    def __post_init__(self) -> None:
        for name in (
            "genesis_root",
            "snapshot_root",
            "current_state_root",
            "authority_state_root",
            "deployment_config_root",
            "external_authorization_root",
            "head_root",
        ):
            _root(object.__getattribute__(self, name), name)
        _u64(self.authority_epoch, "authority_epoch")
        expected = _derive_head_root(self)
        if self.head_root != expected:
            raise F06AuthorizationError("head_root does not rederive")


def _head_payload(value: F06ReopenHeadV1) -> dict[str, object]:
    return {
        "schema": FCIS_M6_F06_REOPEN_AUTHORIZATION_SCHEMA_V1,
        "genesis_root": value.genesis_root,
        "snapshot_root": value.snapshot_root,
        "current_state_root": value.current_state_root,
        "authority_state_root": value.authority_state_root,
        "authority_epoch": value.authority_epoch,
        "deployment_config_root": value.deployment_config_root,
        "external_authorization_root": value.external_authorization_root,
    }


def _derive_head_root(value: F06ReopenHeadV1) -> str:
    return _derive_root("zenodex/fcis/m6/f06/reopen-head", _head_payload(value))


def derive_f06_head_root_v1(value: F06ReopenHeadV1) -> str:
    """Return the exact root for one revalidated head projection."""

    value.__post_init__()
    return _derive_head_root(value)


@dataclass(frozen=True, slots=True)
class F06ExternalAuthorizationEvidenceV1:
    """External authority evidence awaiting the verifier adapter decision."""

    snapshot_root: str
    current_state_root: str
    authority_state_root: str
    authority_epoch: int
    deployment_config_root: str
    external_authorization_root: str
    activation_epoch: int
    expiration_epoch: int | None
    evidence_root: str

    def __post_init__(self) -> None:
        for name in (
            "snapshot_root",
            "current_state_root",
            "authority_state_root",
            "deployment_config_root",
            "external_authorization_root",
            "evidence_root",
        ):
            _root(object.__getattribute__(self, name), name)
        _u64(self.authority_epoch, "authority_epoch")
        _u64(self.activation_epoch, "activation_epoch")
        if self.expiration_epoch is not None:
            _u64(self.expiration_epoch, "expiration_epoch")
            if self.expiration_epoch <= self.activation_epoch:
                raise F06AuthorizationError("expiration_epoch must follow activation_epoch")
        expected = _derive_evidence_root(self)
        if self.evidence_root != expected:
            raise F06AuthorizationError("evidence_root does not rederive")


def _evidence_payload(value: F06ExternalAuthorizationEvidenceV1) -> dict[str, object]:
    return {
        "schema": FCIS_M6_F06_REOPEN_AUTHORIZATION_SCHEMA_V1,
        "snapshot_root": value.snapshot_root,
        "current_state_root": value.current_state_root,
        "authority_state_root": value.authority_state_root,
        "authority_epoch": value.authority_epoch,
        "deployment_config_root": value.deployment_config_root,
        "external_authorization_root": value.external_authorization_root,
        "activation_epoch": value.activation_epoch,
        "expiration_epoch": value.expiration_epoch,
    }


def _derive_evidence_root(value: F06ExternalAuthorizationEvidenceV1) -> str:
    return _derive_root("zenodex/fcis/m6/f06/external-evidence", _evidence_payload(value))


def derive_f06_evidence_root_v1(value: F06ExternalAuthorizationEvidenceV1) -> str:
    """Return the exact root for one external authorization evidence value."""

    value.__post_init__()
    return _derive_evidence_root(value)


@dataclass(frozen=True, slots=True)
class F06AuthorizationTokenV1:
    """Exact-head token rechecked by every operation boundary."""

    head: F06ReopenHeadV1
    evidence: F06ExternalAuthorizationEvidenceV1
    token_root: str

    def __post_init__(self) -> None:
        if type(self.head) is not F06ReopenHeadV1:
            raise F06AuthorizationError("token head has the wrong exact type")
        if type(self.evidence) is not F06ExternalAuthorizationEvidenceV1:
            raise F06AuthorizationError("token evidence has the wrong exact type")
        self.head.__post_init__()
        self.evidence.__post_init__()
        if not _evidence_matches_head(self.evidence, self.head):
            raise F06AuthorizationError("token evidence is crossed with its head")
        _root(self.token_root, "token_root")
        expected = _derive_token_root(self.head, self.evidence)
        if self.token_root != expected:
            raise F06AuthorizationError("token_root does not rederive")


def _derive_token_root(head: F06ReopenHeadV1, evidence: F06ExternalAuthorizationEvidenceV1) -> str:
    return _derive_root(
        "zenodex/fcis/m6/f06/authorization-token",
        {"head_root": head.head_root, "evidence_root": evidence.evidence_root},
    )


@dataclass(frozen=True, slots=True)
class F06AuthorizationUseV1:
    """Successful point-of-use check; it carries no reusable authority."""

    operation: F06OperationV1
    token_root: str
    head_root: str

    def __post_init__(self) -> None:
        if type(self.operation) is not F06OperationV1:
            raise F06AuthorizationError("operation has the wrong exact type")
        _root(self.token_root, "token_root")
        _root(self.head_root, "head_root")


@dataclass(frozen=True, slots=True)
class F06AuthorizationRejectV1:
    code: F06AuthorizationCodeV1
    path: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.code) is not F06AuthorizationCodeV1:
            raise F06AuthorizationError("F06 code has the wrong exact type")
        if type(self.path) is not tuple or any(type(part) is not str for part in self.path):
            raise F06AuthorizationError("F06 path must be an exact string tuple")


F06AuthorizationResultV1: TypeAlias = F06AuthorizationTokenV1 | F06AuthorizationRejectV1
F06AuthorizationUseResultV1: TypeAlias = F06AuthorizationUseV1 | F06AuthorizationRejectV1


class F06ExternalVerifierAdapterV1(Protocol):
    """Shell-selected external authority verifier premise."""

    def verify_f06_reopen_authorization(
        self,
        evidence: object,
        *,
        expected_head_root: object,
        expected_snapshot_root: object,
        expected_current_state_root: object,
        expected_authority_state_root: object,
        expected_authority_epoch: object,
        expected_deployment_config_root: object,
        expected_external_authorization_root: object,
        current_epoch: object,
    ) -> object:
        """Return exact True only after external authority verification."""


def _reject(code: F06AuthorizationCodeV1, *path: str) -> F06AuthorizationRejectV1:
    return F06AuthorizationRejectV1(code, path)


def _reopen_head(
    reopened: object, genesis: object, external_authorization_root: object
) -> F06ReopenHeadV1 | F06AuthorizationRejectV1:
    if type(reopened) is not F03ReopenSuccessV1:
        return _reject(F06AuthorizationCodeV1.WRONG_EXACT_TYPE, "reopened")
    reopened_value = cast(F03ReopenSuccessV1, reopened)
    try:
        reopened_value.__post_init__()
        canonical = reopen_layout_bytes(reopened_value.canonical_layout_bytes)
        if type(canonical) is not F03ReopenSuccessV1 or canonical != reopened_value:
            return _reject(F06AuthorizationCodeV1.REOPEN_REJECTED, "reopened", "fixed_point")
    except (AttributeError, TypeError, ValueError, ArithmeticError, RecursionError):
        return _reject(F06AuthorizationCodeV1.REOPEN_REJECTED, "reopened")

    checked_genesis = validate_f05_genesis_value(genesis)
    if type(checked_genesis) is F05GenesisRejectV1:
        return _reject(F06AuthorizationCodeV1.GENESIS_REJECTED, "genesis")
    genesis_value = cast(F05GenesisV1, checked_genesis)
    history = reopened_value.history
    try:
        external_root = _root(external_authorization_root, "external_authorization_root")
        first_authority = history.authority_epochs[0]
        if history.genesis_state_root != genesis_value.initial_state_root:
            return _reject(F06AuthorizationCodeV1.GENESIS_MISMATCH, "genesis", "state")
        if history.deployment_config_root != genesis_value.initial_configuration_root:
            return _reject(F06AuthorizationCodeV1.GENESIS_MISMATCH, "genesis", "configuration")
        if first_authority.authority_state_root != genesis_value.initial_authority_profile_root:
            return _reject(F06AuthorizationCodeV1.GENESIS_MISMATCH, "genesis", "authority")
        head_payload: dict[str, object] = {
            "schema": FCIS_M6_F06_REOPEN_AUTHORIZATION_SCHEMA_V1,
            "genesis_root": genesis_value.genesis_root,
            "snapshot_root": reopened_value.layout_root,
            "current_state_root": history.current_state_root,
            "authority_state_root": history.current_authority.authority_state_root,
            "authority_epoch": history.current_authority.epoch_index,
            "deployment_config_root": history.deployment_config_root,
            "external_authorization_root": external_root,
        }
        head_root = _derive_root("zenodex/fcis/m6/f06/reopen-head", head_payload)
        return F06ReopenHeadV1(
            genesis_root=genesis_value.genesis_root,
            snapshot_root=reopened_value.layout_root,
            current_state_root=history.current_state_root,
            authority_state_root=history.current_authority.authority_state_root,
            authority_epoch=history.current_authority.epoch_index,
            deployment_config_root=history.deployment_config_root,
            external_authorization_root=external_root,
            head_root=head_root,
        )
    except (AttributeError, IndexError, TypeError, ValueError, ArithmeticError):
        return _reject(F06AuthorizationCodeV1.REOPEN_REJECTED, "reopened", "head")


def _evidence_matches_head(
    evidence: F06ExternalAuthorizationEvidenceV1, head: F06ReopenHeadV1
) -> bool:
    return (
        evidence.snapshot_root == head.snapshot_root
        and evidence.current_state_root == head.current_state_root
        and evidence.authority_state_root == head.authority_state_root
        and evidence.authority_epoch == head.authority_epoch
        and evidence.deployment_config_root == head.deployment_config_root
        and evidence.external_authorization_root == head.external_authorization_root
    )


def _call_external_verifier(
    evidence: F06ExternalAuthorizationEvidenceV1,
    head: F06ReopenHeadV1,
    verifier_adapter: object,
    current_epoch: int,
) -> bool:
    method = getattr(verifier_adapter, "verify_f06_reopen_authorization", None)
    if not callable(method):
        return False
    try:
        decision = cast(Callable[..., object], method)(
            evidence,
            expected_head_root=head.head_root,
            expected_snapshot_root=head.snapshot_root,
            expected_current_state_root=head.current_state_root,
            expected_authority_state_root=head.authority_state_root,
            expected_authority_epoch=head.authority_epoch,
            expected_deployment_config_root=head.deployment_config_root,
            expected_external_authorization_root=head.external_authorization_root,
            current_epoch=current_epoch,
        )
    except (AttributeError, TypeError, ValueError, ArithmeticError, RecursionError):
        return False
    return decision is True


def _check_evidence(
    evidence: object, head: F06ReopenHeadV1, current_epoch: object
) -> F06AuthorizationRejectV1 | F06ExternalAuthorizationEvidenceV1:
    if type(evidence) is not F06ExternalAuthorizationEvidenceV1:
        return _reject(F06AuthorizationCodeV1.EVIDENCE_REJECTED, "evidence")
    checked = evidence
    try:
        checked.__post_init__()
        epoch = _u64(current_epoch, "current_epoch")
    except (AttributeError, TypeError, ValueError, ArithmeticError):
        return _reject(F06AuthorizationCodeV1.EVIDENCE_REJECTED, "evidence")
    if not _evidence_matches_head(checked, head):
        return _reject(F06AuthorizationCodeV1.EVIDENCE_MISMATCH, "evidence", "head")
    if not _active(epoch, checked.activation_epoch, checked.expiration_epoch):
        return _reject(F06AuthorizationCodeV1.AUTHORIZATION_EXPIRED, "evidence", "bounds")
    return checked


def issue_f06_reopen_token(
    reopened: object,
    *,
    genesis: object,
    external_authorization_root: object,
    evidence: object,
    verifier_adapter: object,
    current_epoch: object,
) -> F06AuthorizationResultV1:
    """Issue a token only after canonical reopen and external verification."""

    head = _reopen_head(reopened, genesis, external_authorization_root)
    if type(head) is F06AuthorizationRejectV1:
        return head
    head_value = cast(F06ReopenHeadV1, head)
    checked_evidence = _check_evidence(evidence, head_value, current_epoch)
    if type(checked_evidence) is F06AuthorizationRejectV1:
        return checked_evidence
    evidence_value = cast(F06ExternalAuthorizationEvidenceV1, checked_evidence)
    epoch = cast(int, current_epoch)
    if not _call_external_verifier(evidence_value, head_value, verifier_adapter, epoch):
        return _reject(F06AuthorizationCodeV1.EXTERNAL_REJECTED, "verifier")
    try:
        return F06AuthorizationTokenV1(
            head=head_value,
            evidence=evidence_value,
            token_root=_derive_token_root(head_value, evidence_value),
        )
    except (AttributeError, TypeError, ValueError, ArithmeticError):
        return _reject(F06AuthorizationCodeV1.TOKEN_REJECTED, "token")


def require_f06_token_at_use(
    reopened: object,
    *,
    genesis: object,
    token: object,
    operation: object,
    verifier_adapter: object,
    current_epoch: object,
) -> F06AuthorizationUseResultV1:
    """Reopen and externally reverify the exact token for one operation."""

    if type(operation) is not F06OperationV1:
        return _reject(F06AuthorizationCodeV1.INVALID_OPERATION, "operation")
    if type(token) is not F06AuthorizationTokenV1:
        return _reject(F06AuthorizationCodeV1.TOKEN_REJECTED, "token")
    checked_token = token
    try:
        checked_token.__post_init__()
    except (AttributeError, TypeError, ValueError, ArithmeticError):
        return _reject(F06AuthorizationCodeV1.TOKEN_REJECTED, "token")
    head = _reopen_head(
        reopened,
        genesis,
        checked_token.evidence.external_authorization_root,
    )
    if type(head) is F06AuthorizationRejectV1:
        return head
    head_value = cast(F06ReopenHeadV1, head)
    if head_value != checked_token.head:
        return _reject(F06AuthorizationCodeV1.HEAD_MISMATCH, "token", "head")
    checked_evidence = _check_evidence(checked_token.evidence, head_value, current_epoch)
    if type(checked_evidence) is F06AuthorizationRejectV1:
        return checked_evidence
    evidence_value = cast(F06ExternalAuthorizationEvidenceV1, checked_evidence)
    epoch = cast(int, current_epoch)
    if not _call_external_verifier(evidence_value, head_value, verifier_adapter, epoch):
        return _reject(F06AuthorizationCodeV1.EXTERNAL_REJECTED, "verifier")
    return F06AuthorizationUseV1(
        operation=operation,
        token_root=checked_token.token_root,
        head_root=head_value.head_root,
    )


__all__ = (
    "FCIS_M6_F06_REOPEN_AUTHORIZATION_SCHEMA_V1",
    "F06AuthorizationCodeV1",
    "F06AuthorizationError",
    "F06AuthorizationRejectV1",
    "F06AuthorizationResultV1",
    "F06AuthorizationTokenV1",
    "F06AuthorizationUseResultV1",
    "F06AuthorizationUseV1",
    "F06ExternalAuthorizationEvidenceV1",
    "F06ExternalVerifierAdapterV1",
    "F06OperationV1",
    "F06ReopenHeadV1",
    "derive_f06_evidence_root_v1",
    "derive_f06_head_root_v1",
    "issue_f06_reopen_token",
    "require_f06_token_at_use",
)
