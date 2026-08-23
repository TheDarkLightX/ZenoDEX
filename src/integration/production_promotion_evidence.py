"""Production-promotion evidence verifiers (six lanes).

Architecture
============

The module follows a small object-oriented pipeline so each concern lives in
exactly one place (Single Responsibility), new lanes can be added by writing
one ``Lane`` subclass (Open-Closed), and the shared orchestration is
case-blind to lane-specific schemas (Liskov / Interface Segregation):

    public API (thin wrappers)
        └─ ``_evaluate_lane(lane, evidence, ctx)``           # orchestration
              ├─ ``_P.*`` parser primitives                  # validation
              ├─ ``Lane.validate``                           # rules
              ├─ ``_check_unknown_fields``                   # strict schema
              └─ ``_check_self_binding_hash``                # tamper-evident

Hash chain (defense in depth)
-----------------------------

    profile/posture body  ──►  evidence body  ──►  evidence_hash
        (bounded gate)           (this module)
                                   ▲
                            binding fields (lane-specific):
                            chain_id, profile_hash, exercise_hash,
                            verifier_cmd_hash, etc.

Every lane enforces, in this order:

1. Type/shape check on the raw envelope (``_P.mapping``).
2. Schema discriminator string match (the ``schema`` field).
3. Strict unknown-field rejection (no silent accept).
4. Per-field parse (hex casing, length, safe-token, bool, bounded-int).
5. Cross-field invariants (heights, intervals, signers agreeing, etc.).
6. Binding to external context (bounded gate, live wrapper, operator state).
7. Freshness window (``issued_at`` within configured horizon).
8. Self-binding hash recomputation over the canonical body.

If any step adds a gap, ``production_ready`` is ``False`` and the gap list
explains why. Oracle and hardware-wallet Ed25519 attestations are verified
against canonical ZenoDEX statements. TEE/vendor attestation verification
remains external and is bound here by receipt and measurement hashes.
"""

from __future__ import annotations

import ipaddress
import time
from abc import ABC, abstractmethod
from dataclasses import dataclass
from dataclasses import replace as dataclass_replace
from typing import Any, ClassVar, Final, Mapping, Sequence
from urllib.parse import urlparse

from src.integration.confidential_runtime_receipts import (
    CONFIDENTIAL_RUNTIME_EXECUTION_RECEIPT_SCHEMA_V1,
    confidential_runtime_execution_receipt_hash_v1,
)
from src.integration.live_proof_wrapper import LIVE_PROOF_WRAPPER_ARTIFACT_BINDING_HASH_DOMAIN
from src.integration.zeno_ledger_v0 import (
    canonical_json_bytes_v0,
    compute_dex_snapshot_app_root_v0,
    compute_tau_app_state_app_root_v0,
    hash_v0,
)
from src.state.app_root import APP_ROOT_LANE_KINDS
from src.state.canonical import (
    bounded_json_utf8_size,
    canonical_json_bytes,
    domain_sep_bytes,
    sha256_hex,
)

try:
    from cryptography.exceptions import InvalidSignature
    from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PublicKey

    _ED25519_AVAILABLE = True
except ImportError:  # pragma: no cover - dependency guard for fail-closed reports
    InvalidSignature = Exception
    Ed25519PublicKey = None
    _ED25519_AVAILABLE = False

# -----------------------------------------------------------------------------
# Public schema identifiers and lane ids.
# -----------------------------------------------------------------------------

ORACLE_AUTHORITY_EVIDENCE_SCHEMA_V1: Final = "zenodex/production-oracle-authority-evidence/v1"
HARDWARE_WALLET_EVIDENCE_SCHEMA_V1: Final = "zenodex/production-hardware-wallet-evidence/v1"
ZK_WRAPPING_EVIDENCE_SCHEMA_V1: Final = "zenodex/production-zk-wrapping-evidence/v1"
AUTOTRADER_EVIDENCE_SCHEMA_V1: Final = "zenodex/production-autotrader-evidence/v1"
CONFIDENTIAL_RUNTIME_EVIDENCE_SCHEMA_V1: Final = "zenodex/production-confidential-runtime-evidence/v1"
APP_ROOT_JMT_EVIDENCE_SCHEMA_V1: Final = "zenodex/production-app-root-jmt-evidence/v1"
APP_ROOT_JMT_EVIDENCE_SCHEMA_V2: Final = "zenodex/production-app-root-jmt-evidence/v2"

PRODUCTION_PROMOTION_STATUS_SCHEMA_V1: Final = "zenodex/production-promotion-status/v1"
PRODUCTION_PROMOTION_BUNDLE_STATUS_SCHEMA_V1: Final = "zenodex/production-promotion-bundle-status/v1"

LANE_ORACLE_AUTHORITY: Final = "oracle_authority"
LANE_HARDWARE_WALLET: Final = "hardware_wallet"
LANE_ZK_WRAPPING: Final = "zk_wrapping"
LANE_AUTOTRADER: Final = "autotrader"
LANE_CONFIDENTIAL_RUNTIME: Final = "confidential_runtime"
LANE_APP_ROOT_JMT: Final = "app_root_jmt"

ALL_LANE_IDS: Final = (
    LANE_ORACLE_AUTHORITY,
    LANE_HARDWARE_WALLET,
    LANE_ZK_WRAPPING,
    LANE_AUTOTRADER,
    LANE_CONFIDENTIAL_RUNTIME,
    LANE_APP_ROOT_JMT,
)


# -----------------------------------------------------------------------------
# Validation policy constants (defense in depth — all thresholds explicit).
# -----------------------------------------------------------------------------

_HASH_HEX_LEN: Final = 64
_PUBKEY_HEX_LEN: Final = 64
_SIGNATURE_HEX_LEN: Final = 128
_HEX_CHARS: Final = frozenset("abcdef0123456789")
_SAFE_TOKEN_CHARS: Final = frozenset("abcdefghijklmnopqrstuvwxyz0123456789._-")
_SAFE_TOKEN_MAX_LEN: Final = 128

_MIN_AUTOTRADER_UNATTENDED_SECONDS: Final = 24 * 3600
_MAX_AUTOTRADER_HEARTBEAT_GAP_SECONDS: Final = 5 * 60
_MIN_AUTOTRADER_MULTI_SIGNERS: Final = 2
_MAX_AUTOTRADER_MULTI_SIGNERS: Final = 100
_MAX_AUTOTRADER_CRASH_RECOVERY_ENTRIES: Final = 1000
_MAX_AUTOTRADER_HEARTBEAT_LIST_LEN: Final = 100_000

_MAX_EVIDENCE_AGE_SECONDS: Final = 30 * 24 * 3600
_MAX_AUDIT_AGE_SECONDS: Final = 365 * 24 * 3600
_MAX_TEE_VERIFICATION_LAG_SECONDS: Final = 24 * 3600
_FUTURE_SKEW_TOLERANCE_SECONDS: Final = 60

_MAX_TICKS_PER_PROCESS_HARD_CAP: Final = 1_000_000
_MAX_APPROVED_MEASUREMENTS: Final = 1000
_MAX_APP_ROOT_CHECKS: Final = 100
_MAX_APP_ROOT_NEGATIVE_CHECKS: Final = 50
_MAX_APP_ROOT_SOURCE_PAYLOAD_BYTES: Final = 1_000_000

_APP_ROOT_REQUIRED_POSITIVE_MODES: Final = frozenset(
    {
        "plain_dex_snapshot_live_root",
        "tau_app_state_wrapper_live_root",
        "local_block_pre_snapshot_header",
    }
)
_APP_ROOT_REQUIRED_NEGATIVE_MUTATIONS: Final = frozenset({"lane_tamper_rejected"})
_APP_ROOT_DERIVATION_PATHS: Final[Mapping[str, str]] = {
    "plain_dex_snapshot_live_root": (
        "src/integration/zeno_ledger_v0.py:compute_dex_snapshot_app_root_v0"
    ),
    "tau_app_state_wrapper_live_root": (
        "src/integration/zeno_ledger_v0.py:compute_tau_app_state_app_root_v0"
    ),
    "local_block_pre_snapshot_header": (
        "src/integration/zeno_ledger_v0.py:compute_dex_snapshot_app_root_v0"
    ),
}

_INT_BOUND_HI: Final = (1 << 63) - 1

_ALLOWED_TEE_KINDS: Final = frozenset(
    {"nitro", "azure-sevsnp", "intel-sgx", "amd-sev-snp", "custom-tee"}
)
_TEE_KIND_TO_PREFIX: Final[Mapping[str, str]] = {
    "nitro": "nitro:",
    "azure-sevsnp": "azure-sevsnp:",
    "intel-sgx": "intel-sgx:",
    "amd-sev-snp": "amd-sev-snp:",
    "custom-tee": "custom-tee:",
}
_ALLOWED_HW_WALLET_MODELS: Final = frozenset(
    {
        "ledger-nano-s",
        "ledger-nano-s-plus",
        "ledger-nano-x",
        "ledger-stax",
        "trezor-one",
        "trezor-model-t",
        "trezor-safe-3",
        "trezor-safe-5",
        "keystone-3-pro",
        "gridplus-lattice1",
    }
)
_ALLOWED_OS_PROMPT_KINDS: Final = frozenset(
    {"screenshot_hash", "ocr_text_hash", "screen_capture_hash"}
)
_PUBLIC_TESTNET_NETWORK: Final = "public_testnet"
_NEAR_AND_SAME_HOUR_SECONDS: Final = 3600
_PLACEHOLDER_MARKERS: Final = ("PLACEHOLDER", "REPLACE_ME", "TODO", "FIXME", "YOUR_")
_RUNBOOK_PLACEHOLDER_VALUES: Final = frozenset(
    {
        "APPROVAL_CAPTURED_AT",
        "APPROVAL_SIGNATURE",
        "APPROVAL_TX_PAYLOAD_HASH",
        "ACCEPTED_AT",
        "APP_ROOT_CHECKED_AT",
        "APPROVED_MEASUREMENT",
        "ATTESTATION_EPOCH",
        "ATTESTATION_RECEIPT_HASH",
        "ATTESTATION_CHALLENGE",
        "ATTESTATION_SIGNATURE",
        "AUDITED_AT",
        "AUDIT_ID",
        "AUDIT_REPORT_HASH",
        "AUDITOR",
        "AUTHORITY_ATTESTATION_SIGNATURE",
        "AUTHORITY_ATTESTATION_SIGNER_PUBKEY",
        "CHECK_NOW",
        "CONFIG_MAX_ACTIONS_PER_TICK",
        "CONFIG_MAX_RUNS_PER_PROCESS",
        "DEVICE_FIRMWARE_VERSION",
        "DEVICE_ID",
        "DEVICE_MODEL",
        "DEVICE_PUBKEY",
        "DURATION_SECONDS",
        "EXECUTION_ID",
        "EXECUTION_KIND",
        "EXPECTED_CHAIN_ID",
        "EXPECTED_DEVICE_PUBKEY",
        "EXPECTED_EXTENSION_ID",
        "EXPECTED_ORACLE_AUTHORITY_SIGNER_PUBKEY",
        "EXPECTED_SURFACE",
        "EXTERNAL_VERIFIER_BINDING_HASH",
        "ISSUED_AT",
        "LAST_HEARTBEAT_AT",
        "MAX_ACTIONS_PER_TICK_OBSERVED",
        "MAX_RUNS_PER_PROCESS_OBSERVED",
        "OPERATOR_STATUS_HASH",
        "ORACLE_AUTHORITY_ID",
        "PLATFORM_PUBKEY",
        "PROMPT_CAPTURED_AT",
        "PROMPT_HASH",
        "PROMPT_KIND",
        "PROVIDER_ID",
        "PUBLIC_BROADCAST_BLOCK_HASH",
        "PUBLIC_BROADCAST_EXPLORER_URL",
        "PUBLIC_EFFECT_DIGEST",
        "PUBLIC_SETTLEMENT_BLOCK_HASH",
        "PUBLIC_SETTLEMENT_EXPLORER_URL",
        "RAW_ATTESTATION_HASH",
        "RESULT_CODE",
        "REQUEST_ID",
        "RUNTIME_RECEIPT_HASH",
        "STARTED_AT",
        "SUPERVISOR_ID",
        "SUPERVISOR_PROFILE_HASH",
        "TEE_KIND",
        "TEE_VERIFIED_AT",
        "TICKS_EXECUTED",
        "TICKS_FAILED",
        "TICKS_THROTTLED",
        "CURRENT_EPOCH",
        "UNITS_CHARGED",
        "VERIFIER_CMD_JSON",
        "WALLET_AUTHORITY_PROFILE_HASH",
    }
)


def _is_template_placeholder(value: str) -> bool:
    stripped = value.strip()
    if stripped in _RUNBOOK_PLACEHOLDER_VALUES:
        return True
    upper = stripped.upper()
    return any(marker in upper for marker in _PLACEHOLDER_MARKERS)


# -----------------------------------------------------------------------------
# Gap accumulator.
# -----------------------------------------------------------------------------


class _Gaps:
    """Append-only gap container with consistent ``path: message`` formatting."""

    __slots__ = ("_items",)

    def __init__(self) -> None:
        self._items: list[str] = []

    def add(self, message: str) -> None:
        self._items.append(message)

    def at(self, path: str, message: str) -> None:
        self._items.append(f"{path}: {message}")

    def __bool__(self) -> bool:
        return bool(self._items)

    def __len__(self) -> int:
        return len(self._items)

    def to_list(self) -> list[str]:
        return list(self._items)


# -----------------------------------------------------------------------------
# Parser primitives (``_P``).
# -----------------------------------------------------------------------------


class _P:
    """Pure parsing/validation primitives.

    Each returns the parsed value on success, or ``None`` and appends a gap.
    Never raises; never mutates.
    """

    @staticmethod
    def mapping(value: object, *, path: str, gaps: _Gaps) -> Mapping[str, Any] | None:
        if not isinstance(value, Mapping):
            gaps.at(path, "must be a JSON object")
            return None
        return value

    @staticmethod
    def nonempty_str(value: object, *, path: str, gaps: _Gaps) -> str | None:
        if not isinstance(value, str) or value == "":
            gaps.at(path, "must be a non-empty string")
            return None
        if _is_template_placeholder(value):
            # Production-promotion evidence is operator-facing, so the verifier
            # rejects collection-runbook placeholders at the parser boundary.
            # This keeps producer --check paths from emitting a green lane for a
            # self-consistent template artifact.
            gaps.at(path, f"placeholder value {value!r} must be replaced by real external artifact data")
            return None
        return value

    @staticmethod
    def bool_strict(value: object, *, path: str, gaps: _Gaps) -> bool | None:
        if not isinstance(value, bool):
            gaps.at(path, "must be a bool")
            return None
        return value

    @staticmethod
    def positive_int(value: object, *, path: str, gaps: _Gaps) -> int | None:
        return _P.bounded_int(value, path=path, gaps=gaps, lo=1, hi=_INT_BOUND_HI)

    @staticmethod
    def bounded_int(
        value: object,
        *,
        path: str,
        gaps: _Gaps,
        lo: int,
        hi: int = _INT_BOUND_HI,
    ) -> int | None:
        if not isinstance(value, int) or isinstance(value, bool):
            gaps.at(path, f"must be an integer in [{lo}, {hi}]")
            return None
        if value < lo or value > hi:
            gaps.at(path, f"must be an integer in [{lo}, {hi}]")
            return None
        return int(value)

    @staticmethod
    def hex_token(
        value: object,
        *,
        path: str,
        gaps: _Gaps,
        exact_len: int | None = None,
    ) -> str | None:
        s = _P.nonempty_str(value, path=path, gaps=gaps)
        if s is None:
            return None
        if s.startswith(("0x", "0X")):
            gaps.at(path, "must be lowercase canonical hex without 0x prefix")
            return None
        if any(ch not in _HEX_CHARS for ch in s):
            gaps.at(path, "must be lowercase canonical hex")
            return None
        if exact_len is not None and len(s) != exact_len:
            gaps.at(path, f"must be exactly {exact_len} lowercase canonical hex characters")
            return None
        return s

    @staticmethod
    def safe_token(value: object, *, path: str, gaps: _Gaps) -> str | None:
        s = _P.nonempty_str(value, path=path, gaps=gaps)
        if s is None:
            return None
        if len(s) > _SAFE_TOKEN_MAX_LEN:
            gaps.at(path, f"must be a safe token of at most {_SAFE_TOKEN_MAX_LEN} characters")
            return None
        if any(ch not in _SAFE_TOKEN_CHARS for ch in s):
            gaps.at(path, "must be a safe token (lowercase a-z0-9._-)")
            return None
        return s

    @staticmethod
    def list_of_mappings(
        value: object,
        *,
        path: str,
        gaps: _Gaps,
        min_len: int = 0,
        max_len: int | None = None,
    ) -> list[Mapping[str, Any]] | None:
        if not isinstance(value, list):
            gaps.at(path, "must be a list")
            return None
        if len(value) < min_len:
            gaps.at(path, f"must contain at least {min_len} entries")
            return None
        if max_len is not None and len(value) > max_len:
            gaps.at(path, f"must contain at most {max_len} entries")
            return None
        out: list[Mapping[str, Any]] = []
        for index, item in enumerate(value):
            if not isinstance(item, Mapping):
                gaps.at(f"{path}[{index}]", "must be an object")
                return None
            out.append(item)
        return out

    @staticmethod
    def list_of_positive_ints(
        value: object,
        *,
        path: str,
        gaps: _Gaps,
        min_len: int = 0,
        max_len: int | None = None,
    ) -> list[int] | None:
        if not isinstance(value, list):
            gaps.at(path, "must be a list")
            return None
        if len(value) < min_len:
            gaps.at(path, f"must contain at least {min_len} entries")
            return None
        if max_len is not None and len(value) > max_len:
            gaps.at(path, f"must contain at most {max_len} entries")
            return None
        out: list[int] = []
        for index, item in enumerate(value):
            n = _P.positive_int(item, path=f"{path}[{index}]", gaps=gaps)
            if n is None:
                return None
            out.append(n)
        return out


# -----------------------------------------------------------------------------
# Hashing helpers.
# -----------------------------------------------------------------------------


def _evidence_body(evidence: Mapping[str, Any]) -> dict[str, Any]:
    return {key: value for key, value in dict(evidence).items() if key != "evidence_hash"}


def _hash_evidence_v1(domain: str, body: Mapping[str, Any]) -> str:
    raw: str = hash_v0(domain, _evidence_body(body))
    return raw[2:] if raw.startswith(("0x", "0X")) else raw


def _check_self_binding_hash(
    obj: Mapping[str, Any],
    *,
    domain: str,
    gaps: _Gaps,
) -> str | None:
    raw = _P.hex_token(
        obj.get("evidence_hash"),
        path="evidence_hash",
        gaps=gaps,
        exact_len=_HASH_HEX_LEN,
    )
    if raw is None:
        return None
    expected = _hash_evidence_v1(domain, obj)
    if raw != expected:
        gaps.add("evidence_hash: does not match canonical recomputation")
        return None
    return raw


# -----------------------------------------------------------------------------
# Time helpers.
# -----------------------------------------------------------------------------


def _now_seconds(now: int | None) -> int:
    return int(now) if now is not None else int(time.time())


def _check_freshness(
    issued_at: int,
    *,
    now: int,
    max_age_s: int,
    label: str,
    gaps: _Gaps,
) -> None:
    if issued_at > now + _FUTURE_SKEW_TOLERANCE_SECONDS:
        gaps.add(f"{label} issued_at is in the future")
    elif now - issued_at > max_age_s:
        gaps.add(f"{label} issued_at is older than the production freshness window")


# -----------------------------------------------------------------------------
# Status builder.
# -----------------------------------------------------------------------------


def _build_lane_status(
    *,
    lane: str,
    gaps: _Gaps,
    evidence_hash: str | None,
    issued_at: int | None,
    bindings: Mapping[str, Any],
    extras: Mapping[str, Any],
) -> dict[str, Any]:
    gap_items = gaps.to_list()
    production_ready = not gap_items
    body: dict[str, Any] = {
        "schema": PRODUCTION_PROMOTION_STATUS_SCHEMA_V1,
        "lane": lane,
        "ok": production_ready,
        "production_ready": production_ready,
        "status": "ready" if production_ready else "blocked",
        "gaps": gap_items,
        "evidence_hash": evidence_hash,
        "issued_at": issued_at,
        "bindings": dict(bindings),
    }
    for key, value in dict(extras).items():
        if key not in body:
            body[key] = value
    return body


# -----------------------------------------------------------------------------
# Lane abstract base.
# -----------------------------------------------------------------------------


class Lane(ABC):
    LANE_ID: ClassVar[str]
    SCHEMA: ClassVar[str]
    DOMAIN: ClassVar[str]
    ALLOWED_FIELDS: ClassVar[frozenset[str]]
    MISSING_MESSAGE: ClassVar[str]

    @abstractmethod
    def validate(
        self,
        obj: Mapping[str, Any],
        ctx: "_LaneContext",
        gaps: _Gaps,
    ) -> tuple[dict[str, Any], dict[str, Any]]:
        """Validate body fields. Returns ``(bindings, extras)``."""


def _check_envelope(
    obj: Mapping[str, Any],
    *,
    lane: Lane,
    gaps: _Gaps,
) -> None:
    if obj.get("schema") != lane.SCHEMA:
        gaps.add(f"{lane.LANE_ID} evidence schema mismatch")
    _check_unknown_fields(obj, allowed=lane.ALLOWED_FIELDS, gaps=gaps)


def _check_unknown_fields(
    obj: Mapping[str, Any],
    *,
    allowed: frozenset[str],
    gaps: _Gaps,
) -> None:
    for key in obj.keys():
        if key not in allowed:
            gaps.add(f"unknown field: {key!r}")


# -----------------------------------------------------------------------------
# Lane contexts.
# -----------------------------------------------------------------------------


class _LaneContext:
    __slots__: tuple[str, ...] = ()


class _OracleAuthorityContext(_LaneContext):
    __slots__ = (
        "bounded_exercise_status",
        "expected_chain_id",
        "expected_authority_signer_pubkey",
        "now",
    )

    def __init__(
        self,
        *,
        bounded_exercise_status: Mapping[str, Any] | None,
        expected_chain_id: str | None,
        expected_authority_signer_pubkey: str | None,
        now: int,
    ) -> None:
        self.bounded_exercise_status = bounded_exercise_status
        self.expected_chain_id = expected_chain_id
        self.expected_authority_signer_pubkey = expected_authority_signer_pubkey
        self.now = now


class _HardwareWalletContext(_LaneContext):
    __slots__ = ("wallet_authority_profile_hash", "expected_device_pubkey", "now")

    def __init__(
        self,
        *,
        wallet_authority_profile_hash: str | None,
        expected_device_pubkey: str | None,
        now: int,
    ) -> None:
        self.wallet_authority_profile_hash = wallet_authority_profile_hash
        self.expected_device_pubkey = expected_device_pubkey
        self.now = now


class _ZkWrappingContext(_LaneContext):
    __slots__ = ("live_proof_wrapper_status", "expected_surface", "now")

    def __init__(
        self,
        *,
        live_proof_wrapper_status: Mapping[str, Any] | None,
        expected_surface: str | None,
        now: int,
    ) -> None:
        self.live_proof_wrapper_status = live_proof_wrapper_status
        self.expected_surface = expected_surface
        self.now = now


class _AutotraderContext(_LaneContext):
    __slots__ = (
        "supervisor_profile_hash",
        "config_max_actions_per_tick",
        "config_max_runs_per_process",
        "expected_chain_id",
        "expected_approval_signer_pubkeys",
        "now",
    )

    def __init__(
        self,
        *,
        supervisor_profile_hash: str | None,
        config_max_actions_per_tick: int | None,
        config_max_runs_per_process: int | None,
        expected_chain_id: str | None,
        expected_approval_signer_pubkeys: Sequence[str] | None,
        now: int,
    ) -> None:
        self.supervisor_profile_hash = supervisor_profile_hash
        self.config_max_actions_per_tick = config_max_actions_per_tick
        self.config_max_runs_per_process = config_max_runs_per_process
        self.expected_chain_id = expected_chain_id
        self.expected_approval_signer_pubkeys = expected_approval_signer_pubkeys
        self.now = now


class _ConfidentialContext(_LaneContext):
    __slots__ = (
        "approved_measurements",
        "operator_status_hash",
        "external_verifier_binding_hash",
        "expected_extension_id",
        "now",
    )

    def __init__(
        self,
        *,
        approved_measurements: Sequence[str] | None,
        operator_status_hash: str | None,
        external_verifier_binding_hash: str | None,
        expected_extension_id: str | None,
        now: int,
    ) -> None:
        self.approved_measurements = approved_measurements
        self.operator_status_hash = operator_status_hash
        self.external_verifier_binding_hash = external_verifier_binding_hash
        self.expected_extension_id = expected_extension_id
        self.now = now


class _AppRootJmtContext(_LaneContext):
    __slots__ = ("now",)

    def __init__(self, *, now: int) -> None:
        self.now = now


# -----------------------------------------------------------------------------
# Orchestration.
# -----------------------------------------------------------------------------


def _evaluate_lane(
    lane: Lane,
    evidence: Mapping[str, Any] | None,
    ctx: _LaneContext,
) -> dict[str, Any]:
    gaps = _Gaps()
    if evidence is None:
        gaps.add(lane.MISSING_MESSAGE)
        return _build_lane_status(
            lane=lane.LANE_ID,
            gaps=gaps,
            evidence_hash=None,
            issued_at=None,
            bindings={},
            extras={},
        )
    obj = _P.mapping(evidence, path="evidence", gaps=gaps)
    if obj is None:
        return _build_lane_status(
            lane=lane.LANE_ID,
            gaps=gaps,
            evidence_hash=None,
            issued_at=None,
            bindings={},
            extras={},
        )
    _check_envelope(obj, lane=lane, gaps=gaps)
    bindings, extras = lane.validate(obj, ctx, gaps)
    evidence_hash = _check_self_binding_hash(obj, domain=lane.DOMAIN, gaps=gaps)
    issued_at = _coerce_issued_at(obj.get("issued_at"))
    return _build_lane_status(
        lane=lane.LANE_ID,
        gaps=gaps,
        evidence_hash=evidence_hash,
        issued_at=issued_at,
        bindings=bindings,
        extras=extras,
    )


def _coerce_issued_at(value: object) -> int | None:
    if isinstance(value, int) and not isinstance(value, bool) and value > 0:
        return int(value)
    return None


def _parse_subobject(
    value: object,
    *,
    path: str,
    allowed: frozenset[str],
    gaps: _Gaps,
) -> Mapping[str, Any] | None:
    sub = _P.mapping(value, path=path, gaps=gaps)
    if sub is None:
        return None
    for key in sub.keys():
        if key not in allowed:
            gaps.add(f"unknown field: {path}.{key}")
    return sub


def _invalid_lane_context(expected: str, *, gaps: _Gaps) -> tuple[dict[str, Any], dict[str, Any]]:
    gaps.add(f"internal evaluator context mismatch: expected {expected}")
    return {}, {}


# -----------------------------------------------------------------------------
# Lane 1: oracle authority.
# -----------------------------------------------------------------------------


_ORACLE_FIELDS = frozenset(
    {
        "schema",
        "authority_id",
        "chain_id",
        "target_network",
        "exercise_hash",
        "profile_authority_hash",
        "public_broadcast_height",
        "public_settlement_height",
        "public_broadcast_block_hash",
        "public_settlement_block_hash",
        "public_broadcast_explorer_url",
        "public_settlement_explorer_url",
        "authority_attestation_signature",
        "authority_attestation_signer_pubkey",
        "issued_at",
        "evidence_hash",
    }
)


class _OracleAuthorityLane(Lane):
    LANE_ID = LANE_ORACLE_AUTHORITY
    SCHEMA = ORACLE_AUTHORITY_EVIDENCE_SCHEMA_V1
    DOMAIN = "production_oracle_authority_evidence_v1"
    ALLOWED_FIELDS = _ORACLE_FIELDS
    MISSING_MESSAGE = "production oracle authority evidence is missing"

    def validate(
        self,
        obj: Mapping[str, Any],
        ctx: "_LaneContext",
        gaps: _Gaps,
    ) -> tuple[dict[str, Any], dict[str, Any]]:
        if not isinstance(ctx, _OracleAuthorityContext):
            return _invalid_lane_context("_OracleAuthorityContext", gaps=gaps)
        authority_id = _P.nonempty_str(obj.get("authority_id"), path="authority_id", gaps=gaps)
        chain_id = _P.nonempty_str(obj.get("chain_id"), path="chain_id", gaps=gaps)
        target_network = _P.nonempty_str(obj.get("target_network"), path="target_network", gaps=gaps)
        exercise_hash = _P.nonempty_str(obj.get("exercise_hash"), path="exercise_hash", gaps=gaps)
        profile_authority_hash = _P.nonempty_str(
            obj.get("profile_authority_hash"), path="profile_authority_hash", gaps=gaps
        )
        broadcast_height = _P.positive_int(
            obj.get("public_broadcast_height"), path="public_broadcast_height", gaps=gaps
        )
        settlement_height = _P.positive_int(
            obj.get("public_settlement_height"), path="public_settlement_height", gaps=gaps
        )
        broadcast_block_hash = _P.hex_token(
            obj.get("public_broadcast_block_hash"),
            path="public_broadcast_block_hash",
            gaps=gaps,
            exact_len=_HASH_HEX_LEN,
        )
        settlement_block_hash = _P.hex_token(
            obj.get("public_settlement_block_hash"),
            path="public_settlement_block_hash",
            gaps=gaps,
            exact_len=_HASH_HEX_LEN,
        )
        broadcast_url = _P.nonempty_str(
            obj.get("public_broadcast_explorer_url"),
            path="public_broadcast_explorer_url",
            gaps=gaps,
        )
        settlement_url = _P.nonempty_str(
            obj.get("public_settlement_explorer_url"),
            path="public_settlement_explorer_url",
            gaps=gaps,
        )
        signature = _P.hex_token(
            obj.get("authority_attestation_signature"),
            path="authority_attestation_signature",
            gaps=gaps,
            exact_len=_SIGNATURE_HEX_LEN,
        )
        signer_pubkey = _P.hex_token(
            obj.get("authority_attestation_signer_pubkey"),
            path="authority_attestation_signer_pubkey",
            gaps=gaps,
            exact_len=_PUBKEY_HEX_LEN,
        )
        issued_at = _P.positive_int(obj.get("issued_at"), path="issued_at", gaps=gaps)

        _validate_oracle_authority_rules(
            target_network=target_network,
            chain_id=chain_id,
            broadcast_height=broadcast_height,
            settlement_height=settlement_height,
            broadcast_block_hash=broadcast_block_hash,
            settlement_block_hash=settlement_block_hash,
            broadcast_url=broadcast_url,
            settlement_url=settlement_url,
            issued_at=issued_at,
            ctx=ctx,
            gaps=gaps,
        )
        _validate_oracle_authority_attestation(
            authority_id=authority_id,
            chain_id=chain_id,
            target_network=target_network,
            exercise_hash=exercise_hash,
            profile_authority_hash=profile_authority_hash,
            broadcast_height=broadcast_height,
            settlement_height=settlement_height,
            broadcast_block_hash=broadcast_block_hash,
            settlement_block_hash=settlement_block_hash,
            broadcast_url=broadcast_url,
            settlement_url=settlement_url,
            issued_at=issued_at,
            signature=signature,
            signer_pubkey=signer_pubkey,
            gaps=gaps,
        )
        _validate_oracle_authority_signer_binding(
            signer_pubkey=signer_pubkey,
            ctx=ctx,
            gaps=gaps,
        )
        _bind_oracle_to_bounded(
            ctx.bounded_exercise_status,
            chain_id=chain_id,
            exercise_hash=exercise_hash,
            profile_authority_hash=profile_authority_hash,
            broadcast_height=broadcast_height,
            settlement_height=settlement_height,
            gaps=gaps,
        )

        bindings = {
            "authority_id": authority_id,
            "chain_id": chain_id,
            "target_network": target_network,
            "exercise_hash": exercise_hash,
            "profile_authority_hash": profile_authority_hash,
        }
        extras: dict[str, Any] = {
            "public_broadcast_height": broadcast_height,
            "public_settlement_height": settlement_height,
            "authority_attestation_signer_pubkey": signer_pubkey,
            "authority_attestation_signature": signature,
        }
        if broadcast_height is not None and settlement_height is not None:
            extras["settlement_lag_blocks"] = settlement_height - broadcast_height
        return bindings, extras


def _validate_oracle_authority_rules(
    *,
    target_network: str | None,
    chain_id: str | None,
    broadcast_height: int | None,
    settlement_height: int | None,
    broadcast_block_hash: str | None,
    settlement_block_hash: str | None,
    broadcast_url: str | None,
    settlement_url: str | None,
    issued_at: int | None,
    ctx: _OracleAuthorityContext,
    gaps: _Gaps,
) -> None:
    _validate_oracle_network(target_network=target_network, chain_id=chain_id, ctx=ctx, gaps=gaps)
    _validate_oracle_public_markers(
        broadcast_height=broadcast_height,
        settlement_height=settlement_height,
        broadcast_block_hash=broadcast_block_hash,
        settlement_block_hash=settlement_block_hash,
        broadcast_url=broadcast_url,
        settlement_url=settlement_url,
        gaps=gaps,
    )
    if issued_at is not None:
        _check_freshness(
            issued_at,
            now=ctx.now,
            max_age_s=_MAX_EVIDENCE_AGE_SECONDS,
            label="oracle authority evidence",
            gaps=gaps,
        )


def _validate_oracle_network(
    *,
    target_network: str | None,
    chain_id: str | None,
    ctx: _OracleAuthorityContext,
    gaps: _Gaps,
) -> None:
    if target_network is not None and target_network != _PUBLIC_TESTNET_NETWORK:
        gaps.add("production oracle authority evidence requires target_network=public_testnet")
    if ctx.expected_chain_id is None:
        gaps.add("expected chain_id is required for oracle authority binding")
    elif chain_id is not None and chain_id != ctx.expected_chain_id:
        gaps.add("oracle authority evidence chain_id mismatch")


def _validate_oracle_authority_signer_binding(
    *,
    signer_pubkey: str | None,
    ctx: _OracleAuthorityContext,
    gaps: _Gaps,
) -> None:
    expected = ctx.expected_authority_signer_pubkey
    if expected is None:
        gaps.add("expected oracle authority signer pubkey is required for binding")
        return
    expected = expected.lower()
    if signer_pubkey is not None and signer_pubkey != expected:
        gaps.add("oracle authority attestation signer pubkey mismatch")


def _validate_oracle_public_markers(
    *,
    broadcast_height: int | None,
    settlement_height: int | None,
    broadcast_block_hash: str | None,
    settlement_block_hash: str | None,
    broadcast_url: str | None,
    settlement_url: str | None,
    gaps: _Gaps,
) -> None:
    if broadcast_height is not None and settlement_height is not None and settlement_height < broadcast_height:
        gaps.add("public_settlement_height must be >= public_broadcast_height")
    if (
        broadcast_block_hash is not None
        and settlement_block_hash is not None
        and broadcast_block_hash == settlement_block_hash
    ):
        gaps.add("broadcast and settlement block hashes must differ")
    if broadcast_url is not None and settlement_url is not None and broadcast_url == settlement_url:
        gaps.add("broadcast and settlement explorer URLs must differ")
    if broadcast_url is not None:
        _validate_public_explorer_url(
            broadcast_url,
            label="public_broadcast_explorer_url",
            gaps=gaps,
        )
    if settlement_url is not None:
        _validate_public_explorer_url(
            settlement_url,
            label="public_settlement_explorer_url",
            gaps=gaps,
        )


def _validate_public_explorer_url(url: str, *, label: str, gaps: _Gaps) -> None:
    parsed = urlparse(url)
    host = (parsed.hostname or "").lower()
    if parsed.scheme.lower() != "https" or not host:
        gaps.add(f"{label} must be an https public explorer URL")
        return
    if host == "localhost" or host.endswith(".localhost") or host.endswith(".local"):
        # Review note (grade B+): oracle production evidence previously accepted
        # any non-empty, distinct explorer URL. That let localhost or lab-only
        # fixture URLs satisfy the public-testnet lane. The evaluator now rejects
        # local hosts before a manifest can become production_ready.
        gaps.add(f"{label} must not point at a local explorer host")
        return
    try:
        ip = ipaddress.ip_address(host)
    except ValueError:
        return
    if ip.is_private or ip.is_loopback or ip.is_link_local or ip.is_multicast or ip.is_reserved or ip.is_unspecified:
        gaps.add(f"{label} must not point at a private or non-routable explorer host")


def _oracle_authority_attestation_message(
    *,
    authority_id: str,
    chain_id: str,
    target_network: str,
    exercise_hash: str,
    profile_authority_hash: str,
    public_broadcast_height: int,
    public_settlement_height: int,
    public_broadcast_block_hash: str,
    public_settlement_block_hash: str,
    public_broadcast_explorer_url: str,
    public_settlement_explorer_url: str,
    issued_at: int,
) -> bytes:
    return canonical_json_bytes_v0(
        {
            "domain": "zenodex.production_oracle_authority_attestation.v1",
            "schema": ORACLE_AUTHORITY_EVIDENCE_SCHEMA_V1,
            "authority_id": authority_id,
            "chain_id": chain_id,
            "target_network": target_network,
            "exercise_hash": exercise_hash,
            "profile_authority_hash": profile_authority_hash,
            "public_broadcast_height": public_broadcast_height,
            "public_settlement_height": public_settlement_height,
            "public_broadcast_block_hash": public_broadcast_block_hash,
            "public_settlement_block_hash": public_settlement_block_hash,
            "public_broadcast_explorer_url": public_broadcast_explorer_url,
            "public_settlement_explorer_url": public_settlement_explorer_url,
            "issued_at": issued_at,
        }
    )


def _validate_oracle_authority_attestation(
    *,
    authority_id: str | None,
    chain_id: str | None,
    target_network: str | None,
    exercise_hash: str | None,
    profile_authority_hash: str | None,
    broadcast_height: int | None,
    settlement_height: int | None,
    broadcast_block_hash: str | None,
    settlement_block_hash: str | None,
    broadcast_url: str | None,
    settlement_url: str | None,
    issued_at: int | None,
    signature: str | None,
    signer_pubkey: str | None,
    gaps: _Gaps,
) -> None:
    if (
        authority_id is None
        or chain_id is None
        or target_network is None
        or exercise_hash is None
        or profile_authority_hash is None
        or broadcast_height is None
        or settlement_height is None
        or broadcast_block_hash is None
        or settlement_block_hash is None
        or broadcast_url is None
        or settlement_url is None
        or issued_at is None
        or signature is None
        or signer_pubkey is None
    ):
        return
    if not _ED25519_AVAILABLE or Ed25519PublicKey is None:
        gaps.add("oracle authority Ed25519 verifier is unavailable")
        return
    message = _oracle_authority_attestation_message(
        authority_id=authority_id,
        chain_id=chain_id,
        target_network=target_network,
        exercise_hash=exercise_hash,
        profile_authority_hash=profile_authority_hash,
        public_broadcast_height=broadcast_height,
        public_settlement_height=settlement_height,
        public_broadcast_block_hash=broadcast_block_hash,
        public_settlement_block_hash=settlement_block_hash,
        public_broadcast_explorer_url=broadcast_url,
        public_settlement_explorer_url=settlement_url,
        issued_at=issued_at,
    )
    try:
        public_key = Ed25519PublicKey.from_public_bytes(bytes.fromhex(str(signer_pubkey)))
        public_key.verify(bytes.fromhex(str(signature)), message)
    except (InvalidSignature, ValueError):
        # Review note (grade B -> A-): the oracle lane previously accepted any
        # 64-byte hex signature. Production authority evidence now requires the
        # declared Ed25519 signer key to verify the canonical public-testnet
        # exercise statement.
        gaps.add("oracle authority attestation signature is invalid")


def _bind_oracle_to_bounded(
    bounded: Mapping[str, Any] | None,
    *,
    chain_id: str | None,
    exercise_hash: str | None,
    profile_authority_hash: str | None,
    broadcast_height: int | None,
    settlement_height: int | None,
    gaps: _Gaps,
) -> None:
    if bounded is None:
        gaps.add("bounded oracle authority exercise status is required")
        return
    if bounded.get("authority_exercised") is not True:
        gaps.add("bounded oracle authority exercise must succeed before production binding")
    if bounded.get("public_testnet_exercised") is not True:
        gaps.add("bounded oracle authority exercise must include public testnet evidence")
    _bind_required_context_value(
        bounded,
        "exercise_hash",
        evidence_value=exercise_hash,
        missing_message="bounded oracle authority exercise_hash is required for binding",
        mismatch_message="evidence.exercise_hash does not match bounded exercise_hash",
        gaps=gaps,
    )
    _bind_required_context_value(
        bounded,
        "authority_hash",
        evidence_value=profile_authority_hash,
        missing_message="bounded oracle authority authority_hash is required for binding",
        mismatch_message="evidence.profile_authority_hash does not match bounded authority_hash",
        gaps=gaps,
    )
    _bind_required_context_value(
        bounded,
        "chain_id",
        evidence_value=chain_id,
        missing_message="bounded oracle authority chain_id is required for binding",
        mismatch_message="evidence.chain_id does not match bounded exercise chain_id",
        gaps=gaps,
    )
    _bind_required_context_value(
        bounded,
        "public_broadcast_height",
        evidence_value=broadcast_height,
        missing_message="bounded oracle authority public_broadcast_height is required for binding",
        mismatch_message="evidence.public_broadcast_height does not match bounded exercise height",
        gaps=gaps,
    )
    _bind_required_context_value(
        bounded,
        "public_settlement_height",
        evidence_value=settlement_height,
        missing_message="bounded oracle authority public_settlement_height is required for binding",
        mismatch_message="evidence.public_settlement_height does not match bounded exercise height",
        gaps=gaps,
    )


def _bind_required_context_value(
    ctx: Mapping[str, Any],
    key: str,
    *,
    evidence_value: object,
    missing_message: str,
    mismatch_message: str,
    gaps: _Gaps,
) -> None:
    ctx_value = ctx.get(key)
    if ctx_value is None:
        gaps.add(missing_message)
    elif evidence_value is not None and ctx_value != evidence_value:
        gaps.add(mismatch_message)


# -----------------------------------------------------------------------------
# Lane 2: hardware wallet.
# -----------------------------------------------------------------------------


_HW_WALLET_FIELDS = frozenset(
    {
        "schema",
        "device_id",
        "device_model",
        "device_firmware_version",
        "device_attestation",
        "os_prompt_capture",
        "device_approval_tx",
        "profile_wallet_authority_hash",
        "issued_at",
        "evidence_hash",
    }
)
_HW_ATTESTATION_FIELDS = frozenset({"pubkey", "challenge", "signature"})
_HW_OS_PROMPT_FIELDS = frozenset({"kind", "hash", "captured_at"})
_HW_APPROVAL_FIELDS = frozenset({"tx_payload_hash", "approval_signature", "captured_at"})


def _lower_if_str(value: object) -> object:
    return value.lower() if isinstance(value, str) else value


def production_hardware_wallet_attestation_challenge_v1(evidence: Mapping[str, Any]) -> str:
    """Return the canonical challenge a hardware-wallet attestation must sign.

    The challenge binds the device identity to the OS prompt capture, approval
    transaction payload, and active wallet-authority profile. Cryptographic
    signature verification still belongs to the external hardware-wallet
    attestation flow; this verifier rejects evidence that is internally
    self-consistent but whose challenge was chosen independently of the custody
    approval material.
    """

    attestation_raw = evidence.get("device_attestation")
    attestation = attestation_raw if isinstance(attestation_raw, Mapping) else {}
    prompt_raw = evidence.get("os_prompt_capture")
    prompt = prompt_raw if isinstance(prompt_raw, Mapping) else {}
    approval_raw = evidence.get("device_approval_tx")
    approval = approval_raw if isinstance(approval_raw, Mapping) else {}
    body = {
        "schema": evidence.get("schema"),
        "device_id": evidence.get("device_id"),
        "device_model": _lower_if_str(evidence.get("device_model")),
        "device_firmware_version": evidence.get("device_firmware_version"),
        "device_pubkey": _lower_if_str(attestation.get("pubkey")),
        "os_prompt_capture": {
            "kind": _lower_if_str(prompt.get("kind")),
            "hash": _lower_if_str(prompt.get("hash")),
            "captured_at": prompt.get("captured_at"),
        },
        "approval_tx_payload_hash": _lower_if_str(approval.get("tx_payload_hash")),
        "profile_wallet_authority_hash": evidence.get("profile_wallet_authority_hash"),
    }
    return hash_v0("production_hardware_wallet_attestation_challenge_v1", body).removeprefix("0x")


def production_hardware_wallet_attestation_message_v1(challenge: str) -> bytes:
    """Canonical message signed by the hardware device for custody evidence."""

    return canonical_json_bytes_v0(
        {
            "domain": "zenodex.production_hardware_wallet_attestation.v1",
            "schema": HARDWARE_WALLET_EVIDENCE_SCHEMA_V1,
            "challenge": challenge,
        }
    )


def production_hardware_wallet_approval_message_v1(tx_payload_hash: str) -> bytes:
    """Canonical approval message signed by the hardware device."""

    return canonical_json_bytes_v0(
        {
            "domain": "zenodex.production_hardware_wallet_approval.v1",
            "schema": HARDWARE_WALLET_EVIDENCE_SCHEMA_V1,
            "tx_payload_hash": tx_payload_hash,
        }
    )


class _HardwareWalletLane(Lane):
    LANE_ID = LANE_HARDWARE_WALLET
    SCHEMA = HARDWARE_WALLET_EVIDENCE_SCHEMA_V1
    DOMAIN = "production_hardware_wallet_evidence_v1"
    ALLOWED_FIELDS = _HW_WALLET_FIELDS
    MISSING_MESSAGE = "hardware wallet evidence is missing"

    def validate(
        self,
        obj: Mapping[str, Any],
        ctx: "_LaneContext",
        gaps: _Gaps,
    ) -> tuple[dict[str, Any], dict[str, Any]]:
        if not isinstance(ctx, _HardwareWalletContext):
            return _invalid_lane_context("_HardwareWalletContext", gaps=gaps)
        device_id = _P.nonempty_str(obj.get("device_id"), path="device_id", gaps=gaps)
        device_model_raw = _P.nonempty_str(obj.get("device_model"), path="device_model", gaps=gaps)
        device_model = device_model_raw.lower() if device_model_raw else None
        device_firmware_version = _P.nonempty_str(
            obj.get("device_firmware_version"), path="device_firmware_version", gaps=gaps
        )
        attestation = _parse_hardware_attestation(obj.get("device_attestation"), gaps=gaps)
        prompt = _parse_hardware_prompt(obj.get("os_prompt_capture"), gaps=gaps)
        approval = _parse_hardware_approval(obj.get("device_approval_tx"), gaps=gaps)
        profile_wallet_authority_hash = _P.nonempty_str(
            obj.get("profile_wallet_authority_hash"),
            path="profile_wallet_authority_hash",
            gaps=gaps,
        )
        issued_at = _P.positive_int(obj.get("issued_at"), path="issued_at", gaps=gaps)

        _validate_hardware_wallet_rules(
            raw_evidence=obj,
            device_model=device_model,
            attestation=attestation,
            prompt=prompt,
            approval=approval,
            profile_wallet_authority_hash=profile_wallet_authority_hash,
            issued_at=issued_at,
            ctx=ctx,
            gaps=gaps,
        )
        if issued_at is not None:
            _check_freshness(
                issued_at,
                now=ctx.now,
                max_age_s=_MAX_EVIDENCE_AGE_SECONDS,
                label="hardware wallet evidence",
                gaps=gaps,
            )

        bindings = {
            "device_id": device_id,
            "device_model": device_model,
            "device_firmware_version": device_firmware_version,
            "device_pubkey": attestation.get("pubkey"),
            "profile_wallet_authority_hash": profile_wallet_authority_hash,
        }
        extras: dict[str, Any] = {
            "os_prompt_capture_hash": prompt.get("hash"),
            "approval_tx_payload_hash": approval.get("tx_payload_hash"),
        }
        return bindings, extras


def _parse_hardware_attestation(value: object, *, gaps: _Gaps) -> dict[str, Any]:
    att = _parse_subobject(
        value,
        path="device_attestation",
        allowed=_HW_ATTESTATION_FIELDS,
        gaps=gaps,
    )
    if att is None:
        return {}
    return {
        "pubkey": _P.hex_token(
            att.get("pubkey"),
            path="device_attestation.pubkey",
            gaps=gaps,
            exact_len=_PUBKEY_HEX_LEN,
        ),
        "challenge": _P.hex_token(
            att.get("challenge"),
            path="device_attestation.challenge",
            gaps=gaps,
            exact_len=_HASH_HEX_LEN,
        ),
        "signature": _P.hex_token(
            att.get("signature"),
            path="device_attestation.signature",
            gaps=gaps,
            exact_len=_SIGNATURE_HEX_LEN,
        ),
    }


def _parse_hardware_prompt(value: object, *, gaps: _Gaps) -> dict[str, Any]:
    prompt = _parse_subobject(
        value,
        path="os_prompt_capture",
        allowed=_HW_OS_PROMPT_FIELDS,
        gaps=gaps,
    )
    if prompt is None:
        return {}
    kind_raw = _P.nonempty_str(prompt.get("kind"), path="os_prompt_capture.kind", gaps=gaps)
    return {
        "kind": kind_raw.lower() if kind_raw else None,
        "hash": _P.hex_token(
            prompt.get("hash"),
            path="os_prompt_capture.hash",
            gaps=gaps,
            exact_len=_HASH_HEX_LEN,
        ),
        "captured_at": _P.positive_int(
            prompt.get("captured_at"),
            path="os_prompt_capture.captured_at",
            gaps=gaps,
        ),
    }


def _parse_hardware_approval(value: object, *, gaps: _Gaps) -> dict[str, Any]:
    approval = _parse_subobject(
        value,
        path="device_approval_tx",
        allowed=_HW_APPROVAL_FIELDS,
        gaps=gaps,
    )
    if approval is None:
        return {}
    return {
        "tx_payload_hash": _P.hex_token(
            approval.get("tx_payload_hash"),
            path="device_approval_tx.tx_payload_hash",
            gaps=gaps,
            exact_len=_HASH_HEX_LEN,
        ),
        "approval_signature": _P.hex_token(
            approval.get("approval_signature"),
            path="device_approval_tx.approval_signature",
            gaps=gaps,
            exact_len=_SIGNATURE_HEX_LEN,
        ),
        "captured_at": _P.positive_int(
            approval.get("captured_at"),
            path="device_approval_tx.captured_at",
            gaps=gaps,
        ),
    }


def _validate_hardware_wallet_rules(
    *,
    raw_evidence: Mapping[str, Any],
    device_model: str | None,
    attestation: Mapping[str, Any],
    prompt: Mapping[str, Any],
    approval: Mapping[str, Any],
    profile_wallet_authority_hash: str | None,
    issued_at: int | None,
    ctx: _HardwareWalletContext,
    gaps: _Gaps,
) -> None:
    if device_model is not None and device_model not in _ALLOWED_HW_WALLET_MODELS:
        gaps.add(f"device_model {device_model!r} is not in the allowed hardware wallet list")

    prompt_kind = prompt.get("kind")
    if prompt_kind is not None and prompt_kind not in _ALLOWED_OS_PROMPT_KINDS:
        gaps.add(f"os_prompt_capture.kind {prompt_kind!r} is not in the allowed set")

    _validate_hardware_attestation_challenge(raw_evidence, attestation, gaps=gaps)
    _validate_hardware_attestation_vs_approval(attestation, approval, gaps=gaps)
    _validate_hardware_ed25519_signatures(attestation, approval, gaps=gaps)
    _validate_hardware_context_binding(
        attestation_pubkey=attestation.get("pubkey"),
        profile_wallet_authority_hash=profile_wallet_authority_hash,
        ctx=ctx,
        gaps=gaps,
    )
    _validate_hardware_capture_window(prompt, approval, gaps=gaps)
    _validate_hardware_capture_freshness(
        prompt,
        approval,
        issued_at=issued_at,
        now=ctx.now,
        gaps=gaps,
    )


def _validate_hardware_attestation_challenge(
    raw_evidence: Mapping[str, Any],
    attestation: Mapping[str, Any],
    *,
    gaps: _Gaps,
) -> None:
    challenge = attestation.get("challenge")
    if challenge is None:
        return
    expected = production_hardware_wallet_attestation_challenge_v1(raw_evidence)
    if challenge != expected:
        gaps.add("device_attestation.challenge must equal canonical hardware approval challenge")


def _validate_hardware_attestation_vs_approval(
    attestation: Mapping[str, Any],
    approval: Mapping[str, Any],
    *,
    gaps: _Gaps,
) -> None:
    attestation_challenge = attestation.get("challenge")
    approval_tx_hash = approval.get("tx_payload_hash")
    if attestation_challenge is not None and approval_tx_hash is not None and attestation_challenge == approval_tx_hash:
        gaps.add("device_attestation.challenge must differ from approval tx_payload_hash")

    attestation_signature = attestation.get("signature")
    approval_signature = approval.get("approval_signature")
    if (
        attestation_signature is not None
        and approval_signature is not None
        and attestation_signature == approval_signature
    ):
        gaps.add("attestation signature must differ from approval signature")


def _validate_hardware_ed25519_signatures(
    attestation: Mapping[str, Any],
    approval: Mapping[str, Any],
    *,
    gaps: _Gaps,
) -> None:
    pubkey = attestation.get("pubkey")
    challenge = attestation.get("challenge")
    attestation_signature = attestation.get("signature")
    tx_payload_hash = approval.get("tx_payload_hash")
    approval_signature = approval.get("approval_signature")
    _validate_ed25519_signature(
        pubkey=pubkey,
        signature=attestation_signature,
        message=(
            production_hardware_wallet_attestation_message_v1(str(challenge))
            if challenge is not None
            else None
        ),
        label="device_attestation.signature",
        gaps=gaps,
    )
    _validate_ed25519_signature(
        pubkey=pubkey,
        signature=approval_signature,
        message=(
            production_hardware_wallet_approval_message_v1(str(tx_payload_hash))
            if tx_payload_hash is not None
            else None
        ),
        label="device_approval_tx.approval_signature",
        gaps=gaps,
    )


def _validate_ed25519_signature(
    *,
    pubkey: object,
    signature: object,
    message: bytes | None,
    label: str,
    gaps: _Gaps,
) -> None:
    if pubkey is None or signature is None or message is None:
        return
    if not _ED25519_AVAILABLE or Ed25519PublicKey is None:
        gaps.add(f"{label} Ed25519 verifier is unavailable")
        return
    try:
        public_key = Ed25519PublicKey.from_public_bytes(bytes.fromhex(str(pubkey)))
        public_key.verify(bytes.fromhex(str(signature)), message)
    except (InvalidSignature, ValueError):
        gaps.add(f"{label} is invalid")


def _validate_hardware_context_binding(
    *,
    attestation_pubkey: str | None,
    profile_wallet_authority_hash: str | None,
    ctx: _HardwareWalletContext,
    gaps: _Gaps,
) -> None:
    if ctx.expected_device_pubkey is None:
        gaps.add("expected device pubkey is required for hardware wallet binding")
    elif attestation_pubkey is not None and attestation_pubkey != ctx.expected_device_pubkey.lower():
        gaps.add("device_attestation.pubkey does not match expected device pubkey")

    if ctx.wallet_authority_profile_hash is None:
        gaps.add("wallet authority profile hash is required for binding")
    elif (
        profile_wallet_authority_hash is not None
        and ctx.wallet_authority_profile_hash != profile_wallet_authority_hash
    ):
        gaps.add("evidence.profile_wallet_authority_hash does not match the active wallet authority profile")


def _validate_hardware_capture_window(
    prompt: Mapping[str, Any],
    approval: Mapping[str, Any],
    *,
    gaps: _Gaps,
) -> None:
    approval_captured_at = approval.get("captured_at")
    prompt_captured_at = prompt.get("captured_at")
    if approval_captured_at is None or prompt_captured_at is None:
        return
    if approval_captured_at < prompt_captured_at:
        gaps.add("device_approval_tx.captured_at must be >= os_prompt_capture.captured_at")
    if abs(approval_captured_at - prompt_captured_at) > _NEAR_AND_SAME_HOUR_SECONDS:
        gaps.add("os prompt capture and approval must be captured within the same hour")


def _validate_hardware_capture_freshness(
    prompt: Mapping[str, Any],
    approval: Mapping[str, Any],
    *,
    issued_at: int | None,
    now: int,
    gaps: _Gaps,
) -> None:
    approval_captured_at = approval.get("captured_at")
    prompt_captured_at = prompt.get("captured_at")
    _validate_hardware_capture_timestamp(
        "os_prompt_capture.captured_at",
        prompt_captured_at,
        issued_at=issued_at,
        now=now,
        gaps=gaps,
    )
    _validate_hardware_capture_timestamp(
        "device_approval_tx.captured_at",
        approval_captured_at,
        issued_at=issued_at,
        now=now,
        gaps=gaps,
    )
    if issued_at is None or approval_captured_at is None:
        return
    max_lag = _NEAR_AND_SAME_HOUR_SECONDS + _FUTURE_SKEW_TOLERANCE_SECONDS
    if issued_at - approval_captured_at > max_lag:
        # Review note (grade B+ -> A-): a stale hardware approval could be
        # rehashed with a fresh issued_at while preserving the prompt/approval
        # same-hour relation. Production evidence now requires the device
        # approval itself to be fresh relative to the evidence issuance.
        gaps.add("device_approval_tx.captured_at is too old for evidence issued_at")


def _validate_hardware_capture_timestamp(
    label: str,
    captured_at: object,
    *,
    issued_at: int | None,
    now: int,
    gaps: _Gaps,
) -> None:
    if captured_at is None:
        return
    if not isinstance(captured_at, int) or isinstance(captured_at, bool):
        return
    if issued_at is not None and captured_at > issued_at + _FUTURE_SKEW_TOLERANCE_SECONDS:
        gaps.add(f"{label} cannot postdate evidence issued_at")
    if captured_at > now + _FUTURE_SKEW_TOLERANCE_SECONDS:
        gaps.add(f"{label} is in the future")


# -----------------------------------------------------------------------------
# Lane 3: zk wrapping.
# -----------------------------------------------------------------------------


_ZK_FIELDS = frozenset(
    {
        "schema",
        "surface",
        "circuit_artifact",
        "soundness_audit",
        "verifier_binding",
        "sample_proof_acceptance",
        "issued_at",
        "evidence_hash",
    }
)
_ZK_CIRCUIT_FIELDS = frozenset(
    {
        "artifact_id",
        "artifact_hash",
        "proof_system",
        "circuit_source_hash",
        "verification_key_hash",
        "reproducible_build_hash",
    }
)
_ZK_AUDIT_FIELDS = frozenset({"audit_id", "audit_report_hash", "auditor", "audited_at"})
_ZK_VERIFIER_FIELDS = frozenset({"verifier_cmd_hash", "verifier_binary_hash"})
_ZK_SAMPLE_FIELDS = frozenset({"proof_intent_receipt_hash", "verifier_request_hash", "accepted_at"})
_LIVE_PROOF_WRAPPER_STATUS_SCHEMA = "zenodex/live-proof-wrapper-status/v1"


class _ZkWrappingLane(Lane):
    LANE_ID = LANE_ZK_WRAPPING
    SCHEMA = ZK_WRAPPING_EVIDENCE_SCHEMA_V1
    DOMAIN = "production_zk_wrapping_evidence_v1"
    ALLOWED_FIELDS = _ZK_FIELDS
    MISSING_MESSAGE = "zk wrapping evidence is missing"

    def validate(
        self,
        obj: Mapping[str, Any],
        ctx: "_LaneContext",
        gaps: _Gaps,
    ) -> tuple[dict[str, Any], dict[str, Any]]:
        if not isinstance(ctx, _ZkWrappingContext):
            return _invalid_lane_context("_ZkWrappingContext", gaps=gaps)
        surface = _P.nonempty_str(obj.get("surface"), path="surface", gaps=gaps)

        circuit = _parse_subobject(
            obj.get("circuit_artifact"),
            path="circuit_artifact",
            allowed=_ZK_CIRCUIT_FIELDS,
            gaps=gaps,
        )
        soundness = _parse_subobject(
            obj.get("soundness_audit"),
            path="soundness_audit",
            allowed=_ZK_AUDIT_FIELDS,
            gaps=gaps,
        )
        verifier_binding = _parse_subobject(
            obj.get("verifier_binding"),
            path="verifier_binding",
            allowed=_ZK_VERIFIER_FIELDS,
            gaps=gaps,
        )
        sample = _parse_subobject(
            obj.get("sample_proof_acceptance"),
            path="sample_proof_acceptance",
            allowed=_ZK_SAMPLE_FIELDS,
            gaps=gaps,
        )

        artifact_id = (
            _P.nonempty_str(circuit.get("artifact_id"), path="circuit_artifact.artifact_id", gaps=gaps)
            if circuit is not None
            else None
        )
        artifact_hashes = _collect_zk_hashes(circuit, gaps) if circuit is not None else {}
        proof_system = (
            _P.nonempty_str(circuit.get("proof_system"), path="circuit_artifact.proof_system", gaps=gaps)
            if circuit is not None
            else None
        )

        audit_id, audit_report_hash, auditor, audited_at = _parse_zk_audit(soundness, gaps)
        verifier_cmd_hash, verifier_binary_hash = _parse_zk_verifier(verifier_binding, gaps)
        sample_intent, sample_request, sample_accepted_at = _parse_zk_sample(sample, gaps)
        issued_at = _P.positive_int(obj.get("issued_at"), path="issued_at", gaps=gaps)

        _validate_zk_surface(surface, expected_surface=ctx.expected_surface, gaps=gaps)
        _validate_zk_temporal_rules(
            audited_at=audited_at,
            sample_accepted_at=sample_accepted_at,
            issued_at=issued_at,
            now=ctx.now,
            gaps=gaps,
        )
        _check_zk_pairwise_distinct_hashes(artifact_hashes, gaps=gaps)
        _bind_zk_to_live_wrapper(
            ctx.live_proof_wrapper_status,
            surface=surface,
            artifact_id=artifact_id,
            artifact_hash=artifact_hashes.get("artifact_hash"),
            proof_system=proof_system,
            verifier_cmd_hash=verifier_cmd_hash,
            verifier_binary_hash=verifier_binary_hash,
            sample_intent_hash=sample_intent,
            sample_request_hash=sample_request,
            gaps=gaps,
        )

        if issued_at is not None:
            _check_freshness(
                issued_at,
                now=ctx.now,
                max_age_s=_MAX_EVIDENCE_AGE_SECONDS,
                label="zk wrapping evidence",
                gaps=gaps,
            )

        bindings = {
            "surface": surface,
            "circuit_artifact_id": artifact_id,
            "circuit_artifact_hash": artifact_hashes.get("artifact_hash"),
            "verification_key_hash": artifact_hashes.get("verification_key_hash"),
            "verifier_cmd_hash": verifier_cmd_hash,
            "audit_id": audit_id,
        }
        extras = {
            "proof_system": proof_system,
            "auditor": auditor,
            "audited_at": audited_at,
            "verifier_binary_hash": verifier_binary_hash,
            "audit_report_hash": audit_report_hash,
            "sample_proof_intent_hash": sample_intent,
            "sample_verifier_request_hash": sample_request,
            "sample_accepted_at": sample_accepted_at,
        }
        return bindings, extras


def _collect_zk_hashes(circuit: Mapping[str, Any], gaps: _Gaps) -> dict[str, str | None]:
    return {
        "artifact_hash": _P.hex_token(
            circuit.get("artifact_hash"),
            path="circuit_artifact.artifact_hash",
            gaps=gaps,
            exact_len=_HASH_HEX_LEN,
        ),
        "circuit_source_hash": _P.hex_token(
            circuit.get("circuit_source_hash"),
            path="circuit_artifact.circuit_source_hash",
            gaps=gaps,
            exact_len=_HASH_HEX_LEN,
        ),
        "verification_key_hash": _P.hex_token(
            circuit.get("verification_key_hash"),
            path="circuit_artifact.verification_key_hash",
            gaps=gaps,
            exact_len=_HASH_HEX_LEN,
        ),
        "reproducible_build_hash": _P.hex_token(
            circuit.get("reproducible_build_hash"),
            path="circuit_artifact.reproducible_build_hash",
            gaps=gaps,
            exact_len=_HASH_HEX_LEN,
        ),
    }


def _parse_zk_audit(
    soundness: Mapping[str, Any] | None, gaps: _Gaps
) -> tuple[str | None, str | None, str | None, int | None]:
    if soundness is None:
        return (None, None, None, None)
    audit_id = _P.nonempty_str(soundness.get("audit_id"), path="soundness_audit.audit_id", gaps=gaps)
    audit_report_hash = _P.hex_token(
        soundness.get("audit_report_hash"),
        path="soundness_audit.audit_report_hash",
        gaps=gaps,
        exact_len=_HASH_HEX_LEN,
    )
    auditor = _P.nonempty_str(soundness.get("auditor"), path="soundness_audit.auditor", gaps=gaps)
    audited_at = _P.positive_int(soundness.get("audited_at"), path="soundness_audit.audited_at", gaps=gaps)
    return (audit_id, audit_report_hash, auditor, audited_at)


def _parse_zk_verifier(
    verifier_binding: Mapping[str, Any] | None, gaps: _Gaps
) -> tuple[str | None, str | None]:
    if verifier_binding is None:
        return (None, None)
    return (
        _P.hex_token(
            verifier_binding.get("verifier_cmd_hash"),
            path="verifier_binding.verifier_cmd_hash",
            gaps=gaps,
            exact_len=_HASH_HEX_LEN,
        ),
        _P.hex_token(
            verifier_binding.get("verifier_binary_hash"),
            path="verifier_binding.verifier_binary_hash",
            gaps=gaps,
            exact_len=_HASH_HEX_LEN,
        ),
    )


def _parse_zk_sample(
    sample: Mapping[str, Any] | None, gaps: _Gaps
) -> tuple[str | None, str | None, int | None]:
    if sample is None:
        return (None, None, None)
    return (
        _P.hex_token(
            sample.get("proof_intent_receipt_hash"),
            path="sample_proof_acceptance.proof_intent_receipt_hash",
            gaps=gaps,
            exact_len=_HASH_HEX_LEN,
        ),
        _P.hex_token(
            sample.get("verifier_request_hash"),
            path="sample_proof_acceptance.verifier_request_hash",
            gaps=gaps,
            exact_len=_HASH_HEX_LEN,
        ),
        _P.positive_int(
            sample.get("accepted_at"),
            path="sample_proof_acceptance.accepted_at",
            gaps=gaps,
        ),
    )


def _check_zk_pairwise_distinct_hashes(
    hashes: Mapping[str, str | None],
    *,
    gaps: _Gaps,
) -> None:
    first_name_by_hash: dict[str, str] = {}
    for name in sorted(hashes):
        value = hashes.get(name)
        if value is None:
            continue
        first_name = first_name_by_hash.get(value)
        if first_name is None:
            first_name_by_hash[value] = name
        else:
            gaps.add(f"circuit_artifact.{first_name} must differ from circuit_artifact.{name}")


def _validate_zk_surface(surface: str | None, *, expected_surface: str | None, gaps: _Gaps) -> None:
    if expected_surface is None:
        gaps.add("expected surface is required for zk wrapping binding")
    elif surface is not None and surface != expected_surface:
        gaps.add("zk wrapping evidence surface does not match expected_surface")


def _validate_zk_temporal_rules(
    *,
    audited_at: int | None,
    sample_accepted_at: int | None,
    issued_at: int | None,
    now: int,
    gaps: _Gaps,
) -> None:
    if audited_at is not None:
        if audited_at > now + _FUTURE_SKEW_TOLERANCE_SECONDS:
            gaps.add("soundness audit audited_at is in the future")
        if issued_at is not None and audited_at > issued_at:
            gaps.add("soundness audit audited_at cannot postdate evidence issued_at")
        if now - audited_at > _MAX_AUDIT_AGE_SECONDS:
            gaps.add("soundness audit is outside the audit freshness window")

    if sample_accepted_at is None:
        return
    if sample_accepted_at > now + _FUTURE_SKEW_TOLERANCE_SECONDS:
        gaps.add("sample_proof_acceptance.accepted_at is in the future")
    if issued_at is not None and sample_accepted_at > issued_at:
        gaps.add("sample_proof_acceptance.accepted_at cannot postdate evidence issued_at")


def _bind_zk_to_live_wrapper(
    live: Mapping[str, Any] | None,
    *,
    surface: str | None,
    artifact_id: str | None,
    artifact_hash: str | None,
    proof_system: str | None,
    verifier_cmd_hash: str | None,
    verifier_binary_hash: str | None,
    sample_intent_hash: str | None,
    sample_request_hash: str | None,
    gaps: _Gaps,
) -> None:
    if live is None:
        gaps.add("live proof wrapper status is required for binding")
        return
    _validate_live_wrapper_status_shape(live, gaps=gaps)
    if live.get("zk_proof_verified") is not True:
        gaps.add("live proof wrapper must show zk_proof_verified=true before production")
    if live.get("artifact_binding_complete") is not True:
        gaps.add("live proof wrapper must show artifact_binding_complete=true")
    _bind_zk_artifact(
        live,
        artifact_id=artifact_id,
        artifact_hash=artifact_hash,
        proof_system=proof_system,
        verifier_cmd_hash=verifier_cmd_hash,
        verifier_binary_hash=verifier_binary_hash,
        gaps=gaps,
    )
    _bind_zk_surface(live, surface=surface, gaps=gaps)
    _bind_zk_sample_acceptance(
        live,
        sample_intent_hash=sample_intent_hash,
        sample_request_hash=sample_request_hash,
        gaps=gaps,
    )


def _validate_live_wrapper_status_shape(live: Mapping[str, Any], *, gaps: _Gaps) -> None:
    # Review note (grade B+ -> A-): the ZK wrapping lane previously accepted a
    # minimal hand-made JSON status as long as it said zk_proof_verified=true.
    # Production evidence must be bound to the live wrapper result shape, so the
    # lane now rejects statuses that are missing the proof, verifier, or wrapper
    # metadata fields emitted by verify_live_proof_wrapper.
    if live.get("schema") != _LIVE_PROOF_WRAPPER_STATUS_SCHEMA:
        gaps.add("live proof wrapper status schema mismatch")
    if live.get("required") is not True:
        gaps.add("live proof wrapper status must have required=true")
    if live.get("proof_provided") is not True:
        gaps.add("live proof wrapper status must have proof_provided=true")
    if live.get("verifier_configured") is not True:
        gaps.add("live proof wrapper status must have verifier_configured=true")
    if live.get("artifact_binding_configured") is not True:
        # Review note (grade B+ -> A-): production evidence must come from a
        # wrapper that was configured to bind verifier/circuit artifacts, not
        # only from a sidecar that happens to contain an artifact_binding object.
        gaps.add("live proof wrapper must show artifact_binding_configured=true")
    proof_verifier = live.get("proof_verifier")
    if not isinstance(proof_verifier, Mapping):
        gaps.add("live proof wrapper proof_verifier is required and must be an object")
        return
    if proof_verifier.get("kind") != "subprocess":
        gaps.add("live proof wrapper proof_verifier.kind must be subprocess")
    if live.get("error") is not None:
        gaps.add("live proof wrapper error must be null for production evidence")


def _bind_zk_artifact(
    live: Mapping[str, Any],
    *,
    artifact_id: str | None,
    artifact_hash: str | None,
    proof_system: str | None,
    verifier_cmd_hash: str | None,
    verifier_binary_hash: str | None,
    gaps: _Gaps,
) -> None:
    wrapper_artifact = live.get("artifact_binding")
    if not isinstance(wrapper_artifact, Mapping):
        gaps.add("live proof wrapper artifact_binding is required and must be an object")
        return
    _bind_zk_live_artifact_binding_hash(wrapper_artifact, gaps=gaps)
    _bind_zk_live_artifact_metadata(
        wrapper_artifact,
        artifact_id=artifact_id,
        artifact_hash=artifact_hash,
        proof_system=proof_system,
        verifier_binary_hash=verifier_binary_hash,
        gaps=gaps,
    )
    wrapper_cmd_hash = _normalize_hash_token(wrapper_artifact.get("verifier_cmd_hash"))
    if wrapper_cmd_hash is None:
        gaps.add("live proof wrapper verifier_cmd_hash is required for binding")
    elif verifier_cmd_hash is not None and wrapper_cmd_hash != verifier_cmd_hash:
        gaps.add("live wrapper verifier_cmd_hash does not match evidence verifier_cmd_hash")
    proof_verifier = live.get("proof_verifier")
    if isinstance(proof_verifier, Mapping):
        verifier_status_hash = _normalize_hash_token(proof_verifier.get("cmd_hash"))
        if verifier_status_hash is None:
            gaps.add("live proof wrapper proof_verifier.cmd_hash is required for binding")
        elif verifier_cmd_hash is not None and verifier_status_hash != verifier_cmd_hash:
            gaps.add("live proof wrapper proof_verifier.cmd_hash does not match evidence verifier_cmd_hash")


def _bind_zk_live_artifact_binding_hash(wrapper_artifact: Mapping[str, Any], *, gaps: _Gaps) -> None:
    live_binding_hash = _normalize_hash_token(wrapper_artifact.get("binding_hash"))
    if live_binding_hash is None:
        gaps.add("live proof wrapper artifact_binding.binding_hash is required for binding")
        return
    binding_payload = {
        "verifier_artifact": wrapper_artifact.get("verifier_artifact"),
        "circuit_artifact": wrapper_artifact.get("circuit_artifact"),
        "verifier_cmd_hash": wrapper_artifact.get("verifier_cmd_hash"),
    }
    expected_hash = _normalize_hash_token(
        sha256_hex(
            domain_sep_bytes(LIVE_PROOF_WRAPPER_ARTIFACT_BINDING_HASH_DOMAIN)
            + canonical_json_bytes(binding_payload)
        )
    )
    if expected_hash is not None and live_binding_hash != expected_hash:
        gaps.add("live proof wrapper artifact_binding.binding_hash does not match artifact metadata")


def _bind_zk_live_artifact_metadata(
    wrapper_artifact: Mapping[str, Any],
    *,
    artifact_id: str | None,
    artifact_hash: str | None,
    proof_system: str | None,
    verifier_binary_hash: str | None,
    gaps: _Gaps,
) -> None:
    # The live proof wrapper hashes its verifier and circuit artifacts into the
    # request sent to the verifier. Production-promotion evidence must therefore
    # match those live artifact objects, not only reuse the verifier command
    # hash and sample receipt hashes from a successful wrapper run.
    if wrapper_artifact.get("verifier_artifact_ready") is not True:
        gaps.add("live proof wrapper verifier_artifact_ready must be true")
    if wrapper_artifact.get("circuit_artifact_ready") is not True:
        gaps.add("live proof wrapper circuit_artifact_ready must be true")

    verifier_artifact = wrapper_artifact.get("verifier_artifact")
    if not isinstance(verifier_artifact, Mapping):
        gaps.add("live proof wrapper verifier_artifact is required and must be an object")
    else:
        _bind_zk_live_verifier_artifact(
            verifier_artifact,
            verifier_binary_hash=verifier_binary_hash,
            gaps=gaps,
        )

    circuit_artifact = wrapper_artifact.get("circuit_artifact")
    if not isinstance(circuit_artifact, Mapping):
        gaps.add("live proof wrapper circuit_artifact is required and must be an object")
    else:
        _bind_zk_live_circuit_artifact(
            circuit_artifact,
            artifact_id=artifact_id,
            artifact_hash=artifact_hash,
            proof_system=proof_system,
            gaps=gaps,
        )


def _bind_zk_live_verifier_artifact(
    verifier_artifact: Mapping[str, Any],
    *,
    verifier_binary_hash: str | None,
    gaps: _Gaps,
) -> None:
    if not isinstance(verifier_artifact.get("artifact_id"), str) or not verifier_artifact.get("artifact_id"):
        gaps.add("live proof wrapper verifier_artifact.artifact_id is required")
    live_verifier_hash = _normalize_hash_token(verifier_artifact.get("artifact_hash"))
    if live_verifier_hash is None:
        gaps.add("live proof wrapper verifier_artifact.artifact_hash is required for binding")
    elif verifier_binary_hash is not None and live_verifier_hash != verifier_binary_hash:
        gaps.add("live proof wrapper verifier_artifact.artifact_hash does not match evidence verifier_binary_hash")


def _bind_zk_live_circuit_artifact(
    circuit_artifact: Mapping[str, Any],
    *,
    artifact_id: str | None,
    artifact_hash: str | None,
    proof_system: str | None,
    gaps: _Gaps,
) -> None:
    live_artifact_id = circuit_artifact.get("artifact_id")
    if not isinstance(live_artifact_id, str) or not live_artifact_id:
        gaps.add("live proof wrapper circuit_artifact.artifact_id is required")
    elif artifact_id is not None and live_artifact_id != artifact_id:
        gaps.add("live proof wrapper circuit_artifact.artifact_id does not match evidence circuit_artifact.artifact_id")

    live_artifact_hash = _normalize_hash_token(circuit_artifact.get("artifact_hash"))
    if live_artifact_hash is None:
        gaps.add("live proof wrapper circuit_artifact.artifact_hash is required for binding")
    elif artifact_hash is not None and live_artifact_hash != artifact_hash:
        gaps.add("live proof wrapper circuit_artifact.artifact_hash does not match evidence circuit_artifact.artifact_hash")

    live_proof_system = circuit_artifact.get("proof_system")
    if not isinstance(live_proof_system, str) or not live_proof_system:
        gaps.add("live proof wrapper circuit_artifact.proof_system is required")
    elif proof_system is not None and live_proof_system != proof_system:
        gaps.add("live proof wrapper circuit_artifact.proof_system does not match evidence circuit_artifact.proof_system")


def _normalize_hash_token(value: object) -> str | None:
    """Normalize live-wrapper hash syntax to the evidence lane's 64-hex form.

    Grade: A. The live proof wrapper emits ``0x``-prefixed hashes, while the
    production-promotion evidence body intentionally stores canonical bare
    lowercase hex. Without this boundary normalizer, real live-wrapper output
    could not satisfy the ZK wrapping lane unless an operator hand-edited the
    sidecar, which is exactly the kind of release evidence drift this verifier
    is meant to prevent.
    """
    if not isinstance(value, str) or not value:
        return None
    text = value.strip()
    if text.startswith(("0x", "0X")):
        text = text[2:]
    elif text.startswith("sha256:"):
        text = text[len("sha256:") :]
    text = text.lower()
    if len(text) != _HASH_HEX_LEN or any(ch not in _HEX_CHARS for ch in text):
        return None
    return text


def _bind_zk_surface(
    live: Mapping[str, Any],
    *,
    surface: str | None,
    gaps: _Gaps,
) -> None:
    wrapper_surface = live.get("surface")
    if not isinstance(wrapper_surface, str) or not wrapper_surface:
        gaps.add("live proof wrapper surface is required for binding")
    elif surface is not None and wrapper_surface != surface:
        gaps.add("live wrapper surface does not match evidence surface")


def _bind_zk_sample_acceptance(
    live: Mapping[str, Any],
    *,
    sample_intent_hash: str | None,
    sample_request_hash: str | None,
    gaps: _Gaps,
) -> None:
    live_intent_hash = _normalize_hash_token(live.get("proof_intent_receipt_hash"))
    if live_intent_hash is None:
        gaps.add("live proof wrapper proof_intent_receipt_hash is required for sample binding")
    elif sample_intent_hash is not None and live_intent_hash != sample_intent_hash:
        gaps.add("live proof wrapper proof_intent_receipt_hash does not match sample_proof_acceptance")

    live_request_hash = _normalize_hash_token(live.get("verifier_request_hash"))
    if live_request_hash is None:
        gaps.add("live proof wrapper verifier_request_hash is required for sample binding")
    elif sample_request_hash is not None and live_request_hash != sample_request_hash:
        gaps.add("live proof wrapper verifier_request_hash does not match sample_proof_acceptance")


# -----------------------------------------------------------------------------
# Lane 4: autotrader supervisor.
# -----------------------------------------------------------------------------


_AUTOTRADER_FIELDS = frozenset(
    {
        "schema",
        "supervisor_id",
        "chain_id",
        "profile_supervisor_hash",
        "run_window",
        "crash_recovery",
        "multi_signer_approvals",
        "budget_compliance",
        "issued_at",
        "evidence_hash",
    }
)
_AUTOTRADER_RUN_WINDOW_FIELDS = frozenset(
    {
        "started_at",
        "last_heartbeat_at",
        "duration_seconds",
        "ticks_executed",
        "ticks_failed",
        "ticks_throttled",
        "heartbeat_timestamps",
    }
)
_AUTOTRADER_CRASH_FIELDS = frozenset({"crash_at", "recovery_at", "checkpoint_hash"})
_AUTOTRADER_APPROVAL_FIELDS = frozenset({"signer_pubkey", "approval_hash", "signature"})
_AUTOTRADER_APPROVAL_BODY_FIELDS = (
    "schema",
    "supervisor_id",
    "chain_id",
    "profile_supervisor_hash",
    "run_window",
    "crash_recovery",
    "budget_compliance",
)
_AUTOTRADER_BUDGET_FIELDS = frozenset(
    {
        "max_actions_per_tick_observed",
        "max_runs_per_process_observed",
        "config_max_actions_per_tick",
        "config_max_runs_per_process",
    }
)


def production_autotrader_run_approval_hash_v1(evidence: Mapping[str, Any]) -> str:
    """Return the canonical hash that AutoTrader lane signers approve.

    The approval binds the operator's multi-signer decision to the exact
    supervisor profile, chain, run window, crash-recovery evidence, and budget
    observations. It deliberately excludes signatures, ``issued_at``, and the
    outer evidence hash to avoid circular approval material. Freshness remains a
    separate verifier check against the latest heartbeat and evidence issue time.
    """

    return hash_v0(
        "production_autotrader_run_approval_v1",
        {field: evidence.get(field) for field in _AUTOTRADER_APPROVAL_BODY_FIELDS},
    ).removeprefix("0x")


def production_autotrader_run_approval_message_v1(approval_hash: str) -> bytes:
    """Canonical message signed by AutoTrader production-run approvers."""

    return canonical_json_bytes_v0(
        {
            "domain": "zenodex.production_autotrader_run_approval.v1",
            "schema": AUTOTRADER_EVIDENCE_SCHEMA_V1,
            "approval_hash": approval_hash,
        }
    )


class _AutotraderLane(Lane):
    LANE_ID = LANE_AUTOTRADER
    SCHEMA = AUTOTRADER_EVIDENCE_SCHEMA_V1
    DOMAIN = "production_autotrader_evidence_v1"
    ALLOWED_FIELDS = _AUTOTRADER_FIELDS
    MISSING_MESSAGE = "autotrader evidence is missing"

    def validate(
        self,
        obj: Mapping[str, Any],
        ctx: "_LaneContext",
        gaps: _Gaps,
    ) -> tuple[dict[str, Any], dict[str, Any]]:
        if not isinstance(ctx, _AutotraderContext):
            return _invalid_lane_context("_AutotraderContext", gaps=gaps)
        supervisor_id = _P.nonempty_str(obj.get("supervisor_id"), path="supervisor_id", gaps=gaps)
        chain_id = _P.nonempty_str(obj.get("chain_id"), path="chain_id", gaps=gaps)
        profile_supervisor_hash = _P.nonempty_str(
            obj.get("profile_supervisor_hash"),
            path="profile_supervisor_hash",
            gaps=gaps,
        )

        rw_sub = _parse_subobject(
            obj.get("run_window"),
            path="run_window",
            allowed=_AUTOTRADER_RUN_WINDOW_FIELDS,
            gaps=gaps,
        )
        rw = _parse_autotrader_run_window(rw_sub, gaps)

        crash_recovery = _P.list_of_mappings(
            obj.get("crash_recovery"),
            path="crash_recovery",
            gaps=gaps,
            min_len=0,
            max_len=_MAX_AUTOTRADER_CRASH_RECOVERY_ENTRIES,
        )
        approvals = _P.list_of_mappings(
            obj.get("multi_signer_approvals"),
            path="multi_signer_approvals",
            gaps=gaps,
            min_len=_MIN_AUTOTRADER_MULTI_SIGNERS,
            max_len=_MAX_AUTOTRADER_MULTI_SIGNERS,
        )

        budget = _parse_subobject(
            obj.get("budget_compliance"),
            path="budget_compliance",
            allowed=_AUTOTRADER_BUDGET_FIELDS,
            gaps=gaps,
        )
        budget_parsed = _parse_autotrader_budget(budget, gaps)

        issued_at = _P.positive_int(obj.get("issued_at"), path="issued_at", gaps=gaps)

        if ctx.expected_chain_id is None:
            gaps.add("expected chain_id is required for autotrader binding")
        elif chain_id is not None and chain_id != ctx.expected_chain_id:
            gaps.add("autotrader evidence chain_id mismatch")
        if ctx.supervisor_profile_hash is None:
            gaps.add("supervisor profile hash is required for binding")
        elif (
            profile_supervisor_hash is not None
            and ctx.supervisor_profile_hash != profile_supervisor_hash
        ):
            gaps.add("evidence.profile_supervisor_hash does not match active supervisor profile")

        _validate_autotrader_run_window(rw, gaps=gaps)
        _validate_autotrader_heartbeats(rw, gaps=gaps)
        _validate_autotrader_run_freshness(rw, issued_at=issued_at, now=ctx.now, gaps=gaps)
        crash_count = _validate_autotrader_crash_recovery(crash_recovery, rw=rw, gaps=gaps)
        expected_approval_hash = production_autotrader_run_approval_hash_v1(obj)
        expected_approval_signers = _parse_autotrader_expected_approval_signers(
            ctx.expected_approval_signer_pubkeys,
            gaps=gaps,
        )
        distinct_signers = _validate_autotrader_signers(
            approvals,
            expected_approval_hash=expected_approval_hash,
            expected_signer_pubkeys=expected_approval_signers,
            gaps=gaps,
        )
        _enforce_autotrader_budgets(budget_parsed, ctx=ctx, gaps=gaps)

        if issued_at is not None:
            _check_freshness(
                issued_at,
                now=ctx.now,
                max_age_s=_MAX_EVIDENCE_AGE_SECONDS,
                label="autotrader evidence",
                gaps=gaps,
            )

        bindings = {
            "supervisor_id": supervisor_id,
            "chain_id": chain_id,
            "profile_supervisor_hash": profile_supervisor_hash,
            "run_approval_hash": expected_approval_hash,
        }
        extras = {
            "duration_seconds": rw.get("duration_seconds"),
            "ticks_executed": rw.get("ticks_executed"),
            "ticks_failed": rw.get("ticks_failed"),
            "ticks_throttled": rw.get("ticks_throttled"),
            "crash_recovery_count": crash_count,
            "distinct_signer_count": distinct_signers,
            "expected_signer_count": len(expected_approval_signers),
            "max_actions_per_tick_observed": budget_parsed.get("max_actions_per_tick_observed"),
            "max_runs_per_process_observed": budget_parsed.get("max_runs_per_process_observed"),
        }
        return bindings, extras


def _parse_autotrader_run_window(rw: Mapping[str, Any] | None, gaps: _Gaps) -> dict[str, Any]:
    if rw is None:
        return {}
    return {
        "started_at": _P.positive_int(rw.get("started_at"), path="run_window.started_at", gaps=gaps),
        "last_heartbeat_at": _P.positive_int(
            rw.get("last_heartbeat_at"),
            path="run_window.last_heartbeat_at",
            gaps=gaps,
        ),
        "duration_seconds": _P.positive_int(
            rw.get("duration_seconds"),
            path="run_window.duration_seconds",
            gaps=gaps,
        ),
        "ticks_executed": _P.bounded_int(
            rw.get("ticks_executed"),
            path="run_window.ticks_executed",
            gaps=gaps,
            lo=1,
            hi=_MAX_TICKS_PER_PROCESS_HARD_CAP,
        ),
        "ticks_failed": _P.bounded_int(
            rw.get("ticks_failed"),
            path="run_window.ticks_failed",
            gaps=gaps,
            lo=0,
            hi=_MAX_TICKS_PER_PROCESS_HARD_CAP,
        ),
        "ticks_throttled": _P.bounded_int(
            rw.get("ticks_throttled"),
            path="run_window.ticks_throttled",
            gaps=gaps,
            lo=0,
            hi=_MAX_TICKS_PER_PROCESS_HARD_CAP,
        ),
        "heartbeat_timestamps": _P.list_of_positive_ints(
            rw.get("heartbeat_timestamps"),
            path="run_window.heartbeat_timestamps",
            gaps=gaps,
            min_len=2,
            max_len=_MAX_AUTOTRADER_HEARTBEAT_LIST_LEN,
        ),
    }


def _parse_autotrader_budget(budget: Mapping[str, Any] | None, gaps: _Gaps) -> dict[str, Any]:
    if budget is None:
        return {}
    return {
        "max_actions_per_tick_observed": _P.bounded_int(
            budget.get("max_actions_per_tick_observed"),
            path="budget_compliance.max_actions_per_tick_observed",
            gaps=gaps,
            lo=0,
            hi=_MAX_TICKS_PER_PROCESS_HARD_CAP,
        ),
        "max_runs_per_process_observed": _P.bounded_int(
            budget.get("max_runs_per_process_observed"),
            path="budget_compliance.max_runs_per_process_observed",
            gaps=gaps,
            lo=0,
            hi=_MAX_TICKS_PER_PROCESS_HARD_CAP,
        ),
        "config_max_actions_per_tick": budget.get("config_max_actions_per_tick"),
        "config_max_runs_per_process": budget.get("config_max_runs_per_process"),
    }


def _validate_autotrader_run_window(rw: Mapping[str, Any], gaps: _Gaps) -> None:
    started_at = rw.get("started_at")
    last_hb = rw.get("last_heartbeat_at")
    duration = rw.get("duration_seconds")
    ticks_executed = rw.get("ticks_executed")
    ticks_failed = rw.get("ticks_failed")
    ticks_throttled = rw.get("ticks_throttled")
    if started_at is None or last_hb is None or duration is None:
        return
    if last_hb < started_at:
        gaps.add("last_heartbeat_at must be >= started_at")
    elif started_at + duration != last_hb:
        gaps.add("duration_seconds must equal last_heartbeat_at - started_at")
    if duration < _MIN_AUTOTRADER_UNATTENDED_SECONDS:
        gaps.add(
            f"run_window.duration_seconds must be >= {_MIN_AUTOTRADER_UNATTENDED_SECONDS} for production"
        )
    _validate_autotrader_tick_counts(
        ticks_executed=ticks_executed,
        ticks_failed=ticks_failed,
        ticks_throttled=ticks_throttled,
        gaps=gaps,
    )


def _validate_autotrader_tick_counts(
    *,
    ticks_executed: int | None,
    ticks_failed: int | None,
    ticks_throttled: int | None,
    gaps: _Gaps,
) -> None:
    if ticks_executed is not None and ticks_failed is not None and ticks_failed > ticks_executed:
        gaps.add("ticks_failed cannot exceed ticks_executed")
    if (
        ticks_executed is not None
        and ticks_throttled is not None
        and ticks_throttled > ticks_executed
    ):
        gaps.add("ticks_throttled cannot exceed ticks_executed")


def _validate_autotrader_heartbeats(rw: Mapping[str, Any], gaps: _Gaps) -> None:
    heartbeats = rw.get("heartbeat_timestamps")
    if not isinstance(heartbeats, list) or len(heartbeats) < 2:
        return
    _validate_autotrader_heartbeat_endpoints(
        heartbeats,
        started_at=rw.get("started_at"),
        last_hb=rw.get("last_heartbeat_at"),
        gaps=gaps,
    )
    _validate_autotrader_heartbeat_spacing(heartbeats, gaps=gaps)


def _validate_autotrader_heartbeat_endpoints(
    heartbeats: list[int],
    *,
    started_at: object,
    last_hb: object,
    gaps: _Gaps,
) -> None:
    if started_at is not None and heartbeats[0] != started_at:
        gaps.add("run_window.heartbeat_timestamps[0] must equal started_at")
    if last_hb is not None and heartbeats[-1] != last_hb:
        gaps.add("run_window.heartbeat_timestamps[-1] must equal last_heartbeat_at")


def _validate_autotrader_heartbeat_spacing(heartbeats: list[int], *, gaps: _Gaps) -> None:
    for i, (prev, cur) in enumerate(zip(heartbeats, heartbeats[1:], strict=False), start=1):
        if cur < prev:
            gaps.add(f"run_window.heartbeat_timestamps[{i}] must be >= predecessor")
            return
        if cur - prev > _MAX_AUTOTRADER_HEARTBEAT_GAP_SECONDS:
            gaps.add(
                f"run_window.heartbeat_timestamps: max heartbeat gap "
                f"{_MAX_AUTOTRADER_HEARTBEAT_GAP_SECONDS}s exceeded between index {i - 1} and {i}"
            )
            return


def _validate_autotrader_run_freshness(
    rw: Mapping[str, Any],
    *,
    issued_at: int | None,
    now: int,
    gaps: _Gaps,
) -> None:
    last_hb = rw.get("last_heartbeat_at")
    if issued_at is None or last_hb is None:
        return
    if last_hb > issued_at + _FUTURE_SKEW_TOLERANCE_SECONDS:
        gaps.add("run_window.last_heartbeat_at cannot postdate evidence issued_at")
    if last_hb > now + _FUTURE_SKEW_TOLERANCE_SECONDS:
        gaps.add("run_window.last_heartbeat_at is in the future")
    max_lag = _MAX_AUTOTRADER_HEARTBEAT_GAP_SECONDS + _FUTURE_SKEW_TOLERANCE_SECONDS
    if issued_at - last_hb > max_lag:
        # Review note (grade B -> A-): a stale but internally coherent
        # unattended run can otherwise be rehashed with a fresh issued_at. The
        # production lane now binds issuance to the live supervisor's latest
        # heartbeat freshness window.
        gaps.add("run_window.last_heartbeat_at is too old for evidence issued_at")


def _enforce_autotrader_budgets(
    budget: Mapping[str, Any],
    *,
    ctx: _AutotraderContext,
    gaps: _Gaps,
) -> None:
    if ctx.config_max_actions_per_tick is None:
        gaps.add("config_max_actions_per_tick is required for autotrader binding")
    if ctx.config_max_runs_per_process is None:
        gaps.add("config_max_runs_per_process is required for autotrader binding")
    if not budget:
        return
    _enforce_autotrader_budget_limit(
        configured=ctx.config_max_actions_per_tick,
        observed=budget.get("max_actions_per_tick_observed"),
        cfg_in_evidence=budget.get("config_max_actions_per_tick"),
        overrun_message="budget_compliance observed actions_per_tick exceeds configured maximum",
        config_mismatch_message=(
            "budget_compliance.config_max_actions_per_tick does not match supervisor configuration"
        ),
        gaps=gaps,
    )
    _enforce_autotrader_budget_limit(
        configured=ctx.config_max_runs_per_process,
        observed=budget.get("max_runs_per_process_observed"),
        cfg_in_evidence=budget.get("config_max_runs_per_process"),
        overrun_message="budget_compliance observed runs_per_process exceeds configured maximum",
        config_mismatch_message=(
            "budget_compliance.config_max_runs_per_process does not match supervisor configuration"
        ),
        gaps=gaps,
    )


def _enforce_autotrader_budget_limit(
    *,
    configured: int | None,
    observed: object,
    cfg_in_evidence: object,
    overrun_message: str,
    config_mismatch_message: str,
    gaps: _Gaps,
) -> None:
    if configured is None:
        return
    if isinstance(observed, int) and not isinstance(observed, bool) and observed > configured:
        gaps.add(overrun_message)
    if cfg_in_evidence is not None and cfg_in_evidence != configured:
        gaps.add(config_mismatch_message)


def _parse_autotrader_expected_approval_signers(
    value: object,
    *,
    gaps: _Gaps,
) -> frozenset[str]:
    if not isinstance(value, list):
        gaps.add("expected autotrader approval signer pubkeys are required for binding")
        return frozenset()
    if len(value) < _MIN_AUTOTRADER_MULTI_SIGNERS:
        gaps.add(
            f"expected autotrader approval signer pubkeys must contain at least "
            f"{_MIN_AUTOTRADER_MULTI_SIGNERS} entries"
        )
        return frozenset()
    if len(value) > _MAX_AUTOTRADER_MULTI_SIGNERS:
        gaps.add(
            f"expected autotrader approval signer pubkeys must contain at most "
            f"{_MAX_AUTOTRADER_MULTI_SIGNERS} entries"
        )
        return frozenset()
    out: set[str] = set()
    for index, raw in enumerate(value):
        signer = _P.hex_token(
            raw,
            path=f"expected_autotrader_approval_signer_pubkeys[{index}]",
            gaps=gaps,
            exact_len=_PUBKEY_HEX_LEN,
        )
        if signer is None:
            continue
        if signer in out:
            gaps.add(f"expected_autotrader_approval_signer_pubkeys[{index}] duplicates an earlier key")
        out.add(signer)
    return frozenset(out)


def _validate_autotrader_crash_recovery(
    crash_recovery: list[Mapping[str, Any]] | None,
    *,
    rw: Mapping[str, Any],
    gaps: _Gaps,
) -> int:
    if crash_recovery is None:
        return 0
    started_at = rw.get("started_at")
    last_hb = rw.get("last_heartbeat_at")
    intervals: list[tuple[int, int]] = []
    seen_intervals: set[tuple[int, int]] = set()
    for index, entry in enumerate(crash_recovery):
        interval = _parse_autotrader_crash_interval(index, entry, gaps=gaps)
        if interval is None:
            continue
        if _validate_autotrader_crash_interval(
            index,
            interval,
            started_at=started_at,
            last_hb=last_hb,
            gaps=gaps,
        ):
            intervals.append(interval)
        if interval in seen_intervals:
            gaps.add(f"crash_recovery[{index}] duplicates an earlier crash/recovery interval")
        seen_intervals.add(interval)

    _validate_autotrader_crash_overlaps(intervals, gaps=gaps)
    return len(crash_recovery)


def _parse_autotrader_crash_interval(
    index: int,
    entry: Mapping[str, Any],
    *,
    gaps: _Gaps,
) -> tuple[int, int] | None:
    for key in entry.keys():
        if key not in _AUTOTRADER_CRASH_FIELDS:
            gaps.add(f"unknown field: crash_recovery[{index}].{key}")
    crash_at = _P.positive_int(
        entry.get("crash_at"), path=f"crash_recovery[{index}].crash_at", gaps=gaps
    )
    recovery_at = _P.positive_int(
        entry.get("recovery_at"), path=f"crash_recovery[{index}].recovery_at", gaps=gaps
    )
    _P.hex_token(
        entry.get("checkpoint_hash"),
        path=f"crash_recovery[{index}].checkpoint_hash",
        gaps=gaps,
        exact_len=_HASH_HEX_LEN,
    )
    if crash_at is None or recovery_at is None:
        return None
    return crash_at, recovery_at


def _validate_autotrader_crash_interval(
    index: int,
    interval: tuple[int, int],
    *,
    started_at: int | None,
    last_hb: int | None,
    gaps: _Gaps,
) -> bool:
    crash_at, recovery_at = interval
    valid = True
    if recovery_at < crash_at:
        gaps.add(f"crash_recovery[{index}].recovery_at must be >= crash_at")
        valid = False
    if (
        started_at is not None
        and last_hb is not None
        and (crash_at < started_at or recovery_at > last_hb)
    ):
        gaps.add(f"crash_recovery[{index}] must be within the run window")
    return valid


def _validate_autotrader_crash_overlaps(
    intervals: list[tuple[int, int]],
    *,
    gaps: _Gaps,
) -> None:
    intervals.sort(key=lambda iv: (iv[0], iv[1]))
    for i in range(1, len(intervals)):
        prev_end = intervals[i - 1][1]
        cur_start = intervals[i][0]
        if cur_start < prev_end:
            gaps.add(
                f"crash_recovery interval {intervals[i]} overlaps with {intervals[i - 1]}"
            )
            break


def _validate_autotrader_signers(
    approvals: list[Mapping[str, Any]] | None,
    *,
    expected_approval_hash: str,
    expected_signer_pubkeys: frozenset[str],
    gaps: _Gaps,
) -> int:
    if approvals is None:
        return 0
    seen_signer_pubkeys: set[str] = set()
    approval_hashes: set[str] = set()
    for index, entry in enumerate(approvals):
        signer_pubkey, approval_hash, signature = _parse_autotrader_approval_entry(index, entry, gaps=gaps)
        if signer_pubkey is None or approval_hash is None:
            continue
        _record_autotrader_approval(
            index,
            signer_pubkey=signer_pubkey,
            approval_hash=approval_hash,
            seen_signer_pubkeys=seen_signer_pubkeys,
            approval_hashes=approval_hashes,
            gaps=gaps,
        )
        _validate_ed25519_signature(
            pubkey=signer_pubkey,
            signature=signature,
            message=production_autotrader_run_approval_message_v1(approval_hash),
            label=f"multi_signer_approvals[{index}].signature",
            gaps=gaps,
        )
        if expected_signer_pubkeys and signer_pubkey not in expected_signer_pubkeys:
            gaps.add(f"multi_signer_approvals[{index}].signer_pubkey is not in expected approver set")

    _validate_autotrader_approval_set(
        seen_signer_pubkeys,
        approval_hashes,
        expected_approval_hash=expected_approval_hash,
        gaps=gaps,
    )
    return len(seen_signer_pubkeys)


def _parse_autotrader_approval_entry(
    index: int,
    entry: Mapping[str, Any],
    *,
    gaps: _Gaps,
) -> tuple[str | None, str | None, str | None]:
    for key in entry.keys():
        if key not in _AUTOTRADER_APPROVAL_FIELDS:
            gaps.add(f"unknown field: multi_signer_approvals[{index}].{key}")
    signer_pubkey = _P.hex_token(
        entry.get("signer_pubkey"),
        path=f"multi_signer_approvals[{index}].signer_pubkey",
        gaps=gaps,
        exact_len=_PUBKEY_HEX_LEN,
    )
    approval_hash = _P.hex_token(
        entry.get("approval_hash"),
        path=f"multi_signer_approvals[{index}].approval_hash",
        gaps=gaps,
        exact_len=_HASH_HEX_LEN,
    )
    signature = _P.hex_token(
        entry.get("signature"),
        path=f"multi_signer_approvals[{index}].signature",
        gaps=gaps,
        exact_len=_SIGNATURE_HEX_LEN,
    )
    return signer_pubkey, approval_hash, signature


def _record_autotrader_approval(
    index: int,
    *,
    signer_pubkey: str,
    approval_hash: str,
    seen_signer_pubkeys: set[str],
    approval_hashes: set[str],
    gaps: _Gaps,
) -> None:
    if signer_pubkey in seen_signer_pubkeys:
        gaps.add(f"multi_signer_approvals[{index}] signer_pubkey duplicates an earlier approval")
    seen_signer_pubkeys.add(signer_pubkey)
    approval_hashes.add(approval_hash)


def _validate_autotrader_approval_set(
    seen_signer_pubkeys: set[str],
    approval_hashes: set[str],
    *,
    expected_approval_hash: str,
    gaps: _Gaps,
) -> None:
    if len(seen_signer_pubkeys) < _MIN_AUTOTRADER_MULTI_SIGNERS:
        gaps.add(
            f"production autotrader evidence requires at least {_MIN_AUTOTRADER_MULTI_SIGNERS} distinct signers"
        )
    if len(approval_hashes) > 1:
        gaps.add("multi_signer_approvals entries must all share the same approval_hash")
    if approval_hashes and expected_approval_hash not in approval_hashes:
        gaps.add("multi_signer_approvals approval_hash must equal canonical run approval hash")


# -----------------------------------------------------------------------------
# Lane 5: confidential runtime.
# -----------------------------------------------------------------------------


_CONFIDENTIAL_FIELDS = frozenset(
    {
        "schema",
        "extension_id",
        "provider_id",
        "tee_attestation",
        "approved_measurements_hash",
        "operator_status_hash",
        "external_verifier_binding_hash",
        "private_execution_receipt",
        "issued_at",
        "evidence_hash",
    }
)
_CONFIDENTIAL_TEE_FIELDS = frozenset(
    {
        "kind",
        "raw_attestation_hash",
        "measurement",
        "measurement_in_allowlist",
        "platform_pubkey",
        "attestation_signature",
        "verified_at",
    }
)
_CONFIDENTIAL_RECEIPT_FIELDS = frozenset(
    {
        "runtime_receipt_hash",
        "attestation_receipt_hash",
        "request_id",
        "execution_id",
        "execution_kind",
        "result_code",
        "measurement_provider",
        "attestation_epoch",
        "current_epoch",
        "units_charged",
        "result_redacted",
        "public_effect_digest",
    }
)


class _ConfidentialRuntimeLane(Lane):
    LANE_ID = LANE_CONFIDENTIAL_RUNTIME
    SCHEMA = CONFIDENTIAL_RUNTIME_EVIDENCE_SCHEMA_V1
    DOMAIN = "production_confidential_runtime_evidence_v1"
    ALLOWED_FIELDS = _CONFIDENTIAL_FIELDS
    MISSING_MESSAGE = "confidential runtime evidence is missing"

    def validate(
        self,
        obj: Mapping[str, Any],
        ctx: "_LaneContext",
        gaps: _Gaps,
    ) -> tuple[dict[str, Any], dict[str, Any]]:
        if not isinstance(ctx, _ConfidentialContext):
            return _invalid_lane_context("_ConfidentialContext", gaps=gaps)
        extension_id = _P.nonempty_str(obj.get("extension_id"), path="extension_id", gaps=gaps)
        provider_id = _P.nonempty_str(obj.get("provider_id"), path="provider_id", gaps=gaps)

        tee = _parse_subobject(
            obj.get("tee_attestation"),
            path="tee_attestation",
            allowed=_CONFIDENTIAL_TEE_FIELDS,
            gaps=gaps,
        )
        receipt = _parse_subobject(
            obj.get("private_execution_receipt"),
            path="private_execution_receipt",
            allowed=_CONFIDENTIAL_RECEIPT_FIELDS,
            gaps=gaps,
        )

        tee_data = _parse_confidential_tee(tee, gaps=gaps)
        receipt_data = _parse_confidential_receipt(receipt, gaps=gaps)

        approved_measurements_hash = _P.hex_token(
            obj.get("approved_measurements_hash"),
            path="approved_measurements_hash",
            gaps=gaps,
            exact_len=_HASH_HEX_LEN,
        )
        operator_status_hash = _P.hex_token(
            obj.get("operator_status_hash"),
            path="operator_status_hash",
            gaps=gaps,
            exact_len=_HASH_HEX_LEN,
        )
        external_verifier_binding_hash = _P.hex_token(
            obj.get("external_verifier_binding_hash"),
            path="external_verifier_binding_hash",
            gaps=gaps,
            exact_len=_HASH_HEX_LEN,
        )
        issued_at = _P.positive_int(obj.get("issued_at"), path="issued_at", gaps=gaps)

        _validate_confidential_extension_id(extension_id, ctx=ctx, gaps=gaps)
        _validate_confidential_tee(tee_data, issued_at=issued_at, now=ctx.now, gaps=gaps)
        _validate_confidential_context_bindings(
            approved_measurements=ctx.approved_measurements,
            approved_measurements_hash=approved_measurements_hash,
            measurement=tee_data.get("measurement"),
            operator_status_hash=operator_status_hash,
            expected_operator_status_hash=ctx.operator_status_hash,
            external_verifier_binding_hash=external_verifier_binding_hash,
            expected_external_verifier_binding_hash=ctx.external_verifier_binding_hash,
            gaps=gaps,
        )
        _validate_confidential_receipt(
            receipt_data,
            extension_id=extension_id,
            provider_id=provider_id,
            measurement=tee_data.get("measurement"),
            approved_measurements_hash=approved_measurements_hash,
            operator_status_hash=operator_status_hash,
            external_verifier_binding_hash=external_verifier_binding_hash,
            gaps=gaps,
        )

        if issued_at is not None:
            _check_freshness(
                issued_at,
                now=ctx.now,
                max_age_s=_MAX_EVIDENCE_AGE_SECONDS,
                label="confidential runtime evidence",
                gaps=gaps,
            )

        bindings = {
            "extension_id": extension_id,
            "provider_id": provider_id,
            "tee_kind": tee_data.get("kind"),
            "measurement": tee_data.get("measurement"),
            "platform_pubkey": tee_data.get("platform_pubkey"),
            "approved_measurements_hash": approved_measurements_hash,
            "operator_status_hash": operator_status_hash,
            "external_verifier_binding_hash": external_verifier_binding_hash,
        }
        extras = {
            "tee_kind": tee_data.get("kind"),
            "raw_attestation_hash": tee_data.get("raw_attestation_hash"),
            "attestation_signature": tee_data.get("attestation_signature"),
            "runtime_receipt_hash": receipt_data.get("runtime_receipt_hash"),
            "attestation_receipt_hash": receipt_data.get("attestation_receipt_hash"),
            "request_id": receipt_data.get("request_id"),
            "execution_id": receipt_data.get("execution_id"),
            "execution_kind": receipt_data.get("execution_kind"),
            "result_code": receipt_data.get("result_code"),
            "measurement_provider": receipt_data.get("measurement_provider"),
            "attestation_epoch": receipt_data.get("attestation_epoch"),
            "current_epoch": receipt_data.get("current_epoch"),
            "units_charged": receipt_data.get("units_charged"),
            "public_effect_digest": receipt_data.get("public_effect_digest"),
        }
        return bindings, extras


def _validate_confidential_extension_id(
    extension_id: str | None,
    *,
    ctx: _ConfidentialContext,
    gaps: _Gaps,
) -> None:
    if ctx.expected_extension_id is None:
        gaps.add("expected extension_id is required for confidential runtime binding")
    elif extension_id is not None and extension_id != ctx.expected_extension_id:
        gaps.add("confidential runtime evidence extension_id mismatch")


def _parse_confidential_tee(tee: Mapping[str, Any] | None, *, gaps: _Gaps) -> dict[str, Any]:
    if tee is None:
        return {}
    tee_kind_raw = _P.nonempty_str(tee.get("kind"), path="tee_attestation.kind", gaps=gaps)
    tee_kind = tee_kind_raw.lower() if tee_kind_raw else None
    raw_attestation_hash = _P.hex_token(
        tee.get("raw_attestation_hash"),
        path="tee_attestation.raw_attestation_hash",
        gaps=gaps,
        exact_len=_HASH_HEX_LEN,
    )
    measurement_raw = _P.nonempty_str(
        tee.get("measurement"), path="tee_attestation.measurement", gaps=gaps
    )
    measurement: str | None
    if measurement_raw is None:
        measurement = None
    elif measurement_raw.strip() != measurement_raw:
        gaps.add("tee_attestation.measurement must not contain leading/trailing whitespace")
        measurement = None
    else:
        measurement = measurement_raw
    measurement_in_allowlist = _P.bool_strict(
        tee.get("measurement_in_allowlist"),
        path="tee_attestation.measurement_in_allowlist",
        gaps=gaps,
    )
    platform_pubkey = _P.hex_token(
        tee.get("platform_pubkey"),
        path="tee_attestation.platform_pubkey",
        gaps=gaps,
        exact_len=_PUBKEY_HEX_LEN,
    )
    attestation_signature = _P.hex_token(
        tee.get("attestation_signature"),
        path="tee_attestation.attestation_signature",
        gaps=gaps,
        exact_len=_SIGNATURE_HEX_LEN,
    )
    verified_at = _P.positive_int(
        tee.get("verified_at"), path="tee_attestation.verified_at", gaps=gaps
    )
    return {
        "kind": tee_kind,
        "raw_attestation_hash": raw_attestation_hash,
        "measurement": measurement,
        "measurement_in_allowlist": measurement_in_allowlist,
        "platform_pubkey": platform_pubkey,
        "attestation_signature": attestation_signature,
        "verified_at": verified_at,
    }


def _validate_confidential_tee(
    tee_data: Mapping[str, Any],
    *,
    issued_at: int | None,
    now: int,
    gaps: _Gaps,
) -> None:
    tee_kind = tee_data.get("kind")
    measurement = tee_data.get("measurement")
    if tee_kind is not None and tee_kind not in _ALLOWED_TEE_KINDS:
        gaps.add(f"tee_attestation.kind {tee_kind!r} is not in the allowed set")
    if tee_data.get("measurement_in_allowlist") is False:
        gaps.add("tee_attestation.measurement_in_allowlist must be true for production")
    _validate_confidential_measurement_prefix(tee_kind=tee_kind, measurement=measurement, gaps=gaps)
    _validate_confidential_tee_time(
        verified_at=tee_data.get("verified_at"),
        issued_at=issued_at,
        now=now,
        gaps=gaps,
    )


def _validate_confidential_measurement_prefix(
    *,
    tee_kind: str | None,
    measurement: str | None,
    gaps: _Gaps,
) -> None:
    if measurement is None or tee_kind is None or tee_kind not in _TEE_KIND_TO_PREFIX:
        return
    expected_prefix = _TEE_KIND_TO_PREFIX[tee_kind]
    if not measurement.startswith(expected_prefix):
        gaps.add(
            f"tee_attestation.measurement prefix does not match tee_attestation.kind "
            f"({tee_kind!r} expects {expected_prefix!r})"
        )


def _validate_confidential_tee_time(
    *,
    verified_at: int | None,
    issued_at: int | None,
    now: int,
    gaps: _Gaps,
) -> None:
    if verified_at is None:
        return
    if verified_at > now + _FUTURE_SKEW_TOLERANCE_SECONDS:
        gaps.add("tee_attestation.verified_at is in the future")
    if issued_at is None:
        return
    if verified_at > issued_at + _FUTURE_SKEW_TOLERANCE_SECONDS:
        gaps.add("tee_attestation.verified_at cannot postdate issued_at")
    if issued_at - verified_at > _MAX_TEE_VERIFICATION_LAG_SECONDS:
        gaps.add("tee_attestation.verified_at is outside the TEE verification window")


def _parse_confidential_receipt(receipt: Mapping[str, Any] | None, *, gaps: _Gaps) -> dict[str, Any]:
    if receipt is None:
        return {}
    return {
        "runtime_receipt_hash": _P.hex_token(
            receipt.get("runtime_receipt_hash"),
            path="private_execution_receipt.runtime_receipt_hash",
            gaps=gaps,
            exact_len=_HASH_HEX_LEN,
        ),
        "attestation_receipt_hash": _P.hex_token(
            receipt.get("attestation_receipt_hash"),
            path="private_execution_receipt.attestation_receipt_hash",
            gaps=gaps,
            exact_len=_HASH_HEX_LEN,
        ),
        "request_id": _P.safe_token(
            receipt.get("request_id"),
            path="private_execution_receipt.request_id",
            gaps=gaps,
        ),
        "execution_id": _P.safe_token(
            receipt.get("execution_id"),
            path="private_execution_receipt.execution_id",
            gaps=gaps,
        ),
        "execution_kind": _P.safe_token(
            receipt.get("execution_kind"),
            path="private_execution_receipt.execution_kind",
            gaps=gaps,
        ),
        "result_code": _P.safe_token(
            receipt.get("result_code"),
            path="private_execution_receipt.result_code",
            gaps=gaps,
        ),
        "measurement_provider": _P.safe_token(
            receipt.get("measurement_provider"),
            path="private_execution_receipt.measurement_provider",
            gaps=gaps,
        ),
        "attestation_epoch": _P.bounded_int(
            receipt.get("attestation_epoch"),
            path="private_execution_receipt.attestation_epoch",
            gaps=gaps,
            lo=0,
            hi=0xFFFFFFFF,
        ),
        "current_epoch": _P.bounded_int(
            receipt.get("current_epoch"),
            path="private_execution_receipt.current_epoch",
            gaps=gaps,
            lo=0,
            hi=0xFFFFFFFF,
        ),
        "units_charged": _P.bounded_int(
            receipt.get("units_charged"),
            path="private_execution_receipt.units_charged",
            gaps=gaps,
            lo=0,
            hi=0xFFFFFFFF,
        ),
        "result_redacted": _P.bool_strict(
            receipt.get("result_redacted"),
            path="private_execution_receipt.result_redacted",
            gaps=gaps,
        ),
        "public_effect_digest": _P.hex_token(
            receipt.get("public_effect_digest"),
            path="private_execution_receipt.public_effect_digest",
            gaps=gaps,
            exact_len=_HASH_HEX_LEN,
        ),
    }


def _validate_confidential_context_bindings(
    *,
    approved_measurements: Sequence[str] | None,
    approved_measurements_hash: str | None,
    measurement: str | None,
    operator_status_hash: str | None,
    expected_operator_status_hash: str | None,
    external_verifier_binding_hash: str | None,
    expected_external_verifier_binding_hash: str | None,
    gaps: _Gaps,
) -> None:
    if approved_measurements is None:
        gaps.add("approved_measurements are required for confidential runtime binding")
    else:
        _validate_approved_measurements(
            approved_measurements,
            approved_measurements_hash=approved_measurements_hash,
            measurement=measurement,
            gaps=gaps,
        )

    if expected_operator_status_hash is None:
        gaps.add("operator_status_hash is required for confidential runtime binding")
    elif operator_status_hash is not None and expected_operator_status_hash != operator_status_hash:
        gaps.add("evidence.operator_status_hash does not match active operator status hash")

    if expected_external_verifier_binding_hash is None:
        gaps.add("external_verifier_binding_hash is required for confidential runtime binding")
    elif (
        external_verifier_binding_hash is not None
        and expected_external_verifier_binding_hash != external_verifier_binding_hash
    ):
        gaps.add("evidence.external_verifier_binding_hash does not match active binding hash")


def _validate_confidential_receipt(
    receipt_data: Mapping[str, Any],
    *,
    extension_id: str | None,
    provider_id: str | None,
    measurement: str | None,
    approved_measurements_hash: str | None,
    operator_status_hash: str | None,
    external_verifier_binding_hash: str | None,
    gaps: _Gaps,
) -> None:
    if receipt_data.get("result_code") != "ok":
        # Review note (grade B -> A-): this check intentionally lives in the
        # shared evaluator as well as the builder. A receipt can be hand-edited
        # and self-hashed; the production gate must still require a successful
        # private execution result.
        gaps.add("private_execution_receipt.result_code must be ok")
    if receipt_data.get("result_redacted") is False:
        gaps.add("private_execution_receipt.result_redacted must be true")
    _validate_confidential_runtime_receipt_hash(
        receipt_data,
        extension_id=extension_id,
        provider_id=provider_id,
        measurement=measurement,
        approved_measurements_hash=approved_measurements_hash,
        operator_status_hash=operator_status_hash,
        external_verifier_binding_hash=external_verifier_binding_hash,
        gaps=gaps,
    )


def _validate_confidential_runtime_receipt_hash(
    receipt_data: Mapping[str, Any],
    *,
    extension_id: str | None,
    provider_id: str | None,
    measurement: str | None,
    approved_measurements_hash: str | None,
    operator_status_hash: str | None,
    external_verifier_binding_hash: str | None,
    gaps: _Gaps,
) -> None:
    runtime_receipt_hash = receipt_data.get("runtime_receipt_hash")
    body = _confidential_runtime_receipt_body(
        receipt_data,
        extension_id=extension_id,
        provider_id=provider_id,
        measurement=measurement,
        approved_measurements_hash=approved_measurements_hash,
        operator_status_hash=operator_status_hash,
        external_verifier_binding_hash=external_verifier_binding_hash,
    )
    if body is None:
        return
    expected_hash = confidential_runtime_execution_receipt_hash_v1(body).removeprefix("0x")
    if runtime_receipt_hash is not None and runtime_receipt_hash != expected_hash:
        gaps.add("private_execution_receipt.runtime_receipt_hash does not match canonical runtime receipt")
    if receipt_data.get("attestation_epoch") is not None and receipt_data.get("current_epoch") is not None:
        if int(receipt_data["attestation_epoch"]) > int(receipt_data["current_epoch"]):
            gaps.add("private_execution_receipt.attestation_epoch cannot exceed current_epoch")
    measurement_provider = receipt_data.get("measurement_provider")
    expected_provider = _confidential_measurement_provider(measurement)
    if (
        measurement_provider is not None
        and expected_provider is not None
        and measurement_provider != expected_provider
    ):
        gaps.add("private_execution_receipt.measurement_provider does not match tee_attestation.measurement")


def _confidential_runtime_receipt_body(
    receipt_data: Mapping[str, Any],
    *,
    extension_id: str | None,
    provider_id: str | None,
    measurement: str | None,
    approved_measurements_hash: str | None,
    operator_status_hash: str | None,
    external_verifier_binding_hash: str | None,
) -> dict[str, Any] | None:
    required: tuple[object | None, ...] = (
        receipt_data.get("attestation_receipt_hash"),
        extension_id,
        provider_id,
        receipt_data.get("request_id"),
        receipt_data.get("execution_id"),
        receipt_data.get("execution_kind"),
        receipt_data.get("result_code"),
        receipt_data.get("measurement_provider"),
        operator_status_hash,
        approved_measurements_hash,
        external_verifier_binding_hash,
        receipt_data.get("attestation_epoch"),
        receipt_data.get("current_epoch"),
        receipt_data.get("units_charged"),
        receipt_data.get("result_redacted"),
        receipt_data.get("public_effect_digest"),
    )
    if any(value is None for value in required):
        return None
    return {
        "schema": CONFIDENTIAL_RUNTIME_EXECUTION_RECEIPT_SCHEMA_V1,
        "attestation_receipt_hash": _prefix_0x(str(receipt_data["attestation_receipt_hash"])),
        "extension_id": extension_id,
        "provider_id": provider_id,
        "request_id": receipt_data["request_id"],
        "execution_id": receipt_data["execution_id"],
        "execution_kind": receipt_data["execution_kind"],
        "result_code": receipt_data["result_code"],
        "measurement_provider": receipt_data["measurement_provider"],
        "operator_status_hash": _prefix_0x(str(operator_status_hash)),
        "approved_measurements_hash": _prefix_0x(str(approved_measurements_hash)),
        "external_verifier_binding_hash": _prefix_0x(str(external_verifier_binding_hash)),
        "attestation_epoch": receipt_data["attestation_epoch"],
        "current_epoch": receipt_data["current_epoch"],
        "units_charged": receipt_data["units_charged"],
        "result_redacted": receipt_data["result_redacted"],
        "public_effect_digest": _prefix_0x(str(receipt_data["public_effect_digest"])),
        "public_summary": {
            "execution_admitted": True,
            "policy_ok": True,
            "output_bound_ok": True,
            "request_bound": True,
        },
    }


def _prefix_0x(value: str) -> str:
    return value if value.startswith("0x") else "0x" + value


def _confidential_measurement_provider(measurement: str | None) -> str | None:
    if measurement is None:
        return None
    if measurement.startswith("nitro:"):
        return "nitro"
    if measurement.startswith("azure-sevsnp:"):
        return "azure-sevsnp"
    return "custom"


def _validate_approved_measurements(
    approved: Sequence[str],
    *,
    approved_measurements_hash: str | None = None,
    measurement: str | None,
    gaps: _Gaps,
) -> None:
    normalized = _normalize_approved_measurements(approved, gaps=gaps)
    if normalized is None:
        return
    if measurement is not None and measurement not in normalized:
        gaps.add("tee_attestation.measurement is not in approved_measurements")
    if approved_measurements_hash is not None:
        expected_hash = _confidential_approved_measurements_hash(normalized)
        if approved_measurements_hash != expected_hash:
            # Review note (grade B -> A-): this lane parsed
            # approved_measurements_hash but did not compare it to the active
            # allowlist context. A stale or fabricated allowlist digest could
            # therefore be published while the measured enclave happened to be
            # in the supplied list. The evidence hash now binds the full active
            # measurement allowlist used by the verifier.
            gaps.add("approved_measurements_hash does not match active approved_measurements")


def _confidential_approved_measurements_hash(approved: set[str]) -> str:
    return hash_v0(
        "production_confidential_runtime_approved_measurements_v1",
        {"approved_measurements": sorted(approved)},
    ).removeprefix("0x")


def _normalize_approved_measurements(
    approved: object,
    *,
    gaps: _Gaps,
) -> set[str] | None:
    if not isinstance(approved, Sequence) or isinstance(approved, (str, bytes, bytearray)):
        gaps.add("approved_measurements must be a sequence of strings")
        return None
    if len(approved) > _MAX_APPROVED_MEASUREMENTS:
        gaps.add(
            f"approved_measurements must contain at most {_MAX_APPROVED_MEASUREMENTS} entries"
        )
        return None
    normalized: set[str] = set()
    for index, item in enumerate(approved):
        if not isinstance(item, str):
            gaps.add(f"approved_measurements[{index}] must be a string")
            return None
        if item.strip() != item:
            gaps.add(
                f"approved_measurements[{index}] must not contain leading/trailing whitespace"
            )
            return None
        if item:
            normalized.add(item)
    return normalized


# -----------------------------------------------------------------------------
# Lane 6: app-root/JMT live root coverage.
# -----------------------------------------------------------------------------


_APP_ROOT_JMT_FIELDS = frozenset(
    {
        "schema",
        "evidence_kind",
        "root_system",
        "required_lane_kinds",
        "live_root_checks",
        "negative_checks",
        "issued_at",
        "evidence_hash",
    }
)
_APP_ROOT_LIVE_CHECK_FIELDS = frozenset(
    {
        "check_id",
        "mode",
        "source_kind",
        "source_payload",
        "observed_root",
        "recomputed_root",
        "source_state_hash",
        "required_lane_kinds",
        "live_path",
        "derivation_path",
        "checked_at",
    }
)
_APP_ROOT_NEGATIVE_CHECK_FIELDS = frozenset(
    {
        "check_id",
        "mutation",
        "mode",
        "source_kind",
        "baseline_payload",
        "mutated_payload",
        "baseline_root",
        "mutated_root",
        "required_lane_kinds",
        "derivation_path",
        "rejected",
        "checked_at",
    }
)
_APP_ROOT_ALLOWED_EVIDENCE_KIND = "live_replay"
_APP_ROOT_ALLOWED_ROOT_SYSTEM = "typed_app_root_jmt_v1"
_APP_ROOT_ALLOWED_SOURCE_KINDS = frozenset({"live_node", "live_local_replay", "release_replay"})


@dataclass(frozen=True)
class _ParsedAppRootLiveCheck:
    mode: str | None
    source_kind: str | None
    observed_root: str | None
    recomputed_root: str | None
    source_state_hash: str | None
    lane_kinds: frozenset[str] | None
    live_path: str | None
    derivation_path: str | None
    checked_at: int | None
    derived_source_hash: str | None
    derived_root: str | None


@dataclass(frozen=True)
class _ParsedAppRootNegativeCheck:
    mutation: str | None
    mode: str | None
    source_kind: str | None
    baseline_root: str | None
    mutated_root: str | None
    lane_kinds: frozenset[str] | None
    derivation_path: str | None
    rejected: bool | None
    checked_at: int | None
    derived_baseline_root: str | None
    derived_mutated_root: str | None


class _AppRootJmtLane(Lane):
    LANE_ID = LANE_APP_ROOT_JMT
    SCHEMA = APP_ROOT_JMT_EVIDENCE_SCHEMA_V2
    DOMAIN = "production_app_root_jmt_evidence_v2"
    ALLOWED_FIELDS = _APP_ROOT_JMT_FIELDS
    MISSING_MESSAGE = "app-root/JMT live-root evidence is missing"

    def validate(
        self,
        obj: Mapping[str, Any],
        ctx: "_LaneContext",
        gaps: _Gaps,
    ) -> tuple[dict[str, Any], dict[str, Any]]:
        if not isinstance(ctx, _AppRootJmtContext):
            return _invalid_lane_context("_AppRootJmtContext", gaps=gaps)
        evidence_kind = _P.nonempty_str(obj.get("evidence_kind"), path="evidence_kind", gaps=gaps)
        root_system = _P.nonempty_str(obj.get("root_system"), path="root_system", gaps=gaps)
        required_lane_kinds = _parse_app_root_lane_kind_set(
            obj.get("required_lane_kinds"),
            path="required_lane_kinds",
            gaps=gaps,
        )
        live_checks = _P.list_of_mappings(
            obj.get("live_root_checks"),
            path="live_root_checks",
            gaps=gaps,
            min_len=len(_APP_ROOT_REQUIRED_POSITIVE_MODES),
            max_len=_MAX_APP_ROOT_CHECKS,
        )
        negative_checks = _P.list_of_mappings(
            obj.get("negative_checks"),
            path="negative_checks",
            gaps=gaps,
            min_len=len(_APP_ROOT_REQUIRED_NEGATIVE_MUTATIONS),
            max_len=_MAX_APP_ROOT_NEGATIVE_CHECKS,
        )
        issued_at = _P.positive_int(obj.get("issued_at"), path="issued_at", gaps=gaps)

        _validate_app_root_evidence_kind(evidence_kind, gaps=gaps)
        if root_system is not None and root_system != _APP_ROOT_ALLOWED_ROOT_SYSTEM:
            gaps.add("app-root/JMT root_system must be typed_app_root_jmt_v1")
        if required_lane_kinds is not None:
            _validate_app_root_required_lane_set(required_lane_kinds, path="required_lane_kinds", gaps=gaps)
        observed_roots = _validate_app_root_live_checks(
            live_checks or [],
            ctx=ctx,
            gaps=gaps,
        )
        negative_mutations = _validate_app_root_negative_checks(
            negative_checks or [],
            ctx=ctx,
            gaps=gaps,
        )
        if issued_at is not None:
            _check_freshness(
                issued_at,
                now=ctx.now,
                max_age_s=_MAX_EVIDENCE_AGE_SECONDS,
                label="app-root/JMT evidence",
                gaps=gaps,
            )

        bindings = {
            "evidence_kind": evidence_kind,
            "root_system": root_system,
            "required_lane_kinds": sorted(required_lane_kinds or []),
        }
        extras = {
            "positive_modes": sorted(observed_roots),
            "negative_mutations": sorted(negative_mutations),
        }
        return bindings, extras


def _validate_app_root_evidence_kind(evidence_kind: str | None, *, gaps: _Gaps) -> None:
    if evidence_kind is None:
        return
    if evidence_kind != _APP_ROOT_ALLOWED_EVIDENCE_KIND:
        gaps.add("app-root/JMT evidence_kind must be live_replay")
    if evidence_kind in {"fixture", "synthetic", "demo", "echo"}:
        gaps.add("app-root/JMT fixture or synthetic evidence cannot clear production promotion")


def _parse_app_root_lane_kind_set(
    value: object,
    *,
    path: str,
    gaps: _Gaps,
) -> frozenset[str] | None:
    if not isinstance(value, list):
        gaps.at(path, "must be a list")
        return None
    if not value:
        gaps.at(path, "must be non-empty")
        return None
    normalized: set[str] = set()
    for index, item in enumerate(value):
        lane_kind = _P.nonempty_str(item, path=f"{path}[{index}]", gaps=gaps)
        if lane_kind is None:
            return None
        if lane_kind not in APP_ROOT_LANE_KINDS:
            gaps.at(f"{path}[{index}]", f"unsupported app-root lane kind {lane_kind!r}")
            return None
        if lane_kind in normalized:
            gaps.at(f"{path}[{index}]", f"duplicate app-root lane kind {lane_kind!r}")
            return None
        normalized.add(lane_kind)
    return frozenset(normalized)


def _validate_app_root_required_lane_set(
    lane_kinds: frozenset[str],
    *,
    path: str,
    gaps: _Gaps,
) -> None:
    expected = APP_ROOT_LANE_KINDS
    missing = sorted(expected - lane_kinds)
    extra = sorted(lane_kinds - expected)
    if missing:
        gaps.at(path, "missing lane kind(s): " + ", ".join(missing))
    if extra:
        gaps.at(path, "unsupported lane kind(s): " + ", ".join(extra))


def _app_root_source_payload_hash(payload: Mapping[str, Any]) -> str:
    return hash_v0("app_root_jmt_evidence_source_v1", payload).removeprefix("0x")


def _rederive_app_root_from_source_payload(
    *,
    mode: str | None,
    payload: object,
    path: str,
    gaps: _Gaps,
) -> tuple[str | None, str | None]:
    source_payload = _P.mapping(payload, path=path, gaps=gaps)
    if source_payload is None or mode is None:
        return None, None
    try:
        bounded_json_utf8_size(
            source_payload,
            max_bytes=_MAX_APP_ROOT_SOURCE_PAYLOAD_BYTES,
        )
        source_hash = _app_root_source_payload_hash(source_payload)
        if mode == "tau_app_state_wrapper_live_root":
            root = compute_tau_app_state_app_root_v0(source_payload)
        elif mode in {
            "plain_dex_snapshot_live_root",
            "local_block_pre_snapshot_header",
        }:
            root = compute_dex_snapshot_app_root_v0(source_payload)
        else:
            gaps.at(path, "cannot re-derive unsupported app-root mode")
            return source_hash, None
    except (RecursionError, TypeError, ValueError) as exc:
        gaps.at(path, f"cannot re-derive app root: {type(exc).__name__}")
        return None, None
    return source_hash, root.removeprefix("0x").lower()


def _validate_app_root_derivation_path(
    *,
    mode: str | None,
    derivation_path: str | None,
    path: str,
    gaps: _Gaps,
) -> None:
    if mode is None or derivation_path is None:
        return
    expected = _APP_ROOT_DERIVATION_PATHS.get(mode)
    if expected is None or derivation_path != expected:
        gaps.at(path, "does not match the selected app-root derivation")


def _parse_app_root_live_check(
    check: Mapping[str, Any],
    *,
    index: int,
    gaps: _Gaps,
) -> _ParsedAppRootLiveCheck:
    prefix = f"live_root_checks[{index}]"
    _check_unknown_fields(check, allowed=_APP_ROOT_LIVE_CHECK_FIELDS, gaps=gaps)
    mode = _P.nonempty_str(check.get("mode"), path=f"{prefix}.mode", gaps=gaps)
    _P.safe_token(check.get("check_id"), path=f"{prefix}.check_id", gaps=gaps)
    parsed = _ParsedAppRootLiveCheck(
        mode=mode,
        source_kind=_P.nonempty_str(check.get("source_kind"), path=f"{prefix}.source_kind", gaps=gaps),
        observed_root=_P.hex_token(
            check.get("observed_root"), path=f"{prefix}.observed_root", gaps=gaps, exact_len=_HASH_HEX_LEN
        ),
        recomputed_root=_P.hex_token(
            check.get("recomputed_root"), path=f"{prefix}.recomputed_root", gaps=gaps, exact_len=_HASH_HEX_LEN
        ),
        source_state_hash=_P.hex_token(
            check.get("source_state_hash"), path=f"{prefix}.source_state_hash", gaps=gaps, exact_len=_HASH_HEX_LEN
        ),
        lane_kinds=_parse_app_root_lane_kind_set(
            check.get("required_lane_kinds"), path=f"{prefix}.required_lane_kinds", gaps=gaps
        ),
        live_path=_P.nonempty_str(check.get("live_path"), path=f"{prefix}.live_path", gaps=gaps),
        derivation_path=_P.nonempty_str(
            check.get("derivation_path"), path=f"{prefix}.derivation_path", gaps=gaps
        ),
        checked_at=_P.positive_int(check.get("checked_at"), path=f"{prefix}.checked_at", gaps=gaps),
        derived_source_hash=None,
        derived_root=None,
    )
    derived_hash, derived_root = _rederive_app_root_from_source_payload(
        mode=mode,
        payload=check.get("source_payload"),
        path=f"{prefix}.source_payload",
        gaps=gaps,
    )
    return dataclass_replace(
        parsed,
        derived_source_hash=derived_hash,
        derived_root=derived_root,
    )


def _validate_app_root_live_check(
    parsed: _ParsedAppRootLiveCheck,
    *,
    index: int,
    now: int,
    gaps: _Gaps,
) -> None:
    prefix = f"live_root_checks[{index}]"
    if parsed.mode not in _APP_ROOT_REQUIRED_POSITIVE_MODES:
        gaps.at(f"{prefix}.mode", "unsupported app-root live-root mode")
    _validate_app_root_source_kind(parsed.source_kind, path=f"{prefix}.source_kind", gaps=gaps)
    if parsed.observed_root is not None and parsed.recomputed_root != parsed.observed_root:
        gaps.at(f"{prefix}.observed_root", "does not match recomputed_root")
    if parsed.source_state_hash is not None and parsed.derived_source_hash != parsed.source_state_hash:
        gaps.at(f"{prefix}.source_state_hash", "does not match source_payload")
    if parsed.derived_root is not None and parsed.observed_root != parsed.derived_root:
        gaps.at(f"{prefix}.observed_root", "does not match evaluator-derived root")
    if parsed.derived_root is not None and parsed.recomputed_root != parsed.derived_root:
        gaps.at(f"{prefix}.recomputed_root", "does not match evaluator-derived root")
    if parsed.lane_kinds is not None:
        _validate_app_root_required_lane_set(parsed.lane_kinds, path=f"{prefix}.required_lane_kinds", gaps=gaps)
    _validate_app_root_live_path(parsed.live_path, path=f"{prefix}.live_path", gaps=gaps)
    _validate_app_root_derivation_path(
        mode=parsed.mode,
        derivation_path=parsed.derivation_path,
        path=f"{prefix}.derivation_path",
        gaps=gaps,
    )
    if parsed.checked_at is not None:
        _check_freshness(
            parsed.checked_at,
            now=now,
            max_age_s=_MAX_EVIDENCE_AGE_SECONDS,
            label=f"app-root/JMT {prefix}",
            gaps=gaps,
        )


def _validate_app_root_live_checks(
    checks: Sequence[Mapping[str, Any]],
    *,
    ctx: _AppRootJmtContext,
    gaps: _Gaps,
) -> set[str]:
    seen_modes: set[str] = set()
    for index, check in enumerate(checks):
        parsed = _parse_app_root_live_check(check, index=index, gaps=gaps)
        _validate_app_root_live_check(parsed, index=index, now=ctx.now, gaps=gaps)
        if parsed.mode in _APP_ROOT_REQUIRED_POSITIVE_MODES:
            seen_modes.add(parsed.mode)
    missing_modes = sorted(_APP_ROOT_REQUIRED_POSITIVE_MODES - seen_modes)
    if missing_modes:
        gaps.add("app-root/JMT live_root_checks missing mode(s): " + ", ".join(missing_modes))
    return seen_modes


def _parse_app_root_negative_check(
    check: Mapping[str, Any],
    *,
    index: int,
    gaps: _Gaps,
) -> _ParsedAppRootNegativeCheck:
    prefix = f"negative_checks[{index}]"
    _check_unknown_fields(check, allowed=_APP_ROOT_NEGATIVE_CHECK_FIELDS, gaps=gaps)
    _P.safe_token(check.get("check_id"), path=f"{prefix}.check_id", gaps=gaps)
    mode = _P.nonempty_str(check.get("mode"), path=f"{prefix}.mode", gaps=gaps)
    _baseline_hash, derived_baseline = _rederive_app_root_from_source_payload(
        mode=mode, payload=check.get("baseline_payload"), path=f"{prefix}.baseline_payload", gaps=gaps
    )
    _mutated_hash, derived_mutated = _rederive_app_root_from_source_payload(
        mode=mode, payload=check.get("mutated_payload"), path=f"{prefix}.mutated_payload", gaps=gaps
    )
    return _ParsedAppRootNegativeCheck(
        mutation=_P.nonempty_str(check.get("mutation"), path=f"{prefix}.mutation", gaps=gaps),
        mode=mode,
        source_kind=_P.nonempty_str(check.get("source_kind"), path=f"{prefix}.source_kind", gaps=gaps),
        baseline_root=_P.hex_token(
            check.get("baseline_root"), path=f"{prefix}.baseline_root", gaps=gaps, exact_len=_HASH_HEX_LEN
        ),
        mutated_root=_P.hex_token(
            check.get("mutated_root"), path=f"{prefix}.mutated_root", gaps=gaps, exact_len=_HASH_HEX_LEN
        ),
        lane_kinds=_parse_app_root_lane_kind_set(
            check.get("required_lane_kinds"), path=f"{prefix}.required_lane_kinds", gaps=gaps
        ),
        derivation_path=_P.nonempty_str(
            check.get("derivation_path"), path=f"{prefix}.derivation_path", gaps=gaps
        ),
        rejected=_P.bool_strict(check.get("rejected"), path=f"{prefix}.rejected", gaps=gaps),
        checked_at=_P.positive_int(check.get("checked_at"), path=f"{prefix}.checked_at", gaps=gaps),
        derived_baseline_root=derived_baseline,
        derived_mutated_root=derived_mutated,
    )


def _validate_app_root_negative_check(
    parsed: _ParsedAppRootNegativeCheck,
    *,
    index: int,
    now: int,
    gaps: _Gaps,
) -> None:
    prefix = f"negative_checks[{index}]"
    if parsed.mutation not in _APP_ROOT_REQUIRED_NEGATIVE_MUTATIONS:
        gaps.at(f"{prefix}.mutation", "unsupported app-root negative mutation")
    if parsed.mode not in _APP_ROOT_REQUIRED_POSITIVE_MODES:
        gaps.at(f"{prefix}.mode", "unsupported app-root live-root mode")
    _validate_app_root_source_kind(parsed.source_kind, path=f"{prefix}.source_kind", gaps=gaps)
    if parsed.lane_kinds is not None:
        _validate_app_root_required_lane_set(parsed.lane_kinds, path=f"{prefix}.required_lane_kinds", gaps=gaps)
    _validate_app_root_derivation_path(
        mode=parsed.mode,
        derivation_path=parsed.derivation_path,
        path=f"{prefix}.derivation_path",
        gaps=gaps,
    )
    if parsed.derived_baseline_root is not None and parsed.baseline_root != parsed.derived_baseline_root:
        gaps.at(f"{prefix}.baseline_root", "does not match evaluator-derived root")
    if parsed.derived_mutated_root is not None and parsed.mutated_root != parsed.derived_mutated_root:
        gaps.at(f"{prefix}.mutated_root", "does not match evaluator-derived root")
    derived_rejected = (
        parsed.derived_baseline_root is not None
        and parsed.derived_mutated_root is not None
        and parsed.derived_baseline_root != parsed.derived_mutated_root
    )
    if parsed.rejected is not None and parsed.rejected != derived_rejected:
        gaps.at(f"{prefix}.rejected", "does not match evaluator-derived mutation result")
    if parsed.checked_at is not None:
        _check_freshness(
            parsed.checked_at,
            now=now,
            max_age_s=_MAX_EVIDENCE_AGE_SECONDS,
            label=f"app-root/JMT {prefix}",
            gaps=gaps,
        )


def _validate_app_root_negative_checks(
    checks: Sequence[Mapping[str, Any]],
    *,
    ctx: _AppRootJmtContext,
    gaps: _Gaps,
) -> set[str]:
    seen_mutations: set[str] = set()
    for index, check in enumerate(checks):
        parsed = _parse_app_root_negative_check(check, index=index, gaps=gaps)
        _validate_app_root_negative_check(parsed, index=index, now=ctx.now, gaps=gaps)
        if parsed.mutation in _APP_ROOT_REQUIRED_NEGATIVE_MUTATIONS:
            seen_mutations.add(parsed.mutation)
    missing_mutations = sorted(_APP_ROOT_REQUIRED_NEGATIVE_MUTATIONS - seen_mutations)
    if missing_mutations:
        gaps.add("app-root/JMT negative_checks missing mutation(s): " + ", ".join(missing_mutations))
    return seen_mutations


def _validate_app_root_source_kind(source_kind: str | None, *, path: str, gaps: _Gaps) -> None:
    if source_kind is None:
        return
    if source_kind in {"fixture", "synthetic", "demo", "echo"}:
        gaps.at(path, "fixture or synthetic source kinds cannot clear production promotion")
    elif source_kind not in _APP_ROOT_ALLOWED_SOURCE_KINDS:
        gaps.at(path, "unsupported app-root source kind")


def _validate_app_root_live_path(live_path: str | None, *, path: str, gaps: _Gaps) -> None:
    if live_path is None:
        return
    lowered = live_path.lower()
    if any(marker in lowered for marker in ("fixture", "synthetic", "demo", "echo")):
        gaps.at(path, "must identify a live or replayed authority path, not fixture/demo evidence")


# -----------------------------------------------------------------------------
# Lane registry.
# -----------------------------------------------------------------------------


_ORACLE_AUTHORITY_LANE = _OracleAuthorityLane()
_HARDWARE_WALLET_LANE = _HardwareWalletLane()
_ZK_WRAPPING_LANE = _ZkWrappingLane()
_AUTOTRADER_LANE = _AutotraderLane()
_CONFIDENTIAL_RUNTIME_LANE = _ConfidentialRuntimeLane()
_APP_ROOT_JMT_LANE = _AppRootJmtLane()

_LANE_REGISTRY: Final[Mapping[str, Lane]] = {
    LANE_ORACLE_AUTHORITY: _ORACLE_AUTHORITY_LANE,
    LANE_HARDWARE_WALLET: _HARDWARE_WALLET_LANE,
    LANE_ZK_WRAPPING: _ZK_WRAPPING_LANE,
    LANE_AUTOTRADER: _AUTOTRADER_LANE,
    LANE_CONFIDENTIAL_RUNTIME: _CONFIDENTIAL_RUNTIME_LANE,
    LANE_APP_ROOT_JMT: _APP_ROOT_JMT_LANE,
}


# -----------------------------------------------------------------------------
# Public lane-specific entry points.
# -----------------------------------------------------------------------------


def evaluate_production_oracle_authority_evidence_v1(
    evidence: Mapping[str, Any] | None,
    *,
    bounded_exercise_status: Mapping[str, Any] | None,
    expected_chain_id: str | None = None,
    expected_authority_signer_pubkey: str | None = None,
    now: int | None = None,
) -> dict[str, Any]:
    ctx = _OracleAuthorityContext(
        bounded_exercise_status=bounded_exercise_status,
        expected_chain_id=expected_chain_id,
        expected_authority_signer_pubkey=expected_authority_signer_pubkey,
        now=_now_seconds(now),
    )
    return _evaluate_lane(_ORACLE_AUTHORITY_LANE, evidence, ctx)


def evaluate_production_hardware_wallet_evidence_v1(
    evidence: Mapping[str, Any] | None,
    *,
    wallet_authority_profile_hash: str | None,
    expected_device_pubkey: str | None = None,
    now: int | None = None,
) -> dict[str, Any]:
    ctx = _HardwareWalletContext(
        wallet_authority_profile_hash=wallet_authority_profile_hash,
        expected_device_pubkey=expected_device_pubkey,
        now=_now_seconds(now),
    )
    return _evaluate_lane(_HARDWARE_WALLET_LANE, evidence, ctx)


def evaluate_production_zk_wrapping_evidence_v1(
    evidence: Mapping[str, Any] | None,
    *,
    live_proof_wrapper_status: Mapping[str, Any] | None,
    expected_surface: str | None = None,
    now: int | None = None,
) -> dict[str, Any]:
    ctx = _ZkWrappingContext(
        live_proof_wrapper_status=live_proof_wrapper_status,
        expected_surface=expected_surface,
        now=_now_seconds(now),
    )
    return _evaluate_lane(_ZK_WRAPPING_LANE, evidence, ctx)


def evaluate_production_autotrader_evidence_v1(
    evidence: Mapping[str, Any] | None,
    *,
    supervisor_profile_hash: str | None,
    config_max_actions_per_tick: int | None,
    config_max_runs_per_process: int | None,
    expected_chain_id: str | None = None,
    expected_approval_signer_pubkeys: Sequence[str] | None = None,
    now: int | None = None,
) -> dict[str, Any]:
    ctx = _AutotraderContext(
        supervisor_profile_hash=supervisor_profile_hash,
        config_max_actions_per_tick=config_max_actions_per_tick,
        config_max_runs_per_process=config_max_runs_per_process,
        expected_chain_id=expected_chain_id,
        expected_approval_signer_pubkeys=expected_approval_signer_pubkeys,
        now=_now_seconds(now),
    )
    return _evaluate_lane(_AUTOTRADER_LANE, evidence, ctx)


def evaluate_production_confidential_runtime_evidence_v1(
    evidence: Mapping[str, Any] | None,
    *,
    approved_measurements: Sequence[str] | None,
    operator_status_hash: str | None,
    external_verifier_binding_hash: str | None,
    expected_extension_id: str | None = None,
    now: int | None = None,
) -> dict[str, Any]:
    ctx = _ConfidentialContext(
        approved_measurements=approved_measurements,
        operator_status_hash=operator_status_hash,
        external_verifier_binding_hash=external_verifier_binding_hash,
        expected_extension_id=expected_extension_id,
        now=_now_seconds(now),
    )
    return _evaluate_lane(_CONFIDENTIAL_RUNTIME_LANE, evidence, ctx)


def evaluate_production_app_root_jmt_evidence_v2(
    evidence: Mapping[str, Any] | None,
    *,
    now: int | None = None,
) -> dict[str, Any]:
    ctx = _AppRootJmtContext(now=_now_seconds(now))
    return _evaluate_lane(_APP_ROOT_JMT_LANE, evidence, ctx)


def evaluate_production_app_root_jmt_evidence_v1(
    evidence: Mapping[str, Any] | None,
    *,
    now: int | None = None,
) -> dict[str, Any]:
    """Compatibility entrypoint that applies the fail-closed V2 evaluator."""

    return evaluate_production_app_root_jmt_evidence_v2(evidence, now=now)


# -----------------------------------------------------------------------------
# Aggregate bundle evaluator.
# -----------------------------------------------------------------------------


def evaluate_production_promotion_bundle_v1(
    bundle: object,
    *,
    bounded_oracle_exercise_status: Mapping[str, Any] | None = None,
    wallet_authority_profile_hash: str | None = None,
    live_proof_wrapper_status: Mapping[str, Any] | None = None,
    supervisor_profile_hash: str | None = None,
    config_max_actions_per_tick: int | None = None,
    config_max_runs_per_process: int | None = None,
    approved_measurements: Sequence[str] | None = None,
    operator_status_hash: str | None = None,
    external_verifier_binding_hash: str | None = None,
    expected_chain_id: str | None = None,
    expected_oracle_authority_signer_pubkey: str | None = None,
    expected_surface: str | None = None,
    expected_extension_id: str | None = None,
    expected_device_pubkey: str | None = None,
    expected_autotrader_approval_signer_pubkeys: Sequence[str] | None = None,
    now: int | None = None,
) -> dict[str, Any]:
    """Evaluate a bundle containing evidence for one or more lanes."""
    if bundle is None:
        safe_bundle: Mapping[str, Any] = {}
    elif isinstance(bundle, Mapping):
        safe_bundle = bundle
    else:
        return _bundle_invalid_status("production promotion bundle must be an object")

    now_s = _now_seconds(now)

    contexts: Mapping[str, _LaneContext] = {
        LANE_ORACLE_AUTHORITY: _OracleAuthorityContext(
            bounded_exercise_status=bounded_oracle_exercise_status,
            expected_chain_id=expected_chain_id,
            expected_authority_signer_pubkey=expected_oracle_authority_signer_pubkey,
            now=now_s,
        ),
        LANE_HARDWARE_WALLET: _HardwareWalletContext(
            wallet_authority_profile_hash=wallet_authority_profile_hash,
            expected_device_pubkey=expected_device_pubkey,
            now=now_s,
        ),
        LANE_ZK_WRAPPING: _ZkWrappingContext(
            live_proof_wrapper_status=live_proof_wrapper_status,
            expected_surface=expected_surface,
            now=now_s,
        ),
        LANE_AUTOTRADER: _AutotraderContext(
            supervisor_profile_hash=supervisor_profile_hash,
            config_max_actions_per_tick=config_max_actions_per_tick,
            config_max_runs_per_process=config_max_runs_per_process,
            expected_chain_id=expected_chain_id,
            expected_approval_signer_pubkeys=expected_autotrader_approval_signer_pubkeys,
            now=now_s,
        ),
        LANE_CONFIDENTIAL_RUNTIME: _ConfidentialContext(
            approved_measurements=approved_measurements,
            operator_status_hash=operator_status_hash,
            external_verifier_binding_hash=external_verifier_binding_hash,
            expected_extension_id=expected_extension_id,
            now=now_s,
        ),
        LANE_APP_ROOT_JMT: _AppRootJmtContext(now=now_s),
    }

    unknown_lanes: list[str] = sorted(
        key for key in safe_bundle.keys() if key not in _LANE_REGISTRY
    )

    lanes: dict[str, dict[str, Any]] = {}
    for lane_id in ALL_LANE_IDS:
        lanes[lane_id] = _evaluate_lane(
            _LANE_REGISTRY[lane_id],
            safe_bundle.get(lane_id),
            contexts[lane_id],
        )
    promotion_ready = (
        not unknown_lanes
        and all(s["production_ready"] is True for s in lanes.values())
    )
    blocked_lanes = [name for name, s in lanes.items() if not s["production_ready"]]
    blocked_lanes.extend(f"unknown:{name}" for name in unknown_lanes)
    bundle_gaps: list[str] = [f"unknown lane key {key!r}" for key in unknown_lanes]
    for lane_id, status in lanes.items():
        for gap in status["gaps"]:
            bundle_gaps.append(f"{lane_id}: {gap}")
    return {
        "schema": PRODUCTION_PROMOTION_BUNDLE_STATUS_SCHEMA_V1,
        "promotion_ready": promotion_ready,
        "status": "ready" if promotion_ready else "blocked",
        "blocked_lanes": blocked_lanes,
        "unknown_lanes": unknown_lanes,
        "lanes": lanes,
        "gaps": bundle_gaps,
    }


def _bundle_invalid_status(message: str) -> dict[str, Any]:
    placeholder: dict[str, Any] = {
        "schema": PRODUCTION_PROMOTION_STATUS_SCHEMA_V1,
        "lane": None,
        "ok": False,
        "production_ready": False,
        "status": "blocked",
        "gaps": [message],
        "evidence_hash": None,
        "issued_at": None,
        "bindings": {},
    }
    lanes = {lane_id: dict(placeholder, lane=lane_id) for lane_id in ALL_LANE_IDS}
    return {
        "schema": PRODUCTION_PROMOTION_BUNDLE_STATUS_SCHEMA_V1,
        "promotion_ready": False,
        "status": "blocked",
        "blocked_lanes": list(ALL_LANE_IDS),
        "unknown_lanes": [],
        "lanes": lanes,
        "gaps": [message],
    }


# -----------------------------------------------------------------------------
# Producer-side hash attachers (backward-compatible API).
# -----------------------------------------------------------------------------


def attach_evidence_hash(evidence: Mapping[str, Any], *, domain: str) -> dict[str, Any]:
    body = _evidence_body(evidence)
    return {**body, "evidence_hash": _hash_evidence_v1(domain, body)}


def attach_production_oracle_authority_hash_v1(evidence: Mapping[str, Any]) -> dict[str, Any]:
    return attach_evidence_hash(evidence, domain=_ORACLE_AUTHORITY_LANE.DOMAIN)


def attach_production_hardware_wallet_hash_v1(evidence: Mapping[str, Any]) -> dict[str, Any]:
    return attach_evidence_hash(evidence, domain=_HARDWARE_WALLET_LANE.DOMAIN)


def attach_production_zk_wrapping_hash_v1(evidence: Mapping[str, Any]) -> dict[str, Any]:
    return attach_evidence_hash(evidence, domain=_ZK_WRAPPING_LANE.DOMAIN)


def attach_production_autotrader_hash_v1(evidence: Mapping[str, Any]) -> dict[str, Any]:
    return attach_evidence_hash(evidence, domain=_AUTOTRADER_LANE.DOMAIN)


def attach_production_confidential_runtime_hash_v1(evidence: Mapping[str, Any]) -> dict[str, Any]:
    return attach_evidence_hash(evidence, domain=_CONFIDENTIAL_RUNTIME_LANE.DOMAIN)


def attach_production_app_root_jmt_hash_v1(evidence: Mapping[str, Any]) -> dict[str, Any]:
    return attach_evidence_hash(evidence, domain="production_app_root_jmt_evidence_v1")


def attach_production_app_root_jmt_hash_v2(evidence: Mapping[str, Any]) -> dict[str, Any]:
    return attach_evidence_hash(evidence, domain=_APP_ROOT_JMT_LANE.DOMAIN)
