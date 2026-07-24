"""Authenticated adapter from the pinned RISC0 CLI to exact-once admission.

The adapter owns the process boundary. It never accepts caller-projected
``verified`` booleans. The pinned CLI must verify the aggregate receipt, match
ledger-owned recursive expectations, recompose the disclosed recursive input,
and emit root-bound element facts before this module admits anything.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from typing import TYPE_CHECKING, Any, Mapping, NoReturn, Self, final

from src.core.recursive_stark_admission import (
    RecursiveStarkAdmissionResult,
    RecursiveStarkAdmissionState,
    RecursiveStarkRootFacts,
    TrustedRecursiveStarkAdmissionPolicy,
    _admit_authenticated_recursive_stark_root,
    _AuthenticatedRecursiveStarkRootFacts,
    _mint_recursive_stark_root_facts_after_verification,
    _RecursiveStarkVerificationProvenance,
)
from src.integration._zeno_ledger_pinned_verifier_process_v1 import (
    PinnedVerifierProcessError,
    PinnedVerifierProcessFailure,
    VerifierExecutableFormatV1,
    execute_pinned_verifier_once,
)
from src.integration.recursive_stark_release_binding import (
    load_recursive_stark_release_binding_v1,
)

if TYPE_CHECKING:
    from src.integration.recursive_stark_admission_store import (
        DurableRecursiveStarkAdmissionCursor,
        DurableRecursiveStarkAdmissionResult,
        SQLiteRecursiveStarkAdmissionStore,
    )

VERIFIED_FACTS_SCHEMA_V1 = "zenodex.verified_recursive_stark_root_facts.v1"
AUTHORITY_MANIFEST_SCHEMA_V1 = "zenodex.recursive_stark_verifier_authority.v1"
RECEIPT_CODEC_V1 = "risc0_receipt_canonical_serde_json_depth128_v1"
MAX_AUTHORITY_MANIFEST_BYTES = 1024 * 1024
MAX_VERIFIER_REQUEST_BYTES = 64 * 1024 * 1024
MAX_VERIFIER_STDOUT_BYTES = 16 * 1024 * 1024
MAX_VERIFIER_STDERR_BYTES = 1024 * 1024
DEFAULT_VERIFIER_ADDRESS_SPACE_BYTES = 2 * 1024 * 1024 * 1024
DEFAULT_VERIFIER_STACK_BYTES = 32 * 1024 * 1024

_FACT_KEYS = frozenset(
    {
        "schema",
        "aggregate_image_id",
        "receipt_codec",
        "receipt_kind",
        "receipt_hashfn",
        "receipt_verifier_parameters",
        "receipt_control_id",
        "chain_id",
        "epoch_id",
        "proof_profile",
        "root_journal_hash",
        "verifier_set_root",
        "public_policy_hash",
        "child_verification_claim_hashes",
        "child_verification_claims_root",
        "accepted_receipt_ids",
        "accepted_receipts_root",
        "cross_shard_message_ids",
        "cross_shard_message_ids_root",
    }
)


class RecursiveStarkVerificationError(ValueError):
    """Stable failure at the authenticated verifier-process boundary."""


class RecursiveVerifierExecutableFormat(str, Enum):
    """Dependency-closure policy for the pinned verifier executable."""

    STATIC_ELF_X86_64 = "static_elf_x86_64"
    TEST_SCRIPT = "test_script"


@final
@dataclass(frozen=True)
class PinnedRecursiveStarkVerifier:
    """Verifier binary and policy derived from one authenticated manifest.

    ``authority_manifest_sha256`` is a bootstrap identifier. Release code must
    obtain it from separately governed ledger or release state. The executable
    digest, format, and trusted expectations are derived exclusively from the
    canonical manifest bytes matching that identifier. Constructing both from
    proof-supplied data provides local test evidence only.
    """

    executable: Path
    authority_manifest_json: bytes
    authority_manifest_sha256: str
    timeout_seconds: int = 60
    max_address_space_bytes: int = DEFAULT_VERIFIER_ADDRESS_SPACE_BYTES
    max_stack_bytes: int = DEFAULT_VERIFIER_STACK_BYTES
    sha256: str = field(init=False)
    trusted_expectations: Mapping[str, Any] = field(init=False)
    executable_format: RecursiveVerifierExecutableFormat = field(init=False)
    _trusted_expectations_json: bytes = field(init=False, repr=False)
    _release_binding_config_digest: str | None = field(init=False, default=None, repr=False)
    _replay_manifest_sha256: str | None = field(init=False, default=None, repr=False)

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("PinnedRecursiveStarkVerifier cannot be subclassed")

    def __post_init__(self) -> None:
        if not self.executable.is_absolute():
            raise ValueError("recursive verifier executable must be an absolute path")
        if len(self.authority_manifest_sha256) != 64 or any(
            c not in "0123456789abcdef" for c in self.authority_manifest_sha256
        ):
            raise ValueError(
                "recursive verifier authority_manifest_sha256 must be lowercase 64-character hex"
            )
        if self.timeout_seconds <= 0 or self.timeout_seconds > 300:
            raise ValueError("recursive verifier timeout_seconds must be in 1..300")
        if self.max_address_space_bytes < 256 * 1024 * 1024:
            raise ValueError("recursive verifier address-space limit is too small")
        if self.max_stack_bytes < 1024 * 1024:
            raise ValueError("recursive verifier stack limit is too small")
        executable_sha256, executable_format, canonical_expectations = _parse_authority_manifest_v1(
            self.authority_manifest_json,
            expected_sha256=self.authority_manifest_sha256,
        )
        decoded_expectations = json.loads(canonical_expectations)
        object.__setattr__(self, "sha256", executable_sha256)
        object.__setattr__(self, "executable_format", executable_format)
        object.__setattr__(self, "trusted_expectations", decoded_expectations)
        object.__setattr__(self, "_trusted_expectations_json", canonical_expectations)

    @classmethod
    def from_governed_release_binding(
        cls,
        *,
        executable: Path,
        authority_manifest_json: bytes,
        authority_manifest_sha256: str,
        release_binding_json: bytes,
        expected_release_binding_config_digest: str,
        timeout_seconds: int = 60,
        max_address_space_bytes: int = DEFAULT_VERIFIER_ADDRESS_SPACE_BYTES,
        max_stack_bytes: int = DEFAULT_VERIFIER_STACK_BYTES,
    ) -> Self:
        """Bind a verifier to release bytes matching an external config digest."""

        verifier = cls(
            executable=executable,
            authority_manifest_json=authority_manifest_json,
            authority_manifest_sha256=authority_manifest_sha256,
            timeout_seconds=timeout_seconds,
            max_address_space_bytes=max_address_space_bytes,
            max_stack_bytes=max_stack_bytes,
        )
        policy = _trusted_policy(verifier.trusted_expectations)
        binding = load_recursive_stark_release_binding_v1(
            release_binding_json,
            expected_config_digest=expected_release_binding_config_digest,
            expected_chain_id=policy.expected_chain_id,
            expected_epoch_id=policy.expected_epoch_id,
            expected_proof_profile=policy.expected_proof_profile,
        )
        if binding.authority_manifest_sha256 != verifier.authority_manifest_sha256:
            raise ValueError("recursive verifier release authority manifest mismatch")
        object.__setattr__(
            verifier,
            "_release_binding_config_digest",
            expected_release_binding_config_digest,
        )
        object.__setattr__(
            verifier,
            "_replay_manifest_sha256",
            binding.replay_manifest_sha256,
        )
        return verifier

    def verify_and_admit(
        self,
        *,
        state: RecursiveStarkAdmissionState,
        proof: Mapping[str, Any],
        recursive_input: Mapping[str, Any],
    ) -> RecursiveStarkAdmissionResult:
        """Verify one root and return a data-only exact-once decision."""

        authenticated_facts = self._verify_authenticated_root(
            proof=proof,
            recursive_input=recursive_input,
        )
        return _admit_authenticated_recursive_stark_root(
            state,
            authenticated_facts,
        )

    def verify_and_commit(
        self,
        *,
        store: SQLiteRecursiveStarkAdmissionStore,
        expected_cursor: DurableRecursiveStarkAdmissionCursor,
        proof: Mapping[str, Any],
        recursive_input: Mapping[str, Any],
    ) -> DurableRecursiveStarkAdmissionResult:
        """Verify once and transactionally commit replay indexes and outcome."""

        from src.integration.recursive_stark_admission_store import (
            SQLiteRecursiveStarkAdmissionStore,
        )

        if type(store) is not SQLiteRecursiveStarkAdmissionStore:
            raise TypeError("store must be exactly SQLiteRecursiveStarkAdmissionStore")
        self._require_durable_release_authority()
        authenticated_facts = self._verify_authenticated_root(
            proof=proof,
            recursive_input=recursive_input,
        )
        return store._commit_authenticated_recursive_stark_root(
            expected_cursor=expected_cursor,
            authenticated_root=authenticated_facts,
        )

    def _require_durable_release_authority(self) -> None:
        if self.executable_format is not RecursiveVerifierExecutableFormat.STATIC_ELF_X86_64:
            raise RecursiveStarkVerificationError(
                "durable recursive admission requires a static ELF verifier"
            )
        if self._release_binding_config_digest is None or self._replay_manifest_sha256 is None:
            raise RecursiveStarkVerificationError(
                "durable recursive admission requires a governed release binding"
            )

    def _verify_authenticated_root(
        self,
        *,
        proof: Mapping[str, Any],
        recursive_input: Mapping[str, Any],
    ) -> _AuthenticatedRecursiveStarkRootFacts:
        """Execute the pinned verifier once and mint one private authenticated value."""

        trusted_expectations = json.loads(self._trusted_expectations_json)
        request = _verification_request(
            proof=proof,
            recursive_input=recursive_input,
            trusted_expectations=trusted_expectations,
        )
        request_bytes = _bounded_canonical_json_bytes(request, "verification request")
        request_sha256 = hashlib.sha256(request_bytes).hexdigest()
        try:
            stdout = execute_pinned_verifier_once(
                executable=self.executable,
                expected_sha256=self.sha256,
                executable_format=VerifierExecutableFormatV1(self.executable_format.value),
                request_bytes=request_bytes,
                timeout_seconds=self.timeout_seconds,
                max_address_space_bytes=self.max_address_space_bytes,
                max_stack_bytes=self.max_stack_bytes,
                max_stdout_bytes=MAX_VERIFIER_STDOUT_BYTES,
                max_stderr_bytes=MAX_VERIFIER_STDERR_BYTES,
            )
        except PinnedVerifierProcessError as exc:
            raise _recursive_process_error(exc) from exc
        try:
            payload = json.loads(
                stdout,
                object_pairs_hook=_reject_duplicate_object_keys,
                parse_constant=_reject_json_constant,
            )
        except (UnicodeDecodeError, json.JSONDecodeError, ValueError) as exc:
            raise RecursiveStarkVerificationError(
                "recursive verifier stdout must be one JSON object"
            ) from exc
        facts = parse_recursive_stark_root_facts(
            payload,
            trusted_expectations=trusted_expectations,
        )
        policy = _trusted_policy(trusted_expectations)
        provenance = _RecursiveStarkVerificationProvenance(
            authority_manifest_sha256=self.authority_manifest_sha256,
            verifier_executable_sha256=self.sha256,
            verification_request_sha256=request_sha256,
            release_binding_config_digest=self._release_binding_config_digest,
            replay_manifest_sha256=self._replay_manifest_sha256,
        )
        return _mint_recursive_stark_root_facts_after_verification(
            facts,
            policy,
            provenance,
        )


def _recursive_process_error(
    error: PinnedVerifierProcessError,
) -> RecursiveStarkVerificationError:
    if error.reason is PinnedVerifierProcessFailure.EXECUTABLE_HASH_MISMATCH:
        return RecursiveStarkVerificationError("recursive verifier binary hash mismatch")
    if error.reason is PinnedVerifierProcessFailure.TIMEOUT:
        return RecursiveStarkVerificationError("recursive verifier timed out")
    if error.reason is PinnedVerifierProcessFailure.EXECUTABLE_INVALID:
        return RecursiveStarkVerificationError(
            f"recursive verifier executable invalid: {error.detail}"
        )
    if error.reason is PinnedVerifierProcessFailure.OUTPUT_INVALID:
        detail = error.detail.replace("verifier stdout exceeds byte limit", "stdout exceeds limit")
        return RecursiveStarkVerificationError(f"recursive verifier {detail}")
    return RecursiveStarkVerificationError(
        f"recursive verifier process failed: {error.detail}"
    )


def recursive_stark_authority_manifest_bytes_v1(
    *,
    executable_sha256: str,
    trusted_expectations: Mapping[str, Any],
    executable_format: RecursiveVerifierExecutableFormat = (
        RecursiveVerifierExecutableFormat.STATIC_ELF_X86_64
    ),
) -> bytes:
    """Build canonical bytes for a separately governed authority record."""

    if len(executable_sha256) != 64 or any(
        char not in "0123456789abcdef" for char in executable_sha256
    ):
        raise ValueError("recursive verifier sha256 must be lowercase 64-character hex")
    if not isinstance(executable_format, RecursiveVerifierExecutableFormat):
        raise ValueError("recursive verifier executable_format unsupported")
    expectations_bytes = _bounded_canonical_json_bytes(
        trusted_expectations,
        "trusted expectations",
    )
    expectations = json.loads(expectations_bytes)
    if not isinstance(expectations, dict):
        raise ValueError("recursive verifier trusted_expectations must be an object")
    raw = _canonical_json_bytes(
        {
            "schema": AUTHORITY_MANIFEST_SCHEMA_V1,
            "executable_sha256": executable_sha256,
            "executable_format": executable_format.value,
            "trusted_expectations": expectations,
        }
    )
    if len(raw) > MAX_AUTHORITY_MANIFEST_BYTES:
        raise ValueError(
            f"recursive verifier authority manifest exceeds {MAX_AUTHORITY_MANIFEST_BYTES} bytes"
        )
    return raw


def _parse_authority_manifest_v1(
    raw: bytes,
    *,
    expected_sha256: str,
) -> tuple[str, RecursiveVerifierExecutableFormat, bytes]:
    if not isinstance(raw, bytes):
        raise ValueError("recursive verifier authority manifest must be bytes")
    if len(raw) > MAX_AUTHORITY_MANIFEST_BYTES:
        raise ValueError(
            f"recursive verifier authority manifest exceeds {MAX_AUTHORITY_MANIFEST_BYTES} bytes"
        )
    if hashlib.sha256(raw).hexdigest() != expected_sha256:
        raise ValueError("recursive verifier authority manifest hash mismatch")
    try:
        manifest = json.loads(
            raw.decode("ascii"),
            object_pairs_hook=_reject_duplicate_object_keys,
            parse_float=_reject_authority_float,
            parse_constant=_reject_json_constant,
        )
    except (UnicodeDecodeError, json.JSONDecodeError, ValueError) as exc:
        raise ValueError("recursive verifier authority manifest must be canonical JSON") from exc
    if not isinstance(manifest, dict) or set(manifest) != {
        "schema",
        "executable_sha256",
        "executable_format",
        "trusted_expectations",
    }:
        raise ValueError("recursive verifier authority manifest schema mismatch")
    if manifest.get("schema") != AUTHORITY_MANIFEST_SCHEMA_V1:
        raise ValueError("recursive verifier authority manifest schema mismatch")
    if _canonical_json_bytes(manifest) != raw:
        raise ValueError("recursive verifier authority manifest must be canonical JSON")
    executable_sha256 = manifest.get("executable_sha256")
    if (
        not isinstance(executable_sha256, str)
        or len(executable_sha256) != 64
        or any(char not in "0123456789abcdef" for char in executable_sha256)
    ):
        raise ValueError("recursive verifier authority executable_sha256 invalid")
    try:
        executable_format = RecursiveVerifierExecutableFormat(manifest.get("executable_format"))
    except (TypeError, ValueError) as exc:
        raise ValueError("recursive verifier authority executable_format unsupported") from exc
    expectations = manifest.get("trusted_expectations")
    if not isinstance(expectations, dict):
        raise ValueError("recursive verifier authority trusted_expectations must be an object")
    expectations_bytes = _bounded_canonical_json_bytes(
        expectations,
        "trusted expectations",
    )
    return executable_sha256, executable_format, expectations_bytes


def _reject_authority_float(value: str) -> object:
    raise ValueError(f"authority manifest float is forbidden: {value}")


def parse_recursive_stark_root_facts(
    payload: object,
    *,
    trusted_expectations: Mapping[str, Any],
) -> RecursiveStarkRootFacts:
    """Parse strict shaped facts without authenticating verifier provenance."""

    response = _mapping(payload, "recursive verifier response")
    if set(response) != {"ok", "verified_recursive_facts"}:
        raise RecursiveStarkVerificationError("recursive verifier response schema mismatch")
    if response.get("ok") is not True:
        raise RecursiveStarkVerificationError("recursive verifier did not accept proof")
    facts = _mapping(response.get("verified_recursive_facts"), "verified_recursive_facts")
    if set(facts) != _FACT_KEYS:
        raise RecursiveStarkVerificationError("verified_recursive_facts schema mismatch")
    if facts.get("schema") != VERIFIED_FACTS_SCHEMA_V1:
        raise RecursiveStarkVerificationError("verified_recursive_facts schema unsupported")
    if facts.get("receipt_kind") != "succinct":
        raise RecursiveStarkVerificationError("verified recursive receipt kind mismatch")

    _expect_equal(facts, trusted_expectations, "aggregate_image_id", "risc0_image_id")
    _expect_equal(facts, trusted_expectations, "receipt_codec", "receipt_codec")
    _expect_equal(facts, trusted_expectations, "receipt_kind", "receipt_kind")
    _expect_equal(facts, trusted_expectations, "receipt_hashfn", "receipt_hashfn")
    for key in ("receipt_verifier_parameters", "receipt_control_id"):
        _expect_same_hash(facts, trusted_expectations, key)
    for key in ("chain_id", "epoch_id", "proof_profile"):
        _expect_equal(facts, trusted_expectations, key, key)
    for key in (
        "verifier_set_root",
        "public_policy_hash",
        "child_verification_claims_root",
        "accepted_receipts_root",
        "cross_shard_message_ids_root",
    ):
        _expect_same_hash(facts, trusted_expectations, key)

    return RecursiveStarkRootFacts(
        chain_id=_str(facts, "chain_id"),
        epoch_id=_int(facts, "epoch_id"),
        proof_profile=_str(facts, "proof_profile"),
        root_journal_hash=_str(facts, "root_journal_hash"),
        verifier_set_root=_str(facts, "verifier_set_root"),
        public_policy_hash=_str(facts, "public_policy_hash"),
        child_verification_claim_hashes=_str_tuple(facts, "child_verification_claim_hashes"),
        child_verification_claims_root=_str(facts, "child_verification_claims_root"),
        accepted_receipt_ids=_str_tuple(facts, "accepted_receipt_ids"),
        accepted_receipts_root=_str(facts, "accepted_receipts_root"),
        cross_shard_message_ids=_str_tuple(facts, "cross_shard_message_ids"),
        cross_shard_message_ids_root=_str(facts, "cross_shard_message_ids_root"),
    )


def _verification_request(
    *,
    proof: Mapping[str, Any],
    recursive_input: Mapping[str, Any],
    trusted_expectations: Mapping[str, Any],
) -> dict[str, Any]:
    post_state_root = trusted_expectations.get("post_state_root")
    if not isinstance(post_state_root, str):
        raise RecursiveStarkVerificationError(
            "trusted_expectations.post_state_root must be a string"
        )
    return {
        "schema": "tau_state_proof_verify",
        "schema_version": 1,
        "state_hash": post_state_root,
        "proof": _canonical_copy(proof),
        "recursive_input": _canonical_copy(recursive_input),
        "recursive_expectations": _canonical_copy(trusted_expectations),
    }


def _trusted_policy(
    trusted_expectations: Mapping[str, Any],
) -> TrustedRecursiveStarkAdmissionPolicy:
    return TrustedRecursiveStarkAdmissionPolicy(
        expected_chain_id=_expectation_str(trusted_expectations, "chain_id"),
        expected_epoch_id=_expectation_int(trusted_expectations, "epoch_id"),
        expected_proof_profile=_expectation_str(trusted_expectations, "proof_profile"),
        expected_verifier_set_root=_prefixed_hash(
            _expectation_str(trusted_expectations, "verifier_set_root")
        ),
        expected_public_policy_hash=_prefixed_hash(
            _expectation_str(trusted_expectations, "public_policy_hash")
        ),
    )


def _expect_equal(
    facts: Mapping[str, Any],
    expectations: Mapping[str, Any],
    facts_key: str,
    expectation_key: str,
) -> None:
    if facts.get(facts_key) != expectations.get(expectation_key):
        raise RecursiveStarkVerificationError(
            f"verified_recursive_facts.{facts_key} trusted expectation mismatch"
        )


def _expect_same_hash(
    facts: Mapping[str, Any],
    expectations: Mapping[str, Any],
    key: str,
) -> None:
    fact = facts.get(key)
    expected = expectations.get(key)
    if not isinstance(fact, str) or not isinstance(expected, str):
        raise RecursiveStarkVerificationError(f"{key} must be a hex string")
    if _prefixed_hash(fact) != _prefixed_hash(expected):
        raise RecursiveStarkVerificationError(
            f"verified_recursive_facts.{key} trusted expectation mismatch"
        )


def _prefixed_hash(value: str) -> str:
    normalized = value.removeprefix("0x")
    if len(normalized) != 64 or any(c not in "0123456789abcdef" for c in normalized):
        raise RecursiveStarkVerificationError("hash must be lowercase 32-byte hex")
    return "0x" + normalized


def _mapping(value: object, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise RecursiveStarkVerificationError(f"{name} must be an object")
    return value


def _str(values: Mapping[str, Any], key: str) -> str:
    value = values.get(key)
    if not isinstance(value, str):
        raise RecursiveStarkVerificationError(f"verified_recursive_facts.{key} must be a string")
    return value


def _int(values: Mapping[str, Any], key: str) -> int:
    value = values.get(key)
    if not isinstance(value, int) or isinstance(value, bool):
        raise RecursiveStarkVerificationError(f"verified_recursive_facts.{key} must be an int")
    return value


def _str_tuple(values: Mapping[str, Any], key: str) -> tuple[str, ...]:
    value = values.get(key)
    if not isinstance(value, list) or any(not isinstance(item, str) for item in value):
        raise RecursiveStarkVerificationError(
            f"verified_recursive_facts.{key} must be a string list"
        )
    return tuple(value)


def _expectation_str(values: Mapping[str, Any], key: str) -> str:
    value = values.get(key)
    if not isinstance(value, str):
        raise RecursiveStarkVerificationError(f"trusted_expectations.{key} must be a string")
    return value


def _expectation_int(values: Mapping[str, Any], key: str) -> int:
    value = values.get(key)
    if not isinstance(value, int) or isinstance(value, bool):
        raise RecursiveStarkVerificationError(f"trusted_expectations.{key} must be an int")
    return value


def _canonical_copy(value: Mapping[str, Any]) -> dict[str, Any]:
    try:
        copied = json.loads(_bounded_canonical_json_bytes(value, "verification input"))
    except RecursiveStarkVerificationError:
        raise
    except (TypeError, ValueError, json.JSONDecodeError, RecursionError) as exc:
        raise RecursiveStarkVerificationError("verification input must be canonical JSON") from exc
    if not isinstance(copied, dict):
        raise RecursiveStarkVerificationError("verification input must be a JSON object")
    return copied


def _canonical_json_bytes(value: object) -> bytes:
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
        allow_nan=False,
    ).encode("ascii")


def _bounded_canonical_json_bytes(value: object, label: str) -> bytes:
    try:
        encoded = _canonical_json_bytes(value)
    except (TypeError, ValueError, RecursionError) as exc:
        raise RecursiveStarkVerificationError(f"{label} must be canonical JSON") from exc
    if len(encoded) > MAX_VERIFIER_REQUEST_BYTES:
        raise RecursiveStarkVerificationError(
            f"{label} exceeds {MAX_VERIFIER_REQUEST_BYTES} byte limit"
        )
    return encoded


def _reject_duplicate_object_keys(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _reject_json_constant(value: str) -> None:
    raise ValueError(f"invalid JSON constant: {value}")
