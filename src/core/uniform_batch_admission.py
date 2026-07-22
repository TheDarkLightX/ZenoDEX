"""Deterministic admission certificates for scoped UPBA batches.

This module does not choose global mempool policy. It verifies one local policy:
given a homogeneous eligible swap set for one supported UPBA pool, admitted
intents are the canonical intent-id prefix up to a fixed cap.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping, Sequence

from ..state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex
from ..state.immutable_collections import deep_thaw_json
from ..state.intents import Intent, IntentKind
from .domain_limits import DEX_SWAP_AMOUNT_MAX
from .uniform_batch_clearing import (
    UNIFORM_BATCH_MAX_FILLS,
    UNIFORM_BATCH_OUTPUT_AMOUNT_MAX,
    uniform_batch_intent_set_hash,
)

UNIFORM_BATCH_ADMISSION_CERTIFICATE_SCHEMA_V1 = "zenodex/uniform_batch_admission_certificate/v1"
UNIFORM_BATCH_ADMISSION_INTENT_SET_SCHEMA_V1 = "zenodex/uniform_batch_admission_intent_set/v1"
UNIFORM_BATCH_ADMISSION_POLICY_V1_ID = "zenodex/upba_admission_v1/canonical_intent_id_prefix"
UNIFORM_BATCH_ADMISSION_MAX_ELIGIBLE = 1024

_ADMISSION_CERTIFICATE_KEYS = frozenset(
    {
        "schema",
        "policy_id",
        "pool_id",
        "max_admitted",
        "eligible_count",
        "admitted_count",
        "overflow_count",
        "eligible_intent_set_hash",
        "admitted_intent_set_hash",
        "overflow_intent_set_hash",
    }
)


@dataclass(frozen=True)
class UniformBatchAdmissionCertificateV1:
    pool_id: str
    max_admitted: int
    eligible_count: int
    admitted_count: int
    overflow_count: int
    eligible_intent_set_hash: str
    admitted_intent_set_hash: str
    overflow_intent_set_hash: str
    policy_id: str = UNIFORM_BATCH_ADMISSION_POLICY_V1_ID
    schema: str = UNIFORM_BATCH_ADMISSION_CERTIFICATE_SCHEMA_V1

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "policy_id": self.policy_id,
            "pool_id": self.pool_id,
            "max_admitted": int(self.max_admitted),
            "eligible_count": int(self.eligible_count),
            "admitted_count": int(self.admitted_count),
            "overflow_count": int(self.overflow_count),
            "eligible_intent_set_hash": self.eligible_intent_set_hash,
            "admitted_intent_set_hash": self.admitted_intent_set_hash,
            "overflow_intent_set_hash": self.overflow_intent_set_hash,
        }

    @classmethod
    def from_obj(cls, obj: Mapping[str, Any]) -> "UniformBatchAdmissionCertificateV1":
        _reject_unknown_keys(obj, allowed=_ADMISSION_CERTIFICATE_KEYS, name="admission.certificate")
        schema = _require_str(obj.get("schema"), name="admission.schema")
        if schema != UNIFORM_BATCH_ADMISSION_CERTIFICATE_SCHEMA_V1:
            raise ValueError("unsupported uniform batch admission certificate schema")
        policy_id = _require_str(obj.get("policy_id"), name="admission.policy_id")
        if policy_id != UNIFORM_BATCH_ADMISSION_POLICY_V1_ID:
            raise ValueError("unsupported uniform batch admission policy_id")
        return cls(
            pool_id=_require_str(obj.get("pool_id"), name="admission.pool_id"),
            max_admitted=_require_positive_int(
                obj.get("max_admitted"),
                name="admission.max_admitted",
                maximum=UNIFORM_BATCH_MAX_FILLS,
            ),
            eligible_count=_require_nonnegative_int(
                obj.get("eligible_count"),
                name="admission.eligible_count",
                maximum=UNIFORM_BATCH_ADMISSION_MAX_ELIGIBLE,
            ),
            admitted_count=_require_nonnegative_int(
                obj.get("admitted_count"),
                name="admission.admitted_count",
                maximum=UNIFORM_BATCH_MAX_FILLS,
            ),
            overflow_count=_require_nonnegative_int(
                obj.get("overflow_count"),
                name="admission.overflow_count",
                maximum=UNIFORM_BATCH_ADMISSION_MAX_ELIGIBLE,
            ),
            eligible_intent_set_hash=_require_sha256_hex(
                obj.get("eligible_intent_set_hash"),
                name="admission.eligible_intent_set_hash",
            ),
            admitted_intent_set_hash=_require_sha256_hex(
                obj.get("admitted_intent_set_hash"),
                name="admission.admitted_intent_set_hash",
            ),
            overflow_intent_set_hash=_require_sha256_hex(
                obj.get("overflow_intent_set_hash"),
                name="admission.overflow_intent_set_hash",
            ),
            policy_id=policy_id,
            schema=schema,
        )

    def hash(self) -> str:
        return uniform_batch_admission_certificate_hash(self)


@dataclass(frozen=True)
class UniformBatchAdmissionSelectionV1:
    admitted: tuple[Intent, ...]
    overflow: tuple[Intent, ...]


@dataclass(frozen=True)
class UniformBatchAdmissionVerificationResult:
    ok: bool
    error: str | None
    admitted: tuple[Intent, ...] = ()
    overflow: tuple[Intent, ...] = ()
    certificate_hash: str | None = None

    def __post_init__(self) -> None:
        if not isinstance(self.ok, bool):
            raise ValueError("ok must be bool")
        if not isinstance(self.admitted, tuple) or not isinstance(self.overflow, tuple):
            raise ValueError("admitted and overflow must be tuples")
        if self.ok:
            if self.error is not None:
                raise ValueError("accepted admission result cannot include error")
            try:
                _require_sha256_hex(
                    self.certificate_hash,
                    name="admission.result.certificate_hash",
                )
            except (TypeError, ValueError) as exc:
                raise ValueError(str(exc)) from exc
            return

        if not isinstance(self.error, str) or not self.error:
            raise ValueError("rejected admission result must include an error")
        if self.admitted or self.overflow or self.certificate_hash is not None:
            raise ValueError("rejected admission result cannot include accepted artifacts")


def uniform_batch_admission_certificate_hash(
    certificate: UniformBatchAdmissionCertificateV1 | Mapping[str, Any],
) -> str:
    parsed = (
        certificate
        if isinstance(certificate, UniformBatchAdmissionCertificateV1)
        else UniformBatchAdmissionCertificateV1.from_obj(_require_mapping(certificate, name="admission.certificate"))
    )
    _validate_admission_certificate_shape(parsed)
    return sha256_hex(
        domain_sep_bytes("uniform_batch_admission_certificate", version=1)
        + canonical_json_bytes(parsed.to_dict())
    )


def uniform_batch_admission_intent_set_hash_v1(intents: Sequence[Intent]) -> str:
    _validate_eligible_intent_count(intents)
    entries = [_admission_intent_entry(intent) for intent in intents]
    _require_unique_intent_ids(entries)
    entries.sort(key=lambda entry: entry["intent_id"])
    body = {
        "schema": UNIFORM_BATCH_ADMISSION_INTENT_SET_SCHEMA_V1,
        "intents": entries,
    }
    return sha256_hex(
        domain_sep_bytes("uniform_batch_admission_intent_set", version=1)
        + canonical_json_bytes(body)
    )


def select_uniform_batch_admitted_intents_v1(
    *,
    eligible_intents: Sequence[Intent],
    pool_id: str,
    max_admitted: int = UNIFORM_BATCH_MAX_FILLS,
) -> UniformBatchAdmissionSelectionV1:
    _require_str(pool_id, name="pool_id")
    max_admitted = _require_positive_int(
        max_admitted,
        name="max_admitted",
        maximum=UNIFORM_BATCH_MAX_FILLS,
    )
    _validate_eligible_intent_count(eligible_intents)
    kind: IntentKind | None = None
    asset_pair: frozenset[str] | None = None
    for intent in eligible_intents:
        _validate_supported_admission_intent(intent, pool_id=pool_id)
        if kind is None:
            kind = intent.kind
        elif intent.kind != kind:
            raise ValueError("uniform batch admission requires homogeneous swap kind")
        current_pair = frozenset((str(intent.get_field("asset_in")), str(intent.get_field("asset_out"))))
        if asset_pair is None:
            asset_pair = current_pair
        elif current_pair != asset_pair:
            raise ValueError("uniform batch admission requires one asset pair")
    sorted_intents = tuple(sorted(eligible_intents, key=lambda intent: intent.intent_id))
    _require_unique_intent_ids([_admission_intent_entry(intent) for intent in sorted_intents])
    return UniformBatchAdmissionSelectionV1(
        admitted=sorted_intents[:max_admitted],
        overflow=sorted_intents[max_admitted:],
    )


def build_uniform_batch_admission_certificate_v1(
    *,
    eligible_intents: Sequence[Intent],
    pool_id: str,
    max_admitted: int = UNIFORM_BATCH_MAX_FILLS,
) -> UniformBatchAdmissionCertificateV1:
    selection = select_uniform_batch_admitted_intents_v1(
        eligible_intents=eligible_intents,
        pool_id=pool_id,
        max_admitted=max_admitted,
    )
    certificate = UniformBatchAdmissionCertificateV1(
        pool_id=pool_id,
        max_admitted=max_admitted,
        eligible_count=len(eligible_intents),
        admitted_count=len(selection.admitted),
        overflow_count=len(selection.overflow),
        eligible_intent_set_hash=uniform_batch_admission_intent_set_hash_v1(eligible_intents),
        admitted_intent_set_hash=uniform_batch_intent_set_hash(selection.admitted),
        overflow_intent_set_hash=uniform_batch_admission_intent_set_hash_v1(selection.overflow),
    )
    _validate_admission_certificate_shape(certificate)
    return certificate


def verify_uniform_batch_admission_certificate_v1(
    *,
    eligible_intents: Sequence[Intent],
    admitted_intents: Sequence[Intent],
    certificate: UniformBatchAdmissionCertificateV1 | Mapping[str, Any],
) -> UniformBatchAdmissionVerificationResult:
    try:
        parsed = (
            certificate
            if isinstance(certificate, UniformBatchAdmissionCertificateV1)
            else UniformBatchAdmissionCertificateV1.from_obj(
                _require_mapping(certificate, name="admission.certificate")
            )
        )
        _validate_admission_certificate_shape(parsed)
        selection = select_uniform_batch_admitted_intents_v1(
            eligible_intents=eligible_intents,
            pool_id=parsed.pool_id,
            max_admitted=parsed.max_admitted,
        )
        expected_admitted_ids = [intent.intent_id for intent in selection.admitted]
        admitted_ids = [intent.intent_id for intent in sorted(admitted_intents, key=lambda intent: intent.intent_id)]
        if admitted_ids != expected_admitted_ids:
            raise ValueError("admission certificate admitted intent set mismatch")
        if parsed.eligible_count != len(eligible_intents):
            raise ValueError("admission certificate eligible_count mismatch")
        if parsed.admitted_count != len(selection.admitted):
            raise ValueError("admission certificate admitted_count mismatch")
        if parsed.overflow_count != len(selection.overflow):
            raise ValueError("admission certificate overflow_count mismatch")
        if parsed.eligible_intent_set_hash != uniform_batch_admission_intent_set_hash_v1(eligible_intents):
            raise ValueError("admission certificate eligible_intent_set_hash mismatch")
        if parsed.admitted_intent_set_hash != uniform_batch_intent_set_hash(admitted_intents):
            raise ValueError("admission certificate provided admitted_intent_set_hash mismatch")
        if parsed.admitted_intent_set_hash != uniform_batch_intent_set_hash(selection.admitted):
            raise ValueError("admission certificate admitted_intent_set_hash mismatch")
        if parsed.overflow_intent_set_hash != uniform_batch_admission_intent_set_hash_v1(selection.overflow):
            raise ValueError("admission certificate overflow_intent_set_hash mismatch")
        return UniformBatchAdmissionVerificationResult(
            ok=True,
            error=None,
            admitted=selection.admitted,
            overflow=selection.overflow,
            certificate_hash=parsed.hash(),
        )
    except (TypeError, ValueError) as exc:
        return UniformBatchAdmissionVerificationResult(ok=False, error=str(exc))


def _admission_intent_entry(intent: Intent) -> dict[str, Any]:
    if not isinstance(intent.kind, IntentKind):
        raise TypeError("intent.kind must be an IntentKind")
    fields = intent.fields if isinstance(intent.fields, Mapping) else {}
    return {
        "module": _require_str(intent.module, name="intent.module"),
        "version": _require_str(intent.version, name="intent.version"),
        "kind": intent.kind.value,
        "intent_id": _require_str(intent.intent_id, name="intent.intent_id"),
        "sender_pubkey": _require_str(intent.sender_pubkey, name="intent.sender_pubkey"),
        "deadline": _require_nonnegative_int(intent.deadline, name="intent.deadline"),
        "salt": intent.salt,
        "fields": deep_thaw_json(fields),
    }


def _validate_supported_admission_intent(intent: Intent, *, pool_id: str) -> None:
    if intent.kind not in (IntentKind.SWAP_EXACT_IN, IntentKind.SWAP_EXACT_OUT):
        raise ValueError("uniform batch admission supports SWAP_EXACT_IN or SWAP_EXACT_OUT only")
    if str(intent.get_field("pool_id")) != pool_id:
        raise ValueError("uniform batch admission intent pool_id mismatch")
    asset_in = str(intent.get_field("asset_in"))
    asset_out = str(intent.get_field("asset_out"))
    if asset_in == asset_out:
        raise ValueError("uniform batch admission intent assets must differ")
    if intent.kind == IntentKind.SWAP_EXACT_IN:
        amount_in = intent.get_field("amount_in")
        min_amount_out = intent.get_field("min_amount_out")
        if (
            not isinstance(amount_in, int)
            or isinstance(amount_in, bool)
            or amount_in <= 0
            or amount_in > DEX_SWAP_AMOUNT_MAX
        ):
            raise ValueError("uniform batch admission amount_in must be positive")
        if (
            not isinstance(min_amount_out, int)
            or isinstance(min_amount_out, bool)
            or min_amount_out < 0
            or min_amount_out > UNIFORM_BATCH_OUTPUT_AMOUNT_MAX
        ):
            raise ValueError("uniform batch admission min_amount_out must be non-negative")
        return
    amount_out = intent.get_field("amount_out")
    max_amount_in = intent.get_field("max_amount_in")
    if (
        not isinstance(amount_out, int)
        or isinstance(amount_out, bool)
        or amount_out <= 0
        or amount_out > DEX_SWAP_AMOUNT_MAX
    ):
        raise ValueError("uniform batch admission amount_out must be positive")
    if (
        not isinstance(max_amount_in, int)
        or isinstance(max_amount_in, bool)
        or max_amount_in < 0
        or max_amount_in > DEX_SWAP_AMOUNT_MAX
    ):
        raise ValueError("uniform batch admission max_amount_in must be non-negative")


def _validate_admission_certificate_shape(certificate: UniformBatchAdmissionCertificateV1) -> None:
    if certificate.schema != UNIFORM_BATCH_ADMISSION_CERTIFICATE_SCHEMA_V1:
        raise ValueError("unsupported uniform batch admission certificate schema")
    if certificate.policy_id != UNIFORM_BATCH_ADMISSION_POLICY_V1_ID:
        raise ValueError("unsupported uniform batch admission policy_id")
    _require_str(certificate.pool_id, name="admission.pool_id")
    _require_positive_int(
        certificate.max_admitted,
        name="admission.max_admitted",
        maximum=UNIFORM_BATCH_MAX_FILLS,
    )
    _require_nonnegative_int(
        certificate.eligible_count,
        name="admission.eligible_count",
        maximum=UNIFORM_BATCH_ADMISSION_MAX_ELIGIBLE,
    )
    _require_nonnegative_int(
        certificate.admitted_count,
        name="admission.admitted_count",
        maximum=UNIFORM_BATCH_MAX_FILLS,
    )
    _require_nonnegative_int(
        certificate.overflow_count,
        name="admission.overflow_count",
        maximum=UNIFORM_BATCH_ADMISSION_MAX_ELIGIBLE,
    )
    if certificate.admitted_count > certificate.max_admitted:
        raise ValueError("admission certificate admitted_count exceeds max_admitted")
    if certificate.eligible_count != certificate.admitted_count + certificate.overflow_count:
        raise ValueError("admission certificate counts do not add up")
    _require_sha256_hex(certificate.eligible_intent_set_hash, name="admission.eligible_intent_set_hash")
    _require_sha256_hex(certificate.admitted_intent_set_hash, name="admission.admitted_intent_set_hash")
    _require_sha256_hex(certificate.overflow_intent_set_hash, name="admission.overflow_intent_set_hash")


def _validate_eligible_intent_count(intents: object) -> None:
    if not isinstance(intents, Sequence) or isinstance(intents, (str, bytes, bytearray)):
        raise TypeError("eligible_intents must be a sequence")
    if len(intents) > UNIFORM_BATCH_ADMISSION_MAX_ELIGIBLE:
        raise ValueError(f"eligible_intents exceeds maximum length {UNIFORM_BATCH_ADMISSION_MAX_ELIGIBLE}")


def _require_unique_intent_ids(entries: Sequence[Mapping[str, Any]]) -> None:
    ids = [str(entry["intent_id"]) for entry in entries]
    if len(ids) != len(set(ids)):
        raise ValueError("duplicate admission intent_id")


def _require_mapping(value: Any, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be an object")
    return value


def _reject_unknown_keys(value: Mapping[str, Any], *, allowed: frozenset[str], name: str) -> None:
    unknown = sorted(set(value) - set(allowed))
    if unknown:
        joined = ", ".join(unknown)
        raise ValueError(f"{name} contains unsupported keys: {joined}")


def _require_str(value: Any, *, name: str) -> str:
    if not isinstance(value, str) or not value:
        raise TypeError(f"{name} must be a non-empty string")
    return str(value)


def _require_sha256_hex(value: Any, *, name: str) -> str:
    parsed = _require_str(value, name=name)
    if (
        len(parsed) != 66
        or not parsed.startswith("0x")
        or any(char not in "0123456789abcdef" for char in parsed[2:])
    ):
        raise ValueError(f"{name} must be 0x-prefixed lowercase sha256 hex")
    return parsed


def _require_nonnegative_int(value: Any, *, name: str, maximum: int | None = None) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    if value < 0:
        raise ValueError(f"{name} must be non-negative")
    if maximum is not None and value > maximum:
        raise ValueError(f"{name} exceeds maximum")
    return int(value)


def _require_positive_int(value: Any, *, name: str, maximum: int | None = None) -> int:
    value_int = _require_nonnegative_int(value, name=name, maximum=maximum)
    if value_int <= 0:
        raise ValueError(f"{name} must be positive")
    return value_int
