"""Integration helpers for TEE attestation summaries.

These helpers intentionally stop at deterministic normalization.
Signature verification, certificate-path validation, and JWT/COSE verification are
external concerns; callers should only pass already-verified attestation payloads.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping, cast

from ..core.confidential_extension_receipts import (
    MAX_EPOCH,
    is_canonical_confidential_measurement,
    make_confidential_extension_receipt,
)
from ..state.canonical import canonical_hex_fixed_allow_0x


_NITRO_PCR_HEX_LEN = 96
_AZURE_HOSTDATA_HEX_LEN = 64


def _require_mapping(value: Any, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise ValueError(f"{name} must be a mapping")
    return value


def _require_nonempty_str(value: Any, *, name: str) -> str:
    if not isinstance(value, str) or not value:
        raise ValueError(f"{name} must be a non-empty string")
    return value


def _normalize_hex(value: Any, *, name: str, exact_length: int | None = None) -> str:
    s = _require_nonempty_str(value, name=name).strip().lower()
    if s.startswith("0x"):
        s = s[2:]
    if not s or any(ch not in "0123456789abcdef" for ch in s):
        raise ValueError(f"{name} must be hex")
    if exact_length is not None and len(s) != exact_length:
        raise ValueError(f"{name} must be {exact_length}-char hex")
    return s


def _require_bounded_epoch(value: Any, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0 or value > MAX_EPOCH:
        raise ValueError(f"{name} must be a bounded int")
    return value


@dataclass(frozen=True)
class VerifiedConfidentialAttestation:
    measurement: str
    policy_digest: str
    attestation_epoch: int

    def __post_init__(self) -> None:
        measurement = _require_nonempty_str(self.measurement, name="measurement")
        if not is_canonical_confidential_measurement(measurement):
            raise ValueError("measurement must be canonical")
        policy_digest = canonical_hex_fixed_allow_0x(self.policy_digest, nbytes=32, name="policy_digest")
        attestation_epoch = _require_bounded_epoch(self.attestation_epoch, name="attestation_epoch")
        object.__setattr__(self, "measurement", measurement)
        object.__setattr__(self, "policy_digest", policy_digest)
        object.__setattr__(self, "attestation_epoch", attestation_epoch)


def nitro_measurement_from_summary(summary: Mapping[str, Any]) -> str:
    """Build a stable allowlist key from a verified Nitro attestation summary.

    Expected shape:
    {
      "pcrs": {"0": "...", "8": "..."}
    }

    We bind to PCR0 (image hash) and PCR8 (signing cert fingerprint) because AWS
    documents PCR8 as useful for key-release / approval policy binding.
    """
    payload = _require_mapping(summary, name="summary")
    pcrs = _require_mapping(payload.get("pcrs"), name="pcrs")
    pcr_map = cast(Mapping[object, Any], pcrs)
    pcr0 = _normalize_hex(pcr_map.get("0") or pcr_map.get(0), name="pcr0", exact_length=_NITRO_PCR_HEX_LEN)
    pcr8 = _normalize_hex(pcr_map.get("8") or pcr_map.get(8), name="pcr8", exact_length=_NITRO_PCR_HEX_LEN)
    return f"nitro:pcr0:{pcr0}:pcr8:{pcr8}"


def azure_hostdata_measurement_from_claims(claims: Mapping[str, Any]) -> str:
    """Build a stable allowlist key from verified Azure Attestation claims.

    We use `x-ms-sevsnpvm-hostdata` because Microsoft documents it as the hash of
    the confidential container policy for ACI confidential containers.
    """
    payload = _require_mapping(claims, name="claims")
    attestation_type = _require_nonempty_str(payload.get("x-ms-attestation-type"), name="x-ms-attestation-type").strip().lower()
    if attestation_type != "sevsnpvm":
        raise ValueError("x-ms-attestation-type must be sevsnpvm")
    is_debuggable = payload.get("x-ms-sevsnpvm-is-debuggable")
    if is_debuggable not in (False, "false", "False", 0):
        raise ValueError("azure confidential container must not be debuggable")
    hostdata = _normalize_hex(
        payload.get("x-ms-sevsnpvm-hostdata"),
        name="x-ms-sevsnpvm-hostdata",
        exact_length=_AZURE_HOSTDATA_HEX_LEN,
    )
    return f"azure-sevsnp:hostdata:{hostdata}"


def attestation_epoch_from_unix_time(*, issued_at_s: int, epoch_length_s: int) -> int:
    if not isinstance(issued_at_s, int) or isinstance(issued_at_s, bool) or issued_at_s < 0:
        raise ValueError("issued_at_s must be a non-negative int")
    if not isinstance(epoch_length_s, int) or isinstance(epoch_length_s, bool) or epoch_length_s <= 0:
        raise ValueError("epoch_length_s must be a positive int")
    return issued_at_s // epoch_length_s


def make_confidential_extension_receipt_from_verified_attestation(
    *,
    verified_attestation: VerifiedConfidentialAttestation,
    extension_id: str,
    provider_id: str,
    request_id: str,
    policy_version: str,
    do_execute: int,
    policy_ok: int,
    nonce_unused: int,
    output_bound_ok: int,
    current_epoch: int,
    max_attestation_age: int,
    fee_charged: int,
    receipt_fee: int,
    credit_before: int,
    credit_after: int,
    provider_balance_before: int,
    provider_balance_after: int,
) -> dict[str, Any]:
    if not isinstance(verified_attestation, VerifiedConfidentialAttestation):
        raise TypeError("verified_attestation must be a VerifiedConfidentialAttestation")
    receipt = make_confidential_extension_receipt(
        extension_id=extension_id,
        provider_id=provider_id,
        request_id=request_id,
        policy_version=policy_version,
        policy_digest=verified_attestation.policy_digest,
        measurement=verified_attestation.measurement,
        do_execute=do_execute,
        policy_ok=policy_ok,
        nonce_unused=nonce_unused,
        output_bound_ok=output_bound_ok,
        current_epoch=current_epoch,
        attestation_epoch=verified_attestation.attestation_epoch,
        max_attestation_age=max_attestation_age,
        fee_charged=fee_charged,
        receipt_fee=receipt_fee,
        credit_before=credit_before,
        credit_after=credit_after,
        provider_balance_before=provider_balance_before,
        provider_balance_after=provider_balance_after,
    )
    receipt["_verified_attestation"] = verified_attestation
    return receipt


def make_confidential_extension_receipt_from_nitro(
    *,
    summary: Mapping[str, Any],
    extension_id: str,
    provider_id: str,
    request_id: str,
    policy_version: str,
    policy_digest: str,
    do_execute: int,
    policy_ok: int,
    nonce_unused: int,
    output_bound_ok: int,
    current_epoch: int,
    attestation_epoch: int,
    max_attestation_age: int,
    fee_charged: int,
    receipt_fee: int,
    credit_before: int,
    credit_after: int,
    provider_balance_before: int,
    provider_balance_after: int,
) -> dict[str, Any]:
    verified_attestation = VerifiedConfidentialAttestation(
        measurement=nitro_measurement_from_summary(summary),
        policy_digest=policy_digest,
        attestation_epoch=attestation_epoch,
    )
    return make_confidential_extension_receipt_from_verified_attestation(
        verified_attestation=verified_attestation,
        extension_id=extension_id,
        provider_id=provider_id,
        request_id=request_id,
        policy_version=policy_version,
        do_execute=do_execute,
        policy_ok=policy_ok,
        nonce_unused=nonce_unused,
        output_bound_ok=output_bound_ok,
        current_epoch=current_epoch,
        max_attestation_age=max_attestation_age,
        fee_charged=fee_charged,
        receipt_fee=receipt_fee,
        credit_before=credit_before,
        credit_after=credit_after,
        provider_balance_before=provider_balance_before,
        provider_balance_after=provider_balance_after,
    )


def make_confidential_extension_receipt_from_azure(
    *,
    claims: Mapping[str, Any],
    extension_id: str,
    provider_id: str,
    request_id: str,
    policy_version: str,
    policy_digest: str,
    do_execute: int,
    policy_ok: int,
    nonce_unused: int,
    output_bound_ok: int,
    current_epoch: int,
    attestation_epoch: int,
    max_attestation_age: int,
    fee_charged: int,
    receipt_fee: int,
    credit_before: int,
    credit_after: int,
    provider_balance_before: int,
    provider_balance_after: int,
) -> dict[str, Any]:
    verified_attestation = VerifiedConfidentialAttestation(
        measurement=azure_hostdata_measurement_from_claims(claims),
        policy_digest=policy_digest,
        attestation_epoch=attestation_epoch,
    )
    return make_confidential_extension_receipt_from_verified_attestation(
        verified_attestation=verified_attestation,
        extension_id=extension_id,
        provider_id=provider_id,
        request_id=request_id,
        policy_version=policy_version,
        do_execute=do_execute,
        policy_ok=policy_ok,
        nonce_unused=nonce_unused,
        output_bound_ok=output_bound_ok,
        current_epoch=current_epoch,
        max_attestation_age=max_attestation_age,
        fee_charged=fee_charged,
        receipt_fee=receipt_fee,
        credit_before=credit_before,
        credit_after=credit_after,
        provider_balance_before=provider_balance_before,
        provider_balance_after=provider_balance_after,
    )
