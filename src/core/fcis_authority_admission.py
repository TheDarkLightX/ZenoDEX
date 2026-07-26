"""Closed admission and canonical encoding for untrusted M5 claim data.

Successful admission proves structural validity only.  It does not create a
transition, receipt, bundle, or commit authority witness.  M5 derivation must
recompute those values from one exact evaluator lineage.
"""

from __future__ import annotations

from dataclasses import InitVar, dataclass
from typing import TypeAlias, final

from ..state.owned_json import AUTHORITY_GRAPH_ADMISSION_LIMITS_V1
from ..state.snapshot_combinators import AdmitCode, AdmitOk, AdmitReject
from ..state.state_admission_profile import _encode_admitted, admit
from ..state.state_snapshot_values import FCIS_STATE_SCHEMA_REVISION_V1
from .fcis_authority_schema import FCIS_AUTHORITY_SCHEMA_IDS_V1

_CANONICAL_AUTHORITY_CLAIM_BYTES_TOKEN_V1 = object()


@final
@dataclass(frozen=True, slots=True)
class CanonicalAuthorityClaimBytesV1:
    """Bytes produced by the sole closed encoder for one exact claim schema."""

    schema_id: str
    payload: bytes
    _construction_token: InitVar[object]

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _CANONICAL_AUTHORITY_CLAIM_BYTES_TOKEN_V1:
            raise TypeError("canonical claim bytes require the controlled encoder")
        if type(self.schema_id) is not str or self.schema_id not in FCIS_AUTHORITY_SCHEMA_IDS_V1:
            raise TypeError("canonical claim bytes require a known exact schema")
        if type(self.payload) is not bytes:
            raise TypeError("canonical claim payload must be exact bytes")


def _canonical_authority_claim_bytes_from_encoder_v1(
    schema_id: str,
    payload: bytes,
) -> CanonicalAuthorityClaimBytesV1:
    """Package bytes inside the only structurally permitted constructor site."""

    return CanonicalAuthorityClaimBytesV1(
        schema_id,
        payload,
        _CANONICAL_AUTHORITY_CLAIM_BYTES_TOKEN_V1,
    )


FCISAuthorityClaimAdmissionResultV1: TypeAlias = AdmitOk[object] | AdmitReject
FCISAuthorityClaimEncodingResultV1: TypeAlias = CanonicalAuthorityClaimBytesV1 | AdmitReject


def admit_fcis_authority_claim_v1(
    schema_id: str,
    source: object,
) -> FCISAuthorityClaimAdmissionResultV1:
    """Admit replay or verifier claim data through the sole closed profile."""

    if type(schema_id) is not str or schema_id not in FCIS_AUTHORITY_SCHEMA_IDS_V1:
        return AdmitReject(AdmitCode.UNSUPPORTED_VARIANT, ())
    return admit(
        FCIS_STATE_SCHEMA_REVISION_V1,
        schema_id,
        AUTHORITY_GRAPH_ADMISSION_LIMITS_V1,
        source,
    )


def encode_fcis_authority_claim_v1(
    schema_id: str,
    source: object,
) -> FCISAuthorityClaimEncodingResultV1:
    """Re-admit and encode one claim without minting commit authority."""

    admitted = admit_fcis_authority_claim_v1(schema_id, source)
    if type(admitted) is AdmitReject:
        return admitted
    if type(admitted) is not AdmitOk:
        return AdmitReject(AdmitCode.DOMAIN_INVARIANT, ())
    try:
        payload = _encode_admitted(
            FCIS_STATE_SCHEMA_REVISION_V1,
            schema_id,
            AUTHORITY_GRAPH_ADMISSION_LIMITS_V1,
            admitted.value,
        )
    except (TypeError, ValueError):
        return AdmitReject(AdmitCode.DOMAIN_INVARIANT, ())
    return _canonical_authority_claim_bytes_from_encoder_v1(schema_id, payload)


__all__ = (
    "CanonicalAuthorityClaimBytesV1",
    "FCISAuthorityClaimAdmissionResultV1",
    "FCISAuthorityClaimEncodingResultV1",
    "admit_fcis_authority_claim_v1",
    "encode_fcis_authority_claim_v1",
)
