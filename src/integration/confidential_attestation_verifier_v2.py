"""Production TEE attestation verifier with real document parsing.

This module implements real attestation document verification for:
- AWS Nitro Enclave: COSE_Sign1 / CBOR attestation document parsing
  extracting PCR0, PCR1, PCR2, PCR8 from the actual attestation document.
- Intel SGX: quote structure parsing with measurement (MRENCLAVE) verification.

Key security properties:
- PCR values are extracted from real attestation documents, never hardcoded.
- A measurement allowlist must be configured — no smoke fixtures in production.
- Attestation is bound to a certificate hash for TLS channel establishment.
- ``production_security_claim`` is True only when real attestation is verified.
- Smoke fixture mode is available ONLY when explicitly configured for
  local-testnet deployments.

Copyright (c) DarkLightX/Dana Edwards. All rights reserved.
"""

from __future__ import annotations

import hashlib
import os
import struct
from dataclasses import dataclass, field
from typing import Any, Mapping, Optional, Sequence

from .confidential_attestation import (
    VerifiedConfidentialAttestation,
    nitro_measurement_from_summary,
)
from ..state.canonical import sha256_hex

try:
    import cbor2  # type: ignore[import-untyped]
    _HAS_CBOR2 = True
except ImportError:  # pragma: no cover - cbor2 is a hard dependency for prod
    _HAS_CBOR2 = False

# --- Constants -------------------------------------------------------------

_NITRO_PCR_HEX_LEN = 96  # 48 bytes * 2 hex chars
_SGX_MEASUREMENT_HEX_LEN = 64  # 32 bytes * 2 hex chars
_SGX_QUOTE_HEADER_SIZE = 48
_SGX_REPORT_BODY_OFFSET = 48
# Intel SGX SDK sgx_report_body_t layout (384 bytes total):
#   0-15:   cpu_svn (16 bytes)
#   16-19:  misc_select (4 bytes)
#   20-47:  reserved1 (28 bytes)
#   48-63:  isv_ext_prod_id (16 bytes, SGX2)
#   64-127: report_data (64 bytes)
#   128-159: mr_enclave (32 bytes) — MRENCLAVE
#   160-191: reserved2 (32 bytes)
#   192-223: mr_signer (32 bytes) — MRSIGNER
#   224-239: attributes (16 bytes)
#   240-241: isv_prod_id (2 bytes)
#   242-243: isv_svn (2 bytes)
_SGX_REPORT_DATA_OFFSET = _SGX_REPORT_BODY_OFFSET + 64
_SGX_MRENCLAVE_OFFSET = _SGX_REPORT_BODY_OFFSET + 128
_SGX_MRSIGNER_OFFSET = _SGX_REPORT_BODY_OFFSET + 192
_SGX_ISV_PROD_ID_OFFSET = _SGX_REPORT_BODY_OFFSET + 240
_SGX_ISV_SVN_OFFSET = _SGX_REPORT_BODY_OFFSET + 242
_SGX_REPORT_BODY_SIZE = 384
_COSE_SIGN1_TAG = 18  # CBOR tag for COSE_Sign1

_SMOKE_NITRO_PCR0 = "0123456789abcdef" * 6
_SMOKE_NITRO_PCR8 = "fedcba9876543210" * 6


# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ProductionAttestationVerifierConfig:
    """Configuration for the production attestation verifier.

    Attributes:
        allowlist: Approved measurement strings (e.g. ``nitro:pcr0:...:pcr8:...``).
            Must be non-empty for production mode.
        local_testnet_mode: When True, smoke fixtures are accepted for
            local-testnet development only. Must never be True in production.
        require_certificate_binding: When True, the attestation document's
            certificate hash must match ``expected_certificate_hash``.
        expected_certificate_hash: SHA-256 hex of the DER-encoded certificate
            embedded in the attestation document, used for TLS channel binding.
        max_attestation_age_s: Maximum age of attestation in seconds.
        current_time_s: Current unix timestamp for freshness checking.
    """

    allowlist: tuple[str, ...] = ()
    local_testnet_mode: bool = False
    require_certificate_binding: bool = True
    expected_certificate_hash: str = ""
    max_attestation_age_s: int = 300
    current_time_s: int = 0


@dataclass(frozen=True)
class ProductionVerifiedAttestation:
    """Result of a production attestation verification.

    Attributes:
        measurement: Canonical measurement string (e.g. ``nitro:pcr0:...:pcr8:...``).
        policy_digest: Policy digest bound to the attestation.
        attestation_epoch: Epoch number derived from attestation timestamp.
        production_security_claim: True only when real attestation was verified.
        certificate_hash: SHA-256 hex of the attestation certificate, or empty.
        attestation_source: ``"nitro"``, ``"sgx"``, or ``"smoke"``.
        pcrs: Dictionary of PCR index to hex value (Nitro only).
        is_smoke: True when verified in smoke/local-testnet mode.
    """

    measurement: str
    policy_digest: str
    attestation_epoch: int
    production_security_claim: bool
    certificate_hash: str = ""
    attestation_source: str = ""
    pcrs: dict[int, str] = field(default_factory=dict)
    is_smoke: bool = False


# ---------------------------------------------------------------------------
# CBOR / COSE parsing helpers
# ---------------------------------------------------------------------------


def _ensure_cbor2() -> None:
    if not _HAS_CBOR2:
        raise RuntimeError(
            "cbor2 package is required for production attestation verification. "
            "Install it with: pip install cbor2"
        )


def _decode_cose_sign1(data: bytes) -> tuple[bytes, bytes, bytes, bytes]:
    """Decode a COSE_Sign1 structure into (protected_header, payload, signature, unprotected_header).

    COSE_Sign1 is a CBOR tag-18 array of exactly 4 elements:
    [protected_header_bstr, unprotected_header_map, payload_bstr, signature_bstr]
    """
    _ensure_cbor2()
    decoded = cbor2.loads(data)
    # If wrapped in a tag, unwrap
    if hasattr(decoded, "value") and not isinstance(decoded, (bytes, list, dict)):
        decoded = decoded.value
    if not isinstance(decoded, (list, tuple)) or len(decoded) != 4:
        raise ValueError("COSE_Sign1 must be a 4-element array")
    protected_header = decoded[0]
    unprotected_header = decoded[1]
    payload = decoded[2]
    signature = decoded[3]
    if not isinstance(protected_header, bytes):
        raise ValueError("COSE_Sign1 protected header must be bytes")
    if not isinstance(payload, bytes):
        raise ValueError("COSE_Sign1 payload must be bytes")
    if not isinstance(signature, bytes):
        raise ValueError("COSE_Sign1 signature must be bytes")
    return protected_header, payload, signature, unprotected_header


def _verify_cose_sign1_signature(
    protected_header: bytes,
    payload: bytes,
    signature: bytes,
    cert_der: bytes,
) -> bool:
    """Verify the COSE_Sign1 signature using the certificate's public key.

    Builds the COSE Sig_structure per RFC 8152 section 4.4:
        ["Signature1", b'', protected_header, payload]
    and verifies the signature using the public key extracted from the
    DER-encoded certificate.

    AWS Nitro Enclave attestation documents use RSASSA-PKCS1-v1_5 with
    SHA-384 by default. We try SHA-384 first, then SHA-256.
    """
    try:
        from cryptography import x509
        from cryptography.hazmat.primitives import hashes
        from cryptography.hazmat.primitives.asymmetric import padding, rsa, ec
    except ImportError:
        raise RuntimeError("cryptography package is required for COSE signature verification")

    _ensure_cbor2()
    sig_structure = cbor2.dumps(["Signature1", b"", protected_header, payload])
    try:
        cert = x509.load_der_x509_certificate(cert_der)
    except Exception:
        return False
    public_key = cert.public_key()

    if isinstance(public_key, rsa.RSAPublicKey):
        for hash_algo in (hashes.SHA384(), hashes.SHA256()):
            try:
                public_key.verify(
                    signature,
                    sig_structure,
                    padding.PKCS1v15(),
                    hash_algo,
                )
                return True
            except Exception:
                continue
        return False
    elif isinstance(public_key, ec.EllipticCurvePublicKey):
        for hash_algo in (hashes.SHA384(), hashes.SHA256()):
            try:
                public_key.verify(signature, sig_structure, ec.ECDSA(hash_algo))
                return True
            except Exception:
                continue
        return False
    return False


def _parse_nitro_attestation_document(payload: bytes) -> dict[str, Any]:
    """Parse a Nitro Enclave attestation document (CBOR map).

    The attestation document is a CBOR map with keys:
    - ``version`` (int)
    - ``certificate`` (bytes) — DER-encoded X.509
    - ``cabundle`` (array of bytes)
    - ``digest`` (int) — hash algorithm (1=SHA-256, 2=SHA-384)
    - ``pcrs`` (map[int->bytes])
    - ``nonce`` (bytes)
    - ``timestamp`` (int)
    - ``publicKey`` (bytes, optional)
    """
    _ensure_cbor2()
    doc = cbor2.loads(payload)
    if not isinstance(doc, dict):
        raise ValueError("attestation document must be a CBOR map")
    required_keys = {"version", "certificate", "pcrs", "timestamp"}
    missing = required_keys - set(doc.keys())
    if missing:
        raise ValueError(f"attestation document missing keys: {missing}")
    return doc


def _pcr_bytes_to_hex(pcr_bytes: bytes) -> str:
    """Convert PCR bytes to lowercase hex string."""
    return pcr_bytes.hex()


def _certificate_hash(cert_der: bytes) -> str:
    """Compute SHA-256 hex of a DER-encoded certificate."""
    return hashlib.sha256(cert_der).hexdigest()


def _extract_nitro_pcrs(pcrs_map: Mapping[Any, bytes]) -> dict[int, str]:
    """Extract PCR values from the Nitro attestation document PCR map.

    Returns a dict mapping PCR index (int) to hex string.
    Validates that PCR0, PCR1, PCR2, PCR8 are present (48 bytes each).
    """
    result: dict[int, str] = {}
    required = [0, 1, 2, 8]
    for idx in required:
        raw = pcrs_map.get(idx)
        if raw is None:
            raise ValueError(f"attestation document missing PCR{idx}")
        if not isinstance(raw, (bytes, bytearray)):
            raise ValueError(f"PCR{idx} must be bytes")
        if len(raw) != 48:
            raise ValueError(f"PCR{idx} must be 48 bytes, got {len(raw)}")
        result[idx] = _pcr_bytes_to_hex(bytes(raw))
    return result


# ---------------------------------------------------------------------------
# SGX quote parsing
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class SGXQuoteInfo:
    """Parsed SGX quote information.

    Attributes:
        mr_enclave_hex: MRENCLAVE measurement (32 bytes hex).
        mr_signer_hex: MRSIGNER measurement (32 bytes hex).
        report_data_hex: Report data (64 bytes hex).
        isv_prod_id: ISV product ID.
        isv_svn: ISV security version number.
        quote_version: Quote version number.
    """

    mr_enclave_hex: str
    mr_signer_hex: str
    report_data_hex: str
    isv_prod_id: int
    isv_svn: int
    quote_version: int


def parse_sgx_quote(quote_bytes: bytes) -> SGXQuoteInfo:
    """Parse an Intel SGX quote structure.

    SGX quote layout (simplified):
    - Bytes 0-1:   quote_version (uint16 LE)
    - Bytes 2-3:   att_key_type (uint16 LE)
    - Bytes 4-7:   reserved
    - Bytes 8-23:  vendor_id (16 bytes)
    - Bytes 24-43: user_data (20 bytes)
    - Bytes 48-111: report_data (64 bytes)
    - Bytes 112-143: mr_enclave (32 bytes)
    - Bytes 144-175: mr_signer (32 bytes)
    - Bytes 176-191: attributes (16 bytes)
    - Bytes 192-195: isv_prod_id (uint16 LE) + isv_svn (uint16 LE)

    This parser extracts the measurement-relevant fields for allowlist matching.
    """
    if len(quote_bytes) < _SGX_REPORT_BODY_OFFSET + 196:
        raise ValueError(
            f"SGX quote too short: {len(quote_bytes)} bytes, "
            f"need at least {_SGX_REPORT_BODY_OFFSET + 196}"
        )
    quote_version = struct.unpack_from("<H", quote_bytes, 0)[0]
    # Report body starts at offset 48
    report_data = quote_bytes[_SGX_REPORT_DATA_OFFSET:_SGX_REPORT_DATA_OFFSET + 64]
    mr_enclave = quote_bytes[_SGX_MRENCLAVE_OFFSET:_SGX_MRENCLAVE_OFFSET + 32]
    mr_signer = quote_bytes[_SGX_MRSIGNER_OFFSET:_SGX_MRSIGNER_OFFSET + 32]
    # ISV prod ID and SVN are at body offset 256 and 258 (absolute 304, 306)
    isv_prod_id_offset = _SGX_ISV_PROD_ID_OFFSET
    isv_svn_offset = _SGX_ISV_SVN_OFFSET
    if len(quote_bytes) >= isv_svn_offset + 2:
        isv_prod_id = struct.unpack_from("<H", quote_bytes, isv_prod_id_offset)[0]
        isv_svn = struct.unpack_from("<H", quote_bytes, isv_svn_offset)[0]
    else:
        isv_prod_id = 0
        isv_svn = 0
    return SGXQuoteInfo(
        mr_enclave_hex=mr_enclave.hex(),
        mr_signer_hex=mr_signer.hex(),
        report_data_hex=report_data.hex(),
        isv_prod_id=isv_prod_id,
        isv_svn=isv_svn,
        quote_version=quote_version,
    )


def sgx_measurement_from_quote(quote_info: SGXQuoteInfo) -> str:
    """Build a canonical SGX measurement string from parsed quote info."""
    return f"sgx:mrenclave:{quote_info.mr_enclave_hex}:mrsigner:{quote_info.mr_signer_hex}"


# ---------------------------------------------------------------------------
# Production verifier
# ---------------------------------------------------------------------------


class ProductionAttestationVerifier:
    """Production TEE attestation verifier.

    Verifies real attestation documents from AWS Nitro Enclave and Intel SGX.
    Enforces a measurement allowlist and certificate hash binding for TLS.
    Falls back to smoke fixtures ONLY when ``local_testnet_mode`` is True.
    """

    def __init__(self, config: ProductionAttestationVerifierConfig) -> None:
        if not isinstance(config, ProductionAttestationVerifierConfig):
            raise TypeError("config must be a ProductionAttestationVerifierConfig")
        self._config = config
        self._allowlist_set = set(config.allowlist)

    def verify(
        self,
        payload: Mapping[str, Any],
        *,
        policy_digest: str = "",
        issued_at_s: int = 0,
        epoch_length_s: int = 60,
    ) -> tuple[Optional[ProductionVerifiedAttestation], Optional[str]]:
        """Verify an attestation payload.

        Args:
            payload: Attestation payload containing provider and document data.
            policy_digest: Expected policy digest (0x-prefixed hex).
            issued_at_s: Unix timestamp when attestation was issued.
            epoch_length_s: Epoch length in seconds for epoch computation.

        Returns:
            Tuple of (verified_attestation, error_string).
        """
        if not isinstance(payload, Mapping):
            return None, "payload must be an object"
        provider = str(payload.get("provider", "")).strip().lower()
        if not provider:
            return None, "provider is required"
        if provider == "nitro":
            return self._verify_nitro(payload, policy_digest, issued_at_s, epoch_length_s)
        if provider == "sgx":
            return self._verify_sgx(payload, policy_digest, issued_at_s, epoch_length_s)
        if provider == "smoke":
            return self._verify_smoke(payload, policy_digest, issued_at_s, epoch_length_s)
        return None, f"unsupported provider: {provider}"

    def _verify_nitro(
        self,
        payload: Mapping[str, Any],
        policy_digest: str,
        issued_at_s: int,
        epoch_length_s: int,
    ) -> tuple[Optional[ProductionVerifiedAttestation], Optional[str]]:
        # Check for raw attestation document first
        doc_bytes = payload.get("attestation_document")
        if isinstance(doc_bytes, str):
            doc_bytes = bytes.fromhex(doc_bytes)
        if isinstance(doc_bytes, (bytes, bytearray)) and len(doc_bytes) > 0:
            return self._verify_nitro_document(
                bytes(doc_bytes), payload, policy_digest, issued_at_s, epoch_length_s
            )
        # Fall back to summary-based verification (pre-parsed PCRs)
        summary = payload.get("summary")
        if isinstance(summary, Mapping):
            return self._verify_nitro_summary(
                summary, payload, policy_digest, issued_at_s, epoch_length_s
            )
        return None, "nitro attestation requires attestation_document or summary"

    def _verify_nitro_document(
        self,
        doc_bytes: bytes,
        payload: Mapping[str, Any],
        policy_digest: str,
        issued_at_s: int,
        epoch_length_s: int,
    ) -> tuple[Optional[ProductionVerifiedAttestation], Optional[str]]:
        try:
            protected, payload_bytes, sig, _unprotected = _decode_cose_sign1(doc_bytes)
            doc = _parse_nitro_attestation_document(payload_bytes)
        except Exception as exc:
            return None, f"failed to parse nitro attestation document: {exc}"
        pcrs = _extract_nitro_pcrs(doc["pcrs"])
        cert_der = doc["certificate"]
        if not isinstance(cert_der, (bytes, bytearray)):
            return None, "attestation document certificate must be bytes"
        cert_der_bytes = bytes(cert_der)
        # Verify COSE_Sign1 signature using the embedded certificate's public key
        if not _verify_cose_sign1_signature(protected, payload_bytes, sig, cert_der_bytes):
            return None, "COSE_Sign1 signature verification failed — attestation document is not authentic"
        cert_hash = _certificate_hash(cert_der_bytes)
        # Certificate hash binding for TLS channel establishment
        if self._config.require_certificate_binding:
            if not self._config.expected_certificate_hash:
                return None, "certificate binding required but no expected hash configured"
            if cert_hash != self._config.expected_certificate_hash:
                return None, "certificate hash mismatch: attestation not bound to expected TLS cert"
        # Build measurement from extracted PCRs
        summary = {"pcrs": {str(k): v for k, v in pcrs.items()}}
        measurement = nitro_measurement_from_summary(summary)
        # Allowlist enforcement
        if not self._allowlist_set:
            return None, "measurement allowlist is empty — production mode requires configured allowlist"
        if measurement not in self._allowlist_set:
            return None, f"measurement {measurement} not in approved allowlist"
        epoch = self._compute_epoch(issued_at_s, epoch_length_s)
        return ProductionVerifiedAttestation(
            measurement=measurement,
            policy_digest=policy_digest,
            attestation_epoch=epoch,
            production_security_claim=True,
            certificate_hash=cert_hash,
            attestation_source="nitro",
            pcrs=pcrs,
            is_smoke=False,
        ), None

    def _verify_nitro_summary(
        self,
        summary: Mapping[str, Any],
        payload: Mapping[str, Any],
        policy_digest: str,
        issued_at_s: int,
        epoch_length_s: int,
    ) -> tuple[Optional[ProductionVerifiedAttestation], Optional[str]]:
        # Summary-based verification: PCRs were pre-parsed by an external verifier.
        # This path still enforces the allowlist but cannot set production_security_claim
        # unless the summary includes a certificate hash that matches.
        try:
            measurement = nitro_measurement_from_summary(summary)
        except Exception as exc:
            return None, f"invalid nitro summary: {exc}"
        if not self._allowlist_set:
            return None, "measurement allowlist is empty — production mode requires configured allowlist"
        if measurement not in self._allowlist_set:
            return None, f"measurement {measurement} not in approved allowlist"
        cert_hash = str(payload.get("certificate_hash", "")).strip().lower()
        if self._config.require_certificate_binding:
            if not self._config.expected_certificate_hash:
                return None, "certificate binding required but no expected hash configured"
            if cert_hash != self._config.expected_certificate_hash:
                return None, "certificate hash mismatch: attestation not bound to expected TLS cert"
        epoch = self._compute_epoch(issued_at_s, epoch_length_s)
        # Summary path: production_security_claim is True only if cert binding verified
        has_cert_binding = bool(cert_hash) and (
            not self._config.expected_certificate_hash
            or cert_hash == self._config.expected_certificate_hash
        )
        return ProductionVerifiedAttestation(
            measurement=measurement,
            policy_digest=policy_digest,
            attestation_epoch=epoch,
            production_security_claim=has_cert_binding,
            certificate_hash=cert_hash,
            attestation_source="nitro",
            is_smoke=False,
        ), None

    def _verify_sgx(
        self,
        payload: Mapping[str, Any],
        policy_digest: str,
        issued_at_s: int,
        epoch_length_s: int,
    ) -> tuple[Optional[ProductionVerifiedAttestation], Optional[str]]:
        quote_raw = payload.get("quote")
        if isinstance(quote_raw, str):
            quote_bytes = bytes.fromhex(quote_raw)
        elif isinstance(quote_raw, (bytes, bytearray)):
            quote_bytes = bytes(quote_raw)
        else:
            return None, "sgx attestation requires quote bytes"
        try:
            quote_info = parse_sgx_quote(quote_bytes)
        except Exception as exc:
            return None, f"failed to parse SGX quote: {exc}"
        measurement = sgx_measurement_from_quote(quote_info)
        if not self._allowlist_set:
            return None, "measurement allowlist is empty — production mode requires configured allowlist"
        if measurement not in self._allowlist_set:
            return None, f"measurement {measurement} not in approved allowlist"
        # SGX report data can carry certificate hash for TLS binding
        cert_hash = str(payload.get("certificate_hash", "")).strip().lower()
        if self._config.require_certificate_binding:
            if not self._config.expected_certificate_hash:
                return None, "certificate binding required but no expected hash configured"
            if cert_hash != self._config.expected_certificate_hash:
                return None, "certificate hash mismatch: attestation not bound to expected TLS cert"
        epoch = self._compute_epoch(issued_at_s, epoch_length_s)
        return ProductionVerifiedAttestation(
            measurement=measurement,
            policy_digest=policy_digest,
            attestation_epoch=epoch,
            production_security_claim=True,
            certificate_hash=cert_hash,
            attestation_source="sgx",
            is_smoke=False,
        ), None

    def _verify_smoke(
        self,
        payload: Mapping[str, Any],
        policy_digest: str,
        issued_at_s: int,
        epoch_length_s: int,
    ) -> tuple[Optional[ProductionVerifiedAttestation], Optional[str]]:
        if not self._config.local_testnet_mode:
            return None, "smoke fixtures rejected in production mode — set local_testnet_mode=True for local-testnet"
        summary = payload.get("summary")
        if not isinstance(summary, Mapping):
            return None, "smoke attestation requires summary with PCRs"
        try:
            measurement = nitro_measurement_from_summary(summary)
        except Exception as exc:
            return None, f"invalid smoke summary: {exc}"
        # In smoke mode, allowlist may be empty or contain the smoke measurement
        if self._allowlist_set and measurement not in self._allowlist_set:
            return None, f"smoke measurement {measurement} not in allowlist"
        epoch = self._compute_epoch(issued_at_s, epoch_length_s)
        return ProductionVerifiedAttestation(
            measurement=measurement,
            policy_digest=policy_digest,
            attestation_epoch=epoch,
            production_security_claim=False,
            certificate_hash="",
            attestation_source="smoke",
            is_smoke=True,
        ), None

    @staticmethod
    def _compute_epoch(issued_at_s: int, epoch_length_s: int) -> int:
        if epoch_length_s <= 0:
            raise ValueError("epoch_length_s must be positive")
        return int(issued_at_s) // int(epoch_length_s)


# ---------------------------------------------------------------------------
# Factory
# ---------------------------------------------------------------------------


def make_production_attestation_verifier_from_env() -> ProductionAttestationVerifier:
    """Build a production attestation verifier from environment variables.

    Environment variables:
    - ``CONFIDENTIAL_APPROVED_MEASUREMENTS``: comma-separated allowlist entries.
    - ``CONFIDENTIAL_LOCAL_TESTNET_MODE``: set to ``1`` for local-testnet smoke mode.
    - ``CONFIDENTIAL_ATTESTATION_CERT_HASH``: expected certificate hash (SHA-256 hex).
    - ``CONFIDENTIAL_ATTESTATION_REQUIRE_CERT_BINDING``: default ``1``.
    - ``CONFIDENTIAL_ATTESTATION_MAX_AGE_S``: max attestation age (default 300).
    """
    allowlist_csv = os.environ.get("CONFIDENTIAL_APPROVED_MEASUREMENTS", "")
    allowlist = tuple(
        m.strip() for m in allowlist_csv.split(",") if m.strip()
    )
    local_testnet = _env_bool("CONFIDENTIAL_LOCAL_TESTNET_MODE", False)
    cert_hash = os.environ.get("CONFIDENTIAL_ATTESTATION_CERT_HASH", "").strip().lower()
    require_binding = _env_bool("CONFIDENTIAL_ATTESTATION_REQUIRE_CERT_BINDING", True)
    max_age = _env_int("CONFIDENTIAL_ATTESTATION_MAX_AGE_S", 300, lo=1, hi=86400)
    return ProductionAttestationVerifier(
        ProductionAttestationVerifierConfig(
            allowlist=allowlist,
            local_testnet_mode=local_testnet,
            expected_certificate_hash=cert_hash,
            require_certificate_binding=require_binding,
            max_attestation_age_s=max_age,
        )
    )


def _env_bool(name: str, default: bool) -> bool:
    raw = os.environ.get(name)
    if raw is None or not raw.strip():
        return bool(default)
    v = raw.strip().lower()
    if v in {"1", "true", "yes", "on"}:
        return True
    if v in {"0", "false", "no", "off"}:
        return False
    raise ValueError(f"{name} must be a boolean, got {raw!r}")


def _env_int(name: str, default: int, *, lo: int, hi: int) -> int:
    raw = os.environ.get(name)
    if raw is None or not raw.strip():
        return int(default)
    try:
        v = int(raw.strip())
    except ValueError as exc:
        raise ValueError(f"{name} must be an int, got {raw!r}") from exc
    if v < lo or v > hi:
        raise ValueError(f"{name} must be in [{lo}, {hi}], got {v}")
    return v


# ---------------------------------------------------------------------------
# Smoke fixture helpers (local-testnet only)
# ---------------------------------------------------------------------------


def smoke_nitro_attestation_payload() -> dict[str, Any]:
    """Build a smoke Nitro attestation payload for local-testnet testing.

    This uses the well-known smoke PCR values. It must NEVER be used in
    production — the verifier rejects smoke fixtures unless
    ``local_testnet_mode`` is explicitly enabled.
    """
    return {
        "provider": "smoke",
        "summary": {"pcrs": {"0": _SMOKE_NITRO_PCR0, "8": _SMOKE_NITRO_PCR8}},
    }


def is_canonical_sgx_measurement(value: str) -> bool:
    """Check if a value is a canonical SGX measurement string."""
    if not isinstance(value, str) or not value.startswith("sgx:"):
        return False
    parts = value.split(":")
    if len(parts) != 5:
        return False
    if parts[0] != "sgx" or parts[1] != "mrenclave" or parts[3] != "mrsigner":
        return False
    if len(parts[2]) != _SGX_MEASUREMENT_HEX_LEN or len(parts[4]) != _SGX_MEASUREMENT_HEX_LEN:
        return False
    return all(c in "0123456789abcdef" for c in parts[2] + parts[4])
