"""Tests for the production TEE attestation verifier v2.

Verifies real attestation document parsing (COSE/CBOR for Nitro, quote
structure for SGX), measurement allowlist enforcement, certificate hash
binding, production security claim validation, and smoke fixture fallback.

Copyright (c) DarkLightX/Dana Edwards. All rights reserved.
"""

from __future__ import annotations

import hashlib
import struct
import datetime

import cbor2

from src.integration.confidential_attestation_verifier_v2 import (
    ProductionAttestationVerifier,
    ProductionAttestationVerifierConfig,
    parse_sgx_quote,
    sgx_measurement_from_quote,
    smoke_nitro_attestation_payload,
    is_canonical_sgx_measurement,
)

PCR0 = b"\xaa" * 48
PCR1 = b"\xbb" * 48
PCR2 = b"\xcc" * 48
PCR8 = b"\xdd" * 48
POLICY_DIGEST = "0x" + "e" * 64


def _generate_self_signed_cert() -> tuple[bytes, object]:
    """Generate a real self-signed RSA certificate for testing."""
    from cryptography import x509
    from cryptography.hazmat.primitives import hashes, serialization
    from cryptography.hazmat.primitives.asymmetric import rsa
    from cryptography.x509.oid import NameOID

    private_key = rsa.generate_private_key(public_exponent=65537, key_size=2048)
    subject = issuer = x509.Name([
        x509.NameAttribute(NameOID.COMMON_NAME, "test-nitro-attestation"),
    ])
    cert = (
        x509.CertificateBuilder()
        .subject_name(subject)
        .issuer_name(issuer)
        .public_key(private_key.public_key())
        .serial_number(x509.random_serial_number())
        .not_valid_before(datetime.datetime(2024, 1, 1))
        .not_valid_after(datetime.datetime(2030, 1, 1))
        .sign(private_key, hashes.SHA384())
    )
    cert_der = cert.public_bytes(serialization.Encoding.DER)
    return cert_der, private_key


_CERT_DER, _CERT_KEY = _generate_self_signed_cert()
CERT_DER = _CERT_DER
CERT_HASH = hashlib.sha256(CERT_DER).hexdigest()
NITRO_MEASUREMENT = f"nitro:pcr0:{PCR0.hex()}:pcr8:{PCR8.hex()}"
SMOKE_MEASUREMENT = f"nitro:pcr0:{'0123456789abcdef' * 6}:pcr8:{'fedcba9876543210' * 6}"


def _build_nitro_attestation_document() -> bytes:
    """Build a real COSE_Sign1 attestation document with valid signature."""
    from cryptography.hazmat.primitives import hashes
    from cryptography.hazmat.primitives.asymmetric import padding

    doc = {
        "version": 1, "certificate": CERT_DER, "cabundle": [CERT_DER],
        "digest": 1, "pcrs": {0: PCR0, 1: PCR1, 2: PCR2, 8: PCR8},
        "nonce": b"\x01" * 16, "timestamp": 1700000000,
        "publicKey": b"\x04" + b"\x00" * 64,
    }
    payload = cbor2.dumps(doc)
    protected_header = cbor2.dumps({1: -7})  # alg: RS256
    # Build COSE Sig_structure: ["Signature1", b"", protected_header, payload]
    sig_structure = cbor2.dumps(["Signature1", b"", protected_header, payload])
    signature = _CERT_KEY.sign(sig_structure, padding.PKCS1v15(), hashes.SHA384())
    cose_sign1 = [protected_header, {}, payload, signature]
    return cbor2.dumps(cbor2.CBORTag(18, cose_sign1))


def _build_sgx_quote() -> bytes:
    """Build a minimal SGX quote with known MRENCLAVE and MRSIGNER.

    Uses correct Intel SGX SDK report body offsets:
    - MRENCLAVE at absolute offset 48 + 128 = 176
    - MRSIGNER at absolute offset 48 + 192 = 240
    - ISV_PROD_ID at absolute offset 48 + 240 = 288
    - ISV_SVN at absolute offset 48 + 242 = 290
    """
    quote = bytearray(48 + 384 + 64)
    struct.pack_into("<H", quote, 0, 1)  # version
    # MRENCLAVE at body offset 128 (absolute 176)
    quote[176:208] = b"\xab" * 32
    # MRSIGNER at body offset 192 (absolute 240)
    quote[240:272] = b"\xcd" * 32
    # ISV_PROD_ID at body offset 240 (absolute 288)
    struct.pack_into("<H", quote, 288, 1)
    # ISV_SVN at body offset 242 (absolute 290)
    struct.pack_into("<H", quote, 290, 2)
    return bytes(quote)


def _cfg(allowlist=(), **kw) -> ProductionAttestationVerifierConfig:
    kw.setdefault("expected_certificate_hash", CERT_HASH)
    return ProductionAttestationVerifierConfig(allowlist=tuple(allowlist), **kw)


def _verify_nitro_doc(verifier, doc=None, **kw):
    doc = doc or _build_nitro_attestation_document()
    return verifier.verify(
        {"provider": "nitro", "attestation_document": doc.hex()},
        policy_digest=POLICY_DIGEST, **kw
    )


# --- Real Nitro attestation document validation ----------------------------


def test_real_nitro_attestation_document_validates_and_extracts_pcrs():
    """Real COSE/CBOR Nitro attestation document is parsed and PCRs extracted."""
    result, err = _verify_nitro_doc(
        ProductionAttestationVerifier(_cfg(allowlist=[NITRO_MEASUREMENT]))
    )
    assert err is None and result is not None
    assert result.measurement == NITRO_MEASUREMENT
    assert result.production_security_claim is True
    assert result.attestation_source == "nitro"
    assert result.is_smoke is False
    assert result.certificate_hash == CERT_HASH
    assert result.pcrs[0] == PCR0.hex()
    assert result.pcrs[1] == PCR1.hex()
    assert result.pcrs[2] == PCR2.hex()
    assert result.pcrs[8] == PCR8.hex()


def test_nitro_attestation_rejected_when_measurement_not_in_allowlist():
    """Attestation with measurement not in allowlist is rejected."""
    result, err = _verify_nitro_doc(
        ProductionAttestationVerifier(_cfg(allowlist=["nitro:pcr0:ffff:pcr8:eeee"]))
    )
    assert result is None and "not in approved allowlist" in err


def test_nitro_attestation_rejected_when_allowlist_empty():
    """Empty allowlist is rejected in production mode."""
    result, err = _verify_nitro_doc(ProductionAttestationVerifier(_cfg(allowlist=[])))
    assert result is None and "allowlist is empty" in err


# --- Certificate hash binding ----------------------------------------------


def test_certificate_hash_binding_rejects_mismatched_cert():
    """Attestation with wrong certificate hash is rejected for TLS binding."""
    verifier = ProductionAttestationVerifier(
        ProductionAttestationVerifierConfig(
            allowlist=(NITRO_MEASUREMENT,), expected_certificate_hash="0" * 64,
            require_certificate_binding=True,
        )
    )
    result, err = _verify_nitro_doc(verifier)
    assert result is None and "certificate hash mismatch" in err


def test_certificate_hash_binding_passes_when_cert_matches():
    """Attestation with matching certificate hash passes TLS binding check."""
    result, err = _verify_nitro_doc(
        ProductionAttestationVerifier(_cfg(allowlist=[NITRO_MEASUREMENT]))
    )
    assert err is None and result.certificate_hash == CERT_HASH


# --- Smoke fixture rejection / fallback ------------------------------------


def test_smoke_fixtures_rejected_in_production_mode():
    """Smoke fixtures are rejected when local_testnet_mode is False."""
    verifier = ProductionAttestationVerifier(
        ProductionAttestationVerifierConfig(allowlist=(), local_testnet_mode=False)
    )
    result, err = verifier.verify(smoke_nitro_attestation_payload(), policy_digest=POLICY_DIGEST)
    assert result is None and "smoke fixtures rejected" in err


def test_smoke_fixtures_accepted_in_local_testnet_mode():
    """Smoke fixtures accepted when local_testnet_mode is True."""
    verifier = ProductionAttestationVerifier(
        ProductionAttestationVerifierConfig(
            allowlist=(SMOKE_MEASUREMENT,), local_testnet_mode=True,
            require_certificate_binding=False,
        )
    )
    result, err = verifier.verify(smoke_nitro_attestation_payload(), policy_digest=POLICY_DIGEST)
    assert err is None and result is not None
    assert result.is_smoke is True
    assert result.production_security_claim is False
    assert result.attestation_source == "smoke"


# --- SGX quote parsing and verification ------------------------------------


def test_sgx_quote_parsing_extracts_mrenclave_and_mrsigner():
    """SGX quote is parsed and MRENCLAVE/MRSIGNER are extracted correctly."""
    info = parse_sgx_quote(_build_sgx_quote())
    assert info.mr_enclave_hex == "ab" * 32
    assert info.mr_signer_hex == "cd" * 32
    assert info.isv_prod_id == 1 and info.isv_svn == 2
    assert info.quote_version == 1


def test_sgx_attestation_validates_with_allowlist():
    """SGX attestation with measurement in allowlist is verified."""
    quote = _build_sgx_quote()
    measurement = sgx_measurement_from_quote(parse_sgx_quote(quote))
    verifier = ProductionAttestationVerifier(
        ProductionAttestationVerifierConfig(allowlist=(measurement,), require_certificate_binding=False)
    )
    result, err = verifier.verify(
        {"provider": "sgx", "quote": quote.hex()}, policy_digest=POLICY_DIGEST
    )
    assert err is None and result is not None
    assert result.measurement == measurement
    assert result.production_security_claim is True
    assert result.attestation_source == "sgx"


def test_sgx_attestation_rejected_when_measurement_not_in_allowlist():
    """SGX attestation with unknown measurement is rejected."""
    verifier = ProductionAttestationVerifier(
        ProductionAttestationVerifierConfig(
            allowlist=("sgx:mrenclave:00:00:00:mrsigner:00",), require_certificate_binding=False,
        )
    )
    result, err = verifier.verify(
        {"provider": "sgx", "quote": _build_sgx_quote().hex()}, policy_digest=POLICY_DIGEST
    )
    assert result is None and "not in approved allowlist" in err


def test_sgx_quote_too_short_is_rejected():
    """Truncated SGX quote is rejected with a clear error."""
    verifier = ProductionAttestationVerifier(
        ProductionAttestationVerifierConfig(allowlist=("sgx:x",), require_certificate_binding=False)
    )
    result, err = verifier.verify({"provider": "sgx", "quote": "0011"}, policy_digest=POLICY_DIGEST)
    assert result is None and "SGX quote" in err


# --- Production security claim validation -----------------------------------


def test_production_security_claim_true_for_real_nitro_document():
    """production_security_claim is True when real Nitro document is verified."""
    result, _ = _verify_nitro_doc(
        ProductionAttestationVerifier(_cfg(allowlist=[NITRO_MEASUREMENT]))
    )
    assert result.production_security_claim is True


def test_production_security_claim_false_for_smoke_mode():
    """production_security_claim is False in smoke/local-testnet mode."""
    verifier = ProductionAttestationVerifier(
        ProductionAttestationVerifierConfig(
            allowlist=(SMOKE_MEASUREMENT,), local_testnet_mode=True,
            require_certificate_binding=False,
        )
    )
    result, _ = verifier.verify(smoke_nitro_attestation_payload(), policy_digest=POLICY_DIGEST)
    assert result.production_security_claim is False


# --- Summary-based Nitro verification (backwards compatible) ---------------


def test_nitro_summary_verification_with_certificate_hash():
    """Summary-based Nitro verification with cert hash sets production claim."""
    verifier = ProductionAttestationVerifier(_cfg(allowlist=[NITRO_MEASUREMENT]))
    result, err = verifier.verify(
        {"provider": "nitro", "summary": {"pcrs": {"0": PCR0.hex(), "8": PCR8.hex()}},
         "certificate_hash": CERT_HASH},
        policy_digest=POLICY_DIGEST,
    )
    assert err is None and result.production_security_claim is True
    assert result.certificate_hash == CERT_HASH


def test_nitro_summary_without_cert_hash_does_not_claim_production():
    """Summary-based verification without cert hash does not claim production."""
    verifier = ProductionAttestationVerifier(
        ProductionAttestationVerifierConfig(allowlist=(NITRO_MEASUREMENT,), require_certificate_binding=False)
    )
    result, err = verifier.verify(
        {"provider": "nitro", "summary": {"pcrs": {"0": PCR0.hex(), "8": PCR8.hex()}}},
        policy_digest=POLICY_DIGEST,
    )
    assert err is None and result.production_security_claim is False


# --- Helper function tests -------------------------------------------------


def test_is_canonical_sgx_measurement_validates_format():
    """is_canonical_sgx_measurement validates SGX measurement format."""
    valid = f"sgx:mrenclave:{'ab' * 32}:mrsigner:{'cd' * 32}"
    assert is_canonical_sgx_measurement(valid) is True
    assert is_canonical_sgx_measurement("nitro:pcr0:x:pcr8:y") is False
    assert is_canonical_sgx_measurement("sgx:wrong:ab:mrsigner:cd") is False
