"""Detached ownership boundary for verifier-created M6 finality evidence.

The commit and durable shells receive Python objects at an imperative
boundary.  Exact outer types alone do not own nested values: a caller can
forge an exact slotted object whose fields contain executable subclasses.
This module validates every finality field and constructs a fresh exact
projection before any comparison, hashing, copy, adapter call, or lock.
"""

from __future__ import annotations

from typing import cast

from src.core.m6_safe_mount_types_v1 import (
    ZERO_ROOT_V1,
    FinalityModeV1,
    M6FinalityVerificationReceiptRecordV1,
    M6FinalityVerificationReceiptV1,
    TauBatchCertificateV1,
    VerifiedZenoLedgerFinalityV1,
    ZenoLedgerFinalityCertificateV1,
)
from src.state.canonical import canonical_hex_fixed_allow_0x

_UNOWNED = "finality evidence contains an unowned nested value"


def _slot(value: object, name: str) -> object:
    try:
        return object.__getattribute__(value, name)
    except AttributeError as exc:
        raise ValueError("finality evidence is malformed") from exc


def _exact_text(value: object, *, name: str, allow_none: bool = False) -> str | None:
    if value is None and allow_none:
        return None
    if type(value) is not str:
        raise TypeError(f"{_UNOWNED}: {name}")
    if not value:
        raise ValueError(f"finality evidence contains an empty value: {name}")
    return value


def _exact_int(value: object, *, name: str) -> int:
    if type(value) is not int:
        raise TypeError(f"{_UNOWNED}: {name}")
    return value


def _exact_root(value: object, *, name: str, allow_zero: bool = False) -> str:
    text = _exact_text(value, name=name)
    if text is None:
        raise ValueError("finality evidence contains a missing root")
    try:
        canonical = canonical_hex_fixed_allow_0x(text, nbytes=32, name=name)
    except (TypeError, ValueError) as exc:
        raise ValueError("finality evidence contains a malformed root") from exc
    if text != canonical or (not allow_zero and canonical == ZERO_ROOT_V1):
        raise ValueError("finality evidence contains a non-canonical root")
    return text


def _exact_tuple_of_text(value: object, *, name: str) -> tuple[str, ...]:
    if type(value) is not tuple:
        raise TypeError(f"{_UNOWNED}: {name}")
    result: list[str] = []
    for index, item in enumerate(cast(tuple[object, ...], value)):
        text = _exact_text(item, name=f"{name}[{index}]")
        if text is None:
            raise ValueError("finality evidence contains a missing text value")
        result.append(text)
    return tuple(result)


def _own_tau_certificate(value: object) -> TauBatchCertificateV1:
    if type(value) is not TauBatchCertificateV1:
        raise TypeError(f"{_UNOWNED}: tau_certificate")
    batch_id = _exact_text(_slot(value, "batch_id"), name="tau_certificate.batch_id")
    profile = _exact_root(_slot(value, "tau_profile_root"), name="tau_certificate.tau_profile_root")
    chain_id = _exact_root(_slot(value, "chain_id"), name="tau_certificate.chain_id")
    command_hashes = tuple(
        _exact_root(item, name=f"tau_certificate.ordered_command_hashes[{index}]")
        for index, item in enumerate(
            _exact_tuple_of_text(
                _slot(value, "ordered_command_hashes"),
                name="tau_certificate.ordered_command_hashes",
            )
        )
    )
    nonce_identities = _exact_tuple_of_text(
        _slot(value, "ordered_nonce_identities"),
        name="tau_certificate.ordered_nonce_identities",
    )
    parent_head = _exact_root(
        _slot(value, "candidate_parent_head"),
        name="tau_certificate.candidate_parent_head",
        allow_zero=True,
    )
    certificate_root = _exact_root(
        _slot(value, "certificate_root"),
        name="tau_certificate.certificate_root",
    )
    owned = TauBatchCertificateV1(
        batch_id=cast(str, batch_id),
        tau_profile_root=profile,
        chain_id=chain_id,
        ordered_command_hashes=command_hashes,
        ordered_nonce_identities=nonce_identities,
        candidate_parent_head=parent_head,
        certificate_root=certificate_root,
    )
    if owned.certificate_root != certificate_root:
        raise ValueError("finality evidence Tau certificate root mismatch")
    return owned


def _own_certificate(value: object) -> ZenoLedgerFinalityCertificateV1:
    if type(value) is not ZenoLedgerFinalityCertificateV1:
        raise TypeError(f"{_UNOWNED}: certificate")
    finality_id = _exact_text(_slot(value, "finality_id"), name="certificate.finality_id")
    candidate_head = _exact_root(_slot(value, "candidate_head"), name="certificate.candidate_head")
    publication_root = _exact_root(
        _slot(value, "publication_root"),
        name="certificate.publication_root",
    )
    chain_id = _exact_root(_slot(value, "chain_id"), name="certificate.chain_id")
    validator_set_root = _exact_root(
        _slot(value, "validator_set_root"),
        name="certificate.validator_set_root",
    )
    writer_epoch = _exact_int(_slot(value, "writer_epoch"), name="certificate.writer_epoch")
    signer_ids = _exact_tuple_of_text(_slot(value, "signer_ids"), name="certificate.signer_ids")
    quorum = _exact_int(_slot(value, "quorum"), name="certificate.quorum")
    mode = _slot(value, "mode")
    if type(mode) is not FinalityModeV1:
        raise TypeError(f"{_UNOWNED}: certificate.mode")
    signature_root = _exact_root(_slot(value, "signature_root"), name="certificate.signature_root")
    execution_receipt_root = _exact_root(
        _slot(value, "execution_receipt_root"),
        name="certificate.execution_receipt_root",
        allow_zero=False,
    ) if _slot(value, "execution_receipt_root") is not None else None
    original_root = _exact_root(
        _slot(value, "certificate_root"),
        name="certificate.certificate_root",
    )
    owned = ZenoLedgerFinalityCertificateV1(
        finality_id=cast(str, finality_id),
        candidate_head=candidate_head,
        publication_root=publication_root,
        chain_id=chain_id,
        validator_set_root=validator_set_root,
        writer_epoch=writer_epoch,
        signer_ids=signer_ids,
        quorum=quorum,
        mode=cast(FinalityModeV1, mode),
        signature_root=signature_root,
        execution_receipt_root=execution_receipt_root,
    )
    if owned.certificate_root != original_root:
        raise ValueError("finality evidence certificate root mismatch")
    return owned


def _own_receipt(value: object) -> M6FinalityVerificationReceiptV1:
    if type(value) is not M6FinalityVerificationReceiptV1:
        raise TypeError(f"{_UNOWNED}: verification_receipt")
    fields = {
        "_subject_root": _exact_root(_slot(value, "_subject_root"), name="verification_receipt.subject_root"),
        "_candidate_parent_head": _exact_root(
            _slot(value, "_candidate_parent_head"),
            name="verification_receipt.candidate_parent_head",
            allow_zero=True,
        ),
        "_candidate_head": _exact_root(
            _slot(value, "_candidate_head"),
            name="verification_receipt.candidate_head",
        ),
        "_publication_root": _exact_root(
            _slot(value, "_publication_root"),
            name="verification_receipt.publication_root",
        ),
        "_writer_epoch": _exact_int(
            _slot(value, "_writer_epoch"),
            name="verification_receipt.writer_epoch",
        ),
        "_certificate_root": _exact_root(
            _slot(value, "_certificate_root"),
            name="verification_receipt.certificate_root",
        ),
        "_attestation_root": _exact_root(
            _slot(value, "_attestation_root"),
            name="verification_receipt.attestation_root",
        ),
    }
    record = M6FinalityVerificationReceiptRecordV1(
        subject_root=fields["_subject_root"],
        candidate_parent_head=fields["_candidate_parent_head"],
        candidate_head=fields["_candidate_head"],
        publication_root=fields["_publication_root"],
        writer_epoch=fields["_writer_epoch"],
        certificate_root=fields["_certificate_root"],
        attestation_root=fields["_attestation_root"],
    )
    original_root = _exact_root(
        object.__getattribute__(value, "receipt_root"),
        name="verification_receipt.receipt_root",
    )
    if record.receipt_root != original_root:
        raise ValueError("finality evidence verification receipt root mismatch")
    owned = object.__new__(M6FinalityVerificationReceiptV1)
    for name, field_value in fields.items():
        object.__setattr__(owned, name, field_value)
    object.__setattr__(owned, "_sealed", True)
    return owned


def _own_finality_header(
    value: object,
) -> tuple[str, str, str, str, str | None, str | None]:
    subject_root = _exact_root(_slot(value, "_subject_root"), name="finality.subject_root")
    parent_head = _exact_root(
        _slot(value, "_candidate_parent_head"),
        name="finality.candidate_parent_head",
        allow_zero=True,
    )
    candidate_head = _exact_root(_slot(value, "_candidate_head"), name="finality.candidate_head")
    publication_root = _exact_root(
        _slot(value, "_publication_root"),
        name="finality.publication_root",
    )
    expected_command_root = (
        None
        if _slot(value, "_expected_command_root") is None
        else _exact_root(_slot(value, "_expected_command_root"), name="finality.expected_command_root")
    )
    expected_nonce_root = (
        None
        if _slot(value, "_expected_nonce_root") is None
        else _exact_root(_slot(value, "_expected_nonce_root"), name="finality.expected_nonce_root")
    )
    return (
        subject_root,
        parent_head,
        candidate_head,
        publication_root,
        expected_command_root,
        expected_nonce_root,
    )


def own_verified_zeno_ledger_finality_v1(
    value: object,
) -> VerifiedZenoLedgerFinalityV1:
    """Return a detached exact finality projection or reject it before a lock."""

    if type(value) is not VerifiedZenoLedgerFinalityV1:
        raise TypeError("finality evidence must be verifier-created")
    (
        subject_root,
        parent_head,
        candidate_head,
        publication_root,
        expected_command_root,
        expected_nonce_root,
    ) = _own_finality_header(value)
    certificate = _own_certificate(_slot(value, "_certificate"))
    tau_certificate_raw = _slot(value, "_tau_certificate")
    tau_certificate = (
        None if tau_certificate_raw is None else _own_tau_certificate(tau_certificate_raw)
    )
    verification_receipt = _own_receipt(_slot(value, "_verification_receipt"))
    if certificate.candidate_head != candidate_head:
        raise ValueError("finality evidence candidate-head binding mismatch")
    if certificate.publication_root != publication_root:
        raise ValueError("finality evidence publication binding mismatch")
    if (
        verification_receipt.subject_root != subject_root
        or verification_receipt.candidate_parent_head != parent_head
        or verification_receipt.candidate_head != candidate_head
        or verification_receipt.publication_root != publication_root
        or verification_receipt.writer_epoch != certificate.writer_epoch
        or verification_receipt.certificate_root != certificate.certificate_root
    ):
        raise ValueError("finality evidence verification receipt binding mismatch")
    if certificate.mode is FinalityModeV1.FALLBACK_FORCED_INCLUSION and tau_certificate is not None:
        raise ValueError("finality evidence fallback mode forbids Tau certificate")
    owned = object.__new__(VerifiedZenoLedgerFinalityV1)
    fields: dict[str, object] = {
        "_subject_root": subject_root,
        "_candidate_parent_head": parent_head,
        "_candidate_head": candidate_head,
        "_publication_root": publication_root,
        "_expected_command_root": expected_command_root,
        "_expected_nonce_root": expected_nonce_root,
        "_certificate": certificate,
        "_tau_certificate": tau_certificate,
        "_verification_receipt": verification_receipt,
    }
    for name, field_value in fields.items():
        object.__setattr__(owned, name, field_value)
    object.__setattr__(owned, "_sealed", True)
    return owned


def own_tau_batch_certificate_v1(
    value: object,
) -> TauBatchCertificateV1 | None:
    """Detach the separately supplied Tau certificate before comparisons."""

    return None if value is None else _own_tau_certificate(value)


__all__ = [
    "own_tau_batch_certificate_v1",
    "own_verified_zeno_ledger_finality_v1",
]
