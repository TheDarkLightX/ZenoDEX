from __future__ import annotations

from dataclasses import replace

from src.core.perp_funding_closeout_liability_certificate import (
    CertificateVerdict,
    PositionAccount,
)
from src.core.perp_funding_closeout_mixed_open_netting import (
    MIXED_OPEN_NETTING_SCHEMA,
    MixedOpenFundingNettingCertificate,
    OpenFundingDueRow,
    build_mixed_open_funding_netting_certificate,
    expected_open_funding_due_rows,
    mixed_open_funding_netting_certificate_from_payload,
    mixed_open_funding_netting_certificate_hash,
    mixed_open_funding_netting_certificate_to_payload,
    receiver_claim_rows_from_open_due,
    validate_mixed_open_funding_netting_certificate,
    verify_mixed_open_funding_netting_certificate_payload,
)
from src.core.perp_funding_closeout_receiver_rationing import (
    ReceiverClaimRow,
    build_receiver_haircut_rationing,
)
from src.core.perp_v2.math import PRICE_SCALE

PRICE_E8 = 100 * PRICE_SCALE
FUNDING_RATE_BPS = 100
EPOCH = 7
OPEN_PAYER = "aa" * 48
OPEN_RECEIVER = "bb" * 48
OPEN_RECEIVER_2 = "cc" * 48


def _mixed_post_accounts() -> tuple[PositionAccount, ...]:
    return (
        PositionAccount(OPEN_PAYER, 40_000),
        PositionAccount(OPEN_RECEIVER, -100_000),
    )


def _two_receiver_post_accounts() -> tuple[PositionAccount, ...]:
    return (
        PositionAccount(OPEN_PAYER, 40_000),
        PositionAccount(OPEN_RECEIVER, -60_000),
        PositionAccount(OPEN_RECEIVER_2, -40_000),
    )


def _certificate() -> MixedOpenFundingNettingCertificate:
    return build_mixed_open_funding_netting_certificate(
        _mixed_post_accounts(),
        epoch=EPOCH,
        price_e8=PRICE_E8,
        funding_rate_bps=FUNDING_RATE_BPS,
        receiver_haircut_sum_quote=30_000,
    )


def test_mixed_open_netting_accepts_signed_payer_receiver_surface() -> None:
    certificate = _certificate()

    verdict = validate_mixed_open_funding_netting_certificate(
        _mixed_post_accounts(),
        certificate,
    )

    assert verdict == CertificateVerdict(True, None)
    assert certificate.open_payer_due_sum_quote == 40_000
    assert certificate.receiver_claim_sum_quote == 100_000
    assert certificate.raw_post_open_due_sum_quote == -60_000
    assert certificate.receiver_haircut_sum_quote == 30_000
    assert certificate.payable_receiver_sum_quote == 70_000
    assert certificate.payable_post_open_due_sum_quote == -30_000


def test_raw_net_is_not_enough_to_determine_receiver_payables() -> None:
    certificate = _certificate()
    raw_only_rationing = build_receiver_haircut_rationing(
        (ReceiverClaimRow(OPEN_RECEIVER, 60_000),),
        total_haircut_quote=30_000,
    )

    assert certificate.raw_post_open_due_sum_quote == -60_000
    assert raw_only_rationing.total_claim_quote == 60_000
    assert sum(row.payable_quote for row in raw_only_rationing.receiver_rows) == 30_000
    assert certificate.payable_receiver_sum_quote == 70_000


def test_receiver_haircut_is_rationed_over_gross_receiver_claims() -> None:
    certificate = build_mixed_open_funding_netting_certificate(
        _two_receiver_post_accounts(),
        epoch=EPOCH,
        price_e8=PRICE_E8,
        funding_rate_bps=FUNDING_RATE_BPS,
        receiver_haircut_sum_quote=30_000,
    )
    rows = {
        row.account_pubkey: row
        for row in certificate.receiver_haircut_rationing.receiver_rows
    }

    assert certificate.open_payer_due_sum_quote == 40_000
    assert certificate.receiver_claim_sum_quote == 100_000
    assert rows[OPEN_RECEIVER].haircut_quote == 18_000
    assert rows[OPEN_RECEIVER].payable_quote == 42_000
    assert rows[OPEN_RECEIVER_2].haircut_quote == 12_000
    assert rows[OPEN_RECEIVER_2].payable_quote == 28_000
    assert certificate.payable_post_open_due_sum_quote == -30_000


def test_payload_roundtrip_and_hash_are_stable() -> None:
    certificate = _certificate()
    payload = mixed_open_funding_netting_certificate_to_payload(certificate)
    parsed = mixed_open_funding_netting_certificate_from_payload(payload)

    assert parsed == certificate
    assert verify_mixed_open_funding_netting_certificate_payload(
        payload,
        post_accounts=_mixed_post_accounts(),
    ) == CertificateVerdict(True, None)
    assert mixed_open_funding_netting_certificate_hash(parsed) == mixed_open_funding_netting_certificate_hash(certificate)


def test_rejects_raw_net_based_receiver_rationing() -> None:
    certificate = _certificate()
    raw_only_rationing = build_receiver_haircut_rationing(
        (ReceiverClaimRow(OPEN_RECEIVER, 60_000),),
        total_haircut_quote=30_000,
    )
    broken = replace(
        certificate,
        receiver_haircut_rationing=raw_only_rationing,
    )

    verdict = validate_mixed_open_funding_netting_certificate(
        _mixed_post_accounts(),
        broken,
    )

    assert verdict == CertificateVerdict(False, "receiver haircut rationing mismatch")


def test_rejects_receiver_claim_sum_mismatch() -> None:
    certificate = replace(_certificate(), receiver_claim_sum_quote=60_000)

    verdict = validate_mixed_open_funding_netting_certificate(
        _mixed_post_accounts(),
        certificate,
    )

    assert verdict == CertificateVerdict(False, "receiver_claim_sum_quote mismatch")


def test_rejects_payable_net_mismatch() -> None:
    certificate = replace(_certificate(), payable_post_open_due_sum_quote=-60_000)

    verdict = validate_mixed_open_funding_netting_certificate(
        _mixed_post_accounts(),
        certificate,
    )

    assert verdict == CertificateVerdict(False, "payable_post_open_due_sum_quote mismatch")


def test_rejects_open_due_rows_not_matching_post_accounts() -> None:
    certificate = _certificate()
    changed_post = (
        PositionAccount(OPEN_PAYER, 50_000),
        PositionAccount(OPEN_RECEIVER, -100_000),
    )

    verdict = validate_mixed_open_funding_netting_certificate(
        changed_post,
        certificate,
    )

    assert verdict == CertificateVerdict(False, "open_due_rows mismatch")


def test_rejects_non_mixed_all_receiver_surface() -> None:
    certificate = MixedOpenFundingNettingCertificate(
        schema=MIXED_OPEN_NETTING_SCHEMA,
        epoch=EPOCH,
        price_e8=PRICE_E8,
        funding_rate_bps=FUNDING_RATE_BPS,
        open_due_rows=(OpenFundingDueRow(OPEN_RECEIVER, -60_000),),
        open_payer_due_sum_quote=0,
        receiver_claim_sum_quote=60_000,
        raw_post_open_due_sum_quote=-60_000,
        receiver_haircut_sum_quote=30_000,
        payable_receiver_sum_quote=30_000,
        payable_post_open_due_sum_quote=-30_000,
        receiver_haircut_rationing=build_receiver_haircut_rationing(
            (ReceiverClaimRow(OPEN_RECEIVER, 60_000),),
            total_haircut_quote=30_000,
        ),
    )

    verdict = validate_mixed_open_funding_netting_certificate(
        (PositionAccount(OPEN_RECEIVER, -60_000),),
        certificate,
    )

    assert verdict == CertificateVerdict(False, "mixed open netting requires open payer due")


def test_rejects_invalid_payload_shape() -> None:
    payload = mixed_open_funding_netting_certificate_to_payload(_certificate())
    payload["open_due_rows"] = "not rows"

    verdict = verify_mixed_open_funding_netting_certificate_payload(
        payload,
        post_accounts=_mixed_post_accounts(),
    )

    assert verdict == CertificateVerdict(False, "open_due_rows must be a list")


def test_schema_must_match() -> None:
    certificate = replace(
        _certificate(),
        schema="zenodex.perp.funding_closeout_mixed_open_netting.v0",
    )

    verdict = validate_mixed_open_funding_netting_certificate(
        _mixed_post_accounts(),
        certificate,
    )

    assert verdict == CertificateVerdict(False, "invalid mixed open netting schema")


def test_expected_rows_and_receiver_claim_projection_are_canonical() -> None:
    rows = expected_open_funding_due_rows(
        _two_receiver_post_accounts(),
        price_e8=PRICE_E8,
        funding_rate_bps=FUNDING_RATE_BPS,
    )
    claims = receiver_claim_rows_from_open_due(rows)

    assert rows == (
        OpenFundingDueRow(OPEN_PAYER, 40_000),
        OpenFundingDueRow(OPEN_RECEIVER, -60_000),
        OpenFundingDueRow(OPEN_RECEIVER_2, -40_000),
    )
    assert claims == (
        ReceiverClaimRow(OPEN_RECEIVER, 60_000),
        ReceiverClaimRow(OPEN_RECEIVER_2, 40_000),
    )


def test_payload_rejects_noncanonical_rationing() -> None:
    certificate = _certificate()
    payload = mixed_open_funding_netting_certificate_to_payload(certificate)
    rationing = dict(payload["receiver_haircut_rationing"])
    row = dict(rationing["receiver_rows"][0])
    row["haircut_quote"] = 29_999
    row["payable_quote"] = 70_001
    rationing["receiver_rows"] = [row]
    payload["receiver_haircut_rationing"] = rationing

    verdict = verify_mixed_open_funding_netting_certificate_payload(
        payload,
        post_accounts=_mixed_post_accounts(),
    )

    assert verdict == CertificateVerdict(False, "haircut_quote is not canonical")


def test_signed_netting_formula_sweep() -> None:
    for payer_position in (1, 17, 40_000, 123_456):
        for receiver_position in (-1, -23, -100_000, -234_567):
            certificate = build_mixed_open_funding_netting_certificate(
                (
                    PositionAccount(OPEN_PAYER, payer_position),
                    PositionAccount(OPEN_RECEIVER, receiver_position),
                ),
                epoch=EPOCH,
                price_e8=PRICE_E8,
                funding_rate_bps=FUNDING_RATE_BPS,
                receiver_haircut_sum_quote=0,
            )
            assert certificate.raw_post_open_due_sum_quote == (
                certificate.open_payer_due_sum_quote
                - certificate.receiver_claim_sum_quote
            )
            assert certificate.payable_post_open_due_sum_quote == (
                certificate.raw_post_open_due_sum_quote
                + certificate.receiver_haircut_sum_quote
            )
            assert validate_mixed_open_funding_netting_certificate(
                (
                    PositionAccount(OPEN_PAYER, payer_position),
                    PositionAccount(OPEN_RECEIVER, receiver_position),
                ),
                certificate,
            ) == CertificateVerdict(True, None)
