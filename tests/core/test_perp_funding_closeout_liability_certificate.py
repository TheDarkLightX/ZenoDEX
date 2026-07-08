from __future__ import annotations

from dataclasses import asdict

import pytest

from src.core.perp_funding_closeout_liability_certificate import (
    ALLOCATION_CERT_SCHEMA,
    CARRY_FORWARD_RECEIPT_SCHEMA,
    CERT_SCHEMA,
    RATIONED_ALLOCATION_RECEIPT_SCHEMA,
    SOURCE_BOUND_RATIONED_ALLOCATION_RECEIPT_SCHEMA,
    SOURCE_PORTFOLIO_BOUND_RATIONED_ALLOCATION_RECEIPT_SCHEMA,
    CertificateVerdict,
    ClosedFundingSourceRow,
    ClosedLiabilityAllocationRow,
    ClosedLiabilityRow,
    DueRow,
    FundingCloseoutAllocationCertificate,
    FundingCloseoutAllocationReceipt,
    FundingCloseoutCarryForwardReceipt,
    FundingCloseoutLiabilityCertificate,
    FundingCloseoutLiabilityReceipt,
    FundingCloseoutRationedAllocationReceipt,
    FundingCloseoutSourceBoundRationedAllocationReceipt,
    FundingCloseoutSourcePortfolioBoundRationedAllocationReceipt,
    PositionAccount,
    build_funding_closeout_allocation_certificate,
    build_funding_closeout_allocation_receipt,
    build_funding_closeout_carry_forward_receipt,
    build_funding_closeout_liability_certificate,
    build_funding_closeout_liability_receipt,
    build_funding_closeout_rationed_allocation_receipt,
    build_funding_closeout_source_bound_rationed_allocation_receipt,
    build_funding_closeout_source_portfolio_bound_rationed_allocation_receipt,
    carried_funding_closeout_liability_hash,
    closed_funding_source_rows_from_allocation_certificate,
    funding_closeout_allocation_certificate_from_payload,
    funding_closeout_allocation_certificate_to_payload,
    funding_closeout_allocation_receipt_to_payload,
    funding_closeout_carry_forward_receipt_from_payload,
    funding_closeout_carry_forward_receipt_to_payload,
    funding_closeout_liability_certificate_from_payload,
    funding_closeout_liability_certificate_to_payload,
    funding_closeout_liability_receipt_to_payload,
    funding_closeout_rationed_allocation_receipt_from_payload,
    funding_closeout_rationed_allocation_receipt_to_payload,
    funding_closeout_source_availability_hash,
    funding_closeout_source_bound_rationed_allocation_receipt_from_payload,
    funding_closeout_source_bound_rationed_allocation_receipt_to_payload,
    funding_closeout_source_portfolio_bound_rationed_allocation_receipt_from_payload,
    funding_closeout_source_portfolio_bound_rationed_allocation_receipt_to_payload,
    post_open_receiver_claim_rows,
    pre_close_position_snapshot_hash,
    pre_close_snapshot_hash,
    pre_due_vector_hash,
    validate_funding_closeout_allocation_certificate,
    validate_funding_closeout_liability_certificate,
    verify_funding_closeout_allocation_certificate_payload,
    verify_funding_closeout_allocation_receipt_payload,
    verify_funding_closeout_carry_forward_receipt_payload,
    verify_funding_closeout_liability_certificate_payload,
    verify_funding_closeout_liability_receipt_payload,
    verify_funding_closeout_rationed_allocation_receipt_payload,
    verify_funding_closeout_source_bound_rationed_allocation_receipt_payload,
    verify_funding_closeout_source_portfolio_bound_rationed_allocation_receipt_payload,
)
from src.core.perp_funding_closeout_receiver_rationing import (
    ReceiverClaimRow,
    build_receiver_haircut_rationing,
    receiver_haircut_rationing_to_payload,
)
from src.core.perp_v2.math import PRICE_SCALE

PRICE_E8 = 100 * PRICE_SCALE
FUNDING_RATE_BPS = 100
EPOCH = 3
PAYER = "aa" * 48
RECEIVER = "bb" * 48
RECEIVER_2 = "cc" * 48
PAYER_2 = "dd" * 48
POSITION_BASE = 100_000
MARKET_ID = "perp:funding-closeout-core"


def _pre_accounts() -> tuple[PositionAccount, ...]:
    return (
        PositionAccount(PAYER, POSITION_BASE),
        PositionAccount(RECEIVER, -POSITION_BASE),
    )


def _post_accounts() -> tuple[PositionAccount, ...]:
    return (
        PositionAccount(PAYER, 0),
        PositionAccount(RECEIVER, -POSITION_BASE),
    )


def _multi_receiver_pre_accounts() -> tuple[PositionAccount, ...]:
    return (
        PositionAccount(PAYER, POSITION_BASE),
        PositionAccount(RECEIVER, -60_000),
        PositionAccount(RECEIVER_2, -40_000),
    )


def _multi_receiver_post_accounts() -> tuple[PositionAccount, ...]:
    return (
        PositionAccount(PAYER, 0),
        PositionAccount(RECEIVER, -60_000),
        PositionAccount(RECEIVER_2, -40_000),
    )


def _carried_certificate() -> FundingCloseoutLiabilityCertificate:
    return build_funding_closeout_liability_certificate(
        _pre_accounts(),
        _post_accounts(),
        epoch=EPOCH,
        price_e8=PRICE_E8,
        funding_rate_bps=FUNDING_RATE_BPS,
    )


def _subrogated_certificate() -> FundingCloseoutLiabilityCertificate:
    return build_funding_closeout_liability_certificate(
        _pre_accounts(),
        _post_accounts(),
        epoch=EPOCH,
        price_e8=PRICE_E8,
        funding_rate_bps=FUNDING_RATE_BPS,
        sink_draw_by_account={PAYER: 100_000},
    )


def _subrogated_receipt() -> FundingCloseoutLiabilityReceipt:
    return build_funding_closeout_liability_receipt(
        _pre_accounts(),
        _post_accounts(),
        market_id=MARKET_ID,
        epoch=EPOCH,
        price_e8=PRICE_E8,
        funding_rate_bps=FUNDING_RATE_BPS,
        sink_draw_by_account={PAYER: 100_000},
    )


def _underfunded_allocation_certificate() -> FundingCloseoutAllocationCertificate:
    return build_funding_closeout_allocation_certificate(
        _pre_accounts(),
        _post_accounts(),
        epoch=EPOCH,
        price_e8=PRICE_E8,
        funding_rate_bps=FUNDING_RATE_BPS,
        payer_available_by_account={PAYER: 30_000},
        sink_capacity_by_account={PAYER: 40_000},
    )


def _underfunded_allocation_receipt() -> FundingCloseoutAllocationReceipt:
    return build_funding_closeout_allocation_receipt(
        _pre_accounts(),
        _post_accounts(),
        market_id=MARKET_ID,
        epoch=EPOCH,
        price_e8=PRICE_E8,
        funding_rate_bps=FUNDING_RATE_BPS,
        payer_available_by_account={PAYER: 30_000},
        sink_capacity_by_account={PAYER: 40_000},
    )


def _rationed_allocation_receipt() -> FundingCloseoutRationedAllocationReceipt:
    return build_funding_closeout_rationed_allocation_receipt(
        _multi_receiver_pre_accounts(),
        _multi_receiver_post_accounts(),
        market_id=MARKET_ID,
        epoch=EPOCH,
        price_e8=PRICE_E8,
        funding_rate_bps=FUNDING_RATE_BPS,
        payer_available_by_account={PAYER: 30_000},
        sink_capacity_by_account={PAYER: 40_000},
    )


def _source_bound_rationed_allocation_receipt(
) -> FundingCloseoutSourceBoundRationedAllocationReceipt:
    return build_funding_closeout_source_bound_rationed_allocation_receipt(
        _multi_receiver_pre_accounts(),
        _multi_receiver_post_accounts(),
        market_id=MARKET_ID,
        epoch=EPOCH,
        price_e8=PRICE_E8,
        funding_rate_bps=FUNDING_RATE_BPS,
        payer_available_by_account={PAYER: 30_000},
        sink_capacity_by_account={PAYER: 40_000},
    )


def _portfolio_pre_accounts() -> tuple[PositionAccount, ...]:
    return (
        PositionAccount(PAYER, 100_000),
        PositionAccount(RECEIVER, -90_000),
        PositionAccount(RECEIVER_2, -60_000),
        PositionAccount(PAYER_2, 50_000),
    )


def _portfolio_post_accounts() -> tuple[PositionAccount, ...]:
    return (
        PositionAccount(PAYER, 0),
        PositionAccount(RECEIVER, -90_000),
        PositionAccount(RECEIVER_2, -60_000),
        PositionAccount(PAYER_2, 0),
    )


def _portfolio_emitted_rows() -> tuple[ClosedFundingSourceRow, ...]:
    return (
        ClosedFundingSourceRow(PAYER, EPOCH, 0, 100_000),
        ClosedFundingSourceRow(PAYER_2, EPOCH, 0, 150_000),
    )


def _source_portfolio_receipt(
    *,
    aggregate_sink_capacity_quote: int = 150_000,
) -> FundingCloseoutSourcePortfolioBoundRationedAllocationReceipt:
    return build_funding_closeout_source_portfolio_bound_rationed_allocation_receipt(
        _portfolio_pre_accounts(),
        _portfolio_post_accounts(),
        market_id=MARKET_ID,
        epoch=EPOCH,
        price_e8=PRICE_E8,
        funding_rate_bps=FUNDING_RATE_BPS,
        emitted_source_availability_rows=_portfolio_emitted_rows(),
        aggregate_sink_capacity_quote=aggregate_sink_capacity_quote,
        sink_capacity_by_account={PAYER: 100_000, PAYER_2: 50_000},
    )


def _carry_forward_receipt() -> FundingCloseoutCarryForwardReceipt:
    return build_funding_closeout_carry_forward_receipt(
        _source_portfolio_receipt(),
        carry_epoch=EPOCH + 1,
    )


def _replace_certificate(
    certificate: FundingCloseoutLiabilityCertificate,
    **kwargs: object,
) -> FundingCloseoutLiabilityCertificate:
    values = asdict(certificate)
    values.update(kwargs)
    due_rows = tuple(DueRow(**row) if isinstance(row, dict) else row for row in values["pre_due_rows"])
    liability_rows = tuple(
        ClosedLiabilityRow(**row) if isinstance(row, dict) else row
        for row in values["closed_liability_rows"]
    )
    return FundingCloseoutLiabilityCertificate(
        schema=str(values["schema"]),
        epoch=int(values["epoch"]),
        price_e8=int(values["price_e8"]),
        funding_rate_bps=int(values["funding_rate_bps"]),
        pre_due_vector_hash=str(values["pre_due_vector_hash"]),
        pre_due_rows=due_rows,
        closed_liability_rows=liability_rows,
        post_open_due_sum_quote=int(values["post_open_due_sum_quote"]),
    )


def _replace_allocation_certificate(
    certificate: FundingCloseoutAllocationCertificate,
    **kwargs: object,
) -> FundingCloseoutAllocationCertificate:
    values = asdict(certificate)
    values.update(kwargs)
    due_rows = tuple(DueRow(**row) if isinstance(row, dict) else row for row in values["pre_due_rows"])
    allocation_rows = tuple(
        ClosedLiabilityAllocationRow(**row) if isinstance(row, dict) else row
        for row in values["closed_allocation_rows"]
    )
    return FundingCloseoutAllocationCertificate(
        schema=str(values["schema"]),
        epoch=int(values["epoch"]),
        price_e8=int(values["price_e8"]),
        funding_rate_bps=int(values["funding_rate_bps"]),
        pre_due_vector_hash=str(values["pre_due_vector_hash"]),
        pre_due_rows=due_rows,
        closed_allocation_rows=allocation_rows,
        raw_post_open_due_sum_quote=int(values["raw_post_open_due_sum_quote"]),
        payable_post_open_due_sum_quote=int(values["payable_post_open_due_sum_quote"]),
        receiver_haircut_sum_quote=int(values["receiver_haircut_sum_quote"]),
    )


def test_certificate_accepts_carried_closed_due_without_sink() -> None:
    cert = _carried_certificate()

    verdict = validate_funding_closeout_liability_certificate(_pre_accounts(), _post_accounts(), cert)

    assert verdict == CertificateVerdict(True, None)
    assert cert.closed_liability_rows == (
        ClosedLiabilityRow(
            account_pubkey=PAYER,
            epoch=EPOCH,
            closed_due_quote=100_000,
            carried_due_quote=100_000,
            sink_draw_quote=0,
            subrogated_claim_quote=0,
        ),
    )


def test_certificate_accepts_sink_subrogation() -> None:
    cert = _subrogated_certificate()

    verdict = validate_funding_closeout_liability_certificate(_pre_accounts(), _post_accounts(), cert)

    assert verdict == CertificateVerdict(True, None)
    assert cert.closed_liability_rows == (
        ClosedLiabilityRow(
            account_pubkey=PAYER,
            epoch=EPOCH,
            closed_due_quote=100_000,
            carried_due_quote=0,
            sink_draw_quote=100_000,
            subrogated_claim_quote=100_000,
        ),
    )


def test_payload_verifier_accepts_subrogated_certificate_with_expected_bindings() -> None:
    cert = _subrogated_certificate()
    payload = funding_closeout_liability_certificate_to_payload(cert)

    verdict = verify_funding_closeout_liability_certificate_payload(
        payload,
        expected_epoch=EPOCH,
        expected_price_e8=PRICE_E8,
        expected_funding_rate_bps=FUNDING_RATE_BPS,
        expected_pre_due_vector_hash=cert.pre_due_vector_hash,
        expected_post_open_due_sum_quote=cert.post_open_due_sum_quote,
    )

    assert verdict == CertificateVerdict(True, None)
    assert funding_closeout_liability_certificate_from_payload(payload) == cert


def test_receipt_verifier_accepts_market_epoch_root_bound_subrogation() -> None:
    receipt = _subrogated_receipt()

    verdict = verify_funding_closeout_liability_receipt_payload(
        funding_closeout_liability_receipt_to_payload(receipt),
        expected_market_id=MARKET_ID,
        expected_epoch=EPOCH,
        expected_price_e8=PRICE_E8,
        expected_funding_rate_bps=FUNDING_RATE_BPS,
        expected_pre_close_state_root_hash=receipt.pre_close_state_root_hash,
        expected_post_open_due_sum_quote=receipt.certificate.post_open_due_sum_quote,
    )

    assert verdict == CertificateVerdict(True, None)
    assert receipt.pre_due_vector_hash == receipt.certificate.pre_due_vector_hash
    assert receipt.pre_close_state_root_hash == pre_close_position_snapshot_hash(
        _pre_accounts(),
        market_id=MARKET_ID,
        epoch=EPOCH,
    )
    assert receipt.pre_close_state_root_hash != pre_close_snapshot_hash(
        _pre_accounts(),
        market_id=MARKET_ID,
        epoch=EPOCH,
        price_e8=PRICE_E8,
        funding_rate_bps=FUNDING_RATE_BPS,
    )


def test_receipt_verifier_rejects_wrong_market() -> None:
    receipt = _subrogated_receipt()

    verdict = verify_funding_closeout_liability_receipt_payload(
        funding_closeout_liability_receipt_to_payload(receipt),
        expected_market_id=MARKET_ID + "-other",
        expected_epoch=EPOCH,
        expected_price_e8=PRICE_E8,
        expected_funding_rate_bps=FUNDING_RATE_BPS,
        expected_pre_close_state_root_hash=receipt.pre_close_state_root_hash,
        expected_post_open_due_sum_quote=receipt.certificate.post_open_due_sum_quote,
    )

    assert verdict == CertificateVerdict(False, "market_id mismatch")


def test_receipt_verifier_rejects_wrong_state_root() -> None:
    receipt = _subrogated_receipt()

    verdict = verify_funding_closeout_liability_receipt_payload(
        funding_closeout_liability_receipt_to_payload(receipt),
        expected_market_id=MARKET_ID,
        expected_epoch=EPOCH,
        expected_price_e8=PRICE_E8,
        expected_funding_rate_bps=FUNDING_RATE_BPS,
        expected_pre_close_state_root_hash="sha256:" + "00" * 32,
        expected_post_open_due_sum_quote=receipt.certificate.post_open_due_sum_quote,
    )

    assert verdict == CertificateVerdict(False, "pre_close_state_root_hash mismatch")


def test_receipt_verifier_rejects_certificate_hash_mismatch() -> None:
    receipt = _subrogated_receipt()
    payload = funding_closeout_liability_receipt_to_payload(receipt)
    payload["pre_due_vector_hash"] = "sha256:" + "00" * 32

    verdict = verify_funding_closeout_liability_receipt_payload(
        payload,
        expected_market_id=MARKET_ID,
        expected_epoch=EPOCH,
        expected_price_e8=PRICE_E8,
        expected_funding_rate_bps=FUNDING_RATE_BPS,
        expected_pre_close_state_root_hash=receipt.pre_close_state_root_hash,
        expected_post_open_due_sum_quote=receipt.certificate.post_open_due_sum_quote,
    )

    assert verdict == CertificateVerdict(False, "receipt pre_due_vector_hash mismatch")


def test_receipt_verifier_rejects_root_not_matching_certificate_rows() -> None:
    receipt = _subrogated_receipt()
    wrong_root = pre_close_position_snapshot_hash(
        (PositionAccount(PAYER, POSITION_BASE),),
        market_id=MARKET_ID,
        epoch=EPOCH,
    )
    payload = funding_closeout_liability_receipt_to_payload(receipt)
    payload["pre_close_state_root_hash"] = wrong_root

    verdict = verify_funding_closeout_liability_receipt_payload(
        payload,
        expected_market_id=MARKET_ID,
        expected_epoch=EPOCH,
        expected_price_e8=PRICE_E8,
        expected_funding_rate_bps=FUNDING_RATE_BPS,
        expected_pre_close_state_root_hash=wrong_root,
        expected_post_open_due_sum_quote=receipt.certificate.post_open_due_sum_quote,
    )

    assert verdict == CertificateVerdict(False, "pre_close_state_root_hash does not match pre_due rows")


def test_payload_verifier_rejects_expected_hash_mismatch() -> None:
    cert = _subrogated_certificate()

    verdict = verify_funding_closeout_liability_certificate_payload(
        funding_closeout_liability_certificate_to_payload(cert),
        expected_epoch=EPOCH,
        expected_price_e8=PRICE_E8,
        expected_funding_rate_bps=FUNDING_RATE_BPS,
        expected_pre_due_vector_hash="sha256:" + "00" * 32,
        expected_post_open_due_sum_quote=cert.post_open_due_sum_quote,
    )

    assert verdict == CertificateVerdict(False, "pre_due_vector_hash mismatch")


def test_payload_verifier_rejects_expected_post_open_sum_mismatch() -> None:
    cert = _subrogated_certificate()

    verdict = verify_funding_closeout_liability_certificate_payload(
        funding_closeout_liability_certificate_to_payload(cert),
        expected_epoch=EPOCH,
        expected_price_e8=PRICE_E8,
        expected_funding_rate_bps=FUNDING_RATE_BPS,
        expected_pre_due_vector_hash=cert.pre_due_vector_hash,
        expected_post_open_due_sum_quote=cert.post_open_due_sum_quote + 1,
    )

    assert verdict == CertificateVerdict(False, "post_open_due_sum_quote mismatch")


def test_payload_verifier_rejects_silent_sink_without_subrogation() -> None:
    cert = _subrogated_certificate()
    payload = funding_closeout_liability_certificate_to_payload(cert)
    rows = list(payload["closed_liability_rows"])
    row = dict(rows[0])
    row["carried_due_quote"] = 0
    row["subrogated_claim_quote"] = 0
    rows[0] = row
    payload["closed_liability_rows"] = rows

    verdict = verify_funding_closeout_liability_certificate_payload(
        payload,
        expected_epoch=EPOCH,
        expected_price_e8=PRICE_E8,
        expected_funding_rate_bps=FUNDING_RATE_BPS,
        expected_pre_due_vector_hash=cert.pre_due_vector_hash,
        expected_post_open_due_sum_quote=cert.post_open_due_sum_quote,
    )

    assert verdict == CertificateVerdict(False, "sink draw must create matching subrogated claim")


def test_missing_closed_liability_rejects() -> None:
    broken = _replace_certificate(_carried_certificate(), closed_liability_rows=())

    verdict = validate_funding_closeout_liability_certificate(_pre_accounts(), _post_accounts(), broken)

    assert verdict == CertificateVerdict(False, "closed liability row set mismatch")


def test_wrong_closed_due_rejects() -> None:
    cert = _carried_certificate()
    row = cert.closed_liability_rows[0]
    broken_row = ClosedLiabilityRow(
        account_pubkey=row.account_pubkey,
        epoch=row.epoch,
        closed_due_quote=row.closed_due_quote - 1,
        carried_due_quote=row.carried_due_quote - 1,
        sink_draw_quote=row.sink_draw_quote,
        subrogated_claim_quote=row.subrogated_claim_quote,
    )
    broken = _replace_certificate(cert, closed_liability_rows=(broken_row,))

    verdict = validate_funding_closeout_liability_certificate(_pre_accounts(), _post_accounts(), broken)

    assert verdict == CertificateVerdict(False, "closed_due_quote mismatch")


def test_hash_mismatch_rejects() -> None:
    broken = _replace_certificate(_carried_certificate(), pre_due_vector_hash="sha256:" + "00" * 32)

    verdict = validate_funding_closeout_liability_certificate(_pre_accounts(), _post_accounts(), broken)

    assert verdict == CertificateVerdict(False, "pre_due_vector_hash mismatch")


def test_duplicate_liability_rejects() -> None:
    cert = _carried_certificate()
    row = cert.closed_liability_rows[0]
    broken = _replace_certificate(cert, closed_liability_rows=(row, row))

    verdict = validate_funding_closeout_liability_certificate(_pre_accounts(), _post_accounts(), broken)

    assert verdict == CertificateVerdict(False, "duplicate closed liability account")


def test_unsorted_pre_due_vector_rejects() -> None:
    broken = _replace_certificate(
        _carried_certificate(),
        pre_due_rows=tuple(reversed(_carried_certificate().pre_due_rows)),
    )

    verdict = validate_funding_closeout_liability_certificate(_pre_accounts(), _post_accounts(), broken)

    assert verdict == CertificateVerdict(False, "pre_due_rows must be sorted by account_pubkey")


def test_sink_draw_without_subrogation_rejects() -> None:
    cert = _subrogated_certificate()
    row = cert.closed_liability_rows[0]
    broken_row = ClosedLiabilityRow(
        account_pubkey=row.account_pubkey,
        epoch=row.epoch,
        closed_due_quote=row.closed_due_quote,
        carried_due_quote=row.carried_due_quote,
        sink_draw_quote=row.sink_draw_quote,
        subrogated_claim_quote=0,
    )
    broken = _replace_certificate(cert, closed_liability_rows=(broken_row,))

    verdict = validate_funding_closeout_liability_certificate(_pre_accounts(), _post_accounts(), broken)

    assert verdict == CertificateVerdict(False, "sink draw must create matching subrogated claim")


def test_certificate_hash_is_stable() -> None:
    cert = _carried_certificate()

    assert cert.pre_due_vector_hash == pre_due_vector_hash(cert.pre_due_rows)
    assert cert.pre_due_vector_hash == (
        "sha256:c898f65605d9fb3c556341eaa026806b283612791eb5bebe437309b8c42e48fe"
    )


def test_certificate_schema_is_validated() -> None:
    broken = _replace_certificate(_carried_certificate(), schema=CERT_SCHEMA + ".bad")

    verdict = validate_funding_closeout_liability_certificate(_pre_accounts(), _post_accounts(), broken)

    assert verdict == CertificateVerdict(False, "invalid certificate schema")


def test_value_objects_reject_bool_in_integer_fields() -> None:
    with pytest.raises(TypeError, match="position_base must be an int"):
        PositionAccount(PAYER, True)


def test_duplicate_pre_accounts_reject_before_certificate_build() -> None:
    duplicate_pre = (
        PositionAccount(PAYER, POSITION_BASE),
        PositionAccount(PAYER, POSITION_BASE),
    )

    with pytest.raises(ValueError, match="pre_accounts contains duplicate account_pubkey"):
        build_funding_closeout_liability_certificate(
            duplicate_pre,
            _post_accounts(),
            epoch=EPOCH,
            price_e8=PRICE_E8,
            funding_rate_bps=FUNDING_RATE_BPS,
        )


def test_unknown_sink_draw_account_rejects() -> None:
    with pytest.raises(ValueError, match="sink draw account is not closed with nonzero due"):
        build_funding_closeout_liability_certificate(
            _pre_accounts(),
            _post_accounts(),
            epoch=EPOCH,
            price_e8=PRICE_E8,
            funding_rate_bps=FUNDING_RATE_BPS,
            sink_draw_by_account={"cc" * 48: 1},
        )


def test_v1_certificate_rejects_underfunded_haircut_shape() -> None:
    cert = _carried_certificate()
    payload = funding_closeout_liability_certificate_to_payload(cert)
    rows = list(payload["closed_liability_rows"])
    row = dict(rows[0])
    row["carried_due_quote"] = 0
    row["sink_draw_quote"] = 40_000
    row["subrogated_claim_quote"] = 40_000
    rows[0] = row
    payload["closed_liability_rows"] = rows

    verdict = verify_funding_closeout_liability_certificate_payload(
        payload,
        expected_epoch=EPOCH,
        expected_price_e8=PRICE_E8,
        expected_funding_rate_bps=FUNDING_RATE_BPS,
        expected_pre_due_vector_hash=cert.pre_due_vector_hash,
        expected_post_open_due_sum_quote=cert.post_open_due_sum_quote,
    )

    assert verdict == CertificateVerdict(
        False,
        "positive closed due is not fully carried or subrogated",
    )


def test_v2_allocation_certificate_accepts_underfunded_haircut() -> None:
    cert = _underfunded_allocation_certificate()

    verdict = validate_funding_closeout_allocation_certificate(
        _pre_accounts(),
        _post_accounts(),
        cert,
    )

    assert verdict == CertificateVerdict(True, None)
    assert cert.closed_allocation_rows == (
        ClosedLiabilityAllocationRow(
            account_pubkey=PAYER,
            epoch=EPOCH,
            closed_due_quote=100_000,
            payer_available_quote=30_000,
            sink_capacity_quote=40_000,
            payer_debit_quote=30_000,
            sink_draw_quote=40_000,
            subrogated_claim_quote=40_000,
            receiver_haircut_quote=30_000,
            paid_to_receiver_quote=70_000,
        ),
    )
    assert cert.raw_post_open_due_sum_quote == -100_000
    assert cert.payable_post_open_due_sum_quote == -70_000
    assert cert.receiver_haircut_sum_quote == 30_000


def test_v2_payload_verifier_accepts_underfunded_certificate() -> None:
    cert = _underfunded_allocation_certificate()
    payload = funding_closeout_allocation_certificate_to_payload(cert)

    verdict = verify_funding_closeout_allocation_certificate_payload(
        payload,
        expected_epoch=EPOCH,
        expected_price_e8=PRICE_E8,
        expected_funding_rate_bps=FUNDING_RATE_BPS,
        expected_pre_due_vector_hash=cert.pre_due_vector_hash,
        expected_raw_post_open_due_sum_quote=-100_000,
        expected_payable_post_open_due_sum_quote=-70_000,
    )

    assert verdict == CertificateVerdict(True, None)
    assert funding_closeout_allocation_certificate_from_payload(payload) == cert


def test_v2_payload_verifier_rejects_raw_post_sum_mismatch() -> None:
    cert = _underfunded_allocation_certificate()
    payload = funding_closeout_allocation_certificate_to_payload(cert)

    verdict = verify_funding_closeout_allocation_certificate_payload(
        payload,
        expected_raw_post_open_due_sum_quote=-70_000,
        expected_payable_post_open_due_sum_quote=-70_000,
    )

    assert verdict == CertificateVerdict(False, "raw_post_open_due_sum_quote mismatch")


def test_v2_receipt_verifier_accepts_root_bound_underfunded_certificate() -> None:
    receipt = _underfunded_allocation_receipt()

    verdict = verify_funding_closeout_allocation_receipt_payload(
        funding_closeout_allocation_receipt_to_payload(receipt),
        expected_market_id=MARKET_ID,
        expected_epoch=EPOCH,
        expected_price_e8=PRICE_E8,
        expected_funding_rate_bps=FUNDING_RATE_BPS,
        expected_pre_close_state_root_hash=receipt.pre_close_state_root_hash,
        expected_raw_post_open_due_sum_quote=-100_000,
        expected_payable_post_open_due_sum_quote=-70_000,
    )

    assert verdict == CertificateVerdict(True, None)
    assert receipt.pre_close_state_root_hash == pre_close_position_snapshot_hash(
        _pre_accounts(),
        market_id=MARKET_ID,
        epoch=EPOCH,
    )


def test_v2_receipt_verifier_rejects_raw_post_sum_mismatch() -> None:
    receipt = _underfunded_allocation_receipt()

    verdict = verify_funding_closeout_allocation_receipt_payload(
        funding_closeout_allocation_receipt_to_payload(receipt),
        expected_market_id=MARKET_ID,
        expected_epoch=EPOCH,
        expected_price_e8=PRICE_E8,
        expected_funding_rate_bps=FUNDING_RATE_BPS,
        expected_pre_close_state_root_hash=receipt.pre_close_state_root_hash,
        expected_raw_post_open_due_sum_quote=-70_000,
        expected_payable_post_open_due_sum_quote=-70_000,
    )

    assert verdict == CertificateVerdict(False, "raw_post_open_due_sum_quote mismatch")


def test_v2_payload_rejects_no_haircut_mutation() -> None:
    cert = _underfunded_allocation_certificate()
    payload = funding_closeout_allocation_certificate_to_payload(cert)
    rows = list(payload["closed_allocation_rows"])
    row = dict(rows[0])
    row["receiver_haircut_quote"] = 0
    rows[0] = row
    payload["closed_allocation_rows"] = rows

    verdict = verify_funding_closeout_allocation_certificate_payload(payload)

    assert verdict == CertificateVerdict(False, "receiver_haircut_quote mismatch")


def test_v2_payload_rejects_unadjusted_payable_sum() -> None:
    cert = _underfunded_allocation_certificate()
    broken = _replace_allocation_certificate(
        cert,
        payable_post_open_due_sum_quote=cert.raw_post_open_due_sum_quote,
    )

    verdict = validate_funding_closeout_allocation_certificate(
        _pre_accounts(),
        _post_accounts(),
        broken,
    )

    assert verdict == CertificateVerdict(False, "payable_post_open_due_sum_quote mismatch")


def test_v2_payload_rejects_sink_draw_without_subrogation() -> None:
    cert = _underfunded_allocation_certificate()
    payload = funding_closeout_allocation_certificate_to_payload(cert)
    rows = list(payload["closed_allocation_rows"])
    row = dict(rows[0])
    row["subrogated_claim_quote"] = 0
    rows[0] = row
    payload["closed_allocation_rows"] = rows

    verdict = verify_funding_closeout_allocation_certificate_payload(payload)

    assert verdict == CertificateVerdict(False, "subrogated_claim_quote mismatch")


def test_v2_payload_rejects_duplicate_allocation_rows() -> None:
    cert = _underfunded_allocation_certificate()
    row = cert.closed_allocation_rows[0]
    broken = _replace_allocation_certificate(cert, closed_allocation_rows=(row, row))

    verdict = validate_funding_closeout_allocation_certificate(
        _pre_accounts(),
        _post_accounts(),
        broken,
    )

    assert verdict == CertificateVerdict(False, "duplicate closed allocation account")


def test_v2_receipt_rejects_wrong_market() -> None:
    receipt = _underfunded_allocation_receipt()

    verdict = verify_funding_closeout_allocation_receipt_payload(
        funding_closeout_allocation_receipt_to_payload(receipt),
        expected_market_id=MARKET_ID + "-other",
        expected_epoch=EPOCH,
        expected_price_e8=PRICE_E8,
        expected_funding_rate_bps=FUNDING_RATE_BPS,
        expected_pre_close_state_root_hash=receipt.pre_close_state_root_hash,
        expected_payable_post_open_due_sum_quote=-70_000,
    )

    assert verdict == CertificateVerdict(False, "market_id mismatch")


def test_v2_receipt_rejects_wrong_state_root() -> None:
    receipt = _underfunded_allocation_receipt()

    verdict = verify_funding_closeout_allocation_receipt_payload(
        funding_closeout_allocation_receipt_to_payload(receipt),
        expected_market_id=MARKET_ID,
        expected_epoch=EPOCH,
        expected_price_e8=PRICE_E8,
        expected_funding_rate_bps=FUNDING_RATE_BPS,
        expected_pre_close_state_root_hash="sha256:" + "00" * 32,
        expected_payable_post_open_due_sum_quote=-70_000,
    )

    assert verdict == CertificateVerdict(False, "pre_close_state_root_hash mismatch")


def test_v2_builder_rejects_closed_receiver_due() -> None:
    post_accounts = (
        PositionAccount(PAYER, 0),
        PositionAccount(RECEIVER, 0),
    )

    with pytest.raises(
        ValueError,
        match="allocation certificate only supports positive closed due",
    ):
        build_funding_closeout_allocation_certificate(
            _pre_accounts(),
            post_accounts,
            epoch=EPOCH,
            price_e8=PRICE_E8,
            funding_rate_bps=FUNDING_RATE_BPS,
            payer_available_by_account={PAYER: 30_000, RECEIVER: 0},
            sink_capacity_by_account={PAYER: 40_000, RECEIVER: 0},
        )


def test_v2_schema_is_validated() -> None:
    cert = _underfunded_allocation_certificate()
    broken = _replace_allocation_certificate(cert, schema=ALLOCATION_CERT_SCHEMA + ".bad")

    verdict = validate_funding_closeout_allocation_certificate(
        _pre_accounts(),
        _post_accounts(),
        broken,
    )

    assert verdict == CertificateVerdict(False, "invalid allocation certificate schema")


def test_v3_rationed_receipt_accepts_multi_receiver_haircuts() -> None:
    receipt = _rationed_allocation_receipt()
    expected_claim_rows = post_open_receiver_claim_rows(
        _multi_receiver_post_accounts(),
        price_e8=PRICE_E8,
        funding_rate_bps=FUNDING_RATE_BPS,
    )

    verdict = verify_funding_closeout_rationed_allocation_receipt_payload(
        funding_closeout_rationed_allocation_receipt_to_payload(receipt),
        expected_market_id=MARKET_ID,
        expected_epoch=EPOCH,
        expected_price_e8=PRICE_E8,
        expected_funding_rate_bps=FUNDING_RATE_BPS,
        expected_pre_close_state_root_hash=receipt.pre_close_state_root_hash,
        expected_raw_post_open_due_sum_quote=-100_000,
        expected_payable_post_open_due_sum_quote=-70_000,
        expected_receiver_claim_rows=expected_claim_rows,
    )

    assert verdict == CertificateVerdict(True, None)
    assert receipt.schema == RATIONED_ALLOCATION_RECEIPT_SCHEMA
    assert funding_closeout_rationed_allocation_receipt_from_payload(
        funding_closeout_rationed_allocation_receipt_to_payload(receipt)
    ) == receipt
    rows = {
        row.account_pubkey: row
        for row in receipt.receiver_haircut_rationing.receiver_rows
    }
    assert rows[RECEIVER].haircut_quote == 18_000
    assert rows[RECEIVER].payable_quote == 42_000
    assert rows[RECEIVER_2].haircut_quote == 12_000
    assert rows[RECEIVER_2].payable_quote == 28_000


def test_v2_receipt_verifier_rejects_v3_payload_shape() -> None:
    payload = funding_closeout_rationed_allocation_receipt_to_payload(
        _rationed_allocation_receipt()
    )

    verdict = verify_funding_closeout_allocation_receipt_payload(payload)

    assert verdict == CertificateVerdict(False, "allocation_receipt keys mismatch")


def test_v3_receipt_rejects_missing_rationing_object() -> None:
    payload = funding_closeout_rationed_allocation_receipt_to_payload(
        _rationed_allocation_receipt()
    )
    del payload["receiver_haircut_rationing"]

    verdict = verify_funding_closeout_rationed_allocation_receipt_payload(payload)

    assert verdict == CertificateVerdict(False, "rationed_allocation_receipt keys mismatch")


def test_v3_receipt_rejects_noncanonical_priority_haircut() -> None:
    receipt = _rationed_allocation_receipt()
    payload = funding_closeout_rationed_allocation_receipt_to_payload(receipt)
    rationing = dict(payload["receiver_haircut_rationing"])
    rows = list(rationing["receiver_rows"])
    first = dict(rows[0])
    second = dict(rows[1])
    first["haircut_quote"] = 30_000
    first["payable_quote"] = 30_000
    second["haircut_quote"] = 0
    second["payable_quote"] = 40_000
    rationing["receiver_rows"] = [first, second]
    payload["receiver_haircut_rationing"] = rationing

    verdict = verify_funding_closeout_rationed_allocation_receipt_payload(payload)

    assert verdict == CertificateVerdict(False, "haircut_quote is not canonical")


def test_v3_receipt_rejects_canonical_but_wrong_receiver_claims() -> None:
    receipt = _rationed_allocation_receipt()
    payload = funding_closeout_rationed_allocation_receipt_to_payload(receipt)
    wrong_rationing = build_receiver_haircut_rationing(
        (
            ReceiverClaimRow(RECEIVER, 50_000),
            ReceiverClaimRow(RECEIVER_2, 50_000),
        ),
        total_haircut_quote=30_000,
    )
    payload["receiver_haircut_rationing"] = receiver_haircut_rationing_to_payload(
        wrong_rationing
    )

    verdict = verify_funding_closeout_rationed_allocation_receipt_payload(
        payload,
        expected_receiver_claim_rows=post_open_receiver_claim_rows(
            _multi_receiver_post_accounts(),
            price_e8=PRICE_E8,
            funding_rate_bps=FUNDING_RATE_BPS,
        ),
    )

    assert verdict == CertificateVerdict(False, "receiver haircut rationing mismatch")


def test_v4_source_bound_rationed_receipt_accepts_expected_source_root() -> None:
    receipt = _source_bound_rationed_allocation_receipt()
    expected_claim_rows = post_open_receiver_claim_rows(
        _multi_receiver_post_accounts(),
        price_e8=PRICE_E8,
        funding_rate_bps=FUNDING_RATE_BPS,
    )

    verdict = verify_funding_closeout_source_bound_rationed_allocation_receipt_payload(
        funding_closeout_source_bound_rationed_allocation_receipt_to_payload(receipt),
        expected_market_id=MARKET_ID,
        expected_epoch=EPOCH,
        expected_price_e8=PRICE_E8,
        expected_funding_rate_bps=FUNDING_RATE_BPS,
        expected_pre_close_state_root_hash=receipt.pre_close_state_root_hash,
        expected_source_availability_hash=receipt.source_availability_hash,
        expected_raw_post_open_due_sum_quote=-100_000,
        expected_payable_post_open_due_sum_quote=-70_000,
        expected_receiver_claim_rows=expected_claim_rows,
    )

    assert verdict == CertificateVerdict(True, None)
    assert receipt.schema == SOURCE_BOUND_RATIONED_ALLOCATION_RECEIPT_SCHEMA
    assert funding_closeout_source_bound_rationed_allocation_receipt_from_payload(
        funding_closeout_source_bound_rationed_allocation_receipt_to_payload(receipt)
    ) == receipt
    assert receipt.source_availability_rows == (
        ClosedFundingSourceRow(
            account_pubkey=PAYER,
            epoch=EPOCH,
            payer_available_quote=30_000,
            sink_capacity_quote=40_000,
        ),
    )
    assert receipt.source_availability_rows == (
        closed_funding_source_rows_from_allocation_certificate(receipt.certificate)
    )
    assert receipt.source_availability_hash == funding_closeout_source_availability_hash(
        receipt.source_availability_rows
    )


def test_v4_receipt_rejects_wrong_expected_source_root() -> None:
    receipt = _source_bound_rationed_allocation_receipt()

    verdict = verify_funding_closeout_source_bound_rationed_allocation_receipt_payload(
        funding_closeout_source_bound_rationed_allocation_receipt_to_payload(receipt),
        expected_source_availability_hash="sha256:" + "0" * 64,
    )

    assert verdict == CertificateVerdict(False, "source_availability_hash mismatch")


def test_v4_receipt_rejects_source_row_amount_mismatch() -> None:
    receipt = _source_bound_rationed_allocation_receipt()
    payload = funding_closeout_source_bound_rationed_allocation_receipt_to_payload(
        receipt
    )
    source_row = dict(payload["source_availability_rows"][0])
    source_row["payer_available_quote"] = 30_001
    mutated_source_rows = (
        ClosedFundingSourceRow(
            account_pubkey=str(source_row["account_pubkey"]),
            epoch=int(source_row["epoch"]),
            payer_available_quote=int(source_row["payer_available_quote"]),
            sink_capacity_quote=int(source_row["sink_capacity_quote"]),
        ),
    )
    payload["source_availability_rows"] = [source_row]
    payload["source_availability_hash"] = funding_closeout_source_availability_hash(
        mutated_source_rows
    )

    verdict = verify_funding_closeout_source_bound_rationed_allocation_receipt_payload(
        payload
    )

    assert verdict == CertificateVerdict(False, "source availability rows mismatch")


def test_v4_receipt_rejects_missing_source_rows() -> None:
    payload = funding_closeout_source_bound_rationed_allocation_receipt_to_payload(
        _source_bound_rationed_allocation_receipt()
    )
    del payload["source_availability_rows"]

    verdict = verify_funding_closeout_source_bound_rationed_allocation_receipt_payload(
        payload
    )

    assert verdict == CertificateVerdict(
        False,
        "source_bound_rationed_allocation_receipt keys mismatch",
    )


def test_v5_source_portfolio_receipt_accepts_expected_pending_roots() -> None:
    receipt = _source_portfolio_receipt()
    expected_claim_rows = post_open_receiver_claim_rows(
        _portfolio_post_accounts(),
        price_e8=PRICE_E8,
        funding_rate_bps=FUNDING_RATE_BPS,
    )

    verdict = (
        verify_funding_closeout_source_portfolio_bound_rationed_allocation_receipt_payload(
            funding_closeout_source_portfolio_bound_rationed_allocation_receipt_to_payload(
                receipt
            ),
            expected_market_id=MARKET_ID,
            expected_epoch=EPOCH,
            expected_price_e8=PRICE_E8,
            expected_funding_rate_bps=FUNDING_RATE_BPS,
            expected_pre_close_state_root_hash=receipt.pre_close_state_root_hash,
            expected_pending_source_availability_hashes=(
                receipt.pending_source_availability_hashes
            ),
            expected_aggregate_sink_capacity_quote=150_000,
            expected_raw_post_open_due_sum_quote=-150_000,
            expected_payable_post_open_due_sum_quote=-150_000,
            expected_receiver_claim_rows=expected_claim_rows,
        )
    )

    assert verdict == CertificateVerdict(True, None)
    assert receipt.schema == SOURCE_PORTFOLIO_BOUND_RATIONED_ALLOCATION_RECEIPT_SCHEMA
    assert funding_closeout_source_portfolio_bound_rationed_allocation_receipt_from_payload(
        funding_closeout_source_portfolio_bound_rationed_allocation_receipt_to_payload(
            receipt
        )
    ) == receipt
    assert receipt.source_availability_rows == (
        ClosedFundingSourceRow(PAYER, EPOCH, 0, 100_000),
        ClosedFundingSourceRow(PAYER_2, EPOCH, 0, 50_000),
    )
    assert receipt.pending_source_availability_hashes == tuple(
        sorted(
            funding_closeout_source_availability_hash((row,))
            for row in receipt.emitted_source_availability_rows
        )
    )


def test_v5_source_portfolio_receipt_rejects_pending_root_mismatch() -> None:
    payload = (
        funding_closeout_source_portfolio_bound_rationed_allocation_receipt_to_payload(
            _source_portfolio_receipt()
        )
    )
    payload["pending_source_availability_hashes"] = ["sha256:" + "11" * 32]

    verdict = (
        verify_funding_closeout_source_portfolio_bound_rationed_allocation_receipt_payload(
            payload
        )
    )

    assert verdict == CertificateVerdict(
        False,
        "pending source availability hashes mismatch",
    )


def test_v5_source_portfolio_receipt_rejects_over_reserved_sink_capacity() -> None:
    payload = (
        funding_closeout_source_portfolio_bound_rationed_allocation_receipt_to_payload(
            _source_portfolio_receipt(aggregate_sink_capacity_quote=149_999)
        )
    )

    verdict = (
        verify_funding_closeout_source_portfolio_bound_rationed_allocation_receipt_payload(
            payload
        )
    )

    assert verdict == CertificateVerdict(
        False,
        "source sink reservation exceeds aggregate capacity",
    )


def test_v5_source_portfolio_receipt_rejects_emitted_payer_source_mismatch() -> None:
    payload = (
        funding_closeout_source_portfolio_bound_rationed_allocation_receipt_to_payload(
            _source_portfolio_receipt()
        )
    )
    emitted_rows = list(payload["emitted_source_availability_rows"])
    first_row = dict(emitted_rows[0])
    first_row["payer_available_quote"] = 1
    emitted_rows[0] = first_row
    payload["emitted_source_availability_rows"] = emitted_rows
    mutated_rows = tuple(
        ClosedFundingSourceRow(
            account_pubkey=str(row["account_pubkey"]),
            epoch=int(row["epoch"]),
            payer_available_quote=int(row["payer_available_quote"]),
            sink_capacity_quote=int(row["sink_capacity_quote"]),
        )
        for row in emitted_rows
    )
    payload["pending_source_availability_hashes"] = list(
        sorted(
            funding_closeout_source_availability_hash((row,))
            for row in mutated_rows
        )
    )

    verdict = (
        verify_funding_closeout_source_portfolio_bound_rationed_allocation_receipt_payload(
            payload
        )
    )

    assert verdict == CertificateVerdict(
        False,
        "source availability row does not match emitted payer source",
    )


def test_v5_source_portfolio_receipt_rejects_expected_aggregate_mismatch() -> None:
    receipt = _source_portfolio_receipt()

    verdict = (
        verify_funding_closeout_source_portfolio_bound_rationed_allocation_receipt_payload(
            funding_closeout_source_portfolio_bound_rationed_allocation_receipt_to_payload(
                receipt
            ),
            expected_aggregate_sink_capacity_quote=149_999,
        )
    )

    assert verdict == CertificateVerdict(False, "aggregate sink capacity mismatch")


def test_carry_forward_receipt_accepts_source_portfolio_root_binding() -> None:
    receipt = _carry_forward_receipt()
    payload = funding_closeout_carry_forward_receipt_to_payload(receipt)

    verdict = verify_funding_closeout_carry_forward_receipt_payload(
        payload,
        expected_market_id=MARKET_ID,
        expected_source_epoch=EPOCH,
        expected_carry_epoch=EPOCH + 1,
        expected_pre_close_state_root_hash=receipt.pre_close_state_root_hash,
        expected_pending_source_availability_hashes=(
            receipt.pending_source_availability_hashes
        ),
        expected_carried_liability_hash=receipt.carried_liability_hash,
        expected_aggregate_sink_capacity_quote=150_000,
    )

    assert verdict == CertificateVerdict(True, None)
    assert receipt.schema == CARRY_FORWARD_RECEIPT_SCHEMA
    assert receipt.carried_liability_hash == carried_funding_closeout_liability_hash(
        receipt
    )
    assert funding_closeout_carry_forward_receipt_from_payload(payload) == receipt


def test_carry_forward_receipt_rejects_non_forward_epoch() -> None:
    receipt = build_funding_closeout_carry_forward_receipt(
        _source_portfolio_receipt(),
        carry_epoch=EPOCH,
    )

    verdict = verify_funding_closeout_carry_forward_receipt_payload(
        funding_closeout_carry_forward_receipt_to_payload(receipt)
    )

    assert verdict == CertificateVerdict(
        False,
        "carry_epoch must be greater than source_epoch",
    )


def test_carry_forward_receipt_rejects_pending_source_hash_mismatch() -> None:
    receipt = _carry_forward_receipt()

    verdict = verify_funding_closeout_carry_forward_receipt_payload(
        funding_closeout_carry_forward_receipt_to_payload(receipt),
        expected_pending_source_availability_hashes=("sha256:" + "99" * 32,),
    )

    assert verdict == CertificateVerdict(
        False,
        "pending source availability hashes mismatch",
    )


def test_carry_forward_receipt_rejects_carried_hash_mutation() -> None:
    payload = funding_closeout_carry_forward_receipt_to_payload(
        _carry_forward_receipt()
    )
    payload["carried_liability_hash"] = "sha256:" + "88" * 32

    verdict = verify_funding_closeout_carry_forward_receipt_payload(payload)

    assert verdict == CertificateVerdict(False, "carried_liability_hash mismatch")


def test_exact_count() -> None:
    tests = [
        name
        for name, value in globals().items()
        if name.startswith("test_") and callable(value) and name != "test_exact_count"
    ]
    assert len(tests) == 54
