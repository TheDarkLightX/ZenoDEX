from __future__ import annotations

from src.core.perp_funding_closeout_liability_certificate import (
    ClosedFundingSourceRow,
    PositionAccount,
    build_funding_closeout_source_portfolio_bound_rationed_allocation_receipt,
    funding_closeout_source_portfolio_receipt_hash,
)
from src.core.perp_funding_closeout_policy_ledger import (
    HAIRCUT_POLICY_FINAL_LOSS,
    HAIRCUT_POLICY_RECOVERABLE_CLAIM,
    PolicyLedgerVerdict,
    build_funding_closeout_policy_ledger,
    funding_closeout_policy_ledger_to_payload,
    verify_funding_closeout_policy_ledger_payload,
)
from src.core.perp_v2.math import PRICE_SCALE

PRICE_E8 = 100 * PRICE_SCALE
FUNDING_RATE_BPS = 100
EPOCH = 3
MARKET_ID = "perp:funding-closeout-policy-ledger"
PAYER_A = "aa" * 48
RECEIVER_A = "bb" * 48
RECEIVER_B = "cc" * 48
PAYER_B = "dd" * 48


def _pre_accounts() -> tuple[PositionAccount, ...]:
    return (
        PositionAccount(PAYER_A, 100_000),
        PositionAccount(RECEIVER_A, -90_000),
        PositionAccount(RECEIVER_B, -60_000),
        PositionAccount(PAYER_B, 50_000),
    )


def _post_accounts() -> tuple[PositionAccount, ...]:
    return (
        PositionAccount(PAYER_A, 0),
        PositionAccount(RECEIVER_A, -90_000),
        PositionAccount(RECEIVER_B, -60_000),
        PositionAccount(PAYER_B, 0),
    )


def _emitted_source_rows() -> tuple[ClosedFundingSourceRow, ...]:
    return (
        ClosedFundingSourceRow(PAYER_A, EPOCH, 0, 145_000),
        ClosedFundingSourceRow(PAYER_B, EPOCH, 0, 150_000),
    )


def _source_portfolio_receipt():
    return build_funding_closeout_source_portfolio_bound_rationed_allocation_receipt(
        _pre_accounts(),
        _post_accounts(),
        market_id=MARKET_ID,
        epoch=EPOCH,
        price_e8=PRICE_E8,
        funding_rate_bps=FUNDING_RATE_BPS,
        emitted_source_availability_rows=_emitted_source_rows(),
        aggregate_sink_capacity_quote=150_000,
        sink_capacity_by_account={PAYER_A: 100_000, PAYER_B: 50_000},
    )


def _verify_payload(payload: object, receipt=None) -> PolicyLedgerVerdict:
    return verify_funding_closeout_policy_ledger_payload(
        payload,
        source_portfolio_receipt=receipt,
    )


def test_final_loss_policy_ledger_accepts_source_portfolio_receipt() -> None:
    receipt = _source_portfolio_receipt()
    ledger = build_funding_closeout_policy_ledger(
        receipt,
        haircut_policy=HAIRCUT_POLICY_FINAL_LOSS,
    )

    assert _verify_payload(
        funding_closeout_policy_ledger_to_payload(ledger),
        receipt,
    ) == PolicyLedgerVerdict(True, None)
    assert ledger.total_receiver_haircut_quote == 0
    assert ledger.total_final_loss_quote == 0
    assert ledger.total_recoverable_claim_quote == 0
    assert ledger.total_sink_draw_quote == 150_000
    assert ledger.total_subrogated_claim_quote == 150_000


def test_recoverable_policy_accepts_same_receipt_hash() -> None:
    receipt = _source_portfolio_receipt()
    final_loss = build_funding_closeout_policy_ledger(
        receipt,
        haircut_policy=HAIRCUT_POLICY_FINAL_LOSS,
    )
    recoverable = build_funding_closeout_policy_ledger(
        receipt,
        haircut_policy=HAIRCUT_POLICY_RECOVERABLE_CLAIM,
    )

    assert final_loss.source_portfolio_receipt_hash == recoverable.source_portfolio_receipt_hash
    assert final_loss.source_portfolio_receipt_hash == (
        funding_closeout_source_portfolio_receipt_hash(receipt)
    )
    assert final_loss.haircut_policy != recoverable.haircut_policy
    assert _verify_payload(funding_closeout_policy_ledger_to_payload(final_loss), receipt).ok
    assert _verify_payload(funding_closeout_policy_ledger_to_payload(recoverable), receipt).ok


def test_missing_receiver_haircut_row_rejects_against_receipt() -> None:
    receipt = _source_portfolio_receipt()
    ledger = build_funding_closeout_policy_ledger(
        receipt,
        haircut_policy=HAIRCUT_POLICY_RECOVERABLE_CLAIM,
    )
    payload = funding_closeout_policy_ledger_to_payload(ledger)
    payload["receiver_haircut_rows"] = []

    assert _verify_payload(payload, receipt) == PolicyLedgerVerdict(
        False,
        "policy ledger receiver haircut rows mismatch",
    )


def test_double_classified_haircut_rejects_structurally() -> None:
    receipt = build_funding_closeout_source_portfolio_bound_rationed_allocation_receipt(
        _pre_accounts(),
        _post_accounts(),
        market_id=MARKET_ID,
        epoch=EPOCH,
        price_e8=PRICE_E8,
        funding_rate_bps=FUNDING_RATE_BPS,
        emitted_source_availability_rows=_emitted_source_rows(),
        aggregate_sink_capacity_quote=70_000,
        sink_capacity_by_account={PAYER_A: 40_000, PAYER_B: 30_000},
    )
    ledger = build_funding_closeout_policy_ledger(
        receipt,
        haircut_policy=HAIRCUT_POLICY_FINAL_LOSS,
    )
    payload = funding_closeout_policy_ledger_to_payload(ledger)
    rows = list(payload["receiver_haircut_rows"])
    first = dict(rows[0])
    first["recoverable_claim_quote"] = first["haircut_quote"]
    rows[0] = first
    payload["receiver_haircut_rows"] = rows
    payload["total_recoverable_claim_quote"] = first["haircut_quote"]

    assert _verify_payload(payload) == PolicyLedgerVerdict(
        False,
        "haircut policy row does not classify full haircut",
    )


def test_missing_sink_subrogation_rejects_against_receipt() -> None:
    receipt = _source_portfolio_receipt()
    ledger = build_funding_closeout_policy_ledger(
        receipt,
        haircut_policy=HAIRCUT_POLICY_FINAL_LOSS,
    )
    payload = funding_closeout_policy_ledger_to_payload(ledger)
    payload["sink_subrogation_rows"] = payload["sink_subrogation_rows"][:1]
    payload["total_sink_draw_quote"] = 100_000
    payload["total_subrogated_claim_quote"] = 100_000

    assert _verify_payload(payload, receipt) == PolicyLedgerVerdict(
        False,
        "policy ledger sink subrogation rows mismatch",
    )


def test_wrong_source_receipt_hash_rejects_against_receipt() -> None:
    receipt = _source_portfolio_receipt()
    ledger = build_funding_closeout_policy_ledger(
        receipt,
        haircut_policy=HAIRCUT_POLICY_FINAL_LOSS,
    )
    payload = funding_closeout_policy_ledger_to_payload(ledger)
    payload["source_portfolio_receipt_hash"] = "sha256:" + "0" * 64

    assert _verify_payload(payload, receipt) == PolicyLedgerVerdict(
        False,
        "policy ledger source receipt hash mismatch",
    )
