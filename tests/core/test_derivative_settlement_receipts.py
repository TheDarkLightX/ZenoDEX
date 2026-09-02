"""Tests for derivative settlement receipt envelopes."""

from __future__ import annotations

from hypothesis import given, settings
import hypothesis.strategies as st

from src.core.derivative_settlement_receipts import (
    DERIVATIVE_SETTLEMENT_RECEIPT_MAX_COLLATERAL,
    DERIVATIVE_SETTLEMENT_RECEIPT_SCHEMA,
    DerivativeSettlementReceiptBody,
    derivative_settlement_receipt_hash,
    is_hash_ref,
    make_derivative_settlement_receipt,
    verify_derivative_settlement_receipt,
)


def _h(ch: str, *, prefix: str = "sha256:") -> str:
    return prefix + ch * 64


def _hash_refs() -> st.SearchStrategy[str]:
    return st.builds(
        lambda prefix, body: prefix + body,
        st.sampled_from(("0x", "sha256:")),
        st.text(alphabet="0123456789abcdef", min_size=64, max_size=64),
    )


def _body(*, accepted: bool = True, rejection_code: str = "") -> DerivativeSettlementReceiptBody:
    pre = _h("a")
    post = _h("b") if accepted else pre
    return DerivativeSettlementReceiptBody(
        market="il_futures",
        market_epoch=3,
        action="settle",
        pre_state_root=pre,
        post_state_root=post,
        reference_root=_h("c"),
        payoff_formula_hash=_h("d"),
        witness_hash=_h("e"),
        collateral_bound=1000,
        balance_transfer_root=_h("f"),
        accepted=accepted,
        rejection_code=rejection_code,
    )


def test_derivative_settlement_receipt_round_trip() -> None:
    receipt = make_derivative_settlement_receipt(_body())

    ok, reason = verify_derivative_settlement_receipt(receipt)

    assert receipt["schema"] == DERIVATIVE_SETTLEMENT_RECEIPT_SCHEMA
    assert ok
    assert reason == "ok"
    assert receipt["receipt_hash"] == derivative_settlement_receipt_hash(receipt["body"])


def test_derivative_rejection_receipt_requires_unchanged_state() -> None:
    receipt = make_derivative_settlement_receipt(
        _body(accepted=False, rejection_code="oracle_reference_receipt")
    )

    ok, reason = verify_derivative_settlement_receipt(receipt)

    assert ok
    assert reason == "ok"
    assert receipt["body"]["pre_state_root"] == receipt["body"]["post_state_root"]


def test_derivative_rejection_receipt_rejects_state_change() -> None:
    receipt = make_derivative_settlement_receipt(
        _body(accepted=False, rejection_code="oracle_reference_receipt")
    )
    receipt["body"] = {**receipt["body"], "post_state_root": _h("9")}
    receipt["receipt_hash"] = derivative_settlement_receipt_hash(receipt["body"])

    ok, reason = verify_derivative_settlement_receipt(receipt)

    assert not ok
    assert reason == "rejected_state_changed"


def test_derivative_settlement_receipt_rejects_hash_mismatch() -> None:
    receipt = make_derivative_settlement_receipt(_body())
    receipt["body"] = {**receipt["body"], "collateral_bound": 999}

    ok, reason = verify_derivative_settlement_receipt(receipt)

    assert not ok
    assert reason == "receipt_hash"


def test_derivative_settlement_receipt_rejects_bad_hash_ref() -> None:
    receipt = make_derivative_settlement_receipt(_body())
    receipt["body"] = {**receipt["body"], "reference_root": "bad-root"}
    receipt["receipt_hash"] = derivative_settlement_receipt_hash(receipt["body"])

    ok, reason = verify_derivative_settlement_receipt(receipt)

    assert not ok
    assert reason == "reference_root"


def test_derivative_settlement_receipt_rejects_negative_collateral() -> None:
    receipt = make_derivative_settlement_receipt(_body())
    receipt["body"] = {**receipt["body"], "collateral_bound": -1}
    receipt["receipt_hash"] = derivative_settlement_receipt_hash(receipt["body"])

    ok, reason = verify_derivative_settlement_receipt(receipt)

    assert not ok
    assert reason == "collateral_bound"


def test_hash_ref_accepts_supported_root_forms() -> None:
    assert is_hash_ref(_h("1", prefix="0x"))
    assert is_hash_ref(_h("2", prefix="sha256:"))


@settings(max_examples=80)
@given(
    market_epoch=st.integers(min_value=0, max_value=1_000_000),
    pre_state_root=_hash_refs(),
    post_state_root=_hash_refs(),
    reference_root=_hash_refs(),
    payoff_formula_hash=_hash_refs(),
    witness_hash=_hash_refs(),
    collateral_bound=st.integers(
        min_value=0,
        max_value=DERIVATIVE_SETTLEMENT_RECEIPT_MAX_COLLATERAL,
    ),
    balance_transfer_root=_hash_refs(),
)
def test_derivative_settlement_receipt_property_round_trips_valid_accepted_body(
    market_epoch: int,
    pre_state_root: str,
    post_state_root: str,
    reference_root: str,
    payoff_formula_hash: str,
    witness_hash: str,
    collateral_bound: int,
    balance_transfer_root: str,
) -> None:
    receipt = make_derivative_settlement_receipt(
        DerivativeSettlementReceiptBody(
            market="il_futures",
            market_epoch=market_epoch,
            action="settle_il_epoch",
            pre_state_root=pre_state_root,
            post_state_root=post_state_root,
            reference_root=reference_root,
            payoff_formula_hash=payoff_formula_hash,
            witness_hash=witness_hash,
            collateral_bound=collateral_bound,
            balance_transfer_root=balance_transfer_root,
            accepted=True,
        )
    )

    ok, reason = verify_derivative_settlement_receipt(receipt)

    assert ok
    assert reason == "ok"


@settings(max_examples=80)
@given(
    state_root=_hash_refs(),
    reference_root=_hash_refs(),
    payoff_formula_hash=_hash_refs(),
    witness_hash=_hash_refs(),
    collateral_bound=st.integers(min_value=0, max_value=1_000_000),
    balance_transfer_root=_hash_refs(),
    rejection_code=st.sampled_from(("guard", "oracle_reference", "settlement_witness")),
)
def test_derivative_settlement_receipt_property_round_trips_valid_rejection_body(
    state_root: str,
    reference_root: str,
    payoff_formula_hash: str,
    witness_hash: str,
    collateral_bound: int,
    balance_transfer_root: str,
    rejection_code: str,
) -> None:
    receipt = make_derivative_settlement_receipt(
        DerivativeSettlementReceiptBody(
            market="funding_rate",
            market_epoch=0,
            action="settle_rate_epoch",
            pre_state_root=state_root,
            post_state_root=state_root,
            reference_root=reference_root,
            payoff_formula_hash=payoff_formula_hash,
            witness_hash=witness_hash,
            collateral_bound=collateral_bound,
            balance_transfer_root=balance_transfer_root,
            accepted=False,
            rejection_code=rejection_code,
        )
    )

    ok, reason = verify_derivative_settlement_receipt(receipt)

    assert ok
    assert reason == "ok"


@settings(max_examples=50)
@given(receipt_root=_hash_refs(), bad_root=st.text(min_size=0, max_size=80))
def test_derivative_settlement_receipt_property_rejects_non_hash_balance_root(
    receipt_root: str,
    bad_root: str,
) -> None:
    if is_hash_ref(bad_root):
        return
    receipt = make_derivative_settlement_receipt(_body())
    receipt["body"] = {
        **receipt["body"],
        "reference_root": receipt_root,
        "balance_transfer_root": bad_root,
    }
    receipt["receipt_hash"] = derivative_settlement_receipt_hash(receipt["body"])

    ok, reason = verify_derivative_settlement_receipt(receipt)

    assert not ok
    assert reason == "balance_transfer_root"
