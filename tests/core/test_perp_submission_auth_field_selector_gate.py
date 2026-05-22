from __future__ import annotations

import pytest

from src.core.perp_submission_auth_field_selector_gate import (
    PERP_OP_AUTH_FIELD_SELECTOR_ACTION_TAGS_V1,
    evaluate_perp_submission_auth_field_selector_gate,
    select_perp_submission_auth_signed_field_keys_v1,
)


def test_select_perp_submission_auth_signed_field_keys_v1_set_position_pair_exact_keys() -> None:
    selection = select_perp_submission_auth_signed_field_keys_v1(
        action="set_position_pair",
        op={
            "account_a_pubkey": "aa",
            "account_b_pubkey": "bb",
            "new_position_base_a": 12,
            "new_position_base_b": -12,
            "deadline": 99,
            "extra": "ignored",
        },
    )

    assert selection.signed_field_keys == (
        "account_a_pubkey",
        "account_b_pubkey",
        "new_position_base_a",
        "new_position_base_b",
        "deadline",
    )
    assert selection.signed_field_count == 5


def test_evaluate_perp_submission_auth_field_selector_gate_publish_price_contract() -> None:
    outcome = evaluate_perp_submission_auth_field_selector_gate(
        action_tag=PERP_OP_AUTH_FIELD_SELECTOR_ACTION_TAGS_V1["publish_clearing_price"],
        has_quote_asset=False,
        has_account_a_pubkey=False,
        has_account_b_pubkey=False,
        has_account_c_pubkey=False,
        has_new_position_base_a=False,
        has_new_position_base_b=False,
        has_new_position_base_c=False,
        has_price_e8=True,
        has_deadline=True,
    )

    assert outcome.include_price_e8 is True
    assert outcome.include_deadline is True
    assert outcome.include_account_a_pubkey is False
    assert outcome.required_fields_present is True
    assert outcome.signed_field_count == 2


def test_select_perp_submission_auth_signed_field_keys_v1_rejects_first_missing_required_key() -> None:
    with pytest.raises(ValueError, match="signing dict missing field: account_b_pubkey"):
        select_perp_submission_auth_signed_field_keys_v1(
            action="init_market_2p",
            op={
                "quote_asset": "0x" + "11" * 32,
                "account_a_pubkey": "aa",
                "deadline": 5,
            },
        )


def test_select_perp_submission_auth_signed_field_keys_v1_rejects_unsupported_action() -> None:
    with pytest.raises(ValueError, match="unsupported signed action: unsupported"):
        select_perp_submission_auth_signed_field_keys_v1(action="unsupported", op={"deadline": 1})
