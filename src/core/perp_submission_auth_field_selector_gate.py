from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping

PERP_OP_AUTH_FIELD_SELECTOR_ACTION_TAGS_V1: dict[str, int] = {
    "init_market_2p": 0,
    "init_market_3p": 1,
    "set_position_pair": 2,
    "set_position_triplet": 3,
    "publish_clearing_price": 4,
}

PERP_OP_AUTH_FIELD_SELECTOR_CANDIDATE_KEYS_V1: tuple[str, ...] = (
    "quote_asset",
    "account_a_pubkey",
    "account_b_pubkey",
    "account_c_pubkey",
    "new_position_base_a",
    "new_position_base_b",
    "new_position_base_c",
    "price_e8",
    "deadline",
)


@dataclass(frozen=True)
class PerpSubmissionAuthFieldSelectorGateOutcome:
    include_quote_asset: bool
    include_account_a_pubkey: bool
    include_account_b_pubkey: bool
    include_account_c_pubkey: bool
    include_new_position_base_a: bool
    include_new_position_base_b: bool
    include_new_position_base_c: bool
    include_price_e8: bool
    include_deadline: bool
    required_fields_present: bool
    signed_field_count: int


@dataclass(frozen=True)
class PerpSubmissionAuthSignedFieldSelection:
    signed_field_keys: tuple[str, ...]
    signed_field_count: int


def _require_int(value: Any, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    return int(value)


def _require_bool(value: Any, *, name: str) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be a bool")
    return bool(value)


def _include_flags_for_action_tag(action_tag: int) -> dict[str, bool]:
    if action_tag == 0:
        return {
            "quote_asset": True,
            "account_a_pubkey": True,
            "account_b_pubkey": True,
            "account_c_pubkey": False,
            "new_position_base_a": False,
            "new_position_base_b": False,
            "new_position_base_c": False,
            "price_e8": False,
            "deadline": True,
        }
    if action_tag == 1:
        return {
            "quote_asset": True,
            "account_a_pubkey": True,
            "account_b_pubkey": True,
            "account_c_pubkey": True,
            "new_position_base_a": False,
            "new_position_base_b": False,
            "new_position_base_c": False,
            "price_e8": False,
            "deadline": True,
        }
    if action_tag == 2:
        return {
            "quote_asset": False,
            "account_a_pubkey": True,
            "account_b_pubkey": True,
            "account_c_pubkey": False,
            "new_position_base_a": True,
            "new_position_base_b": True,
            "new_position_base_c": False,
            "price_e8": False,
            "deadline": True,
        }
    if action_tag == 3:
        return {
            "quote_asset": False,
            "account_a_pubkey": True,
            "account_b_pubkey": True,
            "account_c_pubkey": True,
            "new_position_base_a": True,
            "new_position_base_b": True,
            "new_position_base_c": True,
            "price_e8": False,
            "deadline": True,
        }
    if action_tag == 4:
        return {
            "quote_asset": False,
            "account_a_pubkey": False,
            "account_b_pubkey": False,
            "account_c_pubkey": False,
            "new_position_base_a": False,
            "new_position_base_b": False,
            "new_position_base_c": False,
            "price_e8": True,
            "deadline": True,
        }
    raise ValueError("action_tag out of range")


def evaluate_perp_submission_auth_field_selector_gate(
    *,
    action_tag: Any,
    has_quote_asset: Any,
    has_account_a_pubkey: Any,
    has_account_b_pubkey: Any,
    has_account_c_pubkey: Any,
    has_new_position_base_a: Any,
    has_new_position_base_b: Any,
    has_new_position_base_c: Any,
    has_price_e8: Any,
    has_deadline: Any,
) -> PerpSubmissionAuthFieldSelectorGateOutcome:
    tag = _require_int(action_tag, name="action_tag")
    includes = _include_flags_for_action_tag(tag)
    presence = {
        "quote_asset": _require_bool(has_quote_asset, name="has_quote_asset"),
        "account_a_pubkey": _require_bool(has_account_a_pubkey, name="has_account_a_pubkey"),
        "account_b_pubkey": _require_bool(has_account_b_pubkey, name="has_account_b_pubkey"),
        "account_c_pubkey": _require_bool(has_account_c_pubkey, name="has_account_c_pubkey"),
        "new_position_base_a": _require_bool(has_new_position_base_a, name="has_new_position_base_a"),
        "new_position_base_b": _require_bool(has_new_position_base_b, name="has_new_position_base_b"),
        "new_position_base_c": _require_bool(has_new_position_base_c, name="has_new_position_base_c"),
        "price_e8": _require_bool(has_price_e8, name="has_price_e8"),
        "deadline": _require_bool(has_deadline, name="has_deadline"),
    }
    required_fields_present = all((not includes[key]) or presence[key] for key in includes)
    signed_field_count = sum(1 for key in PERP_OP_AUTH_FIELD_SELECTOR_CANDIDATE_KEYS_V1 if includes[key])
    return PerpSubmissionAuthFieldSelectorGateOutcome(
        include_quote_asset=includes["quote_asset"],
        include_account_a_pubkey=includes["account_a_pubkey"],
        include_account_b_pubkey=includes["account_b_pubkey"],
        include_account_c_pubkey=includes["account_c_pubkey"],
        include_new_position_base_a=includes["new_position_base_a"],
        include_new_position_base_b=includes["new_position_base_b"],
        include_new_position_base_c=includes["new_position_base_c"],
        include_price_e8=includes["price_e8"],
        include_deadline=includes["deadline"],
        required_fields_present=bool(required_fields_present),
        signed_field_count=int(signed_field_count),
    )


def select_perp_submission_auth_signed_field_keys_v1(
    *,
    action: str,
    op: Mapping[str, Any],
) -> PerpSubmissionAuthSignedFieldSelection:
    if not isinstance(action, str) or not action:
        raise ValueError("signing dict missing action")
    action_tag = PERP_OP_AUTH_FIELD_SELECTOR_ACTION_TAGS_V1.get(action)
    if action_tag is None:
        raise ValueError(f"unsupported signed action: {action}")
    outcome = evaluate_perp_submission_auth_field_selector_gate(
        action_tag=action_tag,
        has_quote_asset="quote_asset" in op,
        has_account_a_pubkey="account_a_pubkey" in op,
        has_account_b_pubkey="account_b_pubkey" in op,
        has_account_c_pubkey="account_c_pubkey" in op,
        has_new_position_base_a="new_position_base_a" in op,
        has_new_position_base_b="new_position_base_b" in op,
        has_new_position_base_c="new_position_base_c" in op,
        has_price_e8="price_e8" in op,
        has_deadline="deadline" in op,
    )
    includes = {
        "quote_asset": outcome.include_quote_asset,
        "account_a_pubkey": outcome.include_account_a_pubkey,
        "account_b_pubkey": outcome.include_account_b_pubkey,
        "account_c_pubkey": outcome.include_account_c_pubkey,
        "new_position_base_a": outcome.include_new_position_base_a,
        "new_position_base_b": outcome.include_new_position_base_b,
        "new_position_base_c": outcome.include_new_position_base_c,
        "price_e8": outcome.include_price_e8,
        "deadline": outcome.include_deadline,
    }
    if not outcome.required_fields_present:
        for key in PERP_OP_AUTH_FIELD_SELECTOR_CANDIDATE_KEYS_V1:
            if includes[key] and key not in op:
                raise ValueError(f"signing dict missing field: {key}")
        raise ValueError("signing dict missing required field")
    signed_field_keys = tuple(key for key in PERP_OP_AUTH_FIELD_SELECTOR_CANDIDATE_KEYS_V1 if includes[key])
    return PerpSubmissionAuthSignedFieldSelection(
        signed_field_keys=signed_field_keys,
        signed_field_count=int(outcome.signed_field_count),
    )
