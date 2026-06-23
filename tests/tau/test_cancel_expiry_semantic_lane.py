from __future__ import annotations

from pathlib import Path

import yaml


ROOT = Path(__file__).resolve().parents[2]
ORDER_INTENT_KERNEL = ROOT / "src" / "kernels" / "dex" / "order_intent_v1.yaml"


def _load_actions() -> dict[str, dict[str, object]]:
    raw = yaml.safe_load(ORDER_INTENT_KERNEL.read_text(encoding="utf-8"))
    actions = raw.get("actions", [])
    assert isinstance(actions, list)
    return {str(action["id"]): action for action in actions}


def test_cancel_order_never_emits_intent() -> None:
    actions = _load_actions()
    cancel = actions["cancel_order"]
    updates = cancel["updates"]
    effects = cancel["effects"]

    assert updates == [{"var": "order_status", "expr": {"enum": "Cancelled"}}]
    assert effects["event"] == {"enum": "OrderCancelled"}
    assert effects["intent_emitted"] == {"bool": False}


def test_execute_order_requires_live_window_and_emits_intent_only_on_success() -> None:
    actions = _load_actions()
    execute = actions["execute_order"]
    guard_args = execute["guard"]["args"]
    effects = execute["effects"]

    assert {"op": "=", "args": [{"var": "order_status"}, {"enum": "Live"}]} in guard_args
    assert {
        "op": "<=",
        "args": [{"var": "valid_from_epoch"}, {"var": "now_epoch"}],
    } in guard_args
    assert {
        "op": "<=",
        "args": [{"var": "now_epoch"}, {"var": "valid_until_epoch"}],
    } in guard_args

    assert effects["event"] == {"enum": "OrderExecuted"}
    assert effects["intent_emitted"] == {"bool": True}
    assert effects["intent_amount_in"] == {"var": "amount_in"}
    assert effects["intent_min_amount_out"] == {"var": "min_amount_out"}


def test_execute_order_guard_has_expiry_upper_bound() -> None:
    actions = _load_actions()
    execute = actions["execute_order"]
    guard_args = execute["guard"]["args"]

    assert {
        "op": "<=",
        "args": [{"var": "now_epoch"}, {"var": "valid_until_epoch"}],
    } in guard_args
