from __future__ import annotations

from tools.api_server_boundary_concolic import explore_all_targets as explore_api_targets
from tools.receipt_boundary_concolic import explore_all_targets as explore_receipt_targets
from tools.state_boundary_concolic import explore_all_targets as explore_state_targets


def test_receipt_boundary_concolic_is_deterministic_under_bounded_frontier() -> None:
    left = explore_receipt_targets(max_depth=1, max_frontier=64)
    right = explore_receipt_targets(max_depth=1, max_frontier=64)
    assert left == right


def test_api_server_boundary_concolic_is_deterministic_under_bounded_frontier() -> None:
    left = explore_api_targets(max_depth=1, max_frontier=64)
    right = explore_api_targets(max_depth=1, max_frontier=64)
    assert left == right


def test_state_boundary_concolic_is_deterministic_under_bounded_frontier() -> None:
    left = explore_state_targets(max_depth=1, max_frontier=64)
    right = explore_state_targets(max_depth=1, max_frontier=64)
    assert left == right
