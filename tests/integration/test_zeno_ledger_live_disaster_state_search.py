from __future__ import annotations

from tools.zeno_ledger_live_disaster_state_search import run_live_disaster_state_search


def test_live_disaster_state_search_blocks_selected_disasters() -> None:
    report = run_live_disaster_state_search()

    assert report["schema"] == "zenodex/zeno_ledger_live_disaster_state_search/v0"
    assert report["ok"] is True
    assert report["reached_disasters"] == []
    assert report["issue_count"] == 0
    assert report["selected_disaster_state_count"] == 7
    assert report["action_count"] >= 10
    assert all(row["status"] == "unreachable_under_bounds" for row in report["disaster_states"])
    assert report["replay"]["writer_height"] == report["replay"]["readonly_height"]
    assert report["replay"]["writer_tip"] == report["replay"]["readonly_tip"]
