from __future__ import annotations

from tools.zeno_ledger_market_swarm import _agent, _quote_exact_in, _summarize_rows


def test_market_swarm_agent_pubkeys_are_replayable() -> None:
    first = _agent("seed-a", 3)
    second = _agent("seed-a", 3)

    assert first == second
    assert first["pubkey"].startswith("0x")
    assert len(first["pubkey"]) == 98


def test_market_swarm_quote_exact_in_is_bounded_by_reserves() -> None:
    pool = {
        "asset0": "A",
        "asset1": "B",
        "reserve0": 10_000,
        "reserve1": 20_000,
        "fee_bps": 30,
    }

    quoted = _quote_exact_in(pool, "A", 1_000)

    assert 0 < quoted < pool["reserve1"]


def test_market_swarm_summary_tracks_invalid_probes() -> None:
    rows = [
        {"action_family": "momentum", "accepted": True, "rejected": False, "expected_valid": True},
        {"action_family": "readonly_rejection_probe", "accepted": False, "rejected": True, "expected_valid": False},
    ]

    summary = _summarize_rows(rows)

    assert summary["submission_count"] == 2
    assert summary["accepted_count"] == 1
    assert summary["rejected_count"] == 1
    assert summary["invalid_probe_count"] == 1
    assert summary["action_counts"]["readonly_rejection_probe"] == 1
