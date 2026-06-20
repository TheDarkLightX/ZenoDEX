"""Tests for the operation-history checker.

Run: PYTHONPATH=. pytest experiments/dst_history_checker_v1/test_history_checker.py
"""

from __future__ import annotations

import dataclasses

from history_checker import (
    _ASSETS,
    check_history,
    demo_batches,
    demo_initial,
    replay_matches,
    run_history,
)


def _history():
    init = demo_initial()
    batches = demo_batches()
    return init, batches, run_history(init, batches)


def _flip_last_hex(s: str) -> str:
    return s[:-1] + ("0" if s[-1] != "0" else "1")


def test_genuine_history_has_no_anomalies():
    _init, _batches, records = _history()
    assert len(records) == 3
    assert check_history(records) == []


def test_history_is_nonvacuous():
    # The trajectory does real work: roots evolve and assets are present.
    _i, _b, records = _history()
    assert len(set(r.post_root for r in records)) >= 2
    assert all(s > 0 for s in records[0].pre_supplies.values())


def test_replay_is_deterministic():
    init, batches, records = _history()
    assert replay_matches(init, batches, records)


def test_checker_detects_broken_chain():
    _i, _b, records = _history()
    bad = list(records)
    bad[0] = dataclasses.replace(bad[0], post_root=_flip_last_hex(bad[0].post_root))
    anomalies = check_history(bad)
    assert any(a.startswith("chain_root@0") for a in anomalies)


def test_checker_detects_conservation_violation():
    # Phantom value: mint 1_000_000 of an asset into a step's post-supply. A genuine
    # swap conserves supply, so the checker must flag the per-step conservation break.
    _i, _b, records = _history()
    bad = list(records)
    asset = _ASSETS[0]
    ps = dict(bad[1].post_supplies)
    ps[asset] += 1_000_000
    bad[1] = dataclasses.replace(bad[1], post_supplies=ps)
    anomalies = check_history(bad)
    assert any(a.startswith("conservation@1") for a in anomalies)


def test_replay_detects_non_replayable_history():
    # A recorded history whose post-roots don't match a genuine replay is rejected.
    init, batches, records = _history()
    bad = list(records)
    bad[2] = dataclasses.replace(bad[2], post_root=_flip_last_hex(bad[2].post_root))
    assert not replay_matches(init, batches, bad)
