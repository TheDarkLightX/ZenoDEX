"""Tests for the observables/sensor layer (gov_observables.py): staleness fail-closed,
exact-type hostility, and bin parity with the proposers' own binning."""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

_GOV = Path(__file__).resolve().parents[3] / "src" / "tau_specs" / "governance"
sys.path.insert(0, str(_GOV))

import gov_observables as go  # noqa: E402
import gov_proposers as gp  # noqa: E402

EDGES = {"volatility": (100, 500), "utilization": (2000, 6000, 9000)}
ORDER = ("volatility", "utilization")


def obs(vol=50, vol_at=10, util=7000, util_at=10):
    return {
        "volatility": go.Observation(vol, vol_at),
        "utilization": go.Observation(util, util_at),
    }


def test_fresh_signals_bin_deterministically():
    key = go.fresh_state_key(obs(), order=ORDER, edges=EDGES, now_epoch=12, max_stale=8)
    assert key == (0, 2)
    # bin parity with the proposers' own binning (import-bound, but pin it empirically)
    assert key == (gp.bin_index(50, EDGES["volatility"]), gp.bin_index(7000, EDGES["utilization"]))


def test_boundary_freshness_admitted():
    key = go.fresh_state_key(obs(vol_at=2, util_at=2), order=ORDER, edges=EDGES,
                             now_epoch=10, max_stale=8)
    assert key is not None                      # age == max_stale is still fresh


def test_stale_signal_holds():
    key = go.fresh_state_key(obs(vol_at=0), order=ORDER, edges=EDGES,
                             now_epoch=20, max_stale=8)
    assert key is None                          # volatility age 20 > 8


def test_future_dated_signal_holds_wrap_guard():
    key = go.fresh_state_key(obs(vol_at=30), order=ORDER, edges=EDGES,
                             now_epoch=20, max_stale=8)
    assert key is None                          # updated 30 > now 20: never "fresh"
    key2 = go.fresh_state_key(obs(vol_at=65520), order=ORDER, edges=EDGES,
                              now_epoch=8, max_stale=4095)
    assert key2 is None                         # modular wrap would have looked fresh


def test_missing_signal_is_malformed_wiring():
    with pytest.raises(ValueError):
        go.fresh_state_key({"volatility": go.Observation(50, 10)}, order=ORDER,
                           edges=EDGES, now_epoch=12, max_stale=8)
    with pytest.raises(ValueError):
        go.fresh_state_key(obs(), order=ORDER, edges={"volatility": (100, 500)},
                           now_epoch=12, max_stale=8)


def test_hostile_observation_objects_rejected():
    class FakeObs:
        value = 50
        updated_epoch = 10
    with pytest.raises(TypeError):
        go.fresh_state_key({"volatility": FakeObs(), "utilization": go.Observation(1, 1)},
                           order=ORDER, edges=EDGES, now_epoch=12, max_stale=8)

    class EvilInt(int):
        pass
    with pytest.raises(TypeError):
        go.fresh_state_key({"volatility": go.Observation(EvilInt(50), 10),
                            "utilization": go.Observation(1, 1)},
                           order=ORDER, edges=EDGES, now_epoch=12, max_stale=8)


def test_forged_frozen_observation_rejected_at_use():
    o = go.Observation(50, 10)
    object.__setattr__(o, "value", 70000)       # frozen != immutable
    with pytest.raises(TypeError):
        go.fresh_state_key({"volatility": o, "utilization": go.Observation(1, 1)},
                           order=ORDER, edges=EDGES, now_epoch=12, max_stale=8)


def test_hostile_containers_rejected():
    class LyingDict(dict):
        pass
    with pytest.raises(TypeError):
        go.fresh_state_key(LyingDict(obs()), order=ORDER, edges=EDGES,
                           now_epoch=12, max_stale=8)
    with pytest.raises(TypeError):
        go.fresh_state_key(obs(), order=("volatility", "utilization"),
                           edges=LyingDict(EDGES), now_epoch=12, max_stale=8)
    with pytest.raises(TypeError):
        go.fresh_state_key(obs(), order=ORDER, edges=EDGES,
                           now_epoch=True, max_stale=8)


def test_stale_key_feeds_hold_not_action():
    # end-to-end shape: a stale sensor means NO state key, and the convention every
    # proposer in this suite follows is hit=False/hold on a missing key — autonomy
    # never acts on dead sensors.
    key = go.fresh_state_key(obs(vol_at=0), order=ORDER, edges=EDGES,
                             now_epoch=500, max_stale=8)
    assert key is None
    table = {gp.state_key((0, 2)): 520}
    if key is not None:  # pragma: no cover - documents the contract
        gp.q_table_propose(500, key, table)
    # the caller's only admissible move with key=None is to hold (no proposal at all)
