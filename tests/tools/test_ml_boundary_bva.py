from __future__ import annotations

from types import SimpleNamespace

from tools.ml_boundary_bva import (
    EvalRecord,
    _boundary_values_for_param,
    _param_l1_distance,
    _select_cases_with_coverage,
    int_boundary_points,
)


def test_int_boundary_points_includes_edges_and_specials() -> None:
    pts = int_boundary_points(low=-3, high=3)
    assert -3 in pts
    assert -2 in pts
    assert 2 in pts
    assert 3 in pts
    assert 0 in pts
    assert 1 in pts
    assert -1 in pts


def test_int_boundary_points_deduplicates_tight_ranges() -> None:
    pts = int_boundary_points(low=0, high=1)
    assert pts == [0, 1]


def test_select_cases_with_coverage_prefers_new_tags() -> None:
    r0 = EvalRecord(
        reward=1.0,
        pre_state={"x": 0},
        action="a0",
        params={"p": 0},
        expected={"ok": True, "state": {"x": 0}, "effects": {}},
        boundary_score=1.0,
        boundary_tags=("p=min",),
        outcome_key="ok",
        next_state={"x": 0},
    )
    r1 = EvalRecord(
        reward=2.0,
        pre_state={"x": 0},
        action="a0",
        params={"p": 1},
        expected={"ok": True, "state": {"x": 1}, "effects": {}},
        boundary_score=1.0,
        boundary_tags=("p=max",),
        outcome_key="ok",
        next_state={"x": 1},
    )
    r2 = EvalRecord(
        reward=3.0,
        pre_state={"x": 0},
        action="a0",
        params={"p": 2},
        expected={"ok": True, "state": {"x": 2}, "effects": {}},
        boundary_score=1.0,
        boundary_tags=("p=max",),
        outcome_key="ok",
        next_state={"x": 2},
    )
    out = _select_cases_with_coverage([r0, r1, r2], want=2)
    assert len(out) == 2
    tags = {t for r in out for t in r.boundary_tags}
    assert "p=min" in tags
    assert "p=max" in tags


def test_boundary_values_for_int_include_outside_points() -> None:
    t = SimpleNamespace(kind="int", min=2, max=4)
    vals = _boundary_values_for_param(t=t, include_outside=True)
    assert 1 in vals
    assert 5 in vals
    assert 2 in vals
    assert 4 in vals


def test_select_cases_with_coverage_includes_outcome_diversity() -> None:
    rows = [
        EvalRecord(
            reward=4.0,
            pre_state={"x": 0},
            action="a0",
            params={"p": 2},
            expected={"ok": True, "state": {"x": 2}, "effects": {}},
            boundary_score=1.0,
            boundary_tags=("p=max",),
            outcome_key="ok",
            next_state={"x": 2},
        ),
        EvalRecord(
            reward=3.9,
            pre_state={"x": 0},
            action="a0",
            params={"p": 2},
            expected={"ok": False, "code": "ParamType"},
            boundary_score=0.9,
            boundary_tags=("p=max",),
            outcome_key="err:ParamType",
            next_state=None,
        ),
    ]
    out = _select_cases_with_coverage(rows, want=2)
    outcomes = {r.outcome_key for r in out}
    assert "ok" in outcomes
    assert "err:ParamType" in outcomes


def test_param_l1_distance_handles_mixed_types() -> None:
    d = _param_l1_distance({"x": 3, "b": True, "e": "A"}, {"x": 1, "b": False, "e": "A"})
    assert d == 3.0
