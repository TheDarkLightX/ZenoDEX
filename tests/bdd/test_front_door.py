"""Run the ZenoDEX front-door behavior contract under pytest.

Each ``.feature`` in ``features/`` has a sibling ``steps/<stem>_steps.py`` that
exposes a ``registry`` (StepRegistry) and ``make_context()``. Every Scenario
becomes one parametrized test, id'd ``<feature>::<scenario>``.

``@pending`` scenarios are honest RED: they are run and marked ``xfail`` -
visible "front-door decision not yet promoted" signal that keeps the suite green
without pretending the behavior is settled. An ``xpass`` (it unexpectedly works)
is a nudge to drop the tag and promote the scenario.
"""
from __future__ import annotations

import importlib
from pathlib import Path

import pytest

from tests.bdd.runner import Scenario, parse_feature

FEATURES_DIR = Path(__file__).parent / "features"
STEPS_PKG = "tests.bdd.steps"


def _steps_module(feature_path: Path):
    return importlib.import_module(f"{STEPS_PKG}.{feature_path.stem}_steps")


def _collect():
    cases = []
    for feature_path in sorted(FEATURES_DIR.glob("*.feature")):
        feature = parse_feature(feature_path.read_text())
        for scenario in feature.scenarios:
            # REVIEW [B -> A-]: pending scenarios are open obligations. Use a
            # strict xfail so an unexpected pass fails CI and forces promotion or
            # an explicit re-scoping decision.
            marks = (
                [pytest.mark.xfail(reason="@pending front-door red-line", strict=True)]
                if "@pending" in scenario.tags
                else []
            )
            cases.append(
                pytest.param(
                    feature_path, scenario, marks=marks, id=f"{feature_path.stem}::{scenario.name}"
                )
            )
    return cases


@pytest.mark.parametrize("feature_path,scenario", _collect())
def test_front_door_scenario(feature_path: Path, scenario: Scenario) -> None:
    # A scenario with no steps would vacuously "pass" (assert nothing). Reject it
    # so an empty/placeholder scenario can never read as covered behavior.
    # (Codex review 2026-06-06, finding #5.)
    assert scenario.steps, f"scenario {scenario.name!r} has no steps"
    feature = parse_feature(feature_path.read_text())
    steps = _steps_module(feature_path)
    ctx = steps.make_context()
    for step_text in [*feature.background, *scenario.steps]:
        steps.registry.run_step(step_text, ctx)
