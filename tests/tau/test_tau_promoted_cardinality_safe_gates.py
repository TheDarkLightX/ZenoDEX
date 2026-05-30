"""Dual-profile checks for promoted cardinality-safe Tau frontier gates."""
from __future__ import annotations

from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps
from tools.check_tau_runtime_cardinality import check_spec_cardinality


ROOT = Path(__file__).resolve().parents[2]
REC = ROOT / "src" / "tau_specs" / "recommended"
TAU_PROFILES = ("runtime", "latest")

ORDER_ROUTE = REC / "order_route_decision_table_v1.tau"
INTENT_ONESHOT = REC / "intent_oneshot_admission_gate_v1.tau"
NONCE_WINDOW = REC / "nonce_window_replay_guard_v1.tau"
EPOCH_STEP = REC / "epoch_monotonic_step_gate_v1.tau"
ORACLE_SUSTAINED = REC / "oracle_sustained_freshness_2epoch_gate_v1.tau"

PROMOTED = (ORDER_ROUTE, INTENT_ONESHOT, NONCE_WINDOW, EPOCH_STEP, ORACLE_SUSTAINED)


def _run(profile: str, spec_path: Path, steps: list[dict[str, int]]) -> dict[int, dict[str, int]]:
    tau_bin = find_tau_bin(ROOT, profile=profile)
    if not tau_bin:
        pytest.skip(f"{profile} Tau binary not found")
    return run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=spec_path,
        steps=steps,
        timeout_s=90.0,
    )


def _o1(profile: str, spec_path: Path, values: list[int]) -> list[int]:
    out = _run(profile, spec_path, [{"i1": value} for value in values])
    return [out[i]["o1"] for i in range(len(values))]


@pytest.mark.parametrize("spec_path", PROMOTED, ids=lambda path: path.stem)
def test_promoted_specs_are_cardinality_safe_on_both_profiles(spec_path: Path) -> None:
    results = check_spec_cardinality(spec_path, repo_root=ROOT)
    failures = [result for result in results if not result.ok]
    assert failures == []


@pytest.mark.parametrize("profile", TAU_PROFILES)
def test_order_route_decision_table_matches_reference(profile: str) -> None:
    cases = {
        0: {"o1": 1, "o2": 1, "o3": 0, "o4": 0, "o5": 0},
        1: {"o1": 1, "o2": 0, "o3": 1, "o4": 0, "o5": 0},
        2: {"o1": 1, "o2": 0, "o3": 0, "o4": 1, "o5": 0},
        3: {"o1": 1, "o2": 0, "o3": 0, "o4": 0, "o5": 1},
        4: {"o1": 0, "o2": 0, "o3": 0, "o4": 0, "o5": 0},
        255: {"o1": 0, "o2": 0, "o3": 0, "o4": 0, "o5": 0},
    }
    steps = [{"i1": code} for code in cases]
    out = _run(profile, ORDER_ROUTE, steps)
    for idx, expected in enumerate(cases.values()):
        assert {key: out[idx][key] for key in expected} == expected
        assert sum(out[idx][key] for key in ("o2", "o3", "o4", "o5")) == out[idx]["o1"]


@pytest.mark.parametrize("profile", TAU_PROFILES)
def test_intent_oneshot_admits_only_witnessed_rising_edges(profile: str) -> None:
    assert _o1(profile, INTENT_ONESHOT, [1, 1, 0, 1]) == [0, 0, 0, 1]
    assert _o1(profile, INTENT_ONESHOT, [0, 1, 1, 0, 1]) == [0, 1, 0, 0, 1]


@pytest.mark.parametrize("profile", TAU_PROFILES)
def test_nonce_window_rejects_reuse_inside_two_step_window(profile: str) -> None:
    assert _o1(profile, NONCE_WINDOW, [0, 0, 1, 1, 0, 0, 1]) == [0, 0, 1, 0, 0, 0, 1]
    assert _o1(profile, NONCE_WINDOW, [1, 0, 1, 0, 1]) == [0, 0, 0, 0, 0]


@pytest.mark.parametrize("profile", TAU_PROFILES)
def test_epoch_monotonic_step_rejects_skips(profile: str) -> None:
    assert _o1(profile, EPOCH_STEP, [0, 1, 2, 0, 2, 0]) == [0, 1, 1, 1, 0, 1]
    assert _o1(profile, EPOCH_STEP, [0, 3, 1, 1, 2]) == [0, 0, 0, 0, 1]


@pytest.mark.parametrize("profile", TAU_PROFILES)
def test_oracle_sustained_freshness_requires_two_consecutive_fresh_requested_epochs(profile: str) -> None:
    steps = [
        {"i1": 10, "i2": 10, "i3": 2, "i4": 1},
        {"i1": 11, "i2": 11, "i3": 2, "i4": 1},
        {"i1": 12, "i2": 9, "i3": 2, "i4": 1},
        {"i1": 13, "i2": 13, "i3": 2, "i4": 1},
        {"i1": 14, "i2": 14, "i3": 2, "i4": 1},
        {"i1": 15, "i2": 15, "i3": 2, "i4": 0},
        {"i1": 16, "i2": 16, "i3": 2, "i4": 1},
    ]
    out = _run(profile, ORACLE_SUSTAINED, steps)
    assert [out[idx]["o1"] for idx in range(len(steps))] == [0, 1, 0, 0, 1, 0, 0]


@pytest.mark.parametrize("spec_path", PROMOTED, ids=lambda path: path.stem)
def test_promoted_specs_profiles_agree_on_representative_trace(spec_path: Path) -> None:
    if not find_tau_bin(ROOT, profile="runtime") or not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("both Tau profiles required")
    if spec_path == ORACLE_SUSTAINED:
        steps = [
            {"i1": 10, "i2": 10, "i3": 2, "i4": 1},
            {"i1": 11, "i2": 11, "i3": 2, "i4": 1},
            {"i1": 12, "i2": 9, "i3": 2, "i4": 1},
            {"i1": 13, "i2": 13, "i3": 2, "i4": 1},
        ]
    else:
        values = [0, 1, 2, 3, 4, 255] if spec_path in {ORDER_ROUTE, EPOCH_STEP} else [0, 1, 1, 0, 1, 0]
        steps = [{"i1": value} for value in values]
    assert _run("runtime", spec_path, steps) == _run("latest", spec_path, steps)
