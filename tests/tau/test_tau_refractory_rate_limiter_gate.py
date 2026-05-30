"""Dual-profile trace tests for the Tau refractory rate-limiter gate."""
from __future__ import annotations

from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps


ROOT = Path(__file__).resolve().parents[2]
SPEC = ROOT / "experiments" / "tau_frontier" / "refractory_rate_limiter_gate_candidate_v1.tau"
TAU_PROFILES = ("runtime", "latest")


def _run(profile: str, steps: list[dict[str, int]]) -> list[dict[str, int]]:
    tau_bin = find_tau_bin(ROOT, profile=profile)
    if not tau_bin:
        pytest.skip(f"{profile} tau not found")
    return run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=SPEC,
        steps=steps,
        timeout_s=90.0,
    )


@pytest.mark.parametrize("profile", TAU_PROFILES)
def test_continuous_requests_are_rate_limited(profile: str) -> None:
    steps = [{"i1": 1} for _ in range(8)]
    out = _run(profile, steps)
    got = [out[i]["o1"] for i in range(len(steps))]
    assert got == [0, 0, 0, 0, 0, 0, 0, 0]
    assert all(not (got[i] == 1 and got[i + 1] == 1) for i in range(len(got) - 1))


@pytest.mark.parametrize("profile", TAU_PROFILES)
def test_quiet_step_rearms_the_gate(profile: str) -> None:
    steps = [
        {"i1": 0},
        {"i1": 1},
        {"i1": 0},
        {"i1": 1},
    ]
    out = _run(profile, steps)
    assert [out[i]["o1"] for i in range(len(steps))] == [0, 1, 0, 1]


@pytest.mark.parametrize("profile", TAU_PROFILES)
def test_no_spurious_accept_without_request(profile: str) -> None:
    steps = [
        {"i1": 0},
        {"i1": 0},
        {"i1": 1},
        {"i1": 1},
        {"i1": 0},
        {"i1": 1},
    ]
    out = _run(profile, steps)
    got = [out[i]["o1"] for i in range(len(steps))]
    assert got == [0, 0, 1, 0, 0, 1]
    assert all(out[i]["o1"] <= steps[i]["i1"] for i in range(len(steps)))


def test_refractory_rate_limiter_versions_agree() -> None:
    if not find_tau_bin(ROOT, profile="runtime") or not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("both Tau profiles required")
    steps = [
        {"i1": 0},
        {"i1": 1},
        {"i1": 1},
        {"i1": 0},
        {"i1": 1},
        {"i1": 1},
        {"i1": 1},
        {"i1": 0},
    ]
    assert _run("runtime", steps) == _run("latest", steps)
