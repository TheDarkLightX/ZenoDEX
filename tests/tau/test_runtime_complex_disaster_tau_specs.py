from __future__ import annotations

from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps


ROOT = Path(__file__).resolve().parents[2]
SPEC_ROOT = ROOT / "src" / "tau_specs" / "recommended"
TAU_PROFILES = ("runtime", "latest")


def _tau_bin(profile: str) -> str | None:
    return find_tau_bin(ROOT, profile=profile)


@pytest.mark.parametrize("profile", TAU_PROFILES)
def test_settlement_disaster_envelope_v1_traces(profile: str) -> None:
    tau_bin = _tau_bin(profile)
    if not tau_bin:
        pytest.skip(f"{profile} tau not found")

    spec_path = SPEC_ROOT / "settlement_disaster_envelope_v1.tau"
    base = {f"i{idx}": 1 for idx in range(1, 26)}
    steps = [
        dict(base),
        {**base, "i2": 0},
        {**base, "i10": 0},
        {**base, "i15": 0},
        {**base, "i22": 0},
        {**base, "i1": 0, "i18": 0, "i19": 0},
    ]

    outputs = run_tau_spec_steps(tau_bin=tau_bin, spec_path=spec_path, steps=steps, timeout_s=90.0)

    assert outputs[0]["o7"] == 1
    assert outputs[1]["o1"] == 0
    assert outputs[1]["o7"] == 0
    assert outputs[2]["o2"] == 0
    assert outputs[2]["o7"] == 0
    assert outputs[3]["o3"] == 0
    assert outputs[3]["o7"] == 0
    assert outputs[4]["o4"] == 0
    assert outputs[4]["o7"] == 0
    assert outputs[5]["o6"] == 1
    assert outputs[5]["o7"] == 1


@pytest.mark.parametrize("profile", TAU_PROFILES)
def test_proof_mining_payout_replay_guard_v1_blocks_duplicate_payout(profile: str) -> None:
    tau_bin = _tau_bin(profile)
    if not tau_bin:
        pytest.skip(f"{profile} tau not found")

    spec_path = SPEC_ROOT / "proof_mining_payout_replay_guard_v1.tau"
    good = {f"i{idx}": 1 for idx in range(1, 12)}
    good.update({"i12": 0, "i13": 0, "i14": 0, "i15": 0})
    duplicate = {
        **good,
        "i4": 0,
        "i5": 0,
        "i12": 1,
        "i13": 1,
        "i14": 1,
        "i15": 1,
    }
    steps = [
        good,
        duplicate,
        {**good, "i8": 0},
        {**good, "i9": 0},
        {**good, "i1": 0, "i2": 0, "i3": 0},
    ]

    outputs = run_tau_spec_steps(tau_bin=tau_bin, spec_path=spec_path, steps=steps, timeout_s=90.0)

    assert outputs[0]["o5"] == 1
    assert outputs[1]["o2"] == 0
    assert outputs[1]["o6"] == 0
    assert outputs[1]["o7"] == 0
    assert outputs[1]["o5"] == 0
    assert outputs[2]["o3"] == 0
    assert outputs[2]["o5"] == 0
    assert outputs[3]["o3"] == 0
    assert outputs[3]["o5"] == 0
    assert outputs[4]["o5"] == 1


@pytest.mark.parametrize("profile", TAU_PROFILES)
def test_oracle_committee_commit_admission_v1_traces(profile: str) -> None:
    tau_bin = _tau_bin(profile)
    if not tau_bin:
        pytest.skip(f"{profile} tau not found")

    spec_path = SPEC_ROOT / "oracle_committee_commit_admission_v1.tau"
    good = {
        "i1": 1,
        "i2": 7,
        "i3": 5,
        "i4": 9,
        "i5": 1,
        "i6": 2,
        "i7": 0,
        "i8": 0,
        "i9": 20,
        "i10": 50,
        "i11": 1,
        "i12": 1,
        "i13": 1,
        "i14": 1,
        "i15": 1,
        "i16": 1,
        "i17": 1,
    }
    steps = [
        good,
        {**good, "i2": 4},
        {**good, "i7": 1},
        {**good, "i9": 51},
        {**good, "i14": 0},
        {**good, "i1": 0, "i16": 0, "i17": 0},
    ]

    outputs = run_tau_spec_steps(tau_bin=tau_bin, spec_path=spec_path, steps=steps, timeout_s=90.0)

    assert outputs[0]["o6"] == 1
    assert outputs[1]["o1"] == 0
    assert outputs[1]["o6"] == 0
    assert outputs[2]["o2"] == 0
    assert outputs[2]["o6"] == 0
    assert outputs[3]["o3"] == 0
    assert outputs[3]["o6"] == 0
    assert outputs[4]["o4"] == 0
    assert outputs[4]["o6"] == 0
    assert outputs[5]["o5"] == 1
    assert outputs[5]["o6"] == 1


@pytest.mark.parametrize("profile", TAU_PROFILES)
def test_governance_multisig_timelock_guard_v1_traces(profile: str) -> None:
    tau_bin = _tau_bin(profile)
    if not tau_bin:
        pytest.skip(f"{profile} tau not found")

    spec_path = SPEC_ROOT / "governance_multisig_timelock_guard_v1.tau"
    normal = {
        "i1": 1,
        "i2": 5,
        "i3": 4,
        "i4": 7,
        "i5": 100,
        "i6": 50,
        "i7": 200,
        "i8": 1,
        "i9": 0,
        "i10": 1,
        "i11": 1,
        "i12": 1,
        "i13": 1,
        "i14": 1,
        "i15": 0,
        "i16": 1,
        "i17": 1,
    }
    emergency = {**normal, "i5": 0, "i8": 0, "i9": 1, "i15": 1}
    steps = [
        normal,
        emergency,
        {**normal, "i2": 3},
        {**normal, "i5": 40},
        {**normal, "i8": 1, "i9": 1},
        {**normal, "i14": 0},
        {**normal, "i1": 0, "i16": 0, "i17": 0},
    ]

    outputs = run_tau_spec_steps(tau_bin=tau_bin, spec_path=spec_path, steps=steps, timeout_s=90.0)

    assert outputs[0]["o6"] == 1
    assert outputs[1]["o6"] == 1
    assert outputs[2]["o1"] == 0
    assert outputs[2]["o6"] == 0
    assert outputs[3]["o2"] == 0
    assert outputs[3]["o6"] == 0
    assert outputs[4]["o3"] == 0
    assert outputs[4]["o6"] == 0
    assert outputs[5]["o4"] == 0
    assert outputs[5]["o6"] == 0
    assert outputs[6]["o5"] == 1
    assert outputs[6]["o6"] == 1
