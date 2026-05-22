from __future__ import annotations

from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps


ROOT = Path(__file__).resolve().parents[2]


@pytest.mark.parametrize(
    "spec_rel,steps,gate_output,expected_gate",
    [
        (
            "src/tau_specs/recommended/zusd_transfer_guard_v1.tau",
            [
                {"i1": 1, "i2": 1, "i3": 1, "i4": 1, "i5": 1, "i6": 0},
                {"i1": 1, "i2": 0, "i3": 1, "i4": 1, "i5": 1, "i6": 0},
                {"i1": 1, "i2": 1, "i3": 1, "i4": 1, "i5": 1, "i6": 1},
            ],
            "o4",
            [1, 0, 0],
        ),
        (
            "src/tau_specs/recommended/zusd_oracle_commit_guard_v1.tau",
            [
                {"i1": 1, "i2": 1, "i3": 100, "i4": 95, "i5": 1, "i6": 1},
                {"i1": 1, "i2": 1, "i3": 100, "i4": 101, "i5": 1, "i6": 1},
                {"i1": 1, "i2": 1, "i3": 100, "i4": 95, "i5": 1, "i6": 0},
            ],
            "o4",
            [1, 0, 0],
        ),
        (
            "src/tau_specs/recommended/zusd_recovery_mode_gate_v1.tau",
            [
                {"i1": 1, "i2": 1, "i3": 1, "i4": 1, "i5": 1, "i6": 1},
                {"i1": 1, "i2": 1, "i3": 1, "i4": 1, "i5": 0, "i6": 1},
                {"i1": 0, "i2": 0, "i3": 0, "i4": 0, "i5": 0, "i6": 0},
            ],
            "o4",
            [1, 0, 1],
        ),
        (
            "src/tau_specs/recommended/zusd_liquidation_guard_v1.tau",
            [
                {"i1": 1, "i2": 150, "i3": 1, "i4": 200, "i5": 30, "i6": 10, "i7": 100},
                {"i1": 1, "i2": 150, "i3": 1, "i4": 100, "i5": 30, "i6": 10, "i7": 100},
                {"i1": 1, "i2": 150, "i3": 1, "i4": 200, "i5": 30, "i6": 80, "i7": 100},
            ],
            "o4",
            [1, 0, 0],
        ),
        (
            "src/tau_specs/recommended/zusd_supply_conservation_v1.tau",
            [
                {"i1": 80, "i2": 20, "i3": 100, "i4": 60, "i5": 40, "i6": 100},
                {"i1": 80, "i2": 20, "i3": 90, "i4": 60, "i5": 40, "i6": 100},
                {"i1": 80, "i2": 20, "i3": 100, "i4": 60, "i5": 30, "i6": 100},
            ],
            "o4",
            [1, 0, 0],
        ),
        (
            "src/tau_specs/recommended/zusd_oracle_commit_guard_v2.tau",
            [
                {"i1": 1, "i2": 1, "i3": 1, "i4": 1, "i5": 1},
                {"i1": 1, "i2": 0, "i3": 1, "i4": 1, "i5": 1},
                {"i1": 1, "i2": 1, "i3": 1, "i4": 1, "i5": 0},
            ],
            "o4",
            [1, 0, 0],
        ),
        (
            "src/tau_specs/recommended/zusd_cross_module_oracle_sync_gate_v1.tau",
            [
                {"i1": 1, "i2": 1, "i3": 1},
                {"i1": 1, "i2": 0, "i3": 1},
                {"i1": 0, "i2": 1, "i3": 1},
            ],
            "o2",
            [1, 0, 0],
        ),
        (
            "src/tau_specs/recommended/zusd_liquidation_guard_v2.tau",
            [
                {"i1": 1, "i2": 150, "i3": 1, "i4": 200, "i5": 30, "i6": 10, "i7": 100},
                {"i1": 1, "i2": 150, "i3": 1, "i4": 100, "i5": 30, "i6": 10, "i7": 100},
                {"i1": 1, "i2": 150, "i3": 1, "i4": 200, "i5": 30, "i6": 90, "i7": 100},
            ],
            "o4",
            [1, 0, 0],
        ),
        (
            "src/tau_specs/recommended/zusd_supply_conservation_v2.tau",
            [
                {"i1": 80, "i2": 20, "i3": 100, "i4": 60, "i5": 40, "i6": 100},
                {"i1": 80, "i2": 20, "i3": 90, "i4": 60, "i5": 40, "i6": 100},
                {"i1": 80, "i2": 20, "i3": 100, "i4": 60, "i5": 30, "i6": 100},
            ],
            "o4",
            [1, 0, 0],
        ),
        (
            "src/tau_specs/recommended/zusd_mint_guard_v1.tau",
            [
                {"i1": 100, "i2": 0, "i3": 0, "i4": 100, "i5": 100, "i6": 1, "i7": 1, "i8": 1, "i9": 1, "i10": 1},
                {"i1": 100, "i2": 0, "i3": 0, "i4": 90, "i5": 100, "i6": 1, "i7": 1, "i8": 1, "i9": 1, "i10": 1},
                {"i1": 100, "i2": 0, "i3": 0, "i4": 100, "i5": 100, "i6": 0, "i7": 1, "i8": 1, "i9": 1, "i10": 1},
            ],
            "o4",
            [1, 0, 0],
        ),
        (
            "src/tau_specs/recommended/zusd_repay_guard_v1.tau",
            [
                {"i1": 40, "i2": 100, "i3": 80, "i4": 60, "i5": 40},
                {"i1": 40, "i2": 100, "i3": 80, "i4": 70, "i5": 40},
                {"i1": 0, "i2": 100, "i3": 80, "i4": 100, "i5": 80},
            ],
            "o4",
            [1, 0, 0],
        ),
        (
            "src/tau_specs/recommended/zusd_withdraw_collateral_guard_v1.tau",
            [
                {"i1": 10, "i2": 200, "i3": 190, "i4": 100, "i5": 1, "i6": 1},
                {"i1": 10, "i2": 200, "i3": 191, "i4": 100, "i5": 1, "i6": 1},
                {"i1": 10, "i2": 200, "i3": 190, "i4": 100, "i5": 0, "i6": 1},
            ],
            "o4",
            [1, 0, 0],
        ),
        (
            "src/tau_specs/recommended/zusd_deposit_sp_guard_v1.tau",
            [
                {"i1": 20, "i2": 80, "i3": 20, "i4": 60, "i5": 40, "i6": 1},
                {"i1": 20, "i2": 80, "i3": 20, "i4": 61, "i5": 40, "i6": 1},
                {"i1": 20, "i2": 80, "i3": 20, "i4": 60, "i5": 40, "i6": 0},
            ],
            "o4",
            [1, 0, 0],
        ),
        (
            "src/tau_specs/recommended/zusd_withdraw_sp_guard_v1.tau",
            [
                {"i1": 20, "i2": 60, "i3": 40, "i4": 80, "i5": 20, "i6": 1, "i7": 1},
                {"i1": 20, "i2": 60, "i3": 40, "i4": 79, "i5": 20, "i6": 1, "i7": 1},
                {"i1": 20, "i2": 60, "i3": 40, "i4": 80, "i5": 20, "i6": 1, "i7": 0},
            ],
            "o4",
            [1, 0, 0],
        ),
        (
            "src/tau_specs/recommended/zusd_redeem_guard_v1.tau",
            [
                {"i1": 50, "i2": 300, "i3": 450, "i4": 400, "i5": 250, "i6": 400, "i7": 350, "i8": 50, "i9": 1, "i10": 1, "i11": 1, "i12": 1},
                {"i1": 50, "i2": 300, "i3": 450, "i4": 400, "i5": 250, "i6": 400, "i7": 350, "i8": 50, "i9": 1, "i10": 0, "i11": 1, "i12": 1},
                {"i1": 50, "i2": 300, "i3": 450, "i4": 400, "i5": 250, "i6": 400, "i7": 351, "i8": 50, "i9": 1, "i10": 1, "i11": 1, "i12": 1},
            ],
            "o4",
            [1, 0, 0],
        ),
    ],
)
def test_zusd_tau_specs_trace(
    spec_rel: str,
    steps: list[dict[str, int]],
    gate_output: str,
    expected_gate: list[int],
) -> None:
    tau_bin = find_tau_bin()
    if not tau_bin:
        pytest.skip("tau not found")

    spec_path = ROOT / spec_rel
    assert spec_path.exists(), f"missing spec: {spec_path}"

    outputs = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=spec_path,
        steps=steps,
        timeout_s=60.0,
    )

    for idx, exp in enumerate(expected_gate):
        got = outputs.get(idx, {}).get(gate_output)
        assert got == exp, f"{spec_rel} step {idx}: expected {gate_output}={exp}, got {got}"
