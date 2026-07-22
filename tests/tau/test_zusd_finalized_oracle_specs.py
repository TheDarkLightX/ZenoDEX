from __future__ import annotations

import json
from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps
from src.integration.tau_witness import (
    ZUSD_LIQUIDATION_GUARD_V3,
    ZUSD_ORACLE_COMMIT_GUARD_V3,
    build_zusd_liquidation_guard_v3_step,
    build_zusd_oracle_commit_guard_v3_step,
)

ROOT = Path(__file__).resolve().parents[2]


def test_finalized_oracle_witness_builders_are_canonical() -> None:
    assert build_zusd_oracle_commit_guard_v3_step(
        oracle_seen=1,
        pending_initialized=1,
        pending_le_active=1,
        auth_ok=1,
        fresh_ok=1,
    ) == {"i1": 1, "i2": 1, "i3": 1, "i4": 1, "i5": 1}

    assert build_zusd_liquidation_guard_v3_step(
        finalized_initialized=1,
        vault_debt=150,
        under_mcr_at_finalized=1,
        sp_debt=200,
        vault_coll=30,
        sp_coll_before=10,
        max_sp_coll=100,
        pending_matches_finalized=1,
        fresh_finalized=1,
    ) == {
        "i1": 1,
        "i2": 150,
        "i3": 1,
        "i4": 200,
        "i5": 30,
        "i6": 10,
        "i7": 100,
        "i8": 1,
        "i9": 1,
    }


@pytest.mark.parametrize(
    ("spec_path", "steps", "expected"),
    [
        (
            ZUSD_ORACLE_COMMIT_GUARD_V3.path,
            [
                {"i1": 1, "i2": 1, "i3": 1, "i4": 1, "i5": 1},
                {"i1": 1, "i2": 1, "i3": 1, "i4": 0, "i5": 1},
                {"i1": 1, "i2": 0, "i3": 1, "i4": 1, "i5": 1},
                {"i1": 1, "i2": 1, "i3": 1, "i4": 1, "i5": 0},
                {"i1": 0, "i2": 1, "i3": 1, "i4": 1, "i5": 1},
                {"i1": 1, "i2": 1, "i3": 0, "i4": 1, "i5": 1},
            ],
            [1, 0, 0, 0, 0, 0],
        ),
        (
            ZUSD_LIQUIDATION_GUARD_V3.path,
            [
                {
                    "i1": 1,
                    "i2": 150,
                    "i3": 1,
                    "i4": 200,
                    "i5": 30,
                    "i6": 10,
                    "i7": 100,
                    "i8": 1,
                    "i9": 1,
                },
                {
                    "i1": 1,
                    "i2": 150,
                    "i3": 1,
                    "i4": 200,
                    "i5": 30,
                    "i6": 10,
                    "i7": 100,
                    "i8": 0,
                    "i9": 1,
                },
                {
                    "i1": 1,
                    "i2": 150,
                    "i3": 1,
                    "i4": 200,
                    "i5": 30,
                    "i6": 10,
                    "i7": 100,
                    "i8": 1,
                    "i9": 0,
                },
                {
                    "i1": 1,
                    "i2": 150,
                    "i3": 1,
                    "i4": 100,
                    "i5": 30,
                    "i6": 10,
                    "i7": 100,
                    "i8": 1,
                    "i9": 1,
                },
                {
                    "i1": 0,
                    "i2": 150,
                    "i3": 1,
                    "i4": 200,
                    "i5": 30,
                    "i6": 10,
                    "i7": 100,
                    "i8": 1,
                    "i9": 1,
                },
                {
                    "i1": 1,
                    "i2": 150,
                    "i3": 0,
                    "i4": 200,
                    "i5": 30,
                    "i6": 10,
                    "i7": 100,
                    "i8": 1,
                    "i9": 1,
                },
                {
                    "i1": 1,
                    "i2": 0,
                    "i3": 1,
                    "i4": 200,
                    "i5": 30,
                    "i6": 10,
                    "i7": 100,
                    "i8": 1,
                    "i9": 1,
                },
                {
                    "i1": 1,
                    "i2": 150,
                    "i3": 1,
                    "i4": 200,
                    "i5": 30,
                    "i6": 80,
                    "i7": 100,
                    "i8": 1,
                    "i9": 1,
                },
            ],
            [1, 0, 0, 0, 0, 0, 0, 0],
        ),
    ],
)
def test_finalized_oracle_tau_specs(
    spec_path: Path,
    steps: list[dict[str, int]],
    expected: list[int],
) -> None:
    tau_bin = find_tau_bin()
    if not tau_bin:
        pytest.skip("tau not found")

    assert spec_path.is_file()
    outputs = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=spec_path,
        steps=steps,
        timeout_s=60.0,
    )
    assert [outputs[index]["o4"] for index in range(len(steps))] == expected


def test_v3_spec_refs_point_inside_repository() -> None:
    assert ZUSD_ORACLE_COMMIT_GUARD_V3.path == (
        ROOT / "src/tau_specs/recommended/zusd_oracle_commit_guard_v3.tau"
    )
    assert ZUSD_LIQUIDATION_GUARD_V3.path == (
        ROOT / "src/tau_specs/recommended/zusd_liquidation_guard_v3.tau"
    )


def test_v3_specs_are_declared_in_semantic_and_profile_registries() -> None:
    contracts = json.loads(
        (ROOT / "src/tau_specs/recommended/semantic_contracts.json").read_text(encoding="utf-8")
    )
    contracts_by_id = {entry["contract_id"]: entry for entry in contracts["specs"]}
    assert contracts_by_id["zusd_oracle_commit_guard_v3"]["spec_path"] == (
        "src/tau_specs/recommended/zusd_oracle_commit_guard_v3.tau"
    )
    assert contracts_by_id["zusd_liquidation_guard_v3"]["spec_path"] == (
        "src/tau_specs/recommended/zusd_liquidation_guard_v3.tau"
    )

    profiles = json.loads(
        (ROOT / "src/tau_specs/recommended/spec_profiles.json").read_text(encoding="utf-8")
    )
    variants = {entry["variant_id"]: entry for entry in profiles["components"]["zusd"]["variants"]}
    assert variants["oracle_commit_guard_v3"]["spec_path"] == (
        "src/tau_specs/recommended/zusd_oracle_commit_guard_v3.tau"
    )
    assert variants["liquidation_guard_v3"]["spec_path"] == (
        "src/tau_specs/recommended/zusd_liquidation_guard_v3.tau"
    )
    assert (
        variants["liquidation_guard_v3"]["latest_tau_stream_arithmetic"]["runtime_admission"]
        is False
    )
