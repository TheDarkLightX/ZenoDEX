from __future__ import annotations

from itertools import product
from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin, run_tau_spec_steps


ROOT = Path(__file__).resolve().parents[2]


def _monolithic_bundle(bits: tuple[int, ...]) -> int:
    return int(all(bits))


def _split_bundle(bits: tuple[int, ...]) -> int:
    core_module_ok = int(all(bits[:3]))
    feature_extension_ok = int(all(bits[3:7]))
    proof_binding_ok = int(all(bits[7:]))
    return int(core_module_ok and feature_extension_ok and proof_binding_ok)


def test_settlement_module_bundle_split_preserves_boolean_semantics() -> None:
    for bits in product((0, 1), repeat=9):
        assert _split_bundle(bits) == _monolithic_bundle(bits)


def test_settlement_module_bundle_split_tau_replay_matches_monolith_oracle() -> None:
    tau_bin = find_tau_bin()
    if not tau_bin:
        pytest.skip("tau not found")

    all_bits = list(product((0, 1), repeat=9))

    core_outputs = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=ROOT / "src" / "tau_specs" / "recommended" / "settlement_core_module_bundle_v1.tau",
        steps=[
            {"i1": bits[0], "i2": bits[1], "i3": bits[2]}
            for bits in all_bits
        ],
        timeout_s=60.0,
    )
    feature_outputs = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=ROOT / "src" / "tau_specs" / "recommended" / "settlement_feature_extension_bundle_v1.tau",
        steps=[
            {"i1": bits[3], "i2": bits[4], "i3": bits[5], "i4": bits[6]}
            for bits in all_bits
        ],
        timeout_s=60.0,
    )
    proof_outputs = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=ROOT / "src" / "tau_specs" / "recommended" / "settlement_proof_binding_bundle_v1.tau",
        steps=[
            {"i1": bits[7], "i2": bits[8]}
            for bits in all_bits
        ],
        timeout_s=60.0,
    )
    top_outputs = run_tau_spec_steps(
        tau_bin=tau_bin,
        spec_path=ROOT / "src" / "tau_specs" / "recommended" / "settlement_module_flag_bundle_v1.tau",
        steps=[
            {
                "i1": core_outputs[idx]["o1"],
                "i2": feature_outputs[idx]["o1"],
                "i3": proof_outputs[idx]["o1"],
            }
            for idx in range(len(all_bits))
        ],
        timeout_s=60.0,
    )

    for idx, bits in enumerate(all_bits):
        assert top_outputs[idx]["o1"] == _monolithic_bundle(bits)
