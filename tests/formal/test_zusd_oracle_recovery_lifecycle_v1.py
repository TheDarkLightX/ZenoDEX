from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

import pytest


def _maybe_add_external_toolchain() -> None:
    root = Path(__file__).resolve().parents[2]
    toolchain_dir = root / "external" / "ESSO"
    if toolchain_dir.is_dir() and str(toolchain_dir) not in sys.path:
        sys.path.insert(0, str(toolchain_dir))


_maybe_add_external_toolchain()

if importlib.util.find_spec("ESSO") is None:  # pragma: no cover
    pytest.skip("verification toolchain not installed", allow_module_level=True)


def test_zusd_oracle_recovery_lifecycle_v1_model_validates() -> None:
    import yaml

    from ESSO.ir.schema import CandidateIR

    root = Path(__file__).resolve().parents[2]
    model_path = root / "src" / "kernels" / "dex" / "zusd_oracle_recovery_lifecycle_v1.yaml"
    ir = CandidateIR.from_json_dict(
        yaml.safe_load(model_path.read_text(encoding="utf-8"))
    ).canonicalized()
    assert ir.meta["model_id"] == "zusd_oracle_recovery_lifecycle_v1"
    assert len(ir.state_vars) == 0
    assert len(ir.actions) == 1
    assert len(ir.observables.effects) == 5


def test_zusd_oracle_recovery_lifecycle_v1_tau_spec_shape() -> None:
    root = Path(__file__).resolve().parents[2]
    spec_path = root / "src" / "tau_specs" / "recommended" / "zusd_oracle_recovery_lifecycle_v1.tau"
    content = spec_path.read_text(encoding="utf-8")
    assert "set charvar off" in content
    assert "healthy_now" in content
    assert "reenabled_requires_healthy" in content
    assert "outcome_total" in content
    assert "rejection_total" in content
    assert "zusd_oracle_recovery_lifecycle_ok" in content
