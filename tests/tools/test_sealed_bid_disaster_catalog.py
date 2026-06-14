from __future__ import annotations

import importlib.util
import json
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest

from tools.sealed_bid_disaster_catalog import generate_catalog

ROOT = Path(__file__).resolve().parents[2]
pytestmark = pytest.mark.skipif(importlib.util.find_spec("ESSO") is None, reason="ESSO is not installed")


def _export_ref(model_path: str, tmp_path: Path) -> Any:
    cmd = [sys.executable, "-m", "ESSO", "export-python", model_path, "--output", str(tmp_path)]
    proc = subprocess.run(cmd, cwd=str(ROOT), capture_output=True, text=True, check=True)
    payload = json.loads(proc.stdout.strip())
    ref_path = ROOT / payload["files"]["model"]
    spec = importlib.util.spec_from_file_location(ref_path.stem, ref_path)
    assert spec is not None and spec.loader is not None
    mod = importlib.util.module_from_spec(spec)
    sys.modules[ref_path.stem] = mod
    spec.loader.exec_module(mod)
    return mod


def test_sealed_bid_disaster_catalog_discharge_cases() -> None:
    report = generate_catalog()
    assert report["ok"] is True
    assert [row["disaster_id"] for row in report["cases"]] == [
        "empty_auction_deadlock",
        "no_reveal_deadlock",
        "empty_bond_deadlock",
    ]
    for row in report["cases"]:
        assert row["discharged"] is True
        assert row["only_discharge_remains"] is True
        assert row["final_phase"] == "Complete"


def test_commit_reveal_empty_finalize_bva(tmp_path: Path) -> None:
    mod = _export_ref("src/kernels/dex/sealed_bid_commit_reveal_gate_v1.yaml", tmp_path)
    s = mod.init_state()
    at_commit_deadline = mod.step(s, mod.Command("advance_epoch", {"delta": 1}))
    assert at_commit_deadline.ok and at_commit_deadline.state is not None
    equal_deadline_try = mod.step(at_commit_deadline.state, mod.Command("finalize_empty_auction", {}))
    assert equal_deadline_try.ok is False
    after_reveal_deadline = mod.step(at_commit_deadline.state, mod.Command("advance_epoch", {"delta": 1}))
    assert after_reveal_deadline.ok and after_reveal_deadline.state is not None
    pass_try = mod.step(after_reveal_deadline.state, mod.Command("finalize_empty_auction", {}))
    assert pass_try.ok and pass_try.state is not None
    assert pass_try.state.phase == "Complete"


def test_commit_reveal_no_reveal_finalize_bva(tmp_path: Path) -> None:
    mod = _export_ref("src/kernels/dex/sealed_bid_commit_reveal_gate_v1.yaml", tmp_path)
    s = mod.init_state()
    r1 = mod.step(s, mod.Command("commit_bid", {"commitment_bound": True}))
    assert r1.ok and r1.state is not None
    r2 = mod.step(r1.state, mod.Command("advance_epoch", {"delta": 2}))
    assert r2.ok and r2.state is not None
    r3 = mod.step(r2.state, mod.Command("open_reveal", {}))
    assert r3.ok and r3.state is not None
    at_reveal_deadline = mod.step(r3.state, mod.Command("finalize_no_reveal_auction", {}))
    assert at_reveal_deadline.ok is False
    after_deadline = mod.step(r3.state, mod.Command("advance_epoch", {"delta": 1}))
    assert after_deadline.ok and after_deadline.state is not None
    pass_try = mod.step(after_deadline.state, mod.Command("finalize_no_reveal_auction", {}))
    assert pass_try.ok and pass_try.state is not None
    assert pass_try.state.phase == "Complete"


def test_bond_empty_finalize_bva(tmp_path: Path) -> None:
    mod = _export_ref("src/kernels/dex/sealed_bid_non_reveal_bond_v1.yaml", tmp_path)
    s = mod.init_state()
    at_deadline = mod.step(s, mod.Command("advance_epoch", {"delta": 1}))
    assert at_deadline.ok and at_deadline.state is not None
    equal_deadline_try = mod.step(at_deadline.state, mod.Command("finalize_empty_bonds", {}))
    assert equal_deadline_try.ok is False
    after_deadline = mod.step(at_deadline.state, mod.Command("advance_epoch", {"delta": 1}))
    assert after_deadline.ok and after_deadline.state is not None
    pass_try = mod.step(after_deadline.state, mod.Command("finalize_empty_bonds", {}))
    assert pass_try.ok and pass_try.state is not None
    assert pass_try.state.phase == "Complete"
