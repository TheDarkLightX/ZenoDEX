from __future__ import annotations

import json
from pathlib import Path

import pytest

from src.integration.tau_native_mirrors import native_mirror_supported_spec_ids, run_native_tau_mirror


ROOT = Path(__file__).resolve().parents[2]
REGISTRY = ROOT / "tests" / "tau" / "spec_registry.json"


def test_native_tau_mirrors_match_registry_vectors() -> None:
    data = json.loads(REGISTRY.read_text(encoding="utf-8"))
    entries = [entry for entry in data["specs"] if entry.get("mode") == "native_mirror"]

    supported = native_mirror_supported_spec_ids()
    assert entries
    assert {entry["id"] for entry in entries} == supported

    for entry in entries:
        spec_id = entry["id"]
        assert entry.get("native_mirror") == spec_id
        outputs = run_native_tau_mirror(spec_id=spec_id, steps=[dict(step) for step in entry["inputs"]])
        for idx, expected in enumerate(entry["expected"]):
            assert outputs[idx] == expected, spec_id


def test_native_tau_mirror_rejects_unknown_spec() -> None:
    with pytest.raises(ValueError, match="unsupported native Tau mirror"):
        run_native_tau_mirror(spec_id="unsupported", steps=[{"i1": 1}])


@pytest.mark.parametrize("spec_id", ["multi_predicate", "cpmm_basic", "balance_safety", "dex_complete"])
def test_legacy_bv16_native_mirrors_reject_out_of_range_inputs(spec_id: str) -> None:
    with pytest.raises(ValueError, match="bv\\[16\\]"):
        run_native_tau_mirror(spec_id=spec_id, steps=[{"i1": 1 << 16}])
