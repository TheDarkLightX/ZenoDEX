from __future__ import annotations

import importlib.util
import json
from pathlib import Path
from types import ModuleType

import pytest

ROOT = Path(__file__).resolve().parents[1]
TOOL_PATH = ROOT / "tools" / "check_fee_aware_routing_nonconcavity.py"
EVIDENCE_PATH = (
    ROOT
    / "experiments"
    / "math_research_memory"
    / "fee_aware_routing_nonconcavity_evidence_20260717.json"
)


def _load_tool() -> ModuleType:
    spec = importlib.util.spec_from_file_location("fee_aware_routing_nonconcavity", TOOL_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"could not load {TOOL_PATH}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_retained_fee_aware_routing_evidence_replays_exactly() -> None:
    tool = _load_tool()
    retained = json.loads(EVIDENCE_PATH.read_text(encoding="utf-8"))
    replayed = {"ok": True, **tool.build_report(10_000)}
    assert replayed == retained


def test_unbounded_family_regression_rejects_negative_grade_bound() -> None:
    tool = _load_tool()
    with pytest.raises(ValueError, match="max_grade must be nonnegative"):
        tool.build_report(-1)
