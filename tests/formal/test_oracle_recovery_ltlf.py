"""LTLf synthesis tests for oracle recovery liveness model.

Verifies:
- G(stale -> F(fresh OR blocked)): oracle eventually recovers or blocks
- G(stale -> !risky_op): stale oracle blocks risky operations
- F(OracleUpdated): recovery is reachable
"""

from __future__ import annotations

import importlib.util
import json
import subprocess
import sys
from pathlib import Path

import pytest


def _maybe_add_external_toolchain() -> None:
    root = Path(__file__).resolve().parents[2]
    toolchain_dir = root / "external" / "ESSO"
    if toolchain_dir.is_dir() and str(toolchain_dir) not in sys.path:
        sys.path.insert(0, str(toolchain_dir))


_maybe_add_external_toolchain()

ESSO_AVAILABLE = importlib.util.find_spec("ESSO") is not None


def test_oracle_recovery_public_replay_accepts() -> None:
    root = Path(__file__).resolve().parents[2]
    proc = subprocess.run(
        [
            sys.executable,
            "tools/zeno_oracle_ltlf_recovery_replay.py",
            "--format",
            "json",
        ],
        cwd=root,
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    receipt = json.loads(proc.stdout)
    assert receipt["schema"] == "zenodex.oracle.ltlf_recovery_replay.v1"
    assert receipt["status"] == "accepted"
    assert receipt["failed_goal_count"] == 0
    goal_ids = {goal["id"] for goal in receipt["goals"]}
    assert "G_stale_eventually_recovers" in goal_ids
    assert "G_stale_blocks_risky" in goal_ids
    assert "G_recovery_reachable" in goal_ids


def test_oracle_recovery_reachability() -> None:
    """Reachability: the operator can recover from a stale oracle."""
    if not ESSO_AVAILABLE:  # pragma: no cover
        pytest.skip("ESSO verification toolchain not installed")
    import yaml

    from ESSO.ir.schema import CandidateIR
    from ESSO.verify.ltlf_synth import (
        LTLFSynthConfig,
        LTLFSynthFail,
        synthesize_ltlf_reachability,
    )

    root = Path(__file__).resolve().parents[2]
    model_path = root / "formal" / "ltlf" / "oracle_recovery_ltlf_v1.yaml"
    ir = CandidateIR.from_json_dict(
        yaml.safe_load(model_path.read_text(encoding="utf-8"))
    ).canonicalized()

    cfg = LTLFSynthConfig(
        scope="reachable",
        max_states=256,
        max_param_combos=64,
        max_bitvec_width=12,
        termination="explicit_end_action",
        end_action="end",
    )
    # Can the operator reach oracle recovery (fresh after being stale)?
    report = synthesize_ltlf_reachability(
        ir=ir, formula="F effect.event.OracleUpdated", cfg=cfg
    )
    assert not isinstance(report, LTLFSynthFail), getattr(
        report, "message", "LTLf synthesis failed"
    )
    assert bool(report.get("ok")) is True


def test_oracle_recovery_block_reachability() -> None:
    """Reachability: the operator can reach permanent block state."""
    if not ESSO_AVAILABLE:  # pragma: no cover
        pytest.skip("ESSO verification toolchain not installed")
    import yaml

    from ESSO.ir.schema import CandidateIR
    from ESSO.verify.ltlf_synth import (
        LTLFSynthConfig,
        LTLFSynthFail,
        synthesize_ltlf_reachability,
    )

    root = Path(__file__).resolve().parents[2]
    model_path = root / "formal" / "ltlf" / "oracle_recovery_ltlf_v1.yaml"
    ir = CandidateIR.from_json_dict(
        yaml.safe_load(model_path.read_text(encoding="utf-8"))
    ).canonicalized()

    cfg = LTLFSynthConfig(
        scope="reachable",
        max_states=256,
        max_param_combos=64,
        max_bitvec_width=12,
        termination="explicit_end_action",
        end_action="end",
    )
    report = synthesize_ltlf_reachability(
        ir=ir, formula="F state.permanently_blocked", cfg=cfg
    )
    assert not isinstance(report, LTLFSynthFail), getattr(
        report, "message", "LTLf synthesis failed"
    )
    assert bool(report.get("ok")) is True


def test_oracle_recovery_goal_family_realizable() -> None:
    """Multi-property synthesis: required recovery goals are jointly realizable."""
    if not ESSO_AVAILABLE:  # pragma: no cover
        pytest.skip("ESSO verification toolchain not installed")
    import yaml

    from ESSO.ir.schema import CandidateIR
    from ESSO.verify.ltlf_synth import (
        LTLFSynthConfig,
        LTLFSynthFail,
        synthesize_ltlf_multi_property,
    )

    root = Path(__file__).resolve().parents[2]
    model_path = root / "formal" / "ltlf" / "oracle_recovery_ltlf_v1.yaml"
    ir = CandidateIR.from_json_dict(
        yaml.safe_load(model_path.read_text(encoding="utf-8"))
    ).canonicalized()

    cfg = LTLFSynthConfig(
        scope="reachable",
        max_states=256,
        max_param_combos=64,
        max_bitvec_width=12,
        termination="explicit_end_action",
        end_action="end",
    )

    goals_path = root / "formal" / "ltlf" / "oracle_recovery_goal_family_v1.json"
    goals_obj = yaml.safe_load(goals_path.read_text(encoding="utf-8"))
    assert isinstance(goals_obj, dict)
    goals = goals_obj.get("goals")
    assert isinstance(goals, list)
    required_goal_ids = goals_obj.get("required_goal_ids")
    assert isinstance(required_goal_ids, list)

    multi = synthesize_ltlf_multi_property(
        ir=ir,
        goals=goals,
        required_goal_ids=[str(x) for x in required_goal_ids],
        cfg=cfg,
    )
    assert not isinstance(multi, LTLFSynthFail), getattr(
        multi, "message", "LTLf multi-property synthesis failed"
    )
    assert bool(multi.get("required_realizable")) is True
    max_sets = multi.get("maximal_realizable_goal_sets") or []
    realized_sets = [
        set(str(x) for x in (row.get("goal_ids") or []))
        for row in max_sets
        if isinstance(row, dict)
    ]
    # Recovery and safety goals must co-realize.
    assert any(
        {"G_stale_eventually_recovers", "G_recovery_reachable"}.issubset(goal_ids)
        for goal_ids in realized_sets
    )
