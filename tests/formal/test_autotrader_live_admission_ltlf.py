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


def _require_esso() -> None:
    if importlib.util.find_spec("ESSO") is None:  # pragma: no cover
        pytest.skip("verification toolchain not installed")


def _cfg():
    _require_esso()
    from ESSO.verify.ltlf_synth import LTLFSynthConfig

    return LTLFSynthConfig(
        scope="reachable",
        max_states=512,
        max_param_combos=64,
        max_bitvec_width=12,
        termination="explicit_end_action",
        end_action="end",
    )


def _ir():
    _require_esso()
    import yaml

    from ESSO.ir.schema import CandidateIR

    root = Path(__file__).resolve().parents[2]
    model_path = root / "formal" / "ltlf" / "autotrader_live_admission_ltlf_v1.yaml"
    return CandidateIR.from_json_dict(
        yaml.safe_load(model_path.read_text(encoding="utf-8"))
    ).canonicalized()


def test_autotrader_live_admission_submit_is_reachable() -> None:
    _require_esso()
    from ESSO.verify.ltlf_synth import LTLFSynthFail, synthesize_ltlf_reachability

    report = synthesize_ltlf_reachability(
        ir=_ir(),
        formula="F effect.event.BundleSubmitted",
        cfg=_cfg(),
    )
    assert not isinstance(report, LTLFSynthFail), getattr(
        report, "message", "LTLf synthesis failed"
    )
    assert bool(report.get("ok")) is True


def test_autotrader_live_admission_finalize_is_reachable() -> None:
    _require_esso()
    from ESSO.verify.ltlf_synth import LTLFSynthFail, synthesize_ltlf_reachability

    report = synthesize_ltlf_reachability(
        ir=_ir(),
        formula="F effect.event.EmitFinalized",
        cfg=_cfg(),
    )
    assert not isinstance(report, LTLFSynthFail), getattr(
        report, "message", "LTLf synthesis failed"
    )
    assert bool(report.get("ok")) is True


def test_autotrader_live_admission_goal_family_realizable() -> None:
    _require_esso()
    import yaml

    from ESSO.verify.ltlf_synth import LTLFSynthFail, synthesize_ltlf_multi_property

    root = Path(__file__).resolve().parents[2]
    goals_path = root / "formal" / "ltlf" / "autotrader_live_admission_goal_family_v1.json"
    goals_obj = yaml.safe_load(goals_path.read_text(encoding="utf-8"))
    assert isinstance(goals_obj, dict)
    goals = goals_obj.get("goals")
    assert isinstance(goals, list)
    required_goal_ids = goals_obj.get("required_goal_ids")
    assert isinstance(required_goal_ids, list)

    multi = synthesize_ltlf_multi_property(
        ir=_ir(),
        goals=goals,
        required_goal_ids=[str(x) for x in required_goal_ids],
        cfg=_cfg(),
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
    assert any(
        {
            "G_valid_observation_eventually_progresses",
            "G_accepted_nonce_eventually_resolves",
            "G_emit_ready_eventually_resolves",
        }.issubset(goal_ids)
        for goal_ids in realized_sets
    )
