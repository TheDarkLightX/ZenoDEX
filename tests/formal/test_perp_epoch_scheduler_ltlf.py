from __future__ import annotations

import importlib.util
from pathlib import Path

import pytest


if importlib.util.find_spec("ESSO") is None:  # pragma: no cover
    pytest.skip("ESSO not installed (expected via external/ESSO or site package)", allow_module_level=True)


def test_ltlf_scheduler_can_reach_epoch_2_settled() -> None:
    import yaml

    from ESSO.ir.schema import CandidateIR
    from ESSO.verify.ltlf_synth import LTLFSynthConfig, LTLFSynthFail, synthesize_ltlf_reachability

    root = Path(__file__).resolve().parents[2]
    model_path = root / "formal" / "ltlf" / "perp_epoch_scheduler_ltlf_v1.yaml"
    ir = CandidateIR.from_json_dict(yaml.safe_load(model_path.read_text(encoding="utf-8"))).canonicalized()

    # Finite-trace reachability: can the operator schedule advance/publish/settle to reach epoch 2 settled?
    # (This complements the TLA+ liveness model which handles fairness/infinite-trace concerns.)
    cfg = LTLFSynthConfig(
        scope="reachable",
        max_states=256,
        max_param_combos=64,
        max_bitvec_width=12,
        termination="explicit_end_action",
        end_action="end",
    )
    report = synthesize_ltlf_reachability(ir=ir, formula="F state.oracle_last_update_epoch.2", cfg=cfg)
    assert not isinstance(report, LTLFSynthFail), getattr(report, "message", "LTLf synthesis failed")
    assert bool(report.get("ok")) is True

