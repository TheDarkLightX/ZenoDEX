from __future__ import annotations

from pathlib import Path

from tools.state_boundary_concolic_stateful import explore_target


ROOT_DIR = Path(__file__).resolve().parents[2]
MANIFEST_PATH = ROOT_DIR / "tools" / "acceptance_tcb_dangerous_surfaces.json"


def test_state_boundary_concolic_stateful_reaches_nonce_replay_surface() -> None:
    report = explore_target(
        "validate_and_apply_intent_nonce_batch",
        max_depth=1,
        max_frontier=64,
        target_manifest=str(MANIFEST_PATH),
        target_id="nonce_replay_guard",
    )
    assert report.reached_target_ids == ("nonce_replay_guard",)
    labels = {case.outcome_label for case in report.cases}
    assert "ok:last=2" in labels
    assert "reject:nonce sequence invalid" in labels
    assert "reject:duplicate nonce in batch" in labels
