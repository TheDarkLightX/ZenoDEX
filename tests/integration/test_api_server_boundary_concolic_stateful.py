from __future__ import annotations

from pathlib import Path

from tools.api_server_boundary_concolic_stateful import explore_target


ROOT_DIR = Path(__file__).resolve().parents[2]
MANIFEST_PATH = ROOT_DIR / "tools" / "acceptance_tcb_dangerous_surfaces.json"


def test_api_server_boundary_concolic_stateful_reaches_authorization_surface() -> None:
    report = explore_target(
        "settlement_proof_flags",
        max_depth=1,
        max_frontier=64,
        target_manifest=str(MANIFEST_PATH),
        target_id="api_request_authorization_boundary",
    )
    assert report.reached_target_ids == ("api_request_authorization_boundary",)
    assert report.unique_transition_count >= 5
    labels = {case.outcome_label for case in report.cases}
    assert "ok" in labels
    assert any("proof_flags" in label for label in labels)
