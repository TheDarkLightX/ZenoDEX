from __future__ import annotations

from pathlib import Path

from tools.route_certificate_sequence_grammar_fuzz import explore_target, minimize_case


ROOT_DIR = Path(__file__).resolve().parents[2]
MANIFEST_PATH = ROOT_DIR / "tools" / "acceptance_tcb_dangerous_surfaces.json"


def test_route_certificate_sequence_reaches_canonicalization_surface() -> None:
    report = explore_target(
        max_depth=1,
        max_frontier=64,
        target_manifest=str(MANIFEST_PATH),
        target_id="route_canonicalization_boundary",
    )
    assert report.reached_target_ids == ("route_canonicalization_boundary",)
    labels = {case.outcome_label for case in report.cases}
    assert "ok:winner_index=1:candidate_count=2" in labels
    assert any("candidate_set_hash mismatch" in label for label in labels)


def test_route_certificate_sequence_minimize_case_preserves_candidate_set_hash_mismatch() -> None:
    witness = minimize_case("add_better_candidate")
    assert witness.target == "route_certificate_sequence"
    assert witness.derivation == "add_better_candidate"
    assert witness.outcome_label == "reject:step=1:candidate_set_hash mismatch"
    assert witness.path_id == "1a010bc9a4dd2c4b"
    assert witness.path_length == 639
    assert witness.original_size == 1033
    assert witness.original_size == witness.minimized_size
