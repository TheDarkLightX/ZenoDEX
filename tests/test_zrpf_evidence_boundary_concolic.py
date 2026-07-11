from __future__ import annotations

from pathlib import Path

import pytest

from tools.zrpf_evidence_boundary_concolic import (
    MAX_DEPTH,
    TARGETS,
    explore_all_targets,
)

ROOT_DIR = Path(__file__).resolve().parents[1]


# These are offline discovery guardrails. They constrain malformed-manifest
# path coverage and have no receipt-seal or correctness-proof authority.
EXPECTED_ONE_HOP_MUTATIONS = {
    "v1_spot_adapter_evidence": {
        "unknown_nested_field",
        "claim_overpromotion",
        "source_path_escape",
        "source_hash_drift",
        "image_word_mismatch",
        "negative_control_drift",
    },
    "v3_structural_tree_evidence": {
        "unknown_nested_field",
        "claim_overpromotion",
        "source_path_escape",
        "source_hash_drift",
        "image_word_mismatch",
        "negative_control_drift",
        "topology_partition_gap",
        "topology_count_mismatch",
        "cross_field_parent_mismatch",
    },
}


def _install_retained_source_hash_oracles(monkeypatch: pytest.MonkeyPatch) -> None:
    for target in TARGETS:
        document, errors = target.checker.load_manifest()
        assert errors == []
        assert isinstance(document, dict)
        expected_hashes: dict[str, str] = {}
        for value in document.values():
            if not isinstance(value, dict) or not isinstance(value.get("files"), list):
                continue
            for row in value["files"]:
                if isinstance(row, dict) and isinstance(row.get("path"), str):
                    expected_hashes[row["path"]] = row["sha256"]

        live_sha256_file = target.checker.support.sha256_file

        def retained_sha256_file(
            path: Path,
            *,
            expected_hashes: dict[str, str] = expected_hashes,
            live_sha256_file=live_sha256_file,
        ) -> str:
            try:
                relative = Path(path).resolve().relative_to(ROOT_DIR).as_posix()
            except ValueError:
                return live_sha256_file(path)
            if relative in expected_hashes:
                return expected_hashes[relative]
            return live_sha256_file(path)

        monkeypatch.setattr(
            target.checker.support,
            "sha256_file",
            retained_sha256_file,
        )


def test_zrpf_evidence_boundary_atlas_rejects_bounded_depth_two_frontier(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # The live manifests are intentionally stale. Retained hashes are a test-only
    # branch-coverage oracle and do not make either evidence record current.
    _install_retained_source_hash_oracles(monkeypatch)
    reports = explore_all_targets()
    by_name = {report.target: report for report in reports}

    assert set(by_name) == set(EXPECTED_ONE_HOP_MUTATIONS)
    for target in TARGETS:
        report = by_name[target.name]
        assert report.valid_seed_accepted is True
        assert report.all_mutated_states_rejected is True
        assert report.mutated_states_cleanly_rejected == report.mutated_states_explored
        assert report.max_depth_reached == MAX_DEPTH
        assert report.minimum_unique_paths_met is True
        assert report.unique_path_count >= target.minimum_unique_paths
        assert len(report.trace_files) == 2

        one_hop = {
            case.mutation
            for case in report.cases
            if case.depth == 1 and case.outcome_label.startswith("reject:")
        }
        assert one_hop == EXPECTED_ONE_HOP_MUTATIONS[target.name]
        assert any(case.depth == 2 for case in report.cases)


def test_zrpf_evidence_boundary_atlas_has_no_receipt_authority() -> None:
    from tools import zrpf_evidence_boundary_concolic as atlas

    payload = atlas._reports_json(explore_all_targets())

    assert payload["authority"] == "offline_discovery_only"
    assert payload["python_verifies_risc0_seal"] is False
    assert payload["correctness_proof"] is False
