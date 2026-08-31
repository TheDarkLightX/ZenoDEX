from __future__ import annotations

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
REGISTRY = ROOT / "docs/research/FCIS_PR477_PR478_FINDING_DISPOSITION_V1.json"


def _required_findings() -> set[str]:
    return {
        *(f"FCIS-477-{index:03d}" for index in range(1, 19)),
        *(f"FCIS-478-{index:03d}" for index in range(1, 17)),
    }


def test_disposition_is_complete_disjoint_and_research_only() -> None:
    payload = json.loads(REGISTRY.read_text(encoding="utf-8"))
    groups = payload["dispositions"]
    classified = [finding for findings in groups.values() for finding in findings]

    assert set(classified) == _required_findings()
    assert len(classified) == len(set(classified)) == 34
    assert payload["status"] == "RESEARCH_ONLY_EXACT_SUCCESSOR_DISPOSITION"
    assert "remains OPEN" in payload["classification_scope"]
    assert set(payload["authority"].values()) == {"NONE"}
    assert payload["evidence"]["remote_ci"] == "LIVE_EXTERNAL_QUERY_REQUIRED"
    observed_failures = payload["evidence"]["observed_remote_ci_failures"]
    assert [row["run_id"] for row in observed_failures] == [33350595043, 33350792610]
    assert [row["head"] for row in observed_failures] == [
        "d0d2a7ca97829d6ba06d2b6e9a562a7d85594410",
        "da50cdb539ba294dcdab2ee1fdcec728a4e38487",
    ]
    assert payload["evidence"]["test_hygiene_gate"] == ("PASS_6_CRITICAL_PATHS_15_DECLARED_NODES")
    assert payload["evidence"]["focused_shared_tests_passed"] == 1337
    assert payload["evidence"]["focused_shared_tests_deselected"] == 1
    assert payload["evidence"]["affected_test_files_passed"] == 218
    assert payload["evidence"]["runtime_disaster_discovery_tests_passed"] == 192
    assert payload["evidence"]["rejection_precedence_regressions_passed"] == 7
    assert (
        payload["evidence"]["inherited_base_failure"]["successor_base"]
        == (payload["subjects"]["successor_base"])
    )
    assert len(payload["evidence"]["test_hygiene_packets"]) == 2
    assert payload["successor_open_gaps"]


def test_disposition_source_hashes_bind_exact_repaired_files() -> None:
    payload = json.loads(REGISTRY.read_text(encoding="utf-8"))

    for artifact in payload["source_artifacts"]:
        path = ROOT / artifact["path"]
        assert path.is_file()
        assert hashlib.sha256(path.read_bytes()).hexdigest() == artifact["sha256"]
