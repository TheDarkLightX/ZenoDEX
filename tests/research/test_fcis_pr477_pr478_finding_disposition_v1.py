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
    assert payload["evidence"]["remote_ci"] == (
        "INITIAL_FAILURE_MISSING_HYGIENE_PACKET; LOCAL_REPAIR_PASS; EXACT_HEAD_RERUN_PENDING"
    )
    assert payload["evidence"]["test_hygiene_gate"] == ("PASS_3_CRITICAL_PATHS_8_DECLARED_NODES")
    assert payload["successor_open_gaps"]


def test_disposition_source_hashes_bind_exact_repaired_files() -> None:
    payload = json.loads(REGISTRY.read_text(encoding="utf-8"))

    for artifact in payload["source_artifacts"]:
        path = ROOT / artifact["path"]
        assert path.is_file()
        assert hashlib.sha256(path.read_bytes()).hexdigest() == artifact["sha256"]
