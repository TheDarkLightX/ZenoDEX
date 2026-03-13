from __future__ import annotations

import json
from pathlib import Path

from tools.check_tau_shadow_assurance import (
    DEFAULT_CONTRACT_PATH,
    DEFAULT_DELTA_QUEUE_PATH,
    DEFAULT_MATRIX_PATH,
    check_tau_shadow_assurance,
)


def _load_json(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def test_tau_shadow_assurance_repo_artifacts() -> None:
    result = check_tau_shadow_assurance()
    assert result["ok"] is True
    assert result["property_count"] == 25
    assert result["release_blocking_property_count"] == 3
    assert result["shadow_scaffolded_property_count"] == 11
    assert result["assurance_scaffolded_property_count"] == 25
    assert result["pending_or_blocking_delta_count"] == 0


def test_tau_shadow_assurance_blocks_pending_release_delta(tmp_path: Path) -> None:
    queue_path = tmp_path / "semantic_delta_review_queue.json"
    queue_path.write_text(
        json.dumps(
            {
                "schema": "zenodex/tau/semantic-delta-review-queue/v1",
                "entries": [
                    {
                        "delta_id": "delta_nonce_change",
                        "property_ids": ["autotrader_nonce_strict_sequentiality"],
                        "status": "pending",
                        "summary": "nonce acceptance widened"
                    }
                ],
            },
            indent=2,
        ),
        encoding="utf-8",
    )

    result = check_tau_shadow_assurance(
        matrix_path=DEFAULT_MATRIX_PATH,
        delta_queue_path=queue_path,
        contract_path=DEFAULT_CONTRACT_PATH,
    )
    assert result["ok"] is False
    assert any("delta_nonce_change" in err for err in result["errors"])


def test_tau_shadow_assurance_blocks_missing_shadow_invariant(tmp_path: Path) -> None:
    matrix = _load_json(DEFAULT_MATRIX_PATH)
    broken_module = tmp_path / "BrokenNonceShadow.tla"
    broken_module.write_text(
        """---- MODULE BrokenNonceShadow ----
EXTENDS Naturals

TypeOK == TRUE

====
""",
        encoding="utf-8",
    )
    matrix["properties"][0]["shadow_model"]["module_path"] = str(broken_module)
    matrix_path = tmp_path / "dex_safety_property_matrix.json"
    matrix_path.write_text(json.dumps(matrix, indent=2), encoding="utf-8")

    result = check_tau_shadow_assurance(
        matrix_path=matrix_path,
        delta_queue_path=DEFAULT_DELTA_QUEUE_PATH,
        contract_path=DEFAULT_CONTRACT_PATH,
    )
    assert result["ok"] is False
    assert any("AcceptedOnlySequential" in err for err in result["errors"])


def test_tau_shadow_assurance_blocks_bad_tau_contract_ref(tmp_path: Path) -> None:
    matrix = _load_json(DEFAULT_MATRIX_PATH)
    bad_contract = tmp_path / "bad.contract.json"
    bad_contract.write_text(
        json.dumps(
            {
                "schema": "zenodex/tau/spec-contract/v1",
                "spec_id": "wrong_spec",
                "spec_path": "src/tau_specs/recommended/wrong_spec.tau",
            },
            indent=2,
        ),
        encoding="utf-8",
    )
    replay_property = next(
        entry for entry in matrix["properties"] if entry["property_id"] == "deterministic_event_replay"
    )
    contract_ref = next(ref for ref in replay_property["assurance_refs"] if ref["kind"] == "tau_formal_contract")
    contract_ref["path"] = str(bad_contract)
    matrix_path = tmp_path / "dex_safety_property_matrix.json"
    matrix_path.write_text(json.dumps(matrix, indent=2), encoding="utf-8")

    result = check_tau_shadow_assurance(
        matrix_path=matrix_path,
        delta_queue_path=DEFAULT_DELTA_QUEUE_PATH,
        contract_path=DEFAULT_CONTRACT_PATH,
    )
    assert result["ok"] is False
    assert any("tau formal contract spec_id mismatch" in err for err in result["errors"])
