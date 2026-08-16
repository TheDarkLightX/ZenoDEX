from __future__ import annotations

import hashlib
import json
from pathlib import Path

import pytest

from tools import check_production_readiness_g1_profile_inputs as profile_inputs
from tools.check_production_readiness_g1_profile_inputs import (
    DEFAULT_OUTPUT,
    REPAIR_SOURCE_SUBJECT,
    build_document,
    check_artifact,
)
from tools.production_readiness_g1_profile_input_contract import (
    DECISION_INPUTS,
    INPUT_STATUS,
    MECHANISM_SECTIONS,
)


def test_profile_inputs_are_exact_research_only_and_unselected() -> None:
    document = build_document()
    report = check_artifact(DEFAULT_OUTPUT)

    assert report["ok"] is True
    assert report["g1_complete"] is False
    assert report["production_ready"] is False
    assert report["decision_input_count"] == 9
    assert report["selected_profile_count"] == 0
    assert document["production_promotion"] is False
    assert document["policy_authority"] == "NONE"
    assert document["g1_exit_gate"]["complete"] is False


def test_profile_inputs_bind_semantics_and_repair_source_bytes() -> None:
    document = build_document()
    semantic_path = profile_inputs.REPO_ROOT / document["semantic_binding"]["artifact"]

    assert document["semantic_binding"]["sha256"] == hashlib.sha256(
        semantic_path.read_bytes()
    ).hexdigest()
    assert document["source_subject"]["repair_commit"] == REPAIR_SOURCE_SUBJECT
    assert {pin["subject"] for pin in document["source_pins"]} == {
        REPAIR_SOURCE_SUBJECT
    }


def test_every_open_decision_has_the_mechanism_review_packet() -> None:
    document = build_document()

    assert {entry["id"] for entry in document["decision_inputs"]} == set(
        DECISION_INPUTS
    )
    for entry in document["decision_inputs"]:
        assert entry["input_status"] == INPUT_STATUS
        assert entry["decision_status"] == "OPEN_UNSELECTED"
        assert entry["selected_profile"] is None
        assert entry["production_authority"] == "NONE"
        assert MECHANISM_SECTIONS <= set(entry)
        assert entry["source_observations"]
        assert entry["observed_research_behavior"]


def test_source_observations_resolve_exact_symbols_and_lines() -> None:
    for entry in build_document()["decision_inputs"]:
        for observation in entry["source_observations"]:
            assert observation["path"].startswith("src/core/m6_safe_mount_")
            assert observation["symbols"]
            assert all(symbol["line"] > 0 for symbol in observation["symbols"])


def test_selecting_policy_in_the_research_artifact_fails_closed(tmp_path: Path) -> None:
    artifact = json.loads(DEFAULT_OUTPUT.read_text(encoding="utf-8"))
    artifact["decision_inputs"][0]["selected_profile"] = {
        "forbidden": "caller-selected-policy"
    }
    mutated = tmp_path / "selected-profile.json"
    mutated.write_text(
        json.dumps(artifact, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    report = check_artifact(mutated)

    assert report["ok"] is False
    assert report["g1_complete"] is False
    assert report["production_ready"] is False
    assert report["selected_profile_count"] == 1
    assert "artifact differs" in " ".join(report["errors"])


def test_missing_mechanism_section_fails_generation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    decision_id = "protocol_buy_burn_policy"
    incomplete = dict(DECISION_INPUTS[decision_id])
    incomplete.pop("attack_query")
    monkeypatch.setitem(profile_inputs.DECISION_INPUTS, decision_id, incomplete)

    with pytest.raises(ValueError, match="omits mechanism sections"):
        build_document()


def test_unknown_source_symbol_fails_generation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    decision_id = "proof_reward_reserve_policy"
    malformed = dict(DECISION_INPUTS[decision_id])
    malformed["source_symbols"] = {
        "src/core/m6_safe_mount_transition_v1.py": ("_missing_reward_handler",)
    }
    monkeypatch.setitem(profile_inputs.DECISION_INPUTS, decision_id, malformed)

    with pytest.raises(ValueError, match="source symbol is absent"):
        build_document()
