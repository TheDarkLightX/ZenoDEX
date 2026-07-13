from __future__ import annotations

import copy
import hashlib
import json
from pathlib import Path

import pytest

from tools import check_zrpf_current_source_adapter_v2 as checker
from tools import plan_zrpf_source_opened_spot_v6_identity_rebuild as planner


def _load(path: Path) -> dict:
    return json.loads(path.read_text("utf-8"))


def _write(path: Path, document: dict) -> None:
    path.write_bytes(checker._canonical_bytes(document))


def _pending_documents() -> tuple[dict, dict]:
    """Return an explicit bootstrap fixture independent of committed candidates."""

    anchor = {
        "schema": "zenodex/zrpf_current_source_anchor/v2",
        "status": "awaiting_deterministic_source_build_observation",
        "observation_binding": {
            "plan_schema": checker.PENDING_BOOTSTRAP_PLAN_SCHEMA,
            "plan_sha256": None,
            "source_commit": None,
            "source_snapshot_root_sha256": None,
            "stage_id": "source_spot",
        },
        "source_closure": {
            "kind": "tracked_state_proof_workspace_superset_v1",
            "workspace_roots": ["zk/state_proof_risc0"],
            "inventory_root_sha256": None,
            "tracked_file_count": None,
            "tracked_bytes": None,
            "complete_build_input_closure_verified": False,
        },
        "spot_program": {
            "image_id": None,
            "image_id_words": None,
            "program_sha256": None,
        },
        "release_authority": False,
        "production_authority": False,
        "non_claims": sorted(checker.ANCHOR_NON_CLAIMS),
    }
    policy = {
        "schema": "zenodex/zrpf_v2_leaf_adapter_source_policy/v2",
        "status": "awaiting_deterministic_source_and_adapter_observations",
        "adapter_profile": "zrpf_v2_leaf_adapter_compatibility_v2",
        "count_unit": "source_transition_receipt",
        "source_reference": {
            "path": "config/proof_profiles/zrpf_current_source_anchor_v2.json",
            "schema": anchor["schema"],
            "sha256": hashlib.sha256(checker._canonical_bytes(anchor)).hexdigest(),
        },
        "sources": [
            {
                "source_kind": "spot",
                "proof_type": "risc0.zenodex_recursive_spot_leaf.v1",
                "proof_profile": "recursive_spot_leaf_v1",
                "lane_kind": "spot",
                "image_id": None,
                "image_id_words": None,
                "program_sha256": None,
                "source_closure_root": None,
            }
        ],
        "adapter_program": {
            "image_id": None,
            "image_id_words": None,
            "program_sha256": None,
        },
        "receipt_authority": False,
        "release_authority": False,
        "production_authority": False,
        "unsupported_compatibility_fields": [
            "data_availability_certificate_root",
            "carry_queue_pre_root",
            "carry_queue_post_root",
        ],
        "non_claims": sorted(checker.POLICY_NON_CLAIMS),
    }
    return anchor, policy


def test_committed_v2_contract_is_pending_and_fail_closed() -> None:
    report = checker.check_contract()

    assert report == {
        "ok": True,
        "status": "pending_fail_closed",
        "facts": {
            "adapter_profile": "zrpf_v2_leaf_adapter_compatibility_v2",
            "historical_v1_artifacts_preserved": True,
            "source_identity_pending": True,
            "receipt_authority": False,
            "release_authority": False,
            "production_authority": False,
        },
    }


def test_current_planner_observed_candidates_use_only_current_plan_schema() -> None:
    image_raw = bytes(range(32))
    source_program = {
        "image_id": image_raw.hex(),
        "image_id_words": [
            int.from_bytes(image_raw[index : index + 4], "little") for index in range(0, 32, 4)
        ],
        "program_binary_sha256": "a" * 64,
    }
    adapter_program = {
        "image_id": (b"\x80" + bytes(range(1, 32))).hex(),
        "image_id_words": [
            int.from_bytes(
                (b"\x80" + bytes(range(1, 32)))[index : index + 4],
                "little",
            )
            for index in range(0, 32, 4)
        ],
        "program_binary_sha256": "b" * 64,
    }
    plan = {
        "source_commit": "c" * 40,
        "source_guest_source_coverage": {
            "inventory_root_sha256": "d" * 64,
            "tracked_file_count": 1,
            "tracked_bytes": 1,
        },
    }
    source_stage = {
        "program": source_program,
        "source_snapshot_root_sha256": "e" * 64,
    }
    adapter_stage = {"program": adapter_program}
    anchor = planner.build_current_source_anchor_candidate(plan, source_stage)
    policy = planner.build_v2_adapter_source_policy_candidate(
        plan,
        source_stage,
        adapter_stage,
        anchor,
    )

    assert checker._check_anchor(anchor) is False
    checked_source = checker._program(
        anchor["spot_program"],
        allow_pending=False,
        label="source",
    )
    checker._check_policy(
        policy,
        anchor,
        checker._canonical_bytes(anchor),
        checked_source,
        False,
    )

    legacy = copy.deepcopy(anchor)
    legacy["observation_binding"]["plan_schema"] = "zenodex/zrpf_spot_v6_identity_rebuild_plan/v1"
    with pytest.raises(checker.ContractError, match="anchor plan schema mismatch"):
        checker._check_anchor(legacy)


def test_pending_anchor_rejects_current_observed_plan_schema() -> None:
    anchor, _policy = _pending_documents()
    anchor["observation_binding"]["plan_schema"] = planner.PLAN_SCHEMA

    with pytest.raises(checker.ContractError, match="anchor plan schema mismatch"):
        checker._check_anchor(anchor)


def test_pending_anchor_rejects_invented_or_partial_identity(tmp_path: Path) -> None:
    anchor, policy = _pending_documents()
    anchor["spot_program"]["image_id"] = "1" * 64
    anchor_path = tmp_path / "anchor.json"
    _write(anchor_path, anchor)
    policy["source_reference"]["sha256"] = hashlib.sha256(
        anchor_path.read_bytes()
    ).hexdigest()
    policy_path = tmp_path / "policy.json"
    _write(policy_path, policy)

    with pytest.raises(checker.ContractError, match="partially populated"):
        checker.check_contract(anchor_path, policy_path)


@pytest.mark.parametrize(
    ("document_name", "field"),
    (("anchor", "release_authority"), ("policy", "receipt_authority")),
)
def test_authority_promotion_rejects(
    tmp_path: Path,
    document_name: str,
    field: str,
) -> None:
    anchor, policy = _pending_documents()
    if document_name == "anchor":
        anchor[field] = True
    else:
        policy[field] = True
    anchor_path = tmp_path / "anchor.json"
    _write(anchor_path, anchor)
    policy["source_reference"]["sha256"] = hashlib.sha256(
        anchor_path.read_bytes()
    ).hexdigest()
    policy_path = tmp_path / "policy.json"
    _write(policy_path, policy)

    with pytest.raises(checker.ContractError, match="authority must remain false"):
        checker.check_contract(anchor_path, policy_path)


def test_source_reference_rebinding_rejects(tmp_path: Path) -> None:
    _anchor, policy = _pending_documents()
    policy["source_reference"]["sha256"] = "0" * 64
    policy_path = tmp_path / "policy.json"
    _write(policy_path, policy)

    with pytest.raises(checker.ContractError, match="source reference identity"):
        checker.check_contract(checker.DEFAULT_ANCHOR, policy_path)


def test_loader_rejects_duplicate_keys(tmp_path: Path) -> None:
    duplicate = tmp_path / "duplicate.json"
    duplicate.write_text('{"schema":"a","schema":"b"}\n', encoding="utf-8")

    with pytest.raises(checker.ContractError, match="duplicate JSON key"):
        checker._load_canonical(duplicate, "fixture")


def test_historical_v1_sources_and_governance_files_are_byte_preserved() -> None:
    for relative, expected in checker.PROTECTED_V1_SHA256.items():
        assert hashlib.sha256((checker.REPO_ROOT / relative).read_bytes()).hexdigest() == expected
