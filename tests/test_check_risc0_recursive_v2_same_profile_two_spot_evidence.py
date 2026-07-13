from __future__ import annotations

import base64
import copy
import hashlib
import inspect
import json
from pathlib import Path
from typing import Any

import pytest

from tools import check_risc0_recursive_v2_same_profile_two_spot_evidence as checker


def _h(byte: int) -> str:
    return (bytes([byte]) * 32).hex()


def _digest_text(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def _result(message: str) -> dict[str, Any]:
    return {"exit_code": 1, "stderr": message, "stderr_sha256": _digest_text(message)}


def _leaf(
    *,
    role: str,
    lane_id: str,
    statement_hash: str,
    scope_hash: str,
    seed: int,
) -> dict[str, Any]:
    source_id = checker.derive_leaf_source_id(checker.SPOT_LANE_KIND, statement_hash)
    assigned_id = checker.derive_assigned_leaf_id(scope_hash, lane_id, source_id)
    return {
        "role": role,
        "proof_type": checker.SPOT_PROOF_TYPE,
        "profile": checker.SPOT_PROFILE,
        "lane_kind": checker.SPOT_LANE_KIND,
        "lane_id": lane_id,
        "image_id": checker.SPOT_IMAGE_ID,
        "statement_hash": statement_hash,
        "source_id": source_id,
        "assigned_leaf_id": assigned_id,
        "journal_sha256": _h(seed),
        "protocol_child_journal_hash": _h(seed + 1),
        "verification_claim_hash": _h(seed + 2),
        "artifact_file_sha256": _h(seed + 3),
        "artifact_size_bytes": 1000 + seed,
        "receipt_sha256": _h(seed + 4),
    }


def _fixture() -> tuple[dict[str, Any], dict[str, Any], dict[str, Any], str, str]:
    reference_file_sha256 = _h(1)
    baseline_file_sha256 = _h(2)
    source_path = (
        "zk/recursive_stark_v2_risc0/harness/src/bin/"
        "verify_recursive_v2_two_leaf_pair.rs"
    )
    reference = {
        "sdk_version": "3.0.5",
        "program": {
            "image_id": _h(3),
            "program_sha256": _h(4),
            "program_bytes": 448324,
        },
        "source_compile": {
            "files": [{"path": source_path, "sha256": _h(5), "size_bytes": 19001}]
        },
        "proof_pair": {
            "two_leaf_static_verifier": {"sha256": _h(6), "size_bytes": 2719999}
        },
    }
    verifier = {
        "repository_source_pinned": True,
        "independent_proof_implementation": False,
        "source_path": source_path,
        "source_sha256": _h(5),
        "binary_sha256": _h(6),
        "binary_size_bytes": 2719999,
        "status": checker.VERIFIER_STATUS,
    }
    scope_hash = _h(20)
    leaves = [
        _leaf(
            role="spot_baseline",
            lane_id="spot-root-child-0001",
            statement_hash=_h(21),
            scope_hash=scope_hash,
            seed=30,
        ),
        _leaf(
            role="spot_distinct_statement_variant",
            lane_id="spot-root-child-0002",
            statement_hash=_h(22),
            scope_hash=scope_hash,
            seed=40,
        ),
    ]
    baseline = {
        "aggregate_v2": {
            "sdk_version": "3.0.5",
            "image_id": _h(3),
            "program_sha256": _h(4),
            "program_size_bytes": 448324,
        },
        "leaf_claims": [
            {
                key: leaves[0][key]
                for key in (
                    "proof_type",
                    "profile",
                    "lane_id",
                    "image_id",
                    "artifact_file_sha256",
                    "artifact_size_bytes",
                    "receipt_sha256",
                )
            }
            | {"role": "spot"}
        ],
        "verification": {"specialized_host_verifier": verifier},
    }
    verifier_id = checker.derive_child_verifier_id(
        checker.SPOT_IMAGE_ID, checker.SPOT_PROFILE
    )
    verifier_root = checker.derive_immediate_verifier_set_root([verifier_id])
    source_root = checker.derive_descendant_sources_root(
        [row["source_id"] for row in leaves]
    )
    assigned_root = checker.derive_assigned_leaf_ids_root(
        [row["assigned_leaf_id"] for row in leaves]
    )

    def node(*, inner: bool) -> dict[str, Any]:
        return {
            "artifact_file_sha256": _h(50 if inner else 51),
            "artifact_size_bytes": 795000 if inner else 795100,
            "receipt_sha256": _h(52 if inner else 53),
            "journal_sha256": _h(54 if inner else 55),
            "protocol_journal_hash": _h(56 if inner else 57),
            "statement_hash": _h(58 if inner else 59),
            "profile": "recursive_closed_subtree_v2" if inner else "recursive_epoch_root_v2",
            "immediate_child_count": 2 if inner else 1,
            "flat_leaf_count": 2,
            "tree_height": 1 if inner else 2,
            "subtree_node_count": 3 if inner else 4,
            "immediate_verifier_set_root": verifier_root if inner else _h(60),
            "descendant_sources_root": source_root,
        }

    shared = {
        "aggregation_scope_hash": scope_hash,
        "assigned_leaf_ids_root": assigned_root,
        "descendant_claims_root": _h(61),
        "descendant_sources_root": source_root,
        "flat_v1_post_state_root": _h(62),
        "flat_v1_statement_hash": _h(63),
        "leaf_disclosures_root": _h(64),
    }
    alias = _leaf(
        role="spot_lane_alias_control",
        lane_id="spot-root-child-alias",
        statement_hash=leaves[0]["statement_hash"],
        scope_hash=scope_hash,
        seed=70,
    )
    evidence = {
        "schema": checker.EVIDENCE_SCHEMA,
        "version": 1,
        "date": "2026-07-10",
        "status": checker.EXPECTED_STATUS,
        "trust_roots": {
            "recursive_v2_rebuild_reference": {
                "path": "config/proof_profiles/risc0_recursive_v2_rebuild_reference.json",
                "file_sha256": reference_file_sha256,
                "canonical_json_sha256": checker.v2.reference_canonical_sha256(reference),
            },
            "source_pinned_two_leaf_baseline": {
                "path": (
                    "docs/research/"
                    "RECURSIVE_STARK_V2_TWO_LEAF_SOURCE_PINNED_EVIDENCE_20260710.json"
                ),
                "file_sha256": baseline_file_sha256,
                "canonical_json_sha256": checker._canonical_sha256(baseline),
            },
        },
        "aggregate_v2": baseline["aggregate_v2"],
        "specialized_host_verifier": {
            **verifier,
            "source_size_bytes": 19001,
        },
        "leaf_claims": leaves,
        "same_profile_identity": {
            "child_count": 2,
            "unique_proof_type_count": 1,
            "unique_profile_count": 1,
            "unique_image_id_count": 1,
            "unique_verifier_id_count": 1,
            "distinct_lane_id_count": 2,
            "distinct_statement_hash_count": 2,
            "distinct_source_id_count": 2,
            "derived_child_verifier_id": verifier_id,
            "inner_immediate_verifier_set_root": verifier_root,
            "inner_descendant_sources_root": source_root,
        },
        "proof_pair": {
            "inner": node(inner=True),
            "root": node(inner=False),
            "shared_authenticated_roots": shared,
        },
        "negative_controls": {
            "duplicate_lane_same_artifact": _result(checker.DUPLICATE_LANE_STDERR),
            "duplicate_source_lane_alias": {
                "leaf": alias,
                "harness_reject": _result(checker.ALIAS_HARNESS_STDERR),
                "verifier_reject": _result(checker.DUPLICATE_SOURCE_STDERR),
            },
            "swapped_node_levels": _result(checker.SWAPPED_NODES_STDERR),
            "distinct_leaf_receipt_seal_mutation": {
                "mutation_kind": checker.SEAL_MUTATION_KIND,
                "target_role": "spot_distinct_statement_variant",
                "seal_word_index": 0,
                "seal_word_original": 10,
                "seal_word_mutated": 11,
                "verifier_reject": _result(
                    "leaf receipt verification failed: verification indicates proof is invalid\n"
                ),
            },
        },
        "verification": {
            "dry_run_order_invariant": True,
            "duplicate_lane_reject_verified": True,
            "duplicate_source_alias_reject_verified": True,
            "producer_verified_generated_receipts_and_exact_journal_bytes": True,
            "receipt_seal_mutation_reject_verified": True,
            "specialized_verifier_order_invariant": True,
            "swapped_node_reject_verified": True,
        },
        "claims": checker.EXPECTED_CLAIMS,
        "nonclaims": list(checker.EXPECTED_NONCLAIMS),
    }
    return evidence, reference, baseline, reference_file_sha256, baseline_file_sha256


def _validate(evidence: dict[str, Any]) -> None:
    _, reference, baseline, reference_digest, baseline_digest = _fixture()
    checker.validate_evidence(
        evidence,
        reference,
        baseline,
        reference_file_sha256=reference_digest,
        baseline_file_sha256=baseline_digest,
    )


def _reject_code(evidence: dict[str, Any]) -> str:
    with pytest.raises(checker.v2.EvidenceError) as caught:
        _validate(evidence)
    return caught.value.code


def test_structural_fixture_accepts_exact_claim_scope() -> None:
    evidence, reference, baseline, reference_digest, baseline_digest = _fixture()

    checker.validate_evidence(
        evidence,
        reference,
        baseline,
        reference_file_sha256=reference_digest,
        baseline_file_sha256=baseline_digest,
    )
    assert evidence["claims"] == checker.EXPECTED_CLAIMS
    assert tuple(evidence["nonclaims"]) == checker.EXPECTED_NONCLAIMS


def test_protocol_identity_hash_vectors_match_current_rust_contract() -> None:
    baseline_source = checker.derive_leaf_source_id(
        "spot", "4baf0fa30c7600c623281f207904df7c3b341375bc671dc9accbcd646692b749"
    )
    fee_source = checker.derive_leaf_source_id(
        "spot", "34faf68e6c3635d5b8db01c21a3bc55b57350a9d7170dd70a602f4c3fe495d6c"
    )
    verifier_id = checker.derive_child_verifier_id(
        checker.SPOT_IMAGE_ID, checker.SPOT_PROFILE
    )

    assert baseline_source == "7b41f48bd4729576e4515a4893b4f11ddb7db0dbfd3b0c1f9f938964ca008c7f"
    assert fee_source == "06d085a6d4363a5b5b38e2dd858aee6aa628ae59e2af46139b181bd9a8e0b395"
    assert verifier_id == "e0a68fa82f2c45a252cd76b3b68dc4968b14f63eecf8a294dd79113c8d3aa536"
    assert checker.derive_immediate_verifier_set_root([verifier_id]) == (
        "c5ee6e71ac073d712886826c5a021ad5766e0175766d2a0816a171f59ca01560"
    )
    assert checker.derive_descendant_sources_root([baseline_source, fee_source]) == (
        "2b567154ed4a194269ec19fc9d9db51edcc1c1a4fe044187cdd6c6c775ef152f"
    )


def test_assigned_identity_vectors_match_current_rust_contract() -> None:
    scope = "d877eb72562a83560859710c7ff76cd01a6b96638fa2bda76c1347dc1672880f"
    source_one = "7b41f48bd4729576e4515a4893b4f11ddb7db0dbfd3b0c1f9f938964ca008c7f"
    source_two = "06d085a6d4363a5b5b38e2dd858aee6aa628ae59e2af46139b181bd9a8e0b395"
    assigned_one = checker.derive_assigned_leaf_id(
        scope, "spot-root-child-0001", source_one
    )
    assigned_two = checker.derive_assigned_leaf_id(
        scope, "spot-root-child-0002", source_two
    )

    assert assigned_one == "cf87ed5a98a5977436ea3c24ee900b8b6903662ac15571c0cd0ddf1a25749c35"
    assert assigned_two == "8ca806ae148300eebeac61f70fb1be4a5cb448f37f0b22ef3219954b4fc84c67"
    assert checker.derive_assigned_leaf_ids_root([assigned_one, assigned_two]) == (
        "0d864648420f341856c17207275e4f6b50cd5e7850a6ef538a2099f1d87ecda1"
    )


@pytest.mark.parametrize(
    ("mutation", "expected_code"),
    [
        ("claim_escalation", "EVIDENCE_CLAIMS"),
        ("nonclaim_removal", "EVIDENCE_NONCLAIMS"),
        ("unknown_root_key", "EVIDENCE_SCHEMA"),
        ("reference_drift", "EVIDENCE_REFERENCE_BINDING"),
        ("verifier_binary_drift", "EVIDENCE_VERIFIER_BINDING"),
        ("accepted_source_drift", "EVIDENCE_IDENTITY"),
        ("inner_verifier_root_drift", "EVIDENCE_IDENTITY"),
        ("alias_assigned_identity_drift", "EVIDENCE_ALIAS_CONTROL"),
        ("control_transcript_drift", "EVIDENCE_CONTROLS"),
        ("absolute_path_leak", "PUBLIC_PATH_LEAK"),
    ],
)
def test_structure_preserving_boundary_mutations_reject(
    mutation: str, expected_code: str
) -> None:
    evidence, _, _, _, _ = _fixture()
    candidate = copy.deepcopy(evidence)

    if mutation == "claim_escalation":
        candidate["claims"]["production_ready"] = True
    elif mutation == "nonclaim_removal":
        candidate["nonclaims"].pop()
    elif mutation == "unknown_root_key":
        candidate["extra"] = False
    elif mutation == "reference_drift":
        candidate["trust_roots"]["recursive_v2_rebuild_reference"]["file_sha256"] = _h(99)
    elif mutation == "verifier_binary_drift":
        candidate["specialized_host_verifier"]["binary_sha256"] = _h(99)
    elif mutation == "accepted_source_drift":
        candidate["leaf_claims"][1]["source_id"] = _h(99)
    elif mutation == "inner_verifier_root_drift":
        candidate["proof_pair"]["inner"]["immediate_verifier_set_root"] = _h(99)
    elif mutation == "alias_assigned_identity_drift":
        candidate["negative_controls"]["duplicate_source_lane_alias"]["leaf"][
            "assigned_leaf_id"
        ] = _h(99)
    elif mutation == "control_transcript_drift":
        candidate["negative_controls"]["duplicate_lane_same_artifact"]["stderr"] = (
            "different\n"
        )
    elif mutation == "absolute_path_leak":
        control = candidate["negative_controls"]["duplicate_lane_same_artifact"]
        control["stderr"] = "/srv/relocated/evidence\n"
        control["stderr_sha256"] = _digest_text(control["stderr"])
    else:  # pragma: no cover
        raise AssertionError(mutation)

    assert _reject_code(candidate) == expected_code


def test_duplicate_semantic_source_rejects_even_with_distinct_lanes() -> None:
    evidence, _, _, _, _ = _fixture()
    candidate = copy.deepcopy(evidence)
    second = candidate["leaf_claims"][1]
    first = candidate["leaf_claims"][0]
    second["statement_hash"] = first["statement_hash"]
    second["source_id"] = first["source_id"]

    assert _reject_code(candidate) == "EVIDENCE_IDENTITY"


def test_baseline_spot_artifact_substitution_rejects() -> None:
    evidence, _, _, _, _ = _fixture()
    candidate = copy.deepcopy(evidence)
    baseline_leaf = candidate["leaf_claims"][0]
    substituted_leaf = candidate["leaf_claims"][1]
    for key in ("artifact_file_sha256", "artifact_size_bytes", "receipt_sha256"):
        baseline_leaf[key] = substituted_leaf[key]

    assert _reject_code(candidate) == "EVIDENCE_BASELINE_BINDING"


def test_unrelated_alias_harness_reject_class_rejects_even_with_matching_hash() -> None:
    evidence, _, _, _, _ = _fixture()
    candidate = copy.deepcopy(evidence)
    policy = candidate["negative_controls"]["duplicate_source_lane_alias"][
        "harness_reject"
    ]
    policy["stderr"] = "unrelated constructor failure\n"
    policy["stderr_sha256"] = _digest_text(policy["stderr"])

    assert _reject_code(candidate) == "EVIDENCE_CONTROLS"


def test_unrelated_seal_reject_class_rejects_even_with_matching_hash() -> None:
    evidence, _, _, _, _ = _fixture()
    candidate = copy.deepcopy(evidence)
    policy = candidate["negative_controls"]["distinct_leaf_receipt_seal_mutation"][
        "verifier_reject"
    ]
    policy["stderr"] = "leaf metadata mismatch\n"
    policy["stderr_sha256"] = _digest_text(policy["stderr"])

    assert _reject_code(candidate) == "EVIDENCE_CONTROLS"


@pytest.mark.parametrize(
    "case",
    [
        "empty_source_namespace",
        "zero_statement_hash",
        "empty_lane_id",
        "zero_scope_hash",
        "zero_source_id",
        "empty_profile",
        "zero_image_id",
        "zero_root_member",
        "duplicate_root_member",
    ],
)
def test_identity_helpers_match_rust_fail_closed_preconditions(case: str) -> None:
    nonzero = _h(1)
    with pytest.raises(checker.v2.EvidenceError) as caught:
        if case == "empty_source_namespace":
            checker.derive_leaf_source_id("", nonzero)
        elif case == "zero_statement_hash":
            checker.derive_leaf_source_id("spot", _h(0))
        elif case == "empty_lane_id":
            checker.derive_assigned_leaf_id(nonzero, "", nonzero)
        elif case == "zero_scope_hash":
            checker.derive_assigned_leaf_id(_h(0), "lane", nonzero)
        elif case == "zero_source_id":
            checker.derive_assigned_leaf_id(nonzero, "lane", _h(0))
        elif case == "empty_profile":
            checker.derive_child_verifier_id(checker.SPOT_IMAGE_ID, "")
        elif case == "zero_image_id":
            checker.derive_child_verifier_id(_h(0), checker.SPOT_PROFILE)
        elif case == "zero_root_member":
            checker.derive_descendant_sources_root([_h(0)])
        elif case == "duplicate_root_member":
            checker.derive_descendant_sources_root([nonzero, nonzero])
        else:  # pragma: no cover
            raise AssertionError(case)
    assert caught.value.code == "EVIDENCE_IDENTITY"


def test_production_loader_accepts_only_the_pinned_manifest() -> None:
    evidence = checker.load_evidence()

    assert checker.EXPECTED_EVIDENCE_FILE_SHA256 == (
        "18141ffae7279b1a717edb41674b4fae101a489e2d7870b920c45c8d6810512a"
    )
    assert checker.EXPECTED_EVIDENCE_CANONICAL_SHA256 == (
        "6536149d32040a3ebb7a525434ddf1ec7c36890a4219ce2d3295f6f5934754fb"
    )
    assert checker._canonical_sha256(evidence) == checker.EXPECTED_EVIDENCE_CANONICAL_SHA256


def test_committed_manifest_accepts_against_pinned_recursive_trust_roots() -> None:
    evidence, reference, source_pinned_baseline = checker.load_trust_roots()

    assert evidence["claims"] == checker.EXPECTED_CLAIMS
    assert reference["program"]["image_id"] == evidence["aggregate_v2"]["image_id"]
    assert source_pinned_baseline["leaf_claims"][0]["receipt_sha256"] == (
        evidence["leaf_claims"][0]["receipt_sha256"]
    )
    assert evidence["same_profile_identity"]["unique_verifier_id_count"] == 1
    assert evidence["same_profile_identity"]["distinct_source_id_count"] == 2


def test_production_check_does_not_accept_caller_supplied_trust_roots() -> None:
    parameters = inspect.signature(checker.check_live).parameters

    assert "evidence_path" not in parameters
    assert "reference_path" not in parameters
    assert "expected_evidence_sha256" not in parameters


def _leaf_artifact(*, seal_word: int = 10) -> bytes:
    journal = bytes([1, 2, 3, 4])
    receipt = {
        "inner": {"Succinct": {"seal": [seal_word, 20]}},
        "journal": {"bytes": list(journal)},
        "metadata": {},
    }
    receipt_raw = json.dumps(receipt, separators=(",", ":")).encode("ascii")
    outer = {
        "meta": {
            "proof_type": checker.SPOT_PROOF_TYPE,
            "proof_profile": checker.SPOT_PROFILE,
            "lane_kind": checker.SPOT_LANE_KIND,
            "lane_id": "spot-root-child-0002",
            "risc0_image_id": checker.SPOT_IMAGE_ID,
            "statement_hash": _h(21),
        },
        "proof": base64.b64encode(receipt_raw).decode("ascii"),
        "proof_type": checker.SPOT_PROOF_TYPE,
        "schema": "fixture",
        "schema_version": 1,
        "state_hash": _h(22),
    }
    return json.dumps(outer, separators=(",", ":")).encode("ascii")


def test_seal_mutation_changes_only_selected_word_in_temporary_copy(tmp_path: Path) -> None:
    source = tmp_path / "source.json"
    mutated = tmp_path / "mutated.json"
    source.write_bytes(_leaf_artifact())
    mutation = {
        "seal_word_index": 0,
        "seal_word_original": 10,
        "seal_word_mutated": 11,
    }

    mutated.write_bytes(checker._mutate_succinct_seal_word(source.read_bytes(), mutation))
    source_outer = json.loads(source.read_bytes())
    mutated_outer = json.loads(mutated.read_bytes())
    source_receipt = json.loads(base64.b64decode(source_outer["proof"]))
    mutated_receipt = json.loads(base64.b64decode(mutated_outer["proof"]))

    source_without_proof = {key: value for key, value in source_outer.items() if key != "proof"}
    mutated_without_proof = {key: value for key, value in mutated_outer.items() if key != "proof"}
    assert source_without_proof == mutated_without_proof
    assert source_receipt["inner"]["Succinct"]["seal"] == [10, 20]
    assert mutated_receipt["inner"]["Succinct"]["seal"] == [11, 20]
    assert source.read_bytes() == _leaf_artifact()


def test_live_leaf_binding_recomputes_receipt_journal_and_claim_hashes(tmp_path: Path) -> None:
    raw = _leaf_artifact()
    outer, receipt_raw, journal = checker._decode_leaf_artifact(raw, label="FIXTURE")
    _ = outer
    statement_hash = _h(21)
    source_id = checker.derive_leaf_source_id(checker.SPOT_LANE_KIND, statement_hash)
    row = {
        "role": "spot_distinct_statement_variant",
        "proof_type": checker.SPOT_PROOF_TYPE,
        "profile": checker.SPOT_PROFILE,
        "lane_kind": checker.SPOT_LANE_KIND,
        "lane_id": "spot-root-child-0002",
        "image_id": checker.SPOT_IMAGE_ID,
        "statement_hash": statement_hash,
        "source_id": source_id,
        "assigned_leaf_id": _h(23),
        "journal_sha256": hashlib.sha256(journal).hexdigest(),
        "protocol_child_journal_hash": hashlib.sha256(
            checker.CHILD_JOURNAL_HASH_DOMAIN + len(journal).to_bytes(4, "big") + journal
        ).hexdigest(),
        "verification_claim_hash": hashlib.sha256(
            checker.CHILD_CLAIM_HASH_DOMAIN
            + checker._image_id_words_be(checker.SPOT_IMAGE_ID)
            + len(journal).to_bytes(4, "big")
            + journal
        ).hexdigest(),
        "artifact_file_sha256": hashlib.sha256(raw).hexdigest(),
        "artifact_size_bytes": len(raw),
        "receipt_sha256": hashlib.sha256(receipt_raw).hexdigest(),
    }
    artifact = tmp_path / "leaf.json"
    artifact.write_bytes(raw)

    checker._validate_live_leaf(artifact.read_bytes(), row, label="FIXTURE")
    row["verification_claim_hash"] = _h(99)
    with pytest.raises(checker.v2.EvidenceError) as caught:
        checker._validate_live_leaf(artifact.read_bytes(), row, label="FIXTURE")
    assert caught.value.code == "LIVE_LEAF_BINDING"


def test_private_staging_uses_digest_bytes_and_exact_modes(tmp_path: Path) -> None:
    staging = tmp_path / "stage"
    staging.mkdir(mode=0o700)
    staging.chmod(0o700)
    data_raw = b"authenticated artifact"
    executable_raw = b"#!/bin/sh\nexit 0\n"
    data_digest = checker.v2.FileDigest(
        data_raw, hashlib.sha256(data_raw).hexdigest(), len(data_raw)
    )
    executable_digest = checker.v2.FileDigest(
        executable_raw,
        hashlib.sha256(executable_raw).hexdigest(),
        len(executable_raw),
    )

    data_path = checker._stage_verified_file(
        staging,
        filename="artifact.json",
        digest=data_digest,
        executable=False,
        max_bytes=1024,
    )
    executable_path = checker._stage_verified_file(
        staging,
        filename="verifier",
        digest=executable_digest,
        executable=True,
        max_bytes=1024,
    )

    assert data_path.read_bytes() == data_raw
    assert executable_path.read_bytes() == executable_raw
    assert data_path.stat().st_mode & 0o777 == 0o600
    assert executable_path.stat().st_mode & 0o777 == 0o700
    assert staging.stat().st_mode & 0o777 == 0o700


def test_private_staging_is_immune_to_post_digest_original_mutation(tmp_path: Path) -> None:
    staging = tmp_path / "stage"
    staging.mkdir(mode=0o700)
    staging.chmod(0o700)
    original = tmp_path / "original.json"
    original.write_bytes(b"verified bytes")
    digest = checker.v2._read_regular(original, label="original", max_bytes=1024)
    staged = checker._stage_verified_file(
        staging,
        filename="staged.json",
        digest=digest,
        executable=False,
        max_bytes=1024,
    )

    original.write_bytes(b"attacker replacement")

    assert staged.read_bytes() == b"verified bytes"
    assert hashlib.sha256(staged.read_bytes()).hexdigest() == digest.sha256


def test_private_staging_rejects_nonprivate_directory_mode(tmp_path: Path) -> None:
    staging = tmp_path / "stage"
    staging.mkdir(mode=0o755)
    staging.chmod(0o755)
    raw = b"artifact"
    digest = checker.v2.FileDigest(raw, hashlib.sha256(raw).hexdigest(), len(raw))

    with pytest.raises(checker.v2.EvidenceError) as caught:
        checker._stage_verified_file(
            staging,
            filename="artifact.json",
            digest=digest,
            executable=False,
            max_bytes=1024,
        )
    assert caught.value.code == "LIVE_STAGING"


def test_staged_execution_uses_empty_private_home_despite_hostile_parent_home(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    hostile_home = tmp_path / "hostile-parent-home"
    hostile_home.mkdir()
    (hostile_home / "attacker-config").write_text("hostile", encoding="utf-8")
    monkeypatch.setenv("HOME", str(hostile_home))
    staging = tmp_path / "stage"
    staging.mkdir(mode=0o700)
    staging.chmod(0o700)

    clean_env = checker._clean_execution_env(staging)
    private_home = Path(clean_env["HOME"])

    assert private_home == staging / "home"
    assert private_home != hostile_home
    assert private_home.stat().st_mode & 0o777 == 0o700
    assert list(private_home.iterdir()) == []
    assert clean_env == {
        "HOME": str(private_home),
        "LANG": "C",
        "LC_ALL": "C",
        "PATH": "/usr/bin:/bin",
        "RISC0_DEV_MODE": "0",
        "TZ": "UTC",
    }
    assert (hostile_home / "attacker-config").read_text(encoding="utf-8") == "hostile"


def test_cli_rejection_is_machine_readable_for_unpinned_live_artifact(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    placeholder = tmp_path / "placeholder"
    placeholder.write_bytes(b"placeholder")
    placeholder.chmod(0o755)
    arguments: list[str] = []
    for option in (
        "--baseline-spot-leaf",
        "--distinct-spot-leaf",
        "--duplicate-source-alias-leaf",
        "--inner-artifact",
        "--root-artifact",
        "--release-harness",
        "--two-leaf-verifier",
    ):
        arguments.extend((option, str(placeholder)))
    arguments.append("--json")

    assert checker.main(arguments) == 1
    report = json.loads(capsys.readouterr().out)
    assert report["ok"] is False
    assert report["error_code"] == "LIVE_FILE_SHA256"
    assert report["public_claim_allowed"] is False
    assert report["production_ready"] is False
