"""Adversarial contracts for the packet-bound authority-neutral release stage."""

from __future__ import annotations

import copy
import hashlib
import json
import os
from pathlib import Path
from typing import Any, Mapping, cast

import pytest

from tests import test_run_zrpf_remote_reproof_worker_v2 as worker_fixture
from tests import test_zrpf_spot_settlement_v7_local_evidence as v7_fixture
from tools import plan_zrpf_remote_reproof_handoff_v2 as handoff
from tools import run_zrpf_remote_reproof_worker_v2 as worker
from tools import zrpf_remote_release_checks_stage_v2 as release_stage
from tools import zrpf_remote_reproof_handoff_v2_catalog as catalog
from tools import zrpf_spot_v7_release_schema as release_schema

REPO_ROOT = Path(__file__).resolve().parents[1]


def _sha(label: str) -> str:
    return hashlib.sha256(label.encode("ascii")).hexdigest()


def _compact_line(value: Mapping[str, object]) -> bytes:
    return (json.dumps(value, ensure_ascii=True, separators=(",", ":")) + "\n").encode("ascii")


def _exact_seal_mutation(source: bytes) -> bytes:
    document = json.loads(source)
    document["inner"]["Succinct"]["seal"][1] ^= 1
    return json.dumps(document, ensure_ascii=True, separators=(",", ":")).encode("ascii")


def _receipt_journal(source: bytes) -> bytes:
    document = json.loads(source)
    return bytes(document["journal"]["bytes"])


def _v7_artifact_raw(tmp_path: Path) -> dict[str, bytes]:
    fixture_root = tmp_path / "v7-fixture"
    fixture_root.mkdir()
    fixture = v7_fixture._raw_inputs(fixture_root, REPO_ROOT)
    raw = {
        "v7_receipt": fixture["v7_receipt"],
        "v7_seal_mutation": fixture["v7_receipt_seal_mutation"],
        "v6_settlement_receipt": fixture["v6_child_receipt"],
        "v7_guest_input": fixture["v7_guest_input"],
        "v7_journal": fixture["v7_journal"],
        "v7_verifier_output": fixture["v7_verifier_output"],
        "v7_plan_b": fixture["v7_plan_b"],
        "v6_settlement_journal": _receipt_journal(fixture["v6_child_receipt"]),
    }
    for role in (*release_stage.IDENTITY_PROGRAM_ROLES, "v7_program"):
        prefix = b"R0BF" if role == "v7_program" else b"program-v1:"
        raw[role] = prefix + role.encode("ascii")
    for index, (receipt_role, program_role) in enumerate(
        (
            ("v6_leaf_receipt", "v6_leaf_program"),
            ("v6_l1_receipt", "v6_l1_program"),
            ("v6_l2_receipt", "v6_l2_program"),
        ),
        start=1,
    ):
        raw[receipt_role] = v7_fixture._canonical_receipt(
            f"journal:{receipt_role}".encode("ascii"),
            seal_word=39 + index * 2,
            image_id=bytes.fromhex(_sha(f"image:{program_role}")),
        )
    for receipt_role, mutation_role in (
        ("v6_leaf_receipt", "v6_leaf_seal_mutation"),
        ("v6_l1_receipt", "v6_l1_seal_mutation"),
        ("v6_l2_receipt", "v6_l2_seal_mutation"),
        ("v6_settlement_receipt", "v6_settlement_seal_mutation"),
    ):
        raw[mutation_role] = _exact_seal_mutation(raw[receipt_role])
    return raw


def _v7_report(raw: Mapping[str, bytes]) -> dict[str, object]:
    analysis = release_stage.v7_static.analyze_artifacts_v1(
        {
            "v7_receipt": raw["v7_receipt"],
            "v7_receipt_seal_mutation": raw["v7_seal_mutation"],
            "v6_child_receipt": raw["v6_settlement_receipt"],
            "v7_guest_input": raw["v7_guest_input"],
            "v7_journal": raw["v7_journal"],
            "v7_verifier_output": raw["v7_verifier_output"],
            "v7_plan_b": raw["v7_plan_b"],
        }
    )
    return {
        "schema": "zenodex/zrpf_spot_settlement_v7_proof_report/v1",
        "status": "spot_settlement_v7_succinct_receipt_verified_before_persistence",
        "v7_program_id": analysis.output.fixed_fields[0].hex(),
        "v7_profile_id": analysis.output.fixed_fields[1].hex(),
        "v7_program_manifest_root": analysis.output.fixed_fields[2].hex(),
        "v7_journal_sha256": hashlib.sha256(raw["v7_journal"]).hexdigest(),
        "v7_receipt_sha256": hashlib.sha256(raw["v7_receipt"]).hexdigest(),
        "v7_receipt_seal_mutation_sha256": hashlib.sha256(raw["v7_seal_mutation"]).hexdigest(),
        "v7_verifier_output_sha256": hashlib.sha256(raw["v7_verifier_output"]).hexdigest(),
        "v7_plan_b_sha256": hashlib.sha256(raw["v7_plan_b"]).hexdigest(),
        "v7_guest_input_sha256": hashlib.sha256(raw["v7_guest_input"]).hexdigest(),
        "v6_child_receipt_sha256": hashlib.sha256(raw["v6_settlement_receipt"]).hexdigest(),
        "receipt_kind": "succinct",
        "exact_seal_mutation_rejected": True,
        "release_authority": False,
        "settlement_authority": False,
        "production_authority": False,
        "zero_knowledge_privacy": False,
        "nonclaims": list(release_stage.V7_NON_CLAIMS),
    }


def _identity_images(raw: Mapping[str, bytes] | None = None) -> dict[str, str]:
    images = {role: _sha(f"image:{role}") for role in release_stage.IDENTITY_PROGRAM_ROLES}
    if raw is None:
        return images
    for stage_id, program_role, receipt_role, *_rest in release_stage.MUTATION_STAGE_BINDINGS[:-1]:
        receipt = release_stage.v7_static._decode_receipt(
            raw[receipt_role],
            receipt_role,
            maximum_journal_bytes=release_stage.MUTATION_JOURNAL_MAXIMUMS_V1[stage_id],
        )
        images[program_role] = receipt.claimed_image_id.hex()
    return images


def _mutation_report(
    raw: Mapping[str, bytes],
    identity_images: Mapping[str, str],
    v7_report: Mapping[str, object],
) -> dict[str, object]:
    stages: list[dict[str, object]] = []
    for (
        stage_id,
        program_role,
        receipt_role,
        mutation_role,
        journal_role,
        boundary,
    ) in release_stage.MUTATION_STAGE_BINDINGS:
        program = raw[program_role]
        receipt = raw[receipt_role]
        mutation = raw[mutation_role]
        image_id = (
            cast(str, v7_report["v7_program_id"])
            if program_role == "v7_program"
            else identity_images[program_role]
        )
        receipt_document = json.loads(receipt)
        mutation_document = json.loads(mutation)
        source_seal = receipt_document["inner"]["Succinct"]["seal"]
        candidate_seal = mutation_document["inner"]["Succinct"]["seal"]
        journal_sha256 = hashlib.sha256(bytes(receipt_document["journal"]["bytes"])).hexdigest()
        if journal_role is not None:
            assert journal_sha256 == hashlib.sha256(raw[journal_role]).hexdigest()
        stages.append(
            {
                "stage_id": stage_id,
                "program": {
                    "program_bytes": len(program),
                    "program_sha256": hashlib.sha256(program).hexdigest(),
                    "expected_image_id": image_id,
                },
                "receipt_profile_id": release_stage.MUTATION_RECEIPT_PROFILE_ID,
                "positive_receipt_bytes": len(receipt),
                "positive_receipt_sha256": hashlib.sha256(receipt).hexdigest(),
                "positive_journal_sha256": journal_sha256,
                "mutation_receipt_bytes": len(mutation),
                "mutation_receipt_sha256": hashlib.sha256(mutation).hexdigest(),
                "mutation": {
                    "word_count": len(source_seal),
                    "word_index": 1,
                    "original_word": source_seal[1],
                    "mutated_word": candidate_seal[1],
                    "xor_mask": 1,
                },
                "reject_boundary": boundary,
                "reject_code": "receipt_verification_failed",
            }
        )
    report: dict[str, object] = {
        "schema": release_stage.MUTATION_REPORT_SCHEMA,
        "status": release_stage.MUTATION_REPORT_STATUS,
        "report_id": release_stage.ZERO_SHA256,
        "receipt_profile_id": release_stage.MUTATION_RECEIPT_PROFILE_ID,
        "positive_receipts_verified": 5,
        "exact_seal_mutations_rejected": 5,
        "settlement_l2_claim_bound": True,
        "stages": stages,
        "authority": {field: False for field in release_stage.MUTATION_AUTHORITY_FIELDS},
        "non_claims": list(release_stage.MUTATION_NON_CLAIMS),
    }
    report["report_id"] = release_stage._derive_mutation_report_id(report)
    return report


def _write_reports(tmp_path: Path) -> tuple[dict[str, bytes], dict[str, str], dict[str, object]]:
    raw = _v7_artifact_raw(tmp_path)
    v7_report = _v7_report(raw)
    raw["v7_report"] = _compact_line(v7_report)
    images = _identity_images(raw)
    mutation_report = _mutation_report(raw, images, v7_report)
    raw["mutation_report"] = _compact_line(mutation_report)
    return raw, images, v7_report


def _artifact_id(role: str, digest: str, size_bytes: int) -> str:
    contracts = {str(row["role"]): row for row in handoff._artifact_contracts()}
    contract = contracts[role]
    record: dict[str, object] = {
        "schema": handoff.ARTIFACT_RECORD_SCHEMA,
        "artifact_id": release_stage.ZERO_SHA256,
        "contract_id": contract["contract_id"],
        "role": role,
        "path": contract["path"],
        "sha256": digest,
        "size_bytes": size_bytes,
        "producer_stage": contract["producer_stage"],
    }
    return handoff._derive_artifact_id(record)


def _packet(input_ids: list[str]) -> dict[str, object]:
    packet: dict[str, object] = {
        "schema": handoff.EXECUTION_PACKET_SCHEMA,
        "status": "exact_inputs_bound_without_execution_provenance",
        "execution_packet_id": release_stage.ZERO_SHA256,
        "handoff_id": _sha("handoff"),
        "source_binding_id": _sha("source-binding"),
        "task_id": _sha("release-task"),
        "stage_id": "release_checks",
        "ordinal": len(catalog.TASK_SPECS) - 1,
        "worker_commit": "a" * 40,
        "worker_tree": "b" * 40,
        "proof_profile_id": handoff.SUCCINCT_PROFILE_ID,
        "input_artifact_ids": input_ids,
        "input_publication_marker_ids": [
            _sha(f"marker:{stage}") for stage in catalog.RELEASE_CHECK_PREDECESSOR_STAGE_IDS
        ],
        "authority": handoff.false_authority(),
        "non_claims": list(handoff.NON_CLAIMS),
    }
    packet["execution_packet_id"] = handoff.derive_execution_packet_id(packet)
    return packet


def _closure_evidence(
    plan_sha256: str, worker_commit: str, runtime_sha256: str
) -> dict[str, object]:
    return {
        "schema": release_schema.EVIDENCE_SCHEMA,
        "status": "authority_neutral_v7_release_closure_checked",
        "plan_sha256": plan_sha256,
        "c0_commit": "1" * 40,
        "c1_commit": "2" * 40,
        "c2_commit": "3" * 40,
        "governance_commit": worker_commit,
        "governance_tree": "4" * 40,
        "v7_child_image_id": _sha("v7-child"),
        "source_closure_root_sha256": _sha("source-closure"),
        "lockfile_set_root_sha256": _sha("lockfiles"),
        "runtime_identity_sha256": runtime_sha256,
        "validated_facts": dict(release_stage.CLOSURE_VALIDATED_FACTS_V1),
        "authority": {field: False for field in release_schema.AUTHORITY_FIELDS},
        "non_claims": list(release_schema.NON_CLAIMS),
    }


def _evidence_seed() -> dict[str, object]:
    raw = {
        "identity_candidate_report": b"identity-report\n",
        "post_pin_governance_result": b"governance\n",
        "worker_build_report": b"worker-build\n",
        "mutation_report": b"mutation-report\n",
        "v7_report": b"v7-report\n",
        "release_runtime_identity": b"runtime\n",
    }
    observation_raw = {
        role: raw.get(role, f"artifact:{role}\n".encode("ascii"))
        for role in release_stage.PACKET_INPUT_ROLES
    }
    observations = [
        {
            "role": role,
            "artifact_id": _artifact_id(
                role, hashlib.sha256(observation_raw[role]).hexdigest(), len(observation_raw[role])
            ),
            "sha256": hashlib.sha256(observation_raw[role]).hexdigest(),
            "size_bytes": len(observation_raw[role]),
        }
        for role in release_stage.PACKET_INPUT_ROLES
    ]
    packet = _packet([cast(str, row["artifact_id"]) for row in observations])
    plan_sha256 = _sha("release-plan")
    closure = _closure_evidence(
        plan_sha256,
        cast(str, packet["worker_commit"]),
        hashlib.sha256(raw["release_runtime_identity"]).hexdigest(),
    )
    return release_stage._build_evidence(
        packet=packet,
        plan_sha256=plan_sha256,
        closure_evidence=closure,
        observations=observations,
        artifact_raw=raw,
        mutation_report={"report_id": _sha("mutation-report-id")},
        v7_report={"v7_program_id": _sha("v7-program-id")},
    )


def test_valid_v7_and_mutation_reports_bind_exact_artifacts(tmp_path: Path) -> None:
    raw, images, expected_v7 = _write_reports(tmp_path)

    observed_v7 = release_stage._validate_v7_report(raw)
    observed_mutation = release_stage._validate_mutation_report(raw, images, observed_v7)

    assert observed_v7 == expected_v7
    assert observed_mutation["receipt_profile_id"] == release_stage.MUTATION_RECEIPT_PROFILE_ID


def test_v7_semantic_profile_hash_is_distinct_from_receipt_profile_name(tmp_path: Path) -> None:
    raw, _images, _v7 = _write_reports(tmp_path)
    report = cast(dict[str, object], json.loads(raw["v7_report"]))
    assert report["v7_profile_id"] != release_stage.MUTATION_RECEIPT_PROFILE_ID
    report["v7_profile_id"] = _sha("wrong-semantic-profile")
    raw["v7_report"] = _compact_line(report)

    with pytest.raises(release_stage.RemoteReleaseChecksError) as rejected:
        release_stage._validate_v7_report(raw)
    assert rejected.value.code == "release_v7_output_identity_binding"


@pytest.mark.parametrize(
    ("mutation", "code"),
    (
        (
            lambda report: report.__setitem__("receipt_profile_id", _sha("semantic-profile")),
            "release_mutation_profile",
        ),
        (
            lambda report: cast(list[dict[str, Any]], report["stages"])[0]["mutation"].__setitem__(
                "mutated_word", 19
            ),
            "release_mutation_relation",
        ),
        (
            lambda report: cast(list[dict[str, Any]], report["stages"])[4]["program"].__setitem__(
                "expected_image_id", _sha("wrong-v7-image")
            ),
            "release_mutation_image_binding",
        ),
    ),
)
def test_mutation_report_deep_reanchors_reject(
    tmp_path: Path,
    mutation,
    code: str,
) -> None:
    raw, images, v7 = _write_reports(tmp_path)
    report = cast(dict[str, object], json.loads(raw["mutation_report"]))
    mutation(report)
    report["report_id"] = release_stage._derive_mutation_report_id(report)
    raw["mutation_report"] = _compact_line(report)

    with pytest.raises(release_stage.RemoteReleaseChecksError) as rejected:
        release_stage._validate_mutation_report(raw, images, v7)
    assert rejected.value.code == code


@pytest.mark.parametrize(
    ("receipt_role", "mutation_role"),
    (
        ("v6_leaf_receipt", "v6_leaf_seal_mutation"),
        ("v6_l1_receipt", "v6_l1_seal_mutation"),
        ("v6_l2_receipt", "v6_l2_seal_mutation"),
        ("v6_settlement_receipt", "v6_settlement_seal_mutation"),
    ),
)
def test_v6_mutation_relation_is_derived_from_exact_receipt_bytes(
    tmp_path: Path,
    receipt_role: str,
    mutation_role: str,
) -> None:
    raw, images, v7 = _write_reports(tmp_path)
    raw[mutation_role] = raw[receipt_role]
    report = cast(dict[str, object], json.loads(raw["mutation_report"]))
    stage_index = next(
        index
        for index, binding in enumerate(release_stage.MUTATION_STAGE_BINDINGS)
        if binding[2] == receipt_role
    )
    stage = cast(list[dict[str, Any]], report["stages"])[stage_index]
    stage["mutation_receipt_bytes"] = len(raw[mutation_role])
    stage["mutation_receipt_sha256"] = hashlib.sha256(raw[mutation_role]).hexdigest()
    report["report_id"] = release_stage._derive_mutation_report_id(report)
    raw["mutation_report"] = _compact_line(report)

    with pytest.raises(release_stage.RemoteReleaseChecksError) as rejected:
        release_stage._validate_mutation_report(raw, images, v7)
    assert rejected.value.code == "release_mutation_receipt_relation"


def test_v6_settlement_mutation_accepts_protocol_journal_above_legacy_four_kib() -> None:
    source = v7_fixture._canonical_receipt(
        b"j" * 4_097,
        seal_word=19,
        image_id=bytes.fromhex(_sha("large-settlement-image")),
    )
    mutation = _exact_seal_mutation(source)

    facts, journal_sha256, claimed_image_id = release_stage._derive_exact_receipt_mutation(
        source,
        mutation,
        maximum_journal_bytes=release_stage.MUTATION_JOURNAL_MAXIMUMS_V1["v6_settlement"],
    )

    assert facts == {
        "word_count": 3,
        "word_index": 1,
        "original_word": 19,
        "mutated_word": 18,
        "xor_mask": 1,
    }
    assert journal_sha256 == hashlib.sha256(b"j" * 4_097).hexdigest()
    assert claimed_image_id == _sha("large-settlement-image")


def test_v6_leaf_mutation_rejects_journal_above_value_node_bound() -> None:
    source = v7_fixture._canonical_receipt(
        b"j" * (release_stage.MAX_VALUE_NODE_JOURNAL_BYTES_V4 + 1),
        seal_word=19,
        image_id=bytes.fromhex(_sha("oversized-leaf-image")),
    )
    with pytest.raises(release_stage.RemoteReleaseChecksError) as rejected:
        release_stage._derive_exact_receipt_mutation(
            source,
            _exact_seal_mutation(source),
            maximum_journal_bytes=release_stage.MUTATION_JOURNAL_MAXIMUMS_V1["v6_leaf"],
        )
    assert rejected.value.code == "release_mutation_receipt_relation"


def test_receipt_pair_enforces_rust_verifier_total_byte_cap(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source = v7_fixture._canonical_receipt(
        b"bounded-journal",
        seal_word=19,
        image_id=bytes.fromhex(_sha("bounded-image")),
    )
    monkeypatch.setattr(release_stage.v7_static, "MAX_RECEIPT_BYTES_V1", len(source) - 1)
    with pytest.raises(release_stage.RemoteReleaseChecksError) as rejected:
        release_stage._derive_exact_receipt_mutation(
            source,
            _exact_seal_mutation(source),
            maximum_journal_bytes=release_stage.MAX_VALUE_NODE_JOURNAL_BYTES_V4,
        )
    assert rejected.value.code == "release_mutation_receipt_size"


def test_v6_receipt_claimed_image_must_equal_expected_program_image(tmp_path: Path) -> None:
    raw, images, v7 = _write_reports(tmp_path)
    document = json.loads(raw["v6_leaf_receipt"])
    document["inner"]["Succinct"]["claim"]["Value"]["pre"]["Value"]["merkle_root"][0] ^= 1
    raw["v6_leaf_receipt"] = json.dumps(document, separators=(",", ":")).encode("ascii")
    raw["v6_leaf_seal_mutation"] = _exact_seal_mutation(raw["v6_leaf_receipt"])
    report = cast(dict[str, object], json.loads(raw["mutation_report"]))
    stage = cast(list[dict[str, Any]], report["stages"])[0]
    stage["positive_receipt_bytes"] = len(raw["v6_leaf_receipt"])
    stage["positive_receipt_sha256"] = hashlib.sha256(raw["v6_leaf_receipt"]).hexdigest()
    stage["mutation_receipt_bytes"] = len(raw["v6_leaf_seal_mutation"])
    stage["mutation_receipt_sha256"] = hashlib.sha256(raw["v6_leaf_seal_mutation"]).hexdigest()
    report["report_id"] = release_stage._derive_mutation_report_id(report)
    raw["mutation_report"] = _compact_line(report)

    with pytest.raises(release_stage.RemoteReleaseChecksError) as rejected:
        release_stage._validate_mutation_report(raw, images, v7)
    assert rejected.value.code == "release_mutation_receipt_image_binding"


def test_valid_but_wrong_report_mutation_tuple_rejects_exact_byte_binding(tmp_path: Path) -> None:
    raw, images, v7 = _write_reports(tmp_path)
    report = cast(dict[str, object], json.loads(raw["mutation_report"]))
    mutation = cast(dict[str, int], cast(list[dict[str, Any]], report["stages"])[0]["mutation"])
    mutation["original_word"] = 101
    mutation["mutated_word"] = 100
    report["report_id"] = release_stage._derive_mutation_report_id(report)
    raw["mutation_report"] = _compact_line(report)

    with pytest.raises(release_stage.RemoteReleaseChecksError) as rejected:
        release_stage._validate_mutation_report(raw, images, v7)
    assert rejected.value.code == "release_mutation_report_relation_binding"


def test_evidence_self_validation_binds_nested_authority_and_artifact_ids() -> None:
    evidence = _evidence_seed()
    raw = handoff.canonical_json_bytes(evidence)
    assert release_stage.validate_release_evidence_v2(raw) == evidence
    assert all(value is False for value in cast(dict[str, bool], evidence["authority"]).values())
    assert "bundle_id" not in evidence
    facts = cast(dict[str, bool], evidence["validated_facts"])
    assert facts["ordered_predecessor_marker_digest_list_committed"] is True
    assert "all_predecessor_publication_marker_ids_bound" not in facts
    assert "release_evidence_does_not_independently_reopen_or_validate_marker_records" in cast(
        list[str], evidence["non_claims"]
    )

    mutated = copy.deepcopy(evidence)
    cast(
        dict[str, object], cast(dict[str, object], mutated["release_closure_evidence"])["authority"]
    )["production_authority"] = 0
    mutated["evidence_id"] = release_stage.derive_release_evidence_id_v2(mutated)
    with pytest.raises(release_stage.RemoteReleaseChecksError) as rejected:
        release_stage.validate_release_evidence_v2(handoff.canonical_json_bytes(mutated))
    assert rejected.value.code == "release_evidence_closure_authority"


def test_evidence_rejects_reordered_observation_and_return_cycle_field() -> None:
    evidence = _evidence_seed()
    reordered = copy.deepcopy(evidence)
    observations = cast(list[dict[str, object]], reordered["input_observations"])
    observations[0], observations[1] = observations[1], observations[0]
    reordered["evidence_id"] = release_stage.derive_release_evidence_id_v2(reordered)
    with pytest.raises(release_stage.RemoteReleaseChecksError) as rejected:
        release_stage.validate_release_evidence_v2(handoff.canonical_json_bytes(reordered))
    assert rejected.value.code == "release_evidence_observation_order"

    cyclic = copy.deepcopy(evidence)
    cyclic["bundle_id"] = _sha("return-v5")
    cyclic["evidence_id"] = release_stage.derive_release_evidence_id_v2(cyclic)
    with pytest.raises(release_stage.RemoteReleaseChecksError) as rejected:
        release_stage.validate_release_evidence_v2(handoff.canonical_json_bytes(cyclic))
    assert rejected.value.code == "release_evidence_fields"


def test_packet_rejects_marker_replay_and_integer_authority() -> None:
    input_ids = [_sha(f"input:{role}") for role in release_stage.PACKET_INPUT_ROLES]
    packet = _packet(input_ids)
    assert release_stage._parse_release_packet(handoff.canonical_json_bytes(packet)) == packet

    duplicate = copy.deepcopy(packet)
    markers = cast(list[str], duplicate["input_publication_marker_ids"])
    markers[-1] = markers[0]
    duplicate["execution_packet_id"] = handoff.derive_execution_packet_id(duplicate)
    with pytest.raises(release_stage.RemoteReleaseChecksError) as rejected:
        release_stage._parse_release_packet(handoff.canonical_json_bytes(duplicate))
    assert rejected.value.code == "release_packet_marker_inventory"

    integer = copy.deepcopy(packet)
    cast(dict[str, object], integer["authority"])["release_authority"] = 0
    integer["execution_packet_id"] = handoff.derive_execution_packet_id(integer)
    with pytest.raises(release_stage.RemoteReleaseChecksError) as rejected:
        release_stage._parse_release_packet(handoff.canonical_json_bytes(integer))
    assert rejected.value.code == "release_packet_authority"


def test_strict_json_rejects_duplicates_floats_deep_values_and_huge_integers() -> None:
    cases = (
        (b'{"a":1,"a":2}\n', "duplicate_json_key"),
        (b'{"a":1.0}\n', "non_integer_json_number"),
        (b'{"a":123456789012345678901}\n', "json_integer_bound"),
    )
    for raw, code in cases:
        with pytest.raises(release_stage.RemoteReleaseChecksError) as rejected:
            release_stage._decode_json(raw, "boundary")
        assert rejected.value.code == code

    value: object = "leaf"
    for index in range(release_stage.MAX_JSON_DEPTH + 2):
        value = {f"level_{index}": value}
    with pytest.raises(release_stage.RemoteReleaseChecksError) as rejected:
        release_stage._decode_json(handoff.canonical_json_bytes(value), "boundary")
    assert rejected.value.code == "json_depth"


def test_stable_read_rejects_fifo_without_blocking(tmp_path: Path) -> None:
    fifo = tmp_path / "hostile-fifo"
    os.mkfifo(fifo)
    with pytest.raises(release_stage.RemoteReleaseChecksError) as rejected:
        release_stage._stable_read(fifo, "fifo", 1024)
    assert rejected.value.code == "fifo_file"


def test_outputs_must_be_absolute_distinct_absent_and_canonical(tmp_path: Path) -> None:
    left = tmp_path / "plan.json"
    right = tmp_path / "evidence.json"
    release_stage._require_distinct_absent_outputs(left, right)

    left.write_bytes(b"stale")
    with pytest.raises(release_stage.RemoteReleaseChecksError) as rejected:
        release_stage._require_distinct_absent_outputs(left, right)
    assert rejected.value.code == "release_output_precondition"

    with pytest.raises(release_stage.RemoteReleaseChecksError) as rejected:
        release_stage._require_distinct_absent_outputs(Path("plan.json"), Path("evidence.json"))
    assert rejected.value.code == "release_output_precondition"


def test_catalog_exposes_one_acyclic_fully_bound_release_adapter() -> None:
    task = catalog.TASK_SPECS[-1]
    expectation = next(
        spec for spec in catalog.ARTIFACT_SPECS if spec.role == "release_plan_expectation"
    )

    assert task.stage_id == "release_checks"
    assert task.depends_on == catalog.RELEASE_CHECK_PREDECESSOR_STAGE_IDS
    assert task.inputs == catalog.RELEASE_CHECK_INPUT_ROLES
    assert task.execution_adapter_status == "implemented"
    assert task.command_status == "template_available"
    assert task.pre_commands == ()
    assert task.stdout_artifact_role is None
    assert "@execution_packet_file" in task.command
    assert "@repo" not in task.command
    assert "@release_plan_sha256" not in task.command
    assert expectation.producer_stage == "external_operator"
    assert all(task.command.count(f"@{role}") == 1 for role in catalog.RELEASE_CHECK_ARTIFACT_ROLES)
    assert len(task.command) == len(set(task.command))


def test_worker_resolves_every_release_adapter_argument_from_packet_bound_paths(
    tmp_path: Path,
) -> None:
    repo, _chain, plan, artifact_root, packet_path, packet = worker_fixture._stage_context(
        tmp_path, stage_id="release_checks"
    )
    stage = worker.validate_stage_packet(plan, packet, repo, artifact_root)
    input_paths = {item.role: artifact_root / item.path for item in stage.inputs}
    input_paths["execution_packet_file"] = packet_path
    output_root = tmp_path / "resolved-outputs"
    output_root.mkdir()
    output_paths = {item.role: output_root / Path(item.path).name for item in stage.outputs}

    resolved = worker._resolve_command(
        stage.commands[0],
        stage,
        input_paths,
        output_paths,
        {},
    )
    argv = list(resolved.argv)

    assert Path(argv[0]).parent == Path("/usr/bin")
    assert Path(argv[0]).name.startswith("python3")
    assert argv[1] == "tools/zrpf_remote_release_checks_stage_v2.py"
    assert argv[argv.index("--repository") + 1] == "."
    assert argv[argv.index("--execution-packet") + 1] == str(packet_path)
    for role in release_stage.RELEASE_CHECK_ARTIFACT_ROLES:
        flag = f"--artifact-{role.replace('_', '-')}"
        assert argv.count(flag) == 1
        assert argv[argv.index(flag) + 1] == str(input_paths[role])


def test_actual_worker_argv_resolves_exact_dot_repository_at_cli_boundary(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    repo, _chain, plan, artifact_root, packet_path, packet = worker_fixture._stage_context(
        tmp_path, stage_id="release_checks"
    )
    stage = worker.validate_stage_packet(plan, packet, repo, artifact_root)
    input_paths = {item.role: artifact_root / item.path for item in stage.inputs}
    input_paths["execution_packet_file"] = packet_path
    output_root = tmp_path / "resolved-cli-outputs"
    output_root.mkdir()
    output_paths = {item.role: output_root / Path(item.path).name for item in stage.outputs}
    resolved = worker._resolve_command(stage.commands[0], stage, input_paths, output_paths, {})
    observed: dict[str, object] = {}

    def fake_run(**kwargs: object) -> dict[str, object]:
        observed.update(kwargs)
        return {}

    monkeypatch.setattr(release_stage, "run_release_checks_stage_v2", fake_run)
    monkeypatch.chdir(repo)

    assert release_stage.main(list(resolved.argv[2:])) == 0
    assert observed["repository"] == repo


def test_identity_builder_failure_is_normalized_to_stable_release_reject(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    raw = {
        "identity_plan": handoff.canonical_json_bytes({}),
        "identity_observations": handoff.canonical_json_bytes({}),
        "identity_candidate_report": handoff.canonical_json_bytes({}),
    }

    def rejected_build(*_args: object, **_kwargs: object) -> dict[str, object]:
        raise release_stage.identity.RebuildPlanError("bad ancestry")

    monkeypatch.setattr(release_stage.identity, "build_plan", rejected_build)
    with pytest.raises(release_stage.RemoteReleaseChecksError) as rejected:
        release_stage._validate_identity_and_governance(
            REPO_ROOT,
            {"worker_commit": "a" * 40},
            {"expected_c0_commit": "1" * 40},
            raw,
        )
    assert rejected.value.code == "release_identity_plan_recomposition"


def test_end_to_end_adapter_writes_only_two_authority_false_outputs(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    repository = tmp_path / "repo"
    repository.mkdir()
    input_root = tmp_path / "inputs"
    input_root.mkdir()
    output_root = tmp_path / "outputs"
    output_root.mkdir()

    artifact_paths: dict[str, Path] = {}
    artifact_raw: dict[str, bytes] = {}
    for role in release_stage.RELEASE_CHECK_ARTIFACT_ROLES:
        raw = (
            handoff.canonical_json_bytes({})
            if role == "release_runtime_identity"
            else (f"artifact:{role}\n".encode("ascii"))
        )
        path = input_root / role
        path.write_bytes(raw)
        artifact_paths[role] = path
        artifact_raw[role] = raw

    plan = {"schema": "test-release-plan", "authority": release_stage.false_authority_v2()}
    plan_sha256 = release_stage.release.canonical_sha256(plan)
    expectation = {
        "schema": release_stage.EXPECTATION_SCHEMA_V1,
        "status": release_stage.EXPECTATION_STATUS_V1,
        "expected_plan_sha256": plan_sha256,
        "expected_c0_commit": "1" * 40,
        "expected_worker_commit": "a" * 40,
        "expected_runtime_identity_sha256": hashlib.sha256(
            artifact_raw["release_runtime_identity"]
        ).hexdigest(),
        "authority": release_stage.false_authority_v2(),
        "non_claims": list(release_stage.EXPECTATION_NON_CLAIMS_V1),
    }
    expectation_path = input_root / "release-plan-expectation.json"
    expectation_raw = handoff.canonical_json_bytes(expectation)
    expectation_path.write_bytes(expectation_raw)

    contracts = {str(row["role"]): row for row in handoff._artifact_contracts()}
    input_ids = []
    for role in release_stage.PACKET_INPUT_ROLES:
        raw = expectation_raw if role == "release_plan_expectation" else artifact_raw[role]
        record = handoff._artifact_record_from_bytes(
            contracts[role], cast(str, contracts[role]["path"]), raw
        )
        input_ids.append(cast(str, record["artifact_id"]))
    packet = _packet(input_ids)
    packet_path = input_root / "execution-packet.json"
    packet_path.write_bytes(handoff.canonical_json_bytes(packet))

    runtime_sha256 = hashlib.sha256(artifact_raw["release_runtime_identity"]).hexdigest()
    closure = _closure_evidence(plan_sha256, "a" * 40, runtime_sha256)
    fake_v7_report = {"v7_program_id": _sha("v7-program")}
    fake_mutation_report = {"report_id": _sha("mutation-report")}
    monkeypatch.setattr(
        release_stage.release_schema, "validate_runtime_identity", lambda value: value
    )
    monkeypatch.setattr(
        release_stage,
        "_validate_identity_and_governance",
        lambda *_args, **_kwargs: _identity_images(),
    )
    monkeypatch.setattr(release_stage, "_validate_v7_report", lambda _raw: fake_v7_report)
    monkeypatch.setattr(release_stage, "_validate_worker_build", lambda *_args: None)
    monkeypatch.setattr(
        release_stage,
        "_validate_mutation_report",
        lambda *_args: fake_mutation_report,
    )
    monkeypatch.setattr(release_stage.release, "build_release_closure_plan", lambda *_args: plan)
    monkeypatch.setattr(
        release_stage.release,
        "check_release_closure_plan",
        lambda *_args, **_kwargs: closure,
    )

    plan_out = output_root / "release-plan.json"
    evidence_out = output_root / "release-evidence.json"
    evidence = release_stage.run_release_checks_stage_v2(
        repository=repository,
        execution_packet_path=packet_path,
        expectation_path=expectation_path,
        artifact_paths=artifact_paths,
        release_plan_output=plan_out,
        release_evidence_output=evidence_out,
    )

    assert plan_out.read_bytes() == handoff.canonical_json_bytes(plan)
    assert release_stage.validate_release_evidence_v2(evidence_out.read_bytes()) == evidence
    assert all(value is False for value in cast(dict[str, bool], evidence["authority"]).values())
    assert set(output_root.iterdir()) == {plan_out, evidence_out}
