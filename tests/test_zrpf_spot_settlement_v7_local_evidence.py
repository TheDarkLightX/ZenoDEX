"""Authority-neutral evidence contracts for one bounded Spot V7 receipt."""

from __future__ import annotations

import copy
import hashlib
import json
import sys
from pathlib import Path
from types import FrameType

import pytest

from tools import build_zrpf_spot_settlement_v7_local_evidence as builder
from tools import check_zrpf_spot_settlement_v7_local_evidence as checker


def _golden_bytes(repo_root: Path) -> bytes:
    path = (
        repo_root / "zk/spot_settlement_v7_risc0/verifier/tests/vectors/"
        "spot_settlement_v7_firecracker_output_v1.hex"
    )
    compact = "".join(
        line for line in path.read_text(encoding="ascii").splitlines() if not line.startswith("//")
    )
    return bytes.fromhex(compact)


def _canonical_receipt(journal: bytes, *, seal_word: int, image_id: bytes) -> bytes:
    verifier_parameters = list(checker.RECEIPT_VERIFIER_PARAMETERS_WORDS_V1)
    image_words = [
        int.from_bytes(image_id[offset : offset + 4], "little") for offset in range(0, 32, 4)
    ]
    document = {
        "inner": {
            "Succinct": {
                "seal": [17, seal_word, 23],
                "control_id": list(checker.RECEIPT_CONTROL_ID_WORDS_V1),
                "claim": {"Value": {"pre": {"Value": {"merkle_root": image_words}}}},
                "hashfn": "poseidon2",
                "verifier_parameters": verifier_parameters,
                "control_inclusion_proof": [],
            }
        },
        "journal": {"bytes": list(journal)},
        "metadata": {"verifier_parameters": verifier_parameters},
    }
    return json.dumps(document, separators=(",", ":")).encode("utf-8")


def _replace_field(raw: bytearray, offset: int, index: int, value: bytes) -> None:
    assert len(value) == 32
    start = offset + index * 32
    raw[start : start + 32] = value


def _fixture_inputs(tmp_path: Path, repo_root: Path) -> dict[str, Path]:
    output = bytearray(_golden_bytes(repo_root))
    output_header = checker.V7_OUTPUT_HEADER_BYTES_V1
    journal = bytearray(output[output_header:])

    child_journal = b"exact-v6-child-journal-v1"
    certificate = b"full-blob-da-certificate-v1"
    replay = b"source-opened-spot-replay-v3"
    host_input = b"bounded-spot-state-root-host-input-v1"
    child_hash = hashlib.sha256(child_journal).digest()
    replay_hash = hashlib.sha256(replay).digest()
    host_hash = hashlib.sha256(host_input).digest()

    journal_fixed = checker.V7_JOURNAL_HEADER_BYTES_V1
    _replace_field(journal, journal_fixed, 3, child_hash)
    _replace_field(journal, journal_fixed, 6, replay_hash)
    _replace_field(journal, journal_fixed, 7, host_hash)
    journal[14:18] = len(host_input).to_bytes(4, "big")

    output_fixed = checker.V7_OUTPUT_FIXED_FIELDS_OFFSET_V1
    _replace_field(output, output_fixed, 3, hashlib.sha256(journal).digest())
    _replace_field(output, output_fixed, 7, child_hash)
    _replace_field(output, output_fixed, 18, host_hash)
    v7_program_id = bytes(output[output_fixed : output_fixed + 32])
    v6_child_program_id = bytes(output[output_fixed + 4 * 32 : output_fixed + 5 * 32])
    profile_id, _child_profile, manifest_root = checker.derive_protocol_identities_v1(
        v7_program_id=v7_program_id,
        v6_child_program_id=v6_child_program_id,
    )
    _replace_field(output, output_fixed, 1, profile_id)
    _replace_field(output, output_fixed, 2, manifest_root)
    output[22:26] = len(host_input).to_bytes(4, "big")
    output[output_header:] = journal

    plan_length = int.from_bytes(journal[22:26], "big")
    plan = bytes(journal[-plan_length:])
    guest_input = bytearray((1).to_bytes(2, "big"))
    for component in (child_journal, certificate, replay, host_input):
        guest_input.extend(len(component).to_bytes(4, "big"))
        guest_input.extend(component)

    v7_receipt = _canonical_receipt(
        bytes(journal),
        seal_word=19,
        image_id=v7_program_id,
    )
    mutation_document = json.loads(v7_receipt)
    mutation_document["inner"]["Succinct"]["seal"][1] ^= 1
    mutation = json.dumps(mutation_document, separators=(",", ":")).encode("utf-8")
    child_receipt = _canonical_receipt(
        child_journal,
        seal_word=29,
        image_id=v6_child_program_id,
    )

    raw_by_id = {
        "v7_receipt": v7_receipt,
        "v7_receipt_seal_mutation": mutation,
        "v6_child_receipt": child_receipt,
        "v7_guest_input": bytes(guest_input),
        "v7_journal": bytes(journal),
        "v7_verifier_output": bytes(output),
        "v7_plan_b": plan,
    }
    result: dict[str, Path] = {}
    for artifact_id, raw in raw_by_id.items():
        path = tmp_path / f"input-{artifact_id}.bin"
        path.write_bytes(raw)
        result[artifact_id] = path
    return result


def _build(tmp_path: Path, repo_root: Path) -> tuple[Path, Path, str]:
    result = builder.build_evidence(
        recorded_at="2026-07-13",
        artifact_paths=_fixture_inputs(tmp_path, repo_root),
        bundle_directory=tmp_path / "bundle",
        evidence_path=tmp_path / "evidence.json",
    )
    return result.evidence_path, result.bundle_directory, result.evidence_sha256


def _raw_inputs(tmp_path: Path, repo_root: Path) -> dict[str, bytes]:
    return {
        artifact_id: path.read_bytes()
        for artifact_id, path in _fixture_inputs(tmp_path, repo_root).items()
    }


def _trace_reject(artifacts: dict[str, bytes]) -> tuple[str, str]:
    lines: list[int] = []
    target = checker.__file__

    def trace(frame: FrameType, event: str, _arg):
        if event == "line" and frame.f_code.co_filename == target:
            lines.append(frame.f_lineno)
        return trace

    previous = sys.gettrace()
    sys.settrace(trace)
    try:
        with pytest.raises(checker.EvidenceError) as rejected:
            checker.analyze_artifacts_v1(artifacts)
    finally:
        sys.settrace(previous)
    path_id = hashlib.sha256(",".join(map(str, lines)).encode("ascii")).hexdigest()[:16]
    return str(rejected.value), path_id


def test_builder_assembles_and_self_checks_exact_authority_neutral_bundle(
    tmp_path: Path,
) -> None:
    repo_root = Path(__file__).resolve().parents[1]
    evidence_path, bundle, evidence_sha256 = _build(tmp_path, repo_root)

    report = checker.check_evidence(
        evidence_path,
        artifact_directory=bundle,
        expected_evidence_sha256=evidence_sha256,
    )

    assert report["ok"] is True
    assert report["artifacts_checked"] == 7
    assert report["receipt_journal_bindings_checked"] == 2
    assert report["receipt_image_bindings_checked"] == 2
    assert report["protocol_identity_derivations_checked"] == 3
    assert report["exact_seal_mutations_checked"] == 1
    assert report["guest_input_component_bindings_checked"] == 3
    assert report["verifier_output_journal_bindings_checked"] == 19
    assert report["plan_b_exact_bytes_checked"] is True
    assert report["receipt_seals_cryptographically_verified"] is False
    assert report["governed_source_build_verified"] is False
    assert report["firecracker_execution_verified"] is False
    assert report["release_authority"] is False
    assert report["settlement_authority"] is False
    assert report["production_authority"] is False


def test_da_certificate_bytes_are_retained_without_static_semantic_authority(
    tmp_path: Path,
) -> None:
    repo_root = Path(__file__).resolve().parents[1]
    seed = _raw_inputs(tmp_path, repo_root)
    guest = bytearray(seed["v7_guest_input"])
    cursor = 2
    child_length = int.from_bytes(guest[cursor : cursor + 4], "big")
    cursor += 4 + child_length
    certificate_length = int.from_bytes(guest[cursor : cursor + 4], "big")
    certificate_start = cursor + 4
    assert certificate_length > 0
    guest[certificate_start] ^= 1

    candidate = copy.deepcopy(seed)
    candidate["v7_guest_input"] = bytes(guest)
    original = checker.analyze_artifacts_v1(seed)
    mutated = checker.analyze_artifacts_v1(candidate)
    document = checker.compose_evidence_document_v1(
        recorded_at="2026-07-13", artifact_raw=candidate
    )

    assert (
        original.guest_input.data_availability_certificate
        != mutated.guest_input.data_availability_certificate
    )
    assert original.output == mutated.output
    assert (
        "data_availability_certificate_bytes_are_retained_without_static_semantic_decode"
        in document["nonclaims"]
    )
    assert not any("data_availability" in claim for claim in document["claims"])


@pytest.mark.parametrize(
    ("artifact_name", "mutation"),
    (
        ("spot-settlement-v7.receipt.json", lambda raw: raw + b"\n"),
        ("spot-settlement-v7.guest-input.bin", lambda raw: raw[:-1] + bytes([raw[-1] ^ 1])),
        ("spot-settlement-v7.journal.bin", lambda raw: raw[:-1] + bytes([raw[-1] ^ 1])),
        ("spot-settlement-v7.verifier-output.bin", lambda raw: raw[:40] + b"\x00" + raw[41:]),
        ("spot-settlement-v7.plan-b.bin", lambda raw: raw[:-1] + bytes([raw[-1] ^ 1])),
    ),
)
def test_checker_rejects_every_bound_artifact_mutation(
    tmp_path: Path,
    artifact_name: str,
    mutation,
) -> None:
    repo_root = Path(__file__).resolve().parents[1]
    evidence_path, bundle, evidence_sha256 = _build(tmp_path, repo_root)
    target = bundle / artifact_name
    target.write_bytes(mutation(target.read_bytes()))

    with pytest.raises(checker.EvidenceError):
        checker.check_evidence(
            evidence_path,
            artifact_directory=bundle,
            expected_evidence_sha256=evidence_sha256,
        )


def test_checker_rejects_non_exact_seal_mutation(tmp_path: Path) -> None:
    repo_root = Path(__file__).resolve().parents[1]
    evidence_path, bundle, evidence_sha256 = _build(tmp_path, repo_root)
    mutation_path = bundle / "spot-settlement-v7.seal-word-1-xor-lsb.receipt.json"
    document = json.loads(mutation_path.read_bytes())
    document["inner"]["Succinct"]["seal"][2] ^= 1
    mutation_path.write_bytes(json.dumps(document, separators=(",", ":")).encode())

    with pytest.raises(
        checker.EvidenceError,
        match="artifact SHA-256|exactly one word|non-seal receipt bytes",
    ):
        checker.check_evidence(
            evidence_path,
            artifact_directory=bundle,
            expected_evidence_sha256=evidence_sha256,
        )


def test_checker_rejects_claim_promotion_even_with_reanchored_bytes(tmp_path: Path) -> None:
    repo_root = Path(__file__).resolve().parents[1]
    evidence_path, bundle, _evidence_sha256 = _build(tmp_path, repo_root)
    document = json.loads(evidence_path.read_bytes())
    document["claims"]["settlement_authority"] = True
    promoted = checker.canonical_evidence_bytes(document)
    evidence_path.write_bytes(promoted)

    with pytest.raises(checker.EvidenceError, match="settlement_authority"):
        checker.check_evidence(
            evidence_path,
            artifact_directory=bundle,
            expected_evidence_sha256=hashlib.sha256(promoted).hexdigest(),
        )


def test_builder_rejects_unknown_input_and_existing_outputs(tmp_path: Path) -> None:
    repo_root = Path(__file__).resolve().parents[1]
    inputs = _fixture_inputs(tmp_path, repo_root)
    inputs["verified"] = tmp_path / "caller-boolean"
    inputs["verified"].write_text("true", encoding="ascii")

    with pytest.raises(builder.EvidenceBuildError, match="artifact input IDs"):
        builder.build_evidence(
            recorded_at="2026-07-13",
            artifact_paths=inputs,
            bundle_directory=tmp_path / "bundle",
            evidence_path=tmp_path / "evidence.json",
        )

    inputs.pop("verified")
    (tmp_path / "bundle").mkdir()
    with pytest.raises(builder.EvidenceBuildError, match="already exists"):
        builder.build_evidence(
            recorded_at="2026-07-13",
            artifact_paths=inputs,
            bundle_directory=tmp_path / "bundle",
            evidence_path=tmp_path / "evidence.json",
        )


def test_evidence_schema_rejects_unknown_claim_and_integer_boolean(tmp_path: Path) -> None:
    repo_root = Path(__file__).resolve().parents[1]
    evidence_path, bundle, _evidence_sha256 = _build(tmp_path, repo_root)
    for mutate in (
        lambda claims: claims.__setitem__("caller_verified", True),
        lambda claims: claims.__setitem__("release_authority", 0),
    ):
        document = copy.deepcopy(json.loads(evidence_path.read_bytes()))
        mutate(document["claims"])
        raw = checker.canonical_evidence_bytes(document)
        evidence_path.write_bytes(raw)
        with pytest.raises(checker.EvidenceError):
            checker.check_evidence(
                evidence_path,
                artifact_directory=bundle,
                expected_evidence_sha256=hashlib.sha256(raw).hexdigest(),
            )


def test_boundary_atlas_reaches_distinct_deep_cross_field_rejects(tmp_path: Path) -> None:
    repo_root = Path(__file__).resolve().parents[1]
    seed = _raw_inputs(tmp_path, repo_root)
    cases: dict[str, dict[str, bytes]] = {}

    receipt_image = copy.deepcopy(seed)
    receipt = json.loads(receipt_image["v7_receipt"])
    receipt["inner"]["Succinct"]["claim"]["Value"]["pre"]["Value"]["merkle_root"][0] ^= 1
    receipt_image["v7_receipt"] = json.dumps(receipt, separators=(",", ":")).encode()
    receipt = json.loads(receipt_image["v7_receipt_seal_mutation"])
    receipt["inner"]["Succinct"]["claim"]["Value"]["pre"]["Value"]["merkle_root"][0] ^= 1
    receipt_image["v7_receipt_seal_mutation"] = json.dumps(receipt, separators=(",", ":")).encode()
    cases["receipt_image"] = receipt_image

    for name, field_index in (("profile", 1), ("manifest", 2)):
        candidate = copy.deepcopy(seed)
        output = bytearray(candidate["v7_verifier_output"])
        output[checker.V7_OUTPUT_FIXED_FIELDS_OFFSET_V1 + field_index * 32] ^= 1
        candidate["v7_verifier_output"] = bytes(output)
        cases[name] = candidate

    mutation = copy.deepcopy(seed)
    receipt = json.loads(mutation["v7_receipt_seal_mutation"])
    receipt["inner"]["Succinct"]["seal"][2] ^= 1
    mutation["v7_receipt_seal_mutation"] = json.dumps(receipt, separators=(",", ":")).encode()
    cases["non_seal_mutation"] = mutation

    guest_components = {
        "child": 2 + 4,
        "replay": None,
        "host": None,
    }
    guest = seed["v7_guest_input"]
    cursor = 2
    starts: list[int] = []
    for _ in range(4):
        length = int.from_bytes(guest[cursor : cursor + 4], "big")
        cursor += 4
        starts.append(cursor)
        cursor += length
    guest_components["replay"] = starts[2]
    guest_components["host"] = starts[3]
    for name, offset in guest_components.items():
        candidate = copy.deepcopy(seed)
        guest_mutation = bytearray(candidate["v7_guest_input"])
        assert offset is not None
        guest_mutation[offset] ^= 1
        candidate["v7_guest_input"] = bytes(guest_mutation)
        cases[f"guest_{name}"] = candidate

    plan = copy.deepcopy(seed)
    plan_bytes = bytearray(plan["v7_plan_b"])
    plan_bytes[-1] ^= 1
    plan["v7_plan_b"] = bytes(plan_bytes)
    cases["plan"] = plan

    outcomes = {_trace_reject(candidate) for candidate in cases.values()}
    messages = {message for message, _path_id in outcomes}
    assert len(outcomes) >= 8
    assert {
        "V7 receipt image ID mismatch",
        "V7 profile ID mismatch",
        "V7 program manifest root mismatch",
        "seal mutation changes non-seal receipt bytes",
        "V6 child guest-input journal mismatch",
        "source replay SHA-256 mismatch",
        "state-root host input SHA-256 mismatch",
        "exact Plan B mismatch",
    } <= messages
