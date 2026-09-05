"""Actual BLS, retained economic seed, and evidence-preimage preparation checks.

No RISC0 replies are fabricated: this suite prepares inputs and predicted
journals only. Existing receipt/publication gates still need genuine receipts.
"""

from __future__ import annotations

import copy
import dataclasses
import hashlib
import json
from pathlib import Path

import pytest
from py_ecc.bls import G2Basic

from src.core import global_settlement_types_v1 as abi
from src.core.global_economic_state_decoder_v1 import decode_global_economic_state_v1
from tools import isolated_bls_evidence_v1 as evidence
from tools import isolated_bls_proof_inputs_v1 as inputs
from tools import prepare_isolated_bls_proof_v1 as builder

REPO = Path(__file__).resolve().parents[1]


@pytest.fixture(scope="module")
def prepared(tmp_path_factory):
    directory = tmp_path_factory.mktemp("bls-preparation") / "evidence"
    evidence.acquire_evidence(REPO, directory)
    seed = (REPO / builder.SEED_FILE).read_bytes()
    return builder.prepare(seed, directory), directory


def test_given_actual_artifacts_when_preparing_then_signature_and_amounts_are_independently_correct(
    prepared,
):
    payloads, _ = prepared
    authorization = json.loads(payloads["authorization-registry.json"])["authorizations"][0]
    key = bytes.fromhex(authorization["signer_public_key"][2:])
    assert G2Basic.Verify(key, payloads["signing-message.bin"], payloads["signature.bin"])
    assert not G2Basic.Verify(
        key, hashlib.sha256(payloads["signing-message.bin"]).digest(), payloads["signature.bin"]
    )
    value = json.loads(payloads["route.input.json"])
    pre = {row["owner"]: row["amount_atoms"] for row in value["pre_state"]["balances"]}
    post = {row["owner"]: row["amount_atoms"] for row in value["post_state"]["balances"]}
    assert pre == {"alice": 100, "bob": 10, "treasury": 5}
    assert post == {"alice": 68, "bob": 40, "treasury": 7}
    assert sum(pre.values()) == sum(post.values()) == 115
    assert authorization["route_release_id"] == value["occurrence"]["route_release_id"]


def test_shadow_floor_and_rebuilt_policy_have_no_production_evidence(prepared):
    payloads, _ = prepared
    release = json.loads(payloads["signature-registry.json"])["releases"][0]
    assert release["status"] == "SHADOW"
    assert release["accepts_new_authentications"] is False
    assert set(release["evidence_statuses"]) == {
        "SPECIFIED",
        "IMPLEMENTED",
        "TESTED",
        "SOURCE_PINNED",
        "TOOLCHAIN_PINNED",
    }
    subject = json.loads(payloads["subject.json"])
    assert subject["selection_purpose"] == "ISOLATED_QUALIFICATION"
    assert subject["genuine_signature_verified_locally"] is True
    assert subject["production_authority"] is subject["new_receipts_generated"] is False
    assert subject["genesis_ownership_verified"] is False
    assert subject["external_data_availability_verified"] is False
    assert subject["external_finality_verified"] is False
    assert (
        subject["profile_id"]
        != "0xe7faba74392ffa74dc799037c0c4b7844abbda7224a28d562381be2ea051f993"
    )


def test_genesis_allocation_assumption_has_no_profile_or_full_state_hash_cycle(prepared):
    payloads, _ = prepared
    value = json.loads(payloads["route.input.json"])
    pre = decode_global_economic_state_v1(value["pre_state"])
    assumption, sources = builder.genesis_source(pre)
    changed = dataclasses.replace(pre, profile_root="0x" + "ab" * 32)
    changed_assumption, changed_sources = builder.genesis_source(changed)
    assert abi.canonical_global_bytes_v1(assumption) == abi.canonical_global_bytes_v1(
        changed_assumption
    )
    assert sources.manifest_root == changed_sources.manifest_root
    assert "profile_root" not in assumption and "state" not in assumption
    initial = json.loads(payloads["initial.input.json"])
    assert initial["statement"]["state_root"] == pre.state_root
    assert initial["statement"]["profile_root"] == pre.profile_root


def test_epoch_consumes_exact_predicted_route_journal_and_little_endian_image(prepared):
    payloads, _ = prepared
    direct = json.loads(payloads["epoch.input.json"])["DirectEpoch"]
    assert bytes(direct["route_receipts"][0]["journal_bytes"]) == payloads["expected-route.journal"]
    words = direct["route_receipts"][0]["image_id"]
    assert (
        b"".join(word.to_bytes(4, "little") for word in words).hex()
        == builder.GUESTS["route"][0][2:]
    )
    statement = json.loads(bytes(direct["certificate_journal_bytes"]))
    journal = json.loads(payloads["expected-route.journal"])
    assert statement["pre_state_root"] == journal["pre_state_root"]
    assert statement["post_state_root"] == journal["post_state_root"]


def test_preparation_is_exactly_replayable_from_frozen_evidence(prepared):
    payloads, directory = prepared
    assert builder.prepare((REPO / builder.SEED_FILE).read_bytes(), directory) == payloads


def test_seed_policy_or_unknown_field_drift_rejects_before_evidence_access(tmp_path):
    raw = (REPO / builder.SEED_FILE).read_bytes()
    for changed in (raw + b"\n", raw.replace(b'"amount_atoms":30', b'"amount_atoms":31')):
        assert changed != raw
        with pytest.raises(ValueError, match="compatibility seed hash drift"):
            builder.prepare(changed, tmp_path / "does-not-exist")


def test_source_evidence_drift_is_observable_without_crypto_or_publication(tmp_path):
    source = tmp_path / "source.py"
    source.write_bytes(b"exact source")
    directory = tmp_path / "snapshot"
    manifest = evidence.snapshot_files({"source.py": source}, directory)
    evidence.verify_snapshot(manifest, directory)
    (directory / "source.py").write_bytes(b"altered source")
    with pytest.raises(ValueError, match="content drift"):
        evidence.verify_snapshot(manifest, directory)


def test_added_current_source_file_rejects_frozen_subject(prepared, monkeypatch):
    _, directory = prepared
    _, objects = evidence.load_evidence(directory)
    original = evidence._source_files
    monkeypatch.setattr(
        evidence,
        "_source_files",
        lambda root: original(root) | {"src/new_writer.py": root / "src/new_writer.py"},
    )
    with pytest.raises(ValueError, match="source inventory drift"):
        evidence.require_current_evidence(REPO, objects)


def test_current_dependency_file_mutation_rejects_frozen_subject(prepared, monkeypatch, tmp_path):
    _, directory = prepared
    _, objects = evidence.load_evidence(directory)
    distributions, files = evidence._installed_closure()
    name = sorted(files)[0]
    altered = tmp_path / "altered.py"
    altered.write_bytes(b"altered installed dependency")
    monkeypatch.setattr(
        evidence, "_installed_closure", lambda: (distributions, files | {name: altered})
    )
    with pytest.raises(ValueError, match="runtime content drift"):
        evidence.require_current_evidence(REPO, objects)


def test_conserved_misattribution_fails_existing_economic_relation(prepared):
    payloads, _ = prepared
    value = json.loads(payloads["route.input.json"])
    selected = inputs.decode_profile(value)
    policies = abi.EconomicPolicyRegistryV1(
        tuple(
            builder.record(abi.EconomicPolicyBindingV1, row)
            for row in value["policy_registry"]["bindings"]
        )
    )
    occurrence = builder.record(builder.proof.EconomicCommandOccurrenceV1, value["occurrence"])
    changed = copy.deepcopy(value)
    changed["post_state"]["balances"][0]["amount_atoms"] += 1
    changed["post_state"]["balances"][1]["amount_atoms"] -= 1
    with pytest.raises(ValueError, match="GLOBAL_PROJECTION_ROWS_DRIFT"):
        builder.economic_preflight(changed, selected, policies, occurrence)


def test_source_changes_during_preflight_are_refused_before_payload_return(prepared, monkeypatch):
    _, directory = prepared
    checks = 0
    original = builder.require_current_evidence

    def change_after_preflight(repo, objects):
        nonlocal checks
        checks += 1
        if checks == 2:
            raise ValueError("injected source drift during preparation")
        return original(repo, objects)

    monkeypatch.setattr(builder, "require_current_evidence", change_after_preflight)
    with pytest.raises(ValueError, match="source drift during preparation"):
        builder.prepare((REPO / builder.SEED_FILE).read_bytes(), directory)
    assert checks == 2


def test_retained_image_set_mismatch_rejects_before_acquisition(tmp_path):
    path = tmp_path / "metadata.json"
    path.write_bytes(evidence.canonical({"artifacts": []}))
    with pytest.raises(ValueError, match="image set drift"):
        builder.retain_verifiers(path)


def test_retained_binary_drift_rejects_without_executing_it(tmp_path):
    artifact = tmp_path / "foreign-binary"
    artifact.write_bytes(b"not a verifier")
    metadata = {
        "artifacts": [
            {"image_id": row[0], "executable_path": str(artifact)}
            for row in builder.GUESTS.values()
        ]
    }
    path = tmp_path / "metadata.json"
    path.write_bytes(evidence.canonical(metadata))
    with pytest.raises(ValueError, match="artifact drift"):
        builder.retain_verifiers(path)


@pytest.mark.parametrize("name", ("../escape.py", "/absolute.py", "a/../escape.py"))
def test_snapshot_member_escape_is_rejected(tmp_path, name):
    source = tmp_path / "source.py"
    source.write_bytes(b"source")
    with pytest.raises(ValueError, match="member path"):
        evidence.snapshot_files({name: source}, tmp_path / "output")


def test_symlink_artifact_and_oversize_input_reject(tmp_path):
    source = tmp_path / "source.py"
    source.write_bytes(b"source")
    link = tmp_path / "link"
    link.symlink_to(source)
    with pytest.raises(OSError):
        evidence.read_regular(link)
    with pytest.raises(ValueError, match="type or size"):
        evidence.read_regular(source, maximum=1)


@pytest.mark.parametrize("raw", (b"[]", b'{"field":1,"field":2}'))
def test_ambiguous_or_non_object_evidence_json_rejects(raw):
    with pytest.raises(ValueError):
        evidence.closed_json(raw)


def test_output_replay_never_overwrites_existing_bundle(prepared, tmp_path):
    payloads, _ = prepared
    output = tmp_path / "prepared"
    builder.write_bundle(output, payloads)
    before = {p.name: p.read_bytes() for p in output.iterdir()}
    with pytest.raises(FileExistsError):
        builder.write_bundle(output, payloads)
    assert {p.name: p.read_bytes() for p in output.iterdir()} == before
