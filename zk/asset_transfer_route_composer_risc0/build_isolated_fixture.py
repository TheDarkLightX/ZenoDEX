"""Build research-only common-profile proof inputs from measured test artifacts.

The retained release/status labels are fixture assumptions. This program does
not establish signer legitimacy, genesis allocation ownership, or publication.
"""

from __future__ import annotations

import dataclasses
import hashlib
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from check_reference import profile as decode_profile
from check_reference import record

from src.core import global_settlement_types_v1 as abi
from src.core.economic_initial_state_atom_coverage_v1 import (
    EconomicInitialStateAtomClassificationV1 as Classification,
)
from src.core.economic_initial_state_atom_coverage_v1 import (
    EconomicInitialStateAtomSourceV1 as Source,
)
from src.core.economic_initial_state_atom_coverage_v1 import (
    EconomicInitialStateKindV1 as Kind,
)
from src.core.economic_initial_state_atom_coverage_v1 import (
    EconomicInitialStateSourceManifestV1 as SourceManifest,
)
from src.core.economic_initial_state_atom_coverage_v1 import (
    derive_economic_initial_state_atom_occurrences_v1,
    economic_initial_state_atom_coverage_policy_binding_v1,
)
from src.core.economic_initial_state_outbox_continuity_v1 import (
    derive_economic_initial_state_outbox_continuity_root_v1 as outbox_root,
)
from src.core.economic_initial_state_replay_continuity_v1 import (
    derive_economic_initial_state_replay_continuity_root_v1 as replay_root,
)
from src.core.economic_initial_state_terminal_continuity_v1 import (
    derive_economic_initial_state_terminal_continuity_root_v1 as terminal_root,
)
from src.core.economic_receipt_verifier_evidence_v1 import (
    EconomicReceiptVerifierEvidenceArtifactV1 as Evidence,
)
from src.core.economic_receipt_verifier_evidence_v1 import (
    EconomicReceiptVerifierEvidenceManifestV1 as EvidenceManifest,
)
from src.core.economic_receipt_verifier_evidence_v1 import (
    economic_receipt_verifier_backend_protocol_root_v1,
    economic_receipt_verifier_implementation_root_v1,
)
from src.core.economic_receipt_verifier_registry_v1 import (
    MAX_ECONOMIC_RECEIPT_BYTES_V1,
)
from src.core.economic_receipt_verifier_registry_v1 import (
    EconomicReceiptVerifierEvidenceStatusV1 as EvidenceStatus,
)
from src.core.economic_receipt_verifier_registry_v1 import (
    EconomicReceiptVerifierRegistryV1 as VerifierRegistry,
)
from src.core.economic_receipt_verifier_registry_v1 import (
    EconomicReceiptVerifierReleaseV1 as VerifierRelease,
)
from src.core.global_economic_asset_precision_policy_v1 import m6_asset_precision_policy_binding_v1
from src.core.global_economic_capability_profile_binding_v1 import m6_capability_policy_binding_v1
from src.core.global_economic_proof_v1 import EconomicCommandOccurrenceV1, RouteCompositionJournalV1
from src.core.global_economic_state_decoder_v1 import decode_global_economic_state_v1
from src.core.route_composition_receipt_verification_v1 import (
    derive_route_composition_assumption_root_v1,
)
from src.integration.isolated_economic_verifier_set_v1 import (
    IsolatedVerifierArtifactV1,
    bind_isolated_economic_verifier_set_v1,
    read_isolated_verifier_artifact_set_v1,
)


def canonical(value):
    return abi.canonical_global_bytes_v1(value)


def write(path, value):
    path.write_bytes(canonical(value))


def rebind_profile(value, registry, source_manifest):
    bindings = [
        record(abi.EconomicPolicyBindingV1, row) for row in value["policy_registry"]["bindings"]
    ]
    bindings += [
        m6_asset_precision_policy_binding_v1(),
        m6_capability_policy_binding_v1(),
        economic_initial_state_atom_coverage_policy_binding_v1(source_manifest),
    ]
    policies = abi.EconomicPolicyRegistryV1(
        tuple(sorted(bindings, key=lambda row: (row.policy_kind, row.command_kind)))
    )
    prior = decode_profile(value)
    fields = {
        f.name: getattr(prior, f.name) for f in dataclasses.fields(prior) if f.name != "profile_id"
    }
    fields.update(
        verifier_registry_root=registry.registry_root, policy_registry_root=policies.registry_root
    )
    selected = abi.EconomicProfileSnapshotV1.build(**fields)
    value["profile"] = json.loads(canonical(selected))
    value["policy_registry"] = json.loads(canonical(policies))
    for name in ("pre_state", "post_state"):
        value[name]["profile_root"] = selected.profile_id
    pre = decode_global_economic_state_v1(value["pre_state"])
    value["occurrence"]["profile_root"] = selected.profile_id
    value["occurrence"]["pre_state_root"] = pre.state_root
    occurrence = record(EconomicCommandOccurrenceV1, value["occurrence"])
    for context in (
        value["lane_input"]["module_input"]["context"],
        value["lane_input"]["coordinator_context"],
    ):
        context.update(
            profile_root=selected.profile_id, command_occurrence_id=occurrence.occurrence_id
        )
    value["post_state"]["replay_state"] = [
        {"replay_id": occurrence.replay_id, "occurrence_id": occurrence.occurrence_id}
    ]
    decode_global_economic_state_v1(value["post_state"])
    return selected, policies, pre


def verifier_registry(meta, root_image):
    artifacts = tuple(
        IsolatedVerifierArtifactV1(**row)
        for row in sorted(meta["artifacts"], key=lambda row: row["image_id"])
    )
    material = read_isolated_verifier_artifact_set_v1(artifacts)
    evidence = tuple(
        Evidence(EvidenceStatus(name), root)
        for name, root in sorted(meta["evidence_roots"].items())
    )
    manifest = EvidenceManifest(
        proof_system="RISC0_ZKVM_3_0_6",
        implementation_root=economic_receipt_verifier_implementation_root_v1(material),
        receipt_schema_root=meta["receipt_schema_root"],
        journal_schema_root=meta["journal_schema_root"],
        root_image_id=root_image,
        specification_root=meta["specification_root"],
        source_root=meta["source_root"],
        toolchain_root=meta["toolchain_root"],
        backend_protocol_root=economic_receipt_verifier_backend_protocol_root_v1(),
        max_receipt_bytes=MAX_ECONOMIC_RECEIPT_BYTES_V1,
        max_journal_bytes=abi.MAX_JOURNAL_BYTES_V1,
        evidence_artifacts=evidence,
    )
    release_fields = {
        f.name: getattr(manifest, f.name)
        for f in dataclasses.fields(manifest)
        if f.name != "evidence_artifacts"
    }
    release = VerifierRelease.build(
        **release_fields,
        semantic_version="3.0.6-isolated-common.1",
        evidence_manifest_root=manifest.manifest_root,
        status=abi.ReleaseStatusV1.SHADOW,
        accepts_new_receipts=False,
        evidence_statuses=tuple(row.status for row in evidence),
    )
    registry = VerifierRegistry((release,))
    return artifacts, manifest, registry, release


def genesis_source(value):
    pre = decode_global_economic_state_v1(value["pre_state"])
    if pre.height != 0 or value["post_state"]["height"] != 1:
        raise ValueError("isolated genesis must be height zero and transfer height one")
    assumption = {
        "schema": "zenodex/isolated-genesis-assumption/v1",
        "source_authorization_verified": False,
        "state": pre.to_canonical(),
    }
    authorization_root = abi.hash_global_v1("isolated-genesis-assumption-v1", assumption)
    source_manifest = SourceManifest(
        Kind.GENESIS,
        tuple(
            Source(row, Classification.GENESIS_ALLOCATION, authorization_root)
            for row in derive_economic_initial_state_atom_occurrences_v1(pre)
        ),
    )
    return assumption, source_manifest


def initial_input(selected, policies, pre, source_manifest, meta):
    statement = dict(
        schema=abi.GLOBAL_SETTLEMENT_ABI_V1,
        kind=Kind.GENESIS,
        chain_id=pre.chain_id,
        deployment_root=pre.deployment_root,
        profile_root=selected.profile_id,
        writer_epoch=pre.writer_epoch,
        height=0,
        state_root=pre.state_root,
        source_profile_root=abi.ZERO_ROOT_V1,
        source_state_root=abi.ZERO_ROOT_V1,
        source_writer_epoch=0,
        source_height=0,
        state_atom_coverage_root=source_manifest.manifest_root,
        lane_object_coverage_root=abi.hash_global_v1(
            "isolated-initial-lane-disclosure-v1", {"lane_roots": pre.lane_roots}
        ),
        replay_continuity_root=replay_root(Kind.GENESIS, pre, None),
        terminal_continuity_root=terminal_root(Kind.GENESIS, pre, None),
        outbox_continuity_root=outbox_root(Kind.GENESIS, pre, None),
        source_manifest_root=meta["source_root"],
        toolchain_manifest_root=meta["toolchain_root"],
        root_image_id=selected.root_image_id,
    )
    initial = dict(
        schema="zenodex/economic-initial-state-guest-input/v1",
        profile=selected,
        policy_registry=policies,
        state=pre,
        predecessor_state=None,
        source_manifest=source_manifest,
        statement=statement,
    )
    return initial


def write_fixture(output, value, initial, manifest, registry, meta, assumption, selected, pre):
    output.mkdir(exist_ok=False)
    for name, obj in [
        ("route.input.json", value),
        ("initial.input.json", initial),
        ("verifier-manifest.json", manifest.to_canonical()),
        ("verifier-registry.json", registry.to_canonical()),
        ("metadata.json", meta),
        ("genesis-assumption.json", assumption),
    ]:
        write(output / name, obj)
    write(output / "empty-receipts.json", [])
    write(
        output / "fixture-subject.json",
        dict(
            profile_id=selected.profile_id,
            pre_state_root=pre.state_root,
            implementation_root=manifest.implementation_root,
            verifier_registry_root=registry.registry_root,
            signature_authority_verified=False,
            genesis_allocation_authority_verified=False,
            fixture_release_evidence_labels_are_assumptions=True,
            publication_qualified=False,
            production_authority=False,
        ),
    )
    print((output / "fixture-subject.json").read_text())


def build(route_path, metadata_path, output):
    value = json.loads(route_path.read_bytes())
    meta = json.loads(metadata_path.read_bytes())
    artifacts, manifest, registry, release = verifier_registry(
        meta, value["profile"]["root_image_id"]
    )
    assumption, source_manifest = genesis_source(value)
    selected, policies, pre = rebind_profile(value, registry, source_manifest)
    bound = bind_isolated_economic_verifier_set_v1(
        profile=selected,
        verifier_registry=registry,
        evidence_manifest=manifest,
        artifacts=artifacts,
        deployment_root=pre.deployment_root,
        timeout_ms=30000,
    )
    if bound.release_id != release.release_id:
        raise ValueError("measured verifier set binding changed release")
    initial = initial_input(selected, policies, pre, source_manifest, meta)
    write_fixture(output, value, initial, manifest, registry, meta, assumption, selected, pre)


def epoch(route_input_path, route_journal_path, metadata_path, output):
    value = json.loads(route_input_path.read_bytes())
    meta = json.loads(metadata_path.read_bytes())
    raw = route_journal_path.read_bytes()
    journal = record(RouteCompositionJournalV1, json.loads(raw))
    if raw != canonical(journal):
        raise ValueError("route journal is not canonical")
    image = value["routes"]["routes"][0]["guest_image_id"]
    assumption = derive_route_composition_assumption_root_v1(
        profile_id=journal.profile_root,
        route_release_id=journal.route_release_id,
        command_occurrence_id=journal.command_occurrence_id,
        writer_epoch=journal.writer_epoch,
        route_journal_root=journal.journal_root,
        route_journal_digest="0x" + hashlib.sha256(raw).hexdigest(),
        expected_image_id=image,
    )
    occurrence = record(EconomicCommandOccurrenceV1, value["occurrence"])
    if journal.command_occurrence_id != occurrence.occurrence_id:
        raise ValueError("route occurrence mismatch")
    statement = dict(
        schema=abi.GLOBAL_SETTLEMENT_ABI_V1,
        chain_id=journal.chain_id,
        deployment_root=journal.deployment_root,
        profile_root=journal.profile_root,
        writer_epoch=journal.writer_epoch,
        height=1,
        pre_state_root=journal.pre_state_root,
        post_state_root=journal.post_state_root,
        ordered_occurrence_ids=[occurrence.occurrence_id],
        ordered_route_journal_roots=[journal.journal_root],
        ordered_route_assumption_roots=[assumption],
        module_leaf_occurrences=1,
        aggregation_fanout=8,
        aggregation_levels=0,
        effect_plan_root=journal.effect_plan_root,
        terminal_obligations_root=journal.terminal_obligations_root,
        body_commitment=occurrence.command_body_hash,
        data_availability_root=meta["source_root"],
        finality_root=abi.hash_global_v1(
            "isolated-finality-assumption-v1", {"external_finality_verified": False}
        ),
        source_manifest_root=meta["source_root"],
        toolchain_manifest_root=meta["toolchain_root"],
        root_image_id=value["profile"]["root_image_id"],
    )
    words = [int.from_bytes(bytes.fromhex(image[2:])[i : i + 4], "little") for i in range(0, 32, 4)]
    write(
        output,
        {
            "DirectEpoch": {
                "certificate_journal_bytes": list(canonical(statement)),
                "route_receipts": [{"image_id": words, "journal_bytes": list(raw)}],
            }
        },
    )


if __name__ == "__main__":
    if sys.argv[1] == "build":
        build(*(Path(p) for p in sys.argv[2:]))
    elif sys.argv[1] == "epoch":
        epoch(*(Path(p) for p in sys.argv[2:]))
    else:
        raise SystemExit("expected build or epoch")
