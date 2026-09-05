"""Prepare one genuinely signed isolated transfer for retained RISC0 guests.

This tool preserves the public compatibility seed's economic policy, releases
and four images. It acquires evidence, changes the isolated signing policy,
derives all dependent roots, and writes inputs without proving or publishing.
The fixed scalar is public test data, never a live signing key.
"""

from __future__ import annotations

import argparse
import dataclasses
import sys
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from py_ecc.bls import G2Basic

from src.core import global_economic_proof_v1 as proof
from src.core import global_settlement_types_v1 as abi
from src.core.economic_command_authentication_types_v1 import (
    EconomicCommandAuthenticationCandidateV1 as AuthenticationCandidate,
)
from src.core.economic_command_authentication_types_v1 import (
    EconomicCommandAuthenticationEnvelopeV1 as Envelope,
)
from src.core.economic_command_authentication_types_v1 import (
    EconomicCommandIntentV1 as Intent,
)
from src.core.economic_command_authentication_v1 import (
    _authenticate_isolated_economic_command_intent_v1,
    _isolated_economic_command_authentication_message_bytes_v1,
    bind_authenticated_intent_to_occurrence_v1,
)
from src.core.economic_command_authorization_registry_v1 import (
    EconomicCommandAuthorizationRegistryV1 as AuthorizationRegistry,
)
from src.core.economic_command_authorization_registry_v1 import (
    EconomicCommandAuthorizationV1 as Authorization,
)
from src.core.economic_command_signature_verifier_deployment_v1 import (
    CommandSignatureVerifierEvidenceArtifactV1 as Evidence,
)
from src.core.economic_command_signature_verifier_deployment_v1 import (
    EconomicCommandSignatureVerifierEvidenceManifestV1 as EvidenceManifest,
)
from src.core.economic_command_signature_verifier_deployment_v1 import (
    command_signature_verifier_backend_protocol_root_v1,
    command_signature_verifier_implementation_root_v1,
)
from src.core.economic_command_signature_verifier_registry_v1 import (
    CommandSignatureVerifierEvidenceStatusV1 as EvidenceStatus,
)
from src.core.economic_command_signature_verifier_registry_v1 import (
    EconomicCommandSignatureVerifierRegistryV1 as SignatureRegistry,
)
from src.core.economic_command_signature_verifier_registry_v1 import (
    EconomicCommandSignatureVerifierReleaseV1 as SignatureRelease,
)
from src.core.economic_command_signature_verifier_registry_v1 import (
    EconomicCommandSignatureVerifierSelectionPurposeV1 as Purpose,
)
from src.core.global_economic_state_decoder_v1 import decode_global_economic_state_v1
from src.integration.economic_command_bls_signature_verifier_v1 import (
    BLS_ECONOMIC_COMMAND_SIGNATURE_ALGORITHM_V1 as ALGORITHM,
)
from src.integration.economic_command_bls_signature_verifier_v1 import (
    bind_deployed_bls_economic_command_signature_verifier_v1,
)
from tools.isolated_bls_evidence_v1 import (
    ARTIFACT,
    PUBLIC_TEST_SCALAR,
    acquire_evidence,
    canonical,
    closed_json,
    load_evidence,
    read_regular,
    require_current_evidence,
    sha256,
)
from tools.isolated_bls_proof_inputs_v1 import (
    economic_preflight,
    epoch_input,
    genesis_source,
    initial_input,
    rebind,
)
from zk.asset_transfer_route_composer_risc0.check_reference import record

SEED_SHA256 = "e6d7cb2a1b19e3e9f40fef98b85b168ad04c4cfb4d4b443b13fa08ef676d6ee6"
SEED_FILE = "tests/data/isolated_bls_proof_seed_v1.json"
GUESTS = {
    "module": (
        "0x5edda34871caacef5194017f61ade9cdfa8c8aeee0e14907824945e58452fc38",
        "04785a1f721a077ba2012a41c6b9b102e997bcb639c596c4230cf114ec5e0297",
    ),
    "coordinator": (
        "0xa96363692e6397a9eaf92e768a324181077af14e3f3c7b1f7f02741e0eab86c0",
        "34d0c733f2a21a015ecb5ac992e22a7bed29786cac9a2f8e221d1ed33fb9b08d",
    ),
    "route": (
        "0xfcb2e9e1e032508d3df0899eded32598596bd53621e25d56115700fe0cc12d93",
        "f982ad0bd804db85c80592537bcb0881238f3b0bb22be366b401aaa05261f615",
    ),
    "root": (
        "0x587c1a7c9c65a98c2d1a76552324f9dcdf2486d88972a6a79d0889ffb5af173b",
        "6bfd498ad314d82cd2381efa76d97c376d8e643918d41e74e350986d672c6adb",
    ),
}


def signature_release(roots: dict, artifact: bytes):
    contracts = {
        "public_key_schema_root": {"encoding": "lowercase-0x-compressed-G1", "bytes": 48},
        "signature_schema_root": {"encoding": "compressed-G2", "bytes": 96},
        "message_schema_root": {
            "domain": "economic-command-intent-authentication-message-v1",
            "additional_prehash": False,
        },
    }
    evidence = {
        "SPECIFIED": roots["contract.json"],
        "IMPLEMENTED": roots["implementation.json"],
        "TESTED": roots["bls-controls.json"],
        "SOURCE_PINNED": roots["source-manifest.json"],
        "TOOLCHAIN_PINNED": roots["runtime-manifest.json"],
    }
    manifest = EvidenceManifest(
        signature_algorithm=ALGORITHM,
        implementation_root=command_signature_verifier_implementation_root_v1(artifact),
        **{key: "0x" + sha256(canonical(value)) for key, value in contracts.items()},
        specification_root=roots["contract.json"],
        source_root=roots["source-manifest.json"],
        toolchain_root=roots["runtime-manifest.json"],
        backend_protocol_root=command_signature_verifier_backend_protocol_root_v1(),
        max_public_key_bytes=98,
        max_signature_bytes=96,
        evidence_artifacts=tuple(
            Evidence(EvidenceStatus(key), value) for key, value in sorted(evidence.items())
        ),
    )
    fields = {
        f.name: getattr(manifest, f.name)
        for f in dataclasses.fields(manifest)
        if f.name not in ("evidence_artifacts", "backend_protocol_root")
    }
    release = SignatureRelease.build(
        **fields,
        semantic_version="8.0.0-isolated-bls.1",
        evidence_manifest_root=manifest.manifest_root,
        evidence_statuses=tuple(row.status for row in manifest.evidence_artifacts),
        status=abi.ReleaseStatusV1.SHADOW,
        accepts_new_authentications=False,
    )
    return manifest, release, contracts


def authenticate(selected, policies, signatures, authorizations, occurrence, module, evidence_dir):
    row = authorizations.authorizations[0]
    intent = Intent(
        occurrence.chain_id,
        occurrence.deployment_root,
        selected.profile_id,
        occurrence.command_kind,
        occurrence.command_body_hash,
        occurrence.route_release_id,
        occurrence.subject_id,
        occurrence.grant_root,
        occurrence.nonce,
        occurrence.consumed_object_ids,
        1,
        1,
    )
    envelope = Envelope(
        abi.canonical_economic_command_body_bytes_v1(occurrence.command_kind, module.command),
        row.signer_key_id,
        row.signer_public_key,
        ALGORITHM,
        bytes(96),
    )
    candidate = AuthenticationCandidate(
        selected, policies, authorizations, signatures, intent, envelope
    )
    message = _isolated_economic_command_authentication_message_bytes_v1(candidate, row)
    signature = G2Basic.Sign(PUBLIC_TEST_SCALAR, message)
    candidate = dataclasses.replace(
        candidate, envelope=dataclasses.replace(envelope, signature_bytes=signature)
    )
    roots, _ = load_evidence(evidence_dir)
    artifact = evidence_dir / "source" / ARTIFACT
    manifest, release, _ = signature_release(roots, read_regular(artifact))
    bound = bind_deployed_bls_economic_command_signature_verifier_v1(
        artifact_path=artifact,
        release=release,
        evidence_manifest=manifest,
        deployment_root=occurrence.deployment_root,
        profile_root=selected.profile_id,
        selection_purpose=Purpose.ISOLATED_QUALIFICATION,
    )
    authenticated = _authenticate_isolated_economic_command_intent_v1(candidate, bound)
    command = bind_authenticated_intent_to_occurrence_v1(authenticated, occurrence)
    if command.selection_purpose is not Purpose.ISOLATED_QUALIFICATION:
        raise ValueError("prepared authentication purpose drift")
    return (
        candidate,
        message,
        {
            "intent_binding_root": authenticated.binding_root,
            "command_binding_root": command.binding_root,
            "signature_verifier_binding_root": bound.binding_root,
        },
    )


def _authorization(prior):
    return Authorization(
        prior.command_kind,
        prior.subject_id,
        prior.grant_root,
        prior.route_release_id,
        "isolated-public-alice-key-v1",
        "0x" + G2Basic.SkToPk(PUBLIC_TEST_SCALAR).hex(),
        ALGORITHM,
        1,
        1,
        prior.nonce,
        prior.nonce,
        True,
    )


def _envelope_payload(envelope):
    return {
        "schema": "zenodex/isolated-raw-authentication-envelope/v1",
        "command_body_hex": envelope.command_body_bytes.hex(),
        "signer_key_id": envelope.signer_key_id,
        "signer_public_key": envelope.signer_public_key,
        "signature_algorithm": envelope.signature_algorithm,
        "signature_hex": envelope.signature_bytes.hex(),
    }


def _subject_payload(profile_id, authentication):
    return {
        "profile_id": profile_id,
        "seed_sha256": SEED_SHA256,
        "public_test_scalar": PUBLIC_TEST_SCALAR,
        "selection_purpose": Purpose.ISOLATED_QUALIFICATION.value,
        "genuine_signature_verified_locally": True,
        "new_receipts_generated": False,
        "genesis_ownership_verified": False,
        "production_authority": False,
        "loaded_code_correspondence_attested": False,
        "retained_economic_release_labels_are_assumptions": True,
        "external_data_availability_verified": False,
        "external_finality_verified": False,
        "guest_images": {key: row[0] for key, row in GUESTS.items()},
        **authentication,
    }


def prepare(seed: bytes, evidence_dir: Path) -> dict[str, bytes]:
    if sha256(seed) != SEED_SHA256:
        raise ValueError("retained compatibility seed hash drift")
    value = closed_json(seed)
    roots, objects = load_evidence(evidence_dir)
    require_current_evidence(Path(__file__).resolve().parents[1], objects)
    artifact = read_regular(evidence_dir / "source" / ARTIFACT)
    if sha256(artifact) != objects["implementation.json"]["sha256"]:
        raise ValueError("selected BLS artifact drift")
    manifest, release, schemas = signature_release(roots, artifact)
    signatures = SignatureRegistry((release,))
    prior = record(proof.EconomicCommandOccurrenceV1, value["occurrence"])
    authorization = _authorization(prior)
    authorizations = AuthorizationRegistry((authorization,))
    assumption, sources = genesis_source(decode_global_economic_state_v1(value["pre_state"]))
    selected, policies, pre, occurrence = rebind(value, signatures, authorizations, sources)
    module, accepted, lane, journal, checks = economic_preflight(
        value, selected, policies, occurrence
    )
    candidate, message, authentication = authenticate(
        selected, policies, signatures, authorizations, occurrence, module, evidence_dir
    )
    payloads = {
        "route.input.json": value,
        "module.input.json": module.to_canonical(),
        "coordinator.input.json": value["lane_input"],
        "initial.input.json": initial_input(selected, policies, pre, sources, roots),
        "epoch.input.json": epoch_input(selected, occurrence, journal, roots),
        "signature-manifest.json": manifest.to_canonical(),
        "signature-registry.json": signatures.to_canonical(),
        "authorization-registry.json": authorizations.to_canonical(),
        "intent.json": candidate.intent,
        "authentication-envelope.json": _envelope_payload(candidate.envelope),
        "genesis-allocation-assumption.json": assumption,
        "signature-schema-preimages.json": schemas,
        "reference.json": {
            "input": value,
            "module_journal": accepted.module_journal,
            "lane_journal": lane.lane_journal,
            "route_journal": journal,
            "effect_plan": lane.effects,
            **checks,
        },
        "subject.json": _subject_payload(selected.profile_id, authentication),
    }
    output = {name: abi.canonical_global_bytes_v1(obj) for name, obj in payloads.items()}
    output.update(
        {
            "command-body.bin": candidate.envelope.command_body_bytes,
            "signing-message.bin": message,
            "signature.bin": candidate.envelope.signature_bytes,
            "expected-module.journal": abi.canonical_global_bytes_v1(accepted.module_journal),
            "expected-coordinator.journal": abi.canonical_global_bytes_v1(lane.lane_journal),
            "expected-route.journal": abi.canonical_global_bytes_v1(journal),
        }
    )
    # Any source/dependency change while the crypto or economic checks ran
    # invalidates preparation. Physical/loaded-code integrity remains external.
    require_current_evidence(Path(__file__).resolve().parents[1], objects)
    return output


def write_bundle(output: Path, payloads: dict[str, bytes]) -> None:
    output.mkdir(exist_ok=False)
    rows = []
    for name, raw in sorted(payloads.items()):
        if Path(name).name != name or len(raw) > 8 * 1024 * 1024:
            raise ValueError("prepared artifact path/size")
        (output / name).write_bytes(raw)
        if name.endswith(".verifier"):
            (output / name).chmod(0o500)
        rows.append({"path": name, "sha256": sha256(raw), "bytes": len(raw)})
    (output / "inputs.sha256.json").write_bytes(canonical({"files": rows}))


def retain_verifiers(metadata_path: Path) -> dict[str, bytes]:
    """Acquire exactly the historical four endpoints, without receipt checks."""
    metadata = closed_json(read_regular(metadata_path, 1024 * 1024))
    rows = metadata["artifacts"]
    expected = {image: name for name, (image, _) in GUESTS.items()}
    if len(rows) != 4 or {row["image_id"] for row in rows} != set(expected):
        raise ValueError("retained verifier image set drift")
    outputs, measured = {}, []
    for row in rows:
        name = expected[row["image_id"]]
        raw = read_regular(Path(row["executable_path"]))
        if sha256(raw) != GUESTS[name][1]:
            raise ValueError("retained verifier artifact drift")
        filename = name + ".verifier"
        outputs[filename] = raw
        measured.append(
            {
                "image_id": row["image_id"],
                "artifact": filename,
                "sha256": sha256(raw),
                "bytes": len(raw),
            }
        )
    for filename, digest in (
        (
            "verifier-manifest.json",
            "1fe449c82108ebdfd716fb608d0d7e55514c6c93bd6d0d5397238409ae27051d",
        ),
        (
            "verifier-registry.json",
            "5fa88fb8770c8abcb85e5c220760c8518171b66590e0ffe91cf7107fefde71e0",
        ),
    ):
        raw = read_regular(metadata_path.parent / filename)
        if sha256(raw) != digest:
            raise ValueError("retained receipt verifier registry evidence drift")
        outputs[filename] = raw
    outputs["retained-verifiers.json"] = canonical(
        {
            "artifacts": sorted(measured, key=lambda row: row["image_id"]),
            "acquisition_only": True,
            "new_receipts_verified": False,
        }
    )
    return outputs


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--evidence", type=Path, required=True)
    parser.add_argument("--retained-verifier-metadata", type=Path, required=True)
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[1]
    retained = retain_verifiers(args.retained_verifier_metadata)
    acquire_evidence(repo, args.evidence)
    payloads = prepare(read_regular(repo / SEED_FILE), args.evidence)
    payloads.update(retained)
    write_bundle(args.output, payloads)
    print(payloads["subject.json"].decode())


if __name__ == "__main__":
    main()
