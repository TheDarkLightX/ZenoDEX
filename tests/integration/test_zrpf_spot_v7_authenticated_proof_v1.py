from __future__ import annotations

import copy
import hashlib
import json
import pickle
import struct
from pathlib import Path
from typing import Any

import pytest

from src.integration import _zrpf_spot_v7_authenticated_proof_v1 as proof_adapter
from src.integration.recursive_stark_verifier_adapter import (
    RecursiveVerifierExecutableFormat,
)
from tools import zrpf_spot_v7_verifier_payload_codec as payload_codec


def test_pinned_verifier_executes_once_and_retains_only_authority_neutral_observation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture()
    calls: list[dict[str, object]] = []

    def execute_once(**kwargs: object) -> bytes:
        calls.append(dict(kwargs))
        assert kwargs["request_bytes"] == fixture.request
        assert kwargs["expected_sha256"] == fixture.executable_sha256
        return fixture.response

    monkeypatch.setattr(proof_adapter, "execute_pinned_verifier_once", execute_once)
    verifier = _verifier(fixture)
    observation = verifier.verify(
        v7_receipt=fixture.v7_receipt,
        guest_input=fixture.guest_input,
        source_v6_receipt=fixture.source_v6_receipt,
    )

    assert len(calls) == 1
    assert observation._has_private_seal()
    assert observation.pinned_verifier_execution_observed is True
    assert observation.release_governed_verifier_identity_verified is False
    assert observation.proof_receipt_authority is False
    assert observation.release_authority is False
    assert observation.settlement_authority is False
    assert observation.production_authority is False
    assert observation.verified_program_id == fixture.program_id
    assert observation.economic_action_id == fixture.action_id
    assert observation.authorization_nullifier == fixture.authorization_nullifier
    assert observation.cell_transitions_root == fixture.cell_transitions_root
    assert observation.exact_v7_receipt_bytes == fixture.v7_receipt
    assert observation.exact_guest_input_bytes == fixture.guest_input
    assert observation.exact_source_v6_receipt_bytes == fixture.source_v6_receipt
    assert observation.exact_verifier_output_bytes == fixture.verifier_output
    assert observation.exact_v7_journal_bytes == fixture.journal
    assert observation.exact_plan_b_bytes == fixture.plan
    assert (
        observation.proof_verification_request_sha256 == hashlib.sha256(fixture.request).hexdigest()
    )
    assert (
        observation.proof_verification_response_sha256
        == hashlib.sha256(fixture.response).hexdigest()
    )


def test_pinned_observation_is_opaque_immutable_and_nonserializable(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture()
    monkeypatch.setattr(
        proof_adapter,
        "execute_pinned_verifier_once",
        lambda **_kwargs: fixture.response,
    )
    observation = _verifier(fixture).verify(
        v7_receipt=fixture.v7_receipt,
        guest_input=fixture.guest_input,
        source_v6_receipt=fixture.source_v6_receipt,
    )

    with pytest.raises(TypeError):
        observation.__class__(object(), seal=object())  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        observation.epoch_id = 99  # type: ignore[misc]
    with pytest.raises(TypeError):
        copy.copy(observation)
    with pytest.raises(TypeError):
        copy.deepcopy(observation)
    with pytest.raises(TypeError):
        pickle.dumps(observation)


@pytest.mark.parametrize(
    ("mutation", "message"),
    [
        ("artifact_hash", "V7 receipt SHA-256 mismatch"),
        ("action_binding", "authenticated projection disagrees"),
        ("policy", "application_id does not match"),
        ("profile_order", "receipt security profile field order mismatch"),
        ("unbound_asset_root", "projection schema mismatch"),
        ("noncanonical", "must be canonical JSON"),
    ],
)
def test_projection_mutations_reject_at_the_governed_boundary(
    monkeypatch: pytest.MonkeyPatch,
    mutation: str,
    message: str,
) -> None:
    fixture = _fixture()
    response = json.loads(fixture.response)
    projection = response["authenticated_projection"]
    verifier = _verifier(fixture)
    if mutation == "artifact_hash":
        projection["v7_receipt_sha256"] = _hex("wrong-receipt")
    elif mutation == "action_binding":
        projection["economic_action_id"] = _hex("wrong-action")
    elif mutation == "policy":
        verifier = _verifier(fixture, application_id=_hex("wrong-application"))
    elif mutation == "profile_order":
        profile = projection["receipt_security_profile"]
        projection["receipt_security_profile"] = {
            key: profile[key] for key in reversed(tuple(profile))
        }
    elif mutation == "unbound_asset_root":
        projection["asset_effects_root"] = _hex("unbound-asset-effects")
    response_bytes = _rust_json(response)
    if mutation == "noncanonical":
        response_bytes += b"\n"
    monkeypatch.setattr(
        proof_adapter,
        "execute_pinned_verifier_once",
        lambda **_kwargs: response_bytes,
    )
    with pytest.raises(
        proof_adapter.SpotV7SemanticProofVerificationErrorV1,
        match=message,
    ):
        verifier.verify(
            v7_receipt=fixture.v7_receipt,
            guest_input=fixture.guest_input,
            source_v6_receipt=fixture.source_v6_receipt,
        )


def test_aggregate_request_budget_covers_all_individual_artifact_maxima() -> None:
    fixed_json_overhead = len(
        _rust_json(
            {
                "schema": proof_adapter.SPOT_V7_PROOF_VERIFIER_REQUEST_SCHEMA_V1,
                "v7_receipt_hex": "",
                "guest_input_hex": "",
                "source_v6_receipt_hex": "",
            }
        )
    )
    maximum_encoded_bytes = fixed_json_overhead + 2 * (
        proof_adapter.MAX_SPOT_V7_RECEIPT_BYTES_V1
        + proof_adapter.MAX_SPOT_V7_GUEST_INPUT_BYTES_V1
        + proof_adapter.MAX_SPOT_V7_SOURCE_V6_RECEIPT_BYTES_V1
    )

    assert maximum_encoded_bytes <= proof_adapter.MAX_SPOT_V7_PROOF_REQUEST_BYTES_V1


def test_semantically_wrong_action_root_rejects_after_payload_associations(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture(invalid_action_root=True)
    monkeypatch.setattr(
        proof_adapter,
        "execute_pinned_verifier_once",
        lambda **_kwargs: fixture.response,
    )
    with pytest.raises(
        proof_adapter.SpotV7SemanticProofVerificationErrorV1,
        match="list roots do not match",
    ):
        _verifier(fixture).verify(
            v7_receipt=fixture.v7_receipt,
            guest_input=fixture.guest_input,
            source_v6_receipt=fixture.source_v6_receipt,
        )


def test_test_script_manifest_cannot_enter_the_durable_proof_path(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = _fixture()
    called = False

    def fail_if_called(**_kwargs: object) -> bytes:
        nonlocal called
        called = True
        return fixture.response

    monkeypatch.setattr(proof_adapter, "execute_pinned_verifier_once", fail_if_called)
    verifier = _verifier(
        fixture,
        executable_format=RecursiveVerifierExecutableFormat.TEST_SCRIPT,
    )
    with pytest.raises(
        proof_adapter.SpotV7SemanticProofVerificationErrorV1,
        match="requires a static ELF verifier",
    ):
        verifier.verify(
            v7_receipt=fixture.v7_receipt,
            guest_input=fixture.guest_input,
            source_v6_receipt=fixture.source_v6_receipt,
        )
    assert called is False


def test_request_and_authority_manifest_are_exact_and_canonical() -> None:
    fixture = _fixture()
    request = json.loads(fixture.request)
    assert list(request) == [
        "schema",
        "v7_receipt_hex",
        "guest_input_hex",
        "source_v6_receipt_hex",
    ]
    assert _rust_json(request) == fixture.request

    manifest = _authority_manifest(fixture)
    assert (
        json.dumps(
            json.loads(manifest),
            sort_keys=True,
            separators=(",", ":"),
        ).encode()
        == manifest
    )
    with pytest.raises(ValueError, match="hash mismatch"):
        proof_adapter.PinnedSpotV7SemanticProofVerifierV1(
            executable=Path("/governed/spot-v7-proof-verifier"),
            authority_manifest_json=manifest,
            authority_manifest_sha256="11" * 32,
        )


class _Fixture:
    def __init__(self, *, invalid_action_root: bool = False) -> None:
        self.v7_receipt = b'{"receipt":"v7"}'
        self.guest_input = b"exact-v7-guest-input"
        self.source_v6_receipt = b'{"receipt":"source-v6"}'
        self.executable_sha256 = hashlib.sha256(b"governed-verifier").hexdigest()
        self.application_id = _hex("application")
        self.chain_or_domain_id = _hex("domain")
        self.epoch_id = 77
        self.program_id = _hex("v7-program")
        self.profile_id = _hex("v7-profile")
        self.program_manifest_root = _hex("v7-manifest")
        self.source_program_id = _hex("source-program")
        self.source_profile_id = _hex("source-profile")
        self.source_claim_binding = _hex("source-claim")
        self.source_journal_sha256 = _hex("source-journal")
        self.da_certificate_root = _hex("da-certificate")
        self.data_root = _hex("data-root")
        self.plan_commitment = _hex("plan-commitment")
        self.action_id = _hex("economic-action")
        self.authorization_nullifier = _hex("authorization-nullifier")
        self.grant_spend = _hex("grant-spend")
        self.consumed = tuple(sorted((_hex("consumed-a"), _hex("consumed-b"))))
        self.action_ids_root = _list_root(
            b"zenodex.zrpf.economic_action_ids_root.v1", (self.action_id,)
        )
        if invalid_action_root:
            self.action_ids_root = _hex("semantically-wrong-action-root")
        self.action_bindings_root = _list_root(
            b"zenodex.zrpf.action_authorization_bindings_root.v1",
            (self.authorization_nullifier,),
        )
        self.grant_spends_root = _list_root(
            b"zenodex.zrpf.authorization_grant_spends_root.v1", (self.grant_spend,)
        )
        self.consumed_root = _list_root(
            b"zenodex.zrpf.economic_consumed_objects_root.v1", self.consumed
        )
        self.cell_transitions_root = _hex("cell-transitions")
        self.pre_state_root = _hex("pre-state")
        self.post_state_root = _hex("post-state")
        self.required_child_receipt_profile_id = self.source_profile_id
        self.receipt_profile: dict[str, object] = {
            "profile_id": "risc0_succinct_poseidon2_resolve_3_0_5_v1",
            "receipt_kind": "succinct",
            "verifier_parameters": _hex("verifier-parameters"),
            "hashfn": "poseidon2",
            "control_id": _hex("control-id"),
        }
        self.plan = b"canonical-plan-b-v1"
        self.verifier_output, self.journal = _verifier_payload(self)
        self.request = proof_adapter.spot_v7_proof_verifier_request_bytes_v1(
            v7_receipt=self.v7_receipt,
            guest_input=self.guest_input,
            source_v6_receipt=self.source_v6_receipt,
        )
        self.response = _response(self)


def _fixture(*, invalid_action_root: bool = False) -> _Fixture:
    return _Fixture(invalid_action_root=invalid_action_root)


def _authority_manifest(
    fixture: _Fixture,
    *,
    application_id: str | None = None,
    executable_format: RecursiveVerifierExecutableFormat = (
        RecursiveVerifierExecutableFormat.STATIC_ELF_X86_64
    ),
) -> bytes:
    return proof_adapter.spot_v7_proof_verifier_authority_manifest_bytes_v1(
        executable_sha256=fixture.executable_sha256,
        executable_format=executable_format,
        application_id=application_id or fixture.application_id,
        chain_or_domain_id=fixture.chain_or_domain_id,
        epoch_id=fixture.epoch_id,
        verified_program_id=fixture.program_id,
        verified_profile_id=fixture.profile_id,
        verified_program_manifest_root=fixture.program_manifest_root,
        receipt_security_profile=fixture.receipt_profile,
        source_child_program_id=fixture.source_program_id,
        required_source_child_receipt_security_profile_id=(
            fixture.required_child_receipt_profile_id
        ),
    )


def _verifier(
    fixture: _Fixture,
    *,
    application_id: str | None = None,
    executable_format: RecursiveVerifierExecutableFormat = (
        RecursiveVerifierExecutableFormat.STATIC_ELF_X86_64
    ),
) -> proof_adapter.PinnedSpotV7SemanticProofVerifierV1:
    manifest = _authority_manifest(
        fixture,
        application_id=application_id,
        executable_format=executable_format,
    )
    return proof_adapter.PinnedSpotV7SemanticProofVerifierV1(
        executable=Path("/governed/spot-v7-proof-verifier"),
        authority_manifest_json=manifest,
        authority_manifest_sha256=hashlib.sha256(manifest).hexdigest(),
    )


def _response(fixture: _Fixture) -> bytes:
    projection: dict[str, Any] = {
        "request_bytes": len(fixture.request),
        "request_sha256": hashlib.sha256(fixture.request).hexdigest(),
        "v7_receipt_bytes": len(fixture.v7_receipt),
        "v7_receipt_sha256": hashlib.sha256(fixture.v7_receipt).hexdigest(),
        "guest_input_bytes": len(fixture.guest_input),
        "guest_input_sha256": hashlib.sha256(fixture.guest_input).hexdigest(),
        "source_v6_receipt_bytes": len(fixture.source_v6_receipt),
        "source_v6_receipt_sha256": hashlib.sha256(fixture.source_v6_receipt).hexdigest(),
        "verifier_output_bytes": len(fixture.verifier_output),
        "verifier_output_hex": fixture.verifier_output.hex(),
        "verifier_output_sha256": hashlib.sha256(fixture.verifier_output).hexdigest(),
        "journal_bytes": len(fixture.journal),
        "journal_sha256": hashlib.sha256(fixture.journal).hexdigest(),
        "plan_b_bytes": len(fixture.plan),
        "plan_b_sha256": hashlib.sha256(fixture.plan).hexdigest(),
        "verified_program_id": fixture.program_id,
        "verified_profile_id": fixture.profile_id,
        "verified_program_manifest_root": fixture.program_manifest_root,
        "receipt_security_profile": fixture.receipt_profile,
        "source_child_program_id": fixture.source_program_id,
        "required_source_child_receipt_security_profile_id": (
            fixture.required_child_receipt_profile_id
        ),
        "source_child_claim_binding": fixture.source_claim_binding,
        "source_child_journal_sha256": fixture.source_journal_sha256,
        "application_id": fixture.application_id,
        "chain_or_domain_id": fixture.chain_or_domain_id,
        "epoch_id": fixture.epoch_id,
        "data_availability_certificate_root": fixture.da_certificate_root,
        "data_root": fixture.data_root,
        "settlement_effect_plan_commitment": fixture.plan_commitment,
        "economic_action_id": fixture.action_id,
        "authorization_nullifier": fixture.authorization_nullifier,
        "authorization_grant_spend_nullifier": fixture.grant_spend,
        "consumed_object_ids": list(fixture.consumed),
        "action_ids_root": fixture.action_ids_root,
        "action_authorization_bindings_root": fixture.action_bindings_root,
        "authorization_grant_spends_root": fixture.grant_spends_root,
        "consumed_object_ids_root": fixture.consumed_root,
        "cell_transitions_root": fixture.cell_transitions_root,
        "pre_state_root": fixture.pre_state_root,
        "post_state_root": fixture.post_state_root,
    }
    assert tuple(projection) == proof_adapter._PROJECTION_KEYS_IN_RUST_ORDER
    return _rust_json(
        {
            "ok": True,
            "schema": proof_adapter.SPOT_V7_PROOF_VERIFIER_RESPONSE_SCHEMA_V1,
            "authenticated_projection": projection,
        }
    )


def _verifier_payload(fixture: _Fixture) -> tuple[bytes, bytes]:
    semantic = b"s" * payload_codec.SPOT_V7_SEMANTIC_JOURNAL_BYTES_V1
    binding_fields = (
        _field("compatibility-profile"),
        _field("state-root-scheme"),
        _field("source-journal-commitment"),
        _field("source-plan-commitment"),
        bytes.fromhex(fixture.plan_commitment),
        bytes.fromhex(fixture.cell_transitions_root),
        bytes.fromhex(fixture.pre_state_root),
        bytes.fromhex(fixture.post_state_root),
        bytes.fromhex(fixture.action_id),
        _field("action-semantics"),
        _field("effect-commitment"),
        _field("public-policy"),
    )
    binding = b"\x00\x01" + b"".join(binding_fields)
    binding_commitment = hashlib.sha256(
        len(payload_codec.SPOT_V7_EFFECT_BINDING_COMMITMENT_DOMAIN_V1).to_bytes(2, "big")
        + payload_codec.SPOT_V7_EFFECT_BINDING_COMMITMENT_DOMAIN_V1
        + binding
    ).digest()
    journal_fields = (
        bytes.fromhex(fixture.source_program_id),
        bytes.fromhex(fixture.required_child_receipt_profile_id),
        bytes.fromhex(fixture.source_claim_binding),
        bytes.fromhex(fixture.source_journal_sha256),
        bytes.fromhex(fixture.da_certificate_root),
        bytes.fromhex(fixture.data_root),
        _field("host-input-binding"),
        _field("host-input-sha256"),
        hashlib.sha256(semantic).digest(),
        binding_commitment,
        bytes.fromhex(fixture.plan_commitment),
        hashlib.sha256(fixture.plan).digest(),
        bytes.fromhex(fixture.action_ids_root),
    )
    journal_total = (
        payload_codec.SPOT_V7_JOURNAL_HEADER_BYTES_V1
        + 32 * len(journal_fields)
        + len(semantic)
        + len(binding)
        + len(fixture.plan)
    )
    journal = b"".join(
        (
            payload_codec.SPOT_V7_JOURNAL_MAGIC_V1,
            struct.pack(
                ">HIIHHI", 1, journal_total, 1_024, len(semantic), len(binding), len(fixture.plan)
            ),
            *journal_fields,
            semantic,
            binding,
            fixture.plan,
        )
    )
    output_fields = (
        bytes.fromhex(fixture.program_id),
        bytes.fromhex(fixture.profile_id),
        bytes.fromhex(fixture.program_manifest_root),
        hashlib.sha256(journal).digest(),
        *journal_fields[:6],
        bytes.fromhex(fixture.plan_commitment),
        hashlib.sha256(fixture.plan).digest(),
        bytes.fromhex(fixture.pre_state_root),
        bytes.fromhex(fixture.post_state_root),
        bytes.fromhex(fixture.action_ids_root),
        bytes.fromhex(fixture.action_bindings_root),
        bytes.fromhex(fixture.grant_spends_root),
        bytes.fromhex(fixture.consumed_root),
        journal_fields[7],
    )
    total = payload_codec.SPOT_V7_VERIFIER_OUTPUT_HEADER_BYTES_V1 + len(journal)
    output = b"".join(
        (
            payload_codec.SPOT_V7_VERIFIER_OUTPUT_MAGIC_V1,
            struct.pack(">HIIII", 1, total, len(journal), len(fixture.plan), 1_024),
            *output_fields,
            journal,
        )
    )
    payload_codec.decode_structural_v7_verifier_payload_v1(output)
    return output, journal


def _list_root(domain: bytes, values: tuple[str, ...]) -> str:
    return hashlib.sha256(
        len(domain).to_bytes(2, "big")
        + domain
        + len(values).to_bytes(4, "big")
        + b"".join(bytes.fromhex(value) for value in values)
    ).hexdigest()


def _field(label: str) -> bytes:
    return hashlib.sha256(label.encode()).digest()


def _hex(label: str) -> str:
    return _field(label).hex()


def _rust_json(value: object) -> bytes:
    return json.dumps(value, ensure_ascii=True, separators=(",", ":")).encode("ascii")
