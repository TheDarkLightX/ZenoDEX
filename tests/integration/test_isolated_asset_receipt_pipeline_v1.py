"""Real BLS controls with explicitly synthetic RISC0 process replies.

The measured-port factory/transport and all deterministic core joins run here.
This is no new genuine proof qualification: the retained e7faba profile pins a
test signature registry and requires new proofs when its signer policy changes.
"""

from __future__ import annotations

import copy
from dataclasses import replace
from pathlib import Path

import pytest
from py_ecc.bls import G2Basic

from src.core import global_settlement_types_v1 as abi
from src.core.asset_transfer_epoch_allocation_v1 import (
    AssetTransferEpochAllocationAcceptedV1,
    check_asset_transfer_epoch_allocation_v1,
)
from src.core.asset_transfer_lane_module_v1 import transition_asset_transfer_lane_module_v1
from src.integration import economic_command_bls_signature_verifier_v1 as bls
from src.integration import isolated_asset_receipt_pipeline_v1 as pipeline
from src.integration.isolated_profile_receipt_ports_v1 import IsolatedProfileReceiptPortsV1
from tests.integration import publisher_receipt_port_fixtures_v1 as process_fixtures
from tests.integration.asset_receipt_pipeline_fixtures_v1 import _fixture

bind_publisher_test_receipt_ports_v1 = process_fixtures.bind_publisher_test_receipt_ports_v1
simulated_measured_publisher_crypto_v1 = process_fixtures.simulated_measured_publisher_crypto_v1


@pytest.fixture
def subject(simulated_measured_publisher_crypto_v1):
    return _fixture(simulated_measured_publisher_crypto_v1)


def _bind(subject, **changes):
    ports = bind_publisher_test_receipt_ports_v1(subject.candidate, subject)
    return pipeline.bind_isolated_asset_receipt_pipeline_v1(
        **{
            "profile": subject.candidate.profile,
            "policy_registry": subject.policy,
            "receipt_ports": ports,
            "deployment_root": subject.candidate.pre_state.deployment_root,
            "signature_artifact_path": Path(bls.__file__),
            "signature_release": subject.signature_release,
            "signature_evidence_manifest": subject.signature_manifest,
            **changes,
        }
    )


def _verify(handle, subject, **changes):
    return handle.verify(
        **{
            "candidate": subject.candidate,
            "predecessor": subject.candidate.pre_state,
            "raw_evidence": (subject.raw,),
            **changes,
        }
    )


def test_real_signature_and_exact_three_receipt_statements_feed_allocation(subject):
    before = abi.canonical_global_bytes_v1(subject.candidate.pre_state)
    result = _verify(_bind(subject), subject)
    assert subject.calls == list(subject.expected)
    assert len(result.candidate.verified_routes) == 1
    checked = check_asset_transfer_epoch_allocation_v1(
        candidate=result.candidate,
        predecessor=subject.candidate.pre_state,
        module_evidence=result.module_evidence,
    )
    assert isinstance(checked, AssetTransferEpochAllocationAcceptedV1)
    assert subject.candidate.verified_routes == ()
    assert before == abi.canonical_global_bytes_v1(subject.candidate.pre_state)


@pytest.mark.parametrize(
    "field", ("module_receipt_bytes", "coordinator_receipt_bytes", "route_receipt_bytes")
)
def test_each_wrong_receipt_rejects_at_its_own_stage(subject, field):
    raw = replace(subject.raw, **{field: b"foreign"})
    before = abi.canonical_global_bytes_v1(subject.candidate.pre_state)
    with pytest.raises(ValueError, match="receipt statement rejected"):
        _verify(_bind(subject), subject, raw_evidence=(raw,))
    assert (
        len(subject.calls)
        == ("module_receipt_bytes", "coordinator_receipt_bytes", "route_receipt_bytes").index(field)
        + 1
    )
    assert before == abi.canonical_global_bytes_v1(subject.candidate.pre_state)


@pytest.mark.parametrize("stage", ("module", "coordinator", "route"))
def test_each_unavailable_receipt_backend_fails_without_economic_effects(subject, stage):
    subject.fail_at = stage
    with pytest.raises(RuntimeError, match="verifier unavailable"):
        _verify(_bind(subject), subject)
    assert subject.candidate.verified_routes == ()
    assert len(subject.calls) == ("module", "coordinator", "route").index(stage) + 1


@pytest.mark.parametrize("mutation", ("signature", "signer", "nonce", "body", "authorization"))
def test_raw_authentication_failure_precedes_every_receipt_callback(subject, mutation):
    raw = subject.raw
    if mutation == "signature":
        raw = replace(raw, envelope=replace(raw.envelope, signature_bytes=b"\0" * 96))
    elif mutation == "signer":
        raw = replace(
            raw, envelope=replace(raw.envelope, signer_public_key="0x" + G2Basic.SkToPk(26).hex())
        )
    elif mutation == "nonce":
        raw = replace(raw, intent=replace(raw.intent, nonce=2))
    elif mutation == "body":
        raw = replace(raw, envelope=replace(raw.envelope, command_body_bytes=b"{}"))
    else:
        registry = replace(
            raw.authorization_registry,
            authorizations=(
                replace(raw.authorization_registry.authorizations[0], subject_id="mallory"),
            ),
        )
        raw = replace(raw, authorization_registry=registry)
    with pytest.raises(ValueError):
        _verify(_bind(subject), subject, raw_evidence=(raw,))
    assert subject.calls == []


def test_caller_witnesses_are_discarded_and_never_read(subject):
    handle = _bind(subject)
    first = _verify(handle, subject)
    subject.calls.clear()
    candidate = replace(subject.candidate, verified_routes=first.candidate.verified_routes)
    # Even a corrupt retained witness is ignored, never used to authorize a stage.
    object.__setattr__(candidate.verified_routes[0], "_fields", object())
    result = _verify(handle, subject, candidate=candidate)
    assert (
        result.candidate.verified_routes[0].command_occurrence_id
        == candidate.command_occurrences[0].occurrence_id
    )
    assert subject.calls == list(subject.expected)


def test_missing_raw_evidence_cannot_be_replaced_by_a_previous_route_witness(subject):
    handle = _bind(subject)
    result = _verify(handle, subject)
    subject.calls.clear()
    with pytest.raises(ValueError, match="exactly one raw occurrence"):
        _verify(handle, subject, candidate=result.candidate, raw_evidence=())
    assert subject.calls == []


def test_source_mismatch_rejects_before_signature_or_receipts(subject):
    with pytest.raises(ValueError, match="predecessor mismatch"):
        _verify(_bind(subject), subject, predecessor=replace(subject.candidate.pre_state, height=1))
    assert subject.calls == []


def test_mount_requires_exact_origin_profile_deployment_and_acquired_policy_bytes(subject):
    handle = _bind(subject)
    arguments = dict(
        profile=subject.candidate.profile,
        deployment_root=subject.candidate.pre_state.deployment_root,
        policy_registry_bytes=abi.canonical_global_bytes_v1(subject.policy),
    )
    assert (
        type(pipeline._isolated_asset_pipeline_mount_v1(handle, **arguments))
        is IsolatedProfileReceiptPortsV1
    )
    for change in (
        {"deployment_root": "0x" + "ef" * 32},
        {"policy_registry_bytes": b"{}"},
        {"policy_registry_bytes": bytearray(arguments["policy_registry_bytes"])},
        {"profile": replace(subject.candidate.profile, status=abi.ProfileStatusV1.SHADOW)},
    ):
        with pytest.raises(ValueError):
            pipeline._isolated_asset_pipeline_mount_v1(handle, **{**arguments, **change})
    with pytest.raises(ValueError, match="not factory-minted"):
        pipeline._isolated_asset_pipeline_mount_v1(
            object.__new__(pipeline.IsolatedAssetReceiptPipelineV1), **arguments
        )


def test_handle_is_nonconstructible_noncopyable_and_rejects_bare_ports(subject):
    with pytest.raises(TypeError, match="fixed verifier factory"):
        pipeline.IsolatedAssetReceiptPipelineV1()
    handle = _bind(subject)
    with pytest.raises(TypeError, match="cannot be copied"):
        copy.copy(handle)
    with pytest.raises(AttributeError):
        object.__setattr__(handle, "signature_verifier", object())
    with pytest.raises(TypeError, match="exact factory type"):
        _bind(subject, receipt_ports=object())


def test_callback_mutation_cannot_change_the_owned_raw_command_or_post_state(subject):
    handle = _bind(subject)
    expected_root = subject.candidate.post_state.state_root

    def mutate():
        object.__setattr__(subject.raw.module_input.command, "amount_atoms", 99)
        object.__setattr__(subject.candidate.post_state, "height", 99)

    subject.on_call = mutate
    result = _verify(handle, subject)
    assert result.candidate.post_state.state_root == expected_root
    assert (
        result.module_evidence[0][0].post_state.balances
        != subject.raw.module_input.pre_state.balances
    )
    assert subject.calls == list(subject.expected)


@pytest.mark.parametrize(
    "field", ("module_receipt_bytes", "coordinator_receipt_bytes", "route_receipt_bytes")
)
def test_malformed_present_receipt_is_rejected_before_any_verifier(subject, field):
    raw = replace(subject.raw, **{field: bytearray(b"module")})
    with pytest.raises(ValueError, match="bounded exact bytes"):
        _verify(_bind(subject), subject, raw_evidence=(raw,))
    assert subject.calls == []


def test_unavailable_bls_backend_does_not_reuse_previous_authentication(subject, monkeypatch):
    handle = _bind(subject)
    _verify(handle, subject)
    subject.calls.clear()
    monkeypatch.setattr(bls, "_BLS_BACKEND_V1", None)
    with pytest.raises(bls.EconomicCommandBlsBackendUnavailableErrorV1):
        _verify(handle, subject)
    assert subject.calls == []


def test_changed_policy_fee_is_rejected_before_module_receipt_verification(subject):
    module = subject.raw.module_input
    state = replace(
        module.pre_state, policies=(replace(module.pre_state.policies[0], transfer_fee_atoms=1),)
    )
    raw = replace(subject.raw, module_input=replace(module, pre_state=state))
    with pytest.raises(ValueError, match="policy"):
        _verify(_bind(subject), subject, raw_evidence=(raw,))
    assert subject.calls == []


@pytest.mark.parametrize("shape", ("duplicate", "list", "opaque"))
def test_raw_cardinality_and_exact_type_cannot_be_bypassed(subject, shape):
    values = {"duplicate": (subject.raw, subject.raw), "list": [subject.raw], "opaque": (object(),)}
    with pytest.raises((TypeError, ValueError)):
        _verify(_bind(subject), subject, raw_evidence=values[shape])
    assert subject.calls == []


def test_two_occurrences_retain_the_explicit_unqualified_height_position_limit(subject):
    original = subject.candidate
    candidate = replace(
        original,
        command_occurrences=original.command_occurrences * 2,
        ordered_command_body_hashes=original.ordered_command_body_hashes * 2,
        route_state_disclosures=original.route_state_disclosures * 2,
        route_journals=original.route_journals * 2,
        route_effect_plans=original.route_effect_plans * 2,
    )
    with pytest.raises(ValueError, match="one occurrence and one lane"):
        _verify(_bind(subject), subject, candidate=candidate)
    assert subject.calls == []


def test_mount_owns_profile_and_policy_before_caller_mutation(subject):
    handle = _bind(subject)
    profile = copy.deepcopy(subject.candidate.profile)
    policy_bytes = abi.canonical_global_bytes_v1(subject.policy)
    object.__setattr__(subject.policy.bindings[0], "policy_root", "0x" + "df" * 32)
    object.__setattr__(subject.candidate.profile, "status", abi.ProfileStatusV1.SHADOW)
    assert (
        type(
            pipeline._isolated_asset_pipeline_mount_v1(
                handle,
                profile=profile,
                deployment_root=subject.candidate.pre_state.deployment_root,
                policy_registry_bytes=policy_bytes,
            )
        )
        is IsolatedProfileReceiptPortsV1
    )


def test_nonzero_custody_retains_existing_coordinator_rejection(subject):
    module = subject.raw.module_input
    state = replace(
        module.pre_state,
        supplies=tuple(
            replace(row, amount_atoms=row.amount_atoms + 5) for row in module.pre_state.supplies
        ),
    )
    changed = replace(
        module, pre_state=state, custody=(abi.EconomicAmountV1("custodian", "USD", "vault", 5),)
    )
    accepted = transition_asset_transfer_lane_module_v1(changed)
    subject.expected = (
        (
            subject.expected[0][0],
            subject.expected[0][1],
            abi.canonical_global_bytes_v1(accepted.module_journal),
        ),
        *subject.expected[1:],
    )
    with pytest.raises(ValueError, match="CONSERVATION_STATE_MISMATCH"):
        _verify(_bind(subject), subject, raw_evidence=(replace(subject.raw, module_input=changed),))
    assert subject.calls == [subject.expected[0]]


@pytest.mark.parametrize(
    "field",
    (
        "intent",
        "envelope",
        "authorization_registry",
        "signature_verifier_registry",
        "asset_policy_registry",
        "module_input",
    ),
)
def test_malformed_raw_disclosures_reject_before_crypto(subject, field):
    with pytest.raises(TypeError):
        _verify(_bind(subject), subject, raw_evidence=(replace(subject.raw, **{field: object()}),))
    assert subject.calls == []
