"""Bounded custody semantics for the isolated receipt pipeline.

Receipt replies use the existing measured synthetic transport and signatures use
the real deterministic BLS fixture.  The cases exercise semantic selection,
custody projection, and fail-closed raw evidence handling; they confer no
publication or live authority.
"""

from __future__ import annotations

from dataclasses import replace
from pathlib import Path

import pytest

from src.core import global_settlement_types_v1 as abi
from src.core.asset_transfer_epoch_allocation_v1 import (
    AssetTransferEpochAllocationAcceptedV1,
    check_asset_transfer_epoch_allocation_v1,
)
from src.integration import economic_command_bls_signature_verifier_v1 as bls
from src.integration import isolated_asset_receipt_pipeline_v1 as pipeline
from tests.integration import publisher_receipt_port_fixtures_v1 as process_fixtures
from tests.integration.custody_asset_receipt_pipeline_fixtures_v1 import _fixture

simulated_measured_publisher_crypto_v1 = (
    process_fixtures.simulated_measured_publisher_crypto_v1
)


@pytest.fixture
def subject(simulated_measured_publisher_crypto_v1):
    return _fixture(simulated_measured_publisher_crypto_v1)


def _bind(subject):
    ports = process_fixtures.bind_publisher_test_receipt_ports_v1(
        subject.candidate,
        subject,
    )
    return pipeline.bind_isolated_custody_asset_receipt_pipeline_v1(
        profile=subject.candidate.profile,
        policy_registry=subject.policy,
        receipt_ports=ports,
        deployment_root=subject.candidate.pre_state.deployment_root,
        signature_artifact_path=Path(bls.__file__),
        signature_release=subject.signature_release,
        signature_evidence_manifest=subject.signature_manifest,
    )


def _bind_legacy(subject):
    ports = process_fixtures.bind_publisher_test_receipt_ports_v1(
        subject.candidate,
        subject,
    )
    return pipeline.bind_isolated_asset_receipt_pipeline_v1(
        profile=subject.candidate.profile,
        policy_registry=subject.policy,
        receipt_ports=ports,
        deployment_root=subject.candidate.pre_state.deployment_root,
        signature_artifact_path=Path(bls.__file__),
        signature_release=subject.signature_release,
        signature_evidence_manifest=subject.signature_manifest,
    )


def _verify(handle, subject, **changes):
    values = {
        "candidate": subject.candidate,
        "predecessor": subject.candidate.pre_state,
        "raw_evidence": (subject.raw,),
        **changes,
    }
    return handle.verify(
        **values,
    )


def _state_bytes(subject):
    return tuple(
        abi.canonical_global_bytes_v1(value)
        for value in (
            subject.raw.module_input.to_canonical(),
            subject.candidate.pre_state,
            subject.candidate.post_state,
        )
    )


def test_nonzero_custody_uses_exact_global_rows_and_feeds_allocation(subject):
    assert subject.raw.module_input.custody == (
        abi.EconomicAmountV1("custodian", "USD", "vault", 7),
    )
    assert subject.candidate.pre_state.custody == subject.raw.module_input.custody
    assert subject.candidate.pre_state.liabilities == (
        abi.EconomicAmountV1("alice", "USD", "vault", 7),
    )
    assert subject.candidate.post_state.custody == subject.candidate.pre_state.custody
    assert subject.candidate.post_state.liabilities == subject.candidate.pre_state.liabilities
    before = _state_bytes(subject)

    result = _verify(_bind(subject), subject)

    assert subject.calls == list(subject.expected)
    conservation = result.module_evidence[0][0].effects.asset_conservation
    assert conservation[0].owned_and_custodied_pre_atoms == 2170
    assert conservation[0].owned_and_custodied_post_atoms == 2170
    checked = check_asset_transfer_epoch_allocation_v1(
        candidate=result.candidate,
        predecessor=subject.candidate.pre_state,
        module_evidence=result.module_evidence,
    )
    assert isinstance(checked, AssetTransferEpochAllocationAcceptedV1)
    assert _state_bytes(subject) == before


def test_zero_custody_remains_a_valid_custody_semantics_epoch(
    simulated_measured_publisher_crypto_v1,
):
    zero = _fixture(simulated_measured_publisher_crypto_v1, custody_atoms=0)
    result = _verify(_bind(zero), zero)

    assert zero.raw.module_input.custody == ()
    assert zero.candidate.pre_state.custody == ()
    assert zero.candidate.pre_state.liabilities == ()
    assert zero.candidate.post_state.custody == ()
    assert zero.calls == list(zero.expected)
    assert isinstance(
        check_asset_transfer_epoch_allocation_v1(
            candidate=result.candidate,
            predecessor=zero.candidate.pre_state,
            module_evidence=result.module_evidence,
        ),
        AssetTransferEpochAllocationAcceptedV1,
    )


@pytest.mark.parametrize("variant", ("missing", "misattributed"))
def test_missing_or_misattributed_raw_custody_rejects_before_allocation(
    subject,
    variant,
):
    module = subject.raw.module_input
    if variant == "missing":
        state = replace(
            module.pre_state,
            supplies=tuple(
                replace(row, amount_atoms=row.amount_atoms - 7)
                if row.asset == "USD"
                else row
                for row in module.pre_state.supplies
            ),
        )
        changed_module = replace(module, pre_state=state, custody=())
    else:
        changed_module = replace(
            module,
            custody=(abi.EconomicAmountV1("mallory", "USD", "vault", 7),),
        )
    raw = replace(subject.raw, module_input=changed_module)
    before = _state_bytes(subject)

    with pytest.raises(ValueError, match="receipt statement rejected"):
        _verify(_bind(subject), subject, raw_evidence=(raw,))

    assert len(subject.calls) == 1
    assert _state_bytes(subject) == before


def test_wrong_semantic_root_is_coherently_bound_but_rejected_before_receipts(
    simulated_measured_publisher_crypto_v1,
):
    subject = _fixture(
        simulated_measured_publisher_crypto_v1,
        semantic_root_overrides={"module": "0x" + "99" * 32},
    )
    before = _state_bytes(subject)

    with pytest.raises(ValueError, match="custody semantics module specification root mismatch"):
        _verify(_bind(subject), subject)

    assert subject.calls == []
    assert _state_bytes(subject) == before


def test_invalid_signature_rejects_before_every_receipt_callback(subject):
    raw = replace(
        subject.raw,
        envelope=replace(subject.raw.envelope, signature_bytes=b"\0" * 96),
    )
    before = _state_bytes(subject)

    with pytest.raises(ValueError, match="command authentication signature rejected"):
        _verify(_bind(subject), subject, raw_evidence=(raw,))

    assert subject.calls == []
    assert _state_bytes(subject) == before


def test_legacy_factory_still_accepts_zero_custody_under_the_legacy_contract(
    simulated_measured_publisher_crypto_v1,
):
    zero = _fixture(simulated_measured_publisher_crypto_v1, custody_atoms=0)
    result = _verify(_bind_legacy(zero), zero)

    assert zero.calls == list(zero.expected)
    assert result.candidate.verified_routes
    assert result.candidate.pre_state.custody == ()
    assert result.candidate.pre_state.liabilities == ()
