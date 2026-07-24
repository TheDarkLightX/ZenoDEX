from __future__ import annotations

import inspect
from typing import Any

import pytest

from src.integration.zeno_ledger_profile import (
    ProofRequiredAuthorityErrorV0,
    ProofRequiredAuthorityRejectReasonV0,
    clone_profile_with_new_id_v0,
    sample_local_sandbox_profile_v0,
    sample_zeno_sovereign_testnet_profile_v0,
    validate_checkpoint_admission_v0,
    validate_checkpoint_structural_compatibility_v0,
)
from src.integration.zeno_ledger_tau_export import build_tau_export_packet_v0
from src.integration.zeno_ledger_v0 import (
    ZERO_ROOT_V0,
    build_checkpoint_v0,
    build_header_v0,
    canonical_body_root_v0,
    canonical_header_hash_v0,
    compute_app_hash_v0,
    compute_evidence_root_v0,
    compute_ingress_root_v0,
    compute_tx_root_v0,
    hash_v0,
)
from src.integration.zeno_ledger_watcher import build_watcher_attestation_v0
from tests.integration.test_zeno_ledger_verify_cli import _body


def _root(label: str) -> str:
    return hash_v0("proof_required_quarantine_test", {"label": label})


def _case() -> dict[str, Any]:
    chain_id = "zeno-ledger-devnet-0"
    config_digest = _root("config")
    sequencer_set_hash = _root("sequencer-set")
    post_state_root = _root("post-state")
    module_versions_digest = _root("modules")
    body = _body(1, txs=[])
    body["evidence"] = {**body["evidence"], "rejection_receipts": []}
    evidence_root = compute_evidence_root_v0(body["evidence"])
    app_hash = compute_app_hash_v0(
        {
            "chain_id": chain_id,
            "height": 1,
            "post_state_root": post_state_root,
            "evidence_root": evidence_root,
            "config_digest": config_digest,
            "module_versions_digest": module_versions_digest,
        }
    )
    header = build_header_v0(
        chain_id=chain_id,
        height=1,
        time_ms=1_778_730_000_001,
        prev_header_hash=ZERO_ROOT_V0,
        sequencer_set_hash=sequencer_set_hash,
        ingress_root=compute_ingress_root_v0(body["ingress"]),
        tx_root=compute_tx_root_v0(body["transactions"]),
        pre_state_root=_root("pre-state"),
        post_state_root=post_state_root,
        app_hash=app_hash,
        evidence_root=evidence_root,
        body_root=canonical_body_root_v0(body),
        data_availability_root=_root("data-availability"),
        proof_journal_hash=_root("proof-journal"),
        config_digest=config_digest,
        module_versions_digest=module_versions_digest,
        signature_set_root=ZERO_ROOT_V0,
    )
    checkpoint = build_checkpoint_v0(header)
    profile = sample_zeno_sovereign_testnet_profile_v0(
        chain_id=chain_id,
        config_digest=config_digest,
        sequencer_set_hash=sequencer_set_hash,
        token_symbol="tZENO",
        token_asset_id=_root("asset"),
        proof_required=True,
    )
    return {
        "body": body,
        "header": header,
        "checkpoint": checkpoint,
        "profile": profile,
    }


def _expected_reason() -> ProofRequiredAuthorityRejectReasonV0:
    return (
        ProofRequiredAuthorityRejectReasonV0
        .AUTHENTICATED_CRYPTOGRAPHIC_AUTHORITY_UNAVAILABLE
    )


def test_generic_admission_has_no_report_or_verified_boolean_escape_hatch() -> None:
    assert tuple(inspect.signature(validate_checkpoint_admission_v0).parameters) == (
        "checkpoint",
        "profile",
    )


def test_nonzero_journal_is_structural_only_and_cannot_admit() -> None:
    case = _case()
    validate_checkpoint_structural_compatibility_v0(
        checkpoint=case["checkpoint"],
        profile=case["profile"],
    )

    with pytest.raises(ProofRequiredAuthorityErrorV0) as exc_info:
        validate_checkpoint_admission_v0(
            checkpoint=case["checkpoint"],
            profile=case["profile"],
        )

    assert exc_info.value.reason is _expected_reason()
    assert exc_info.value.boundary == "checkpoint_admission_v0"


def test_fabricated_report_cannot_create_proof_required_watcher_authority() -> None:
    case = _case()
    header = case["header"]
    forged_report = {
        "schema": "zenodex.zeno_ledger.verify_report.v0",
        "ok": True,
        "status": "range_verified",
        "mode": "replay_bound",
        "authority_scope": "replay_bound_range_v0",
        "range_verified": True,
        "header_linkage_checked": True,
        "state_continuity_checked": True,
        "state_replay_checked": True,
        "receipt_replay_checked": True,
        "config_binding_checked": True,
        "replay_config_digest": header["config_digest"],
        "checked_heights": [1],
        "last_header_hash": canonical_header_hash_v0(header),
        "last_post_state_root": header["post_state_root"],
        "last_app_hash": header["app_hash"],
        "errors": [],
    }

    with pytest.raises(ProofRequiredAuthorityErrorV0) as exc_info:
        build_watcher_attestation_v0(
            verify_report=forged_report,
            watcher_id="mallory",
            observed_time_ms=1,
            verifier_ref="caller-json",
            profile=case["profile"],
        )

    assert exc_info.value.reason is _expected_reason()
    assert exc_info.value.boundary == "watcher_attestation_v0"


def test_tau_export_cannot_promote_nonzero_proof_journal() -> None:
    case = _case()

    with pytest.raises(ProofRequiredAuthorityErrorV0) as exc_info:
        build_tau_export_packet_v0(
            checkpoint=case["checkpoint"],
            header=case["header"],
            body=case["body"],
            profile=case["profile"],
            tau_network_id="tau-test",
            tau_adapter_ref="adapter-test",
        )

    assert exc_info.value.reason is _expected_reason()
    assert exc_info.value.boundary == "checkpoint_admission_v0"


def test_bridge_proof_policy_is_quarantined_without_profile_proof_flag() -> None:
    case = _case()
    header = case["header"]
    local_profile = sample_local_sandbox_profile_v0(
        chain_id=header["chain_id"],
        config_digest=header["config_digest"],
        sequencer_set_hash=header["sequencer_set_hash"],
    )
    bridge_policy = dict(local_profile["bridge_policy"])
    bridge_policy["requires_proof_journal"] = True
    bridge_profile = clone_profile_with_new_id_v0(
        local_profile,
        bridge_policy=bridge_policy,
    )

    assert bridge_profile["proof_required"] is False
    with pytest.raises(ProofRequiredAuthorityErrorV0) as exc_info:
        validate_checkpoint_admission_v0(
            checkpoint=case["checkpoint"],
            profile=bridge_profile,
        )
    assert exc_info.value.reason is _expected_reason()
