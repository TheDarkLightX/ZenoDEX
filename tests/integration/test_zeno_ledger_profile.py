from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from src.integration.zeno_ledger_profile import (
    DEPLOYMENT_MODE_TAU_EXCLUSIVE_RELEASE_V0,
    DEPLOYMENT_MODE_ZENO_SOVEREIGN_TESTNET_V0,
    TOKEN_SCOPE_NONE_V0,
    TOKEN_SCOPE_ZENO_LEDGER_TESTNET_V0,
    ProofRequiredAuthorityErrorV0,
    ProofRequiredAuthorityRejectReasonV0,
    clone_profile_with_new_id_v0,
    make_zeno_ledger_profile_v0,
    profile_content_hash_v0,
    sample_local_sandbox_profile_v0,
    sample_tau_exclusive_release_profile_v0,
    sample_zeno_sovereign_testnet_profile_v0,
    validate_checkpoint_admission_v0,
    validate_checkpoint_structural_compatibility_v0,
    validate_zeno_ledger_profile_v0,
)
from src.integration.zeno_ledger_v0 import (
    ZERO_ROOT_V0,
    build_checkpoint_v0,
    build_header_v0,
    compute_app_hash_v0,
    hash_v0,
)

ROOT = Path(__file__).resolve().parents[2]
MAKE_PROFILE_SCRIPT = ROOT / "tools" / "zeno_ledger_make_profile.py"


def _root(label: str) -> str:
    return hash_v0("test_root", {"label": label})


def _run_make_profile(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(MAKE_PROFILE_SCRIPT), *args],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )


def _checkpoint(
    *,
    chain_id: str = "zeno-ledger-devnet-0",
    config_digest: str | None = None,
    sequencer_set_hash: str | None = None,
    proof_journal_hash: str = ZERO_ROOT_V0,
) -> dict[str, object]:
    cfg = config_digest or _root("config")
    seq = sequencer_set_hash or _root("sequencer-set")
    app_hash = compute_app_hash_v0(
        {
            "chain_id": chain_id,
            "height": 1,
            "post_state_root": _root("post"),
            "evidence_root": _root("evidence"),
            "config_digest": cfg,
            "module_versions_digest": _root("modules"),
        }
    )
    header = build_header_v0(
        chain_id=chain_id,
        height=1,
        time_ms=1_778_730_000_000,
        prev_header_hash=ZERO_ROOT_V0,
        sequencer_set_hash=seq,
        ingress_root=_root("ingress"),
        tx_root=_root("tx"),
        pre_state_root=_root("pre"),
        post_state_root=_root("post"),
        app_hash=app_hash,
        evidence_root=_root("evidence"),
        body_root=_root("body"),
        data_availability_root=_root("da"),
        proof_journal_hash=proof_journal_hash,
        config_digest=cfg,
        module_versions_digest=_root("modules"),
        signature_set_root=ZERO_ROOT_V0,
    )
    return build_checkpoint_v0(header)


def test_local_sandbox_profile_admits_matching_checkpoint_without_proof() -> None:
    config = _root("config")
    sequencer = _root("sequencer-set")
    profile = sample_local_sandbox_profile_v0(
        chain_id="zeno-ledger-devnet-0",
        config_digest=config,
        sequencer_set_hash=sequencer,
    )
    validate_zeno_ledger_profile_v0(profile)
    checkpoint = _checkpoint(config_digest=config, sequencer_set_hash=sequencer)
    validate_checkpoint_admission_v0(checkpoint=checkpoint, profile=profile)


def test_profile_id_is_content_addressed() -> None:
    profile = sample_local_sandbox_profile_v0(
        chain_id="zeno-ledger-devnet-0",
        config_digest=_root("config"),
        sequencer_set_hash=_root("sequencer-set"),
    )
    assert profile["profile_id"] == profile_content_hash_v0(profile)
    forged = dict(profile)
    forged["chain_id"] = "other-chain"
    with pytest.raises(ValueError, match="profile_id mismatch"):
        validate_zeno_ledger_profile_v0(forged)


def test_tau_exclusive_release_requires_tau_exclusive_token_policy() -> None:
    config = _root("config")
    sequencer = _root("sequencer-set")
    token_asset = _root("zeno-token")
    profile = sample_tau_exclusive_release_profile_v0(
        chain_id="zeno-ledger-tau-release-0",
        config_digest=config,
        sequencer_set_hash=sequencer,
        token_symbol="ZENO",
        token_asset_id=token_asset,
    )
    validate_zeno_ledger_profile_v0(profile)
    assert profile["deployment_mode"] == DEPLOYMENT_MODE_TAU_EXCLUSIVE_RELEASE_V0
    assert profile["tau_net_adapter_required"] is True
    assert profile["token_policy"]["issuance_scope"] == "tau_net_exclusive"
    assert profile["token_policy"]["tau_net_exclusive"] is True
    assert profile["token_policy"]["external_minting_allowed"] is False
    assert profile["token_policy"]["non_tau_deployment_allowed"] is False


def test_sovereign_testnet_profile_does_not_depend_on_tau_net() -> None:
    config = _root("config")
    sequencer = _root("sequencer-set")
    token_asset = _root("zeno-test-token")
    profile = sample_zeno_sovereign_testnet_profile_v0(
        chain_id="zeno-ledger-testnet-0",
        config_digest=config,
        sequencer_set_hash=sequencer,
        token_symbol="tZENO",
        token_asset_id=token_asset,
    )
    validate_zeno_ledger_profile_v0(profile)
    assert profile["deployment_mode"] == DEPLOYMENT_MODE_ZENO_SOVEREIGN_TESTNET_V0
    assert profile["proof_required"] is False
    assert profile["body_required"] is True
    assert profile["tau_net_adapter_required"] is False
    assert profile["bridge_policy"] == {
        "bridge_value_enabled": False,
        "requires_tau_checkpoint": False,
        "requires_proof_journal": False,
    }
    assert profile["token_policy"]["issuance_scope"] == TOKEN_SCOPE_ZENO_LEDGER_TESTNET_V0
    assert profile["token_policy"]["tau_net_exclusive"] is False
    assert profile["token_policy"]["external_minting_allowed"] is False
    assert profile["token_policy"]["non_tau_deployment_allowed"] is True

    checkpoint = _checkpoint(
        chain_id="zeno-ledger-testnet-0",
        config_digest=config,
        sequencer_set_hash=sequencer,
        proof_journal_hash=ZERO_ROOT_V0,
    )
    validate_checkpoint_admission_v0(checkpoint=checkpoint, profile=profile)


def test_sovereign_testnet_profile_can_require_zk_without_requiring_tau() -> None:
    config = _root("config")
    sequencer = _root("sequencer-set")
    profile = sample_zeno_sovereign_testnet_profile_v0(
        chain_id="zeno-ledger-testnet-0",
        config_digest=config,
        sequencer_set_hash=sequencer,
        token_symbol="tZENO",
        token_asset_id=_root("zeno-test-token"),
        proof_required=True,
    )
    assert profile["tau_net_adapter_required"] is False
    assert profile["bridge_policy"]["requires_tau_checkpoint"] is False
    assert profile["bridge_policy"]["requires_proof_journal"] is True

    checkpoint_without_proof = _checkpoint(
        chain_id="zeno-ledger-testnet-0",
        config_digest=config,
        sequencer_set_hash=sequencer,
        proof_journal_hash=ZERO_ROOT_V0,
    )
    with pytest.raises(ValueError, match="proof_journal_hash required"):
        validate_checkpoint_admission_v0(checkpoint=checkpoint_without_proof, profile=profile)

    checkpoint_with_proof = _checkpoint(
        chain_id="zeno-ledger-testnet-0",
        config_digest=config,
        sequencer_set_hash=sequencer,
        proof_journal_hash=_root("proof-journal"),
    )
    validate_checkpoint_structural_compatibility_v0(
        checkpoint=checkpoint_with_proof,
        profile=profile,
    )
    with pytest.raises(ProofRequiredAuthorityErrorV0) as exc_info:
        validate_checkpoint_admission_v0(checkpoint=checkpoint_with_proof, profile=profile)
    assert exc_info.value.reason is (
        ProofRequiredAuthorityRejectReasonV0
        .AUTHENTICATED_CRYPTOGRAPHIC_AUTHORITY_UNAVAILABLE
    )


def test_sovereign_testnet_rejects_tau_dependent_bridge_policy() -> None:
    config = _root("config")
    sequencer = _root("sequencer-set")
    token_policy = {
        "token_symbol": "tZENO",
        "token_asset_id": _root("zeno-test-token"),
        "issuance_scope": TOKEN_SCOPE_ZENO_LEDGER_TESTNET_V0,
        "tau_net_exclusive": False,
        "external_minting_allowed": False,
        "non_tau_deployment_allowed": True,
    }
    bridge_policy = {
        "bridge_value_enabled": False,
        "requires_tau_checkpoint": True,
        "requires_proof_journal": False,
    }
    with pytest.raises(ValueError, match="must not require Tau checkpoint"):
        make_zeno_ledger_profile_v0(
            profile_name="bad sovereign profile",
            deployment_mode=DEPLOYMENT_MODE_ZENO_SOVEREIGN_TESTNET_V0,
            chain_id="zeno-ledger-testnet-0",
            accepted_config_digests=[config],
            accepted_sequencer_set_hashes=[sequencer],
            proof_required=False,
            body_required=True,
            tau_net_adapter_required=False,
            token_policy=token_policy,
            bridge_policy=bridge_policy,
        )


def test_tau_exclusive_release_rejects_missing_proof_journal() -> None:
    config = _root("config")
    sequencer = _root("sequencer-set")
    profile = sample_tau_exclusive_release_profile_v0(
        chain_id="zeno-ledger-tau-release-0",
        config_digest=config,
        sequencer_set_hash=sequencer,
        token_symbol="ZENO",
        token_asset_id=_root("zeno-token"),
    )
    checkpoint = _checkpoint(
        chain_id="zeno-ledger-tau-release-0",
        config_digest=config,
        sequencer_set_hash=sequencer,
        proof_journal_hash=ZERO_ROOT_V0,
    )
    with pytest.raises(ValueError, match="proof_journal_hash required"):
        validate_checkpoint_admission_v0(checkpoint=checkpoint, profile=profile)


def test_tau_exclusive_release_quarantines_checkpoint_with_proof_journal() -> None:
    config = _root("config")
    sequencer = _root("sequencer-set")
    profile = sample_tau_exclusive_release_profile_v0(
        chain_id="zeno-ledger-tau-release-0",
        config_digest=config,
        sequencer_set_hash=sequencer,
        token_symbol="ZENO",
        token_asset_id=_root("zeno-token"),
    )
    checkpoint = _checkpoint(
        chain_id="zeno-ledger-tau-release-0",
        config_digest=config,
        sequencer_set_hash=sequencer,
        proof_journal_hash=_root("proof-journal"),
    )
    validate_checkpoint_structural_compatibility_v0(
        checkpoint=checkpoint,
        profile=profile,
    )
    with pytest.raises(ProofRequiredAuthorityErrorV0) as exc_info:
        validate_checkpoint_admission_v0(checkpoint=checkpoint, profile=profile)
    assert exc_info.value.reason is (
        ProofRequiredAuthorityRejectReasonV0
        .AUTHENTICATED_CRYPTOGRAPHIC_AUTHORITY_UNAVAILABLE
    )


def test_tau_exclusive_release_rejects_non_tau_token_deployment() -> None:
    config = _root("config")
    sequencer = _root("sequencer-set")
    token_policy = {
        "token_symbol": "ZENO",
        "token_asset_id": _root("zeno-token"),
        "issuance_scope": TOKEN_SCOPE_NONE_V0,
        "tau_net_exclusive": False,
        "external_minting_allowed": True,
        "non_tau_deployment_allowed": True,
    }
    bridge_policy = {
        "bridge_value_enabled": True,
        "requires_tau_checkpoint": True,
        "requires_proof_journal": True,
    }
    with pytest.raises(ValueError, match="token scope must be tau_net_exclusive"):
        make_zeno_ledger_profile_v0(
            profile_name="bad release",
            deployment_mode=DEPLOYMENT_MODE_TAU_EXCLUSIVE_RELEASE_V0,
            chain_id="zeno-ledger-tau-release-0",
            accepted_config_digests=[config],
            accepted_sequencer_set_hashes=[sequencer],
            proof_required=True,
            body_required=True,
            tau_net_adapter_required=True,
            token_policy=token_policy,
            bridge_policy=bridge_policy,
        )


def test_checkpoint_admission_rejects_unlisted_config_digest() -> None:
    profile = sample_local_sandbox_profile_v0(
        chain_id="zeno-ledger-devnet-0",
        config_digest=_root("config-a"),
        sequencer_set_hash=_root("sequencer-set"),
    )
    checkpoint = _checkpoint(config_digest=_root("config-b"), sequencer_set_hash=_root("sequencer-set"))
    with pytest.raises(ValueError, match="config_digest not admitted"):
        validate_checkpoint_admission_v0(checkpoint=checkpoint, profile=profile)


def test_checkpoint_admission_rejects_chain_id_mismatch() -> None:
    profile = sample_local_sandbox_profile_v0(
        chain_id="zeno-ledger-devnet-0",
        config_digest=_root("config"),
        sequencer_set_hash=_root("sequencer-set"),
    )
    checkpoint = _checkpoint(chain_id="wrong-chain", config_digest=_root("config"), sequencer_set_hash=_root("sequencer-set"))
    with pytest.raises(ValueError, match="chain_id not admitted"):
        validate_checkpoint_admission_v0(checkpoint=checkpoint, profile=profile)


def test_clone_profile_with_new_id_updates_profile_id() -> None:
    profile = sample_local_sandbox_profile_v0(
        chain_id="zeno-ledger-devnet-0",
        config_digest=_root("config"),
        sequencer_set_hash=_root("sequencer-set"),
    )
    cloned = clone_profile_with_new_id_v0(profile, profile_name="renamed sandbox")
    assert cloned["profile_id"] == profile_content_hash_v0(cloned)
    assert cloned["profile_id"] != profile["profile_id"]


def test_make_profile_cli_emits_sovereign_testnet_profile(tmp_path: Path) -> None:
    profile_path = tmp_path / "profile.json"
    proc = _run_make_profile(
        "--mode",
        DEPLOYMENT_MODE_ZENO_SOVEREIGN_TESTNET_V0,
        "--chain-id",
        "zeno-ledger-testnet-0",
        "--config-digest",
        _root("config"),
        "--sequencer-set-hash",
        _root("sequencer-set"),
        "--token-symbol",
        "tZENO",
        "--token-asset-id",
        _root("zeno-test-token"),
        "--out",
        str(profile_path),
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["ok"] is True
    assert report["profile_path"] == str(profile_path)
    profile = json.loads(profile_path.read_text(encoding="utf-8"))
    validate_zeno_ledger_profile_v0(profile)
    assert profile["deployment_mode"] == DEPLOYMENT_MODE_ZENO_SOVEREIGN_TESTNET_V0
    assert profile["tau_net_adapter_required"] is False


def test_make_profile_cli_rejects_tau_release_without_token_asset() -> None:
    proc = _run_make_profile(
        "--mode",
        DEPLOYMENT_MODE_TAU_EXCLUSIVE_RELEASE_V0,
        "--chain-id",
        "zeno-ledger-tau-release-0",
        "--config-digest",
        _root("config"),
        "--sequencer-set-hash",
        _root("sequencer-set"),
        "--token-symbol",
        "ZENO",
    )

    assert proc.returncode == 1
    report = json.loads(proc.stdout)
    assert report["ok"] is False
    assert "token_asset_id" in report["errors"][0]
