from __future__ import annotations

import dataclasses

import pytest

from src.integration.zeno_ledger_profile import (
    sample_zeno_sovereign_testnet_profile_v0,
)
from src.integration.zeno_ledger_proof_authority_consumer_v1 import (
    PROOF_AUTHORITY_OBLIGATION_ID_V1,
    GovernedProofAuthorityBindingV1,
    ProofAuthorityConsumerError,
    ProofAuthorityConsumerRejectReasonV1,
    ProofAuthorityDecisionStatusV1,
    ProofAuthorityDecisionV1,
    make_governed_proof_authority_binding_v1,
    make_proof_authority_requirement_v1,
    resolve_proof_authority_v1,
)
from src.integration.zeno_ledger_v0 import hash_v0


def _root(label: str) -> str:
    return hash_v0("proof_authority_consumer_test_v1", {"label": label})


def _profile(*, proof_required: bool) -> dict[str, object]:
    return sample_zeno_sovereign_testnet_profile_v0(
        chain_id="zeno-proof-authority-test-0",
        config_digest=_root("config"),
        sequencer_set_hash=_root("sequencers"),
        token_symbol="tZENO",
        token_asset_id=_root("token"),
        proof_required=proof_required,
    )


def _binding(
    profile: dict[str, object],
    *,
    valid_from_height: int = 4,
    valid_until_height: int | None = 8,
) -> GovernedProofAuthorityBindingV1:
    return make_governed_proof_authority_binding_v1(
        chain_id=str(profile["chain_id"]),
        authority_manifest_sha256="11" * 32,
        verifier_registry_id=_root("registry"),
        verifier_registry_entry_id=_root("registry-entry"),
        valid_from_height=valid_from_height,
        valid_until_height=valid_until_height,
    )


def test_non_proof_profile_resolves_to_exact_not_required_decision() -> None:
    profile = _profile(proof_required=False)
    requirement = make_proof_authority_requirement_v1(
        profile=profile,
        replay_config_digest=_root("config"),
        expected_policy_id=None,
        from_height=4,
        to_height=4,
    )

    decision = resolve_proof_authority_v1(
        requirement=requirement,
        governed_binding=None,
        authenticated_result=None,
    )

    assert decision.status is ProofAuthorityDecisionStatusV1.NOT_REQUIRED
    assert decision.required is False
    assert decision.satisfied is False
    assert decision.capable is False
    assert decision.pending_report() is None


def test_proof_required_profile_returns_typed_pending_obligation() -> None:
    profile = _profile(proof_required=True)
    requirement = make_proof_authority_requirement_v1(
        profile=profile,
        replay_config_digest=_root("config"),
        expected_policy_id=None,
        from_height=4,
        to_height=8,
    )

    decision = resolve_proof_authority_v1(
        requirement=requirement,
        governed_binding=None,
        authenticated_result=None,
    )

    assert decision.status is ProofAuthorityDecisionStatusV1.REQUIRED_PENDING
    assert decision.required is True
    assert decision.satisfied is False
    assert decision.capable is False
    pending = decision.pending_report()
    assert pending is not None
    assert pending["obligation_id"] == PROOF_AUTHORITY_OBLIGATION_ID_V1
    assert pending["profile_id"] == profile["profile_id"]
    assert pending["from_height"] == 4
    assert pending["to_height"] == 8
    assert pending["missing_bindings"] == [
        "authenticated_strict_verifier_result",
        "consensus_bound_authority_manifest_sha256",
        "consensus_bound_proof_authority_policy_id",
        "consensus_bound_verifier_registry_id",
    ]


def test_structural_profile_pending_obligation_names_missing_replay_config() -> None:
    profile = _profile(proof_required=True)
    requirement = make_proof_authority_requirement_v1(
        profile=profile,
        replay_config_digest=None,
        expected_policy_id=None,
        from_height=4,
        to_height=4,
    )

    decision = resolve_proof_authority_v1(
        requirement=requirement,
        governed_binding=None,
        authenticated_result=None,
    )

    pending = decision.pending_report()
    assert pending is not None
    missing_bindings = pending["missing_bindings"]
    assert isinstance(missing_bindings, list)
    assert "replay_config_digest" in missing_bindings
    assert pending["replay_config_digest"] is None


def test_fabricated_boolean_mapping_cannot_satisfy_authority() -> None:
    profile = _profile(proof_required=True)
    binding = _binding(profile)
    requirement = make_proof_authority_requirement_v1(
        profile=profile,
        replay_config_digest=_root("config"),
        expected_policy_id=binding.policy_id,
        from_height=4,
        to_height=8,
    )

    with pytest.raises(ProofAuthorityConsumerError) as caught:
        resolve_proof_authority_v1(
            requirement=requirement,
            governed_binding=binding,
            authenticated_result={"accepted": True, "risc0_verified": True},
        )

    assert (
        caught.value.reason
        is ProofAuthorityConsumerRejectReasonV1.AUTHENTICATED_RESULT_TYPE_INVALID
    )


def test_fabricated_result_without_governed_binding_rejects() -> None:
    profile = _profile(proof_required=True)
    requirement = make_proof_authority_requirement_v1(
        profile=profile,
        replay_config_digest=_root("config"),
        expected_policy_id=None,
        from_height=4,
        to_height=8,
    )

    with pytest.raises(ProofAuthorityConsumerError) as caught:
        resolve_proof_authority_v1(
            requirement=requirement,
            governed_binding=None,
            authenticated_result={"accepted": True},
        )

    assert (
        caught.value.reason
        is ProofAuthorityConsumerRejectReasonV1.AUTHENTICATED_RESULT_TYPE_INVALID
    )


def test_governed_binding_rejects_wrong_committed_policy() -> None:
    profile = _profile(proof_required=True)
    binding = _binding(profile)
    requirement = make_proof_authority_requirement_v1(
        profile=profile,
        replay_config_digest=_root("config"),
        expected_policy_id=_root("different-policy"),
        from_height=4,
        to_height=8,
    )

    with pytest.raises(ProofAuthorityConsumerError) as caught:
        resolve_proof_authority_v1(
            requirement=requirement,
            governed_binding=binding,
            authenticated_result=None,
        )

    assert caught.value.reason is ProofAuthorityConsumerRejectReasonV1.POLICY_MISMATCH


def test_governed_binding_rejects_stale_policy_for_range() -> None:
    profile = _profile(proof_required=True)
    binding = _binding(profile, valid_until_height=7)
    requirement = make_proof_authority_requirement_v1(
        profile=profile,
        replay_config_digest=_root("config"),
        expected_policy_id=binding.policy_id,
        from_height=4,
        to_height=8,
    )

    with pytest.raises(ProofAuthorityConsumerError) as caught:
        resolve_proof_authority_v1(
            requirement=requirement,
            governed_binding=binding,
            authenticated_result=None,
        )

    assert caught.value.reason is ProofAuthorityConsumerRejectReasonV1.POLICY_STALE


def test_governed_binding_rejects_not_yet_valid_policy_for_range() -> None:
    profile = _profile(proof_required=True)
    binding = _binding(profile, valid_from_height=5)
    requirement = make_proof_authority_requirement_v1(
        profile=profile,
        replay_config_digest=_root("config"),
        expected_policy_id=binding.policy_id,
        from_height=4,
        to_height=8,
    )

    with pytest.raises(ProofAuthorityConsumerError) as caught:
        resolve_proof_authority_v1(
            requirement=requirement,
            governed_binding=binding,
            authenticated_result=None,
        )

    assert caught.value.reason is ProofAuthorityConsumerRejectReasonV1.POLICY_NOT_YET_VALID


def test_policy_id_tamper_rejects_during_construction() -> None:
    profile = _profile(proof_required=True)
    binding = _binding(profile)

    with pytest.raises(ValueError, match="policy_id mismatch"):
        dataclasses.replace(binding, policy_id=_root("tampered-policy"))


def test_governed_binding_rejects_schema_or_profile_substitution() -> None:
    binding = _binding(_profile(proof_required=True))

    with pytest.raises(ValueError, match="strict result schema mismatch"):
        dataclasses.replace(binding, strict_result_schema="caller.result.v1")
    with pytest.raises(ValueError, match="proof profile mismatch"):
        dataclasses.replace(binding, proof_profile="caller_proof_profile")


def test_decision_has_no_public_construction_path() -> None:
    with pytest.raises(TypeError, match="private seal"):
        ProofAuthorityDecisionV1(
            ProofAuthorityDecisionStatusV1.SATISFIED,
            None,
            seal=object(),
        )
