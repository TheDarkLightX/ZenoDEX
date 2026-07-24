from __future__ import annotations

from copy import deepcopy

import pytest

from src.core.dex import DexConfig
from src.integration.dex_engine import DexEngineConfig
from src.integration.zeno_ledger_proof_authority_consumer_v1 import (
    GovernedProofAuthorityBindingV1,
    make_governed_proof_authority_binding_v1,
)
from src.integration.zeno_ledger_replay import (
    REPLAY_ENGINE_CONFIG_PROFILE_V1,
    REPLAY_ENGINE_CONFIG_SCHEMA_V1,
    parse_replay_engine_config_v1,
    replay_engine_config_digest_v1,
    replay_engine_config_document_v1,
)


def _policy(*, chain_id: str = "tau-test") -> GovernedProofAuthorityBindingV1:
    return make_governed_proof_authority_binding_v1(
        chain_id=chain_id,
        authority_manifest_sha256="11" * 32,
        verifier_registry_id="0x" + "22" * 32,
        verifier_registry_entry_id="0x" + "33" * 32,
        valid_from_height=1,
        valid_until_height=10,
    )


def _document() -> dict[str, object]:
    return replay_engine_config_document_v1(
        DexEngineConfig(chain_id="tau-test"),
        proof_authority_policy=_policy(),
    )


def test_config_v1_round_trips_complete_cycle_free_policy() -> None:
    document = _document()

    config, policy, canonical = parse_replay_engine_config_v1(document)

    assert canonical == document
    assert config.chain_id == "tau-test"
    assert policy.policy_id == (
        "0xa33a534c7c1b17e49e8710a904849ec0db74e150ab579cf37c0b434447606825"
    )
    assert document["schema"] == REPLAY_ENGINE_CONFIG_SCHEMA_V1
    assert document["profile"] == REPLAY_ENGINE_CONFIG_PROFILE_V1
    assert replay_engine_config_digest_v1(document) == (
        "0x5f5869a1291ea7b17b57bb07d1394ad9ba880f202725755b8995226c3938415f"
    )


def test_config_v1_rejects_unknown_top_level_or_policy_fields() -> None:
    document = _document()
    expanded = deepcopy(document)
    expanded["proof_verified"] = True
    with pytest.raises(ValueError, match="config V1 keys mismatch"):
        parse_replay_engine_config_v1(expanded)

    expanded_policy = deepcopy(document)
    policy = expanded_policy["proof_authority_policy"]
    assert isinstance(policy, dict)
    policy["accepted"] = True
    with pytest.raises(ValueError, match="binding keys mismatch"):
        parse_replay_engine_config_v1(expanded_policy)


def test_config_v1_rejects_policy_id_or_chain_substitution() -> None:
    document = _document()
    wrong_policy = deepcopy(document)
    policy = wrong_policy["proof_authority_policy"]
    assert isinstance(policy, dict)
    policy["policy_id"] = "0x" + "44" * 32
    with pytest.raises(ValueError, match="policy_id mismatch"):
        parse_replay_engine_config_v1(wrong_policy)

    with pytest.raises(ValueError, match="chain_id does not match"):
        replay_engine_config_document_v1(
            DexEngineConfig(chain_id="tau-test"),
            proof_authority_policy=_policy(chain_id="other-chain"),
        )


def test_config_v1_rejects_v0_projection_or_wrong_hash_domain() -> None:
    document = _document()
    projected = {key: value for key, value in document.items() if key != "proof_authority_policy"}
    projected["schema"] = "zenodex/zeno_ledger/replay_engine_config/v0"
    projected["profile"] = "bounded_dex_engine_v0"

    with pytest.raises(ValueError, match="config V1 keys mismatch"):
        parse_replay_engine_config_v1(projected)
    policy = document["proof_authority_policy"]
    assert isinstance(policy, dict)
    assert replay_engine_config_digest_v1(document) != policy["policy_id"]


def test_config_v1_matches_rust_u64_and_ascii_boundaries() -> None:
    max_u64_policy = make_governed_proof_authority_binding_v1(
        chain_id="tau-test",
        authority_manifest_sha256="11" * 32,
        verifier_registry_id="0x" + "22" * 32,
        verifier_registry_entry_id="0x" + "33" * 32,
        valid_from_height=(1 << 64) - 1,
        valid_until_height=(1 << 64) - 1,
    )
    max_u64_document = replay_engine_config_document_v1(
        DexEngineConfig(
            chain_id="tau-test",
            min_lp_position_age_seconds=(1 << 64) - 1,
        ),
        proof_authority_policy=max_u64_policy,
    )
    max_u64_config, parsed_policy, _canonical = parse_replay_engine_config_v1(
        max_u64_document
    )
    assert max_u64_config.min_lp_position_age_seconds == (1 << 64) - 1
    assert parsed_policy.valid_until_height == (1 << 64) - 1

    document = _document()
    oversized_config = deepcopy(document)
    config = oversized_config["config"]
    assert isinstance(config, dict)
    config["min_lp_position_age_seconds"] = 1 << 64
    with pytest.raises(ValueError, match="must fit in a u64"):
        parse_replay_engine_config_v1(oversized_config)

    with pytest.raises(ValueError, match="must be a u64"):
        make_governed_proof_authority_binding_v1(
            chain_id="tau-test",
            authority_manifest_sha256="11" * 32,
            verifier_registry_id="0x" + "22" * 32,
            verifier_registry_entry_id="0x" + "33" * 32,
            valid_from_height=1,
            valid_until_height=1 << 64,
        )

    with pytest.raises(ValueError, match="only ASCII"):
        replay_engine_config_document_v1(
            DexEngineConfig(
                chain_id="tau-test",
                dex_config=DexConfig(protocol_fee_recipient_pubkey="café"),
            ),
            proof_authority_policy=_policy(),
        )

    unicode_document = deepcopy(document)
    unicode_config = unicode_document["config"]
    assert isinstance(unicode_config, dict)
    dex_config = unicode_config["dex_config"]
    assert isinstance(dex_config, dict)
    dex_config["protocol_fee_recipient_pubkey"] = "café"
    with pytest.raises(ValueError, match="only ASCII"):
        parse_replay_engine_config_v1(unicode_document)


def test_governed_policy_token_boundary_is_explicit() -> None:
    accepted = make_governed_proof_authority_binding_v1(
        chain_id="a" * 256,
        authority_manifest_sha256="11" * 32,
        verifier_registry_id="0x" + "22" * 32,
        verifier_registry_entry_id="0x" + "33" * 32,
        valid_from_height=0,
        valid_until_height=0,
    )
    assert len(accepted.chain_id) == 256

    with pytest.raises(ValueError, match="bounded str"):
        make_governed_proof_authority_binding_v1(
            chain_id="a" * 257,
            authority_manifest_sha256="11" * 32,
            verifier_registry_id="0x" + "22" * 32,
            verifier_registry_entry_id="0x" + "33" * 32,
            valid_from_height=0,
            valid_until_height=0,
        )
