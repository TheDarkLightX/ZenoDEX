"""Cross-language request vectors for the proof-neutral finality V2 checker."""

from __future__ import annotations

import hashlib

from src.integration._zrpf_spot_v7_checkpoint_finality_checker_codec import (
    _CheckpointFinalityCheckerBindingV1,
    _CheckpointFinalityCheckerInputV1,
    _CheckpointFinalityCheckerPolicyV1,
    _encode_checker_request_v1,
)
from src.integration._zrpf_spot_v7_operational_mechanics import (
    _encode_checkpoint_finality_certificate_v2,
    _finality_certificate_root_v2,
    _TestOnlySpotV7OperationalPolicyV1,
)

_REQUEST_MAGIC_V1 = b"ZRPFCFV2REQV1!!!"
_REQUEST_VERSION_V1 = 1
_POLICY_GENESIS_HASH_OFFSET_V1 = 218
_PRIOR_RECORD_HASH_OFFSET_V1 = 851
_EMPTY_PRIOR_RECORD_BYTES_V1 = 264


def _repeat_root(byte: int) -> str:
    return "0x" + (bytes((byte,)) * 32).hex()


def _position_bytes(tag: int) -> bytes:
    """Return a non-palindromic field witness with every byte position active."""

    return bytes((tag + (17 * index) + (index * index)) % 256 for index in range(32))


def _position_root(tag: int) -> str:
    return "0x" + _position_bytes(tag).hex()


def _root_bytes(value: str) -> bytes:
    raw = bytes.fromhex(value.removeprefix("0x"))
    assert len(raw) == 32
    return raw


def _policy() -> _TestOnlySpotV7OperationalPolicyV1:
    return _TestOnlySpotV7OperationalPolicyV1(
        application_id=_repeat_root(1),
        chain_or_domain_id=_repeat_root(2),
        data_schema_id=_repeat_root(3),
        storage_policy_hash=_repeat_root(4),
        minimum_retention_epochs=20,
        minimum_remaining_epochs=5,
        maximum_blob_bytes=1_024,
        finality_network_id=_repeat_root(6),
        finality_protocol_id=_repeat_root(7),
        external_finality_policy_hash=_repeat_root(8),
        finality_verifier_set_root=_repeat_root(9),
        genesis_application_checkpoint_sequence=41,
        genesis_application_checkpoint_hash=_repeat_root(5),
    )


def _certificate(
    *,
    policy: _TestOnlySpotV7OperationalPolicyV1,
    sequence: int,
    checkpoint_hash: str,
    parent_hash: str,
) -> bytes:
    certificate_root = _finality_certificate_root_v2(
        policy=policy,
        epoch_id=11,
        proof_journal_hash=_repeat_root(3),
        post_state_root=_repeat_root(4),
        sequence=sequence,
        checkpoint_hash=checkpoint_hash,
        parent_hash=parent_hash,
        evidence_root=_repeat_root(10),
        policy_root=policy.checkpoint_finality_policy_root,
    )
    return _encode_checkpoint_finality_certificate_v2(
        policy=policy,
        epoch_id=11,
        proof_journal_hash=_repeat_root(3),
        post_state_root=_repeat_root(4),
        sequence=sequence,
        checkpoint_hash=checkpoint_hash,
        parent_hash=parent_hash,
        evidence_root=_repeat_root(10),
        policy_root=policy.checkpoint_finality_policy_root,
        certificate_root=certificate_root,
    )


def _checker_request(
    *,
    sequence: int,
    checkpoint_hash: str,
    parent_hash: str,
    prior_record: tuple[int, str] | None,
) -> bytes:
    policy = _policy()
    policy_bytes = b"".join(
        (
            _root_bytes(policy.application_id),
            _root_bytes(policy.chain_or_domain_id),
            _root_bytes(policy.finality_network_id),
            _root_bytes(policy.finality_protocol_id),
            _root_bytes(policy.external_finality_policy_hash),
            _root_bytes(policy.finality_verifier_set_root),
            policy.genesis_application_checkpoint_sequence.to_bytes(8, "big"),
            _root_bytes(policy.genesis_application_checkpoint_hash),
        )
    )
    expected_bytes = b"".join(
        (
            _root_bytes(policy.application_id),
            _root_bytes(policy.chain_or_domain_id),
            (11).to_bytes(8, "big"),
            _root_bytes(_repeat_root(3)),
            _root_bytes(_repeat_root(4)),
            sequence.to_bytes(8, "big"),
            _root_bytes(checkpoint_hash),
            _root_bytes(parent_hash),
            _root_bytes(policy.finality_network_id),
            _root_bytes(policy.finality_protocol_id),
            _root_bytes(policy.external_finality_policy_hash),
            _root_bytes(policy.finality_verifier_set_root),
            _root_bytes(_repeat_root(10)),
        )
    )
    if prior_record is None:
        prior_bytes = bytes((0,)) + bytes(_EMPTY_PRIOR_RECORD_BYTES_V1)
    else:
        prior_sequence, prior_hash = prior_record
        record_bytes = b"".join(
            (
                _root_bytes(policy.application_id),
                _root_bytes(policy.chain_or_domain_id),
                _root_bytes(policy.finality_network_id),
                _root_bytes(policy.finality_protocol_id),
                _root_bytes(policy.external_finality_policy_hash),
                _root_bytes(policy.finality_verifier_set_root),
                _root_bytes(policy.checkpoint_finality_policy_root),
                prior_sequence.to_bytes(8, "big"),
                _root_bytes(prior_hash),
            )
        )
        assert len(record_bytes) == _EMPTY_PRIOR_RECORD_BYTES_V1
        prior_bytes = bytes((1,)) + record_bytes
    certificate_bytes = _certificate(
        policy=policy,
        sequence=sequence,
        checkpoint_hash=checkpoint_hash,
        parent_hash=parent_hash,
    )
    request = b"".join(
        (
            _REQUEST_MAGIC_V1,
            _REQUEST_VERSION_V1.to_bytes(2, "big"),
            policy_bytes,
            expected_bytes,
            prior_bytes,
            len(certificate_bytes).to_bytes(2, "big"),
            certificate_bytes,
        )
    )
    assert len(request) == 885 + len(certificate_bytes)
    return request


def _production_checker_input(
    *,
    sequence: int,
    checkpoint_hash: str,
    parent_hash: str,
) -> _CheckpointFinalityCheckerInputV1:
    policy = _policy()
    certificate_bytes = _certificate(
        policy=policy,
        sequence=sequence,
        checkpoint_hash=checkpoint_hash,
        parent_hash=parent_hash,
    )
    certificate_root = _finality_certificate_root_v2(
        policy=policy,
        epoch_id=11,
        proof_journal_hash=_repeat_root(3),
        post_state_root=_repeat_root(4),
        sequence=sequence,
        checkpoint_hash=checkpoint_hash,
        parent_hash=parent_hash,
        evidence_root=_repeat_root(10),
        policy_root=policy.checkpoint_finality_policy_root,
    )
    return _CheckpointFinalityCheckerInputV1(
        policy=_CheckpointFinalityCheckerPolicyV1(
            application_id=_root_bytes(policy.application_id),
            chain_or_domain_id=_root_bytes(policy.chain_or_domain_id),
            finality_network_id=_root_bytes(policy.finality_network_id),
            finality_protocol_id=_root_bytes(policy.finality_protocol_id),
            external_finality_policy_hash=_root_bytes(policy.external_finality_policy_hash),
            finality_verifier_set_root=_root_bytes(policy.finality_verifier_set_root),
            genesis_application_checkpoint_sequence=(
                policy.genesis_application_checkpoint_sequence
            ),
            genesis_application_checkpoint_hash=_root_bytes(
                policy.genesis_application_checkpoint_hash
            ),
        ),
        binding=_CheckpointFinalityCheckerBindingV1(
            application_id=_root_bytes(policy.application_id),
            chain_or_domain_id=_root_bytes(policy.chain_or_domain_id),
            epoch_id=11,
            proof_journal_hash=_root_bytes(_repeat_root(3)),
            post_state_root=_root_bytes(_repeat_root(4)),
            application_checkpoint_sequence=sequence,
            application_checkpoint_hash=_root_bytes(checkpoint_hash),
            parent_application_checkpoint_hash=_root_bytes(parent_hash),
            finality_network_id=_root_bytes(policy.finality_network_id),
            finality_protocol_id=_root_bytes(policy.finality_protocol_id),
            external_finality_policy_hash=_root_bytes(policy.external_finality_policy_hash),
            finality_verifier_set_root=_root_bytes(policy.finality_verifier_set_root),
            finality_evidence_root=_root_bytes(_repeat_root(10)),
            finality_policy_root=_root_bytes(policy.checkpoint_finality_policy_root),
            certificate_root=_root_bytes(certificate_root),
        ),
        exact_certificate_bytes=certificate_bytes,
    )


def _position_distinct_checker_input() -> _CheckpointFinalityCheckerInputV1:
    genesis_sequence = 0x0102_0304_0506_0708
    checkpoint_sequence = genesis_sequence + 2
    epoch_id = 0x1112_1314_1516_1718
    policy = _TestOnlySpotV7OperationalPolicyV1(
        application_id=_position_root(0x11),
        chain_or_domain_id=_position_root(0x22),
        data_schema_id=_position_root(0xD1),
        storage_policy_hash=_position_root(0xD2),
        minimum_retention_epochs=20,
        minimum_remaining_epochs=5,
        maximum_blob_bytes=1_024,
        finality_network_id=_position_root(0x66),
        finality_protocol_id=_position_root(0x77),
        external_finality_policy_hash=_position_root(0x88),
        finality_verifier_set_root=_position_root(0x99),
        genesis_application_checkpoint_sequence=genesis_sequence,
        genesis_application_checkpoint_hash=_position_root(0x55),
    )
    proof_journal_hash = _position_root(0x33)
    post_state_root = _position_root(0x44)
    checkpoint_hash = _position_root(0xBB)
    parent_hash = _position_root(0xAB)
    evidence_root = _position_root(0xAA)
    policy_root = policy.checkpoint_finality_policy_root
    certificate_root = _finality_certificate_root_v2(
        policy=policy,
        epoch_id=epoch_id,
        proof_journal_hash=proof_journal_hash,
        post_state_root=post_state_root,
        sequence=checkpoint_sequence,
        checkpoint_hash=checkpoint_hash,
        parent_hash=parent_hash,
        evidence_root=evidence_root,
        policy_root=policy_root,
    )
    certificate_bytes = _encode_checkpoint_finality_certificate_v2(
        policy=policy,
        epoch_id=epoch_id,
        proof_journal_hash=proof_journal_hash,
        post_state_root=post_state_root,
        sequence=checkpoint_sequence,
        checkpoint_hash=checkpoint_hash,
        parent_hash=parent_hash,
        evidence_root=evidence_root,
        policy_root=policy_root,
        certificate_root=certificate_root,
    )
    return _CheckpointFinalityCheckerInputV1(
        policy=_CheckpointFinalityCheckerPolicyV1(
            application_id=_root_bytes(policy.application_id),
            chain_or_domain_id=_root_bytes(policy.chain_or_domain_id),
            finality_network_id=_root_bytes(policy.finality_network_id),
            finality_protocol_id=_root_bytes(policy.finality_protocol_id),
            external_finality_policy_hash=_root_bytes(policy.external_finality_policy_hash),
            finality_verifier_set_root=_root_bytes(policy.finality_verifier_set_root),
            genesis_application_checkpoint_sequence=genesis_sequence,
            genesis_application_checkpoint_hash=_root_bytes(
                policy.genesis_application_checkpoint_hash
            ),
        ),
        binding=_CheckpointFinalityCheckerBindingV1(
            application_id=_root_bytes(policy.application_id),
            chain_or_domain_id=_root_bytes(policy.chain_or_domain_id),
            epoch_id=epoch_id,
            proof_journal_hash=_root_bytes(proof_journal_hash),
            post_state_root=_root_bytes(post_state_root),
            application_checkpoint_sequence=checkpoint_sequence,
            application_checkpoint_hash=_root_bytes(checkpoint_hash),
            parent_application_checkpoint_hash=_root_bytes(parent_hash),
            finality_network_id=_root_bytes(policy.finality_network_id),
            finality_protocol_id=_root_bytes(policy.finality_protocol_id),
            external_finality_policy_hash=_root_bytes(policy.external_finality_policy_hash),
            finality_verifier_set_root=_root_bytes(policy.finality_verifier_set_root),
            finality_evidence_root=_root_bytes(evidence_root),
            finality_policy_root=_root_bytes(policy_root),
            certificate_root=_root_bytes(certificate_root),
        ),
        exact_certificate_bytes=certificate_bytes,
    )


def test_production_encoder_uses_canonical_empty_prior_at_genesis() -> None:
    expected = _checker_request(
        sequence=42,
        checkpoint_hash=_repeat_root(11),
        parent_hash=_repeat_root(5),
        prior_record=None,
    )
    observed = _encode_checker_request_v1(
        _production_checker_input(
            sequence=42,
            checkpoint_hash=_repeat_root(11),
            parent_hash=_repeat_root(5),
        )
    )

    assert observed == expected


def test_production_encoder_uses_canonical_prior_record_above_genesis() -> None:
    expected = _checker_request(
        sequence=43,
        checkpoint_hash=_repeat_root(12),
        parent_hash=_repeat_root(11),
        prior_record=(42, _repeat_root(11)),
    )
    observed = _encode_checker_request_v1(
        _production_checker_input(
            sequence=43,
            checkpoint_hash=_repeat_root(12),
            parent_hash=_repeat_root(11),
        )
    )

    assert observed == expected


def test_position_distinct_vector_activates_field_order_byte_order_and_cursor_tag() -> None:
    """Pair with Rust's fixed digest so round trips cannot mask representation drift."""

    request = _encode_checker_request_v1(_position_distinct_checker_input())

    assert len(request) == 1_320
    assert request[18:50] == _position_bytes(0x11)
    assert request[18:50] != request[18:50][::-1]
    assert request[210:218] == bytes.fromhex("0102030405060708")
    assert request[314:322] == bytes.fromhex("1112131415161718")
    assert request[618] == 1
    assert request[843:851] == bytes.fromhex("0102030405060709")
    assert hashlib.sha256(request).hexdigest() == (
        "5c6a7d9c69037d53cb4d647a597a99d92db078186ba9a43f54cc4714ba27ad36"
    )


def test_python_vectors_match_rust_nonzero_and_zero_boundary_vectors() -> None:
    """The paired Rust test executes acceptance and typed rejection."""

    nonzero_genesis = _checker_request(
        sequence=42,
        checkpoint_hash=_repeat_root(11),
        parent_hash=_repeat_root(5),
        prior_record=None,
    )
    assert len(nonzero_genesis) == 1_304
    assert hashlib.sha256(nonzero_genesis).hexdigest() == (
        "39bbe96f57abd64637dfa90db85b2c724e4d8d49dae1a88c7f8b7a58a3675809"
    )

    zero_genesis = bytearray(nonzero_genesis)
    zero_genesis[_POLICY_GENESIS_HASH_OFFSET_V1 : _POLICY_GENESIS_HASH_OFFSET_V1 + 32] = bytes(32)
    assert hashlib.sha256(zero_genesis).hexdigest() == (
        "35bfe80dd3ec8d27005d578ec88eb0a18e20a797377357180d82af49255cfcc4"
    )

    nonzero_prior = _checker_request(
        sequence=43,
        checkpoint_hash=_repeat_root(12),
        parent_hash=_repeat_root(11),
        prior_record=(42, _repeat_root(11)),
    )
    assert hashlib.sha256(nonzero_prior).hexdigest() == (
        "0b2444d39e04086c2e4cadcc8a1bc117ad6a519ef516ccfed5b7c9b502dd84bb"
    )

    zero_prior_above_genesis = bytearray(nonzero_prior)
    zero_prior_above_genesis[_PRIOR_RECORD_HASH_OFFSET_V1 : _PRIOR_RECORD_HASH_OFFSET_V1 + 32] = (
        bytes(32)
    )
    assert hashlib.sha256(zero_prior_above_genesis).hexdigest() == (
        "df6f34074ca16d722b30f5e05483ec54218fb2870bedc498e8ca0cd756195051"
    )
