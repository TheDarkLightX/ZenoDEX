"""E02 nonce/nullifier relation tests."""

from __future__ import annotations

import json
from typing import cast

import pytest

from experiments.fcis_m6_e02_nonce_nullifier_check import _identity_from_vector, run_checks
from src.core import fcis_m6_e02_nonce_nullifier as e02
from src.core.fcis_m6_e01_request_identity import (
    E01CommandFamilyV1,
    _mint_authenticated_command_v1,
    derive_request_identity_v1,
)
from src.core.fcis_m6_e02_nonce_nullifier import (
    MAX_E02_CURRENT_NONCE_V1,
    MAX_E02_U64_V1,
    E02Error,
    E02NullifierV1,
    derive_nonce_nullifier_v1,
    is_verified_nullifier_v1,
    nullifier_root_from_body_v1,
)


def _payload() -> dict[str, object]:
    with open(
        "docs/research/m6_tasks/TASK_E02_NONCE_NULLIFIER_V1.json",
        encoding="utf-8",
    ) as handle:
        value = json.load(handle)
    assert type(value) is dict
    return cast(dict[str, object], value)


def test_e02_checker_passes() -> None:
    run_checks()


def test_next_nonce_relation_and_overflow_are_fail_closed() -> None:
    identity = _identity_from_vector()
    current_nonce = cast(int, _payload()["current_nonce"])
    assert (
        derive_nonce_nullifier_v1(
            request_identity=identity,
            current_nonce=current_nonce,
        ).nonce
        == current_nonce + 1
    )
    for invalid in (current_nonce - 1, current_nonce + 1, MAX_E02_CURRENT_NONCE_V1):
        with pytest.raises(E02Error):
            derive_nonce_nullifier_v1(request_identity=identity, current_nonce=invalid)


def test_zero_and_maximum_next_nonce_boundaries_are_explicit() -> None:
    identity = _identity_from_vector()
    low_command = _mint_authenticated_command_v1(
        command_root="1" * 64,
        sender_id=identity.sender_id,
        command_family=identity.command_family,
        nonce=1,
        authentication_profile_root=identity.authentication_profile_root,
        authentication_evidence_root="2" * 64,
    )
    low_identity = derive_request_identity_v1(
        authenticated_command=low_command,
        deployment_config_root=identity.deployment_config_root,
        expected_sequence=identity.expected_sequence,
        authority_epoch_index=identity.authority_epoch_index,
    )
    assert derive_nonce_nullifier_v1(request_identity=low_identity, current_nonce=0).nonce == 1

    high_command = _mint_authenticated_command_v1(
        command_root="3" * 64,
        sender_id=identity.sender_id,
        command_family=identity.command_family,
        nonce=MAX_E02_U64_V1,
        authentication_profile_root=identity.authentication_profile_root,
        authentication_evidence_root="4" * 64,
    )
    high_identity = derive_request_identity_v1(
        authenticated_command=high_command,
        deployment_config_root=identity.deployment_config_root,
        expected_sequence=identity.expected_sequence,
        authority_epoch_index=identity.authority_epoch_index,
    )
    assert (
        derive_nonce_nullifier_v1(
            request_identity=high_identity,
            current_nonce=MAX_E02_CURRENT_NONCE_V1,
        ).nonce
        == MAX_E02_U64_V1
    )


def test_nullifier_root_binds_each_preimage_axis_and_rejects_open_fields() -> None:
    identity = _identity_from_vector()
    nullifier = derive_nonce_nullifier_v1(request_identity=identity, current_nonce=6)
    body = nullifier.preimage_body()
    root = nullifier_root_from_body_v1(body)
    assert root == nullifier.nullifier_root
    for field, changed in (
        ("deployment_config_root", "f" * 64),
        ("sender_id", "mallory"),
        ("nonce", 8),
        ("command_family", E01CommandFamilyV1.MIGRATION.value),
    ):
        candidate = dict(body)
        candidate[field] = changed
        assert nullifier_root_from_body_v1(candidate) != root
    with pytest.raises(E02Error):
        nullifier_root_from_body_v1({**body, "extra": "rejected"})
    with pytest.raises(E02Error):
        nullifier_root_from_body_v1({**body, "nonce": True})


def test_nullifier_witness_is_verifier_owned_and_mutation_invalidates_it() -> None:
    identity = _identity_from_vector()
    nullifier = derive_nonce_nullifier_v1(request_identity=identity, current_nonce=6)
    assert is_verified_nullifier_v1(nullifier)
    replayed_copy = object.__new__(E02NullifierV1)
    object.__setattr__(replayed_copy, "request_identity", nullifier.request_identity)
    object.__setattr__(replayed_copy, "current_nonce", nullifier.current_nonce)
    object.__setattr__(replayed_copy, "nullifier_root", nullifier.nullifier_root)
    assert is_verified_nullifier_v1(replayed_copy)

    object.__setattr__(nullifier, "current_nonce", nullifier.current_nonce - 1)
    assert not is_verified_nullifier_v1(nullifier)


def test_point_of_use_verification_replays_retained_sources_without_registry() -> None:
    identity = _identity_from_vector()
    current_nonce = cast(int, _payload()["current_nonce"])
    nullifier = derive_nonce_nullifier_v1(
        request_identity=identity,
        current_nonce=current_nonce,
    )

    assert nullifier.request_identity is identity
    assert nullifier.current_nonce == current_nonce

    for name in ("_E02_NULLIFIERS_V1", "_E02_NULLIFIER_SNAPSHOTS_V1"):
        registry = getattr(e02, name, None)
        if registry is not None:
            registry.clear()

    assert is_verified_nullifier_v1(nullifier)
