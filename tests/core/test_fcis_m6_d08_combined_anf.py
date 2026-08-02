from __future__ import annotations

from dataclasses import replace

import pytest

from experiments.fcis_m6_d08_combined_anf_check import build_instance
from src.core.fcis_m6_d08_combined_anf import (
    D08CombinedANFAcceptV1,
    D08CombinedANFCodeV1,
    D08CombinedANFError,
    D08CombinedANFRejectV1,
    authorized_publication_atom_v1,
    is_verified_combined_anf_accept_v1,
    verify_combined_anf_v1,
)


def _code(value: object) -> D08CombinedANFCodeV1:
    assert type(value) is D08CombinedANFRejectV1
    return value.code


def test_valid_combined_anf_returns_one_canonical_root() -> None:
    instance = build_instance()
    result = verify_combined_anf_v1(instance)
    assert type(result) is D08CombinedANFAcceptV1
    assert result.anf_root == instance.authority_normal_form.root
    assert result.publication_atom == instance.publication_atom


def test_acceptance_retains_complete_instance_for_deterministic_replay() -> None:
    instance = build_instance()
    first = verify_combined_anf_v1(instance)
    assert type(first) is D08CombinedANFAcceptV1

    assert first.instance == instance
    second = verify_combined_anf_v1(first.instance)
    assert type(second) is D08CombinedANFAcceptV1
    assert second is not first
    assert second.anf_root == first.anf_root
    assert second.publication_atom == first.publication_atom
    assert is_verified_combined_anf_accept_v1(first)
    assert authorized_publication_atom_v1(first) == instance.publication_atom


def test_point_of_use_replay_rejects_crossed_retained_instance() -> None:
    instance = build_instance()
    result = verify_combined_anf_v1(instance)
    assert type(result) is D08CombinedANFAcceptV1
    object.__setattr__(
        result,
        "instance",
        replace(instance, decision=instance.base_decision),
    )

    assert not is_verified_combined_anf_accept_v1(result)
    with pytest.raises(D08CombinedANFError, match="replay"):
        authorized_publication_atom_v1(result)


def test_wrong_exact_type_is_typed_rejection() -> None:
    result = verify_combined_anf_v1(object())
    assert _code(result) is D08CombinedANFCodeV1.WRONG_EXACT_TYPE


def test_source_extraction_failure_is_typed_rejection() -> None:
    instance = build_instance()
    result = verify_combined_anf_v1(replace(instance, state_source=object()))
    assert _code(result) is D08CombinedANFCodeV1.SOURCE_EXTRACTION_REJECTED


def test_stage_binding_mutants_are_rejected_at_their_own_boundary() -> None:
    instance = build_instance()
    foreign_tcg = replace(
        instance.tcg_certificate,
        topology_root="f" * 64,
    )
    foreign_c3 = replace(
        instance.authority_normal_form,
        c3_claim_set_root="0x" + "e" * 64,
    )
    proof_context = instance.proof_context
    assert proof_context is not None
    cases = (
        (
            replace(instance, tcg_certificate=foreign_tcg),
            D08CombinedANFCodeV1.TCG_REJECTED,
        ),
        (
            replace(instance, authority_normal_form=foreign_c3),
            D08CombinedANFCodeV1.C3_ROOT_MISMATCH,
        ),
        (
            replace(instance, proof_context=None),
            D08CombinedANFCodeV1.PROOF_CONTEXT_MISMATCH,
        ),
        (
            replace(instance, post_snapshot=instance.pre_snapshot),
            D08CombinedANFCodeV1.POST_HISTORY_MISMATCH,
        ),
        (
            replace(instance, decision=instance.base_decision),
            D08CombinedANFCodeV1.LATER_ROOT_SUBSTITUTION,
        ),
    )
    for candidate, expected_code in cases:
        assert _code(verify_combined_anf_v1(candidate)) is expected_code


def test_tcg_malformed_certificate_does_not_escape_as_an_exception() -> None:
    instance = build_instance()
    object.__setattr__(instance.tcg_certificate, "edges", "malformed")
    assert _code(verify_combined_anf_v1(instance)) is D08CombinedANFCodeV1.TCG_REJECTED
