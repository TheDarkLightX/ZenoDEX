from __future__ import annotations

from dataclasses import replace

from experiments.fcis_m6_d08_combined_anf_check import build_instance
from src.core.fcis_m6_d08_combined_anf import (
    D08CombinedANFAcceptV1,
    D08CombinedANFCodeV1,
    D08CombinedANFRejectV1,
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
