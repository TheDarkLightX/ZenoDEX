"""Focused G01 proof-context value tests."""

from __future__ import annotations

from experiments.fcis_m6_g01_proof_context_check import build_context
from src.core.fcis_m6_g01_proof_context import (
    G01ProofContextCodeV1,
    G01ProofContextRejectV1,
    G01ProofContextV1,
    validate_g01_proof_context_v1,
)


def test_context_root_and_wire_projection_are_deterministic() -> None:
    context = build_context()

    assert context.context_root == context.recomputed_root
    assert context.to_wire()["value"]["context_root"] == context.context_root
    assert validate_g01_proof_context_v1(context, at_epoch=7) == context


def test_context_epoch_boundaries_are_closed() -> None:
    context = build_context()

    assert validate_g01_proof_context_v1(context, at_epoch=5) == context
    assert validate_g01_proof_context_v1(context, at_epoch=10) == context
    before = validate_g01_proof_context_v1(context, at_epoch=4)
    after = validate_g01_proof_context_v1(context, at_epoch=11)
    assert type(before) is G01ProofContextRejectV1
    assert type(after) is G01ProofContextRejectV1
    assert before.code is G01ProofContextCodeV1.NOT_ACTIVE
    assert after.code is G01ProofContextCodeV1.NOT_ACTIVE


def test_context_revalidation_detects_hostile_state_mutation() -> None:
    context = build_context()
    object.__setattr__(context, "state_root", "0x" + "f" * 64)

    result = validate_g01_proof_context_v1(context)

    assert type(result) is G01ProofContextRejectV1
    assert result.code is G01ProofContextCodeV1.CONTEXT_ROOT_MISMATCH


def test_context_revalidation_rejects_incomplete_exact_object() -> None:
    incomplete = object.__new__(G01ProofContextV1)

    result = validate_g01_proof_context_v1(incomplete)

    assert type(result) is G01ProofContextRejectV1
    assert result.code is G01ProofContextCodeV1.INVALID_TEXT


def test_context_revalidation_rejects_wrong_exact_type_and_boolean_epoch() -> None:
    wrong = validate_g01_proof_context_v1(object())
    boolean_epoch = validate_g01_proof_context_v1(build_context(), at_epoch=True)

    assert type(wrong) is G01ProofContextRejectV1
    assert wrong.code is G01ProofContextCodeV1.WRONG_EXACT_TYPE
    assert type(boolean_epoch) is G01ProofContextRejectV1
    assert boolean_epoch.code is G01ProofContextCodeV1.INVALID_EPOCH
