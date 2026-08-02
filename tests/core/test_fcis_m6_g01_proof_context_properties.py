"""Property-style G01 proof-context identity tests."""

from __future__ import annotations

import hypothesis.strategies as st
from hypothesis import given, settings

from experiments.fcis_m6_g01_proof_context_check import build_context
from src.core.fcis_durable_retraction import tagged_digest
from src.core.fcis_m6_g01_proof_context import (
    G01ProofContextCodeV1,
    G01ProofContextRejectV1,
    validate_g01_proof_context_v1,
)

_LABELS = st.text(
    alphabet=st.characters(
        whitelist_categories=("Ll", "Lu", "Nd"),
        whitelist_characters="_-",
    ),
    min_size=1,
    max_size=24,
)


@settings(max_examples=24, deadline=None, derandomize=True)  # type: ignore[untyped-decorator]
@given(label=_LABELS)  # type: ignore[untyped-decorator]
def test_generated_state_root_substitutions_fail_context_root_revalidation(label: str) -> None:
    context = build_context()
    object.__setattr__(context, "state_root", f"0x{tagged_digest('g01/property/' + label)}")

    result = validate_g01_proof_context_v1(context)

    assert type(result) is G01ProofContextRejectV1
    assert result.code is G01ProofContextCodeV1.CONTEXT_ROOT_MISMATCH
