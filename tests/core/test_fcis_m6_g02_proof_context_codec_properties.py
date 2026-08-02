"""Property-style mutation tests for the G02 proof-context codec."""

from __future__ import annotations

import hypothesis.strategies as st
from hypothesis import given, settings

from experiments.fcis_m6_g02_proof_context_check import build_context
from src.core.fcis_durable_retraction import tagged_digest
from src.core.fcis_m6_g02_proof_context_codec import (
    G02ProofContextCodeV1,
    G02ProofContextRejectV1,
    decode_g02_proof_context_v1,
    encode_g02_proof_context_v1,
)

_LABELS = st.text(
    alphabet=st.characters(
        whitelist_categories=("Ll", "Lu", "Nd"),
        whitelist_characters="_-",
    ),
    min_size=1,
    max_size=32,
)


@settings(max_examples=24, deadline=None, derandomize=True)  # type: ignore[untyped-decorator]
@given(label=_LABELS)  # type: ignore[untyped-decorator]
def test_generated_state_root_substitutions_reject_without_new_context_root(
    label: str,
) -> None:
    context = build_context()
    encoded = encode_g02_proof_context_v1(context)
    replacement = f"0x{tagged_digest(f'g02/property/{label}')}"
    mutated = encoded.replace(context.state_root.encode("ascii"), replacement.encode("ascii"), 1)

    result = decode_g02_proof_context_v1(mutated)

    assert type(result) is G02ProofContextRejectV1
    assert result.code is G02ProofContextCodeV1.CONTEXT_REJECTED


@settings(max_examples=24, deadline=None, derandomize=True)  # type: ignore[untyped-decorator]
@given(label=_LABELS)  # type: ignore[untyped-decorator]
def test_generated_trailing_bytes_reject_as_invalid_frame(label: str) -> None:
    encoded = encode_g02_proof_context_v1(build_context())
    result = decode_g02_proof_context_v1(encoded + label.encode("utf-8"))

    assert type(result) is G02ProofContextRejectV1
    assert result.code is G02ProofContextCodeV1.INVALID_FRAME
