from __future__ import annotations

import importlib.util
import sys
from typing import Any

import pytest

if importlib.util.find_spec("hypothesis") is None:  # pragma: no cover
    pytest.skip("hypothesis not installed", allow_module_level=True)

import hypothesis.strategies as st
from hypothesis import given, settings

from src.integration.proof_verifier import SubprocessProofVerifier
from src.state.canonical import canonical_json_bytes

ALPHABET = "abcdefghijklmnopqrstuvwxyz0123456789_-"
TEXT = st.text(ALPHABET, min_size=0, max_size=16)
NON_EMPTY_TEXT = st.text(ALPHABET, min_size=1, max_size=16)

JSON_VALUE: st.SearchStrategy[Any] = st.recursive(
    st.none() | st.booleans() | st.integers(min_value=-10_000, max_value=10_000) | TEXT,
    lambda child: st.lists(child, max_size=3) | st.dictionaries(NON_EMPTY_TEXT, child, max_size=3),
    max_leaves=12,
)

JSON_OBJECT = st.dictionaries(NON_EMPTY_TEXT, JSON_VALUE, max_size=6)
ECHO_VERIFIER_CMD = [
    sys.executable,
    "-c",
    "import json,sys; json.load(sys.stdin); json.dump({'ok': True}, sys.stdout)",
]


@given(payload=JSON_OBJECT)
@settings(max_examples=40, deadline=None, derandomize=True)
def test_subprocess_proof_verifier_accepts_generated_json_payload_objects(payload: dict[str, Any]) -> None:
    verifier = SubprocessProofVerifier(
        cmd=ECHO_VERIFIER_CMD,
        timeout_s=1.0,
        max_bytes=16_384,
        max_stdout_bytes=512,
        max_stderr_bytes=512,
    )
    assert verifier.verify(payload) == (True, None)


@given(payload=JSON_OBJECT)
@settings(max_examples=40, deadline=None, derandomize=True)
def test_subprocess_proof_verifier_fail_closes_when_generated_payload_exceeds_limit(payload: dict[str, Any]) -> None:
    verifier = SubprocessProofVerifier(
        cmd=ECHO_VERIFIER_CMD,
        timeout_s=1.0,
        max_bytes=max(1, len(canonical_json_bytes(payload)) - 1),
        max_stdout_bytes=512,
        max_stderr_bytes=512,
    )
    assert verifier.verify(payload) == (False, "proof payload too large")
