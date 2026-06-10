"""Property-based fail-closed invariants for the admitted median_3 verifier.

These assert global properties the deterministic chaos lane samples pointwise:

1. garbage objects never accept and never raise uncontrolled;
2. mutating any single content-bound top-level field never spuriously accepts;
3. the median_3 arithmetic helper always returns the middle of three values;
4. a single signing key can never supply two of the three median inputs, no
   matter which pair collides (the quorum's independence is a property of the
   signing key, not the self-chosen reporter_id label).
"""

from __future__ import annotations

import copy
import importlib.util
from pathlib import Path
import sys

import pytest

if importlib.util.find_spec("hypothesis") is None:  # pragma: no cover
    pytest.skip("hypothesis not installed", allow_module_level=True)

import hypothesis.strategies as st
from hypothesis import assume, given, settings

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "tools"))
sys.path.insert(0, str(REPO))

from zenodex_oracle_admitted_median3 import (  # noqa: E402
    _canonical_pubkey,
    _confidence,
    _median3,
    _single_report_admission,
    aggregate_content_hash,
    sample_admitted_median3_aggregate,
    verify_admitted_median3_aggregate,
)


# A honest accepted aggregate is expensive to build (real BLS signing), so build
# it once and deep-copy per example.
_HONEST_AGGREGATE = sample_admitted_median3_aggregate()


def _assert_honest_baseline() -> None:
    result = verify_admitted_median3_aggregate(copy.deepcopy(_HONEST_AGGREGATE))
    assert result.status == "accepted"
    assert result.distinct_reporter_pubkey_count == 3


_json_values = st.recursive(
    st.none()
    | st.booleans()
    | st.integers(min_value=-(10**9), max_value=10**9)
    | st.text(max_size=8),
    lambda children: st.lists(children, max_size=4)
    | st.dictionaries(st.text(max_size=6), children, max_size=4),
    max_leaves=12,
)


@settings(max_examples=200)
@given(
    obj=st.dictionaries(
        st.one_of(st.text(max_size=8), st.integers(min_value=0, max_value=5)),
        _json_values,
        max_size=8,
    )
)
def test_admitted_median3_garbage_never_accepts_never_raises(obj: dict) -> None:
    # The pure verifier consumes a parsed JSON object. Arbitrary objects (incl.
    # non-string keys, which canonical encoding rejects) must fail closed with a
    # result, never an uncaught exception, and never an acceptance.
    result = verify_admitted_median3_aggregate(obj)
    assert result.status in {"rejected", "inconclusive", "accepted"}
    assert result.status != "accepted"
    assert result.errors  # a rejection must name at least one reason


@settings(max_examples=75)
@given(
    key=st.sampled_from(
        [
            "schema",
            "query_id",
            "current_epoch",
            "max_staleness_epochs",
            "evidence_floor",
            "evidence_class",
            "max_deviation_bps",
            "min_distinct_sources",
            "report_admissions",
            "aggregate",
            "aggregate_id",
        ]
    ),
    replacement=st.none()
    | st.booleans()
    | st.integers(min_value=-5, max_value=10**9)
    | st.text(max_size=8)
    | st.lists(st.integers(min_value=0, max_value=3), max_size=3),
)
def test_admitted_median3_top_level_mutation_never_accepts(key: str, replacement: object) -> None:
    _assert_honest_baseline()
    aggregate = copy.deepcopy(_HONEST_AGGREGATE)
    assume(aggregate.get(key) != replacement)
    aggregate[key] = replacement
    # Every top-level field except aggregate_id is content-bound by the hash, and
    # aggregate_id must equal that hash, so any single-field change must reject.
    result = verify_admitted_median3_aggregate(aggregate)
    assert result.status != "accepted"
    assert result.errors


@settings(max_examples=200)
@given(hex_body=st.text(alphabet="0123456789abcdef", min_size=2, max_size=96))
def test_canonical_pubkey_is_encoding_invariant(hex_body: str) -> None:
    # A single signing key must map to one canonical form regardless of an
    # optional 0x prefix or hex case, so encoding variants cannot dodge the
    # duplicate-pubkey check.
    canonical = _canonical_pubkey(hex_body)
    assert _canonical_pubkey("0x" + hex_body) == canonical
    assert _canonical_pubkey("0X" + hex_body.upper()) == canonical
    assert _canonical_pubkey(hex_body.upper()) == canonical
    assert canonical == canonical.lower()


@settings(max_examples=200)
@given(values=st.lists(st.integers(min_value=1, max_value=10**12), min_size=3, max_size=3))
def test_median3_helper_returns_middle_value(values: list[int]) -> None:
    median = _median3(values)
    ordered = sorted(values)
    assert median == ordered[1]
    # Confidence is the max absolute spread from the median, never negative.
    confidence = _confidence(values, median)
    assert confidence == max(abs(v - median) for v in values)
    assert confidence >= 0


@settings(max_examples=10, deadline=None)
@given(collide=st.sampled_from([(0, 1), (0, 2), (1, 2)]))
def test_admitted_median3_any_colliding_key_pair_rejects(collide: tuple[int, int]) -> None:
    keep, overwrite = collide
    aggregate = copy.deepcopy(_HONEST_AGGREGATE)
    keep_admission = aggregate["report_admissions"][keep]
    keep_key = {0: 43, 1: 44, 2: 45}[keep]
    target = aggregate["report_admissions"][overwrite]
    submission = target["signed_submission"]
    report = submission["reports"][0]
    aggregate["report_admissions"][overwrite] = _single_report_admission(
        private_key=keep_key,  # collide signing key with the kept admission
        reporter_id=submission["reporter_id"],  # keep distinct reporter_id label
        source_id=report["source_id"],  # keep distinct source
        query_id=aggregate["query_id"],
        value_e8=report["value_e8"],
        observed_epoch=report["observed_epoch"],
        source_diversity=target["source_diversity"],
        current_epoch=aggregate["current_epoch"],
        max_staleness_epochs=aggregate["max_staleness_epochs"],
    )
    assert keep_admission is aggregate["report_admissions"][keep]
    aggregate["aggregate_id"] = aggregate_content_hash(aggregate)
    result = verify_admitted_median3_aggregate(aggregate)
    assert result.status == "rejected"
    assert any(error.startswith("duplicate_reporter_pubkey:") for error in result.errors)
    assert result.distinct_reporter_pubkey_count == 2
