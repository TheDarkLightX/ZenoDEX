"""Python side of the shared claimant-backing guard parity vector.

Obligation: for every recorded V1 state, the Python view, its root, and its exact
reject code and message equal the fixture, and the fixture equals its renderer.
The Rust test ``zk/global_settlement_abi_v1/tests/claimant_backing_guard_golden.rs``
replays the same fixture, so a divergence in fold keys, the OPEN filter, checked
arithmetic, precedence, or message bytes fails on at least one side.

Named mutation killers live in the fixture (``mutation_killers``); each names the
vector that fails when the mutation is applied. Authority: NONE.
"""

from __future__ import annotations

import dataclasses
import hashlib
import json
from pathlib import Path
from typing import Any

import pytest

from src.core.global_economic_state_effect_refinement_v1 import (
    CLAIMANT_BACKING_MESSAGE_BY_CODE_V1,
    CLAIMANT_BACKING_VIEW_HASH_DOMAIN_V1,
    ClaimantBackingRejectCodeV1,
    ClaimantBackingViewV1,
    classify_claimant_backing_error_v1,
)
from src.core.global_settlement_types_v1 import canonical_global_bytes_v1
from tools import render_global_claimant_backing_guard_v1_golden as renderer

ROOT = Path(__file__).resolve().parents[2]
FIXTURE = ROOT / "tests/data/global_claimant_backing_guard_v1_golden.json"


def _fixture() -> dict[str, Any]:
    value = json.loads(FIXTURE.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_fixture_is_the_renderer_output() -> None:
    assert FIXTURE.read_bytes() == renderer.render_bytes_v1()


def test_fixture_header_and_message_table_are_shared() -> None:
    fixture = _fixture()
    assert fixture["fixture_schema"] == renderer.FIXTURE_SCHEMA_V1
    assert fixture["authority"] == "NONE"
    assert fixture["hash_domain"] == CLAIMANT_BACKING_VIEW_HASH_DOMAIN_V1
    assert fixture["reject_messages"] == {
        code.value: message for code, message in CLAIMANT_BACKING_MESSAGE_BY_CODE_V1.items()
    }
    assert set(fixture["reject_messages"]) == {code.value for code in ClaimantBackingRejectCodeV1}


@pytest.mark.parametrize("name", sorted(renderer.VECTORS_V1))
def test_vector_replays_state_view_root_and_outcome(name: str) -> None:
    vector = _fixture()["vectors"][name]
    state = renderer.build_state_v1(vector["spec"])
    canonical_bytes = canonical_global_bytes_v1(state)
    assert hashlib.sha256(canonical_bytes).hexdigest() == vector["state_bytes_sha256"]
    assert json.loads(canonical_bytes) == vector["state"]
    assert state.state_root == vector["expected_state_root"]
    view, outcome = renderer.evaluate_v1(state)
    assert outcome == vector["expected_outcome"]
    if view is None:
        assert vector["expected_view"] is None and vector["expected_view_root"] is None
        assert outcome["code"] == ClaimantBackingRejectCodeV1.CLAIMANT_BACKING_TOTAL_OVERFLOW.value
    else:
        assert view.to_canonical() == vector["expected_view"]
        assert view.view_root == vector["expected_view_root"]
    if outcome["status"] == "REJECT":
        assert outcome["message"] == CLAIMANT_BACKING_MESSAGE_BY_CODE_V1[
            ClaimantBackingRejectCodeV1(outcome["code"])
        ]


def test_histories_reference_recorded_vectors_in_order() -> None:
    fixture = _fixture()
    for steps in fixture["histories"].values():
        assert len(steps) >= 2
        assert all(step in fixture["vectors"] for step in steps)
    final = fixture["vectors"][fixture["histories"]["deposit_deposit_drain_overdrain"][-1]]
    assert final["expected_outcome"]["code"] == "LIABILITIES_EXCEED_SAME_CONTROL_DOMAIN_BACKING"


def test_mutation_killers_name_recorded_vectors_with_the_expected_polarity() -> None:
    fixture = _fixture()
    killers = fixture["mutation_killers"]
    assert set(killers) == set(renderer.MUTATION_KILLERS_V1)
    seen_codes: set[str] = set()
    for mutation, killer in killers.items():
        assert set(killer) == {"vector", "expected_code"}, mutation
        outcome = fixture["vectors"][killer["vector"]]["expected_outcome"]
        if killer["expected_code"] == renderer.ACCEPT_V1:
            assert outcome == {"status": "ACCEPT"}, mutation
        else:
            assert outcome["status"] == "REJECT" and outcome["code"] == killer["expected_code"], mutation
            seen_codes.add(killer["expected_code"])
    assert seen_codes == {code.value for code in ClaimantBackingRejectCodeV1}


def test_view_has_no_reserve_or_balance_column() -> None:
    names = [field.name for field in dataclasses.fields(ClaimantBackingViewV1)]
    assert names == [
        "custody_by_control_domain",
        "entitlements_by_control_domain",
        "entitlements_by_claimant",
        "open_terminals_by_claimant",
    ]
    assert not any("reserve" in name or "balance" in name for name in names)


def test_precedence_is_overflow_then_domain_then_claimant() -> None:
    vectors = _fixture()["vectors"]
    assert vectors["precedence_terminal_overflow_before_domain"]["expected_outcome"]["code"] == (
        "CLAIMANT_BACKING_TOTAL_OVERFLOW"
    )
    assert vectors["precedence_entitlement_overflow_before_domain"]["expected_outcome"]["code"] == (
        "CLAIMANT_BACKING_TOTAL_OVERFLOW"
    )
    assert vectors["precedence_domain_before_claimant"]["expected_outcome"]["code"] == (
        "LIABILITIES_EXCEED_SAME_CONTROL_DOMAIN_BACKING"
    )


def test_classifier_maps_only_exact_guard_messages() -> None:
    for code, message in CLAIMANT_BACKING_MESSAGE_BY_CODE_V1.items():
        assert classify_claimant_backing_error_v1(ValueError(message)) is code
    assert classify_claimant_backing_error_v1(ValueError("economic refinement zero economic amount")) is None
    assert classify_claimant_backing_error_v1(TypeError(next(iter(CLAIMANT_BACKING_MESSAGE_BY_CODE_V1.values())))) is None
