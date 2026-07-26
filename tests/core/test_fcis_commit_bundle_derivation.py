from __future__ import annotations

from dataclasses import fields

import pytest

from src.core.fcis_commit_bundle_derivation import (
    CommitBundleV1,
    build_commit_bundle_v1,
    recompute_bundle_root_v1,
    recompute_outbox_plan_v1,
)
from src.core.fcis_decision_derivation import (
    AcceptV1,
    RejectV1,
    evaluate_fcis_decision_v1,
)
from src.core.fcis_outbox_values import OutboxPlanV1
from tests.core.test_fcis_decision_derivation import _exact_inputs


def _accept() -> AcceptV1:
    result = evaluate_fcis_decision_v1(**_exact_inputs())
    assert type(result) is AcceptV1
    return result


def _reject() -> RejectV1:
    inputs = _exact_inputs()
    result = evaluate_fcis_decision_v1(**{**inputs, "settlement": object()})
    assert type(result) is RejectV1
    return result


def test_build_commit_bundle_from_accept_produces_exact_bundle() -> None:
    accept = _accept()
    bundle = build_commit_bundle_v1(accept)

    assert type(bundle) is CommitBundleV1
    assert bundle.decision is accept
    assert type(bundle.outbox_plan) is OutboxPlanV1
    assert tuple(field.name for field in fields(bundle)) == (
        "decision",
        "outbox_plan",
        "_canonical_bundle_bytes",
        "_bundle_root",
    )
    assert bundle.next_state is accept.next_state
    assert bundle.commit_plan is accept.commit_plan
    assert bundle.receipt is accept.receipt
    assert bundle.expected_pre_root == accept.receipt.binding.pre_state_root


def test_build_commit_bundle_from_reject_returns_unchanged_reject() -> None:
    reject = _reject()
    result = build_commit_bundle_v1(reject)

    assert result is reject


def test_build_commit_bundle_is_deterministic() -> None:
    accept = _accept()
    first = build_commit_bundle_v1(accept)
    second = build_commit_bundle_v1(accept)

    assert first == second
    assert first.bundle_root == second.bundle_root
    assert first.canonical_bundle_bytes == second.canonical_bundle_bytes


def test_bundle_root_is_canonical_digest() -> None:
    accept = _accept()
    bundle = build_commit_bundle_v1(accept)

    root = bundle.bundle_root
    assert type(root) is str
    assert root.startswith("0x")
    assert len(root) == 66
    assert all(c in "0123456789abcdef" for c in root[2:])


def test_canonical_bundle_bytes_are_exact_bytes() -> None:
    accept = _accept()
    bundle = build_commit_bundle_v1(accept)

    assert type(bundle.canonical_bundle_bytes) is bytes
    assert len(bundle.canonical_bundle_bytes) > 0


def test_recompute_bundle_root_matches_retained_root() -> None:
    accept = _accept()
    bundle = build_commit_bundle_v1(accept)

    recomputed_bytes, recomputed_root = recompute_bundle_root_v1(bundle)

    assert recomputed_bytes == bundle._canonical_bundle_bytes
    assert recomputed_root == bundle._bundle_root


def test_recompute_outbox_plan_matches_retained_plan() -> None:
    accept = _accept()
    bundle = build_commit_bundle_v1(accept)

    recomputed = recompute_outbox_plan_v1(bundle)

    assert recomputed == bundle.outbox_plan


def test_outbox_plan_records_match_settlement_events() -> None:
    accept = _accept()
    bundle = build_commit_bundle_v1(accept)

    events = accept.commit_plan.effects.settlement.events
    expected_count = 0 if events is None else len(events)
    assert len(bundle.outbox_plan.records) == expected_count


def test_outbox_record_identities_are_distinct_canonical_digests() -> None:
    accept = _accept()
    bundle = build_commit_bundle_v1(accept)

    identities = [record.effect_identity for record in bundle.outbox_plan.records]
    assert len(identities) == len(set(identities))
    for identity in identities:
        assert identity.startswith("0x")
        assert len(identity) == 66


def test_outbox_record_idempotency_keys_are_distinct_canonical_digests() -> None:
    accept = _accept()
    bundle = build_commit_bundle_v1(accept)

    keys = [record.idempotency_key for record in bundle.outbox_plan.records]
    assert len(keys) == len(set(keys))
    for key in keys:
        assert key.startswith("0x")
        assert len(key) == 66


def test_outbox_record_effect_index_is_sequential() -> None:
    accept = _accept()
    bundle = build_commit_bundle_v1(accept)

    indices = [record.effect_index for record in bundle.outbox_plan.records]
    assert indices == list(range(len(indices)))


def test_outbox_record_effect_kind_is_canonical_event() -> None:
    accept = _accept()
    bundle = build_commit_bundle_v1(accept)

    for record in bundle.outbox_plan.records:
        assert record.effect_kind.value == "canonical_event"


def test_commit_bundle_constructor_requires_controlled_token() -> None:
    accept = _accept()
    bundle = build_commit_bundle_v1(accept)

    with pytest.raises(TypeError, match="controlled derivation"):
        CommitBundleV1(
            bundle.decision,
            bundle.outbox_plan,
            bundle._canonical_bundle_bytes,
            bundle._bundle_root,
            object(),
        )


def test_build_commit_bundle_rejects_non_decision() -> None:
    with pytest.raises(TypeError, match="exact DecisionV1"):
        build_commit_bundle_v1(object())  # type: ignore[arg-type]


def test_recompute_bundle_root_rejects_non_bundle() -> None:
    with pytest.raises(TypeError, match="exact CommitBundleV1"):
        recompute_bundle_root_v1(object())  # type: ignore[arg-type]


def test_recompute_outbox_plan_rejects_non_bundle() -> None:
    with pytest.raises(TypeError, match="exact CommitBundleV1"):
        recompute_outbox_plan_v1(object())  # type: ignore[arg-type]
