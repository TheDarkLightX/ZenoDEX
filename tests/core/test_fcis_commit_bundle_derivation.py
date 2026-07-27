from __future__ import annotations

from dataclasses import fields

import pytest

import src.core.fcis_commit_bundle_derivation as bundle_derivation
from src.core.fcis_authority_admission import (
    admit_fcis_authority_claim_v1,
    encode_fcis_authority_claim_v1,
)
from src.core.fcis_commit_bundle_derivation import (
    CommitBundleV1,
    _derive_bundle_claim_v1,
    _derive_bundle_root_v1,
    _derive_outbox_plan_v1,
    build_commit_bundle_v1,
    recompute_bundle_root_v1,
    recompute_outbox_plan_v1,
)
from src.core.fcis_commit_bundle_values import FCIS_COMMIT_BUNDLE_SCHEMA_ID_V1
from src.core.fcis_decision_derivation import (
    AcceptV1,
    RejectV1,
    acceptance_receipt_root_v1,
    evaluate_fcis_decision_v1,
)
from src.core.fcis_decision_values import FCISRejectCodeV1
from src.core.fcis_outbox_values import (
    OutboxEffectKindV1,
    OutboxPlanV1,
)
from src.core.settlement_snapshots import snapshot_settlement
from src.state.canonical import (
    canonical_json_bytes,
    domain_sep_bytes,
    hex_to_bytes_fixed,
    sha256_hex,
)
from src.state.intent_snapshots import admit_intent_batch
from src.state.intents import IntentKind
from src.state.owned_json import project_owned_json, snapshot_owned_json_object
from src.state.snapshot_combinators import AdmitOk
from tests.core.test_fcis_decision_derivation import _exact_inputs
from tests.core.test_fcis_support_profile_v5 import (
    _context_source as _support_context_source,
)
from tests.core.test_fcis_support_profile_v5 import (
    _single_intent_case,
)
from tests.core.test_fcis_support_profile_v5 import (
    _state_source as _support_state_source,
)


def _accept() -> AcceptV1:
    result = evaluate_fcis_decision_v1(**_exact_inputs())
    assert type(result) is AcceptV1
    return result


def _event_accept(kind: IntentKind = IntentKind.CREATE_POOL) -> AcceptV1:
    state, intent, settlement = _single_intent_case(kind)
    assert settlement.events is not None
    result = evaluate_fcis_decision_v1(
        state_source=_support_state_source(state),
        settlement=snapshot_settlement(settlement),
        intents=admit_intent_batch([intent]),
        context=_support_context_source(),
        budget=_exact_inputs()["budget"],
    )
    assert type(result) is AcceptV1
    return result


def _event_bundle(kind: IntentKind = IntentKind.CREATE_POOL) -> CommitBundleV1:
    bundle = build_commit_bundle_v1(_event_accept(kind))
    assert type(bundle) is CommitBundleV1
    return bundle


def _outbox_fixture(*events: dict[str, object]) -> tuple[OutboxPlanV1, str]:
    accept = _event_accept()
    receipt_root = acceptance_receipt_root_v1(accept)
    owned_events = tuple(snapshot_owned_json_object(event) for event in events)
    return _derive_outbox_plan_v1(owned_events, receipt_root), receipt_root


def _reject() -> RejectV1:
    inputs = _exact_inputs()
    result = evaluate_fcis_decision_v1(**{**inputs, "settlement": object()})
    assert type(result) is RejectV1
    return result


def test_build_commit_bundle_from_accept_produces_exact_bundle() -> None:
    """M5-P3-BUNDLE-001: only controlled derivation creates a bundle."""
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
    """M5-P3-BUNDLE-002: ordinary rejection remains unchanged and unbundled."""
    reject = _reject()
    result = build_commit_bundle_v1(reject)

    assert result is reject


def test_bundle_derivation_fault_returns_stable_typed_rejection(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """M5-P3-BUNDLE-002A: a controlled derivation fault emits no bundle."""

    accept = _accept()

    def fail_derivation(_decision: object) -> CommitBundleV1:
        raise ValueError("injected controlled derivation mismatch")

    monkeypatch.setattr(bundle_derivation, "_build_bundle_v1", fail_derivation)
    first = build_commit_bundle_v1(accept)
    second = build_commit_bundle_v1(accept)

    assert type(first) is RejectV1
    assert type(second) is RejectV1
    assert first == second
    assert first.receipt.public_reason == "commit bundle derivation rejected"
    assert first.receipt.code.member_ordinal == tuple(FCISRejectCodeV1).index(
        FCISRejectCodeV1.CANONICAL_BINDING_REJECTED
    )
    assert len(first.receipt.path) == 1
    assert first.receipt.path[0].text == "commit_bundle"
    assert not hasattr(first, "next_state")
    assert not hasattr(first, "commit_plan")
    assert not hasattr(first, "outbox_plan")


def test_build_commit_bundle_is_deterministic() -> None:
    """M5-P3-BUNDLE-005: repeated derivation is byte-identical."""
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
    plan, _receipt_root = _outbox_fixture({"kind": "one"})
    record = plan.records[0]

    expected_member = tuple(OutboxEffectKindV1).index(OutboxEffectKindV1.CANONICAL_EVENT)
    assert record.effect_kind.member_ordinal == expected_member


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


def test_no_events_produces_exact_empty_outbox_plan() -> None:
    """M5-P3-BUNDLE-003: no events produces the exact empty plan."""

    plan, _receipt_root = _outbox_fixture()

    assert type(plan) is OutboxPlanV1
    assert plan.records == ()


def test_multiple_events_preserve_semantic_order_and_contiguous_indices() -> None:
    """M5-P3-BUNDLE-004: event order and contiguous indices are preserved."""

    first = {"kind": "first", "amount": 1}
    second = {"kind": "second", "amount": 2}
    plan, _receipt_root = _outbox_fixture(first, second)

    assert tuple(record.effect_index for record in plan.records) == (0, 1)
    assert tuple(project_owned_json(record.payload) for record in plan.records) == (first, second)


def _expected_effect_identity(
    receipt_root: str,
    index: int,
    kind: str,
    payload: bytes,
) -> str:
    kind_bytes = kind.encode("utf-8")
    preimage = (
        domain_sep_bytes("zenodex/fcis/outbox-effect-identity", version=1)
        + hex_to_bytes_fixed(receipt_root, nbytes=32, name="receipt_root")
        + index.to_bytes(4, "big")
        + len(kind_bytes).to_bytes(4, "big")
        + kind_bytes
        + len(payload).to_bytes(8, "big")
        + payload
    )
    return sha256_hex(preimage)


def test_effect_identity_exact_framing_and_field_sensitivity() -> None:
    """M5-P3-BUNDLE-006: each framed identity field affects the digest."""

    plan, receipt_root = _outbox_fixture({"kind": "one", "amount": 7})
    record = plan.records[0]
    payload = canonical_json_bytes(project_owned_json(record.payload))
    expected = _expected_effect_identity(
        receipt_root,
        record.effect_index,
        OutboxEffectKindV1.CANONICAL_EVENT.value,
        payload,
    )
    assert record.effect_identity == expected
    variants = (
        _expected_effect_identity(
            "0x" + "01" * 32, 0, OutboxEffectKindV1.CANONICAL_EVENT.value, payload
        ),
        _expected_effect_identity(
            receipt_root, 1, OutboxEffectKindV1.CANONICAL_EVENT.value, payload
        ),
        _expected_effect_identity(receipt_root, 0, "other", payload),
        _expected_effect_identity(receipt_root, 0, OutboxEffectKindV1.CANONICAL_EVENT.value, b"{}"),
    )
    assert all(candidate != expected for candidate in variants)


def test_idempotency_key_exact_framing() -> None:
    plan, receipt_root = _outbox_fixture({"kind": "one", "amount": 7})
    record = plan.records[0]
    preimage = (
        domain_sep_bytes("zenodex/fcis/outbox-idempotency", version=1)
        + hex_to_bytes_fixed(receipt_root, nbytes=32, name="receipt_root")
        + record.effect_index.to_bytes(4, "big")
        + hex_to_bytes_fixed(record.effect_identity, nbytes=32, name="effect_identity")
    )
    assert record.idempotency_key == sha256_hex(preimage)


def test_outbox_and_bundle_literal_golden_vectors() -> None:
    """M5-P3-BUNDLE-006A: exact bytes and digests are release-visible vectors."""

    plan, receipt_root = _outbox_fixture({"kind": "one", "amount": 7})
    record = plan.records[0]
    payload = canonical_json_bytes(project_owned_json(record.payload))
    bundle = _event_bundle()

    assert receipt_root == "0xc723eddeb8de4109067f5faef0f43588c8c38bbe7d4922c3535a7cf3a23cf227"
    assert payload.hex() == "7b22616d6f756e74223a372c226b696e64223a226f6e65227d"
    assert record.effect_identity == (
        "0x4b6a29f9f762a6f8134ce1705b59913325c63b57b59d9c097b9c9820ad5f1a56"
    )
    assert record.idempotency_key == (
        "0x8a0cf6a529309dbf322743c52fbedb759a735ec1bc582a2aca05114c6f776b6f"
    )
    assert bundle.bundle_root == (
        "0x67fae2221b654ca27b4f9a0d49e25cc9df8894dbca290387466018744047409c"
    )
    assert sha256_hex(bundle.canonical_bundle_bytes) == (
        "0xea62214083eae37f0945be812cdd09c6ee7c6a3fede83ae9830ebc8857d78104"
    )


def test_exhaustive_bounded_event_derivation_is_deterministic_and_sensitive() -> None:
    """M5-P3-BUNDLE-PROP-001: bounded event values replay exactly and bind payloads."""

    accept = _event_accept()
    receipt_root = acceptance_receipt_root_v1(accept)
    observed_identities: set[str] = set()
    observed_plan_roots: set[str] = set()
    for amount in (0, 1, 2, 7, 255, 256, 65_535):
        event = snapshot_owned_json_object({"kind": "bounded", "amount": amount})
        first = _derive_outbox_plan_v1((event,), receipt_root)
        second = _derive_outbox_plan_v1((event,), receipt_root)
        first_claim = _derive_bundle_claim_v1(accept, first)
        second_claim = _derive_bundle_claim_v1(accept, second)
        _, first_root = _derive_bundle_root_v1(first_claim)
        _, second_root = _derive_bundle_root_v1(second_claim)

        assert first == second
        assert first.records[0].effect_identity == second.records[0].effect_identity
        assert first_root == second_root
        observed_identities.add(first.records[0].effect_identity)
        observed_plan_roots.add(first_root)

    assert len(observed_identities) == 7
    assert len(observed_plan_roots) == 7


def test_bundle_claim_round_trips_through_the_closed_grammar() -> None:
    """M5-P3-BUNDLE-007: decoded claims round-trip through closed admission."""

    bundle = _event_bundle()
    claim = _derive_bundle_claim_v1(bundle.decision, bundle.outbox_plan)
    admitted = admit_fcis_authority_claim_v1(FCIS_COMMIT_BUNDLE_SCHEMA_ID_V1, claim)

    assert type(admitted) is AdmitOk
    assert admitted.value == claim
    first = encode_fcis_authority_claim_v1(FCIS_COMMIT_BUNDLE_SCHEMA_ID_V1, claim)
    second = encode_fcis_authority_claim_v1(FCIS_COMMIT_BUNDLE_SCHEMA_ID_V1, admitted.value)
    assert first == second


def test_event_mutation_changes_effect_identity_and_bundle_root() -> None:
    first_plan, _ = _outbox_fixture({"kind": "one", "amount": 7})
    second_plan, _ = _outbox_fixture({"kind": "one", "amount": 8})
    bundle = _event_bundle(IntentKind.CREATE_POOL)
    first_claim = _derive_bundle_claim_v1(bundle.decision, first_plan)
    second_claim = _derive_bundle_claim_v1(bundle.decision, second_plan)
    _, first_root = _derive_bundle_root_v1(first_claim)
    _, second_root = _derive_bundle_root_v1(second_claim)

    assert first_plan.records[0].effect_identity != second_plan.records[0].effect_identity
    assert first_root != second_root
