from __future__ import annotations

from dataclasses import fields, replace
from typing import cast

import pytest

import src.core.fcis_commit_bundle_derivation as bundle_derivation
from src.core.fcis_authority_admission import (
    CanonicalAuthorityClaimBytesV1,
    admit_fcis_authority_claim_v1,
    encode_fcis_authority_claim_v1,
)
from src.core.fcis_authority_normal_form_v1 import FCISAuthorityNormalFormV1
from src.core.fcis_commit_bundle_derivation import (
    CommitBundleV1,
    _derive_bundle_claim_v1,
    _derive_bundle_root_v1,
    _derive_outbox_plan_v1,
    build_anf_bound_commit_bundle_v1,
    build_commit_bundle_v1,
    recompute_anf_root_v1,
    recompute_bundle_root_v1,
    recompute_outbox_plan_v1,
    recompute_outbox_root_v1,
    verify_anf_bound_commit_bundle_v1,
)
from src.core.fcis_commit_bundle_values import (
    FCIS_COMMIT_BUNDLE_SCHEMA_ID_V1,
    FCIS_COMMIT_BUNDLE_SCHEMA_ID_V2,
)
from src.core.fcis_decision_derivation import (
    AcceptV1,
    RejectV1,
    acceptance_receipt_root_v1,
    evaluate_fcis_decision_v1,
    evaluate_source_bound_fcis_decision_v1,
    evaluate_source_bound_fcis_decision_with_anf_v1,
)
from src.core.fcis_decision_values import FCISRejectCodeV1
from src.core.fcis_outbox_values import (
    FCIS_OUTBOX_PLAN_SCHEMA_ID_V1,
    FCIS_OUTBOX_PLAN_SCHEMA_ID_V2,
    OutboxEffectKindV1,
    OutboxPlanV1,
    OutboxPlanV2,
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
from tests.core.test_fcis_m6_d03_anf_receipt_binding import (
    _authority_normal_form,
    _source_occurrence,
    evaluate_source_bound_fcis_step_candidate_v1_for_test,
)
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
    assert bundle.outbox_schema_id == FCIS_OUTBOX_PLAN_SCHEMA_ID_V1
    assert bundle.bundle_schema_id == FCIS_COMMIT_BUNDLE_SCHEMA_ID_V1
    assert tuple(field.name for field in fields(bundle)) == (
        "decision",
        "outbox_plan",
        "_canonical_bundle_bytes",
        "_bundle_root",
        "authority_normal_form",
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
        build_commit_bundle_v1(object())


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
    return cast(str, sha256_hex(preimage))


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

    assert receipt_root == "0x313b513e357566987f2fe882577ec75ceb60fda5e04bac5f9aa6d073edd9d380"
    assert payload.hex() == "7b22616d6f756e74223a372c226b696e64223a226f6e65227d"
    assert record.effect_identity == (
        "0x5e5b37c1e16c2e3f7f1fc1d883a908458772e04c5310d0f83fa5ab2f206e7899"
    )
    assert record.idempotency_key == (
        "0x460a6968d9d0b355371f59ee45db918ca8bc6ea6030953437e9889171ff26aaa"
    )
    assert bundle.bundle_root == (
        "0x0626a082ff542b69fd1a14f9384dd1b5aa54025633a460de37dd372416827ee0"
    )
    assert bundle.outbox_root == (
        "0xf7ac577051aaac3bf3704a9a699c2174235c262c62716c1663b792d32cacc0e9"
    )
    assert sha256_hex(bundle.canonical_bundle_bytes) == (
        "0xfdec6cd51d03e5384a282ab967b32026791c26672548fa70ff2c208e520071c1"
    )
    assert len(bundle.canonical_bundle_bytes) == 9_043


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
    assert type(bundle.outbox_plan) is OutboxPlanV1
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


def _anf_accept_with_value() -> tuple[AcceptV1, FCISAuthorityNormalFormV1]:
    inputs = _exact_inputs()
    occurrence = _source_occurrence(inputs)
    evaluation = evaluate_source_bound_fcis_step_candidate_v1_for_test(occurrence)
    base = evaluate_source_bound_fcis_decision_v1(
        source_occurrence=occurrence,
        budget=inputs["budget"],
    )
    assert type(base) is AcceptV1
    anf = _authority_normal_form(evaluation, base, inputs["budget"])
    decision = evaluate_source_bound_fcis_decision_with_anf_v1(
        source_occurrence=occurrence,
        budget=inputs["budget"],
        authority_normal_form=anf,
    )
    assert type(decision) is AcceptV1
    return decision, anf


def _anf_accept() -> AcceptV1:
    return _anf_accept_with_value()[0]


def test_d04_anf_bundle_recomputes_decision_outbox_and_all_roots() -> None:
    decision, anf = _anf_accept_with_value()
    bundle = build_anf_bound_commit_bundle_v1(decision, anf)

    assert type(bundle) is CommitBundleV1
    assert bundle.decision is decision
    assert bundle.authority_normal_form is anf
    assert type(bundle.outbox_plan) is OutboxPlanV2
    assert bundle.outbox_schema_id == FCIS_OUTBOX_PLAN_SCHEMA_ID_V2
    assert bundle.bundle_schema_id == FCIS_COMMIT_BUNDLE_SCHEMA_ID_V2
    assert bundle.authority_normal_form_root == decision.receipt.binding.authority_normal_form_root
    assert bundle.outbox_plan.authority_normal_form_root == bundle.authority_normal_form_root
    assert recompute_anf_root_v1(bundle) == bundle.authority_normal_form_root
    assert recompute_outbox_plan_v1(bundle) == bundle.outbox_plan
    assert recompute_outbox_root_v1(bundle) == bundle.outbox_root
    canonical_bytes, bundle_root = recompute_bundle_root_v1(bundle)
    assert canonical_bytes == bundle.canonical_bundle_bytes
    assert bundle_root == bundle.bundle_root
    assert verify_anf_bound_commit_bundle_v1(bundle)


def test_d04_anf_bundle_uses_distinct_v2_canonical_schema() -> None:
    decision, anf = _anf_accept_with_value()
    bundle = build_anf_bound_commit_bundle_v1(decision, anf)

    assert type(bundle) is CommitBundleV1
    assert type(bundle.outbox_plan) is OutboxPlanV2
    claim = bundle_derivation._derive_anf_bound_bundle_claim_v2(
        decision,
        bundle.outbox_plan,
    )
    encoded = encode_fcis_authority_claim_v1(FCIS_COMMIT_BUNDLE_SCHEMA_ID_V2, claim)
    assert type(encoded) is CanonicalAuthorityClaimBytesV1
    assert encoded.payload == bundle.canonical_bundle_bytes
    encoded_outbox = encode_fcis_authority_claim_v1(
        FCIS_OUTBOX_PLAN_SCHEMA_ID_V2,
        bundle.outbox_plan,
    )
    assert type(encoded_outbox) is CanonicalAuthorityClaimBytesV1
    expected_outbox_root = sha256_hex(
        domain_sep_bytes(FCIS_OUTBOX_PLAN_SCHEMA_ID_V2, version=2) + encoded_outbox.payload
    )
    assert bundle.outbox_root == expected_outbox_root


def test_d04_anf_builder_rejects_legacy_unbound_decision() -> None:
    result = build_anf_bound_commit_bundle_v1(_accept(), None)

    assert type(result) is RejectV1
    assert result.receipt.public_reason == "commit bundle derivation rejected"


def test_d04_crossed_foreign_outbox_rejects_before_publication() -> None:
    decision, anf = _anf_accept_with_value()
    bundle = build_anf_bound_commit_bundle_v1(decision, anf)
    foreign = build_commit_bundle_v1(_event_accept())

    assert type(bundle) is CommitBundleV1
    assert type(foreign) is CommitBundleV1
    object.__setattr__(bundle, "outbox_plan", foreign.outbox_plan)

    assert not verify_anf_bound_commit_bundle_v1(bundle)


def test_d04_crossed_decision_rejects_before_publication() -> None:
    decision, anf = _anf_accept_with_value()
    bundle = build_anf_bound_commit_bundle_v1(decision, anf)
    foreign = build_commit_bundle_v1(_event_accept())

    assert type(bundle) is CommitBundleV1
    assert type(foreign) is CommitBundleV1
    object.__setattr__(bundle, "decision", foreign.decision)

    assert not verify_anf_bound_commit_bundle_v1(bundle)


def test_d04_foreign_anf_rejects_before_publication() -> None:
    decision, anf = _anf_accept_with_value()
    foreign = replace(anf, command_root="0x" + "99" * 32)

    result = build_anf_bound_commit_bundle_v1(decision, foreign)

    assert type(result) is RejectV1
