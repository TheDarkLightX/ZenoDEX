"""Restricted allocation consumer controls; receipt/signature ports are test mocks."""

from dataclasses import replace

import pytest

from src.core import asset_transfer_epoch_allocation_v1 as consumer
from src.core import global_accounting_allocation_certificate_v1 as allocation
from src.core import global_economic_proof_v1 as proof
from src.core import global_settlement_types_v1 as types
from src.core.asset_lane_coordinator_v1 import compose_asset_lane_single_v1
from src.core.asset_lane_projection_v1 import AssetLaneCoordinatorRejectCodeV1
from src.core.asset_transfer_global_allocation_v1 import GlobalAllocationBindingRejectCodeV1
from src.core.epoch_effect_composition_v1 import compose_asset_lane_epoch_effect_plans_v1
from src.core.route_composition_receipt_verification_v1 import (
    RouteCompositionReceiptCandidateV1,
    RouteCompositionReceiptEnvelopeV1,
    verify_route_composition_receipt_v1,
)
from tests.core.test_asset_transfer_global_allocation_v1 import _global_allocation_fixture
from tests.core.test_global_settlement_abi_v1 import (
    _asset_lane_context,
    _asset_module_input_for_occurrence,
    _epoch_admission_fixture,
    _epoch_asset_module_state,
    _epoch_candidate,
    _occurrence,
    _RecordingReceiptVerifier,
    _verified_asset_lane_for_occurrence,
    _verified_asset_module_for_occurrence,
)


def _prospective_post(current, occurrence, accepted):
    projection = accepted.private_port.post_state
    replay = types.ReplayStateV1(occurrence.replay_id, occurrence.occurrence_id)
    return replace(
        current,
        height=occurrence.height,
        balances=projection.balances,
        supplies=projection.supplies,
        lane_roots=(
            replace(current.lane_roots[0], state_root=projection.state_root),
            *current.lane_roots[1:],
        ),
        replay_state=tuple(sorted((*current.replay_state, replay))),
    )


def _verified_step(profile, occurrence, current, module_state):
    module_input = replace(
        _asset_module_input_for_occurrence(profile, occurrence, _epoch_asset_module_state(profile)),
        pre_state=module_state,
        custody=current.custody,
    )
    accepted, witness = _verified_asset_module_for_occurrence(profile, occurrence, module_input)
    lane, verified_lane, effect = _verified_asset_lane_for_occurrence(
        profile,
        occurrence,
        module_input,
        accepted,
        witness,
    )
    post = _prospective_post(current, occurrence, accepted)
    journal = proof.RouteCompositionJournalV1(
        current.chain_id,
        current.deployment_root,
        current.profile_root,
        current.writer_epoch,
        occurrence.route_release_id,
        occurrence.occurrence_id,
        (lane.journal_root,),
        current.state_root,
        post.state_root,
        effect.effect_plan_root,
        lane.terminal_obligations_root,
    )
    verified_route = verify_route_composition_receipt_v1(
        RouteCompositionReceiptCandidateV1(
            profile,
            occurrence,
            (lane,),
            (verified_lane,),
            journal,
            RouteCompositionReceiptEnvelopeV1(
                proof.ReceiptKindV1.SUCCINCT,
                b"allocation-route",
            ),
        ),
        _RecordingReceiptVerifier(),
    )
    return accepted, witness, post, lane, journal, verified_route, effect


def _fixture(*, count=1, zero_claimant=False):
    """Reuse governed fixtures and actual transitions; never mint opaque witnesses directly."""
    profile, route, _, _, _, pre, _ = _global_allocation_fixture()
    if zero_claimant:
        pre = replace(pre, liabilities=(types.EconomicAmountV1("alice", "USD", "pool", 0),))
    module_state = replace(
        _epoch_asset_module_state(profile), balances=pre.balances, supplies=pre.supplies
    )
    current = pre
    occurrences, journals, disclosures, routes, effects, evidence = [], [], [], [], [], []
    for index in range(count):
        occurrence = replace(
            _occurrence(profile, route, pre),
            tx_index=index,
            nonce=index + 1,
            pre_state_root=current.state_root,
        )
        accepted, witness, post, lane, journal, verified_route, effect = _verified_step(
            profile,
            occurrence,
            current,
            module_state,
        )
        occurrences.append(occurrence)
        journals.append(journal)
        disclosures.append(proof.EconomicEpochRouteStateDisclosureV1((lane,), post))
        routes.append(verified_route)
        effects.append(effect)
        evidence.append((accepted, witness))
        current, module_state = post, accepted.post_state
    effect_plan = compose_asset_lane_epoch_effect_plans_v1(tuple(effects))
    template = _epoch_admission_fixture(1)
    certificate = replace(
        template.certificate,
        profile_root=profile.profile_id,
        pre_state_root=pre.state_root,
        post_state_root=current.state_root,
        ordered_occurrence_ids=tuple(row.occurrence_id for row in occurrences),
        ordered_route_journal_roots=tuple(row.journal_root for row in journals),
        ordered_route_assumption_roots=tuple(row.assumption_root for row in routes),
        module_leaf_occurrences=count,
        aggregation_levels=0 if count <= 8 else 1,
        effect_plan_root=effect_plan.effect_plan_root,
        root_image_id=profile.root_image_id,
    )
    certificate = replace(certificate, journal_bytes=len(certificate.canonical_journal_bytes))
    candidate = _epoch_candidate(
        profile,
        certificate,
        pre,
        current,
        tuple(occurrences),
        tuple(journals),
        tuple(disclosures),
        tuple(routes),
        tuple(effects),
        effect_plan,
        template.receipt_bytes,
    )
    return candidate, tuple(evidence)


def _check(candidate, evidence, *, predecessor=None):
    return consumer.check_asset_transfer_epoch_allocation_v1(
        candidate=candidate,
        predecessor=candidate.pre_state if predecessor is None else predecessor,
        module_evidence=evidence,
    )


def test_single_occurrence_derives_exact_partition_without_mutating_input():
    candidate, evidence = _fixture()
    before = types.canonical_global_bytes_v1(
        (candidate.pre_state, candidate.post_state, candidate.command_occurrences)
    )
    result = _check(candidate, evidence)
    assert isinstance(result, consumer.AssetTransferEpochAllocationAcceptedV1)
    assert len(result.checks) == 1
    assert result.checks[0].global_state_root == candidate.post_state.state_root
    assert result.checks[0].authority == "NONE"
    assert result.source_state_root == candidate.pre_state.state_root
    assert before == types.canonical_global_bytes_v1(
        (candidate.pre_state, candidate.post_state, candidate.command_occurrences)
    )


def test_zero_claimant_identity_is_preserved_even_with_matching_totals():
    # Nonzero custody currently fails coordinator admission (retained below).
    # This is exact row-identity coverage, not a nonzero custody qualification.
    candidate, evidence = _fixture(zero_claimant=True)
    pre, post = candidate.pre_state, candidate.post_state
    changed = replace(post, liabilities=(replace(post.liabilities[0], owner="mallory"),))
    disclosure = replace(candidate.route_state_disclosures[0], post_state=changed)
    candidate = replace(candidate, post_state=changed, route_state_disclosures=(disclosure,))
    result = _check(candidate, evidence)
    assert isinstance(result, consumer.AssetTransferEpochAllocationRejectedV1)
    assert result.code is consumer.AssetTransferEpochAllocationRejectCodeV1.GLOBAL_FRAGMENT_REJECTED
    assert result.cause is not None
    assert result.cause.code is GlobalAllocationBindingRejectCodeV1.GLOBAL_CLAIMANT_CONTINUITY_DRIFT
    assert sum(row.amount_atoms for row in pre.liabilities) == sum(
        row.amount_atoms for row in changed.liabilities
    )
    assert pre.liabilities[0].owner == "alice"


def test_conserved_account_reassignment_is_refused_by_full_projection_rows():
    candidate, evidence = _fixture()
    rows = candidate.post_state.balances
    changed_rows = (
        replace(rows[0], amount_atoms=rows[0].amount_atoms - 1),
        replace(rows[1], amount_atoms=rows[1].amount_atoms + 1),
        *rows[2:],
    )
    assert sum(row.amount_atoms for row in changed_rows) == sum(row.amount_atoms for row in rows)
    post = replace(candidate.post_state, balances=changed_rows)
    changed = replace(
        candidate,
        post_state=post,
        route_state_disclosures=(replace(candidate.route_state_disclosures[0], post_state=post),),
    )
    result = _check(changed, evidence)
    assert result.code is consumer.AssetTransferEpochAllocationRejectCodeV1.GLOBAL_FRAGMENT_REJECTED
    assert result.cause.code is GlobalAllocationBindingRejectCodeV1.GLOBAL_PROJECTION_ROWS_DRIFT


def test_wrong_module_membership_rejects_before_fragment_admission():
    candidate, evidence = _fixture()
    disclosure = candidate.route_state_disclosures[0]
    wrong = replace(disclosure.lane_journals[0], ordered_module_journal_roots=("0x" + "ee" * 32,))
    candidate = replace(
        candidate, route_state_disclosures=(replace(disclosure, lane_journals=(wrong,)),)
    )
    result = _check(candidate, evidence)
    assert (
        result.code is consumer.AssetTransferEpochAllocationRejectCodeV1.MODULE_MEMBERSHIP_MISMATCH
    )
    assert result.occurrence_index == 0


@pytest.mark.parametrize("change", ("omit", "duplicate", "list", "foreign_witness"))
def test_evidence_shape_and_exact_cardinality_refuse(change):
    candidate, evidence = _fixture()
    changed = {
        "omit": (),
        "duplicate": evidence * 2,
        "list": list(evidence),
        "foreign_witness": ((evidence[0][0], object()),),
    }[change]
    result = _check(candidate, changed)
    assert isinstance(result, consumer.AssetTransferEpochAllocationRejectedV1)
    assert result.code in {
        consumer.AssetTransferEpochAllocationRejectCodeV1.EVIDENCE_SHAPE,
        consumer.AssetTransferEpochAllocationRejectCodeV1.EPOCH_CARDINALITY,
    }


def test_two_command_epoch_retains_current_standalone_height_limit():
    candidate, evidence = _fixture(count=2)
    # The enclosing epoch accepts this ordinary history. Its intermediate height
    # remains constant; standalone W04 deliberately requires an adjacent height.
    proof.verify_economic_epoch_v1(candidate, _RecordingReceiptVerifier())
    from src.core.asset_transfer_global_allocation_v1 import (
        AssetTransferGlobalAllocationCandidateV1,
    )
    from src.core.asset_transfer_receipt_admission_v1 import (
        verify_asset_transfer_global_fragment_receipt_v1,
    )

    result = verify_asset_transfer_global_fragment_receipt_v1(
        evidence[1][1],
        AssetTransferGlobalAllocationCandidateV1(
            evidence[1][0],
            candidate.command_occurrences[1],
            candidate.route_state_disclosures[0].post_state,
            candidate.route_state_disclosures[1].post_state,
        ),
    )
    assert result.code is GlobalAllocationBindingRejectCodeV1.GLOBAL_OCCURRENCE_DRIFT


def test_module_evidence_cannot_be_reordered_between_occurrences():
    candidate, evidence = _fixture(count=2)
    result = _check(candidate, tuple(reversed(evidence)))
    assert result.code is consumer.AssetTransferEpochAllocationRejectCodeV1.OCCURRENCE_MISMATCH
    assert result.occurrence_index == 0


@pytest.mark.parametrize("controlled_atoms", (1, 7, 1 << 127))
def test_nonzero_custody_retains_module_coordinator_conservation_disagreement(controlled_atoms):
    profile, _, occurrence, accepted, _, pre, _ = _global_allocation_fixture(
        controlled_atoms=controlled_atoms
    )
    base = _epoch_asset_module_state(profile)
    module_input = replace(
        _asset_module_input_for_occurrence(profile, occurrence, base),
        pre_state=replace(base, balances=pre.balances, supplies=pre.supplies),
        custody=pre.custody,
    )
    context = _asset_lane_context(profile, occurrence, module_input, accepted)
    result = compose_asset_lane_single_v1(
        context, accepted.module_journal, accepted.private_port, accepted.effects
    )
    assert result.code is AssetLaneCoordinatorRejectCodeV1.CONSERVATION_STATE_MISMATCH
    module_total = accepted.effects.asset_conservation[0].owned_and_custodied_pre_atoms
    assert (
        accepted.private_port.pre_state.owned_and_custodied_atoms("USD")
        == module_total + controlled_atoms
    )


@pytest.mark.parametrize(
    "table", ("reserves", "outbox", "open_terminal", "drained_terminal", "tombstoned_terminal")
)
def test_unsupported_tables_are_refused_without_partial_acceptance(table):
    candidate, evidence = _fixture()
    root = "0x" + "dd" * 32
    if table == "reserves":
        field, rows = "reserves", (types.EconomicAmountV1("protocol", "USD", "reserve", 1),)
    elif table == "outbox":
        field, rows = (
            "outbox",
            (types.OutboxStateV1(root, "external", root, root, types.OutboxStatusV1.PENDING),),
        )
    else:
        status = types.TerminalObligationStatusV1(table.removesuffix("_terminal").upper())
        field, rows = (
            "terminal_obligations",
            (
                types.TerminalObligationV1(
                    "terminal", types.LaneIdV1.ASSET_TRANSFER, "alice", "USD", 1, status
                ),
            ),
        )
    post = replace(candidate.post_state, **{field: rows})
    changed = replace(
        candidate,
        post_state=post,
        route_state_disclosures=(replace(candidate.route_state_disclosures[0], post_state=post),),
    )
    before = types.canonical_global_bytes_v1((changed.pre_state, changed.post_state))
    result = _check(changed, evidence)
    assert result.code is consumer.AssetTransferEpochAllocationRejectCodeV1.GLOBAL_FRAGMENT_REJECTED
    assert result.cause.code is GlobalAllocationBindingRejectCodeV1.GLOBAL_UNSUPPORTED_STATE
    assert not hasattr(result, "checks")
    assert before == types.canonical_global_bytes_v1((changed.pre_state, changed.post_state))


def test_projector_root_mutant_is_killed_by_mandatory_certificate_checker(monkeypatch):
    candidate, evidence = _fixture()
    original = consumer.project_allocation_certificate_v1

    def wrong_root(state, roots, slots):
        result = original(state, roots, slots)
        assert isinstance(result, allocation.GlobalAccountingAllocationCertificateV1)
        assert len(slots) == 12
        assert roots == ((types.LaneIdV1.ASSET_TRANSFER, slots[0].receipt_root),)
        assert slots[0].receipt_root == slots[0].fragment.binding_root
        return replace(result, allocation_root="0x" + "dd" * 32)

    monkeypatch.setattr(consumer, "project_allocation_certificate_v1", wrong_root)
    result = _check(candidate, evidence)
    assert result.code is consumer.AssetTransferEpochAllocationRejectCodeV1.CERTIFICATE_REJECTED
    assert isinstance(result.cause, allocation.AllocationCertificateRejectedV1)


@pytest.mark.parametrize("bad_result", (None, True, object()))
def test_unregistered_checker_outcomes_are_internal_errors_not_success(monkeypatch, bad_result):
    candidate, evidence = _fixture()
    monkeypatch.setattr(
        consumer, "check_global_accounting_allocation_certificate_v1", lambda *_args: bad_result
    )
    with pytest.raises(TypeError, match="unregistered outcome"):
        _check(candidate, evidence)


def test_source_and_final_state_are_exact_independent_bindings():
    candidate, evidence = _fixture()
    wrong_source = replace(candidate.pre_state, history_root="0x" + "cc" * 32)
    assert (
        _check(candidate, evidence, predecessor=wrong_source).code
        is consumer.AssetTransferEpochAllocationRejectCodeV1.SOURCE_MISMATCH
    )
    wrong_final = replace(candidate.post_state, history_root="0x" + "cc" * 32)
    assert (
        _check(replace(candidate, post_state=wrong_final), evidence).code
        is consumer.AssetTransferEpochAllocationRejectCodeV1.FINAL_STATE_MISMATCH
    )


@pytest.mark.parametrize("count", (0, 65))
def test_epoch_command_limits_reject_before_owned_snapshot(monkeypatch, count):
    candidate, evidence = _fixture()
    object.__setattr__(candidate, "command_occurrences", candidate.command_occurrences * count)
    monkeypatch.setattr(
        consumer,
        "_snapshot_economic_epoch_candidate_v1",
        lambda *_args: pytest.fail("unbounded snapshot"),
    )
    assert (
        _check(candidate, evidence).code
        is consumer.AssetTransferEpochAllocationRejectCodeV1.EPOCH_CARDINALITY
    )


@pytest.mark.parametrize("field,value", (("height", True), ("balances", [])))
def test_validation_bypassed_nonexact_state_returns_typed_rejection(field, value):
    candidate, evidence = _fixture()
    object.__setattr__(candidate.pre_state, field, value)
    assert (
        _check(candidate, evidence).code
        is consumer.AssetTransferEpochAllocationRejectCodeV1.MALFORMED_INPUT
    )


def test_retained_input_alias_cannot_change_owned_checker_subject(monkeypatch):
    candidate, evidence = _fixture()
    initial_root, final_root = candidate.pre_state.state_root, candidate.post_state.state_root
    original = consumer.project_allocation_certificate_v1

    def mutate_caller_after_snapshot(state, roots, slots):
        object.__setattr__(candidate.pre_state, "height", 99)
        object.__setattr__(candidate.post_state, "height", 99)
        return original(state, roots, slots)

    monkeypatch.setattr(consumer, "project_allocation_certificate_v1", mutate_caller_after_snapshot)
    result = _check(candidate, evidence)
    assert isinstance(result, consumer.AssetTransferEpochAllocationAcceptedV1)
    assert (result.source_state_root, result.post_state_root) == (initial_root, final_root)
