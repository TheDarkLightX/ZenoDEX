"""One-store margin/custody histories; receipt IPC fixtures are not proofs."""

from dataclasses import replace

import pytest

from src.core.asset_lane_custody_coordinator_v2 import transition_asset_lane_custody_v2
from src.core.asset_lane_custody_global_v2 import derive_asset_lane_custody_global_post_v2
from src.core.asset_lane_custody_statement_v2 import prepare_asset_lane_custody_global_statement_v2
from src.core.asset_lane_state_v2 import AssetLaneContextV2
from src.core.economic_receipt_verifier_evidence_v1 import (
    economic_receipt_verifier_implementation_root_v1,
)
from src.core.global_settlement_primitives_v2 import (
    canonical_economic_command_body_bytes_v2,
    hash_economic_command_body_v2,
)
from src.core.global_settlement_types_v2 import (
    TerminalObligationStatusV2,
    canonical_global_bytes_v2,
)
from src.core.perps_margin_global_v2 import PerpsMarginGlobalRejectedV2
from src.core.perps_margin_receipt_v2 import prepare_perps_margin_statement_v2
from src.core.perps_margin_types_v1 import (
    PERPS_MARGIN_CLOSE_COMMAND_KIND_V1 as CLOSE,
)
from src.core.perps_margin_types_v1 import (
    PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1 as DEPOSIT,
)
from src.core.perps_margin_types_v1 import (
    PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1 as WITHDRAW,
)
from src.core.perps_margin_wire_v2 import PerpsMarginRequestV2
from src.integration import global_receipt_verifier_v1 as receipt_transport
from src.integration import isolated_custody_publisher_v2 as implementation
from src.integration.global_receipt_verifier_v1 import GlobalReceiptVerifierErrorV1
from src.integration.isolated_custody_publisher_v2 import (
    CustodyPublicationConfigurationV2,
    CustodyPublicationIndeterminateV2,
    IsolatedCustodyPublisherV2,
    JointMarginPublicationConfigurationV2,
)
from src.integration.isolated_custody_publisher_v2 import (
    CustodyPublicationStatusV2 as Status,
)
from tests.core.test_asset_lane_coordinator_v2 import _transfer_command
from tests.core.test_perps_margin_global_v2 import _command
from tests.integration.test_authenticated_asset_lane_custody_receipt_v2 import (
    _RECEIPT,
    _receipt_exchange,
    _sign,
)
from tests.integration.test_isolated_custody_publisher_v2 import _CrashConnection, _logical_store
from tests.integration.test_isolated_economic_command_authentication_v2 import (
    protocol_case as protocol_case,
)
from tests.integration.test_joint_margin_capacity_v2 import _inputs_with_terminal_history
from tests.integration.test_profiled_asset_lane_custody_receipt_v2 import (
    _binding as _custody_binding,
)
from tests.integration.test_profiled_asset_lane_custody_receipt_v2 import (
    receipt_artifact as receipt_artifact,
)
from tests.integration.test_profiled_perps_margin_receipt_v2 import perps_margin_signed_case


def _setup(protocol_case, receipt_path):
    base = perps_margin_signed_case()
    custody = CustodyPublicationConfigurationV2(
        base.profile, _custody_binding(base, receipt_path.read_bytes()),
        base.signature_manifest, str(receipt_path), protocol_case[1],
    )
    margin_role = replace(base.guest_role_binding, evidence_manifest=replace(
        base.receipt_manifest,
        implementation_root=economic_receipt_verifier_implementation_root_v1(receipt_path.read_bytes()),
    ))
    return base, JointMarginPublicationConfigurationV2(custody, margin_role, str(receipt_path))


def _signed_command(base, head, command, outer_nonce):
    route = base.profile.route_registry.route_for_command(command.command_kind)
    body_hash = hash_economic_command_body_v2(command.command_kind, command)
    occurrence = replace(
        base.request.occurrence, height=head.global_state.height + 1,
        pre_state_root=head.global_state.state_root, command_kind=command.command_kind,
        command_body_hash=body_hash, route_release_id=route.route_release_id, nonce=outer_nonce,
    )
    candidate = _sign(replace(
        base.candidate,
        intent=replace(base.candidate.intent, command_kind=command.command_kind,
                       command_body_hash=body_hash, route_release_id=route.route_release_id,
                       nonce=outer_nonce),
        envelope=replace(base.candidate.envelope, command_body_bytes=canonical_economic_command_body_bytes_v2(
            command.command_kind, command,
        )),
    ))
    return candidate, occurrence


def _margin(base, head, kind, amount, account_nonce, outer_nonce, account="margin-a"):
    command = _command(kind, amount, account_nonce, account)
    candidate, occurrence = _signed_command(base, head, command, outer_nonce)
    return candidate, PerpsMarginRequestV2(command, occurrence)


def _transfer(base, head, amount, outer_nonce):
    command = _transfer_command(amount_atoms=amount)
    candidate, occurrence = _signed_command(base, head, command, outer_nonce)
    return candidate, AssetLaneContextV2(
        head.global_state.writer_epoch, head.custody_state.transfer_state.module_release_id,
        head.global_state.state_root, occurrence,
    ), command


def _open(path, base, configuration, *, create=False):
    method = IsolatedCustodyPublisherV2.create if create else IsolatedCustodyPublisherV2.open
    return method(path, base.global_pre, base.assets, configuration, margin_state=base.margin)


def _publish_margin(publisher, candidate, request, monkeypatch):
    head = publisher.snapshot()
    expected = prepare_perps_margin_statement_v2(
        head.custody_state, head.margin_state, head.global_state, request,
    )
    _receipt_exchange(monkeypatch, expected)
    return publisher.publish(candidate, request, receipt_bytes=_RECEIPT)


def _holdings(head):
    return {row.owner: row.amount_atoms for row in head.global_state.balances}


def test_given_equal_claims_when_drained_transferred_refilled_and_closed_then_one_durable_history(
    tmp_path, protocol_case, receipt_artifact, monkeypatch,
):
    base, configuration = _setup(protocol_case, receipt_artifact)
    path = tmp_path / "joint.sqlite"
    attempts = []
    first_claims = []
    with _open(path, base, configuration, create=True) as publisher:
        # Account nonces are independent; subject replay nonces span both routes.
        history = (
            (DEPOSIT, 30, 1, 1, "margin-a", 70, 30),
            (DEPOSIT, 30, 1, 2, "margin-b", 40, 60),
            (WITHDRAW, 10, 2, 3, "margin-a", 50, 50),
            (WITHDRAW, 20, 3, 4, "margin-a", 70, 30),
        )
        for kind, amount, nonce, outer, account, balance, liability in history:
            candidate, request = _margin(base, publisher.snapshot(), kind, amount, nonce, outer, account)
            result = _publish_margin(publisher, candidate, request, monkeypatch)
            assert result.status is Status.COMMITTED
            attempts.append((candidate, request))
            head = publisher.snapshot()
            assert _holdings(head) == {"alice": balance}
            assert [(row.owner, row.amount_atoms) for row in head.global_state.liabilities] == [("alice", liability)]
            assert sum(row.amount_atoms for row in head.global_state.custody) == liability
            if outer == 2:
                first_claims = [row.obligation_id for row in head.global_state.terminal_obligations]
                assert len(set(first_claims)) == 2
        drained = publisher.snapshot()
        assert drained.margin_state.claim_id("margin-a") is None
        assert drained.margin_state.claim_id("margin-b") in first_claims
        old_terminals = drained.global_state.terminal_obligations
        old_margin = canonical_global_bytes_v2(drained.margin_state)

        candidate, context, command = _transfer(base, drained, 5, 5)
        accepted = transition_asset_lane_custody_v2(context, drained.custody_state, command)
        post = derive_asset_lane_custody_global_post_v2(
            drained.custody_state, accepted, drained.global_state, context.occurrence,
        )
        expected = prepare_asset_lane_custody_global_statement_v2(
            context, drained.custody_state, command, drained.global_state, post,
        )
        _receipt_exchange(monkeypatch, expected)
        assert publisher.publish(candidate, context, command, receipt_bytes=_RECEIPT).status is Status.COMMITTED
        transferred = publisher.snapshot()
        # The existing signed transfer includes a two-atom treasury fee.
        assert _holdings(transferred) == {"alice": 63, "bob": 5, "treasury": 2}
        assert canonical_global_bytes_v2(transferred.margin_state) == old_margin
        assert transferred.global_state.terminal_obligations == old_terminals

        for kind, amount, nonce, outer, account in (
            (DEPOSIT, 20, 4, 6, "margin-a"),
            (WITHDRAW, 20, 5, 7, "margin-a"),
            (WITHDRAW, 30, 2, 8, "margin-b"),
            (CLOSE, 0, 6, 9, "margin-a"),
            (CLOSE, 0, 3, 10, "margin-b"),
        ):
            candidate, request = _margin(base, publisher.snapshot(), kind, amount, nonce, outer, account)
            assert _publish_margin(publisher, candidate, request, monkeypatch).status is Status.COMMITTED
            attempts.append((candidate, request))
            if outer == 6:
                assert publisher.snapshot().margin_state.claim_id("margin-a") not in first_claims
        final = publisher.snapshot()
        assert _holdings(final) == {"alice": 93, "bob": 5, "treasury": 2}
        assert final.sequence == len(final.global_state.replay_state) == 10
        assert final.global_state.supplies == base.global_pre.supplies
        assert final.global_state.custody == final.global_state.liabilities == ()
        assert final.margin_state.active_claims == ()
        assert all(row.status.value == "CLOSED" for row in final.margin_state.economic_state.accounts)
        assert len(final.global_state.terminal_obligations) == 3
        assert all(row.status is TerminalObligationStatusV2.DRAINED for row in final.global_state.terminal_obligations)
        assert final.global_state.history_root == base.global_pre.history_root
        assert final.global_state.outbox == base.global_pre.outbox

    with _open(path, base, configuration) as reopened:
        assert reopened.snapshot() == final
        before = _logical_store(path)
        signatures_before = len(protocol_case[2])
        for candidate, request in attempts:
            assert reopened.publish(candidate, request, receipt_bytes=_RECEIPT).status is Status.ALREADY_COMMITTED
        assert len(protocol_case[2]) == signatures_before
        assert _logical_store(path) == before
        candidate, request = _margin(base, final, DEPOSIT, 1, 7, 11)
        rejected = reopened.publish(candidate, request, receipt_bytes=b"")
        assert type(rejected) is PerpsMarginGlobalRejectedV2
        assert rejected.code.value == "ACCOUNT_CLOSED"
        assert rejected.pre_state_root == rejected.post_state_root == final.global_state.state_root
        assert rejected.effects.is_empty
        assert _logical_store(path) == before
        reopened.revoke()
        revoked_store = _logical_store(path)
        candidate, request = attempts[0]
        assert reopened.publish(candidate, request, receipt_bytes=_RECEIPT).status is Status.ALREADY_COMMITTED
        assert _logical_store(path) == revoked_store
    with pytest.raises(PermissionError, match="authority"):
        _open(path, base, configuration)


@pytest.mark.parametrize("fault", ["economic", "signature", "receipt", "stale", "proof_refusal", "foreign_image"])
def test_given_invalid_margin_attempt_when_processed_then_logical_store_is_unchanged(
    tmp_path, protocol_case, receipt_artifact, monkeypatch, fault,
):
    base, configuration = _setup(protocol_case, receipt_artifact)
    path = tmp_path / "joint.sqlite"
    with _open(path, base, configuration, create=True) as publisher:
        candidate, request = _margin(base, publisher.snapshot(), DEPOSIT, 101 if fault == "economic" else 30, 1, 1)
        if fault == "signature":
            candidate = _sign(candidate, scalar=18)
        elif fault == "receipt":
            receipt_artifact.write_bytes(b"substituted verifier bytes")
        elif fault == "stale":
            request = replace(request, occurrence=replace(request.occurrence, pre_state_root="0x" + "99" * 32))
        elif fault in ("proof_refusal", "foreign_image"):
            expected = prepare_perps_margin_statement_v2(
                base.assets, base.margin, base.global_pre, request,
            )
            _receipt_exchange(monkeypatch, expected)
            exchange = receipt_transport._invoke_v1

            def refuse_receipt(descriptor, raw, timeout):
                response, _, _ = exchange(descriptor, raw, timeout)
                if fault == "proof_refusal":
                    return b"", b"", 2
                return response[:-32] + b"\x99" * 32, b"", 0

            monkeypatch.setattr(receipt_transport, "_invoke_v1", refuse_receipt)
        before = _logical_store(path)
        if fault == "economic":
            result = publisher.publish(candidate, request, receipt_bytes=b"")
            assert type(result) is PerpsMarginGlobalRejectedV2
            assert result.code.value == "INSUFFICIENT_BALANCE"
            assert result.effects.is_empty
        elif fault == "stale":
            assert publisher.publish(candidate, request, receipt_bytes=_RECEIPT).status is Status.STALE_HEAD
        else:
            exception = ValueError if fault == "signature" else GlobalReceiptVerifierErrorV1
            with pytest.raises(exception) as error:
                publisher.publish(candidate, request, receipt_bytes=_RECEIPT)
            if fault in ("proof_refusal", "foreign_image"):
                assert error.value.reason.value == (
                    "VERIFICATION_REJECTED" if fault == "proof_refusal" else "RESPONSE_BINDING"
                )
        assert _logical_store(path) == before
        assert publisher.snapshot().margin_state == base.margin


@pytest.mark.parametrize("interference", ["revoke", "competitor"])
def test_given_verified_margin_when_current_authority_or_head_changes_then_loser_is_noop(
    tmp_path, protocol_case, receipt_artifact, monkeypatch, interference,
):
    base, configuration = _setup(protocol_case, receipt_artifact)
    path = tmp_path / "joint.sqlite"
    real_verifier = implementation.verify_isolated_profiled_perps_margin_receipt_v2
    with _open(path, base, configuration, create=True) as first, _open(path, base, configuration) as second:
        candidate, request = _margin(base, first.snapshot(), DEPOSIT, 30, 1, 1)
        competitor, alternate = _margin(base, second.snapshot(), DEPOSIT, 40, 1, 2)
        winner_store = []

        def interfere_after_verification(*args, **kwargs):
            statement = real_verifier(*args, **kwargs)
            monkeypatch.setattr(implementation, "verify_isolated_profiled_perps_margin_receipt_v2", real_verifier)
            if interference == "revoke":
                second.revoke()
            else:
                assert _publish_margin(second, competitor, alternate, monkeypatch).status is Status.COMMITTED
            winner_store.append(_logical_store(path))
            return statement

        monkeypatch.setattr(implementation, "verify_isolated_profiled_perps_margin_receipt_v2", interfere_after_verification)
        outcome = _publish_margin(first, candidate, request, monkeypatch)
        assert outcome.status is (Status.AUTHORITY_STALE if interference == "revoke" else Status.STALE_HEAD)
        assert _logical_store(path) == winner_store[0]
        head = first.snapshot()
        if interference == "revoke":
            assert head.sequence == 0
            assert head.margin_state == base.margin
        else:
            assert head.sequence == 1
            assert _holdings(head) == {"alice": 60}
            assert head.margin_state.economic_state.accounts[0].collateral_atoms == 40
            assert len(head.global_state.terminal_obligations) == 1


@pytest.mark.parametrize("point", ["INSERT INTO publications", "UPDATE heads SET publication_id", "COMMIT"])
def test_given_interrupted_joint_commit_when_reopened_then_all_three_states_are_pre_or_post(
    tmp_path, protocol_case, receipt_artifact, monkeypatch, point,
):
    base, configuration = _setup(protocol_case, receipt_artifact)
    path = tmp_path / "joint.sqlite"
    with _open(path, base, configuration, create=True) as publisher:
        initial = publisher.snapshot()
        candidate, request = _margin(base, initial, DEPOSIT, 30, 1, 1)
        before = _logical_store(path)
        real_verifier = implementation.verify_isolated_profiled_perps_margin_receipt_v2

        def arm_after_verification(*args, **kwargs):
            statement = real_verifier(*args, **kwargs)
            publisher._connection = _CrashConnection(publisher._connection, point)
            return statement

        monkeypatch.setattr(implementation, "verify_isolated_profiled_perps_margin_receipt_v2", arm_after_verification)
        exception = CustodyPublicationIndeterminateV2 if point == "COMMIT" else RuntimeError
        with pytest.raises(exception):
            _publish_margin(publisher, candidate, request, monkeypatch)
    with _open(path, base, configuration) as recovered:
        head = recovered.snapshot()
        if point == "COMMIT":
            assert head.sequence == 1
            assert _holdings(head) == {"alice": 70}
            assert head.margin_state.economic_state.accounts[0].collateral_atoms == 30
            assert len(head.global_state.terminal_obligations) == len(head.global_state.replay_state) == 1
            assert recovered.publish(candidate, request, receipt_bytes=_RECEIPT).status is Status.ALREADY_COMMITTED
        else:
            assert head == initial
            assert _logical_store(path) == before


def test_given_changed_margin_role_when_restarted_then_no_writer_authority_is_restored(
    tmp_path, protocol_case, receipt_artifact,
):
    base, configuration = _setup(protocol_case, receipt_artifact)
    path = tmp_path / "joint.sqlite"
    with _open(path, base, configuration, create=True):
        pass
    changed_role = replace(configuration.margin_role, evidence_manifest=replace(
        configuration.margin_role.evidence_manifest, root_image_id="0x" + "99" * 32,
    ))
    changed = replace(configuration, margin_role=changed_role)
    before = _logical_store(path)
    with pytest.raises(ValueError, match="configuration"):
        _open(path, base, changed)
    assert _logical_store(path) == before


def test_given_near_capacity_history_when_deposit_would_make_next_input_undecodable_then_no_commit(
    tmp_path, protocol_case, receipt_artifact, monkeypatch,
):
    from src.integration import profiled_perps_margin_receipt_v2 as admission

    base, configuration = _setup(protocol_case, receipt_artifact)
    terminal_history = _inputs_with_terminal_history(2252)[2].terminal_obligations
    base = replace(base, global_pre=replace(base.global_pre, terminal_obligations=terminal_history))
    path = tmp_path / "joint.sqlite"
    monkeypatch.setattr(admission, "_verify_selected_custody_statement_v2", lambda *_: pytest.fail("receipt IO"))
    with _open(path, base, configuration, create=True) as publisher:
        initial = publisher.snapshot()
        candidate, request = _margin(base, initial, DEPOSIT, 1, 1, 1)
        before = _logical_store(path)
        outcome = publisher.publish(candidate, request, receipt_bytes=b"")
        assert type(outcome) is PerpsMarginGlobalRejectedV2
        assert outcome.code.value == "SUCCESSOR_REJECTED"
        assert outcome.pre_state_root == outcome.post_state_root == initial.global_state.state_root
        assert outcome.effects.is_empty
        assert len(protocol_case[2]) == 1
        assert _logical_store(path) == before
        assert publisher.snapshot() == initial
