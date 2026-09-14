"""Isolated publication controls; receipt IPC fixtures are not RISC0 proofs."""

import os
import sqlite3
from dataclasses import replace

import pytest

from src.core.asset_lane_coordinator_values_v2 import AssetLaneRejectedV2
from src.core.asset_lane_custody_coordinator_v2 import transition_asset_lane_custody_v2
from src.core.asset_lane_state_v2 import AssetLaneContextV2
from src.core.economic_command_authentication_v2 import (
    prepare_isolated_economic_command_authentication_v2,
)
from src.core.global_settlement_primitives_v2 import canonical_global_bytes_v2
from src.core.perps_margin_wire_v2 import PerpsMarginRequestV2
from src.integration import isolated_custody_publisher_v2 as implementation
from src.integration.custody_publication_record_v2 import custody_request_id_v2
from src.integration.global_receipt_verifier_v1 import GlobalReceiptVerifierErrorV1
from src.integration.isolated_custody_publisher_v2 import (
    CustodyPublicationConfigurationV2,
    CustodyPublicationIndeterminateV2,
    CustodyPublicationRequestV2,
    CustodyPublicationStatusV2,
    IsolatedCustodyPublisherV2,
)
from tests.integration.test_authenticated_asset_lane_custody_receipt_v2 import (
    _RECEIPT,
    _case,
    _receipt_exchange,
    _sign,
)
from tests.integration.test_isolated_economic_command_authentication_v2 import (
    protocol_case as protocol_case,
)
from tests.integration.test_profiled_asset_lane_custody_receipt_v2 import (
    _binding,
)
from tests.integration.test_profiled_asset_lane_custody_receipt_v2 import (
    receipt_artifact as receipt_artifact,
)
from tests.integration.test_profiled_perps_margin_receipt_v2 import (
    perps_margin_signed_case,
)


def _configuration(case, signature_path, receipt_path):
    return CustodyPublicationConfigurationV2(
        case.candidate.profile,
        _binding(case, receipt_path.read_bytes()),
        case.manifest,
        str(receipt_path),
        signature_path,
    )


def _create(tmp_path, case, configuration):
    return IsolatedCustodyPublisherV2.create(
        tmp_path / "custody.sqlite", case.inputs[3], case.inputs[1], configuration
    )


def _publish(publisher, case, receipt=_RECEIPT):
    return publisher.publish(
        case.candidate,
        CustodyPublicationRequestV2(case.inputs[0], case.inputs[2]),
        receipt_bytes=receipt,
    )


def _logical_store(path):
    with sqlite3.connect(f"file:{path}?mode=ro", uri=True) as connection:
        return tuple(
            tuple(connection.execute(f"SELECT * FROM {table} ORDER BY 1"))
            for table in ("genesis", "authority_history", "publications", "heads")
        )


def test_given_legacy_custody_pair_when_owned_request_is_published_then_request_bytes_are_identical(
    tmp_path, protocol_case, receipt_artifact, monkeypatch
):
    _, signature_path, _ = protocol_case
    case = _case()
    context, command = case.inputs[0], case.inputs[2]
    legacy_context_bytes = canonical_global_bytes_v2(context)
    legacy_command_bytes = canonical_global_bytes_v2(command)
    request = CustodyPublicationRequestV2(context, command)
    assert request.context is not context
    assert request.command is not command
    object.__setattr__(context, "writer_epoch", context.writer_epoch + 1)
    assert canonical_global_bytes_v2(request.context) == legacy_context_bytes
    assert canonical_global_bytes_v2(request.command) == legacy_command_bytes
    owned, _, message = prepare_isolated_economic_command_authentication_v2(case.candidate)
    legacy_request_parts = (
        legacy_context_bytes,
        legacy_command_bytes,
        message,
        owned.envelope.signature_bytes,
        _RECEIPT,
    )
    configuration = _configuration(case, signature_path, receipt_artifact)
    _receipt_exchange(monkeypatch, case.expected)
    with _create(tmp_path, case, configuration) as publisher:
        assert publisher.publish(
            case.candidate, request, receipt_bytes=_RECEIPT
        ).status is CustodyPublicationStatusV2.COMMITTED
        _, records = publisher._read()
    assert records[0].request_parts == legacy_request_parts
    assert records[0].request_id == custody_request_id_v2(*legacy_request_parts)
    assert records[0].request_id == "0x54f07f0a2a1f484fec67c310361418ee8df1a49718ec8a5fba242bad3fa84515"


def test_given_unsupported_request_after_authentication_preparation_when_published_then_tables_are_unchanged(
    tmp_path, protocol_case, receipt_artifact, monkeypatch
):
    class DerivedCustodyPublicationRequestV2(CustodyPublicationRequestV2):
        pass

    class DerivedPerpsMarginRequestV2(PerpsMarginRequestV2):
        pass

    _, signature_path, _ = protocol_case
    case = _case()
    configuration = _configuration(case, signature_path, receipt_artifact)
    authenticated = []
    prepare = implementation.prepare_isolated_economic_command_authentication_v2

    def record_authentication(candidate):
        authenticated.append(candidate)
        return prepare(candidate)

    monkeypatch.setattr(
        implementation,
        "prepare_isolated_economic_command_authentication_v2",
        record_authentication,
    )
    forged_request = CustodyPublicationRequestV2(case.inputs[0], case.inputs[2])
    object.__setattr__(forged_request, "context", object())
    margin_request = perps_margin_signed_case().request
    with _create(tmp_path, case, configuration) as publisher:
        before = _logical_store(tmp_path / "custody.sqlite")
        for unsupported_request, error in (
            (object(), "exact route-owned"),
            (
                DerivedCustodyPublicationRequestV2(case.inputs[0], case.inputs[2]),
                "exact route-owned",
            ),
            (forged_request, "custody publication context"),
            (margin_request, "margin publication needs"),
            (
                DerivedPerpsMarginRequestV2(
                    margin_request.command,
                    margin_request.occurrence,
                    margin_request.oracle,
                ),
                "exact route-owned",
            ),
        ):
            with pytest.raises(TypeError, match=error):
                publisher.publish(case.candidate, unsupported_request, receipt_bytes=_RECEIPT)
        assert authenticated == [case.candidate] * 5
        assert _logical_store(tmp_path / "custody.sqlite") == before
        assert publisher.snapshot().sequence == 0
    with pytest.raises(TypeError, match="context"):
        CustodyPublicationRequestV2(object(), case.inputs[2])
    with pytest.raises(TypeError, match="asset lane command"):
        CustodyPublicationRequestV2(case.inputs[0], object())


def test_given_authenticated_transfer_when_reopened_then_complete_post_and_exact_retry(
    tmp_path, protocol_case, receipt_artifact, monkeypatch
):
    _, signature_path, signatures = protocol_case
    case = _case()
    configuration = _configuration(case, signature_path, receipt_artifact)
    exchanges = _receipt_exchange(monkeypatch, case.expected)
    accepted = transition_asset_lane_custody_v2(*case.inputs[:3])
    with _create(tmp_path, case, configuration) as publisher:
        before = publisher.snapshot()
        result = _publish(publisher, case)
        assert result.status is CustodyPublicationStatusV2.COMMITTED
        after = publisher.snapshot()
        assert after.sequence == before.sequence + 1
        assert after.global_state.to_canonical() == case.inputs[4].to_canonical()
        assert after.custody_state.to_canonical() == accepted.post_state.to_canonical()
        assert after.global_state.custody == before.global_state.custody
        assert after.global_state.liabilities == before.global_state.liabilities
        assert after.global_state.history_root == before.global_state.history_root
    with IsolatedCustodyPublisherV2.open(
        tmp_path / "custody.sqlite", case.inputs[3], case.inputs[1], configuration
    ) as reopened:
        assert reopened.snapshot().publication_id == after.publication_id
        retried = _publish(reopened, case)
        assert retried.status is CustodyPublicationStatusV2.ALREADY_COMMITTED
        assert retried.committed_publication_id == after.publication_id
        assert len(exchanges) == len(signatures) == 1


def test_given_revocation_when_new_request_then_no_economic_change(
    tmp_path, protocol_case, receipt_artifact
):
    _, signature_path, signatures = protocol_case
    case = _case()
    configuration = _configuration(case, signature_path, receipt_artifact)
    with _create(tmp_path, case, configuration) as publisher:
        before = publisher.snapshot()
        publisher.revoke()
        result = _publish(publisher, case)
        assert result.status is CustodyPublicationStatusV2.AUTHORITY_STALE
        assert publisher.snapshot().publication_id == before.publication_id
        assert signatures == []
    with pytest.raises(PermissionError, match="authority"):
        IsolatedCustodyPublisherV2.open(
            tmp_path / "custody.sqlite", case.inputs[3], case.inputs[1], configuration
        )


@pytest.mark.parametrize("index", [1, 2, 3, 4])
def test_given_supported_custody_command_when_committed_then_fixed_economic_result(
    tmp_path, protocol_case, receipt_artifact, monkeypatch, index
):
    _, signature_path, _ = protocol_case
    case = _case(index)
    configuration = _configuration(case, signature_path, receipt_artifact)
    _receipt_exchange(monkeypatch, case.expected)
    with _create(tmp_path, case, configuration) as publisher:
        assert _publish(publisher, case).status is CustodyPublicationStatusV2.COMMITTED
        assert publisher.snapshot().global_state.to_canonical() == case.inputs[4].to_canonical()


@pytest.mark.parametrize("failure", ["economic", "signature", "receipt", "wrong_head"])
def test_given_rejected_request_when_processed_then_every_durable_table_is_unchanged(
    tmp_path, protocol_case, receipt_artifact, monkeypatch, failure
):
    _, signature_path, _ = protocol_case
    case = _case(amount=0) if failure == "economic" else _case()
    configuration = _configuration(case, signature_path, receipt_artifact)
    if failure == "signature":
        case = replace(case, candidate=_sign(case.candidate, scalar=18))
    if failure == "receipt":
        receipt_artifact.write_bytes(b"substituted verifier")
    if failure == "wrong_head":
        original = case.inputs[0]
        context = AssetLaneContextV2(
            original.writer_epoch, original.module_release_id, "0x" + "99" * 32, original.occurrence
        )
        case = replace(case, inputs=(context, *case.inputs[1:]))
    with _create(tmp_path, case, configuration) as publisher:
        before = _logical_store(tmp_path / "custody.sqlite")
        if failure == "economic":
            result = _publish(publisher, case, b"")
            assert type(result) is AssetLaneRejectedV2
            assert result == case.expected
        elif failure == "wrong_head":
            assert _publish(publisher, case).status is CustodyPublicationStatusV2.STALE_HEAD
        else:
            exception = GlobalReceiptVerifierErrorV1 if failure == "receipt" else ValueError
            with pytest.raises(exception):
                _publish(publisher, case)
        assert _logical_store(tmp_path / "custody.sqlite") == before
        assert publisher.snapshot().sequence == 0


def test_given_commit_then_revocation_when_exact_retry_then_acknowledge_only_old_commit(
    tmp_path, protocol_case, receipt_artifact, monkeypatch
):
    _, signature_path, signatures = protocol_case
    case = _case()
    configuration = _configuration(case, signature_path, receipt_artifact)
    exchanges = _receipt_exchange(monkeypatch, case.expected)
    with _create(tmp_path, case, configuration) as publisher:
        committed = _publish(publisher, case)
        publisher.revoke()
        before = _logical_store(tmp_path / "custody.sqlite")
        retry = _publish(publisher, case)
        assert retry.status is CustodyPublicationStatusV2.ALREADY_COMMITTED
        assert retry.committed_publication_id == committed.committed_publication_id
        assert (
            _publish(publisher, case, _RECEIPT + b"x").status
            is CustodyPublicationStatusV2.AUTHORITY_STALE
        )
        assert _logical_store(tmp_path / "custody.sqlite") == before
        assert len(exchanges) == len(signatures) == 1


def test_given_verification_in_flight_when_another_connection_revokes_then_commit_is_noop(
    tmp_path, protocol_case, receipt_artifact, monkeypatch
):
    _, signature_path, _ = protocol_case
    case = _case()
    configuration = _configuration(case, signature_path, receipt_artifact)
    _receipt_exchange(monkeypatch, case.expected)
    real_verifier = implementation.verify_isolated_profiled_asset_lane_custody_receipt_v2
    with (
        _create(tmp_path, case, configuration) as first,
        IsolatedCustodyPublisherV2.open(
            tmp_path / "custody.sqlite", case.inputs[3], case.inputs[1], configuration
        ) as operator,
    ):
        after_revoke = []

        def revoke_after_verification(*args, **kwargs):
            statement = real_verifier(*args, **kwargs)
            operator.revoke()
            after_revoke.append(_logical_store(tmp_path / "custody.sqlite"))
            return statement

        monkeypatch.setattr(
            implementation,
            "verify_isolated_profiled_asset_lane_custody_receipt_v2",
            revoke_after_verification,
        )
        assert _publish(first, case).status is CustodyPublicationStatusV2.AUTHORITY_STALE
        assert _logical_store(tmp_path / "custody.sqlite") == after_revoke[0]
        assert first.snapshot().sequence == 0


def test_given_two_writers_from_same_source_when_competing_then_exactly_one_complete_commit(
    tmp_path, protocol_case, receipt_artifact, monkeypatch
):
    _, signature_path, _ = protocol_case
    first_case, second_case = _case(), _case(amount=11)
    configuration = _configuration(first_case, signature_path, receipt_artifact)
    _receipt_exchange(monkeypatch, first_case.expected)
    real_verifier = implementation.verify_isolated_profiled_asset_lane_custody_receipt_v2
    with (
        _create(tmp_path, first_case, configuration) as first,
        IsolatedCustodyPublisherV2.open(
            tmp_path / "custody.sqlite", first_case.inputs[3], first_case.inputs[1], configuration
        ) as second,
    ):
        winner = []

        def commit_competitor_after_verification(*args, **kwargs):
            statement = real_verifier(*args, **kwargs)
            monkeypatch.setattr(
                implementation,
                "verify_isolated_profiled_asset_lane_custody_receipt_v2",
                real_verifier,
            )
            _receipt_exchange(monkeypatch, second_case.expected)
            winner.append(_publish(second, second_case))
            return statement

        monkeypatch.setattr(
            implementation,
            "verify_isolated_profiled_asset_lane_custody_receipt_v2",
            commit_competitor_after_verification,
        )
        assert _publish(first, first_case).status is CustodyPublicationStatusV2.STALE_HEAD
        assert winner[0].status is CustodyPublicationStatusV2.COMMITTED
        assert first.snapshot().sequence == 1
        assert first.snapshot().global_state.to_canonical() == second_case.inputs[4].to_canonical()
        assert len(_logical_store(tmp_path / "custody.sqlite")[2]) == 1


@pytest.mark.parametrize("changed", ["genesis", "role", "signature_manifest", "name"])
def test_given_restart_when_expected_subject_changes_then_refuse_without_writes(
    tmp_path, protocol_case, receipt_artifact, changed
):
    _, signature_path, signatures = protocol_case
    case = _case()
    configuration = _configuration(case, signature_path, receipt_artifact)
    with _create(tmp_path, case, configuration):
        pass
    path = tmp_path / "custody.sqlite"
    global_state = case.inputs[3]
    if changed == "genesis":
        global_state = replace(global_state, history_root="0x" + "77" * 32)
    elif changed == "role":
        role = replace(
            configuration.guest_role_binding,
            evidence_manifest=replace(
                configuration.guest_role_binding.evidence_manifest, source_root="0x" + "78" * 32
            ),
        )
        configuration = replace(configuration, guest_role_binding=role)
    elif changed == "signature_manifest":
        configuration = replace(
            configuration,
            signature_manifest=replace(
                configuration.signature_manifest, source_root="0x" + "79" * 32
            ),
        )
    else:
        renamed = path.with_name("other.sqlite")
        path.rename(renamed)
        path = renamed
    before = _logical_store(path)
    with pytest.raises(ValueError, match="configuration"):
        IsolatedCustodyPublisherV2.open(path, global_state, case.inputs[1], configuration)
    assert _logical_store(path) == before
    assert signatures == []


class _CrashConnection:
    """Exercise real SQL/rollback, interrupting immediately after a named write."""

    def __init__(self, connection, prefix):
        self.connection, self.prefix = connection, prefix
        self.armed = True

    def __getattr__(self, name):
        return getattr(self.connection, name)

    def execute(self, sql, parameters=()):
        result = self.connection.execute(sql, parameters)
        if self.armed and sql.startswith(self.prefix):
            self.armed = False
            raise RuntimeError("injected interruption after SQL")
        return result


@pytest.mark.parametrize(
    "point", ["INSERT INTO publications", "UPDATE heads SET publication_id", "COMMIT"]
)
def test_given_interruption_when_recovered_then_complete_pre_or_post(
    tmp_path, protocol_case, receipt_artifact, monkeypatch, point
):
    _, signature_path, _ = protocol_case
    case = _case()
    configuration = _configuration(case, signature_path, receipt_artifact)
    _receipt_exchange(monkeypatch, case.expected)
    with _create(tmp_path, case, configuration) as publisher:
        before = _logical_store(tmp_path / "custody.sqlite")
        real_verifier = implementation.verify_isolated_profiled_asset_lane_custody_receipt_v2

        def arm_after_verification(*args, **kwargs):
            statement = real_verifier(*args, **kwargs)
            publisher._connection = _CrashConnection(publisher._connection, point)
            return statement

        monkeypatch.setattr(
            implementation,
            "verify_isolated_profiled_asset_lane_custody_receipt_v2",
            arm_after_verification,
        )
        exception = CustodyPublicationIndeterminateV2 if point == "COMMIT" else RuntimeError
        with pytest.raises(exception):
            _publish(publisher, case)
    with IsolatedCustodyPublisherV2.open(
        tmp_path / "custody.sqlite", case.inputs[3], case.inputs[1], configuration
    ) as recovered:
        if point == "COMMIT":
            assert recovered.snapshot().sequence == 1
            assert recovered.snapshot().global_state.to_canonical() == case.inputs[4].to_canonical()
            assert _publish(recovered, case).status is CustodyPublicationStatusV2.ALREADY_COMMITTED
        else:
            assert recovered.snapshot().sequence == 0
            assert _logical_store(tmp_path / "custody.sqlite") == before


@pytest.mark.parametrize("surface", ["statement", "frame", "source_publication_id", "schema"])
def test_given_corrupt_history_when_reopening_then_fail_closed(
    tmp_path, protocol_case, receipt_artifact, monkeypatch, surface
):
    _, signature_path, _ = protocol_case
    case = _case()
    configuration = _configuration(case, signature_path, receipt_artifact)
    _receipt_exchange(monkeypatch, case.expected)
    with _create(tmp_path, case, configuration) as publisher:
        _publish(publisher, case)
    path = tmp_path / "custody.sqlite"
    with sqlite3.connect(path) as attacker:
        if surface == "schema":
            attacker.execute("CREATE TABLE extra(value TEXT)")
        elif surface == "source_publication_id":
            attacker.execute("UPDATE publications SET source_publication_id=?", ("0x" + "44" * 32,))
        else:
            attacker.execute(f"UPDATE publications SET {surface}=?", (b"corrupt",))
    with pytest.raises(ValueError):
        IsolatedCustodyPublisherV2.open(path, case.inputs[3], case.inputs[1], configuration)


def test_given_capacity_exhaustion_when_revoked_then_fencing_remains_available(
    tmp_path, protocol_case, receipt_artifact, monkeypatch
):
    _, signature_path, _ = protocol_case
    case = _case()
    configuration = _configuration(case, signature_path, receipt_artifact)
    _receipt_exchange(monkeypatch, case.expected)
    with _create(tmp_path, case, configuration) as publisher:
        monkeypatch.setattr(implementation, "MAX_CUSTODY_PUBLICATIONS_V2", 0)
        before = _logical_store(tmp_path / "custody.sqlite")
        assert _publish(publisher, case).status is CustodyPublicationStatusV2.CAPACITY_EXCEEDED
        assert _logical_store(tmp_path / "custody.sqlite") == before
        assert publisher.revoke().status.value == "REVOKED"


def test_given_existing_store_when_create_retried_then_no_replace(
    tmp_path, protocol_case, receipt_artifact
):
    _, signature_path, _ = protocol_case
    case = _case()
    configuration = _configuration(case, signature_path, receipt_artifact)
    with _create(tmp_path, case, configuration):
        before = _logical_store(tmp_path / "custody.sqlite")
        with pytest.raises(FileExistsError):
            _create(tmp_path, case, configuration)
        assert _logical_store(tmp_path / "custody.sqlite") == before


@pytest.mark.parametrize("kind", ["mode", "hardlink", "symlink", "wal"])
def test_given_unqualified_filesystem_identity_when_opening_then_refuse(
    tmp_path, protocol_case, receipt_artifact, kind
):
    _, signature_path, _ = protocol_case
    case = _case()
    configuration = _configuration(case, signature_path, receipt_artifact)
    with _create(tmp_path, case, configuration):
        pass
    path = tmp_path / "custody.sqlite"
    if kind == "mode":
        path.chmod(0o644)
    elif kind == "hardlink":
        os.link(path, tmp_path / "alias")
    elif kind == "symlink":
        target = path.with_name("original.sqlite")
        path.rename(target)
        path.symlink_to(target)
    else:
        path.with_name(path.name + "-wal").write_bytes(b"unqualified")
    with pytest.raises((ValueError, PermissionError)):
        IsolatedCustodyPublisherV2.open(path, case.inputs[3], case.inputs[1], configuration)


def test_unverified_material_has_no_direct_mint_or_raw_commit_entry(
    tmp_path, protocol_case, receipt_artifact
):
    _, signature_path, _ = protocol_case
    case = _case()
    configuration = _configuration(case, signature_path, receipt_artifact)
    with _create(tmp_path, case, configuration) as publisher:
        # Retains the entry points from the successful pre-repair bypass.
        with pytest.raises(TypeError):
            publisher._read(mint_token=True)
        assert not hasattr(publisher, "_commit")
        assert publisher.snapshot().sequence == 0


@pytest.mark.parametrize("point", ["connect", "before_link", "after_link"])
def test_given_bootstrap_interruption_when_retried_then_install_exact_genesis(
    tmp_path, protocol_case, receipt_artifact, monkeypatch, point
):
    _, signature_path, _ = protocol_case
    case = _case()
    configuration = _configuration(case, signature_path, receipt_artifact)
    connect, link = implementation.sqlite3.connect, implementation.os.link

    def interrupted_connect(*args, **kwargs):
        raise RuntimeError("bootstrap connect interruption")

    def interrupted_link(*args, **kwargs):
        if point == "after_link":
            link(*args, **kwargs)
        raise RuntimeError("bootstrap link interruption")

    monkeypatch.setattr(
        implementation.sqlite3, "connect", interrupted_connect if point == "connect" else connect
    )
    monkeypatch.setattr(implementation.os, "link", interrupted_link if point != "connect" else link)
    with pytest.raises(RuntimeError, match="interruption"):
        _create(tmp_path, case, configuration)
    path = tmp_path / "custody.sqlite"
    if point != "after_link":
        assert not path.exists()
    else:
        assert path.stat().st_nlink == 2
    monkeypatch.setattr(implementation.sqlite3, "connect", connect)
    monkeypatch.setattr(implementation.os, "link", link)
    with _create(tmp_path, case, configuration) as recovered:
        assert recovered.snapshot().sequence == 0
        assert recovered.snapshot().global_state.to_canonical() == case.inputs[3].to_canonical()
        assert recovered.snapshot().custody_state.to_canonical() == case.inputs[1].to_canonical()
        assert path.stat().st_nlink == 1
        assert not path.with_name("." + path.name + ".custody-bootstrap-v2").exists()


def test_given_foreign_bootstrap_candidate_when_create_then_preserve_it(
    tmp_path, protocol_case, receipt_artifact
):
    _, signature_path, _ = protocol_case
    case = _case()
    configuration = _configuration(case, signature_path, receipt_artifact)
    candidate = tmp_path / ".custody.sqlite.custody-bootstrap-v2"
    with sqlite3.connect(candidate) as foreign:
        foreign.execute("CREATE TABLE unrelated(x)")
    candidate.chmod(0o600)
    before = candidate.read_bytes()
    with pytest.raises(ValueError, match="schema"):
        _create(tmp_path, case, configuration)
    assert candidate.read_bytes() == before
    assert not (tmp_path / "custody.sqlite").exists()


def test_given_revocation_response_loss_when_retried_then_resolve_terminal_authority(
    tmp_path, protocol_case, receipt_artifact
):
    _, signature_path, _ = protocol_case
    case = _case()
    configuration = _configuration(case, signature_path, receipt_artifact)
    with _create(tmp_path, case, configuration) as publisher:
        publisher._connection = _CrashConnection(publisher._connection, "COMMIT")
        with pytest.raises(CustodyPublicationIndeterminateV2, match="authority"):
            publisher.revoke()
        assert publisher.revoke().status.value == "REVOKED"
        assert publisher.snapshot().sequence == 0


def test_given_failed_rollback_when_closing_then_indeterminate_and_recover_pre(
    tmp_path, protocol_case, receipt_artifact, monkeypatch
):
    _, signature_path, _ = protocol_case
    case = _case()
    configuration = _configuration(case, signature_path, receipt_artifact)
    _receipt_exchange(monkeypatch, case.expected)

    class RollbackFailure(_CrashConnection):
        def execute(self, sql, parameters=()):
            if sql == "ROLLBACK":
                raise sqlite3.OperationalError("injected rollback failure")
            return super().execute(sql, parameters)

    with _create(tmp_path, case, configuration) as publisher:
        publisher._connection = RollbackFailure(publisher._connection, "INSERT INTO publications")
        with pytest.raises(CustodyPublicationIndeterminateV2, match="rollback"):
            _publish(publisher, case)
    with IsolatedCustodyPublisherV2.open(
        tmp_path / "custody.sqlite", case.inputs[3], case.inputs[1], configuration
    ) as reopened:
        assert reopened.snapshot().sequence == 0
