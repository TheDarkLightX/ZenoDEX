from __future__ import annotations

import copy
import hashlib
import json
import sqlite3
import subprocess
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

import pytest

import src.integration.zrpf_source_opened_spot_v6_verifier_adapter as source_adapter
from src.core._zrpf_settlement_certificate_authority import (
    _source_opened_spot_v6_projection_binding_v1,
)
from src.core.zrpf_settlement_effect_plan import (
    AuthorizationConsumptionV1,
    authorization_consumption_nullifier_v1,
)
from src.integration._zrpf_authenticated_certificate_store_engine import (
    _GRANT_LIST_DOMAIN,
    _identifier_list_digest,
)
from src.integration._zrpf_settlement_admission_journal_codec import (
    SETTLEMENT_ADMISSION_FIXED_BYTES_V1,
    derive_settlement_certificate_id_v1,
)
from src.integration.recursive_stark_verifier_adapter import (
    RecursiveVerifierExecutableFormat,
)
from src.integration.zrpf_atomic_settlement_store import (
    SQLiteZrpfAtomicSettlementStoreV1,
)
from src.integration.zrpf_atomic_settlement_store_types import (
    ZrpfAtomicSettlementDispositionV1,
    ZrpfAtomicSettlementRejectReasonV1,
    ZrpfAtomicSettlementStoreErrorV1,
)
from src.integration.zrpf_settlement_verifier_adapter import (
    PinnedSettlementCertificateVerifierV1,
)
from src.integration.zrpf_source_opened_spot_v6_live_ledger_gate import (
    SOURCE_OPENED_SPOT_V6_LIVE_LEDGER_AUTHORITY_BLOCKED_REASON_V1,
    SourceOpenedSpotV6LiveLedgerDispositionV1,
    SourceOpenedSpotV6LiveLedgerRejectReasonV1,
    _reject_authenticated_source_opened_spot_v6_live_ledger_value_movement,
)
from src.integration.zrpf_source_opened_spot_v6_verifier_adapter import (
    SOURCE_OPENED_SPOT_V6_AUTHORITY_MANIFEST_SCHEMA,
    SOURCE_OPENED_SPOT_V6_REQUEST_SCHEMA,
    SOURCE_OPENED_SPOT_V6_RESPONSE_SCHEMA,
    PinnedSourceOpenedSpotSettlementVerifierV6,
    SourceOpenedSpotV6VerificationError,
    _parse_source_opened_spot_v6_response,
    source_opened_spot_v6_authority_manifest_bytes,
    source_opened_spot_v6_request_bytes,
)
from tests.integration import test_zrpf_atomic_settlement_store as generic_test_support

_RECEIPT = b"exact-risc0-succinct-receipt"
_CERTIFICATE = b"exact-postcard-settlement-certificate-v1"
_EFFECT_PLAN = b"exact-postcard-settlement-effect-plan-v2"
_DA_CERTIFICATE = b"exact-full-blob-content-certificate"


def _bare(index: int) -> str:
    return f"{index:064x}"


def _prefixed(index: int) -> str:
    return "0x" + _bare(index)


def _root(index: int) -> bytes:
    return bytes.fromhex(_bare(index))


def test_source_opened_adapter_uses_pre_exec_process_contract() -> None:
    source = Path(source_adapter.__file__).read_text(encoding="utf-8")

    assert "execute_pinned_verifier_once" in source
    assert "resource.prlimit" not in source
    assert "subprocess.Popen" not in source
    assert "_apply_resource_limits" not in source


def _guest_input() -> bytes:
    proposal = b"proposal-v5"
    authorization = _root(31) + _root(32) + (7).to_bytes(8, "big") + _root(33)
    witness = b"sparse-witness"
    base = b"".join(
        (
            (2).to_bytes(2, "big"),
            len(proposal).to_bytes(4, "big"),
            proposal,
            authorization,
            len(witness).to_bytes(4, "big"),
            witness,
            len(_DA_CERTIFICATE).to_bytes(4, "big"),
            _DA_CERTIFICATE,
        )
    )
    source = b"source-opened-spot-leaf-input-v6"
    return b"".join(
        (
            (3).to_bytes(2, "big"),
            len(base).to_bytes(4, "big"),
            base,
            len(source).to_bytes(4, "big"),
            source,
        )
    )


def _admission_frame(
    *,
    pre_state: int = 16,
    post_state: int = 17,
) -> tuple[bytes, dict[str, object]]:
    total = SETTLEMENT_ADMISSION_FIXED_BYTES_V1 + len(_CERTIFICATE) + len(_EFFECT_PLAN)
    frame = bytearray()
    frame.extend(b"ZRPFSAV1")
    frame.extend((1).to_bytes(2, "big"))
    frame.extend(total.to_bytes(4, "big"))
    frame.extend(len(_CERTIFICATE).to_bytes(4, "big"))
    frame.extend(len(_EFFECT_PLAN).to_bytes(4, "big"))
    frame.extend(_CERTIFICATE)
    frame.extend(_EFFECT_PLAN)
    frame.extend(hashlib.sha256(_CERTIFICATE).digest())
    frame.extend(hashlib.sha256(_EFFECT_PLAN).digest())
    frame.extend((1).to_bytes(2, "big"))
    frame.extend((2).to_bytes(2, "big"))
    frame.extend(_root(1))
    frame.extend(_root(2))
    frame.extend((9).to_bytes(8, "big"))
    frame.extend(_root(3))
    frame.extend(_root(4))
    frame.extend(_root(5))
    frame.extend(_root(6))
    frame.append(1)
    frame.extend(_root(7))
    for index in range(8, 16):
        frame.extend(_root(index))
    frame.extend((1).to_bytes(4, "big"))
    frame.extend((1).to_bytes(4, "big"))
    for index in (pre_state, post_state, *range(18, 26)):
        frame.extend(_root(index))
    certificate_id = derive_settlement_certificate_id_v1(_CERTIFICATE)
    frame.extend(certificate_id)
    frame.extend(_root(26))
    assert len(frame) == total
    projection: dict[str, object] = {
        "journal_version": 1,
        "certificate_version": 1,
        "effect_plan_version": 2,
        "application_id": _bare(1),
        "chain_or_domain_id": _bare(2),
        "epoch_id": 9,
        "semantic_profile_id": _bare(3),
        "semantic_journal_hash": _bare(4),
        "semantic_claim_binding": _bare(5),
        "proof_tree_root": _bare(6),
        "semantic_root_kind": "value_subtree",
        "semantic_root": _bare(7),
        "dependency_manifest_root": _bare(8),
        "public_policy_hash": _bare(9),
        "economic_action_batch_commitment": _bare(10),
        "settlement_effect_plan_commitment": _bare(11),
        "economic_action_ids_root": _bare(12),
        "action_authorization_bindings_root": _bare(13),
        "authorization_grant_spends_root": _bare(14),
        "consumed_object_ids_root": _bare(15),
        "action_count": 1,
        "consumed_object_count": 1,
        "pre_state_root": _bare(pre_state),
        "post_state_root": _bare(post_state),
        "cell_writes_root": _bare(18),
        "asset_effects_root": _bare(19),
        "messages_root": _bare(20),
        "carries_root": _bare(21),
        "rewards_root": _bare(22),
        "data_availability_certificate_root": _bare(23),
        "schedule_certificate_root": _bare(24),
        "carry_continuity_certificate_root": _bare(25),
        "settlement_certificate_id": certificate_id.hex(),
        "certificate_commitment": _bare(26),
    }
    return bytes(frame), projection


def _execution_projection(
    *,
    pre_state_index: int = 16,
    post_state_index: int = 17,
) -> dict[str, object]:
    action_id = _prefixed(30)
    subject = _prefixed(31)
    scope = _prefixed(32)
    grant = _prefixed(33)
    pre_state = _prefixed(pre_state_index)
    nullifier = authorization_consumption_nullifier_v1(
        application_id=_prefixed(1),
        chain_or_domain_id=_prefixed(2),
        economic_action_id=action_id,
        authorization_subject_id=subject,
        authorization_grant_id=grant,
        authorization_scope_id=scope,
        authorization_nonce=7,
        action_pre_state_root=pre_state,
    )
    authorization = AuthorizationConsumptionV1(
        application_id=_prefixed(1),
        chain_or_domain_id=_prefixed(2),
        economic_action_id=action_id,
        authorization_subject_id=subject,
        authorization_grant_id=grant,
        authorization_scope_id=scope,
        authorization_nonce=7,
        action_pre_state_root=pre_state,
        authorization_nullifier=nullifier,
    )
    return {
        "application_id": _bare(1),
        "chain_or_domain_id": _bare(2),
        "epoch_id": 9,
        "pre_state_root": _bare(pre_state_index),
        "post_state_root": _bare(post_state_index),
        "action": {
            "action_id": _bare(30),
            "action_type_id": _bare(34),
            "authorization_subject_id": _bare(31),
            "authorization_scope_id": _bare(32),
            "authorization_nonce": 7,
            "authorization_grant_id": _bare(33),
            "action_authorization_binding": _bare(35),
            "authorization_grant_spend_nullifier": (
                authorization.authorization_grant_spend_nullifier[2:]
            ),
            "valid_from_epoch": 8,
            "valid_through_epoch": 10,
            "pre_state_root": _bare(pre_state_index),
            "action_semantics_hash": _bare(36),
            "effect_commitment": _bare(37),
            "consumed_object_ids": [_bare(38)],
        },
        "cell_write": {
            "economic_action_id": _bare(30),
            "cell_key": _bare(39),
            "pre_value_hash": _bare(40),
            "post_value_hash": _bare(41),
        },
        "ordinary_asset_rows": [
            {
                "economic_action_id": _bare(30),
                "asset_id": _bare(42),
                "debit_atoms": "17",
                "credit_atoms": "17",
            },
            {
                "economic_action_id": _bare(30),
                "asset_id": _bare(43),
                "debit_atoms": "29",
                "credit_atoms": "29",
            },
        ],
    }


def _receipt_profile() -> dict[str, object]:
    return {
        "profile_id": "risc0_succinct_poseidon2_resolve_3_0_5_v1",
        "receipt_kind": "succinct",
        "verifier_parameters": _bare(60),
        "hashfn": "poseidon2",
        "control_id": _bare(61),
    }


def _policy() -> dict[str, object]:
    return {
        "application_id": _bare(1),
        "chain_id": "zenodex-devnet",
        "chain_or_domain_id": _bare(2),
        "epoch_id": 9,
        "proof_profile": "zrpf_source_opened_spot_settlement_v6",
        "public_policy_hash": _bare(9),
        "verifier_set_root": _bare(62),
        "governed_settlement_program_id": _bare(50),
        "governed_settlement_profile_id": _bare(3),
        "governed_settlement_manifest_root": _bare(51),
        "receipt_security_profile": _receipt_profile(),
    }


def _response(
    *,
    pre_state: int = 16,
    post_state: int = 17,
) -> dict[str, object]:
    journal, projection = _admission_frame(pre_state=pre_state, post_state=post_state)
    guest = _guest_input()
    values = {
        "receipt_bytes": len(_RECEIPT),
        "receipt_sha256": hashlib.sha256(_RECEIPT).hexdigest(),
        "guest_input_bytes": len(guest),
        "guest_input_sha256": hashlib.sha256(guest).hexdigest(),
        "admission_journal_bytes": len(journal),
        "admission_journal_hex": journal.hex(),
        "admission_journal_sha256": hashlib.sha256(journal).hexdigest(),
        "certificate_bytes": len(_CERTIFICATE),
        "certificate_hex": _CERTIFICATE.hex(),
        "certificate_sha256": hashlib.sha256(_CERTIFICATE).hexdigest(),
        "effect_plan_bytes": len(_EFFECT_PLAN),
        "effect_plan_hex": _EFFECT_PLAN.hex(),
        "effect_plan_sha256": hashlib.sha256(_EFFECT_PLAN).hexdigest(),
        "governed_settlement_program_id": _bare(50),
        "governed_settlement_profile_id": _bare(3),
        "governed_settlement_manifest_root": _bare(51),
        "settlement_claim_binding": _bare(52),
        "receipt_security_profile": _receipt_profile(),
        "admission_projection": projection,
        "execution_projection": _execution_projection(
            pre_state_index=pre_state,
            post_state_index=post_state,
        ),
    }
    return {
        "ok": True,
        "schema": SOURCE_OPENED_SPOT_V6_RESPONSE_SCHEMA,
        "verified_settlement_admission": values,
    }


def _response_bytes(response: dict[str, object] | None = None) -> bytes:
    return json.dumps(response or _response(), ensure_ascii=True, separators=(",", ":")).encode(
        "ascii"
    )


def _write_static_verifier(path: Path, response: bytes) -> str:
    source = path.with_suffix(".c")
    source.write_text(
        "#include <stdio.h>\n"
        "int main(void) {\n"
        "  char buffer[4096];\n"
        "  while (fread(buffer, 1, sizeof(buffer), stdin) != 0) {}\n"
        f"  fputs({json.dumps(response.decode('ascii'))}, stdout);\n"
        "  return ferror(stdin) || ferror(stdout);\n"
        "}\n",
        encoding="ascii",
    )
    subprocess.run(
        ["/usr/bin/gcc", "-static", "-O2", "-s", "-o", str(path), str(source)],
        check=True,
        capture_output=True,
    )
    path.chmod(0o700)
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _adapter(tmp_path: Path, response: dict[str, object] | None = None) -> PinnedSourceOpenedSpotSettlementVerifierV6:
    executable = tmp_path / "source-opened-v6-verifier"
    executable_sha256 = _write_static_verifier(executable, _response_bytes(response))
    manifest = source_opened_spot_v6_authority_manifest_bytes(
        executable_sha256=executable_sha256,
        policy=_policy(),
        executable_format=RecursiveVerifierExecutableFormat.STATIC_ELF_X86_64,
    )
    decoded = json.loads(manifest)
    assert decoded["schema"] == SOURCE_OPENED_SPOT_V6_AUTHORITY_MANIFEST_SCHEMA
    return PinnedSourceOpenedSpotSettlementVerifierV6(
        executable=executable,
        authority_manifest_json=manifest,
        authority_manifest_sha256=hashlib.sha256(manifest).hexdigest(),
    )


def _store(tmp_path: Path) -> SQLiteZrpfAtomicSettlementStoreV1:
    return SQLiteZrpfAtomicSettlementStoreV1(
        tmp_path / "source-opened-v6.sqlite3",
        genesis_settlement_state_root=_prefixed(16),
    )


def _commit(
    adapter: PinnedSourceOpenedSpotSettlementVerifierV6,
    store: SQLiteZrpfAtomicSettlementStoreV1,
    *,
    admission_cursor=None,
    settlement_cursor=None,
):
    return adapter.verify_and_commit(
        store=store,
        expected_admission_cursor=admission_cursor or store.read_admission_cursor(),
        expected_settlement_cursor=settlement_cursor or store.read_settlement_cursor(),
        settlement_receipt=_RECEIPT,
        guest_input=_guest_input(),
    )


def test_request_bytes_match_the_exact_rust_struct_field_order() -> None:
    raw = source_opened_spot_v6_request_bytes(_RECEIPT, _guest_input())
    expected = (
        b'{"schema":"'
        + SOURCE_OPENED_SPOT_V6_REQUEST_SCHEMA.encode("ascii")
        + b'","receipt_hex":"'
        + _RECEIPT.hex().encode("ascii")
        + b'","guest_input_hex":"'
        + _guest_input().hex().encode("ascii")
        + b'"}'
    )
    assert raw == expected


def test_response_requires_exact_canonical_rust_json_bytes() -> None:
    with pytest.raises(SourceOpenedSpotV6VerificationError, match="canonical JSON"):
        _parse_source_opened_spot_v6_response(
            _response_bytes() + b"\n",
            settlement_receipt=_RECEIPT,
            guest_input=_guest_input(),
            policy=_policy(),
        )


def test_real_cli_schema_projects_and_atomically_persists_every_exact_artifact(
    tmp_path: Path,
) -> None:
    adapter = _adapter(tmp_path)
    store = _store(tmp_path)

    result = _commit(adapter, store)

    assert result.committed is True
    assert result.settlement_authority is False
    assert result.certificate_receipt is not None
    with sqlite3.connect(store.path) as connection:
        connection.row_factory = sqlite3.Row
        association = connection.execute(
            "SELECT * FROM zrpf_source_opened_spot_v6_associations"
        ).fetchone()
        certificate = connection.execute(
            "SELECT * FROM zrpf_settlement_certificates"
        ).fetchone()
        global_grant = connection.execute(
            "SELECT authorization_grant_spend_nullifier "
            "FROM zrpf_settlement_certificate_grant_spends"
        ).fetchone()
    assert association is not None and certificate is not None and global_grant is not None
    assert bytes(association["settlement_receipt"]) == _RECEIPT
    assert bytes(association["guest_input"]) == _guest_input()
    assert bytes(association["admission_journal"]).hex() == _response()[
        "verified_settlement_admission"
    ]["admission_journal_hex"]  # type: ignore[index]
    assert bytes(certificate["canonical_certificate"]) == _CERTIFICATE
    assert bytes(certificate["exact_effect_plan"]) == _EFFECT_PLAN
    assert bytes(certificate["data_availability_certificate"]) == _DA_CERTIFICATE
    assert hashlib.sha256(bytes(certificate["source_opened_replay"])).digest() == bytes(
        association["source_opened_replay_sha256"]
    )
    assert bytes(association["governed_program_id"]) == _root(50)
    assert bytes(association["governed_profile_id"]) == _root(3)
    assert bytes(association["governed_manifest_root"]) == _root(51)
    assert bytes(global_grant[0]) == bytes(association["authorization_grant_spend_nullifier"])
    assert bytes(association["normalized_plan_commitment"]) == bytes(
        certificate["plan_commitment"]
    )
    assert _store(tmp_path).read_settlement_cursor().revision == 1
    replay = _commit(adapter, _store(tmp_path))
    assert replay.idempotent_replay is True


def _generic_adapter_with_exact_v6_grant(
    tmp_path: Path,
    *,
    v6_first: bool,
) -> tuple[str, PinnedSettlementCertificateVerifierV1]:
    plan = generic_test_support._plan(
        root=231 if v6_first else 230,
        epoch=10 if v6_first else 8,
        pre_state=17 if v6_first else 16,
        post_state=18 if v6_first else 17,
        ordinary_action=212 if v6_first else 210,
        authorized_action=213 if v6_first else 211,
        grant=33,
        cell_base=270 if v6_first else 240,
    )
    grant_spend = plan.authorization_consumptions[0].authorization_grant_spend_nullifier
    action = _execution_projection()["action"]
    assert isinstance(action, dict)
    exact_grant_spend = "0x" + str(action["authorization_grant_spend_nullifier"])
    assert grant_spend == exact_grant_spend
    response = generic_test_support._verified_certificate_response(
        plan,
        seed=70 if v6_first else 71,
    )
    adapter = generic_test_support._certificate_adapter(
        tmp_path,
        response,
        name=f"cross-profile-generic-{'after' if v6_first else 'before'}-v6",
    )
    return grant_spend, adapter


@pytest.mark.parametrize("v6_first", (False, True))
def test_global_grant_spend_rejects_generic_and_exact_v6_in_both_orders(
    tmp_path: Path,
    v6_first: bool,
) -> None:
    shared_grant_spend, generic_adapter = _generic_adapter_with_exact_v6_grant(
        tmp_path,
        v6_first=v6_first,
    )
    v6_adapter = _adapter(
        tmp_path,
        None if v6_first else _response(pre_state=17, post_state=18),
    )
    store = _store(tmp_path)

    if v6_first:
        assert _commit(v6_adapter, store).committed
        rejected = generic_test_support._verify_and_commit_certificate(
            generic_adapter,
            store,
        )
    else:
        assert generic_test_support._verify_and_commit_certificate(
            generic_adapter,
            store,
        ).committed
        rejected = _commit(v6_adapter, store)

    assert rejected.disposition is ZrpfAtomicSettlementDispositionV1.REJECTED
    assert (
        rejected.settlement_reject_reason
        is ZrpfAtomicSettlementRejectReasonV1.DUPLICATE_AUTHORIZATION_GRANT_SPEND
    )
    restarted = _store(tmp_path)
    assert restarted.read_settlement_cursor().revision == 1
    with sqlite3.connect(store.path) as connection:
        rows = connection.execute(
            "SELECT authorization_grant_spend_nullifier "
            "FROM zrpf_settlement_certificate_grant_spends"
        ).fetchall()
    assert rows == [(bytes.fromhex(shared_grant_spend[2:]),)]


def test_concurrent_generic_and_exact_v6_grant_spend_commit_exactly_once(
    tmp_path: Path,
) -> None:
    plan = generic_test_support._plan(
        root=232,
        epoch=9,
        pre_state=16,
        post_state=18,
        ordinary_action=214,
        authorized_action=215,
        grant=33,
        cell_base=300,
    )
    shared_grant_spend = plan.authorization_consumptions[
        0
    ].authorization_grant_spend_nullifier
    generic_adapter = generic_test_support._certificate_adapter(
        tmp_path,
        generic_test_support._verified_certificate_response(plan, seed=72),
        name="concurrent-generic-exact-v6",
    )
    v6_adapter = _adapter(tmp_path)
    stores = (_store(tmp_path), _store(tmp_path))
    admission = stores[0].read_admission_cursor()
    settlement = stores[0].read_settlement_cursor()

    with ThreadPoolExecutor(max_workers=2) as pool:
        futures = (
            pool.submit(
                generic_test_support._verify_and_commit_certificate,
                generic_adapter,
                stores[0],
                admission_cursor=admission,
                settlement_cursor=settlement,
            ),
            pool.submit(
                _commit,
                v6_adapter,
                stores[1],
                admission_cursor=admission,
                settlement_cursor=settlement,
            ),
        )
    results = tuple(future.result() for future in futures)

    assert sum(result.committed for result in results) == 1
    assert sum(
        result.disposition is ZrpfAtomicSettlementDispositionV1.REJECTED
        for result in results
    ) == 1
    restarted = _store(tmp_path)
    assert restarted.read_settlement_cursor().revision == 1
    with sqlite3.connect(restarted.path) as connection:
        rows = connection.execute(
            "SELECT authorization_grant_spend_nullifier "
            "FROM zrpf_settlement_certificate_grant_spends"
        ).fetchall()
    assert rows == [(bytes.fromhex(shared_grant_spend[2:]),)]


def test_two_v6_writers_have_one_commit_and_one_idempotent_replay(tmp_path: Path) -> None:
    adapter = _adapter(tmp_path)
    stores = (_store(tmp_path), _store(tmp_path))
    admission = stores[0].read_admission_cursor()
    settlement = stores[0].read_settlement_cursor()
    with ThreadPoolExecutor(max_workers=2) as pool:
        futures = [
            pool.submit(
                _commit,
                adapter,
                store,
                admission_cursor=admission,
                settlement_cursor=settlement,
            )
            for store in stores
        ]
    results = [future.result() for future in futures]
    assert sum(result.committed for result in results) == 1
    assert sum(result.idempotent_replay for result in results) == 1
    with sqlite3.connect(stores[0].path) as connection:
        assert connection.execute(
            "SELECT count(*) FROM zrpf_source_opened_spot_v6_associations"
        ).fetchone()[0] == 1


def test_authenticated_v6_live_ledger_value_movement_is_a_typed_no_op(
    tmp_path: Path,
) -> None:
    adapter = _adapter(tmp_path)
    store = _store(tmp_path)
    database_before = store.path.read_bytes()
    admission_before = store.read_admission_cursor()
    settlement_before = store.read_settlement_cursor()

    blocked = adapter.verify_live_ledger_value_movement(
        settlement_receipt=_RECEIPT,
        guest_input=_guest_input(),
    )

    assert blocked.disposition is SourceOpenedSpotV6LiveLedgerDispositionV1.BLOCKED
    assert (
        blocked.reject_reason
        is SourceOpenedSpotV6LiveLedgerRejectReasonV1.VALUE_MOVEMENT_AUTHORITY_UNAVAILABLE
    )
    assert (
        blocked.authority_blocked_reason
        == SOURCE_OPENED_SPOT_V6_LIVE_LEDGER_AUTHORITY_BLOCKED_REASON_V1
    )
    assert blocked.epoch_id == 9
    assert blocked.pre_state_root == _prefixed(16)
    assert blocked.post_state_root == _prefixed(17)
    assert blocked.state_changed is False
    assert blocked.replay_indexes_changed is False
    assert blocked.proof_association_changed is False
    assert blocked.live_ledger_prestate_cas_verified is False
    assert blocked.typed_value_transition_verified is False
    assert blocked.durable_atomic_value_commit_verified is False
    assert blocked.settlement_authority is False
    assert blocked.signature_authority is False
    assert blocked.grant_authority is False
    assert blocked.provider_retrievability_verified is False
    assert blocked.external_finality_verified is False
    assert blocked.release_authority is False
    assert blocked.production_authority is False
    assert store.path.read_bytes() == database_before
    assert store.read_admission_cursor() == admission_before
    assert store.read_settlement_cursor() == settlement_before
    with sqlite3.connect(store.path) as connection:
        for table in (
            "zrpf_admissions",
            "zrpf_settlement_plans",
            "zrpf_settlement_certificates",
            "zrpf_source_opened_spot_v6_associations",
            "zrpf_settlement_action_nullifiers",
            "zrpf_settlement_consumed_objects",
        ):
            assert connection.execute(f"SELECT count(*) FROM {table}").fetchone()[0] == 0


def test_proof_only_result_cannot_enter_live_ledger_value_movement_gate(
    tmp_path: Path,
) -> None:
    adapter = _adapter(tmp_path)
    proof_store = _store(tmp_path)
    proof_only_result = _commit(adapter, proof_store)
    assert proof_only_result.committed is True
    assert proof_only_result.settlement_authority is False

    with pytest.raises(TypeError, match="receipt-authenticated V6 capability"):
        _reject_authenticated_source_opened_spot_v6_live_ledger_value_movement(
            proof_only_result  # type: ignore[arg-type]
        )


def test_unsealed_exact_v6_type_cannot_enter_live_ledger_value_movement_gate() -> None:
    from src.core._zrpf_settlement_certificate_authority import (
        _AuthenticatedSourceOpenedSpotV6SettlementV1,
    )

    forged = object.__new__(_AuthenticatedSourceOpenedSpotV6SettlementV1)
    with pytest.raises(TypeError, match="sealed V6 capability"):
        _reject_authenticated_source_opened_spot_v6_live_ledger_value_movement(forged)


@pytest.mark.parametrize(
    ("mutation", "match"),
    (
        ("journal_hash", "admission journal SHA-256"),
        ("certificate_echo", "certificate exact bytes"),
        ("program", "governed_settlement_program_id policy"),
        ("projection", "admission pre_state_root mismatch"),
        ("asset_amount", "ordinary asset row is not conserved"),
        ("grant_spend", "authorization grant spend mismatch"),
    ),
)
def test_response_mutations_reject_before_capability_mint(mutation: str, match: str) -> None:
    response = copy.deepcopy(_response())
    values = response["verified_settlement_admission"]
    assert isinstance(values, dict)
    if mutation == "journal_hash":
        values["admission_journal_sha256"] = _bare(99)
    elif mutation == "certificate_echo":
        values["certificate_hex"] = b"wrong-certificate".hex()
    elif mutation == "program":
        values["governed_settlement_program_id"] = _bare(99)
    elif mutation == "projection":
        projection = values["admission_projection"]
        assert isinstance(projection, dict)
        projection["pre_state_root"] = _bare(99)
    elif mutation == "asset_amount":
        execution = values["execution_projection"]
        assert isinstance(execution, dict)
        rows = execution["ordinary_asset_rows"]
        assert isinstance(rows, list) and isinstance(rows[0], dict)
        rows[0]["credit_atoms"] = "18"
    else:
        execution = values["execution_projection"]
        assert isinstance(execution, dict)
        action = execution["action"]
        assert isinstance(action, dict)
        action["authorization_grant_spend_nullifier"] = _bare(99)

    with pytest.raises(SourceOpenedSpotV6VerificationError, match=match):
        _parse_source_opened_spot_v6_response(
            _response_bytes(response),
            settlement_receipt=_RECEIPT,
            guest_input=_guest_input(),
            policy=_policy(),
        )


@pytest.mark.parametrize(
    ("column", "match"),
    (
        ("settlement_receipt", "settlement_receipt sha256 mismatch"),
        ("guest_input", "guest_input sha256 mismatch"),
        ("admission_journal", "admission_journal sha256 mismatch"),
        ("canonical_projection", "canonical_projection sha256 mismatch"),
    ),
)
def test_restart_rejects_v4_exact_artifact_mutation(
    tmp_path: Path,
    column: str,
    match: str,
) -> None:
    adapter = _adapter(tmp_path)
    store = _store(tmp_path)
    assert _commit(adapter, store).committed
    with sqlite3.connect(store.path) as connection:
        connection.execute(
            f"UPDATE zrpf_source_opened_spot_v6_associations "
            f"SET {column} = CAST({column} || x'00' AS BLOB)"
        )
    with pytest.raises(ZrpfAtomicSettlementStoreErrorV1, match=match):
        _store(tmp_path)


def test_restart_rejects_v4_association_row_downgrade(tmp_path: Path) -> None:
    adapter = _adapter(tmp_path)
    store = _store(tmp_path)
    assert _commit(adapter, store).committed
    with sqlite3.connect(store.path) as connection:
        connection.execute("DELETE FROM zrpf_source_opened_spot_v6_associations")

    with pytest.raises(
        ZrpfAtomicSettlementStoreErrorV1,
        match="association metadata count mismatch",
    ):
        _store(tmp_path)


def test_v3_to_v5_migration_is_empty_certificate_history_only(tmp_path: Path) -> None:
    empty = _store(tmp_path)
    with sqlite3.connect(empty.path) as connection:
        connection.execute("DROP TABLE zrpf_source_opened_spot_v6_associations")
        connection.execute("DROP TABLE zrpf_source_opened_spot_v6_association_meta")
        connection.execute("DROP TABLE zrpf_settlement_certificate_grant_spends")
        connection.execute("PRAGMA user_version = 3")
    reopened = _store(tmp_path)
    with sqlite3.connect(reopened.path) as connection:
        assert connection.execute("PRAGMA user_version").fetchone()[0] == 5
        assert connection.execute(
            "SELECT count(*) FROM zrpf_source_opened_spot_v6_associations"
        ).fetchone()[0] == 0

    second_path = tmp_path / "nonempty.sqlite3"
    nonempty = SQLiteZrpfAtomicSettlementStoreV1(
        second_path,
        genesis_settlement_state_root=_prefixed(16),
    )
    second_adapter_path = tmp_path / "second-adapter"
    second_adapter_path.mkdir()
    assert _commit(_adapter(second_adapter_path), nonempty).committed
    with sqlite3.connect(nonempty.path) as connection:
        connection.execute("DROP TABLE zrpf_source_opened_spot_v6_associations")
        connection.execute("DROP TABLE zrpf_source_opened_spot_v6_association_meta")
        connection.execute("DROP TABLE zrpf_settlement_certificate_grant_spends")
        connection.execute("PRAGMA user_version = 3")
    with pytest.raises(
        ZrpfAtomicSettlementStoreErrorV1,
        match="cannot migrate without exact V6 associations",
    ):
        SQLiteZrpfAtomicSettlementStoreV1(
            second_path,
            genesis_settlement_state_root=_prefixed(16),
        )
    with sqlite3.connect(second_path) as connection:
        assert connection.execute("PRAGMA user_version").fetchone()[0] == 3


def test_v4_to_v5_migration_backfills_exact_v6_association_grant(
    tmp_path: Path,
) -> None:
    adapter = _adapter(tmp_path)
    store = _store(tmp_path)
    assert _commit(adapter, store).committed
    with sqlite3.connect(store.path) as connection:
        expected = connection.execute(
            "SELECT authorization_grant_spend_nullifier "
            "FROM zrpf_source_opened_spot_v6_associations"
        ).fetchone()
        assert expected is not None
        connection.execute("DROP TABLE zrpf_settlement_certificate_grant_spends")
        connection.execute("PRAGMA user_version = 4")

    reopened = _store(tmp_path)

    assert reopened.read_settlement_cursor().revision == 1
    with sqlite3.connect(store.path) as connection:
        assert connection.execute("PRAGMA user_version").fetchone()[0] == 5
        observed = connection.execute(
            "SELECT authorization_grant_spend_nullifier "
            "FROM zrpf_settlement_certificate_grant_spends"
        ).fetchone()
    assert observed == expected


def _projection_binding_with_grant(row: sqlite3.Row, grant_spend: str) -> bytes:
    prefixed_columns = (
        "settlement_certificate_id",
        "certificate_commitment",
        "governed_program_id",
        "governed_profile_id",
        "governed_manifest_root",
        "normalized_plan_commitment",
    )
    prefixed = {
        column: "0x" + bytes(row[column]).hex()
        for column in prefixed_columns
    }
    return bytes.fromhex(
        _source_opened_spot_v6_projection_binding_v1(
            admission_journal_sha256=bytes(row["admission_journal_sha256"]).hex(),
            settlement_receipt_sha256=bytes(row["settlement_receipt_sha256"]).hex(),
            guest_input_sha256=bytes(row["guest_input_sha256"]).hex(),
            source_opened_replay_sha256=bytes(row["source_opened_replay_sha256"]).hex(),
            settlement_certificate_id=prefixed["settlement_certificate_id"],
            certificate_commitment=prefixed["certificate_commitment"],
            governed_program_id=prefixed["governed_program_id"],
            governed_profile_id=prefixed["governed_profile_id"],
            governed_manifest_root=prefixed["governed_manifest_root"],
            authorization_grant_spend_nullifier=grant_spend,
            canonical_projection_sha256=bytes(row["canonical_projection_sha256"]).hex(),
            normalized_plan_commitment=prefixed["normalized_plan_commitment"],
        )
    )


def test_v4_cross_profile_grant_collision_rolls_back_v5_migration(
    tmp_path: Path,
) -> None:
    store = _store(tmp_path)
    generic_plan = generic_test_support._plan(
        root=233,
        epoch=8,
        pre_state=16,
        post_state=17,
        ordinary_action=216,
        authorized_action=217,
        grant=34,
        cell_base=330,
    )
    generic_adapter = generic_test_support._certificate_adapter(
        tmp_path,
        generic_test_support._verified_certificate_response(generic_plan, seed=73),
        name="migration-valid-generic",
    )
    assert generic_test_support._verify_and_commit_certificate(
        generic_adapter,
        store,
    ).committed
    assert _commit(
        _adapter(tmp_path, _response(pre_state=17, post_state=18)),
        store,
    ).committed
    assert _store(tmp_path).read_settlement_cursor().revision == 2
    shared_grant = generic_plan.authorization_consumptions[
        0
    ].authorization_grant_spend_nullifier

    with sqlite3.connect(store.path) as connection:
        connection.row_factory = sqlite3.Row
        association = connection.execute(
            "SELECT * FROM zrpf_source_opened_spot_v6_associations"
        ).fetchone()
        assert association is not None
        replacement_binding = _projection_binding_with_grant(
            association,
            shared_grant,
        )
        connection.execute(
            "UPDATE zrpf_source_opened_spot_v6_associations "
            "SET authorization_grant_spend_nullifier = ?, "
            "canonical_projection_binding_sha256 = ?",
            (bytes.fromhex(shared_grant[2:]), replacement_binding),
        )
        connection.execute(
            "UPDATE zrpf_settlement_certificates "
            "SET authorization_grant_spend_list_sha256 = ? "
            "WHERE certificate_journal_hash = ?",
            (
                _identifier_list_digest(_GRANT_LIST_DOMAIN, (shared_grant,)),
                bytes(association["certificate_journal_hash"]),
            ),
        )
        connection.execute("DROP TABLE zrpf_settlement_certificate_grant_spends")
        connection.execute("PRAGMA user_version = 4")

    with pytest.raises(
        ZrpfAtomicSettlementStoreErrorV1,
        match=(
            "UNIQUE constraint failed: "
            "zrpf_settlement_certificate_grant_spends"
            r"\.authorization_grant_spend_nullifier"
        ),
    ):
        _store(tmp_path)

    with sqlite3.connect(store.path) as connection:
        assert connection.execute("PRAGMA user_version").fetchone()[0] == 4
        names = {
            str(row[0])
            for row in connection.execute(
                "SELECT name FROM sqlite_master WHERE type = 'table'"
            )
        }
    assert "zrpf_settlement_certificate_grant_spends" not in names


def test_legacy_fake_adapter_requires_explicit_test_only_opt_in(tmp_path: Path) -> None:
    executable = tmp_path / "placeholder"
    executable.write_bytes(b"not-an-elf")
    manifest = json.dumps(
        {
            "schema": "placeholder",
        },
        separators=(",", ":"),
    ).encode("ascii")
    from src.integration.zrpf_settlement_verifier_adapter import (
        PinnedSettlementCertificateVerifierV1,
    )

    with pytest.raises(ValueError, match="legacy_test_only=True"):
        PinnedSettlementCertificateVerifierV1(
            executable=executable,
            authority_manifest_json=manifest,
            authority_manifest_sha256=hashlib.sha256(manifest).hexdigest(),
        )
