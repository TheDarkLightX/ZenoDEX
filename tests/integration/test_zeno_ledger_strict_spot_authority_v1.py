from __future__ import annotations

import base64
import hashlib
import json
from copy import deepcopy
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

import pytest

from src.core.dex import DexState
from src.integration._zeno_ledger_pinned_verifier_process_v1 import (
    VerifierExecutableFormatV1,
    execute_pinned_verifier_once,
)
from src.integration.dex_engine import DexEngineConfig
from src.integration.dex_snapshot import state_from_snapshot
from src.integration.zeno_ledger_profile import (
    sample_zeno_sovereign_testnet_profile_v0,
)
from src.integration.zeno_ledger_proof_authority_consumer_v1 import (
    ProofAuthorityDecisionStatusV1,
    ProofAuthorityDecisionV1,
    make_governed_proof_authority_binding_v1,
)
from src.integration.zeno_ledger_replay import (
    replay_engine_config_digest_v0,
    replay_engine_config_digest_v1,
    replay_engine_config_document_v0,
    replay_engine_config_document_v1,
)
from src.integration.zeno_ledger_strict_spot_authority_v1 import (
    SPOT_AUTHORITY_RESULT_SCHEMA_V1,
    STRICT_SPOT_AUTHORITY_SCOPE_V1,
    STRICT_SPOT_TRANSACTION_BRIDGE_SCHEMA_V1,
    PinnedStrictSpotAuthorityVerifierV1,
    StrictSpotAuthorityError,
    StrictSpotAuthorityRejectReasonV1,
    _parse_and_bind_response,
    _prepare_request,
    _PreparedRequestV1,
    _require_token,
    strict_spot_authority_manifest_bytes_v1,
)
from src.integration.zeno_ledger_v0 import (
    ZERO_ROOT_V0,
    build_checkpoint_v0,
    build_header_v0,
    build_proof_metadata_v0,
    compute_tx_root_v0,
    hash_v0,
    proof_metadata_hash_v0,
)
from src.integration.zeno_ledger_verifier_registry_v0 import (
    make_verifier_registry_entry_v0,
    make_verifier_registry_v0,
    validate_proof_metadata_against_verifier_registry_v0,
)
from src.state.canonical import canonical_json_bytes

_CHAIN_ID = "zeno-strict-spot-protocol-test-0"
_HEIGHT = 7
_BLOCK_TIMESTAMP = 1_778_730_000
_JOURNAL = b"strict-spot-protocol-fixture-journal-v1"
_JOURNAL_SHA256 = hashlib.sha256(_JOURNAL).hexdigest()
_STATE_BRIDGE_FIXTURE = (
    Path(__file__).resolve().parents[2]
    / "tests/fixtures/zrpf_spot_state_root_v5_bridge_v1.json"
)
_FALSE_FACT_FIELDS = (
    "block_timestamp_directly_committed_in_spot_journal",
    "chain_and_height_directly_committed_in_spot_journal",
    "spot_app_hash_equals_zeno_ledger_state_root_verified",
    "data_availability_verified",
    "proof_metadata_object_verified",
    "serialized_facts_are_opaque_capability",
    "governed_policy_registry_join_verified",
    "settlement_authority",
    "production_authority",
)


def _root(label: str) -> str:
    return hash_v0("strict_spot_authority_protocol_test_v1", {"label": label})


def _fake_response(
    request: Mapping[str, Any],
    *,
    mutation: str = "",
    spot_state_roots: Mapping[str, str] | None = None,
) -> bytes:
    expectations = request["authority_expectations"]
    header = request["ledger_header"]
    transactions = request["block"]["transactions"]
    canonical_batch = canonical_json_bytes(transactions)
    spot_root = _root("fake-verified-spot-root")
    facts: dict[str, Any] = {
        "schema": SPOT_AUTHORITY_RESULT_SCHEMA_V1,
        "authority_scope": STRICT_SPOT_AUTHORITY_SCOPE_V1,
        "authority_manifest_sha256": expectations["authority_manifest_sha256"],
        "verifier_registry_id": expectations["verifier_registry_id"],
        "verifier_registry_entry_id": expectations["verifier_registry_entry_id"],
        "policy_id": expectations["policy_id"],
        "chain_id": expectations["chain_id"],
        "height": expectations["height"],
        "valid_from_height": expectations["valid_from_height"],
        "valid_until_height": expectations["valid_until_height"],
        "proof_profile": expectations["proof_profile"],
        "actual_image_id": expectations["expected_image_id"],
        "receipt_codec": expectations["receipt_codec"],
        "receipt_kind": expectations["receipt_kind"],
        "receipt_verifier_parameters": expectations["receipt_verifier_parameters"],
        "receipt_hashfn": expectations["receipt_hashfn"],
        "receipt_control_id": expectations["receipt_control_id"],
        "canonical_receipt_sha256": "aa" * 32,
        "canonical_journal_sha256": _JOURNAL_SHA256,
        "canonical_journal_base64": base64.b64encode(_JOURNAL).decode("ascii"),
        "state_hash": request["state_hash"],
        "spot_pre_app_hash": (
            spot_root
            if spot_state_roots is None
            else spot_state_roots["source_pre_app_hash"]
        ),
        "spot_post_app_hash": (
            spot_root
            if spot_state_roots is None
            else spot_state_roots["source_post_app_hash"]
        ),
        "spot_pre_nonce_root": (
            spot_root
            if spot_state_roots is None
            else spot_state_roots["source_pre_nonce_root"]
        ),
        "spot_post_nonce_root": (
            spot_root
            if spot_state_roots is None
            else spot_state_roots["source_post_nonce_root"]
        ),
        "spot_ingress_commitment": spot_root,
        "spot_accepted_receipts_root": spot_root,
        "spot_tx_execution_order_commitment": spot_root,
        "spot_route_price_intervals_root": spot_root,
        "spot_route_price_interval_authority_root": spot_root,
        "spot_route_price_interval_authority_policy_root": spot_root,
        "spot_shared_pool_frontier_signature_certificates_root": spot_root,
        "block_timestamp": expectations["block_timestamp"],
        "ledger_header_time_ms": header["time_ms"],
        "canonical_header_hash": expectations["canonical_header_hash"],
        "proof_metadata_hash": expectations["proof_metadata_hash"],
        "proof_commitment": expectations["proof_commitment"],
        "ledger_pre_state_root": header["pre_state_root"],
        "ledger_post_state_root": header["post_state_root"],
        "ledger_app_hash": header["app_hash"],
        "ledger_evidence_root": header["evidence_root"],
        "ledger_body_root": header["body_root"],
        "ledger_data_availability_root": header["data_availability_root"],
        "ledger_proof_journal_hash": header["proof_journal_hash"],
        "config_digest": expectations["config_digest"],
        "module_versions_digest": expectations["module_versions_digest"],
        "public_policy_hash": expectations["public_policy_hash"],
        "feature_suite_hash": expectations["feature_suite_hash"],
        "dependency_lock_hash": expectations["dependency_lock_hash"],
        "toolchain_lock_hash": expectations["toolchain_lock_hash"],
        "transaction_domain_bridge": {
            "schema": STRICT_SPOT_TRANSACTION_BRIDGE_SCHEMA_V1,
            "tx_count": len(transactions),
            "canonical_transaction_batch_sha256": hashlib.sha256(
                canonical_batch
            ).hexdigest(),
            "spot_txs_commitment": spot_root,
            "zeno_ledger_tx_root": header["tx_root"],
            "roots_are_domain_distinct": True,
        },
    }
    facts.update({field: False for field in _FALSE_FACT_FIELDS})
    if mutation == "height":
        facts["height"] += 1
    return canonical_json_bytes(
        {
            "schema": SPOT_AUTHORITY_RESULT_SCHEMA_V1,
            "schema_version": 1,
            "ok": True,
            "authenticated_spot_proof_facts": facts,
        }
    )


def _write_protocol_verifier(
    path: Path,
    *,
    counter_path: Path,
    mutation: str = "",
) -> Path:
    source = f"""#!/usr/bin/python3
import base64
import hashlib
import json
from pathlib import Path
import sys

counter = Path({str(counter_path)!r})
count = int(counter.read_text(encoding="utf-8")) if counter.exists() else 0
counter.write_text(str(count + 1), encoding="utf-8")
request = json.load(sys.stdin)
expectations = request["authority_expectations"]
header = request["ledger_header"]
transactions = request["block"]["transactions"]
journal = {_JOURNAL!r}
spot_root = {_root("fake-verified-spot-root")!r}
canonical_batch = json.dumps(
    transactions,
    sort_keys=True,
    separators=(",", ":"),
    ensure_ascii=False,
).encode("utf-8")
facts = {{
    "schema": {SPOT_AUTHORITY_RESULT_SCHEMA_V1!r},
    "authority_scope": {STRICT_SPOT_AUTHORITY_SCOPE_V1!r},
    "authority_manifest_sha256": expectations["authority_manifest_sha256"],
    "verifier_registry_id": expectations["verifier_registry_id"],
    "verifier_registry_entry_id": expectations["verifier_registry_entry_id"],
    "policy_id": expectations["policy_id"],
    "chain_id": expectations["chain_id"],
    "height": expectations["height"],
    "valid_from_height": expectations["valid_from_height"],
    "valid_until_height": expectations["valid_until_height"],
    "proof_profile": expectations["proof_profile"],
    "actual_image_id": expectations["expected_image_id"],
    "receipt_codec": expectations["receipt_codec"],
    "receipt_kind": expectations["receipt_kind"],
    "receipt_verifier_parameters": expectations["receipt_verifier_parameters"],
    "receipt_hashfn": expectations["receipt_hashfn"],
    "receipt_control_id": expectations["receipt_control_id"],
    "canonical_receipt_sha256": "aa" * 32,
    "canonical_journal_sha256": hashlib.sha256(journal).hexdigest(),
    "canonical_journal_base64": base64.b64encode(journal).decode("ascii"),
    "state_hash": request["state_hash"],
    "spot_pre_app_hash": spot_root,
    "spot_post_app_hash": spot_root,
    "spot_pre_nonce_root": spot_root,
    "spot_post_nonce_root": spot_root,
    "spot_ingress_commitment": spot_root,
    "spot_accepted_receipts_root": spot_root,
    "spot_tx_execution_order_commitment": spot_root,
    "spot_route_price_intervals_root": spot_root,
    "spot_route_price_interval_authority_root": spot_root,
    "spot_route_price_interval_authority_policy_root": spot_root,
    "spot_shared_pool_frontier_signature_certificates_root": spot_root,
    "block_timestamp": expectations["block_timestamp"],
    "ledger_header_time_ms": header["time_ms"],
    "canonical_header_hash": expectations["canonical_header_hash"],
    "proof_metadata_hash": expectations["proof_metadata_hash"],
    "proof_commitment": expectations["proof_commitment"],
    "ledger_pre_state_root": header["pre_state_root"],
    "ledger_post_state_root": header["post_state_root"],
    "ledger_app_hash": header["app_hash"],
    "ledger_evidence_root": header["evidence_root"],
    "ledger_body_root": header["body_root"],
    "ledger_data_availability_root": header["data_availability_root"],
    "ledger_proof_journal_hash": header["proof_journal_hash"],
    "config_digest": expectations["config_digest"],
    "module_versions_digest": expectations["module_versions_digest"],
    "public_policy_hash": expectations["public_policy_hash"],
    "feature_suite_hash": expectations["feature_suite_hash"],
    "dependency_lock_hash": expectations["dependency_lock_hash"],
    "toolchain_lock_hash": expectations["toolchain_lock_hash"],
    "transaction_domain_bridge": {{
        "schema": {STRICT_SPOT_TRANSACTION_BRIDGE_SCHEMA_V1!r},
        "tx_count": len(transactions),
        "canonical_transaction_batch_sha256": hashlib.sha256(canonical_batch).hexdigest(),
        "spot_txs_commitment": spot_root,
        "zeno_ledger_tx_root": header["tx_root"],
        "roots_are_domain_distinct": True,
    }},
}}
for field in {_FALSE_FACT_FIELDS!r}:
    facts[field] = False
if {mutation!r} == "height":
    facts["height"] += 1
json.dump(
    {{
        "schema": {SPOT_AUTHORITY_RESULT_SCHEMA_V1!r},
        "schema_version": 1,
        "ok": True,
        "authenticated_spot_proof_facts": facts,
    }},
    sys.stdout,
    sort_keys=True,
    separators=(",", ":"),
)
"""
    path.write_text(source, encoding="utf-8")
    path.chmod(0o700)
    return path


@dataclass(frozen=True)
class _Case:
    executable: Path
    counter_path: Path
    manifest_bytes: bytes
    manifest_sha256: str
    verifier: PinnedStrictSpotAuthorityVerifierV1
    payload: dict[str, Any]
    metadata: dict[str, Any]
    header: dict[str, Any]
    checkpoint: dict[str, Any]
    replay_config: dict[str, Any]
    profile: dict[str, Any]
    registry: dict[str, Any]
    pre_state: DexState | None = None
    post_state: DexState | None = None

    def prepare(self) -> _PreparedRequestV1:
        return _prepare_request(
            manifest=self.verifier._manifest,
            authority_manifest_sha256=self.manifest_sha256,
            spot_request_payload=self.payload,
            proof_metadata=self.metadata,
            header=self.header,
            checkpoint=self.checkpoint,
            replay_config=self.replay_config,
            profile=self.profile,
            verifier_registry=self.registry,
        )

    def verify_authority(self) -> ProofAuthorityDecisionV1:
        return self.verifier.verify_and_resolve(
            spot_request_payload=self.payload,
            proof_metadata=self.metadata,
            header=self.header,
            checkpoint=self.checkpoint,
            replay_config=self.replay_config,
            profile=self.profile,
            verifier_registry=self.registry,
            pre_state=self.pre_state,
            post_state=self.post_state,
        )


def _make_case(
    tmp_path: Path,
    *,
    executable_format: VerifierExecutableFormatV1,
    response_mutation: str = "",
    bridge_vector: bool = False,
) -> _Case:
    program_id = "risc0:spot:" + _root("program")[2:]
    verifier_id = "risc0:receipt-verifier:v1:spot"
    entry = make_verifier_registry_entry_v0(
        proof_kind="risc0_zkvm_v0",
        program_id=program_id,
        verifier_id=verifier_id,
        valid_from_height=_HEIGHT,
        valid_until_height=_HEIGHT,
    )
    registry = make_verifier_registry_v0(entries=[entry])
    counter_path = tmp_path / "verifier-count.txt"
    executable = _write_protocol_verifier(
        tmp_path / "strict-spot-protocol-verifier.py",
        counter_path=counter_path,
        mutation=response_mutation,
    )
    manifest_bytes = strict_spot_authority_manifest_bytes_v1(
        executable_sha256=hashlib.sha256(executable.read_bytes()).hexdigest(),
        executable_format=executable_format,
        verifier_registry_id=str(registry["registry_id"]),
        verifier_registry_entry_id=str(entry["entry_id"]),
        program_id=program_id,
        verifier_id=verifier_id,
        expected_image_id=_root("expected-image"),
        receipt_kind="succinct",
        receipt_verifier_parameters="risc0-3.0.5-poseidon2-v1",
        receipt_hashfn="poseidon2",
        receipt_control_id="resolve-zkr-control-v1",
        public_policy_hash=_root("public-policy"),
    )
    manifest_sha256 = hashlib.sha256(manifest_bytes).hexdigest()
    policy = make_governed_proof_authority_binding_v1(
        chain_id=_CHAIN_ID,
        authority_manifest_sha256=manifest_sha256,
        verifier_registry_id=str(registry["registry_id"]),
        verifier_registry_entry_id=str(entry["entry_id"]),
        valid_from_height=_HEIGHT,
        valid_until_height=_HEIGHT,
    )
    replay_config = replay_engine_config_document_v1(
        DexEngineConfig(chain_id=_CHAIN_ID),
        proof_authority_policy=policy,
    )
    config_digest = replay_engine_config_digest_v1(replay_config)
    pre_state = None
    post_state = None
    transactions: list[object] = []
    if bridge_vector:
        vector = json.loads(_STATE_BRIDGE_FIXTURE.read_text(encoding="utf-8"))
        sender = vector["sender_pubkey"]
        ingress_nonce = vector["ingress_nonce"]
        transactions = [
            {
                "tx_sender_pubkey": sender,
                "nonce": ingress_nonce,
                "operations": {},
            }
        ]
        pre_state = state_from_snapshot(vector["pre_state"])
        post_state = state_from_snapshot(vector["post_state"])
        pre_state.nonces.set_last(sender, ingress_nonce - 1)
        post_state.nonces.set_last(sender, ingress_nonce)
    source_pre_app_hash = (
        _root("spot-pre-app")
        if not bridge_vector
        else vector["expected"]["source_pre_app_hash"]
    )
    source_post_app_hash = (
        _root("spot-post-app")
        if not bridge_vector
        else vector["expected"]["source_post_app_hash"]
    )
    source_pre_nonce_root = (
        _root("spot-pre-nonce")
        if not bridge_vector
        else vector["expected"]["source_pre_nonce_root"]
    )
    source_post_nonce_root = (
        _root("spot-post-nonce")
        if not bridge_vector
        else vector["expected"]["source_post_nonce_root"]
    )
    proof = {
        "schema": "tau_state_proof",
        "schema_version": 1,
        "state_hash": _root("state-hash"),
        "proof_type": "risc0.zenodex_spot_transition.v1",
        "proof": base64.b64encode(b"protocol-only-retained-receipt").decode("ascii"),
        "meta": {
            "risc0_image_id": _root("expected-image"),
            "txs_commitment": _root("spot-txs"),
            "tx_execution_order_commitment": _root("spot-order"),
            "ingress_commitment": _root("spot-ingress"),
            "pre_nonce_root": source_pre_nonce_root,
            "post_nonce_root": source_post_nonce_root,
            "accepted_receipts_root": _root("spot-receipts"),
            "pre_app_hash": source_pre_app_hash,
            "post_app_hash": source_post_app_hash,
            "protocol_fee_share_bps": 0,
            "protocol_fee_recipient_pubkey": None,
            "route_price_interval_count": 0,
            "route_price_intervals_root": _root("spot-route-intervals"),
            "route_price_interval_authority_root": _root("spot-route-authority"),
            "route_price_interval_authority_policy_root": _root("public-policy"),
            "route_price_interval_max_width_bps": 0,
            "shared_pool_frontier_signature_certificate_count": 0,
            "shared_pool_frontier_signature_certificates_root": _root("spot-frontier"),
            "receipt_codec": "risc0_receipt_canonical_serde_json_depth128_v1",
            "receipt_kind": "succinct",
            "receipt_verifier_parameters": "risc0-3.0.5-poseidon2-v1",
            "receipt_hashfn": "poseidon2",
            "receipt_control_id": "resolve-zkr-control-v1",
        },
    }
    shared_roots = {
        "pre_state_root": (
            _root("ledger-pre-state")
            if not bridge_vector
            else vector["expected"]["pre_state_root_v5"]
        ),
        "post_state_root": (
            _root("ledger-post-state")
            if not bridge_vector
            else vector["expected"]["post_state_root_v5"]
        ),
        "tx_root": compute_tx_root_v0(transactions),
        "evidence_root": _root("ledger-evidence"),
        "body_root": _root("ledger-body"),
    }
    metadata = build_proof_metadata_v0(
        chain_id=_CHAIN_ID,
        height=_HEIGHT,
        proof_kind="risc0_zkvm_v0",
        program_id=program_id,
        verifier_id=verifier_id,
        proof_commitment=hash_v0("risc0_tau_state_proof_envelope_v0", proof),
        public_input_hash=_root("public-input"),
        journal_hash="0x" + _JOURNAL_SHA256,
        conflict_schedule_hash=_root("conflict-schedule"),
        feature_suite_hash=_root("feature-suite"),
        dependency_lock_hash=_root("dependency-lock"),
        toolchain_lock_hash=_root("toolchain-lock"),
        **shared_roots,
    )
    header = build_header_v0(
        chain_id=_CHAIN_ID,
        height=_HEIGHT,
        time_ms=_BLOCK_TIMESTAMP * 1_000,
        prev_header_hash=ZERO_ROOT_V0,
        sequencer_set_hash=_root("sequencers"),
        ingress_root=_root("ingress"),
        app_hash=_root("ledger-app"),
        data_availability_root=_root("data-availability"),
        proof_journal_hash=proof_metadata_hash_v0(metadata),
        config_digest=config_digest,
        module_versions_digest=_root("module-versions"),
        signature_set_root=ZERO_ROOT_V0,
        **shared_roots,
    )
    profile = sample_zeno_sovereign_testnet_profile_v0(
        chain_id=_CHAIN_ID,
        config_digest=config_digest,
        sequencer_set_hash=str(header["sequencer_set_hash"]),
        token_symbol="tZENO",
        token_asset_id=_root("token"),
        proof_required=True,
    )
    payload = {
        "state_hash": proof["state_hash"],
        "proof": proof,
        "block": {
            "header": {"timestamp": _BLOCK_TIMESTAMP},
            "transactions": transactions,
        },
        "tau_state": {"app_hash": source_post_app_hash},
        "context": {
            "app_hash_pre": source_pre_app_hash,
            "block_timestamp": _BLOCK_TIMESTAMP,
            "pre_nonces": [],
            "protocol_fee_share_bps": 0,
            "protocol_fee_recipient_pubkey": None,
            "tx_execution_order": [],
            "route_price_intervals": [],
            "route_price_interval_authority": None,
            "route_price_interval_authority_policy": None,
            "route_price_interval_max_width_bps": 0,
            "shared_pool_frontier_signature_certificates": [],
        },
        "trusted_route_price_interval_authority_policy_root": _root("public-policy"),
    }
    verifier = PinnedStrictSpotAuthorityVerifierV1(
        executable=executable.resolve(),
        authority_manifest_json=manifest_bytes,
        authority_manifest_sha256=manifest_sha256,
    )
    return _Case(
        executable=executable,
        counter_path=counter_path,
        manifest_bytes=manifest_bytes,
        manifest_sha256=manifest_sha256,
        verifier=verifier,
        payload=payload,
        metadata=metadata,
        header=header,
        checkpoint=build_checkpoint_v0(header),
        replay_config=replay_config,
        profile=profile,
        registry=registry,
        pre_state=pre_state,
        post_state=post_state,
    )


def test_protocol_fixture_executes_once_and_matches_host_recomposition(tmp_path: Path) -> None:
    """A deterministic fake checks transport only and mints no authority."""

    case = _make_case(tmp_path, executable_format=VerifierExecutableFormatV1.TEST_SCRIPT)
    prepared = case.prepare()

    stdout = execute_pinned_verifier_once(
        executable=case.executable.resolve(),
        expected_sha256=hashlib.sha256(case.executable.read_bytes()).hexdigest(),
        executable_format=VerifierExecutableFormatV1.TEST_SCRIPT,
        request_bytes=prepared.request_bytes,
        timeout_seconds=10,
        max_address_space_bytes=512 * 1024 * 1024,
        max_stack_bytes=8 * 1024 * 1024,
    )
    facts = _parse_and_bind_response(
        stdout,
        prepared=prepared,
        manifest=case.verifier._manifest,
    )

    assert facts["height"] == _HEIGHT
    assert case.counter_path.read_text(encoding="utf-8") == "1"
    assert facts["settlement_authority"] is False
    assert facts["production_authority"] is False


def test_authority_method_rejects_test_script_without_execution(tmp_path: Path) -> None:
    case = _make_case(tmp_path, executable_format=VerifierExecutableFormatV1.TEST_SCRIPT)

    with pytest.raises(StrictSpotAuthorityError) as caught:
        case.verify_authority()

    assert caught.value.reason is StrictSpotAuthorityRejectReasonV1.EXECUTABLE_POLICY_MISMATCH
    assert not case.counter_path.exists()


def test_static_orchestration_calls_verifier_once_but_state_bridge_stays_pending(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Mocked protocol output exercises orchestration, not receipt evidence."""

    case = _make_case(
        tmp_path,
        executable_format=VerifierExecutableFormatV1.STATIC_ELF_X86_64,
    )
    call_count = 0

    def fake_execute(**kwargs: Any) -> bytes:
        nonlocal call_count
        call_count += 1
        request = json.loads(kwargs["request_bytes"])
        return _fake_response(request)

    monkeypatch.setattr(
        "src.integration.zeno_ledger_strict_spot_authority_v1.execute_pinned_verifier_once",
        fake_execute,
    )

    decision = case.verify_authority()

    assert call_count == 1
    assert decision.status is ProofAuthorityDecisionStatusV1.REQUIRED_PENDING
    assert decision.required is True
    assert decision.satisfied is False
    assert _root("fake-verified-spot-root") != case.header["post_state_root"]
    pending = decision.pending_report()
    assert pending is not None
    assert pending["missing_bindings"] == [
        "authenticated_spot_to_ledger_state_domain_bridge",
    ]


def test_exact_replayed_state_bridge_satisfies_proof_authority_after_one_execution(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The private bridge closes proof authority without promoting settlement."""

    case = _make_case(
        tmp_path,
        executable_format=VerifierExecutableFormatV1.STATIC_ELF_X86_64,
        bridge_vector=True,
    )
    vector = json.loads(_STATE_BRIDGE_FIXTURE.read_text(encoding="utf-8"))
    expected = vector["expected"]
    spot_state_roots = {
        "source_pre_app_hash": expected["source_pre_app_hash"],
        "source_post_app_hash": expected["source_post_app_hash"],
        "source_pre_nonce_root": expected["source_pre_nonce_root"],
        "source_post_nonce_root": expected["source_post_nonce_root"],
    }
    call_count = 0

    def fake_execute(**kwargs: Any) -> bytes:
        nonlocal call_count
        call_count += 1
        request = json.loads(kwargs["request_bytes"])
        response = _fake_response(request, spot_state_roots=spot_state_roots)
        facts = json.loads(response)["authenticated_spot_proof_facts"]
        assert facts["settlement_authority"] is False
        assert facts["production_authority"] is False
        return response

    monkeypatch.setattr(
        "src.integration.zeno_ledger_strict_spot_authority_v1.execute_pinned_verifier_once",
        fake_execute,
    )

    decision = case.verify_authority()

    assert call_count == 1
    assert decision.status is ProofAuthorityDecisionStatusV1.SATISFIED
    assert decision.required is True
    assert decision.satisfied is True
    assert decision.pending_report() is None


def test_state_bridge_uses_pre_execution_state_capture(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Verifier-side effects cannot change the replay state being joined."""

    case = _make_case(
        tmp_path,
        executable_format=VerifierExecutableFormatV1.STATIC_ELF_X86_64,
        bridge_vector=True,
    )
    assert case.pre_state is not None
    assert case.post_state is not None
    pre_state = case.pre_state
    post_state = case.post_state
    vector = json.loads(_STATE_BRIDGE_FIXTURE.read_text(encoding="utf-8"))
    expected = vector["expected"]
    sender = vector["sender_pubkey"]
    ingress_nonce = vector["ingress_nonce"]
    spot_state_roots = {
        "source_pre_app_hash": expected["source_pre_app_hash"],
        "source_post_app_hash": expected["source_post_app_hash"],
        "source_pre_nonce_root": expected["source_pre_nonce_root"],
        "source_post_nonce_root": expected["source_post_nonce_root"],
    }
    call_count = 0

    def fake_execute(**kwargs: Any) -> bytes:
        nonlocal call_count
        call_count += 1
        pre_state.nonces.set_last(sender, ingress_nonce + 100)
        post_state.nonces.set_last(sender, ingress_nonce + 101)
        return _fake_response(
            json.loads(kwargs["request_bytes"]),
            spot_state_roots=spot_state_roots,
        )

    monkeypatch.setattr(
        "src.integration.zeno_ledger_strict_spot_authority_v1.execute_pinned_verifier_once",
        fake_execute,
    )

    decision = case.verify_authority()

    assert call_count == 1
    assert pre_state.nonces.get_last(sender) == ingress_nonce + 100
    assert post_state.nonces.get_last(sender) == ingress_nonce + 101
    assert decision.status is ProofAuthorityDecisionStatusV1.SATISFIED
    assert decision.satisfied is True


def test_state_bridge_uses_pre_execution_transaction_capture(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    case = _make_case(
        tmp_path,
        executable_format=VerifierExecutableFormatV1.STATIC_ELF_X86_64,
        bridge_vector=True,
    )
    vector = json.loads(_STATE_BRIDGE_FIXTURE.read_text(encoding="utf-8"))
    expected = vector["expected"]
    spot_state_roots = {
        "source_pre_app_hash": expected["source_pre_app_hash"],
        "source_post_app_hash": expected["source_post_app_hash"],
        "source_pre_nonce_root": expected["source_pre_nonce_root"],
        "source_post_nonce_root": expected["source_post_nonce_root"],
    }
    transaction = case.payload["block"]["transactions"][0]
    original_nonce = transaction["nonce"]
    call_count = 0

    def fake_execute(**kwargs: Any) -> bytes:
        nonlocal call_count
        call_count += 1
        transaction["nonce"] = original_nonce + 100
        return _fake_response(
            json.loads(kwargs["request_bytes"]),
            spot_state_roots=spot_state_roots,
        )

    monkeypatch.setattr(
        "src.integration.zeno_ledger_strict_spot_authority_v1.execute_pinned_verifier_once",
        fake_execute,
    )

    decision = case.verify_authority()

    assert call_count == 1
    assert transaction["nonce"] == original_nonce + 100
    assert decision.status is ProofAuthorityDecisionStatusV1.SATISFIED
    assert decision.satisfied is True


def test_registry_binding_uses_one_canonical_prevalidation_capture(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    case = _make_case(
        tmp_path,
        executable_format=VerifierExecutableFormatV1.STATIC_ELF_X86_64,
        bridge_vector=True,
    )
    vector = json.loads(_STATE_BRIDGE_FIXTURE.read_text(encoding="utf-8"))
    expected = vector["expected"]
    spot_state_roots = {
        "source_pre_app_hash": expected["source_pre_app_hash"],
        "source_post_app_hash": expected["source_post_app_hash"],
        "source_pre_nonce_root": expected["source_pre_nonce_root"],
        "source_post_nonce_root": expected["source_post_nonce_root"],
    }
    original_program_id = case.registry["entries"][0]["program_id"]
    validation_count = 0

    def mutate_original_then_validate(*args: Any, **kwargs: Any) -> Any:
        nonlocal validation_count
        validation_count += 1
        case.registry["entries"][0]["program_id"] = "risc0:spot:mutated"
        return validate_proof_metadata_against_verifier_registry_v0(*args, **kwargs)

    def fake_execute(**kwargs: Any) -> bytes:
        return _fake_response(
            json.loads(kwargs["request_bytes"]),
            spot_state_roots=spot_state_roots,
        )

    monkeypatch.setattr(
        "src.integration.zeno_ledger_strict_spot_authority_v1."
        "validate_proof_metadata_against_verifier_registry_v0",
        mutate_original_then_validate,
    )
    monkeypatch.setattr(
        "src.integration.zeno_ledger_strict_spot_authority_v1.execute_pinned_verifier_once",
        fake_execute,
    )

    decision = case.verify_authority()

    assert validation_count == 1
    assert case.registry["entries"][0]["program_id"] != original_program_id
    assert decision.status is ProofAuthorityDecisionStatusV1.SATISFIED
    assert decision.satisfied is True


@pytest.mark.parametrize(
    "mutated_field",
    [
        "source_pre_app_hash",
        "source_post_app_hash",
        "source_pre_nonce_root",
        "source_post_nonce_root",
    ],
)
def test_authenticated_source_root_mismatch_rejects_after_exactly_one_execution(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    mutated_field: str,
) -> None:
    case = _make_case(
        tmp_path,
        executable_format=VerifierExecutableFormatV1.STATIC_ELF_X86_64,
        bridge_vector=True,
    )
    vector = json.loads(_STATE_BRIDGE_FIXTURE.read_text(encoding="utf-8"))
    expected = vector["expected"]
    spot_state_roots = {
        "source_pre_app_hash": expected["source_pre_app_hash"],
        "source_post_app_hash": expected["source_post_app_hash"],
        "source_pre_nonce_root": expected["source_pre_nonce_root"],
        "source_post_nonce_root": expected["source_post_nonce_root"],
    }
    spot_state_roots[mutated_field] = "0x" + "ff" * 32
    call_count = 0

    def fake_execute(**kwargs: Any) -> bytes:
        nonlocal call_count
        call_count += 1
        return _fake_response(
            json.loads(kwargs["request_bytes"]),
            spot_state_roots=spot_state_roots,
        )

    monkeypatch.setattr(
        "src.integration.zeno_ledger_strict_spot_authority_v1.execute_pinned_verifier_once",
        fake_execute,
    )

    with pytest.raises(StrictSpotAuthorityError) as caught:
        case.verify_authority()

    assert caught.value.reason is StrictSpotAuthorityRejectReasonV1.STATE_DOMAIN_BRIDGE_MISMATCH
    assert call_count == 1


@pytest.mark.parametrize(
    ("mutation", "expected_reason"),
    [
        ("manifest", StrictSpotAuthorityRejectReasonV1.CONFIG_INVALID),
        ("registry", StrictSpotAuthorityRejectReasonV1.REGISTRY_MISMATCH),
        ("config", StrictSpotAuthorityRejectReasonV1.CONFIG_INVALID),
        ("metadata", StrictSpotAuthorityRejectReasonV1.METADATA_MISMATCH),
        ("height", StrictSpotAuthorityRejectReasonV1.HEADER_MISMATCH),
        ("checkpoint", StrictSpotAuthorityRejectReasonV1.HEADER_MISMATCH),
    ],
)
def test_outer_identity_substitution_rejects_before_process(
    tmp_path: Path,
    mutation: str,
    expected_reason: StrictSpotAuthorityRejectReasonV1,
) -> None:
    case = _make_case(tmp_path, executable_format=VerifierExecutableFormatV1.TEST_SCRIPT)
    payload: Mapping[str, Any] = case.payload
    metadata: Mapping[str, Any] = case.metadata
    header: Mapping[str, Any] = case.header
    checkpoint: Mapping[str, Any] = case.checkpoint
    replay_config: Mapping[str, Any] = case.replay_config
    profile: Mapping[str, Any] = case.profile
    registry: Mapping[str, Any] = case.registry
    if mutation == "manifest":
        config = deepcopy(case.replay_config)
        config["proof_authority_policy"]["authority_manifest_sha256"] = "11" * 32
        replay_config = config
    elif mutation == "registry":
        registry_mutation = deepcopy(case.registry)
        registry_mutation["registry_id"] = _root("wrong-registry")
        registry = registry_mutation
    elif mutation == "config":
        config = deepcopy(case.replay_config)
        config["proof_authority_policy"]["policy_id"] = _root("wrong-policy")
        replay_config = config
    elif mutation == "metadata":
        metadata_mutation = deepcopy(case.metadata)
        metadata_mutation["proof_commitment"] = _root("wrong-proof-commitment")
        metadata = metadata_mutation
    elif mutation == "height":
        header_mutation = deepcopy(case.header)
        header_mutation["height"] = _HEIGHT + 1
        header = header_mutation
    else:
        checkpoint_mutation = deepcopy(case.checkpoint)
        checkpoint_mutation["header_hash"] = _root("wrong-header")
        checkpoint = checkpoint_mutation

    with pytest.raises(StrictSpotAuthorityError) as caught:
        _prepare_request(
            manifest=case.verifier._manifest,
            authority_manifest_sha256=case.manifest_sha256,
            spot_request_payload=payload,
            proof_metadata=metadata,
            header=header,
            checkpoint=checkpoint,
            replay_config=replay_config,
            profile=profile,
            verifier_registry=registry,
        )

    assert caught.value.reason is expected_reason
    assert not case.counter_path.exists()


def test_v0_config_cannot_project_into_proof_required_adapter(tmp_path: Path) -> None:
    case = _make_case(tmp_path, executable_format=VerifierExecutableFormatV1.TEST_SCRIPT)
    v0_config = replay_engine_config_document_v0(DexEngineConfig(chain_id=_CHAIN_ID))
    assert replay_engine_config_digest_v0(v0_config) != case.header["config_digest"]

    with pytest.raises(StrictSpotAuthorityError) as caught:
        _prepare_request(
            manifest=case.verifier._manifest,
            authority_manifest_sha256=case.manifest_sha256,
            spot_request_payload=case.payload,
            proof_metadata=case.metadata,
            header=case.header,
            checkpoint=case.checkpoint,
            replay_config=v0_config,
            profile=case.profile,
            verifier_registry=case.registry,
        )

    assert caught.value.reason is StrictSpotAuthorityRejectReasonV1.CONFIG_INVALID
    assert not case.counter_path.exists()


def test_response_height_substitution_rejects_after_one_protocol_execution(
    tmp_path: Path,
) -> None:
    case = _make_case(
        tmp_path,
        executable_format=VerifierExecutableFormatV1.TEST_SCRIPT,
        response_mutation="height",
    )
    prepared = case.prepare()

    stdout = execute_pinned_verifier_once(
        executable=case.executable.resolve(),
        expected_sha256=hashlib.sha256(case.executable.read_bytes()).hexdigest(),
        executable_format=VerifierExecutableFormatV1.TEST_SCRIPT,
        request_bytes=prepared.request_bytes,
        timeout_seconds=10,
        max_address_space_bytes=512 * 1024 * 1024,
        max_stack_bytes=8 * 1024 * 1024,
    )
    with pytest.raises(StrictSpotAuthorityError) as caught:
        _parse_and_bind_response(
            stdout,
            prepared=prepared,
            manifest=case.verifier._manifest,
        )

    assert caught.value.reason is StrictSpotAuthorityRejectReasonV1.RESPONSE_MISMATCH
    assert case.counter_path.read_text(encoding="utf-8") == "1"


def test_manifest_policy_graph_is_acyclic_and_config_owns_policy(tmp_path: Path) -> None:
    case = _make_case(tmp_path, executable_format=VerifierExecutableFormatV1.TEST_SCRIPT)
    manifest = json.loads(case.manifest_bytes)

    assert "policy_id" not in manifest
    assert "config_digest" not in manifest
    assert (
        case.replay_config["proof_authority_policy"]["authority_manifest_sha256"]
        == case.manifest_sha256
    )


def test_strict_token_parser_matches_rust_utf8_length_precedence() -> None:
    assert _require_token("a" * 256, name="fixture.token") == "a" * 256

    with pytest.raises(ValueError, match="at most 256 UTF-8 bytes"):
        _require_token("a" * 257, name="fixture.token")

    within_byte_cap = "é" * 128
    assert len(within_byte_cap.encode("utf-8")) == 256
    with pytest.raises(ValueError, match="contains unsupported characters"):
        _require_token(within_byte_cap, name="fixture.token")

    above_byte_cap = within_byte_cap + "a"
    assert len(above_byte_cap.encode("utf-8")) == 257
    with pytest.raises(ValueError, match="at most 256 UTF-8 bytes"):
        _require_token(above_byte_cap, name="fixture.token")
