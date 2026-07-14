from __future__ import annotations

import base64
import hashlib
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import pytest

from src.core.dex import DexState
from src.integration.dex_engine import DexEngineConfig
from src.integration.dex_snapshot import snapshot_from_state
from src.integration.zeno_ledger_authenticated_proof_verification_v1 import (
    RESPONSE_SCHEMA_V1,
    PinnedZenoLedgerRisc0VerifierV1,
    VerifierExecutableFormatV1,
    zeno_ledger_risc0_authority_manifest_bytes_v1,
)
from src.integration.zeno_ledger_profile import (
    clone_profile_with_new_id_v0,
    sample_zeno_sovereign_testnet_profile_v0,
)
from src.integration.zeno_ledger_replay import (
    replay_engine_config_digest_v0,
    replay_engine_config_document_v0,
)
from src.integration.zeno_ledger_v0 import (
    ZERO_ROOT_V0,
    build_checkpoint_v0,
    build_header_v0,
    build_proof_metadata_v0,
    canonical_body_root_v0,
    canonical_json_bytes_v0,
    compute_app_hash_v0,
    compute_evidence_root_v0,
    compute_ingress_root_v0,
    compute_tx_root_v0,
    dex_state_root_v0,
    hash_v0,
    proof_metadata_hash_v0,
)
from src.integration.zeno_ledger_verifier_registry_v0 import (
    make_verifier_registry_entry_v0,
    make_verifier_registry_v0,
)
from src.state.balances import BalanceTable
from src.state.lp import LPTable
from tests.integration.test_zeno_ledger_verify_cli import _body
from tools.zeno_ledger_verify import (
    REPLAY_BOUND_MODE,
    STRUCTURAL_DIAGNOSTIC_MODE,
    verify_zeno_ledger_v0,
)
from tools.zeno_ledger_verify import (
    main as verify_main,
)


def _root(label: str) -> str:
    return hash_v0("test_root_v0", {"label": label})


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _verifier_script(path: Path, *, counter_path: Path) -> Path:
    source = f"""#!/usr/bin/env python3
import base64
import json
from pathlib import Path
import sys

counter = Path({str(counter_path)!r})
count = int(counter.read_text(encoding="utf-8")) if counter.exists() else 0
counter.write_text(str(count + 1), encoding="utf-8")
request = json.load(sys.stdin)
response = {{
    "schema": {RESPONSE_SCHEMA_V1!r},
    "accepted": True,
    "journal_b64": base64.b64encode(b"scoped-test-journal").decode("ascii"),
    "verified_facts": request["expected_verified_facts"],
}}
json.dump(response, sys.stdout, sort_keys=True, separators=(",", ":"))
"""
    path.write_text(source, encoding="utf-8")
    path.chmod(0o700)
    return path


@dataclass(frozen=True)
class _Case:
    headers_dir: Path
    bodies_dir: Path
    checkpoints_dir: Path
    proof_metadata_dir: Path
    proof_artifacts_dir: Path
    proof_reports_dir: Path
    snapshots_dir: Path
    config_path: Path
    profile_path: Path
    verifier: PinnedZenoLedgerRisc0VerifierV1
    registry: dict[str, Any]
    counter_path: Path

    def verify(
        self,
        *,
        mode: str,
        authenticated: bool,
        include_report: bool = True,
        require_report: bool | None = None,
    ) -> dict[str, Any]:
        kwargs: dict[str, Any] = {}
        if authenticated:
            kwargs = {
                "proof_artifacts_dir": self.proof_artifacts_dir,
                "proof_authority_verifier": self.verifier,
                "verifier_registry": self.registry,
            }
        return verify_zeno_ledger_v0(
            headers_dir=self.headers_dir,
            bodies_dir=self.bodies_dir,
            checkpoints_dir=self.checkpoints_dir,
            profile_path=self.profile_path,
            from_height=1,
            to_height=1,
            proof_metadata_dir=self.proof_metadata_dir,
            proof_verification_report_dir=self.proof_reports_dir if include_report else None,
            require_proof_verification_report=(
                include_report if require_report is None else require_report
            ),
            mode=mode,
            pre_snapshots_dir=self.snapshots_dir if mode == REPLAY_BOUND_MODE else None,
            engine_config_path=self.config_path if mode == REPLAY_BOUND_MODE else None,
            require_rejection_receipt_replay=mode == REPLAY_BOUND_MODE,
            **kwargs,
        )


def _make_case(
    tmp_path: Path,
    *,
    executable_format: VerifierExecutableFormatV1 = VerifierExecutableFormatV1.TEST_SCRIPT,
) -> _Case:
    headers_dir = tmp_path / "headers"
    bodies_dir = tmp_path / "bodies"
    checkpoints_dir = tmp_path / "checkpoints"
    proof_metadata_dir = tmp_path / "proof_metadata"
    proof_artifacts_dir = tmp_path / "proof_artifacts"
    proof_reports_dir = tmp_path / "proof_reports"
    snapshots_dir = tmp_path / "pre_snapshots"
    config_path = tmp_path / "engine_config.json"
    profile_path = tmp_path / "profile.json"

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    state_root = dex_state_root_v0(state)
    config = DexEngineConfig(chain_id="zeno-ledger-devnet-0")
    config_document = replay_engine_config_document_v0(config)
    config_digest = replay_engine_config_digest_v0(config_document)
    sequencer_set_hash = _root("sequencer-set")

    body = _body(1, txs=[])
    evidence = body.get("evidence")
    assert isinstance(evidence, dict)
    evidence["rejection_receipts"] = []
    evidence_root = compute_evidence_root_v0(body["evidence"])
    tx_root = compute_tx_root_v0(body["transactions"])
    body_root = canonical_body_root_v0(body)
    artifact = {
        "schema": "tau_state_proof",
        "schema_version": 1,
        "state_hash": _root("state")[2:],
        "proof_type": "risc0.zenodex_spot_transition.v1",
        "proof": base64.b64encode(b"retained-risc0-receipt").decode("ascii"),
        "meta": {"fixture": "proof-required-authority-wiring"},
    }
    artifact_bytes = canonical_json_bytes_v0(artifact)
    program_id = "risc0:spot:" + _root("image-id")[2:]
    verifier_id = "risc0:receipt-verifier:v1:spot"
    metadata = build_proof_metadata_v0(
        chain_id="zeno-ledger-devnet-0",
        height=1,
        proof_kind="risc0_zkvm_v0",
        program_id=program_id,
        verifier_id=verifier_id,
        proof_commitment=hash_v0("risc0_tau_state_proof_envelope_v0", artifact),
        public_input_hash=_root("public-input"),
        journal_hash=_root("journal"),
        pre_state_root=state_root,
        post_state_root=state_root,
        tx_root=tx_root,
        evidence_root=evidence_root,
        body_root=body_root,
        conflict_schedule_hash=_root("schedule"),
        feature_suite_hash=_root("features"),
        dependency_lock_hash=_root("dependency-lock"),
        toolchain_lock_hash=_root("toolchain-lock"),
    )
    module_versions_digest = _root("modules")
    app_hash = compute_app_hash_v0(
        {
            "chain_id": "zeno-ledger-devnet-0",
            "height": 1,
            "post_state_root": state_root,
            "evidence_root": evidence_root,
            "config_digest": config_digest,
            "module_versions_digest": module_versions_digest,
        }
    )
    header = build_header_v0(
        chain_id="zeno-ledger-devnet-0",
        height=1,
        time_ms=1_778_730_000_001,
        prev_header_hash=ZERO_ROOT_V0,
        sequencer_set_hash=sequencer_set_hash,
        ingress_root=compute_ingress_root_v0(body["ingress"]),
        tx_root=tx_root,
        pre_state_root=state_root,
        post_state_root=state_root,
        app_hash=app_hash,
        evidence_root=evidence_root,
        body_root=body_root,
        data_availability_root=_root("data-availability"),
        proof_journal_hash=proof_metadata_hash_v0(metadata),
        config_digest=config_digest,
        module_versions_digest=module_versions_digest,
        signature_set_root=ZERO_ROOT_V0,
    )
    checkpoint = build_checkpoint_v0(header)
    profile = sample_zeno_sovereign_testnet_profile_v0(
        chain_id="zeno-ledger-devnet-0",
        config_digest=config_digest,
        sequencer_set_hash=sequencer_set_hash,
        token_symbol="tZENO",
        token_asset_id=_root("test-token"),
        proof_required=True,
    )

    entry = make_verifier_registry_entry_v0(
        proof_kind="risc0_zkvm_v0",
        program_id=program_id,
        verifier_id=verifier_id,
        valid_from_height=1,
        valid_until_height=1,
    )
    registry = make_verifier_registry_v0(entries=[entry])
    counter_path = tmp_path / "verifier-count.txt"
    executable = _verifier_script(tmp_path / "verifier.py", counter_path=counter_path)
    executable_sha256 = hashlib.sha256(executable.read_bytes()).hexdigest()
    manifest = zeno_ledger_risc0_authority_manifest_bytes_v1(
        executable_sha256=executable_sha256,
        executable_format=executable_format,
        registry_id=str(registry["registry_id"]),
        registry_entry_id=str(entry["entry_id"]),
        program_id=program_id,
        verifier_id=verifier_id,
        actual_image_id=_root("image-id"),
        receipt_kind="succinct",
        hash_function="sha-256",
        verifier_parameters_digest=_root("verifier-parameters"),
        control_id=_root("control-id"),
    )
    verifier = PinnedZenoLedgerRisc0VerifierV1(
        executable=executable.resolve(),
        authority_manifest_json=manifest,
        authority_manifest_sha256=hashlib.sha256(manifest).hexdigest(),
    )

    _write_json(headers_dir / "1.json", header)
    _write_json(bodies_dir / "1.json", body)
    _write_json(checkpoints_dir / "1.json", checkpoint)
    _write_json(proof_metadata_dir / "1.json", metadata)
    proof_artifacts_dir.mkdir(parents=True)
    (proof_artifacts_dir / "1.json").write_bytes(artifact_bytes)
    _write_json(
        proof_reports_dir / "1.json",
        {
            "schema": "zenodex.zeno_ledger.risc0_proof_metadata_report.v0",
            "ok": True,
            "header_bound": True,
            "proof_journal_hash": header["proof_journal_hash"],
            "proof_kind": metadata["proof_kind"],
            "program_id": metadata["program_id"],
            "verifier_id": metadata["verifier_id"],
            "toolchain_lock_hash": metadata["toolchain_lock_hash"],
            "risc0_verified": True,
        },
    )
    _write_json(snapshots_dir / "1.json", snapshot_from_state(state).data)
    _write_json(config_path, config_document)
    _write_json(profile_path, profile)
    return _Case(
        headers_dir=headers_dir,
        bodies_dir=bodies_dir,
        checkpoints_dir=checkpoints_dir,
        proof_metadata_dir=proof_metadata_dir,
        proof_artifacts_dir=proof_artifacts_dir,
        proof_reports_dir=proof_reports_dir,
        snapshots_dir=snapshots_dir,
        config_path=config_path,
        profile_path=profile_path,
        verifier=verifier,
        registry=registry,
        counter_path=counter_path,
    )


def test_proof_required_replay_rejects_metadata_without_authenticated_verifier(
    tmp_path: Path,
) -> None:
    case = _make_case(tmp_path)

    report = case.verify(
        mode=REPLAY_BOUND_MODE,
        authenticated=False,
        include_report=False,
    )

    assert report["ok"] is False
    assert report["proof_authority_status"] == "required_pending"
    pending = report["proof_authority_pending_obligation"]
    assert pending["obligation_id"] == "zeno_ledger.proof_authority.consumer_binding.v1"
    assert "profile_requires_governed_proof_authority_binding" in report["errors"]
    assert not case.counter_path.exists()


def test_proof_required_replay_rejects_fabricated_positive_report(
    tmp_path: Path,
) -> None:
    case = _make_case(tmp_path)

    report = case.verify(mode=REPLAY_BOUND_MODE, authenticated=False)

    assert report["ok"] is False
    assert report["proof_verification_checked_heights"] == []
    assert report["governed_proof_authority_checked_heights"] == []
    assert "profile_requires_governed_proof_authority_binding" in report["errors"]


@pytest.mark.parametrize(
    ("include_report", "require_report"),
    ((True, False), (False, True), (True, True)),
)
def test_replay_bound_authority_rejects_caller_authored_report_lane(
    tmp_path: Path,
    include_report: bool,
    require_report: bool,
) -> None:
    case = _make_case(
        tmp_path,
        executable_format=VerifierExecutableFormatV1.STATIC_ELF_X86_64,
    )

    report = case.verify(
        mode=REPLAY_BOUND_MODE,
        authenticated=True,
        include_report=include_report,
        require_report=require_report,
    )

    assert report["ok"] is False
    assert report["proof_verification_checked_heights"] == []
    assert report["governed_proof_authority_checked_heights"] == []
    assert report["proof_authority_satisfied"] is False
    assert report["settlement_authority"] is False
    assert report["production_authority"] is False
    assert "replay_bound_rejects_caller_authored_proof_verification_reports" in report[
        "errors"
    ]
    assert not case.counter_path.exists()


@pytest.mark.parametrize(
    ("mutation", "expected_error"),
    [
        ("chain", "checkpoint chain_id not admitted by profile"),
        ("height", "proof_metadata/header height mismatch"),
        ("header", "proof_metadata/header proof_journal_hash mismatch"),
        ("config", "checkpoint config_digest not admitted by profile"),
    ],
)
def test_authenticated_proof_rejects_wrong_profile_or_header_binding(
    tmp_path: Path,
    mutation: str,
    expected_error: str,
) -> None:
    case = _make_case(tmp_path)
    if mutation == "chain":
        profile = json.loads(case.profile_path.read_text(encoding="utf-8"))
        _write_json(
            case.profile_path,
            clone_profile_with_new_id_v0(profile, chain_id="wrong-chain"),
        )
    elif mutation == "height":
        metadata_path = case.proof_metadata_dir / "1.json"
        metadata = json.loads(metadata_path.read_text(encoding="utf-8"))
        metadata["height"] = 2
        _write_json(metadata_path, metadata)
    elif mutation == "header":
        header_path = case.headers_dir / "1.json"
        header = json.loads(header_path.read_text(encoding="utf-8"))
        header["proof_journal_hash"] = _root("wrong-proof-journal")
        _write_json(header_path, header)
    else:
        profile = json.loads(case.profile_path.read_text(encoding="utf-8"))
        _write_json(
            case.profile_path,
            clone_profile_with_new_id_v0(
                profile,
                accepted_config_digests=[_root("wrong-config")],
            ),
        )

    report = case.verify(
        mode=REPLAY_BOUND_MODE,
        authenticated=True,
        include_report=False,
    )

    assert report["ok"] is False
    assert any(expected_error in error for error in report["errors"]), report["errors"]
    assert report["governed_proof_authority_checked_heights"] == []
    assert not case.counter_path.exists()


def test_proof_required_replay_rejects_duck_typed_verifier(
    tmp_path: Path,
) -> None:
    case = _make_case(tmp_path)

    report = verify_zeno_ledger_v0(
        headers_dir=case.headers_dir,
        bodies_dir=case.bodies_dir,
        checkpoints_dir=case.checkpoints_dir,
        profile_path=case.profile_path,
        from_height=1,
        to_height=1,
        proof_metadata_dir=case.proof_metadata_dir,
        proof_artifacts_dir=case.proof_artifacts_dir,
        proof_authority_verifier=object(),
        verifier_registry=case.registry,
        mode=REPLAY_BOUND_MODE,
        pre_snapshots_dir=case.snapshots_dir,
        engine_config_path=case.config_path,
        require_rejection_receipt_replay=True,
    )

    assert report["ok"] is False
    assert "proof_authority_verifier_type_invalid" in report["errors"]
    assert not case.counter_path.exists()


def test_caller_supplied_echo_verifier_cannot_satisfy_proof_authority(
    tmp_path: Path,
) -> None:
    case = _make_case(tmp_path)

    report = case.verify(
        mode=REPLAY_BOUND_MODE,
        authenticated=True,
        include_report=False,
    )

    assert report["ok"] is False
    assert report["status"] == "rejected"
    assert report["proof_authority_required"] is True
    assert report["proof_authority_satisfied"] is False
    assert report["proof_verification_checked_heights"] == []
    assert report["governed_proof_authority_checked_heights"] == []
    assert report["settlement_authority"] is False
    assert report["production_authority"] is False
    assert any("proof_authority_verifier_must_be_static_elf" in error for error in report["errors"])
    assert not case.counter_path.exists()


def test_caller_supplied_static_manifest_still_lacks_governed_binding(
    tmp_path: Path,
) -> None:
    case = _make_case(
        tmp_path,
        executable_format=VerifierExecutableFormatV1.STATIC_ELF_X86_64,
    )

    report = case.verify(
        mode=REPLAY_BOUND_MODE,
        authenticated=True,
        include_report=False,
    )

    assert report["ok"] is False
    assert report["proof_authority_satisfied"] is False
    assert report["proof_authority_status"] == "required_pending"
    assert report["proof_authority_pending_obligation"] is not None
    assert report["governed_proof_authority_checked_heights"] == []
    assert any(
        "governed_proof_authority_binding_unavailable_v0" in error for error in report["errors"]
    )
    assert not case.counter_path.exists()


def test_cli_without_strict_authority_inputs_cannot_satisfy_proof_authority(
    tmp_path: Path,
    capsys: pytest.CaptureFixture[str],
) -> None:
    case = _make_case(tmp_path)

    exit_code = verify_main(
        [
            "--headers-dir",
            str(case.headers_dir),
            "--bodies-dir",
            str(case.bodies_dir),
            "--checkpoints-dir",
            str(case.checkpoints_dir),
            "--proof-metadata-dir",
            str(case.proof_metadata_dir),
            "--profile",
            str(case.profile_path),
            "--from-height",
            "1",
            "--to-height",
            "1",
            "--require-state-replay",
            "--pre-snapshots-dir",
            str(case.snapshots_dir),
            "--engine-config",
            str(case.config_path),
            "--require-rejection-receipt-replay",
        ]
    )
    report = json.loads(capsys.readouterr().out)

    assert exit_code == 1
    assert report["proof_authority_satisfied"] is False
    assert report["governed_proof_authority_checked_heights"] == []
    assert "profile_requires_governed_proof_authority_binding" in report["errors"]
    assert not case.counter_path.exists()


def test_structural_mode_remains_explicitly_non_authoritative(
    tmp_path: Path,
) -> None:
    case = _make_case(tmp_path)

    report = case.verify(mode=STRUCTURAL_DIAGNOSTIC_MODE, authenticated=False)

    assert report["ok"] is True
    assert report["status"] == "structural_diagnostic_accepted"
    assert report["authority_scope"] == "none"
    assert report["proof_verification_checked_heights"] == [1]
    assert report["proof_authority_required"] is True
    assert report["proof_authority_satisfied"] is False
    assert report["governed_proof_authority_checked_heights"] == []
    assert report["settlement_authority"] is False
    assert report["production_authority"] is False
