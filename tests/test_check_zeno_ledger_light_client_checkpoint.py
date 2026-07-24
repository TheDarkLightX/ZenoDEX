from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from src.integration.zeno_ledger_profile import sample_zeno_sovereign_testnet_profile_v0
from src.integration.zeno_ledger_signature import (
    bls_public_key_hex_from_private_key_v0,
    build_bls_signed_artifact_envelope_v0,
)
from src.integration.zeno_ledger_signer_registry import build_signer_registry_v0
from src.integration.zeno_ledger_v0 import (
    BATCH_CUTOFF_SCHEMA_V0,
    BODY_SCHEMA_V0,
    INGRESS_RECEIPT_SCHEMA_V0,
    build_checkpoint_v0,
    build_header_v0,
    canonical_body_root_v0,
    canonical_header_hash_v0,
    compute_app_hash_v0,
    compute_evidence_root_v0,
    compute_ingress_root_v0,
    compute_tx_root_v0,
    hash_v0,
)
from tools.check_zeno_ledger_light_client_checkpoint import (
    CHECKPOINT_PAYLOAD_KIND,
    light_client_checkpoint_hash_v0,
    light_client_signature_set_root_v0,
    main,
    validate_light_client_checkpoint_v0,
)
from tools.zeno_ledger_verify import ZERO_ROOT

ROOT = Path(__file__).resolve().parents[1]
TEST_BLS_PRIVATE_KEY_A = "0x" + "01" * 32
TEST_BLS_PRIVATE_KEY_B = "0x" + "02" * 32


def _root(label: str) -> str:
    return hash_v0("light_client_test_root", {"label": label})


def _body(height: int) -> dict[str, object]:
    tx_hash = hash_v0("light_client_test_tx", {"height": height})
    return {
        "schema": BODY_SCHEMA_V0,
        "chain_id": "zeno-ledger-light-client-testnet-0",
        "height": height,
        "ingress": {
            "batch_cutoff": {
                "schema": BATCH_CUTOFF_SCHEMA_V0,
                "chain_id": "zeno-ledger-light-client-testnet-0",
                "height": height,
                "cutoff_time_ms": 1_778_730_000_000 + height,
                "cutoff_sequence": 1000 + height,
                "sequencer_id": "sequencer-light-client-0",
                "policy_id": "public_cutoff_v0",
                "policy_digest": _root("policy"),
            },
            "ingress_receipts": [
                {
                    "schema": INGRESS_RECEIPT_SCHEMA_V0,
                    "chain_id": "zeno-ledger-light-client-testnet-0",
                    "tx_hash": tx_hash,
                    "received_time_ms": 1_778_729_999_000 + height,
                    "received_sequence": 900 + height,
                    "sequencer_id": "sequencer-light-client-0",
                    "status": "included",
                    "height": height,
                    "index": 0,
                    "reject_code": None,
                    "receipt_hash": _root(f"receipt-{height}"),
                }
            ],
            "forced_inclusion_requests": [],
            "forced_inclusion_decisions": [],
        },
        "transactions": [{"sender": "alice", "nonce": height}],
        "settlement_envelopes": [],
        "evidence": {
            "upba_certificates": [],
            "price_grid_tables": [],
            "uniform_batch_hypergraph_roots": [],
            "oracle_packets": [],
            "proof_receipts": [],
            "rejection_receipts": [],
        },
    }


def _header(body: dict[str, object], *, prev_header_hash: str, signature_set_root: str) -> dict[str, object]:
    evidence_root = compute_evidence_root_v0(body["evidence"])  # type: ignore[arg-type]
    app_hash = compute_app_hash_v0(
        {
            "chain_id": body["chain_id"],
            "height": body["height"],
            "post_state_root": _root(f"post-state-{body['height']}"),
            "evidence_root": evidence_root,
            "config_digest": _root("config"),
            "module_versions_digest": _root("modules"),
        }
    )
    return build_header_v0(
        chain_id=str(body["chain_id"]),
        height=int(body["height"]),
        time_ms=1_778_730_000_000 + int(body["height"]),
        prev_header_hash=prev_header_hash,
        sequencer_set_hash=_root("sequencer-set"),
        ingress_root=compute_ingress_root_v0(body["ingress"]),  # type: ignore[arg-type]
        tx_root=compute_tx_root_v0(body["transactions"]),  # type: ignore[arg-type]
        pre_state_root=_root(f"pre-state-{body['height']}"),
        post_state_root=_root(f"post-state-{body['height']}"),
        app_hash=app_hash,
        evidence_root=evidence_root,
        body_root=canonical_body_root_v0(body),
        data_availability_root=_root("da"),
        proof_journal_hash=ZERO_ROOT,
        config_digest=_root("config"),
        module_versions_digest=_root("modules"),
        signature_set_root=signature_set_root,
    )


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True), encoding="utf-8")


def _registry() -> dict[str, object]:
    public_key_a = bls_public_key_hex_from_private_key_v0(TEST_BLS_PRIVATE_KEY_A)
    public_key_b = bls_public_key_hex_from_private_key_v0(TEST_BLS_PRIVATE_KEY_B)
    return build_signer_registry_v0(
        registry_id="release-light-client-watchers-v0",
        payload_kind=CHECKPOINT_PAYLOAD_KIND,
        threshold=2,
        signers=[
            {
                "signer_id": "release-watcher-a",
                "key_id": "release-bls-key-a",
                "public_key": public_key_a,
                "weight": 1,
            },
            {
                "signer_id": "release-watcher-b",
                "key_id": "release-bls-key-b",
                "public_key": public_key_b,
                "weight": 1,
            },
        ],
    )


def _write_chain(tmp_path: Path, *, signature_set_root: str) -> tuple[Path, Path, Path, list[dict[str, object]]]:
    headers_dir = tmp_path / "headers"
    bodies_dir = tmp_path / "bodies"
    checkpoints_dir = tmp_path / "checkpoints"
    headers: list[dict[str, object]] = []
    prev_hash = ZERO_ROOT
    for height in (1, 2):
        body = _body(height)
        header = _header(body, prev_header_hash=prev_hash, signature_set_root=signature_set_root)
        checkpoint = build_checkpoint_v0(header)
        _write_json(headers_dir / f"{height}.json", header)
        _write_json(bodies_dir / f"{height}.json", body)
        _write_json(checkpoints_dir / f"{height}.json", checkpoint)
        headers.append(header)
        prev_hash = canonical_header_hash_v0(header)
    return headers_dir, bodies_dir, checkpoints_dir, headers


def _envelopes_for_checkpoint(checkpoint: dict[str, object]) -> list[dict[str, object]]:
    checkpoint_hash = light_client_checkpoint_hash_v0(checkpoint)
    return [
        build_bls_signed_artifact_envelope_v0(
            payload_kind=CHECKPOINT_PAYLOAD_KIND,
            payload_hash=checkpoint_hash,
            signer_id="release-watcher-a",
            key_id="release-bls-key-a",
            private_key_hex=TEST_BLS_PRIVATE_KEY_A,
        ),
        build_bls_signed_artifact_envelope_v0(
            payload_kind=CHECKPOINT_PAYLOAD_KIND,
            payload_hash=checkpoint_hash,
            signer_id="release-watcher-b",
            key_id="release-bls-key-b",
            private_key_hex=TEST_BLS_PRIVATE_KEY_B,
        ),
    ]


def _fixture(tmp_path: Path) -> tuple[Path, Path, Path, dict[str, object], list[dict[str, object]]]:
    registry = _registry()
    signature_set_root = light_client_signature_set_root_v0(registry)
    headers_dir, bodies_dir, checkpoints_dir, _headers = _write_chain(
        tmp_path,
        signature_set_root=signature_set_root,
    )
    checkpoint = json.loads((checkpoints_dir / "2.json").read_text(encoding="utf-8"))
    envelopes = _envelopes_for_checkpoint(checkpoint)
    return headers_dir, bodies_dir, checkpoints_dir, registry, envelopes


def test_light_client_checkpoint_accepts_header_checkpoint_and_quorum(tmp_path: Path) -> None:
    headers_dir, bodies_dir, checkpoints_dir, registry, envelopes = _fixture(tmp_path)

    report = validate_light_client_checkpoint_v0(
        headers_dir=headers_dir,
        bodies_dir=bodies_dir,
        checkpoints_dir=checkpoints_dir,
        registry=registry,
        envelopes=envelopes,
        from_height=1,
        to_height=2,
    )

    assert report["ok"] is True
    assert report["status"] == "structural_diagnostic_accepted"
    assert report["structural_diagnostic_verified"] is True
    assert report["range_replay_verified"] is False
    assert report["range_verify_report"]["checked_heights"] == [1, 2]
    assert report["quorum_report"]["accepted_weight"] == 2
    assert report["checkpoint_hash"]
    assert report["proof_authority_required"] is False
    assert report["proof_authority_satisfied"] is False
    assert report["proof_authority_capable"] is False
    assert report["settlement_authority"] is False
    assert report["production_authority"] is False


def test_light_client_rejects_proof_required_profile_structural_promotion(
    tmp_path: Path,
) -> None:
    headers_dir, bodies_dir, checkpoints_dir, registry, envelopes = _fixture(tmp_path)
    profile_path = tmp_path / "proof-required-profile.json"
    _write_json(
        profile_path,
        sample_zeno_sovereign_testnet_profile_v0(
            chain_id="zeno-ledger-light-client-testnet-0",
            config_digest=_root("config"),
            sequencer_set_hash=_root("sequencer-set"),
            token_symbol="tZENO",
            token_asset_id=_root("token"),
            proof_required=True,
        ),
    )

    report = validate_light_client_checkpoint_v0(
        headers_dir=headers_dir,
        bodies_dir=bodies_dir,
        checkpoints_dir=checkpoints_dir,
        registry=registry,
        envelopes=envelopes,
        from_height=1,
        to_height=2,
        profile_path=profile_path,
    )

    assert report["ok"] is False
    assert report["range_replay_verified"] is False
    assert report["proof_authority_required"] is True
    assert report["proof_authority_satisfied"] is False
    assert report["proof_authority_capable"] is False
    assert any("proof-required profile cannot be promoted" in error for error in report["errors"])


def test_light_client_checkpoint_rejects_threshold_shortfall(tmp_path: Path) -> None:
    headers_dir, bodies_dir, checkpoints_dir, registry, envelopes = _fixture(tmp_path)

    report = validate_light_client_checkpoint_v0(
        headers_dir=headers_dir,
        bodies_dir=bodies_dir,
        checkpoints_dir=checkpoints_dir,
        registry=registry,
        envelopes=envelopes[:1],
        from_height=1,
        to_height=2,
    )

    assert report["ok"] is False
    assert any("threshold not met" in error for error in report["errors"])


def test_light_client_checkpoint_rejects_signature_set_root_mismatch(tmp_path: Path) -> None:
    registry = _registry()
    headers_dir, bodies_dir, checkpoints_dir, _headers = _write_chain(
        tmp_path,
        signature_set_root=_root("wrong-signature-set-root"),
    )
    checkpoint = json.loads((checkpoints_dir / "2.json").read_text(encoding="utf-8"))
    envelopes = _envelopes_for_checkpoint(checkpoint)

    report = validate_light_client_checkpoint_v0(
        headers_dir=headers_dir,
        bodies_dir=bodies_dir,
        checkpoints_dir=checkpoints_dir,
        registry=registry,
        envelopes=envelopes,
        from_height=1,
        to_height=2,
    )

    assert report["ok"] is False
    assert any("signature_set_root does not match signer registry root" in error for error in report["errors"])


def test_light_client_checkpoint_rejects_inline_checkpoint_signature_set(tmp_path: Path) -> None:
    headers_dir, bodies_dir, checkpoints_dir, registry, envelopes = _fixture(tmp_path)
    checkpoint_path = checkpoints_dir / "2.json"
    checkpoint = json.loads(checkpoint_path.read_text(encoding="utf-8"))
    checkpoint["signature_set"] = [{"unexpected": "inline-signature"}]
    _write_json(checkpoint_path, checkpoint)

    report = validate_light_client_checkpoint_v0(
        headers_dir=headers_dir,
        bodies_dir=bodies_dir,
        checkpoints_dir=checkpoints_dir,
        registry=registry,
        envelopes=envelopes,
        from_height=1,
        to_height=2,
    )

    assert report["ok"] is False
    assert any("signature_set must be empty" in error for error in report["errors"])


def test_light_client_checkpoint_cli_outputs_report(tmp_path: Path, capsys) -> None:
    headers_dir, bodies_dir, checkpoints_dir, registry, envelopes = _fixture(tmp_path)
    registry_path = tmp_path / "registry.json"
    envelope_a_path = tmp_path / "checkpoint.a.sig.json"
    envelope_b_path = tmp_path / "checkpoint.b.sig.json"
    _write_json(registry_path, registry)
    _write_json(envelope_a_path, envelopes[0])
    _write_json(envelope_b_path, envelopes[1])

    code = main(
        [
            "--headers-dir",
            str(headers_dir),
            "--bodies-dir",
            str(bodies_dir),
            "--checkpoints-dir",
            str(checkpoints_dir),
            "--registry",
            str(registry_path),
            "--envelope",
            str(envelope_a_path),
            "--envelope",
            str(envelope_b_path),
            "--from-height",
            "1",
            "--to-height",
            "2",
        ]
    )
    out = capsys.readouterr().out
    report = json.loads(out)

    assert code == 0
    assert report["ok"] is True
    assert report["schema"] == "zenodex.zeno_ledger.light_client_checkpoint_report.v0"


def test_zenoctl_light_client_verify_checkpoint_accepts_real_fixture(tmp_path: Path) -> None:
    headers_dir, bodies_dir, checkpoints_dir, registry, envelopes = _fixture(tmp_path)
    registry_path = tmp_path / "registry.json"
    envelope_a_path = tmp_path / "checkpoint.a.sig.json"
    envelope_b_path = tmp_path / "checkpoint.b.sig.json"
    _write_json(registry_path, registry)
    _write_json(envelope_a_path, envelopes[0])
    _write_json(envelope_b_path, envelopes[1])

    proc = subprocess.run(
        [
            sys.executable,
            "tools/zenoctl.py",
            "light-client",
            "verify-checkpoint",
            "--headers-dir",
            str(headers_dir),
            "--bodies-dir",
            str(bodies_dir),
            "--checkpoints-dir",
            str(checkpoints_dir),
            "--registry",
            str(registry_path),
            "--envelope",
            str(envelope_a_path),
            "--envelope",
            str(envelope_b_path),
            "--from-height",
            "1",
            "--to-height",
            "2",
        ],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    report = json.loads(proc.stdout)

    assert proc.returncode == 0, proc.stderr
    assert report["ok"] is True
    assert report["quorum_report"]["accepted_weight"] == 2
    assert report["range_verify_report"]["checked_heights"] == [1, 2]
