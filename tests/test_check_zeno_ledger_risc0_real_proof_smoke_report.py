from __future__ import annotations

import copy
import json
from pathlib import Path

from src.integration.zeno_ledger_v0 import (
    BATCH_CUTOFF_SCHEMA_V0,
    BODY_SCHEMA_V0,
    EVIDENCE_KEYS_V0,
    ZERO_ROOT_V0,
    build_header_v0,
    canonical_body_root_v0,
    compute_app_hash_v0,
    compute_evidence_root_v0,
    compute_ingress_root_v0,
    compute_tx_root_v0,
    hash_v0,
    proof_metadata_hash_v0,
)
from tools.check_zeno_ledger_risc0_real_proof_smoke_report import (
    LEDGER_BINDING_SCHEMA,
    PROOF_TYPE,
    main,
    validate_risc0_real_proof_smoke_report_v0,
)
from tools.zeno_ledger_risc0_proof_metadata import (
    build_header_derived_risc0_proof_metadata_diagnostic_v0,
)


def _hex(label: str) -> str:
    value = label.encode("utf-8").hex()
    return (value + "0" * 64)[:64]


def _case(name: str) -> dict[str, object]:
    return {
        "case": name,
        "ok": True,
        "proof_type": PROOF_TYPE,
        "state_hash": _hex("state"),
        "post_app_hash": _hex(f"post-{name}"),
        "pre_app_hash": "" if name == "empty" else _hex(f"pre-{name}"),
        "txs_commitment": _hex(f"txs-{name}"),
        "risc0_image_id": _hex("image"),
        "proof_base64_len": 128,
        "proof_path": f"/tmp/{name}_tau_state_proof.json",
        "ledger_binding": {
            "schema": LEDGER_BINDING_SCHEMA,
            "ok": True,
            "status": "non_authoritative_header_derived_metadata",
            "authority_scope": "none",
            "header_derived_fields": [
                "chain_id",
                "height",
                "pre_state_root",
                "post_state_root",
                "tx_root",
                "evidence_root",
                "body_root",
            ],
            "proof_authority_satisfied": False,
            "settlement_authority": False,
            "production_authority": False,
            "header_bound": True,
            "body_checked": True,
            "post_state_root_checked": True,
            "pre_state_root_checked": True,
            "body_tx_count": 0 if name == "empty" else 1,
            "body_path": f"/tmp/{name}_zeno_ledger_body.json",
            "header_path": f"/tmp/{name}_zeno_ledger_header.json",
            "metadata_path": f"/tmp/{name}_risc0_proof_metadata.json",
            "proof_journal_hash": _hex(f"journal-{name}"),
            "pre_state_root": _hex(f"pre-root-{name}"),
            "post_state_root": _hex(f"post-root-{name}"),
            "tx_root": _hex(f"tx-root-{name}"),
            "body_root": _hex(f"body-root-{name}"),
            "evidence_root": _hex(f"evidence-root-{name}"),
            "ledger_app_hash": _hex(f"ledger-app-{name}"),
        },
    }


def _report() -> dict[str, object]:
    cases = [
        _case(name)
        for name in (
            "empty",
            "faucet_mint",
            "create_pool",
            "swap_exact_in",
            "add_liquidity",
            "remove_liquidity",
            "spot_block_liquidity_cycle",
        )
    ]
    return {
        "schema": "zenodex.risc0_real_proof_smoke.v0",
        "ok": True,
        "case_count": len(cases),
        "cases": cases,
    }


def _root(label: str) -> str:
    return hash_v0("risc0_smoke_report_test", {"label": label})


def _write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True), encoding="utf-8")


def _artifact_report(tmp_path: Path) -> dict[str, object]:
    post_state_root = _root("post-state")
    proof = {
        "schema": "tau_state_proof",
        "schema_version": 1,
        "state_hash": _hex("state"),
        "proof_type": PROOF_TYPE,
        "proof": "cmlzYzAtcmVjZWlwdA==",
        "meta": {
            "risc0_image_id": _hex("image"),
            "txs_commitment": _hex("txs-empty"),
            "ingress_commitment": _hex("ingress-empty"),
            "pre_nonce_root": _hex("pre-nonce-empty"),
            "post_nonce_root": _hex("post-nonce-empty"),
            "accepted_receipts_root": _hex("accepted-receipts-empty"),
            "pre_app_hash": "",
            "post_app_hash": post_state_root[2:],
        },
    }
    body = {
        "schema": BODY_SCHEMA_V0,
        "chain_id": "zenodex-risc0-smoke-report-test",
        "height": 1,
        "ingress": {
            "batch_cutoff": {
                "schema": BATCH_CUTOFF_SCHEMA_V0,
                "chain_id": "zenodex-risc0-smoke-report-test",
                "height": 1,
                "cutoff_time_ms": 1,
                "cutoff_sequence": 1,
                "sequencer_id": "sequencer-0",
                "policy_id": "test",
                "policy_digest": _root("policy"),
            },
            "ingress_receipts": [],
            "forced_inclusion_requests": [],
            "forced_inclusion_decisions": [],
        },
        "transactions": [],
        "settlement_envelopes": [],
        "evidence": {key: [] for key in EVIDENCE_KEYS_V0},
    }
    evidence_root = compute_evidence_root_v0(body["evidence"])  # type: ignore[arg-type]
    config_digest = _root("config")
    module_versions_digest = _root("modules")
    app_hash = compute_app_hash_v0(
        {
            "chain_id": body["chain_id"],
            "height": body["height"],
            "post_state_root": post_state_root,
            "evidence_root": evidence_root,
            "config_digest": config_digest,
            "module_versions_digest": module_versions_digest,
        }
    )
    header_unbound = build_header_v0(
        chain_id=str(body["chain_id"]),
        height=int(body["height"]),
        time_ms=1,
        prev_header_hash=ZERO_ROOT_V0,
        sequencer_set_hash=_root("sequencer-set"),
        ingress_root=compute_ingress_root_v0(body["ingress"]),  # type: ignore[arg-type]
        tx_root=compute_tx_root_v0(body["transactions"]),  # type: ignore[arg-type]
        pre_state_root=_root("pre-state-absent"),
        post_state_root=post_state_root,
        app_hash=app_hash,
        evidence_root=evidence_root,
        body_root=canonical_body_root_v0(body),  # type: ignore[arg-type]
        data_availability_root=_root("da"),
        proof_journal_hash=ZERO_ROOT_V0,
        config_digest=config_digest,
        module_versions_digest=module_versions_digest,
        signature_set_root=ZERO_ROOT_V0,
    )
    metadata = build_header_derived_risc0_proof_metadata_diagnostic_v0(
        proof_envelope=proof,
        header=header_unbound,
        conflict_schedule_hash=_root("schedule"),
        feature_suite_hash=_root("features"),
        dependency_lock_hash=_root("dependency"),
        toolchain_lock_hash=_root("toolchain"),
    )
    proof_journal_hash = proof_metadata_hash_v0(metadata)
    header = {**header_unbound, "proof_journal_hash": proof_journal_hash}

    proof_path = tmp_path / "empty_tau_state_proof.json"
    body_path = tmp_path / "empty_zeno_ledger_body.json"
    header_path = tmp_path / "empty_zeno_ledger_header.json"
    metadata_path = tmp_path / "empty_risc0_proof_metadata.json"
    _write_json(proof_path, proof)
    _write_json(body_path, body)
    _write_json(header_path, header)
    _write_json(metadata_path, metadata)

    return {
        "schema": "zenodex.risc0_real_proof_smoke.v0",
        "ok": True,
        "case_count": 1,
        "cases": [
            {
                "case": "empty",
                "ok": True,
                "proof_type": PROOF_TYPE,
                "state_hash": proof["state_hash"],
                "post_app_hash": proof["meta"]["post_app_hash"],
                "pre_app_hash": "",
                "txs_commitment": proof["meta"]["txs_commitment"],
                "risc0_image_id": proof["meta"]["risc0_image_id"],
                "proof_base64_len": len(str(proof["proof"])),
                "proof_path": str(proof_path),
                "ledger_binding": {
                    "schema": LEDGER_BINDING_SCHEMA,
                    "ok": True,
                    "status": "non_authoritative_header_derived_metadata",
                    "authority_scope": "none",
                    "header_derived_fields": [
                        "chain_id",
                        "height",
                        "pre_state_root",
                        "post_state_root",
                        "tx_root",
                        "evidence_root",
                        "body_root",
                    ],
                    "proof_authority_satisfied": False,
                    "settlement_authority": False,
                    "production_authority": False,
                    "header_bound": True,
                    "body_checked": True,
                    "post_state_root_checked": True,
                    "pre_state_root_checked": True,
                    "body_tx_count": 0,
                    "body_path": str(body_path),
                    "header_path": str(header_path),
                    "metadata_path": str(metadata_path),
                    "proof_journal_hash": proof_journal_hash,
                    "pre_state_root": header["pre_state_root"],
                    "post_state_root": header["post_state_root"],
                    "tx_root": header["tx_root"],
                    "body_root": header["body_root"],
                    "evidence_root": header["evidence_root"],
                    "ledger_app_hash": header["app_hash"],
                },
            }
        ],
    }


def test_risc0_real_proof_smoke_report_accepts_all_supported_cases() -> None:
    check = validate_risc0_real_proof_smoke_report_v0(_report())

    assert check["ok"] is True
    assert check["case_count"] == 7
    assert check["required_cases"] == [
        "add_liquidity",
        "create_pool",
        "empty",
        "faucet_mint",
        "remove_liquidity",
        "spot_block_liquidity_cycle",
        "swap_exact_in",
    ]


def test_risc0_real_proof_smoke_report_rejects_missing_case() -> None:
    report = _report()
    report["cases"] = report["cases"][:-1]  # type: ignore[index]
    report["case_count"] = 6

    check = validate_risc0_real_proof_smoke_report_v0(report)

    assert check["ok"] is False
    assert "missing required cases: spot_block_liquidity_cycle" in check["errors"]


def test_risc0_real_proof_smoke_report_rejects_empty_receipt() -> None:
    report = _report()
    case = copy.deepcopy(report["cases"][1])  # type: ignore[index]
    case["proof_base64_len"] = 0
    report["cases"][1] = case  # type: ignore[index]

    check = validate_risc0_real_proof_smoke_report_v0(report)

    assert check["ok"] is False
    assert any("proof_base64_len must be a positive int" in err for err in check["errors"])


def test_risc0_real_proof_smoke_report_rejects_bad_commitment_hex() -> None:
    report = _report()
    case = copy.deepcopy(report["cases"][2])  # type: ignore[index]
    case["txs_commitment"] = "not-hex"
    report["cases"][2] = case  # type: ignore[index]

    check = validate_risc0_real_proof_smoke_report_v0(report)

    assert check["ok"] is False
    assert any("txs_commitment must be 64-char hex" in err for err in check["errors"])


def test_risc0_real_proof_smoke_report_rejects_missing_ledger_binding() -> None:
    report = _report()
    case = copy.deepcopy(report["cases"][2])  # type: ignore[index]
    case.pop("ledger_binding")
    report["cases"][2] = case  # type: ignore[index]

    check = validate_risc0_real_proof_smoke_report_v0(report)

    assert check["ok"] is False
    assert any("ledger_binding must be an object" in err for err in check["errors"])


def test_risc0_real_proof_smoke_report_rejects_unbound_header() -> None:
    report = _report()
    case = copy.deepcopy(report["cases"][3])  # type: ignore[index]
    binding = copy.deepcopy(case["ledger_binding"])  # type: ignore[index]
    binding["header_bound"] = False
    case["ledger_binding"] = binding
    report["cases"][3] = case  # type: ignore[index]

    check = validate_risc0_real_proof_smoke_report_v0(report)

    assert check["ok"] is False
    assert any("ledger_binding.header_bound must be true" in err for err in check["errors"])


def test_risc0_real_proof_smoke_report_rejects_authority_promotion() -> None:
    report = _report()
    case = copy.deepcopy(report["cases"][3])  # type: ignore[index]
    binding = copy.deepcopy(case["ledger_binding"])  # type: ignore[index]
    binding["production_authority"] = True
    case["ledger_binding"] = binding
    report["cases"][3] = case  # type: ignore[index]

    check = validate_risc0_real_proof_smoke_report_v0(report)

    assert check["ok"] is False
    assert any(
        "ledger_binding.production_authority must be false" in err for err in check["errors"]
    )


def test_risc0_real_proof_smoke_report_validates_artifact_binding(tmp_path: Path) -> None:
    report = _artifact_report(tmp_path)

    check = validate_risc0_real_proof_smoke_report_v0(
        report,
        required_cases={"empty"},
        require_proof_files=True,
    )

    assert check["ok"] is True
    assert check["cases"][0]["ledger_binding_ok"] is True


def test_risc0_real_proof_smoke_report_rejects_tampered_artifact_binding(tmp_path: Path) -> None:
    report = _artifact_report(tmp_path)
    binding = report["cases"][0]["ledger_binding"]  # type: ignore[index]
    metadata_path = Path(binding["metadata_path"])  # type: ignore[index]
    metadata = json.loads(metadata_path.read_text(encoding="utf-8"))
    metadata["post_state_root"] = _root("tampered-post-state")
    _write_json(metadata_path, metadata)

    check = validate_risc0_real_proof_smoke_report_v0(
        report,
        required_cases={"empty"},
        require_proof_files=True,
    )

    assert check["ok"] is False
    assert any("artifact_binding" in err for err in check["errors"])


def test_risc0_real_proof_smoke_report_cli_outputs_check(tmp_path, capsys) -> None:
    report_path = tmp_path / "real_proof_smoke_report.json"
    report_path.write_text(json.dumps(_report(), indent=2, sort_keys=True), encoding="utf-8")

    code = main([str(report_path)])
    out = capsys.readouterr().out
    check = json.loads(out)

    assert code == 0
    assert check["ok"] is True
    assert check["schema"] == "zenodex.risc0_real_proof_smoke_report_check.v0"


def test_risc0_real_proof_smoke_report_cli_accepts_required_case_subset(tmp_path, capsys) -> None:
    report = _artifact_report(tmp_path)
    report_path = tmp_path / "single_case_report.json"
    report_path.write_text(json.dumps(report, indent=2, sort_keys=True), encoding="utf-8")

    code = main([str(report_path), "--required-case", "empty", "--require-proof-files"])
    out = capsys.readouterr().out
    check = json.loads(out)

    assert code == 0
    assert check["ok"] is True
    assert check["required_cases"] == ["empty"]
