from __future__ import annotations

import copy
import json
from pathlib import Path

import pytest

from src.core.risc0_tx_execution_order import (
    build_tx_execution_order_certificate_v1,
    route_price_interval_authority_policy_root_hex_v1,
    route_price_interval_authority_root_hex_v1,
    route_price_intervals_root_hex_v1,
)
from src.integration.risc0_route_body_projection import (
    project_route_body_transactions_to_proof_v1,
    route_body_projection_contract_hash_v1,
    route_body_projection_contract_v1,
)
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
from tools.zeno_ledger_risc0_proof_metadata import build_risc0_proof_metadata_v0
from tools.zeno_ledger_risc0_real_proof_smoke import (
    _apply_route_order_policy_to_context,
    _ledger_binding_for_case,
    _ledger_body_for_case,
    _proof_transactions_for_case,
    _route_order_receipt_requirement_for_case,
    _smoke_cases,
    _tx_order_inputs_for_case,
)


def _hex(label: str) -> str:
    value = label.encode("utf-8").hex()
    return (value + "0" * 64)[:64]


def _projection_contract_fields() -> dict[str, object]:
    return {
        "projection_contract": route_body_projection_contract_v1(),
        "projection_contract_hash": route_body_projection_contract_hash_v1(),
    }


def _empty_route_price_meta() -> dict[str, object]:
    return {
        "route_price_interval_count": 0,
        "route_price_intervals_root": route_price_intervals_root_hex_v1([]),
        "route_price_interval_authority_root": (
            route_price_interval_authority_root_hex_v1(None)
        ),
        "route_price_interval_authority_policy_root": (
            route_price_interval_authority_policy_root_hex_v1(None)
        ),
        "route_price_interval_max_width_bps": None,
    }


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
        "execution_context_hash": _hex(f"execution-context-{name}"),
        "proof_base64_len": 128,
        "proof_path": f"/tmp/{name}_tau_state_proof.json",
        "ledger_binding": {
            "schema": LEDGER_BINDING_SCHEMA,
            "ok": True,
            "header_bound": True,
            "body_checked": True,
            "post_state_root_checked": True,
            "pre_state_root_checked": True,
            "body_tx_count": 0 if name == "empty" else 1,
            "proof_tx_count": 0 if name == "empty" else 1,
            "body_path": f"/tmp/{name}_zeno_ledger_body.json",
            "header_path": f"/tmp/{name}_zeno_ledger_header.json",
            "metadata_path": f"/tmp/{name}_risc0_proof_metadata.json",
            "proof_transactions_path": f"/tmp/{name}_risc0_proof_transactions.json",
            "proof_journal_hash": _hex(f"journal-{name}"),
            "body_transactions_hash": _hex(f"body-txs-{name}"),
            "proof_transactions_hash": _hex(f"proof-txs-{name}"),
            "proof_transactions_match_body": True,
            "body_to_proof_projection_checked": True,
            **_projection_contract_fields(),
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


def _route_order_report(*, body_order_checked: bool | None) -> dict[str, object]:
    case = _case("route_order")
    binding = case["ledger_binding"]  # type: ignore[index]
    if body_order_checked is not None:
        binding["body_tx_execution_order_commitment_checked"] = body_order_checked  # type: ignore[index]
    return {
        "schema": "zenodex.risc0_real_proof_smoke.v0",
        "ok": True,
        "case_count": 1,
        "cases": [case],
    }


def _root(label: str) -> str:
    return hash_v0("risc0_smoke_report_test", {"label": label})


def _write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True), encoding="utf-8")


def _write_fake_risc0_commitment_cli(tmp_path: Path, *, txs_commitment: str) -> Path:
    path = tmp_path / "fake_risc0_commitment_cli.py"
    path.write_text(
        "\n".join(
            [
                "#!/usr/bin/env python3",
                "import json",
                "import sys",
                "req = json.load(sys.stdin)",
                "print(json.dumps({",
                "    'schema': 'tau_state_proof_txs_commitment_result',",
                "    'schema_version': 1,",
                "    'ok': True,",
                "    'tx_count': len(req.get('transactions', [])),",
                f"    'txs_commitment': {txs_commitment!r},",
                "}, sort_keys=True))",
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    path.chmod(path.stat().st_mode | 0o111)
    return path


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
            "execution_context_hash": _hex("execution-context-empty"),
            "txs_commitment": _hex("txs-empty"),
            "tx_execution_order_commitment": _hex("tx-order-empty"),
            "ingress_commitment": _hex("ingress-empty"),
            "pre_nonce_root": _hex("pre-nonce-empty"),
            "post_nonce_root": _hex("post-nonce-empty"),
            "accepted_receipts_root": _hex("accepted-receipts-empty"),
            "pre_app_hash": "",
            "post_app_hash": post_state_root[2:],
            "protocol_fee_share_bps": 0,
            "protocol_fee_recipient_pubkey": None,
            **_empty_route_price_meta(),
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
    proof_transactions: list[object] = []
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
    metadata = build_risc0_proof_metadata_v0(
        proof_envelope=proof,
        header=header_unbound,
        conflict_schedule_hash=_root("schedule"),
        feature_suite_hash=_root("features"),
        dependency_lock_hash=_root("dependency"),
        toolchain_lock_hash=_root("toolchain"),
        expected_execution_context_hash=str(
            proof["meta"]["execution_context_hash"]
        ),
    )
    proof_journal_hash = proof_metadata_hash_v0(metadata)
    header = {**header_unbound, "proof_journal_hash": proof_journal_hash}

    proof_path = tmp_path / "empty_tau_state_proof.json"
    body_path = tmp_path / "empty_zeno_ledger_body.json"
    header_path = tmp_path / "empty_zeno_ledger_header.json"
    metadata_path = tmp_path / "empty_risc0_proof_metadata.json"
    proof_transactions_path = tmp_path / "empty_risc0_proof_transactions.json"
    _write_json(proof_path, proof)
    _write_json(body_path, body)
    _write_json(header_path, header)
    _write_json(metadata_path, metadata)
    _write_json(proof_transactions_path, proof_transactions)

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
                    "header_bound": True,
                    "body_checked": True,
                    "post_state_root_checked": True,
                    "pre_state_root_checked": True,
                    "body_tx_count": 0,
                    "proof_tx_count": 0,
                    "body_path": str(body_path),
                    "header_path": str(header_path),
                    "metadata_path": str(metadata_path),
                    "proof_transactions_path": str(proof_transactions_path),
                    "proof_journal_hash": proof_journal_hash,
                    "body_transactions_hash": hash_v0("risc0_smoke_body_transactions_v0", body["transactions"]),
                    "proof_transactions_hash": hash_v0(
                        "risc0_smoke_proof_transactions_v0",
                        proof_transactions,
                    ),
                    "proof_transactions_match_body": True,
                    "body_to_proof_projection_checked": True,
                    **_projection_contract_fields(),
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


def _route_order_case() -> dict[str, object]:
    case: dict[str, object] = {
        "pre_snapshot": None,
        "pre_hash": "",
        "transactions": [
            {
                "sender_pubkey": "writer",
                "nonce": 0,
                "operations": {
                    "2": [
                        {
                            "module": "TauSwap",
                            "version": "v1",
                            "kind": "SWAP_EXACT_IN",
                            "intent_id": "writer-swap",
                            "sender_pubkey": "writer",
                            "deadline": 100,
                            "pool_id": "pool-a",
                            "asset_in": "asset-a",
                            "asset_out": "asset-b",
                            "amount_in": 1,
                            "min_amount_out": 0,
                        }
                    ]
                },
            },
            {
                "sender_pubkey": "route-sender",
                "nonce": 0,
                "operations": {
                    "5": [
                        {
                            "module": "TauSwap",
                            "version": "0.1",
                            "kind": "ROUTE_EXACT_IN",
                            "intent_id": "route-intent",
                            "sender_pubkey": "route-sender",
                            "deadline": 100,
                            "quote_receipt_hash": _hex("route-risc0-binding"),
                            "recipient": "route-recipient",
                            "asset_in": "asset-a",
                            "asset_out": "asset-b",
                            "leg_indices": [0],
                            "legs": [{"hops": [{"pool_id": "pool-a"}]}],
                            "total_amount_in": 1,
                            "total_min_amount_out": 0,
                            "total_amount_out": 0,
                            "total_max_amount_in": 0,
                            "quote_receipt": {
                                "body": {
                                    "schema": "zenodex/route_quote_receipt/v1",
                                    "kind": "exact_in",
                                    "asset_in": "asset-a",
                                    "asset_out": "asset-b",
                                    "amount_in": 1,
                                    "amount_out": 1,
                                    "legs": [
                                        {
                                            "amount_in": 1,
                                            "amount_out": 1,
                                            "hops": [
                                                {
                                                    "pool_id": "pool-a",
                                                    "asset_in": "asset-a",
                                                    "asset_out": "asset-b",
                                                    "amount_in": 1,
                                                    "amount_out": 1,
                                                }
                                            ],
                                        }
                                    ],
                                    "pools": {"pool-a": "fingerprint-a"},
                                },
                                "receipt_hash": "0xreceipt",
                                "risc0_route_quote_receipt_binding_hash": _hex("route-risc0-binding"),
                            },
                        }
                    ]
                },
            },
        ],
        "post_hash": _hex("route-order-post"),
    }
    case["proof_transactions"] = list(
        project_route_body_transactions_to_proof_v1(case["transactions"])
    )
    return case


def _route_order_proof(*, tx_execution_order_commitment: str) -> dict[str, object]:
    post_state_root = _root("route-order-post-state")
    return {
        "schema": "tau_state_proof",
        "schema_version": 1,
        "state_hash": _hex("route-order-state"),
        "proof_type": PROOF_TYPE,
        "proof": "cmlzYzAtcmVjZWlwdA==",
        "meta": {
            "risc0_image_id": _hex("image"),
            "execution_context_hash": _hex("route-order-execution-context"),
            "txs_commitment": _hex("route-order-txs"),
            "tx_execution_order_commitment": tx_execution_order_commitment,
            "ingress_commitment": _hex("route-order-ingress"),
            "pre_nonce_root": _hex("route-order-pre-nonce"),
            "post_nonce_root": _hex("route-order-post-nonce"),
            "accepted_receipts_root": _hex("route-order-accepted"),
            "pre_app_hash": "",
            "post_app_hash": post_state_root[2:],
            "protocol_fee_share_bps": 0,
            "protocol_fee_recipient_pubkey": None,
            **_empty_route_price_meta(),
        },
    }


def test_risc0_smoke_body_emits_required_route_order_receipt() -> None:
    case = _route_order_case()

    tx_order_inputs = _tx_order_inputs_for_case(case)  # type: ignore[arg-type]
    requirement = _route_order_receipt_requirement_for_case(case)  # type: ignore[arg-type]
    body = _ledger_body_for_case(name="route_order", case=case, height=1)  # type: ignore[arg-type]
    context: dict[str, object] = {}
    context_changed = _apply_route_order_policy_to_context(context, case)  # type: ignore[arg-type]

    assert [tx.pool_write_ids for tx in tx_order_inputs] == [("pool-a",), ("pool-a",)]
    assert [tx.route_read_pool_ids for tx in tx_order_inputs] == [(), ("pool-a",)]
    assert requirement is not None
    assert requirement.required is True
    assert context_changed is True
    assert context == {"tx_execution_order": [1, 0]}
    assert body["evidence"]["proof_receipts"][-1] == requirement.receipt()  # type: ignore[index]


def test_risc0_smoke_route_order_case_binds_body_projection_to_proof_v1_route_intent() -> None:
    case = _smoke_cases()["route_order"]
    body_route_op = case["transactions"][1]["operations"]["5"][0]
    proof_transactions = _proof_transactions_for_case(case)
    route_op = proof_transactions[1]["operations"]["2"][0]

    assert body_route_op["kind"] == "ROUTE_EXACT_IN"
    assert route_op["kind"] == "ROUTE_EXACT_IN"
    assert "quote_receipt_hash" in route_op
    assert route_op["legs"] == route_op["quote_receipt"]["body"]["legs"]
    assert proof_transactions == list(project_route_body_transactions_to_proof_v1(case["transactions"]))

    tx_order_inputs = _tx_order_inputs_for_case(case)
    assert tx_order_inputs[0].route_read_pool_ids == ()
    assert tx_order_inputs[0].pool_write_ids
    assert tx_order_inputs[1].route_read_pool_ids == tx_order_inputs[0].pool_write_ids

    requirement = _route_order_receipt_requirement_for_case(case)
    assert requirement is not None
    assert requirement.required is True
    assert requirement.tx_execution_order == (1, 0)


def test_risc0_smoke_ledger_binding_accepts_matching_route_order_receipt(tmp_path: Path) -> None:
    case = _route_order_case()
    requirement = _route_order_receipt_requirement_for_case(case)  # type: ignore[arg-type]
    assert requirement is not None
    proof = _route_order_proof(tx_execution_order_commitment=requirement.tx_execution_order_commitment)

    binding = _ledger_binding_for_case(
        name="route_order",
        case=case,  # type: ignore[arg-type]
        proof=proof,  # type: ignore[arg-type]
        repo=Path.cwd(),
        out_dir=tmp_path,
        height=1,
    )

    assert binding["body_tx_execution_order_commitment_checked"] is True
    body = json.loads(Path(binding["body_path"]).read_text(encoding="utf-8"))
    assert requirement.receipt() in body["evidence"]["proof_receipts"]


def test_risc0_smoke_ledger_binding_rejects_route_order_receipt_mismatch(tmp_path: Path) -> None:
    case = _route_order_case()
    identity = build_tx_execution_order_certificate_v1([0, 1], tx_count=2)
    proof = _route_order_proof(tx_execution_order_commitment=identity.tx_execution_order_commitment)

    with pytest.raises(ValueError, match="body tx_execution_order receipt/proof meta mismatch"):
        _ledger_binding_for_case(
            name="route_order",
            case=case,  # type: ignore[arg-type]
            proof=proof,  # type: ignore[arg-type]
            repo=Path.cwd(),
            out_dir=tmp_path,
            height=1,
        )


def test_risc0_smoke_ledger_binding_rejects_body_projection_drift(tmp_path: Path) -> None:
    case = _route_order_case()
    proof_transactions = copy.deepcopy(case["proof_transactions"])  # type: ignore[index]
    proof_transactions[1]["operations"]["2"][0]["total_amount_in"] = 2  # type: ignore[index]
    case["proof_transactions"] = proof_transactions
    requirement = _route_order_receipt_requirement_for_case(case)  # type: ignore[arg-type]
    assert requirement is not None
    proof = _route_order_proof(tx_execution_order_commitment=requirement.tx_execution_order_commitment)

    with pytest.raises(ValueError, match="proof_transactions must match deterministic body projection"):
        _ledger_binding_for_case(
            name="route_order",
            case=case,  # type: ignore[arg-type]
            proof=proof,  # type: ignore[arg-type]
            repo=Path.cwd(),
            out_dir=tmp_path,
            height=1,
        )


def test_risc0_smoke_route_order_rejects_malformed_route_receipt() -> None:
    case = _route_order_case()
    route_op = case["transactions"][1]["operations"]["5"][0]  # type: ignore[index]
    route_op.pop("quote_receipt")  # type: ignore[attr-defined]

    with pytest.raises(TypeError, match="quote_receipt must be an object"):
        _tx_order_inputs_for_case(case)  # type: ignore[arg-type]


def test_risc0_smoke_route_order_rejects_lie_between_body_and_manual_summary() -> None:
    case = _route_order_case()
    case["tx_execution_order_inputs"] = [  # type: ignore[index]
        {
            "sender_pubkey": "writer",
            "route_read_pool_ids": [],
            "pool_write_ids": ["pool-b"],
        },
        {
            "sender_pubkey": "route-sender",
            "route_read_pool_ids": ["pool-a"],
            "pool_write_ids": ["pool-a"],
        },
    ]

    with pytest.raises(ValueError, match="tx_execution_order_inputs must match transaction-derived summary"):
        _tx_order_inputs_for_case(case)  # type: ignore[arg-type]


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


def test_risc0_real_proof_smoke_report_rejects_route_order_case_without_order_receipt_check() -> None:
    report = _route_order_report(body_order_checked=None)

    check = validate_risc0_real_proof_smoke_report_v0(report, required_cases={"route_order"})

    assert check["ok"] is False
    assert any(
        "ledger_binding.body_tx_execution_order_commitment_checked must be true" in err for err in check["errors"]
    )


def test_risc0_real_proof_smoke_report_accepts_route_order_case_with_order_receipt_check() -> None:
    report = _route_order_report(body_order_checked=True)

    check = validate_risc0_real_proof_smoke_report_v0(report, required_cases={"route_order"})

    assert check["ok"] is True
    assert check["required_cases"] == ["route_order"]


def test_risc0_real_proof_smoke_report_rejects_missing_projection_binding() -> None:
    report = _route_order_report(body_order_checked=True)
    case = report["cases"][0]  # type: ignore[index]
    binding = copy.deepcopy(case["ledger_binding"])  # type: ignore[index]
    binding["body_to_proof_projection_checked"] = False
    case["ledger_binding"] = binding  # type: ignore[index]

    check = validate_risc0_real_proof_smoke_report_v0(report, required_cases={"route_order"})

    assert check["ok"] is False
    assert any(
        "ledger_binding.body_to_proof_projection_checked must be true" in err for err in check["errors"]
    )


def test_risc0_real_proof_smoke_report_rejects_missing_projection_contract_hash() -> None:
    report = _route_order_report(body_order_checked=True)
    case = report["cases"][0]  # type: ignore[index]
    binding = copy.deepcopy(case["ledger_binding"])  # type: ignore[index]
    binding.pop("projection_contract_hash")
    case["ledger_binding"] = binding  # type: ignore[index]

    check = validate_risc0_real_proof_smoke_report_v0(report, required_cases={"route_order"})

    assert check["ok"] is False
    assert any("ledger_binding.projection_contract_hash must be 64-char hex" in err for err in check["errors"])


def test_risc0_real_proof_smoke_report_rejects_projection_contract_hash_mismatch() -> None:
    report = _route_order_report(body_order_checked=True)
    case = report["cases"][0]  # type: ignore[index]
    binding = copy.deepcopy(case["ledger_binding"])  # type: ignore[index]
    binding["projection_contract_hash"] = _hex("wrong-projection-contract")
    case["ledger_binding"] = binding  # type: ignore[index]

    check = validate_risc0_real_proof_smoke_report_v0(report, required_cases={"route_order"})

    assert check["ok"] is False
    assert any("ledger_binding.projection_contract_hash mismatch" in err for err in check["errors"])


def test_risc0_real_proof_smoke_report_rejects_projection_contract_semantic_drift() -> None:
    report = _route_order_report(body_order_checked=True)
    case = report["cases"][0]  # type: ignore[index]
    binding = copy.deepcopy(case["ledger_binding"])  # type: ignore[index]
    contract = copy.deepcopy(binding["projection_contract"])  # type: ignore[index]
    contract["semantic_tag"] = "drifted host projection"
    binding["projection_contract"] = contract
    case["ledger_binding"] = binding  # type: ignore[index]

    check = validate_risc0_real_proof_smoke_report_v0(report, required_cases={"route_order"})

    assert check["ok"] is False
    assert any("ledger_binding.projection_contract mismatch" in err for err in check["errors"])


def test_risc0_real_proof_smoke_report_validates_artifact_binding(tmp_path: Path) -> None:
    report = _artifact_report(tmp_path)

    check = validate_risc0_real_proof_smoke_report_v0(
        report,
        required_cases={"empty"},
        require_proof_files=True,
    )

    assert check["ok"] is True
    assert check["cases"][0]["ledger_binding_ok"] is True


def test_risc0_real_proof_smoke_report_accepts_rust_txs_commitment_match(tmp_path: Path) -> None:
    report = _artifact_report(tmp_path)
    expected = report["cases"][0]["txs_commitment"]  # type: ignore[index]
    assert isinstance(expected, str)
    fake_cli = _write_fake_risc0_commitment_cli(tmp_path, txs_commitment=expected)

    check = validate_risc0_real_proof_smoke_report_v0(
        report,
        required_cases={"empty"},
        require_proof_files=True,
        risc0_cli_bin=fake_cli,
    )

    assert check["ok"] is True


def test_risc0_real_proof_smoke_report_rejects_rust_txs_commitment_mismatch(tmp_path: Path) -> None:
    report = _artifact_report(tmp_path)
    fake_cli = _write_fake_risc0_commitment_cli(tmp_path, txs_commitment=_hex("wrong-rust-txs"))

    check = validate_risc0_real_proof_smoke_report_v0(
        report,
        required_cases={"empty"},
        require_proof_files=True,
        risc0_cli_bin=fake_cli,
    )

    assert check["ok"] is False
    assert any("artifact_binding.rust_txs_commitment mismatch" in err for err in check["errors"])


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


def test_risc0_real_proof_smoke_report_rejects_tampered_proof_transactions_artifact(tmp_path: Path) -> None:
    report = _artifact_report(tmp_path)
    binding = report["cases"][0]["ledger_binding"]  # type: ignore[index]
    proof_transactions_path = Path(binding["proof_transactions_path"])  # type: ignore[index]
    _write_json(proof_transactions_path, [{"unexpected": "transaction"}])

    check = validate_risc0_real_proof_smoke_report_v0(
        report,
        required_cases={"empty"},
        require_proof_files=True,
    )

    assert check["ok"] is False
    assert any("artifact_binding.proof_transactions_hash mismatch" in err for err in check["errors"])
    assert any("artifact_binding.body_to_proof_projection rejected" in err for err in check["errors"])


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


def test_risc0_real_proof_smoke_report_cli_accepts_route_order_required_case(
    tmp_path,
    capsys,
) -> None:
    report_path = tmp_path / "route_order_report.json"
    report_path.write_text(
        json.dumps(_route_order_report(body_order_checked=True), indent=2, sort_keys=True),
        encoding="utf-8",
    )

    code = main([str(report_path), "--required-case", "route_order"])
    out = capsys.readouterr().out
    check = json.loads(out)

    assert code == 0
    assert check["ok"] is True
    assert check["required_cases"] == ["route_order"]


def test_risc0_real_proof_smoke_report_cli_rejects_route_order_without_body_check(
    tmp_path,
    capsys,
) -> None:
    report_path = tmp_path / "route_order_report.json"
    report_path.write_text(
        json.dumps(_route_order_report(body_order_checked=False), indent=2, sort_keys=True),
        encoding="utf-8",
    )

    code = main([str(report_path), "--required-case", "route_order"])
    out = capsys.readouterr().out
    check = json.loads(out)

    assert code == 1
    assert check["ok"] is False
    assert any(
        "body_tx_execution_order_commitment_checked must be true" in error
        for error in check["errors"]
    )
