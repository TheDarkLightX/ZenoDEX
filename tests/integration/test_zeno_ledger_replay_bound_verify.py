from __future__ import annotations

import json
import subprocess
import sys
from copy import deepcopy
from pathlib import Path
from typing import Any

import pytest

import src.integration.zeno_ledger_v0 as zeno_ledger_v0
from src.core.dex import DexState
from src.integration.dex_engine import DexEngineConfig
from src.integration.dex_snapshot import snapshot_from_state
from src.integration.zeno_ledger_replay import (
    parse_replay_engine_config_v0,
    replay_engine_config_digest_v0,
    replay_engine_config_document_v0,
)
from src.integration.zeno_ledger_v0 import (
    apply_body_transactions_v0,
    build_header_v0,
    build_tx_receipt_v0,
    canonical_body_root_v0,
    canonical_header_hash_v0,
    compute_app_hash_v0,
    compute_evidence_root_v0,
    compute_ingress_root_v0,
    compute_tx_root_v0,
    dex_state_root_v0,
    hash_v0,
    tx_hash_v0,
)
from src.integration.zeno_ledger_watcher import build_watcher_attestation_v0
from src.state.balances import BalanceTable
from src.state.lp import LPTable
from tests.integration.test_zeno_ledger_verify_cli import _body, _root
from tools.zeno_ledger_verify import (
    REPLAY_BOUND_MODE,
    STRUCTURAL_DIAGNOSTIC_MODE,
    verify_zeno_ledger_v0,
)

ZERO_ROOT = "0x" + "00" * 32
ROOT = Path(__file__).resolve().parents[2]
ATTEST_SCRIPT = ROOT / "tools" / "zeno_ledger_attest.py"
VERIFY_SCRIPT = ROOT / "tools" / "zeno_ledger_verify.py"


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _empty_state() -> DexState:
    return DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())


def _empty_body(height: int) -> dict[str, Any]:
    body = _body(height, txs=[])
    evidence = dict(body["evidence"])
    evidence["rejection_receipts"] = []
    body["evidence"] = evidence
    return body


def _header(
    *,
    body: dict[str, Any],
    prev_header_hash: str,
    pre_state_root: str,
    post_state_root: str,
    config_digest: str,
) -> dict[str, Any]:
    evidence_root = compute_evidence_root_v0(body["evidence"])
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
    return build_header_v0(
        chain_id=str(body["chain_id"]),
        height=int(body["height"]),
        time_ms=1_778_730_000_000 + int(body["height"]),
        prev_header_hash=prev_header_hash,
        sequencer_set_hash=_root("sequencer-set"),
        ingress_root=compute_ingress_root_v0(body["ingress"]),
        tx_root=compute_tx_root_v0(body["transactions"]),
        pre_state_root=pre_state_root,
        post_state_root=post_state_root,
        app_hash=app_hash,
        evidence_root=evidence_root,
        body_root=canonical_body_root_v0(body),
        data_availability_root=_root("da"),
        proof_journal_hash=ZERO_ROOT,
        config_digest=config_digest,
        module_versions_digest=module_versions_digest,
        signature_set_root=ZERO_ROOT,
    )


def _strict_verify(
    *,
    headers_dir: Path,
    bodies_dir: Path,
    snapshots_dir: Path,
    config_path: Path,
    to_height: int,
) -> dict[str, Any]:
    return verify_zeno_ledger_v0(
        headers_dir=headers_dir,
        bodies_dir=bodies_dir,
        checkpoints_dir=None,
        profile_path=None,
        from_height=1,
        to_height=to_height,
        mode=REPLAY_BOUND_MODE,
        pre_snapshots_dir=snapshots_dir,
        engine_config_path=config_path,
        require_rejection_receipt_replay=True,
    )


def _write_single_height(
    tmp_path: Path,
    *,
    body: dict[str, Any],
    pre_state: DexState,
    post_state_root: str,
    header_config_digest: str | None = None,
) -> tuple[Path, Path, Path, Path, str]:
    headers_dir = tmp_path / "headers"
    bodies_dir = tmp_path / "bodies"
    snapshots_dir = tmp_path / "pre_snapshots"
    config_path = tmp_path / "engine_config.json"
    config = DexEngineConfig(chain_id="zeno-ledger-devnet-0")
    config_document = replay_engine_config_document_v0(config)
    config_digest = replay_engine_config_digest_v0(config_document)
    header = _header(
        body=body,
        prev_header_hash=ZERO_ROOT,
        pre_state_root=dex_state_root_v0(pre_state),
        post_state_root=post_state_root,
        config_digest=header_config_digest or config_digest,
    )
    _write_json(headers_dir / "1.json", header)
    _write_json(bodies_dir / "1.json", body)
    _write_json(snapshots_dir / "1.json", snapshot_from_state(pre_state).data)
    _write_json(config_path, config_document)
    return headers_dir, bodies_dir, snapshots_dir, config_path, config_digest


def test_recomputed_child_pre_state_mismatch_is_only_structurally_accepted(
    tmp_path: Path,
) -> None:
    headers_dir = tmp_path / "headers"
    bodies_dir = tmp_path / "bodies"
    snapshots_dir = tmp_path / "pre_snapshots"
    config_path = tmp_path / "engine_config.json"
    config = DexEngineConfig(chain_id="zeno-ledger-devnet-0")
    config_document = replay_engine_config_document_v0(config)
    config_digest = replay_engine_config_digest_v0(config_document)
    state = _empty_state()
    state_root = dex_state_root_v0(state)

    body_1 = _empty_body(1)
    header_1 = _header(
        body=body_1,
        prev_header_hash=ZERO_ROOT,
        pre_state_root=state_root,
        post_state_root=state_root,
        config_digest=config_digest,
    )
    body_2 = _empty_body(2)
    header_2 = _header(
        body=body_2,
        prev_header_hash=canonical_header_hash_v0(header_1),
        pre_state_root=_root("forged-child-pre-state"),
        post_state_root=state_root,
        config_digest=config_digest,
    )
    for height, header, body in ((1, header_1, body_1), (2, header_2, body_2)):
        _write_json(headers_dir / f"{height}.json", header)
        _write_json(bodies_dir / f"{height}.json", body)
    _write_json(snapshots_dir / "1.json", snapshot_from_state(state).data)
    _write_json(config_path, config_document)

    structural = verify_zeno_ledger_v0(
        headers_dir=headers_dir,
        bodies_dir=bodies_dir,
        checkpoints_dir=None,
        profile_path=None,
        from_height=1,
        to_height=2,
        mode=STRUCTURAL_DIAGNOSTIC_MODE,
    )
    replay_bound = verify_zeno_ledger_v0(
        headers_dir=headers_dir,
        bodies_dir=bodies_dir,
        checkpoints_dir=None,
        profile_path=None,
        from_height=1,
        to_height=2,
        mode=REPLAY_BOUND_MODE,
        pre_snapshots_dir=snapshots_dir,
        engine_config_path=config_path,
        require_rejection_receipt_replay=True,
    )

    assert structural["ok"] is True
    assert structural["status"] == "structural_diagnostic_accepted"
    assert structural["range_verified"] is False
    assert structural["state_continuity_checked"] is False
    assert replay_bound["ok"] is False
    assert replay_bound["status"] == "rejected"
    assert replay_bound["checked_heights"] == []
    assert replay_bound["proof_metadata_checked_heights"] == []
    assert replay_bound["proof_verification_checked_heights"] == []
    assert replay_bound["last_header_hash"] is None
    assert replay_bound["last_post_state_root"] is None
    assert replay_bound["last_app_hash"] is None
    assert any("pre_state_root does not match parent post_state_root" in error for error in replay_bound["errors"])


def test_replay_bound_range_uses_one_anchor_snapshot_and_one_body_replay_per_height(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    headers_dir = tmp_path / "headers"
    bodies_dir = tmp_path / "bodies"
    snapshots_dir = tmp_path / "pre_snapshots"
    config_path = tmp_path / "engine_config.json"
    config = DexEngineConfig(chain_id="zeno-ledger-devnet-0")
    config_document = replay_engine_config_document_v0(config)
    config_digest = replay_engine_config_digest_v0(config_document)
    state = _empty_state()
    state_root = dex_state_root_v0(state)
    previous_hash = ZERO_ROOT
    for height in (1, 2, 3):
        body = _empty_body(height)
        header = _header(
            body=body,
            prev_header_hash=previous_hash,
            pre_state_root=state_root,
            post_state_root=state_root,
            config_digest=config_digest,
        )
        _write_json(headers_dir / f"{height}.json", header)
        _write_json(bodies_dir / f"{height}.json", body)
        previous_hash = canonical_header_hash_v0(header)
    _write_json(snapshots_dir / "1.json", snapshot_from_state(state).data)
    _write_json(config_path, config_document)

    original_apply = zeno_ledger_v0.apply_body_transactions_v0
    replayed_heights: list[int] = []

    def counted_apply_body_transactions_v0(
        *,
        state: DexState,
        body: dict[str, Any],
        config: DexEngineConfig,
        default_block_timestamp: int | None = None,
    ) -> tuple[DexState, dict[str, Any], list[dict[str, Any]]]:
        replayed_heights.append(int(body["height"]))
        return original_apply(
            state=state,
            body=body,
            config=config,
            default_block_timestamp=default_block_timestamp,
        )

    monkeypatch.setattr(
        zeno_ledger_v0,
        "apply_body_transactions_v0",
        counted_apply_body_transactions_v0,
    )

    report = _strict_verify(
        headers_dir=headers_dir,
        bodies_dir=bodies_dir,
        snapshots_dir=snapshots_dir,
        config_path=config_path,
        to_height=3,
    )

    assert report["ok"] is True
    assert report["checked_heights"] == [1, 2, 3]
    assert replayed_heights == [1, 2, 3]

    mismatched_balances = BalanceTable()
    mismatched_balances.set("0x" + "11" * 48, "0x" + "22" * 32, 1)
    mismatched_state = DexState(
        balances=mismatched_balances,
        pools={},
        lp_balances=LPTable(),
    )
    _write_json(snapshots_dir / "2.json", snapshot_from_state(mismatched_state).data)
    replayed_heights.clear()

    mismatch_report = _strict_verify(
        headers_dir=headers_dir,
        bodies_dir=bodies_dir,
        snapshots_dir=snapshots_dir,
        config_path=config_path,
        to_height=3,
    )

    assert mismatch_report["ok"] is False
    assert mismatch_report["checked_heights"] == []
    assert replayed_heights == [1]
    assert any(
        "snapshot root does not match carried replay state" in error
        for error in mismatch_report["errors"]
    )


def test_replay_bound_range_accepts_only_with_all_authority_checks(tmp_path: Path) -> None:
    headers_dir = tmp_path / "headers"
    bodies_dir = tmp_path / "bodies"
    snapshots_dir = tmp_path / "pre_snapshots"
    config_path = tmp_path / "engine_config.json"
    config = DexEngineConfig(chain_id="zeno-ledger-devnet-0")
    config_document = replay_engine_config_document_v0(config)
    config_digest = replay_engine_config_digest_v0(config_document)
    state = _empty_state()
    state_root = dex_state_root_v0(state)
    previous_hash = ZERO_ROOT
    for height in (1, 2):
        body = _empty_body(height)
        header = _header(
            body=body,
            prev_header_hash=previous_hash,
            pre_state_root=state_root,
            post_state_root=state_root,
            config_digest=config_digest,
        )
        _write_json(headers_dir / f"{height}.json", header)
        _write_json(bodies_dir / f"{height}.json", body)
        _write_json(snapshots_dir / f"{height}.json", snapshot_from_state(state).data)
        previous_hash = canonical_header_hash_v0(header)
    _write_json(config_path, config_document)

    report = _strict_verify(
        headers_dir=headers_dir,
        bodies_dir=bodies_dir,
        snapshots_dir=snapshots_dir,
        config_path=config_path,
        to_height=2,
    )

    assert report["ok"] is True
    assert report["status"] == "range_verified"
    assert report["authority_scope"] == "replay_bound_range_v0"
    assert report["checked_heights"] == [1, 2]
    for field in (
        "range_verified",
        "header_linkage_checked",
        "state_continuity_checked",
        "state_replay_checked",
        "receipt_replay_checked",
        "config_binding_checked",
    ):
        assert report[field] is True
    assert report["proof_authority_capable"] is False
    attestation = build_watcher_attestation_v0(
        verify_report=report,
        watcher_id="watcher-410",
        observed_time_ms=1_778_730_000_000,
        verifier_ref="JAMES-410-20260713",
    )
    assert attestation["status"] == "range_verified"
    assert attestation["proof_authority_required"] is False
    assert attestation["proof_authority_satisfied"] is False
    assert attestation["proof_authority_capable"] is False
    assert attestation["settlement_authority"] is False
    assert attestation["production_authority"] is False

    forged_proof_required = deepcopy(report)
    forged_proof_required["proof_authority_required"] = True
    with pytest.raises(ValueError, match="proof-required report"):
        build_watcher_attestation_v0(
            verify_report=forged_proof_required,
            watcher_id="watcher-410",
            observed_time_ms=1_778_730_000_000,
            verifier_ref="JAMES-410-20260713",
        )


def test_replay_bound_range_rejects_fabricated_post_state_root(tmp_path: Path) -> None:
    state = _empty_state()
    inputs = _write_single_height(
        tmp_path,
        body=_empty_body(1),
        pre_state=state,
        post_state_root=_root("fabricated-post-state"),
    )

    report = _strict_verify(
        headers_dir=inputs[0],
        bodies_dir=inputs[1],
        snapshots_dir=inputs[2],
        config_path=inputs[3],
        to_height=1,
    )

    assert report["ok"] is False
    assert report["checked_heights"] == []
    assert any("post_state_root does not match re-executed body state" in error for error in report["errors"])


@pytest.mark.parametrize("mutation", ["forged", "missing", "duplicated", "reordered"])
def test_replay_bound_range_rejects_mutated_rejection_receipts(
    tmp_path: Path,
    mutation: str,
) -> None:
    state = _empty_state()
    config = DexEngineConfig(chain_id="zeno-ledger-devnet-0")
    transactions = [
        {"sender": "alice", "nonce": 1},
        {"sender": "bob", "nonce": 1},
    ]
    body = _body(1, txs=transactions)
    evidence = dict(body["evidence"])
    evidence["rejection_receipts"] = []
    body["evidence"] = evidence
    _post_state, executed_body, _receipts = apply_body_transactions_v0(
        state=state,
        body=body,
        config=config,
    )
    committed = deepcopy(executed_body["evidence"]["rejection_receipts"])
    if mutation == "forged":
        committed[0] = build_tx_receipt_v0(
            tx_hash=tx_hash_v0(transactions[0]),
            height=1,
            index=0,
            accepted=False,
            error_code="forged_rejection",
            state_changed=False,
        )
    elif mutation == "missing":
        committed = committed[1:]
    elif mutation == "duplicated":
        committed.append(deepcopy(committed[-1]))
    else:
        committed.reverse()
    mutated_body = deepcopy(executed_body)
    mutated_body["evidence"]["rejection_receipts"] = committed
    inputs = _write_single_height(
        tmp_path,
        body=mutated_body,
        pre_state=state,
        post_state_root=dex_state_root_v0(state),
    )

    structural = verify_zeno_ledger_v0(
        headers_dir=inputs[0],
        bodies_dir=inputs[1],
        checkpoints_dir=None,
        profile_path=None,
        from_height=1,
        to_height=1,
        mode=STRUCTURAL_DIAGNOSTIC_MODE,
    )
    replay_bound = _strict_verify(
        headers_dir=inputs[0],
        bodies_dir=inputs[1],
        snapshots_dir=inputs[2],
        config_path=inputs[3],
        to_height=1,
    )

    assert structural["ok"] is True
    assert replay_bound["ok"] is False
    assert any("rejection receipts do not match" in error for error in replay_bound["errors"])


def test_replay_bound_range_rejects_mismatched_engine_config_digest(tmp_path: Path) -> None:
    state = _empty_state()
    inputs = _write_single_height(
        tmp_path,
        body=_empty_body(1),
        pre_state=state,
        post_state_root=dex_state_root_v0(state),
        header_config_digest=_root("unrelated-config"),
    )

    report = _strict_verify(
        headers_dir=inputs[0],
        bodies_dir=inputs[1],
        snapshots_dir=inputs[2],
        config_path=inputs[3],
        to_height=1,
    )

    assert report["ok"] is False
    assert report["config_binding_checked"] is False
    assert any("config_digest does not match governed engine config" in error for error in report["errors"])


def test_replay_bound_range_rejects_tampered_fixed_engine_config(tmp_path: Path) -> None:
    state = _empty_state()
    canonical_document = replay_engine_config_document_v0(
        DexEngineConfig(chain_id="zeno-ledger-devnet-0")
    )
    tampered_document = deepcopy(canonical_document)
    tampered_document["config"]["max_intents"] = 257
    tampered_digest = hash_v0("zeno_ledger_replay_engine_config_v0", tampered_document)
    inputs = _write_single_height(
        tmp_path,
        body=_empty_body(1),
        pre_state=state,
        post_state_root=dex_state_root_v0(state),
        header_config_digest=tampered_digest,
    )
    _write_json(inputs[3], tampered_document)

    report = _strict_verify(
        headers_dir=inputs[0],
        bodies_dir=inputs[1],
        snapshots_dir=inputs[2],
        config_path=inputs[3],
        to_height=1,
    )

    assert report["ok"] is False
    assert report["checked_heights"] == []
    assert any("engine_config_invalid" in error for error in report["errors"])


def test_replay_engine_config_document_is_float_free_and_rejects_injected_float() -> None:
    canonical_document = replay_engine_config_document_v0(
        DexEngineConfig(chain_id="zeno-ledger-devnet-0")
    )

    assert "timeout_s" not in canonical_document["config"]["proof_config"]
    assert "float64_hex" not in json.dumps(canonical_document, sort_keys=True)

    tampered_document = deepcopy(canonical_document)
    tampered_document["config"]["proof_config"]["timeout_s"] = 10.0
    with pytest.raises((TypeError, ValueError), match="float"):
        parse_replay_engine_config_v0(tampered_document)


def test_verify_cli_requires_explicit_structural_or_replay_mode(tmp_path: Path) -> None:
    state = _empty_state()
    inputs = _write_single_height(
        tmp_path,
        body=_empty_body(1),
        pre_state=state,
        post_state_root=dex_state_root_v0(state),
    )

    proc = subprocess.run(
        [
            sys.executable,
            str(VERIFY_SCRIPT),
            "--headers-dir",
            str(inputs[0]),
            "--bodies-dir",
            str(inputs[1]),
            "--from-height",
            "1",
            "--to-height",
            "1",
        ],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )

    assert proc.returncode == 2
    assert "one of the arguments --structural-only --require-state-replay is required" in proc.stderr


def test_watcher_attestation_rejects_structural_diagnostic_report(tmp_path: Path) -> None:
    state = _empty_state()
    inputs = _write_single_height(
        tmp_path,
        body=_empty_body(1),
        pre_state=state,
        post_state_root=dex_state_root_v0(state),
    )
    structural = verify_zeno_ledger_v0(
        headers_dir=inputs[0],
        bodies_dir=inputs[1],
        checkpoints_dir=None,
        profile_path=None,
        from_height=1,
        to_height=1,
        mode=STRUCTURAL_DIAGNOSTIC_MODE,
    )

    with pytest.raises(ValueError, match="replay-bound range verification"):
        build_watcher_attestation_v0(
            verify_report=structural,
            watcher_id="watcher-410",
            observed_time_ms=1_778_730_000_000,
            verifier_ref="JAMES-410-20260713",
        )


def test_attest_cli_refuses_structural_report_and_accepts_replay_bound_range(
    tmp_path: Path,
) -> None:
    state = _empty_state()
    inputs = _write_single_height(
        tmp_path,
        body=_empty_body(1),
        pre_state=state,
        post_state_root=dex_state_root_v0(state),
    )
    common = [
        sys.executable,
        str(ATTEST_SCRIPT),
        "--headers-dir",
        str(inputs[0]),
        "--bodies-dir",
        str(inputs[1]),
        "--from-height",
        "1",
        "--to-height",
        "1",
        "--watcher-id",
        "watcher-410",
        "--observed-time-ms",
        "1778730000000",
        "--verifier-ref",
        "JAMES-410-20260713",
    ]

    structural = subprocess.run(
        [*common, "--structural-only"],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )
    replay_bound = subprocess.run(
        [
            *common,
            "--require-state-replay",
            "--require-rejection-receipt-replay",
            "--pre-snapshots-dir",
            str(inputs[2]),
            "--engine-config",
            str(inputs[3]),
        ],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )

    structural_report = json.loads(structural.stdout)
    replay_bound_report = json.loads(replay_bound.stdout)
    assert structural.returncode == 1
    assert structural_report["ok"] is False
    assert structural_report["verify_report"]["status"] == "structural_diagnostic_accepted"
    assert replay_bound.returncode == 0, replay_bound.stderr
    assert replay_bound_report["ok"] is True
    assert replay_bound_report["verify_report"]["status"] == "range_verified"
    assert replay_bound_report["attestation"]["status"] == "range_verified"
