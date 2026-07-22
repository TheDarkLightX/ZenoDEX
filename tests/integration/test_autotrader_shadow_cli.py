from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

import tools.autotrader_shadow as autotrader_shadow_cli
from src.agents.krr_bundle_artifacts import (
    KRRReviewRecord,
    KRRSourceSnapshot,
    build_autotrader_krr_bundle,
    sign_autotrader_krr_bundle,
)
from src.agents.local_policy import dump_local_policy_document
from src.agents.policy_compiler import compile_policy_candidate
from src.agents.strategy_ir import AUTOTRADER_TAU_POLICY_SPECS
from src.core.quote_receipts import make_route_quote_receipt
from src.core.routing import best_route_exact_in_2hop
from src.state.canonical import sha256_hex
from src.state.immutable_json import snapshot_json_mapping
from src.state.pools import PoolState, PoolStatus

REPO_ROOT = Path(__file__).resolve().parents[2]
CLI_PATH = REPO_ROOT / "tools" / "autotrader_shadow.py"


def _pool(pid: str, a0: str, a1: str, r0: int, r1: int, fee_bps: int = 0) -> PoolState:
    return PoolState(
        pool_id=pid,
        asset0=min(a0, a1),
        asset1=max(a0, a1),
        reserve0=r0 if a0 < a1 else r1,
        reserve1=r1 if a0 < a1 else r0,
        fee_bps=fee_bps,
        lp_supply=1,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )


def _candidate(*, backend: str = "local", fixed_order_size: int = 100) -> dict[str, object]:
    out: dict[str, object] = {
        "strategy_id": f"dca.{backend}.cli",
        "owner_pubkey": "owner.pubkey.1",
        "policy_backend": backend,
        "template": "dca",
        "asset_universe": ["A", "B"],
        "notional_caps": {
            "per_order_max": fixed_order_size,
            "per_window_max": 500,
            "lifetime_max": 1_000,
        },
        "risk_limits": {
            "max_slippage_bps": 50,
            "max_oracle_staleness_epochs": 3,
        },
        "strategy_window": {
            "valid_from_epoch": 1,
            "valid_until_epoch": 100,
            "min_order_spacing_epochs": 0,
        },
        "template_params": {
            "fixed_order_size": fixed_order_size,
            "cadence_epochs": 4,
            "asset_in": "A",
            "asset_out": "B",
        },
    }
    if backend == "tau":
        out["tau_policy_specs"] = list(AUTOTRADER_TAU_POLICY_SPECS)
    return out


def _policy_and_market(tmp_path: Path) -> tuple[Path, Path, Path]:
    strategy = compile_policy_candidate(_candidate()).strategy
    pools = {"p_ab": _pool("p_ab", "A", "B", 1_000, 2_000, 10)}
    quote = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=100)
    assert quote is not None
    receipt = snapshot_json_mapping(
        make_route_quote_receipt(kind="exact_in", quote=quote, pools_by_id=pools, quote_epoch=5),
        name="test_receipt",
    )

    policy_path = tmp_path / "policy.json"
    policy_path.write_text(json.dumps(dump_local_policy_document(strategy), indent=2), encoding="utf-8")
    pools_path = tmp_path / "pools.json"
    pools_path.write_text(
        json.dumps(
            {
                pid: {
                    "pool_id": pool.pool_id,
                    "asset0": pool.asset0,
                    "asset1": pool.asset1,
                    "reserve0": pool.reserve0,
                    "reserve1": pool.reserve1,
                    "fee_bps": pool.fee_bps,
                    "lp_supply": pool.lp_supply,
                    "status": pool.status.value,
                    "created_at": pool.created_at,
                    "curve_tag": pool.curve_tag,
                    "curve_params": pool.curve_params,
                }
                for pid, pool in pools.items()
            },
            indent=2,
            sort_keys=True,
        ),
        encoding="utf-8",
    )
    receipt_path = tmp_path / "receipt.json"
    receipt_path.write_text(json.dumps(receipt, indent=2, sort_keys=True), encoding="utf-8")
    return policy_path, pools_path, receipt_path


def _write_signal_source_registry(tmp_path: Path) -> Path:
    registry_path = tmp_path / "signal_source_registry.json"
    registry_path.write_text(
        json.dumps(
            {
                "schema": "zenodex/autotrader-external-signal-source-registry/v1",
                "entry_count": 2,
                "entries": [
                    {
                        "schema": "zenodex/autotrader-external-signal-source-registry-entry/v1",
                        "source_id": "feed.news.alpha",
                        "source_kind": "advisory_external",
                        "allowed_trust_tiers": ["advisory"],
                        "require_advisory_only": True,
                        "require_auth": False,
                        "require_freshness": False,
                        "enabled": True,
                        "tags": [],
                    },
                    {
                        "schema": "zenodex/autotrader-external-signal-source-registry-entry/v1",
                        "source_id": "oracle.alpha",
                        "source_kind": "attested_external",
                        "allowed_trust_tiers": ["attested", "verified"],
                        "require_advisory_only": False,
                        "require_auth": True,
                        "require_freshness": True,
                        "enabled": True,
                        "tags": [],
                    },
                ]
            },
            indent=2,
            sort_keys=True,
        ),
        encoding="utf-8",
    )
    return registry_path


def _write_tampered_signal_source_registry(tmp_path: Path) -> Path:
    registry_path = _write_signal_source_registry(tmp_path)
    payload = json.loads(registry_path.read_text(encoding="utf-8"))
    payload["entry_count"] = 3
    registry_path.write_text(
        json.dumps(payload, indent=2, sort_keys=True),
        encoding="utf-8",
    )
    return registry_path


def _write_krr_bundle(tmp_path: Path) -> Path:
    snapshot_body = b"macro advisory snapshot"
    snapshot = KRRSourceSnapshot(
        snapshot_id="feed.news.alpha.snap1",
        source_id="feed.news.alpha",
        source_class="research_paper",
        source_uri="https://example.com/research/note",
        fetched_at="2026-03-12T00:00:00Z",
        observed_at="2026-03-12T00:00:00Z",
        media_type="text/plain",
        content_sha256=sha256_hex(snapshot_body),
        content_bytes=len(snapshot_body),
        trust_ceiling="advisory",
        parser_id="raw_snapshot",
        parser_version="v1",
        text_sha256=sha256_hex(snapshot_body),
        title="Research Note",
    )
    bundle = build_autotrader_krr_bundle(
        bundle_name="bundle.shadow.cli",
        built_at="2026-03-12T00:15:00Z",
        compiler_version="bundle_builder_v1",
        policy_version="policy_v1",
        runtime_krr_kb={
            "operator_priors": {},
            "semantic_rules": [],
            "check_priors": {"policy::budget_guard": {"base_weight": 1.25}},
            "check_family_priors": {},
        },
        runtime_external_signals={
            "external_signals": [
                {
                    "signal_id": "sig.news.1",
                    "source_id": snapshot.source_id,
                    "source_kind": "advisory_external",
                    "trust_tier": "advisory",
                    "freshness_ok": True,
                    "auth_ok": False,
                    "advisory_only": True,
                    "tags": ["macro"],
                }
            ]
        },
        runtime_signal_source_registry={
            "entries": [
                {
                    "source_id": snapshot.source_id,
                    "source_kind": "advisory_external",
                    "allowed_trust_tiers": ["advisory"],
                    "require_advisory_only": True,
                }
            ]
        },
        runtime_history={"history_source_stats": {snapshot.source_id: {"submit": 3, "reject": 0, "skip": 1}}},
        source_snapshots=(snapshot,),
        review_records=(
            KRRReviewRecord(
                review_id="bundle.shadow.cli.review",
                target_kind="bundle",
                target_id="bundle.shadow.cli",
                decision="approve",
                reviewer="security.review",
                reviewed_at="2026-03-12T00:10:00Z",
                rationale="shadow bundle approved",
                approved_for_runtime=True,
                provenance_ok=True,
            ),
        ),
    )
    signed = sign_autotrader_krr_bundle(bundle, privkey=21)
    bundle_path = tmp_path / "krr_bundle.json"
    bundle_path.write_text(json.dumps(signed.to_dict(), indent=2, sort_keys=True), encoding="utf-8")
    return bundle_path


def test_build_shadow_report_degrades_when_krr_advice_raises(monkeypatch: pytest.MonkeyPatch) -> None:
    strategy = compile_policy_candidate(_candidate()).strategy
    pools = {"p_ab": _pool("p_ab", "A", "B", 1_000, 2_000, 10)}
    quote = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=100)
    assert quote is not None
    receipt = make_route_quote_receipt(kind="exact_in", quote=quote, pools_by_id=pools, quote_epoch=5)

    def _boom(**_: object) -> dict[str, object] | None:
        raise RuntimeError("shadow krr unavailable")

    monkeypatch.setattr(autotrader_shadow_cli, "advise_autotrader_krr", _boom)

    report = autotrader_shadow_cli.build_shadow_report(
        strategy=strategy,
        controller_state=autotrader_shadow_cli.AutoTraderControllerState(),
        receipt=receipt,
        pools_by_id=pools,
        current_epoch=5,
        intent_deadline=99,
        slippage_bps=None,
        nonce_start=None,
        tau_config=None,
        krr_backend="python",
        krr_kb_path=None,
        krr_kb=None,
        history_check_stats=None,
        external_signals=(),
        signal_source_registry=None,
    )

    assert report["decision"]["tag"] == "submit"
    assert report["krr_advice"] is None
    assert report["krr_advice_error"] == "RuntimeError:shadow krr unavailable"


def test_autotrader_shadow_cli_policy_file_roundtrip(tmp_path: Path) -> None:
    policy_path, pools_path, receipt_path = _policy_and_market(tmp_path)
    telemetry_path = tmp_path / "shadow_report.json"
    external_signals_path = tmp_path / "external_signals.json"
    registry_path = _write_signal_source_registry(tmp_path)
    external_signals_path.write_text(
        json.dumps(
            {
                "external_signals": [
                    {
                        "signal_id": "sig.news.1",
                        "source_id": "feed.news.alpha",
                        "source_kind": "advisory_external",
                        "trust_tier": "advisory",
                        "freshness_ok": True,
                        "auth_ok": False,
                        "advisory_only": True,
                        "tags": ["macro"],
                    },
                    {
                        "signal_id": "sig.oracle.1",
                        "source_id": "oracle.alpha",
                        "source_kind": "attested_external",
                        "trust_tier": "verified",
                        "freshness_ok": True,
                        "auth_ok": True,
                        "advisory_only": False,
                        "tags": ["oracle"],
                    },
                ]
            },
            indent=2,
            sort_keys=True,
        ),
        encoding="utf-8",
    )

    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--policy-file",
            str(policy_path),
            "--receipt-file",
            str(receipt_path),
            "--pools-file",
            str(pools_path),
            "--external-signals-file",
            str(external_signals_path),
            "--signal-source-registry-file",
            str(registry_path),
            "--current-epoch",
            "5",
            "--intent-deadline",
            "99",
            "--telemetry-out",
            str(telemetry_path),
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["decision"]["tag"] == "submit"
    assert report["strategy_support_matrix"]["overall_status"] == "supported"
    assert report["strategy_support_matrix"]["shadow"]["supported"] is True
    assert report["strategy_support_matrix"]["live"]["supported"] is True
    assert report["tau_policy_bundle"]["schema"] == "zenodex/strategy-policy-bundle/v1"
    assert report["policy_artifact"]["schema"] == "zenodex/strategy-policy-artifact/v1"
    assert report["candidate_set"]["schema"] == "zenodex/strategy-candidate-set/v1"
    assert report["candidate_set_contract"]["ok"] is True
    assert report["decision_certificate"]["schema"] == "zenodex/strategy-decision/v1"
    assert report["decision_contract"]["ok"] is True
    assert report["decision_witness"]["schema"] == "zenodex/decision-witness/v1"
    assert report["decision_witness"]["witness_kind"] == "autotrader_binary_decision"
    assert report["decision_witness_contract"]["ok"] is True
    assert report["bounded_multiaction_candidate_set"]["schema"] == "zenodex/strategy-multi-action-candidate-set/v1"
    assert report["bounded_multiaction_candidate_set_contract"]["ok"] is True
    assert report["bounded_multiaction_candidate_set_contract"]["error"] is None
    assert report["bounded_multiaction_candidate_set_contract"]["frontier_unambiguous"] is True
    assert report["bounded_multiaction_decision_certificate"]["schema"] == "zenodex/strategy-multi-action-decision/v1"
    assert report["bounded_multiaction_decision_contract"]["ok"] is True
    assert report["bounded_multiaction_decision_contract"]["frontier_unambiguous"] is True
    assert report["bounded_multiaction_decision_witness"]["schema"] == "zenodex/decision-witness/v1"
    assert report["bounded_multiaction_decision_witness"]["witness_kind"] == "autotrader_multiaction_decision"
    assert report["bounded_multiaction_decision_witness_contract"]["ok"] is True
    assert report["bounded_multiaction_decision_witness_contract"]["frontier_unambiguous"] is True
    assert report["bounded_multiaction_tau_argmax_contract"]["ok"] is None
    assert report["bounded_multiaction_tau_argmax_contract"]["error"] == "tau_disabled"
    assert report["bounded_multiaction_tau_argmax_contract"]["tau_enabled"] is False
    assert report["bounded_multiaction_tau_argmax_contract"]["tau_used"] is False
    assert report["bounded_multiaction_tau_argmax_contract"]["frontier_unambiguous"] is True
    assert report["bounded_multiaction_decision_certificate"]["winner_kind"] == "place_swap_exact_in"
    assert report["kill_switch"]["ok"] is True
    assert len(report["external_signals"]) == 2
    assert report["signal_source_registry"]["entry_count"] == 2
    assert report["observation_packet"]["external_signals"][1]["source_kind"] == "attested_external"
    assert report["observation_packet"]["signal_source_registry_present"] is True
    assert report["krr_advice"] is not None
    assert report["krr_advice"]["backend_used"] == "python"
    assert "policy::budget_guard" in report["krr_advice"]["preferred_checks"]
    assert "policy::oracle_freshness" in report["krr_advice"]["preferred_checks"]
    assert "signal::external_advisory_separation" in report["krr_advice"]["candidate_checks"]
    assert "signal::external_attestation" in report["krr_advice"]["candidate_checks"]
    assert "signal::source_registry" in report["krr_advice"]["candidate_checks"]
    assert "quote::route_economic_sanity" in report["krr_advice"]["candidate_checks"]
    assert report["krr_advice"]["observation_summary"]["external_signal_count"] == 2
    assert report["krr_advice"]["observation_summary"]["trusted_external_signal_count"] == 1
    assert report["krr_advice"]["observation_summary"]["advisory_external_signal_count"] == 1
    assert report["krr_advice"]["observation_summary"]["source_registry_present"] is True
    assert report["krr_advice"]["route_risk_summary"]["route_shape_supported_for_intents"] is True
    assert telemetry_path.exists()
    persisted = json.loads(telemetry_path.read_text(encoding="utf-8"))
    assert persisted["decision"]["controller_state_after"]["budget_state"]["spent_in_window"] == 100


def test_autotrader_shadow_cli_rejects_tampered_typed_signal_source_registry_payload(
    tmp_path: Path,
) -> None:
    policy_path, pools_path, receipt_path = _policy_and_market(tmp_path)
    registry_path = _write_tampered_signal_source_registry(tmp_path)

    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--policy-file",
            str(policy_path),
            "--receipt-file",
            str(receipt_path),
            "--pools-file",
            str(pools_path),
            "--signal-source-registry-file",
            str(registry_path),
            "--current-epoch",
            "5",
            "--intent-deadline",
            "99",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["ok"] is False
    assert report["decision"]["reason"] == "signal_source_registry_load_rejected"
    assert (
        "signal source registry payload rejected: "
        "external signal source registry payload mismatch"
    ) in report["decision"]["explain"][-1]
    assert report["signal_source_registry_contract"]["ok"] is False
    assert report["signal_source_registry_contract"]["source_kind"] == "signal_source_registry_file"


def test_autotrader_shadow_cli_rejects_invalid_external_signal_file(tmp_path: Path) -> None:
    policy_path, pools_path, receipt_path = _policy_and_market(tmp_path)
    external_signals_path = tmp_path / "bad_external_signals.json"
    external_signals_path.write_text(
        json.dumps(
            [
                {
                    "signal_id": "sig.bad.1",
                    "source_id": "feed.bad.alpha",
                    "source_kind": "advisory_external",
                    "trust_tier": "attested",
                    "freshness_ok": True,
                    "auth_ok": True,
                    "advisory_only": True,
                }
            ]
        ),
        encoding="utf-8",
    )

    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--policy-file",
            str(policy_path),
            "--receipt-file",
            str(receipt_path),
            "--pools-file",
            str(pools_path),
            "--external-signals-file",
            str(external_signals_path),
            "--current-epoch",
            "5",
            "--intent-deadline",
            "99",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["ok"] is False
    assert report["decision"]["reason"] == "external_signals_load_rejected"
    assert "external signal contract rejected: advisory_external_invalid" in report["decision"]["explain"][-1]
    assert report["external_signals_contract"]["ok"] is False
    assert report["external_signals_contract"]["source_kind"] == "external_signals_file"


def test_autotrader_shadow_cli_marks_multiaction_frontier_ambiguous_when_strategy_has_multiple_actions(
    tmp_path: Path,
) -> None:
    _, pools_path, receipt_path = _policy_and_market(tmp_path)
    candidate_path = tmp_path / "candidate.json"
    candidate = _candidate()
    candidate["allowed_actions"] = ["swap_exact_in", "order_intent"]
    candidate_path.write_text(json.dumps(candidate, indent=2, sort_keys=True), encoding="utf-8")

    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--candidate-file",
            str(candidate_path),
            "--receipt-file",
            str(receipt_path),
            "--pools-file",
            str(pools_path),
            "--current-epoch",
            "5",
            "--intent-deadline",
            "99",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["decision"]["tag"] == "submit"
    assert report["bounded_multiaction_candidate_set"] is None
    assert report["bounded_multiaction_candidate_set_contract"]["ok"] is None
    assert report["bounded_multiaction_candidate_set_contract"]["frontier_unambiguous"] is False
    assert report["bounded_multiaction_candidate_set_contract"]["error"] == "multi_action_frontier_ambiguous"
    assert report["bounded_multiaction_decision_certificate"] is None
    assert report["bounded_multiaction_decision_contract"]["ok"] is None
    assert report["bounded_multiaction_decision_contract"]["frontier_unambiguous"] is False
    assert report["bounded_multiaction_decision_contract"]["error"] == "multi_action_frontier_ambiguous"
    assert report["decision_witness"]["schema"] == "zenodex/decision-witness/v1"
    assert report["decision_witness"]["witness_kind"] == "autotrader_binary_decision"
    assert report["decision_witness_contract"]["ok"] is True
    assert report["bounded_multiaction_decision_witness"] is None
    assert report["bounded_multiaction_decision_witness_contract"]["ok"] is None
    assert report["bounded_multiaction_decision_witness_contract"]["frontier_unambiguous"] is False
    assert (
        report["bounded_multiaction_decision_witness_contract"]["error"]
        == "multi_action_frontier_ambiguous"
    )
    assert report["bounded_multiaction_tau_argmax_contract"]["ok"] is None
    assert report["bounded_multiaction_tau_argmax_contract"]["error"] == "multi_action_frontier_ambiguous"
    assert report["bounded_multiaction_tau_argmax_contract"]["tau_enabled"] is False
    assert report["bounded_multiaction_tau_argmax_contract"]["tau_used"] is False
    assert report["bounded_multiaction_tau_argmax_contract"]["frontier_unambiguous"] is False


def test_autotrader_shadow_cli_accepts_krr_bundle_file(tmp_path: Path) -> None:
    policy_path, pools_path, receipt_path = _policy_and_market(tmp_path)
    bundle_path = _write_krr_bundle(tmp_path)

    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--policy-file",
            str(policy_path),
            "--receipt-file",
            str(receipt_path),
            "--pools-file",
            str(pools_path),
            "--krr-bundle-file",
            str(bundle_path),
            "--current-epoch",
            "5",
            "--intent-deadline",
            "99",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["krr_bundle"]["schema"] == "zenodex/autotrader-krr-bundle/v1"
    assert report["krr_bundle_contract"] == {"ok": True, "error": None}
    assert report["history_check_stats_contract"] == {"ok": None, "error": None}
    assert len(report["external_signals"]) == 1
    assert report["signal_source_registry"]["entry_count"] == 1
    assert report["krr_advice"] is not None
    assert report["krr_advice"]["backend_used"] == "python"


def test_autotrader_shadow_cli_rejects_mixed_krr_bundle_and_raw_signal_inputs(tmp_path: Path) -> None:
    policy_path, pools_path, receipt_path = _policy_and_market(tmp_path)
    bundle_path = _write_krr_bundle(tmp_path)
    external_signals_path = tmp_path / "external_signals.json"
    external_signals_path.write_text(
        json.dumps(
            {
                "external_signals": [
                    {
                        "signal_id": "sig.news.override",
                        "source_id": "feed.news.alpha",
                        "source_kind": "advisory_external",
                        "trust_tier": "advisory",
                        "freshness_ok": True,
                        "auth_ok": False,
                        "advisory_only": True,
                    }
                ]
            }
        ),
        encoding="utf-8",
    )

    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--policy-file",
            str(policy_path),
            "--receipt-file",
            str(receipt_path),
            "--pools-file",
            str(pools_path),
            "--krr-bundle-file",
            str(bundle_path),
            "--external-signals-file",
            str(external_signals_path),
            "--current-epoch",
            "5",
            "--intent-deadline",
            "99",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 1
    report = json.loads(proc.stderr)
    assert report["ok"] is False
    assert "cannot be combined with raw KRR KB, signal, registry, or history inputs" in report["error"]


def test_autotrader_shadow_cli_candidate_tau_fail_closed(tmp_path: Path) -> None:
    _, pools_path, receipt_path = _policy_and_market(tmp_path)
    candidate_path = tmp_path / "candidate.json"
    candidate_path.write_text(json.dumps(_candidate(backend="tau"), indent=2), encoding="utf-8")

    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--candidate-file",
            str(candidate_path),
            "--receipt-file",
            str(receipt_path),
            "--pools-file",
            str(pools_path),
            "--current-epoch",
            "5",
            "--intent-deadline",
            "99",
            "--krr-backend",
            "off",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["decision"]["tag"] == "reject"
    assert report["decision"]["reason"] == "tau_policy_backend_requires_enabled_tau_config"
    assert report["krr_advice"] is None


def test_autotrader_shadow_cli_policy_text_inline_roundtrip(tmp_path: Path) -> None:
    _, pools_path, receipt_path = _policy_and_market(tmp_path)

    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--policy-text",
            "dca 100 A into B every 4 epochs until epoch 20",
            "--owner-pubkey",
            "owner.pubkey.1",
            "--receipt-file",
            str(receipt_path),
            "--pools-file",
            str(pools_path),
            "--current-epoch",
            "5",
            "--intent-deadline",
            "99",
            "--krr-backend",
            "off",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["strategy"]["template"] == "dca"
    assert report["decision"]["tag"] == "submit"
    assert report["krr_advice"] is None


def test_autotrader_shadow_cli_policy_text_file_requires_owner(tmp_path: Path) -> None:
    _, pools_path, receipt_path = _policy_and_market(tmp_path)
    text_path = tmp_path / "policy.txt"
    text_path.write_text("dca 100 A into B every 4 epochs until epoch 20", encoding="utf-8")

    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--policy-text-file",
            str(text_path),
            "--receipt-file",
            str(receipt_path),
            "--pools-file",
            str(pools_path),
            "--current-epoch",
            "5",
            "--intent-deadline",
            "99",
            "--krr-backend",
            "off",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["ok"] is False
    assert report["decision"]["reason"] == "strategy_source_load_rejected"
    assert "owner_pubkey contains unsupported characters" in report["decision"]["explain"][-1]
    assert report["strategy_source_contract"]["ok"] is False
    assert report["strategy_source_contract"]["source_kind"] == "policy_text_file"


def test_autotrader_shadow_cli_bad_pools_file_fails(tmp_path: Path) -> None:
    policy_path, _, receipt_path = _policy_and_market(tmp_path)
    bad_pools_path = tmp_path / "bad_pools.json"
    bad_pools_path.write_text(json.dumps({"pools": "bad"}), encoding="utf-8")

    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--policy-file",
            str(policy_path),
            "--receipt-file",
            str(receipt_path),
            "--pools-file",
            str(bad_pools_path),
            "--current-epoch",
            "5",
            "--intent-deadline",
            "99",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["ok"] is False
    assert report["decision"]["reason"] == "pools_file_load_rejected"
    assert "pools file must be a map of pool_id -> pool object or a list of pool objects" in report["decision"]["explain"][-1]
    assert report["pools_file_contract"]["ok"] is False
    assert report["pools_file_contract"]["source_kind"] == "pools_file"


def test_autotrader_shadow_cli_rejects_bad_candidate_file_structurally(tmp_path: Path) -> None:
    _, pools_path, receipt_path = _policy_and_market(tmp_path)
    candidate_path = tmp_path / "bad_candidate.json"
    candidate_path.write_text(json.dumps(["bad"]), encoding="utf-8")

    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--candidate-file",
            str(candidate_path),
            "--receipt-file",
            str(receipt_path),
            "--pools-file",
            str(pools_path),
            "--current-epoch",
            "5",
            "--intent-deadline",
            "99",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["ok"] is False
    assert report["decision"]["reason"] == "strategy_source_load_rejected"
    assert "candidate file must be an object" in report["decision"]["explain"][-1]
    assert report["strategy_source_contract"]["ok"] is False
    assert report["strategy_source_contract"]["source_kind"] == "candidate_file"


def test_autotrader_shadow_cli_rejects_bad_policy_file_structurally(tmp_path: Path) -> None:
    _, pools_path, receipt_path = _policy_and_market(tmp_path)
    policy_path = tmp_path / "bad_policy.json"
    policy_path.write_text(json.dumps({"schema": "wrong"}), encoding="utf-8")

    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--policy-file",
            str(policy_path),
            "--receipt-file",
            str(receipt_path),
            "--pools-file",
            str(pools_path),
            "--current-epoch",
            "5",
            "--intent-deadline",
            "99",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["ok"] is False
    assert report["decision"]["reason"] == "strategy_source_load_rejected"
    assert "unsupported local policy schema" in report["decision"]["explain"][-1]
    assert report["strategy_source_contract"]["ok"] is False
    assert report["strategy_source_contract"]["source_kind"] == "policy_file"


def test_autotrader_shadow_cli_bad_receipt_file_fails_structurally(tmp_path: Path) -> None:
    policy_path, pools_path, _ = _policy_and_market(tmp_path)
    bad_receipt_path = tmp_path / "bad_receipt.json"
    bad_receipt_path.write_text(json.dumps(["bad"]), encoding="utf-8")

    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--policy-file",
            str(policy_path),
            "--receipt-file",
            str(bad_receipt_path),
            "--pools-file",
            str(pools_path),
            "--current-epoch",
            "5",
            "--intent-deadline",
            "99",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["ok"] is False
    assert report["decision"]["reason"] == "receipt_file_load_rejected"
    assert "receipt file must be a JSON object" in report["decision"]["explain"][-1]
    assert report["receipt_file_contract"]["ok"] is False
    assert report["receipt_file_contract"]["source_kind"] == "receipt_file"


def test_autotrader_shadow_cli_bad_controller_state_file_fails_structurally(tmp_path: Path) -> None:
    policy_path, pools_path, receipt_path = _policy_and_market(tmp_path)
    controller_path = tmp_path / "bad_controller_state.json"
    controller_path.write_text(json.dumps({"controller_state": "bad"}), encoding="utf-8")

    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--policy-file",
            str(policy_path),
            "--receipt-file",
            str(receipt_path),
            "--pools-file",
            str(pools_path),
            "--controller-state-file",
            str(controller_path),
            "--current-epoch",
            "5",
            "--intent-deadline",
            "99",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["ok"] is False
    assert report["decision"]["reason"] == "controller_state_load_rejected"
    assert "controller_state must be an object" in report["decision"]["explain"][-1]
    assert report["controller_state_contract"]["ok"] is False
    assert report["controller_state_contract"]["source_kind"] == "controller_state_file"


def test_autotrader_shadow_cli_degrades_on_krr_bundle_hash_mismatch(tmp_path: Path) -> None:
    policy_path, pools_path, receipt_path = _policy_and_market(tmp_path)
    bundle_path = _write_krr_bundle(tmp_path)
    payload = json.loads(bundle_path.read_text(encoding="utf-8"))
    payload["bundle_hash"] = "0x" + ("de" * 32)
    bundle_path.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")

    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--policy-file",
            str(policy_path),
            "--receipt-file",
            str(receipt_path),
            "--pools-file",
            str(pools_path),
            "--krr-bundle-file",
            str(bundle_path),
            "--current-epoch",
            "5",
            "--intent-deadline",
            "99",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["decision"]["tag"] == "submit"
    assert report["krr_bundle"] is None
    assert report["krr_bundle_contract"]["ok"] is False
    assert "bundle hash mismatch" in report["krr_bundle_contract"]["error"]
    assert report["krr_advice"] is None
    assert report["krr_advice_error"] is None


def test_autotrader_shadow_cli_degrades_on_bad_history_check_stats_file(tmp_path: Path) -> None:
    policy_path, pools_path, receipt_path = _policy_and_market(tmp_path)
    history_path = tmp_path / "bad_history.json"
    history_path.write_text(json.dumps(["bad"]), encoding="utf-8")

    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--policy-file",
            str(policy_path),
            "--receipt-file",
            str(receipt_path),
            "--pools-file",
            str(pools_path),
            "--history-check-stats-file",
            str(history_path),
            "--current-epoch",
            "5",
            "--intent-deadline",
            "99",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["decision"]["tag"] == "submit"
    assert report["history_check_stats_contract"]["ok"] is False
    assert "history check stats file must be a JSON object" in report["history_check_stats_contract"]["error"]
    assert report["krr_advice"] is not None
