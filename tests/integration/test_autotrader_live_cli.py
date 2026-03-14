from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import src.integration.autotrader_live as autotrader_live
import tools.autotrader_live as autotrader_live_cli
from src.agents.krr_bundle_artifacts import (
    KRRReviewRecord,
    KRRSourceSnapshot,
    build_autotrader_krr_bundle,
    sign_autotrader_krr_bundle,
)
from src.agents.local_policy import dump_local_policy_document
from src.agents.policy_compiler import compile_policy_candidate
from src.agents.strategy_ir import StrategyAction
from src.agents.tau_policy_adapter import TauPolicyReceipt
from src.core.quote_receipts import make_route_quote_receipt
from src.core.routing import best_route_exact_in_2hop
from src.integration.autotrader_controller import (
    AutoTraderControllerState,
    AutoTraderDecision,
    AutoTraderDecisionTag,
)
from src.integration.autotrader_live import AutoTraderLiveReport
from src.integration.autotrader_signals import AutoTraderSessionState, AutoTraderWalletCapability
from src.integration.tau_net_client import bls_pubkey_hex_from_privkey
from src.state.canonical import sha256_hex
from src.state.pools import PoolState, PoolStatus

REPO_ROOT = Path(__file__).resolve().parents[2]
CLI_PATH = REPO_ROOT / "tools" / "autotrader_live.py"


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


def _candidate(*, owner_pubkey: str, fixed_order_size: int = 100) -> dict[str, object]:
    return {
        "strategy_id": "dca.live.cli",
        "owner_pubkey": owner_pubkey,
        "policy_backend": "local",
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


def _policy_and_market(tmp_path: Path, *, owner_pubkey: str) -> tuple[Path, Path, Path]:
    strategy = compile_policy_candidate(_candidate(owner_pubkey=owner_pubkey)).strategy
    pools = {"p_ab": _pool("p_ab", "A", "B", 1_000, 2_000, 10)}
    quote = best_route_exact_in_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_in=100)
    assert quote is not None
    receipt = make_route_quote_receipt(kind="exact_in", quote=quote, pools_by_id=pools, quote_epoch=5)

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
                "entries": [
                    {
                        "source_id": "feed.news.alpha",
                        "source_kind": "advisory_external",
                        "allowed_trust_tiers": ["advisory"],
                        "require_advisory_only": True,
                    },
                    {
                        "source_id": "oracle.alpha",
                        "source_kind": "attested_external",
                        "allowed_trust_tiers": ["attested", "verified"],
                        "require_auth": True,
                        "require_freshness": True,
                    },
                ]
            },
            indent=2,
            sort_keys=True,
        ),
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
        bundle_name="bundle.live.cli",
        built_at="2026-03-12T00:15:00Z",
        compiler_version="bundle_builder_v1",
        policy_version="policy_v1",
        runtime_krr_kb={
            "operator_priors": {},
            "semantic_rules": [],
            "check_priors": {"live::nonce_guard": {"base_weight": 1.5}},
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
                review_id="bundle.live.cli.review",
                target_kind="bundle",
                target_id="bundle.live.cli",
                decision="approve",
                reviewer="security.review",
                reviewed_at="2026-03-12T00:10:00Z",
                rationale="live bundle approved",
                approved_for_runtime=True,
                provenance_ok=True,
            ),
        ),
    )
    signed = sign_autotrader_krr_bundle(bundle, privkey=21)
    bundle_path = tmp_path / "krr_bundle.json"
    bundle_path.write_text(json.dumps(signed.to_dict(), indent=2, sort_keys=True), encoding="utf-8")
    return bundle_path


def test_autotrader_live_cli_policy_file_roundtrip(tmp_path: Path) -> None:
    privkey = 21
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    policy_path, pools_path, receipt_path = _policy_and_market(tmp_path, owner_pubkey=owner_pubkey)
    telemetry_path = tmp_path / "live_report.json"
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
                    },
                    {
                        "signal_id": "sig.oracle.1",
                        "source_id": "oracle.alpha",
                        "source_kind": "attested_external",
                        "trust_tier": "verified",
                        "freshness_ok": True,
                        "auth_ok": True,
                        "advisory_only": False,
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
            "--last-used-nonce",
            "0",
            "--signer-privkey",
            str(privkey),
            "--krr-backend",
            "python",
            "--chain-id",
            "tau-local",
            "--tx-sequence-number",
            "7",
            "--tx-expiration-time",
            "999",
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
    assert len(report["external_signals"]) == 2
    assert report["signal_source_registry"]["entry_count"] == 2
    assert report["observation_packet"]["external_signals"][1]["trust_tier"] == "verified"
    assert report["observation_packet"]["signal_source_registry_present"] is True
    assert report["tau_policy_bundle"]["schema"] == "zenodex/strategy-policy-bundle/v1"
    assert report["policy_artifact"]["schema"] == "zenodex/strategy-policy-artifact/v1"
    assert report["policy_artifact_contract"]["ok"] is True
    assert report["tau_policy_bundle_contract"]["ok"] is True
    assert report["candidate_set"]["schema"] == "zenodex/strategy-candidate-set/v1"
    assert report["candidate_set_contract"]["ok"] is True
    assert report["decision_certificate"]["schema"] == "zenodex/strategy-decision/v1"
    assert report["decision_contract"]["ok"] is True
    assert report["kill_switch"]["ok"] is True
    assert report["live_admission"]["ok"] is True
    assert report["live_admission"]["error"] is None
    assert report["system_compose"]["ok"] is True
    assert report["system_compose"]["error"] is None
    assert report["submit_bundle"]["ok"] is True
    assert report["submit_bundle"]["error"] is None
    assert report["emit_finalize"]["ok"] is True
    assert report["emit_finalize"]["error"] is None
    assert report["decision"]["guard_state"] == {
        "signal_provenance_ok": True,
        "route_economic_sanity_ok": True,
        "execution_ok": True,
        "oracle_freshness_ok": True,
        "budget_ok": True,
    }
    assert report["krr_advice"] is not None
    assert "live::signer_match" in report["krr_advice"]["preferred_checks"]
    assert "live::nonce_guard" in report["krr_advice"]["preferred_checks"]
    assert "signal::external_advisory_separation" in report["krr_advice"]["candidate_checks"]
    assert "signal::external_attestation" in report["krr_advice"]["candidate_checks"]
    assert "signal::source_registry" in report["krr_advice"]["candidate_checks"]
    assert "quote::route_economic_sanity" in report["krr_advice"]["candidate_checks"]
    assert report["krr_advice"]["observation_summary"]["external_signal_count"] == 2
    assert report["krr_advice"]["observation_summary"]["source_registry_present"] is True
    assert report["krr_advice"]["route_risk_summary"]["route_shape_supported_for_intents"] is True
    assert report["signing"]["last_used_nonce_after"] == 1
    assert report["wallet_capability"]["notional_remaining"] == 1000
    assert report["session_state"]["session_id"] == "dca.live.cli.session"
    assert report["operations"]["2"][0]["signature"].startswith("0x")
    assert report["tau_tx_payload"]["sequence_number"] == 7
    assert report["tx_envelope_tau_receipt"] is None
    assert report["live_admission_tau_receipt"] is None
    assert report["system_compose_tau_receipt"] is None
    persisted = json.loads(telemetry_path.read_text(encoding="utf-8"))
    assert persisted["signing"]["signer_pubkey"] == owner_pubkey


def test_live_report_to_dict_includes_new_tau_receipts() -> None:
    strategy_receipt = TauPolicyReceipt(
        strategy_id="strat.live.1",
        strategy_hash="0xabc",
        spec_id="autotrader_system_compose_v1",
        gate_output="o3",
        steps=({"i1": 1},),
        expected_ok=True,
    )
    decision = AutoTraderDecision(
        tag=AutoTraderDecisionTag.SUBMIT,
        reason="ok",
        explain=("ok",),
        state=AutoTraderControllerState(),
    )
    wallet_capability = AutoTraderWalletCapability(
        session_id="session.1",
        owner_pubkey="0xowner",
        chain_id="tau-local",
        valid_from_epoch=1,
        valid_until_epoch=10,
        notional_remaining=100,
        allowed_assets=("A", "B"),
        allowed_actions=(StrategyAction.PLACE_SWAP_EXACT_IN,),
        enabled=True,
    )
    report = AutoTraderLiveReport(
        decision=decision,
        signer_pubkey="0xsigner",
        chain_id="tau-local",
        last_used_nonce_before=0,
        last_used_nonce_after=1,
        wallet_capability=wallet_capability,
        session_state=AutoTraderSessionState(
            session_id="session.1",
            owner_pubkey="0xowner",
            chain_id="tau-local",
        ),
        session_state_tau_receipt=strategy_receipt,
        external_signal_source_registry_tau_receipts=(
            autotrader_live.AutoTraderExternalSignalSourceRegistryTauReceipt(
                spec_id="autotrader_external_signal_source_registry_guard_v1",
                gate_output="o8",
                signal_id="sig.oracle.1",
                source_id="oracle.alpha",
                steps=({"i1": 1},),
                expected_ok=True,
            ),
        ),
        live_admission_tau_receipt=strategy_receipt,
        system_compose_tau_receipt=strategy_receipt,
        submit_bundle_tau_receipt=strategy_receipt,
        emit_finalize_tau_receipt=strategy_receipt,
    )

    payload = autotrader_live_cli._live_report_to_dict(report)

    assert payload["live_admission_tau_receipt"]["spec_id"] == "autotrader_system_compose_v1"
    assert payload["system_compose_tau_receipt"]["gate_output"] == "o3"
    assert payload["submit_bundle_tau_receipt"]["spec_id"] == "autotrader_system_compose_v1"
    assert payload["emit_finalize_tau_receipt"]["spec_id"] == "autotrader_system_compose_v1"
    assert payload["session_state"]["session_id"] == "session.1"
    assert payload["session_state_tau_receipt"]["spec_id"] == "autotrader_system_compose_v1"
    assert payload["external_signal_source_registry_tau_receipts"][0]["signal_id"] == "sig.oracle.1"


def test_autotrader_live_cli_rejects_invalid_external_signal_file(tmp_path: Path) -> None:
    privkey = 32
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    policy_path, pools_path, receipt_path = _policy_and_market(tmp_path, owner_pubkey=owner_pubkey)
    external_signals_path = tmp_path / "bad_external_signals.json"
    external_signals_path.write_text(
        json.dumps(
            [
                {
                    "signal_id": "sig.bad.1",
                    "source_id": "feed.bad.alpha",
                    "source_kind": "attested_external",
                    "trust_tier": "advisory",
                    "freshness_ok": True,
                    "auth_ok": True,
                    "advisory_only": False,
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
            "--last-used-nonce",
            "0",
            "--signer-privkey",
            str(privkey),
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 1
    report = json.loads(proc.stderr)
    assert report["ok"] is False
    assert "external signal contract rejected: attested_external_invalid" in report["error"]


def test_autotrader_live_cli_accepts_krr_bundle_file(tmp_path: Path) -> None:
    privkey = 21
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    policy_path, pools_path, receipt_path = _policy_and_market(tmp_path, owner_pubkey=owner_pubkey)
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
            "--last-used-nonce",
            "0",
            "--signer-privkey",
            str(privkey),
            "--krr-backend",
            "python",
            "--chain-id",
            "tau-local",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["krr_bundle"]["schema"] == "zenodex/autotrader-krr-bundle/v1"
    assert len(report["external_signals"]) == 1
    assert report["signal_source_registry"]["entry_count"] == 1
    assert report["krr_advice"] is not None
    assert report["krr_advice"]["backend_used"] == "python"


def test_autotrader_live_cli_rejects_mixed_krr_bundle_and_raw_signal_inputs(tmp_path: Path) -> None:
    privkey = 21
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    policy_path, pools_path, receipt_path = _policy_and_market(tmp_path, owner_pubkey=owner_pubkey)
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
            "--last-used-nonce",
            "0",
            "--signer-privkey",
            str(privkey),
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 1
    report = json.loads(proc.stderr)
    assert "cannot be combined with raw KRR KB, signal, registry, or history inputs" in report["error"]


def test_autotrader_live_cli_accepts_explicit_wallet_capability_file(tmp_path: Path) -> None:
    privkey = 31
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    policy_path, pools_path, receipt_path = _policy_and_market(tmp_path, owner_pubkey=owner_pubkey)
    capability_path = tmp_path / "wallet_capability.json"
    capability_path.write_text(
        json.dumps(
            {
                "session_id": "session.cli.1",
                "owner_pubkey": owner_pubkey,
                "chain_id": "tau-local",
                "valid_from_epoch": 1,
                "valid_until_epoch": 100,
                "notional_remaining": 500,
                "allowed_assets": ["A", "B"],
                "allowed_actions": ["place_swap_exact_in"],
                "enabled": True,
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
            "--wallet-capability-file",
            str(capability_path),
            "--current-epoch",
            "5",
            "--intent-deadline",
            "99",
            "--last-used-nonce",
            "0",
            "--signer-privkey",
            str(privkey),
            "--chain-id",
            "tau-local",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["decision"]["tag"] == "submit"
    assert report["live_admission"]["ok"] is True
    assert report["system_compose"]["ok"] is True
    assert report["system_compose"]["error"] is None
    assert report["wallet_capability"]["session_id"] == "session.cli.1"
    assert report["session_state"]["session_id"] == "session.cli.1"


def test_autotrader_live_cli_accepts_explicit_session_state_file(tmp_path: Path) -> None:
    privkey = 41
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    policy_path, pools_path, receipt_path = _policy_and_market(tmp_path, owner_pubkey=owner_pubkey)
    capability_path = tmp_path / "wallet_capability.json"
    session_state_path = tmp_path / "session_state.json"
    capability_path.write_text(
        json.dumps(
            {
                "session_id": "session.cli.2",
                "owner_pubkey": owner_pubkey,
                "chain_id": "tau-local",
                "valid_from_epoch": 1,
                "valid_until_epoch": 100,
                "notional_remaining": 500,
                "allowed_assets": ["A", "B"],
                "allowed_actions": ["place_swap_exact_in"],
                "enabled": True,
            },
            indent=2,
            sort_keys=True,
        ),
        encoding="utf-8",
    )
    session_state_path.write_text(
        json.dumps(
            {
                "session_id": "session.cli.2",
                "owner_pubkey": owner_pubkey,
                "chain_id": "tau-local",
                "enabled": True,
                "revoked_at_epoch": None,
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
            "--wallet-capability-file",
            str(capability_path),
            "--session-state-file",
            str(session_state_path),
            "--current-epoch",
            "5",
            "--intent-deadline",
            "99",
            "--last-used-nonce",
            "0",
            "--signer-privkey",
            str(privkey),
            "--chain-id",
            "tau-local",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["decision"]["tag"] == "submit"
    assert report["session_state"]["session_id"] == "session.cli.2"


def test_autotrader_live_cli_rejects_bad_session_state_file(tmp_path: Path) -> None:
    privkey = 42
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    policy_path, pools_path, receipt_path = _policy_and_market(tmp_path, owner_pubkey=owner_pubkey)
    session_state_path = tmp_path / "bad_session_state.json"
    session_state_path.write_text(json.dumps({"session_state": "bad"}), encoding="utf-8")

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
            "--session-state-file",
            str(session_state_path),
            "--current-epoch",
            "5",
            "--intent-deadline",
            "99",
            "--last-used-nonce",
            "0",
            "--signer-privkey",
            str(privkey),
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 1
    report = json.loads(proc.stderr)
    assert report["ok"] is False
    assert "session_state must be an object" in report["error"]


def test_autotrader_live_cli_rejects_signer_mismatch(tmp_path: Path) -> None:
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(22)
    policy_path, pools_path, receipt_path = _policy_and_market(tmp_path, owner_pubkey=owner_pubkey)

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
            "--last-used-nonce",
            "0",
            "--signer-privkey",
            "23",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["decision"]["tag"] == "reject"
    assert report["decision"]["reason"] == "signer_pubkey_mismatch"
    assert report["live_admission"]["ok"] is False
    assert report["live_admission"]["error"] == "signer_pubkey_mismatch"
    assert report["system_compose"]["ok"] is False
    assert report["system_compose"]["error"] == "signer_binding_rejected"
    assert report["krr_advice"] is None


def test_autotrader_live_cli_bad_pools_file_fails(tmp_path: Path) -> None:
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(24)
    policy_path, _, receipt_path = _policy_and_market(tmp_path, owner_pubkey=owner_pubkey)
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
            "--last-used-nonce",
            "0",
            "--signer-privkey",
            "24",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 1
    report = json.loads(proc.stderr)
    assert report["ok"] is False
    assert "pools file must be a map" in report["error"]
