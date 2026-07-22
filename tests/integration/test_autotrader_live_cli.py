from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import src.integration.autotrader_live as autotrader_live
import tools.autotrader_live as autotrader_live_cli
from src.agents.autotrader_client_policy_bundle import (
    build_autotrader_client_policy_bundle,
    sign_autotrader_client_policy_bundle,
)
from src.agents.autotrader_client_policy_surface import build_autotrader_client_policy_surface
from src.agents.autotrader_user_rule_bundle import (
    AutoTraderUserMarket,
    AutoTraderUserRulePreset,
    build_autotrader_user_rule_bundle_from_preset,
)
from src.agents.krr_bundle_artifacts import (
    KRRReviewRecord,
    KRRSourceSnapshot,
    build_autotrader_krr_bundle,
    sign_autotrader_krr_bundle,
)
from src.agents.local_policy import dump_local_policy_document
from src.agents.policy_compiler import compile_policy_candidate
from src.agents.strategy_ir import PolicyBackend, StrategyAction
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
from src.state.immutable_json import snapshot_json_mapping
from src.state.pools import PoolState, PoolStatus

REPO_ROOT = Path(__file__).resolve().parents[2]
CLI_PATH = REPO_ROOT / "tools" / "autotrader_live.py"
_LIVE_ACK_ARGS = ("--acknowledge-experimental-live-risk",)


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


def _write_client_policy_bundle(
    tmp_path: Path,
    *,
    owner_pubkey: str,
    privkey: int,
    fixed_order_size: int = 100,
) -> Path:
    strategy = compile_policy_candidate(
        _candidate(owner_pubkey=owner_pubkey, fixed_order_size=fixed_order_size)
    ).strategy
    surface = build_autotrader_client_policy_surface(strategy=strategy)
    bundle = build_autotrader_client_policy_bundle(
        bundle_name=f"{strategy.strategy_id}.bundle",
        built_at="2026-04-09T12:00:00Z",
        client_policy_surface=surface,
    )
    signed = sign_autotrader_client_policy_bundle(bundle, privkey=privkey)
    bundle_path = tmp_path / "client_policy_bundle.json"
    bundle_path.write_text(json.dumps(signed.to_dict(), indent=2, sort_keys=True), encoding="utf-8")
    return bundle_path


def _write_policy_artifact_and_tau_policy_bundle(
    tmp_path: Path,
    *,
    owner_pubkey: str,
    privkey: int,
) -> tuple[Path, Path]:
    strategy = compile_policy_candidate(_candidate(owner_pubkey=owner_pubkey)).strategy
    tau_policy_bundle = autotrader_live.build_tau_policy_bundle(
        strategy=strategy,
        compile_contract_tau_receipt=autotrader_live.build_compile_contract_tau_policy_receipt(
            strategy=strategy
        ).to_dict(),
    )
    policy_artifact = autotrader_live.sign_strategy_policy_artifact(
        autotrader_live.build_strategy_policy_artifact(
            strategy=strategy,
            tau_policy_bundle=tau_policy_bundle,
        ),
        privkey=privkey,
    )
    tau_path = tmp_path / "tau_policy_bundle.json"
    tau_path.write_text(
        json.dumps(tau_policy_bundle.to_dict(), indent=2, sort_keys=True),
        encoding="utf-8",
    )
    artifact_path = tmp_path / "policy_artifact.json"
    artifact_path.write_text(
        json.dumps(policy_artifact.to_dict(), indent=2, sort_keys=True),
        encoding="utf-8",
    )
    return artifact_path, tau_path


def _write_user_rule_bundle(
    tmp_path: Path,
    *,
    owner_pubkey: str,
    preset_id: AutoTraderUserRulePreset = AutoTraderUserRulePreset.CONSERVATIVE_DCA,
) -> Path:
    bundle = build_autotrader_user_rule_bundle_from_preset(
        bundle_name=f"{preset_id.value}.bundle",
        built_at="2026-04-09T12:00:00Z",
        strategy_id=f"strategy.{preset_id.value}",
        owner_pubkey=owner_pubkey,
        policy_backend=PolicyBackend.LOCAL,
        preset_id=preset_id,
        market=AutoTraderUserMarket(asset_in="A", asset_out="B"),
        fixed_order_size=100,
        cadence_epochs=4,
        valid_from_epoch=1,
        valid_until_epoch=100,
    )
    bundle_path = tmp_path / "user_rule_bundle.json"
    bundle_path.write_text(json.dumps(bundle.to_dict(), indent=2, sort_keys=True), encoding="utf-8")
    return bundle_path


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
    client_policy_bundle_path = _write_client_policy_bundle(
        tmp_path,
        owner_pubkey=owner_pubkey,
        privkey=privkey,
    )
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
            *_LIVE_ACK_ARGS,
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
            "--client-policy-bundle-file",
            str(client_policy_bundle_path),
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
    assert report["client_policy_bundle"]["schema"] == "zenodex/autotrader-client-policy-bundle/v1"
    assert report["client_policy_bundle_contract"]["ok"] is True
    assert report["client_policy_bundle_contract"]["error"] is None
    assert report["client_policy_bundle_contract"]["signature_ok"] is True
    assert report["client_policy_bundle_hash"] == report["client_policy_bundle"]["client_policy_bundle_hash"]
    assert report["client_policy_surface_hash"] == report["client_policy_bundle"]["client_policy_surface_hash"]
    assert report["local_guard_evaluation"]["ok"] is True
    assert report["local_guard_evaluation"]["blocking_families"] == []
    assert report["candidate_set"]["schema"] == "zenodex/strategy-candidate-set/v1"
    assert report["candidate_set_contract"]["ok"] is True
    assert report["decision_certificate"]["schema"] == "zenodex/strategy-decision/v1"
    assert report["decision_contract"]["ok"] is True
    assert report["bounded_multiaction_candidate_set"]["schema"] == "zenodex/strategy-multi-action-candidate-set/v1"
    assert report["bounded_multiaction_candidate_set_contract"]["ok"] is True
    assert report["bounded_multiaction_candidate_set_contract"]["error"] is None
    assert report["bounded_multiaction_candidate_set_contract"]["frontier_unambiguous"] is True
    assert report["bounded_multiaction_decision_certificate"]["schema"] == "zenodex/strategy-multi-action-decision/v1"
    assert report["bounded_multiaction_decision_witness"]["schema"] == "zenodex/decision-witness/v1"
    assert report["bounded_multiaction_decision_witness"]["witness_kind"] == "autotrader_multiaction_decision"
    assert report["bounded_multiaction_decision_contract"]["ok"] is True
    assert report["bounded_multiaction_decision_contract"]["frontier_unambiguous"] is True
    assert report["bounded_multiaction_decision_witness_contract"]["ok"] is True
    assert report["bounded_multiaction_decision_witness_contract"]["frontier_unambiguous"] is True
    assert report["bounded_multiaction_tau_argmax_contract"]["ok"] is None
    assert report["bounded_multiaction_tau_argmax_contract"]["error"] == "tau_disabled"
    assert report["bounded_multiaction_tau_argmax_contract"]["tau_enabled"] is False
    assert report["bounded_multiaction_tau_argmax_contract"]["tau_used"] is False
    assert report["bounded_multiaction_tau_argmax_contract"]["frontier_unambiguous"] is True
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
    assert report["krr_explanation"] is not None
    assert report["user_rule_summary"] is not None
    assert report["actionability_explanation"] is not None
    assert report["user_rule_summary"]["source_form"] == "compiled_strategy_ir"
    assert report["user_rule_summary"]["overall_support_status"] == "supported"
    assert report["user_rule_summary"]["surface_support_matrix"]["live"]["supported"] is True
    assert report["user_rule_summary"]["intent"]["asset_pair"] == "A/B"
    assert report["krr_explanation"]["authoring_posture"]["source_form"] == "compiled_strategy_ir"
    assert report["krr_explanation"]["trust_posture"]["primary_trust_tier"] == "verified"
    assert report["actionability_explanation"]["actionability"]["actionable"] is True
    assert report["actionability_explanation"]["authoring"]["overall_support_status"] == "supported"
    assert report["actionability_explanation"]["authoring"]["surface_support_matrix"]["shadow"]["supported"] is True
    assert report["actionability_explanation"]["intent"]["asset_pair"] == "A/B"
    assert report["actionability_explanation"]["trust_posture"]["primary_trust_tier"] == "verified"
    assert report["actionability_summary"]["headline"] == "Actionable: submit because ok."
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
    assert report["risk_disclosure"]["advanced_feature"] is True
    assert report["risk_disclosure"]["experimental"] is True
    assert report["risk_disclosure"]["requires_explicit_acknowledgement"] is True
    assert report["risk_disclosure"]["user_acknowledged"] is True


def test_autotrader_live_cli_user_rule_bundle_file_roundtrip(tmp_path: Path) -> None:
    privkey = 21
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    _, pools_path, receipt_path = _policy_and_market(tmp_path, owner_pubkey=owner_pubkey)
    user_rule_bundle_path = _write_user_rule_bundle(tmp_path, owner_pubkey=owner_pubkey)

    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            *_LIVE_ACK_ARGS,
            "--user-rule-bundle-file",
            str(user_rule_bundle_path),
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
            str(privkey),
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["decision"]["tag"] == "submit"
    assert report["client_policy_bundle_contract"]["ok"] is True
    assert report["client_policy_bundle_contract"]["signature_ok"] is True
    assert report["user_rule_summary"]["source_form"] == "autotrader_user_rule_bundle"
    assert report["user_rule_summary"]["preset_id"] == "conservative_dca"
    assert report["user_rule_summary"]["preset_profile"]["label"] == "Conservative DCA"
    assert report["krr_explanation"]["authoring_posture"]["source_form"] == "autotrader_user_rule_bundle"
    assert report["krr_explanation"]["authoring_posture"]["source_preset_id"] == "conservative_dca"
    assert report["krr_explanation"]["authoring_posture"]["preset_profile"]["optimize_for"] == "execution_safety"
    assert report["actionability_explanation"]["authoring"]["source_form"] == "autotrader_user_rule_bundle"
    assert report["actionability_explanation"]["authoring"]["preset_id"] == "conservative_dca"
    assert report["actionability_explanation"]["authoring"]["preset_profile"]["label"] == "Conservative DCA"
    assert report["actionability_summary"]["preset_summary"].startswith("Conservative DCA: Accumulate slowly")
    assert report["krr_advice"]["authoring_summary"]["source_form"] == "autotrader_user_rule_bundle"
    assert report["krr_advice"]["authoring_summary"]["source_preset_id"] == "conservative_dca"


def test_autotrader_live_cli_capital_preservation_preset_roundtrip(tmp_path: Path) -> None:
    privkey = 21
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    _, pools_path, receipt_path = _policy_and_market(tmp_path, owner_pubkey=owner_pubkey)

    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            *_LIVE_ACK_ARGS,
            "--user-rule-preset",
            "capital_preservation_dca",
            "--asset-in",
            "A",
            "--asset-out",
            "B",
            "--fixed-order-size",
            "100",
            "--cadence-epochs",
            "4",
            "--valid-from-epoch",
            "1",
            "--valid-until-epoch",
            "100",
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
            str(privkey),
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["decision"]["tag"] == "submit"
    assert report["client_policy_bundle_contract"]["ok"] is True
    assert report["user_rule_summary"]["preset_id"] == "capital_preservation_dca"
    assert report["user_rule_summary"]["preset_profile"]["label"] == "Capital Preservation DCA"
    assert report["user_rule_summary"]["preset_profile"]["optimize_for"] == "capital_preservation"
    assert report["krr_explanation"]["authoring_posture"]["source_preset_id"] == "capital_preservation_dca"
    assert report["actionability_explanation"]["authoring"]["preset_id"] == "capital_preservation_dca"
    assert report["krr_advice"]["authoring_summary"]["source_preset_id"] == "capital_preservation_dca"



def test_autotrader_live_cli_user_rule_preset_roundtrip(tmp_path: Path) -> None:
    privkey = 21
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    _, pools_path, receipt_path = _policy_and_market(tmp_path, owner_pubkey=owner_pubkey)

    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            *_LIVE_ACK_ARGS,
            "--user-rule-preset",
            "balanced_dca",
            "--asset-in",
            "A",
            "--asset-out",
            "B",
            "--fixed-order-size",
            "100",
            "--cadence-epochs",
            "4",
            "--valid-from-epoch",
            "1",
            "--valid-until-epoch",
            "100",
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
            str(privkey),
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["decision"]["tag"] == "submit"
    assert report["client_policy_bundle_contract"]["ok"] is True
    assert report["client_policy_bundle_contract"]["signature_ok"] is True
    assert report["user_rule_summary"]["source_form"] == "autotrader_user_rule_bundle"
    assert report["user_rule_summary"]["preset_id"] == "balanced_dca"
    assert report["user_rule_summary"]["preset_profile"]["label"] == "Balanced DCA"
    assert report["krr_explanation"]["authoring_posture"]["source_preset_id"] == "balanced_dca"
    assert report["krr_explanation"]["authoring_posture"]["preset_profile"]["optimize_for"] == "balanced_execution"
    assert report["actionability_explanation"]["authoring"]["preset_id"] == "balanced_dca"
    assert report["actionability_explanation"]["authoring"]["preset_profile"]["label"] == "Balanced DCA"
    assert report["krr_advice"]["authoring_summary"]["source_preset_id"] == "balanced_dca"


def test_autotrader_live_cli_user_rule_mode_stop_loss_roundtrip(tmp_path: Path) -> None:
    privkey = 21
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    _, pools_path, receipt_path = _policy_and_market(tmp_path, owner_pubkey=owner_pubkey)

    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            *_LIVE_ACK_ARGS,
            "--user-rule-mode",
            "stop_loss_order_intent",
            "--asset-in",
            "A",
            "--asset-out",
            "B",
            "--fixed-order-size",
            "100",
            "--trigger-price",
            "90000",
            "--per-window-max",
            "300",
            "--lifetime-max",
            "1200",
            "--max-slippage-bps",
            "50",
            "--max-oracle-staleness-epochs",
            "3",
            "--valid-from-epoch",
            "1",
            "--valid-until-epoch",
            "100",
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
            str(privkey),
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["decision"]["tag"] == "reject"
    assert report["live_admission"]["error"] == "unsupported_live_strategy_mode"
    assert report["user_rule_summary"]["authoring_mode"] == "stop_loss_order_intent"
    assert report["user_rule_summary"]["overall_support_status"] == "compile_only"
    assert report["user_rule_summary"]["surface_support_matrix"]["shadow"]["supported"] is False
    assert report["user_rule_summary"]["surface_support_matrix"]["live"]["supported"] is False
    assert report["user_rule_summary"]["intent"]["template"] == "stop_loss"
    assert report["user_rule_summary"]["trigger"]["trigger_price"] == 90000
    assert report["actionability_explanation"]["authoring"]["overall_support_status"] == "compile_only"
    assert report["actionability_explanation"]["actionability"]["blocking_layer"] == "live_admission"


def test_autotrader_live_cli_trigger_preset_roundtrip(tmp_path: Path) -> None:
    privkey = 21
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    _, pools_path, receipt_path = _policy_and_market(tmp_path, owner_pubkey=owner_pubkey)

    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            *_LIVE_ACK_ARGS,
            "--user-rule-preset",
            "protective_stop_loss",
            "--asset-in",
            "A",
            "--asset-out",
            "B",
            "--fixed-order-size",
            "100",
            "--trigger-price",
            "90000",
            "--valid-from-epoch",
            "1",
            "--valid-until-epoch",
            "100",
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
            str(privkey),
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["decision"]["tag"] == "reject"
    assert report["live_admission"]["error"] == "unsupported_live_strategy_mode"
    assert report["user_rule_summary"]["preset_id"] == "protective_stop_loss"
    assert report["user_rule_summary"]["authoring_mode"] == "stop_loss_order_intent"
    assert report["user_rule_summary"]["trigger"]["trigger_price"] == 90000
    assert report["krr_explanation"] is None
    assert report["actionability_explanation"]["authoring"]["preset_id"] == "protective_stop_loss"


def test_autotrader_live_cli_text_summary_for_stop_loss_mode_includes_trigger(tmp_path: Path) -> None:
    privkey = 21
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    _, pools_path, receipt_path = _policy_and_market(tmp_path, owner_pubkey=owner_pubkey)

    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            *_LIVE_ACK_ARGS,
            "--user-rule-mode",
            "stop_loss_order_intent",
            "--asset-in",
            "A",
            "--asset-out",
            "B",
            "--fixed-order-size",
            "100",
            "--trigger-price",
            "90000",
            "--per-window-max",
            "300",
            "--lifetime-max",
            "1200",
            "--max-slippage-bps",
            "50",
            "--max-oracle-staleness-epochs",
            "3",
            "--valid-from-epoch",
            "1",
            "--valid-until-epoch",
            "100",
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
            str(privkey),
            "--text-summary",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    lines = proc.stdout.strip().splitlines()
    assert "Actionability: Blocked by live admission: unsupported_live_strategy_mode." in lines
    assert "Intent: stop_loss on A/B via place_order_intent." in lines
    assert "Sizing: fixed_order_size=100, per_order_max=100." in lines
    assert "Trigger: trigger_price=90000." in lines
    assert "Support: tier=compile_only; compile=supported, shadow=rejected(unsupported_shadow_strategy_mode), live=rejected(unsupported_live_strategy_mode)." in lines


def test_autotrader_live_cli_recommends_user_rule_preset_as_json() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--recommend-user-rule-preset",
            "--desired-optimize-for",
            "price_discipline",
            "--desired-max-slippage-bps",
            "20",
            "--desired-max-oracle-staleness-epochs",
            "3",
            "--desired-max-live-orders",
            "2",
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    payload = json.loads(proc.stdout)
    assert payload["ok"] is True
    assert payload["schema"] == "zenodex/autotrader-user-rule-preset-recommendation/v1"
    assert payload["recommended_preset"]["preset_id"] == "price_discipline_dca"
    assert payload["recommended_preset"]["mode"] == "dca_swap_exact_in"
    assert payload["ranked_candidates"][0]["total_penalty"] == 0


def test_autotrader_live_cli_recommends_trigger_user_rule_preset_as_json() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--recommend-user-rule-preset",
            "--desired-user-rule-mode",
            "stop_loss_order_intent",
            "--desired-optimize-for",
            "downside_protection",
            "--desired-max-slippage-bps",
            "25",
            "--desired-max-oracle-staleness-epochs",
            "1",
            "--desired-max-live-orders",
            "1",
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    payload = json.loads(proc.stdout)
    assert payload["recommended_preset"]["preset_id"] == "protective_stop_loss"
    assert payload["recommended_preset"]["mode"] == "stop_loss_order_intent"
    assert payload["criteria"]["desired_user_rule_mode"] == "stop_loss_order_intent"



def test_autotrader_live_cli_recommends_user_rule_preset_as_text() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--recommend-user-rule-preset",
            "--desired-max-slippage-bps",
            "20",
            "--desired-max-oracle-staleness-epochs",
            "1",
            "--desired-max-live-orders",
            "1",
            "--text-summary",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    lines = proc.stdout.strip().splitlines()
    assert lines[0] == "Recommended preset: capital_preservation_dca (Capital Preservation DCA)"
    assert lines[1] == "Mode: dca_swap_exact_in"
    assert lines[2] == "Optimize for: capital_preservation"
    assert lines[3] == "Criteria: desired_max_slippage_bps=20, desired_max_oracle_staleness_epochs=1, desired_max_live_orders=1"
    assert lines[4] == "Top candidates:"



def test_autotrader_live_cli_rejects_recommend_without_criteria() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--recommend-user-rule-preset",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 1
    payload = json.loads(proc.stderr)
    assert payload["ok"] is False
    assert "at least one criterion" in payload["error"]



def test_autotrader_live_cli_compares_user_rule_presets_as_json() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--compare-user-rule-presets",
            "capital_preservation_dca",
            "high_throughput_dca",
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    payload = json.loads(proc.stdout)
    assert payload["ok"] is True
    assert payload["schema"] == "zenodex/autotrader-user-rule-preset-comparison/v1"
    assert payload["left"]["preset_id"] == "capital_preservation_dca"
    assert payload["right"]["preset_id"] == "high_throughput_dca"
    assert payload["guard_profile_deltas"]["max_slippage_bps"] == {"left": 20, "right": 150}



def test_autotrader_live_cli_compares_user_rule_presets_as_text() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--compare-user-rule-presets",
            "balanced_dca",
            "price_discipline_dca",
            "--text-summary",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    lines = proc.stdout.strip().splitlines()
    assert lines[0] == "Comparing presets: balanced_dca -> price_discipline_dca"
    assert lines[1] == "Labels: Balanced DCA -> Price Discipline DCA"
    assert "Top-level deltas:" in lines
    assert "- optimize_for: balanced_execution -> price_discipline" in lines
    assert "Guard profile deltas:" in lines
    assert "- max_slippage_bps: 75 -> 20" in lines



def test_autotrader_live_cli_describes_user_rule_preset_as_json() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--describe-user-rule-preset",
            "price_discipline_dca",
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    payload = json.loads(proc.stdout)
    assert payload["ok"] is True
    assert payload["schema"] == "zenodex/autotrader-user-rule-preset-description/v1"
    assert payload["preset"]["preset_id"] == "price_discipline_dca"
    assert payload["preset"]["mode"] == "dca_swap_exact_in"
    assert payload["preset"]["label"] == "Price Discipline DCA"
    assert payload["preset"]["optimize_for"] == "price_discipline"
    assert payload["preset"]["authoring_requirements"]["requires_cadence_epochs"] is True
    assert payload["preset"]["authoring_requirements"]["requires_trigger_price"] is False
    assert payload["preset"]["live_execution_posture"]["supported"] is True
    assert payload["preset"]["overall_support_status"] == "supported"
    assert payload["preset"]["surface_support_matrix"]["shadow"]["supported"] is True



def test_autotrader_live_cli_describes_user_rule_preset_as_text() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--describe-user-rule-preset",
            "capital_preservation_dca",
            "--text-summary",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    lines = proc.stdout.strip().splitlines()
    assert lines[0] == "Preset: capital_preservation_dca (Capital Preservation DCA)"
    assert lines[1] == "Mode: dca_swap_exact_in"
    assert lines[2] == "Optimize for: capital_preservation"
    assert lines[3].startswith("Summary: Accumulate only under the tightest execution conditions")
    assert any(line == "Required parameters: asset_in, asset_out, fixed_order_size, valid_from_epoch, valid_until_epoch" for line in lines)
    assert any(line == "Mode-specific parameters: cadence_epochs" for line in lines)
    assert any(line == "Support tier: supported." for line in lines)
    assert any(line == "Surface support: compile=supported, shadow=supported, live=supported." for line in lines)
    assert any(line == "Live execution: supported by current executor." for line in lines)
    assert any(line.startswith("Operating profile: cadence_posture=very_spaced") for line in lines)
    assert any(line.startswith("Guard profile: per_window_orders=2") for line in lines)



def test_autotrader_live_cli_rejects_combined_preset_recommend_and_list() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--recommend-user-rule-preset",
            "--desired-optimize-for",
            "throughput",
            "--list-user-rule-presets",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 1
    payload = json.loads(proc.stderr)
    assert payload["ok"] is False
    assert "mutually exclusive" in payload["error"]



def test_autotrader_live_cli_rejects_combined_preset_compare_and_describe() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--compare-user-rule-presets",
            "balanced_dca",
            "price_discipline_dca",
            "--describe-user-rule-preset",
            "balanced_dca",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 1
    payload = json.loads(proc.stderr)
    assert payload["ok"] is False
    assert "mutually exclusive" in payload["error"]



def test_autotrader_live_cli_rejects_combined_preset_list_and_describe() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--list-user-rule-presets",
            "--describe-user-rule-preset",
            "balanced_dca",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 1
    payload = json.loads(proc.stderr)
    assert payload["ok"] is False
    assert "mutually exclusive" in payload["error"]



def test_autotrader_live_cli_lists_user_rule_presets_as_json() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--list-user-rule-presets",
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    payload = json.loads(proc.stdout)
    assert payload["ok"] is True
    assert payload["schema"] == "zenodex/autotrader-user-rule-preset-catalog/v1"
    assert payload["preset_count"] == 7
    assert [preset["preset_id"] for preset in payload["presets"]] == [
        "capital_preservation_dca",
        "conservative_dca",
        "balanced_dca",
        "price_discipline_dca",
        "high_throughput_dca",
        "protective_stop_loss",
        "disciplined_take_profit",
    ]



def test_autotrader_live_cli_lists_user_rule_presets_as_text() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--list-user-rule-presets",
            "--text-summary",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    lines = proc.stdout.strip().splitlines()
    assert lines[0] == "Available autotrader user-rule presets:"
    assert any(line == "- capital_preservation_dca: Capital Preservation DCA | mode=dca_swap_exact_in | optimize_for=capital_preservation | live=supported | tier=supported | compile=supported; shadow=supported; live=supported" for line in lines)
    assert any(line == "- conservative_dca: Conservative DCA | mode=dca_swap_exact_in | optimize_for=execution_safety | live=supported | tier=supported | compile=supported; shadow=supported; live=supported" for line in lines)
    assert any(line == "- high_throughput_dca: High-Throughput DCA | mode=dca_swap_exact_in | optimize_for=throughput | live=supported | tier=supported | compile=supported; shadow=supported; live=supported" for line in lines)
    assert any(line == "- protective_stop_loss: Protective Stop-Loss | mode=stop_loss_order_intent | optimize_for=downside_protection | live=fail_closed | tier=compile_only | compile=supported; shadow=rejected; live=rejected" for line in lines)
    assert any(line == "- disciplined_take_profit: Disciplined Take-Profit | mode=take_profit_order_intent | optimize_for=profit_realization | live=fail_closed | tier=compile_only | compile=supported; shadow=rejected; live=rejected" for line in lines)




def test_autotrader_live_cli_lists_only_live_supported_user_rule_presets_as_json() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--list-user-rule-presets",
            "--only-live-supported-presets",
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    payload = json.loads(proc.stdout)
    assert payload["ok"] is True
    assert payload["filters"] == {
        "live_supported_only": True,
        "fail_closed_only": False,
    }
    assert [preset["preset_id"] for preset in payload["presets"]] == [
        "capital_preservation_dca",
        "conservative_dca",
        "balanced_dca",
        "price_discipline_dca",
        "high_throughput_dca",
    ]
    assert all(
        preset["live_execution_posture"]["supported"] is True
        for preset in payload["presets"]
    )


def test_autotrader_live_cli_lists_only_fail_closed_user_rule_presets_as_json() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--list-user-rule-presets",
            "--only-fail-closed-presets",
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    payload = json.loads(proc.stdout)
    assert payload["ok"] is True
    assert payload["filters"] == {
        "live_supported_only": False,
        "fail_closed_only": True,
    }
    assert [preset["preset_id"] for preset in payload["presets"]] == [
        "protective_stop_loss",
        "disciplined_take_profit",
    ]
    assert all(
        preset["live_execution_posture"]["supported"] is False
        for preset in payload["presets"]
    )


def test_autotrader_live_cli_rejects_combined_live_supported_and_fail_closed_filters() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--list-user-rule-presets",
            "--only-live-supported-presets",
            "--only-fail-closed-presets",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 1
    payload = json.loads(proc.stderr)
    assert payload["ok"] is False
    assert "mutually exclusive" in payload["error"]


def test_autotrader_live_cli_recommends_live_supported_user_rule_preset_as_json() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--recommend-user-rule-preset",
            "--desired-optimize-for",
            "throughput",
            "--require-live-supported",
            "--pretty",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    payload = json.loads(proc.stdout)
    assert payload["ok"] is True
    assert payload["criteria"]["require_live_supported"] is True
    assert payload["recommended_preset"]["preset_id"] == "high_throughput_dca"
    assert payload["recommended_preset"]["live_execution_posture"]["supported"] is True


def test_autotrader_live_cli_rejects_live_supported_recommend_when_constraints_unsatisfied() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--recommend-user-rule-preset",
            "--desired-user-rule-mode",
            "stop_loss_order_intent",
            "--require-live-supported",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 1
    payload = json.loads(proc.stderr)
    assert payload["ok"] is False
    assert "no presets satisfy" in payload["error"]

def test_autotrader_live_cli_text_summary_roundtrip(tmp_path: Path) -> None:
    privkey = 21
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    policy_path, pools_path, receipt_path = _policy_and_market(tmp_path, owner_pubkey=owner_pubkey)
    client_policy_bundle_path = _write_client_policy_bundle(
        tmp_path,
        owner_pubkey=owner_pubkey,
        privkey=privkey,
    )
    telemetry_path = tmp_path / "live_report_text_mode.json"
    external_signals_path = tmp_path / "external_signals_text_mode.json"
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
            *_LIVE_ACK_ARGS,
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
            "--client-policy-bundle-file",
            str(client_policy_bundle_path),
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
            "--text-summary",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    lines = proc.stdout.strip().splitlines()
    assert lines == [
        "Decision: submit",
        "Actionability: Actionable: submit because ok.",
        "Trust: Trust posture: primary tier verified from 2 trusted signals with registry support. Weighted support: primary=0.95, trusted=1.71, external=0.76.",
        "Confidence: Confidence stable at 0.5993383254421811.",
        "Intent: dca on A/B via place_swap_exact_in.",
        "Sizing: fixed_order_size=100, cadence_epochs=4, per_order_max=100.",
        "Support: tier=supported; compile=supported, shadow=supported, live=supported.",
        "Risk acknowledgement: acknowledged.",
    ]
    persisted = json.loads(telemetry_path.read_text(encoding="utf-8"))
    assert persisted["actionability_summary"]["headline"] == "Actionable: submit because ok."



def test_autotrader_live_cli_text_summary_includes_preset_profile(tmp_path: Path) -> None:
    privkey = 21
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    _, pools_path, receipt_path = _policy_and_market(tmp_path, owner_pubkey=owner_pubkey)

    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            *_LIVE_ACK_ARGS,
            "--user-rule-preset",
            "balanced_dca",
            "--asset-in",
            "A",
            "--asset-out",
            "B",
            "--fixed-order-size",
            "100",
            "--cadence-epochs",
            "4",
            "--valid-from-epoch",
            "1",
            "--valid-until-epoch",
            "100",
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
            str(privkey),
            "--text-summary",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    lines = proc.stdout.strip().splitlines()
    assert lines[0] == "Decision: submit"
    assert lines[1] == "Actionability: Actionable: submit because ok."
    assert lines[2].startswith(
        "Preset: Balanced DCA: Accumulate on a steadier schedule with moderate slippage"
    )
    assert lines[3] == "Trust: Trust posture: primary tier verified from 1 trusted signal without registry support. Weighted support: primary=0.95, trusted=0.95."
    assert lines[4] == "Confidence: Confidence stable at 0.5993383254421811."
    assert lines[-1] == "Risk acknowledgement: acknowledged."


def test_autotrader_live_cli_rejects_tampered_client_policy_bundle_signature(tmp_path: Path) -> None:
    privkey = 21
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    policy_path, pools_path, receipt_path = _policy_and_market(tmp_path, owner_pubkey=owner_pubkey)
    client_policy_bundle_path = _write_client_policy_bundle(
        tmp_path,
        owner_pubkey=owner_pubkey,
        privkey=privkey,
    )
    payload = json.loads(client_policy_bundle_path.read_text(encoding="utf-8"))
    payload["signature"] = "0x00"
    client_policy_bundle_path.write_text(
        json.dumps(payload, indent=2, sort_keys=True),
        encoding="utf-8",
    )

    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            *_LIVE_ACK_ARGS,
            "--policy-file",
            str(policy_path),
            "--receipt-file",
            str(receipt_path),
            "--pools-file",
            str(pools_path),
            "--client-policy-bundle-file",
            str(client_policy_bundle_path),
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

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["decision"]["tag"] == "reject"
    assert report["decision"]["reason"] == "client_policy_bundle_signature_invalid"
    assert report["live_admission"]["ok"] is False
    assert report["live_admission"]["error"] == "client_policy_bundle_signature_invalid"
    assert report["client_policy_bundle_contract"]["ok"] is False
    assert report["client_policy_bundle_contract"]["error"] == "client_policy_bundle_signature_invalid"
    assert report["client_policy_bundle_contract"]["signature_ok"] is False


def test_autotrader_live_cli_rejects_unsigned_client_policy_bundle(tmp_path: Path) -> None:
    privkey = 21
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    policy_path, pools_path, receipt_path = _policy_and_market(tmp_path, owner_pubkey=owner_pubkey)
    client_policy_bundle_path = _write_client_policy_bundle(
        tmp_path,
        owner_pubkey=owner_pubkey,
        privkey=privkey,
    )
    payload = json.loads(client_policy_bundle_path.read_text(encoding="utf-8"))
    payload["signature"] = None
    payload["signer_pubkey"] = None
    client_policy_bundle_path.write_text(
        json.dumps(payload, indent=2, sort_keys=True),
        encoding="utf-8",
    )

    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            *_LIVE_ACK_ARGS,
            "--policy-file",
            str(policy_path),
            "--receipt-file",
            str(receipt_path),
            "--pools-file",
            str(pools_path),
            "--client-policy-bundle-file",
            str(client_policy_bundle_path),
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

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["decision"]["tag"] == "reject"
    assert report["decision"]["reason"] == "client_policy_bundle_signature_missing"
    assert report["live_admission"]["ok"] is False
    assert report["live_admission"]["error"] == "client_policy_bundle_signature_missing"
    assert report["client_policy_bundle_contract"]["ok"] is False
    assert report["client_policy_bundle_contract"]["error"] == "client_policy_bundle_signature_missing"
    assert report["client_policy_bundle_contract"]["signature_ok"] is False


def test_autotrader_live_cli_rejects_client_policy_bundle_hash_mismatch(tmp_path: Path) -> None:
    privkey = 21
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    policy_path, pools_path, receipt_path = _policy_and_market(tmp_path, owner_pubkey=owner_pubkey)
    client_policy_bundle_path = _write_client_policy_bundle(
        tmp_path,
        owner_pubkey=owner_pubkey,
        privkey=privkey,
    )
    payload = json.loads(client_policy_bundle_path.read_text(encoding="utf-8"))
    payload["client_policy_bundle_hash"] = "0xdeadbeef"
    client_policy_bundle_path.write_text(
        json.dumps(payload, indent=2, sort_keys=True),
        encoding="utf-8",
    )

    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            *_LIVE_ACK_ARGS,
            "--policy-file",
            str(policy_path),
            "--receipt-file",
            str(receipt_path),
            "--pools-file",
            str(pools_path),
            "--client-policy-bundle-file",
            str(client_policy_bundle_path),
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

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["decision"]["tag"] == "reject"
    assert report["decision"]["reason"] == "client_policy_bundle_load_rejected"
    assert "client policy bundle hash mismatch" in report["decision"]["explain"][-1]
    assert report["live_admission"]["ok"] is False
    assert report["live_admission"]["error"] == "client_policy_bundle_load_rejected"
    assert report["client_policy_bundle_contract"]["ok"] is False
    assert report["client_policy_bundle_contract"]["error"] == "client_policy_bundle_load_rejected"
    assert report["client_policy_bundle"] is None


def test_autotrader_live_cli_rejects_client_policy_bundle_strategy_mismatch(tmp_path: Path) -> None:
    privkey = 21
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    policy_path, pools_path, receipt_path = _policy_and_market(tmp_path, owner_pubkey=owner_pubkey)
    client_policy_bundle_path = _write_client_policy_bundle(
        tmp_path,
        owner_pubkey=owner_pubkey,
        privkey=privkey,
        fixed_order_size=101,
    )

    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            *_LIVE_ACK_ARGS,
            "--policy-file",
            str(policy_path),
            "--receipt-file",
            str(receipt_path),
            "--pools-file",
            str(pools_path),
            "--client-policy-bundle-file",
            str(client_policy_bundle_path),
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

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["decision"]["tag"] == "reject"
    assert report["decision"]["reason"] == "client_policy_bundle_strategy_hash_mismatch"
    assert report["live_admission"]["ok"] is False
    assert report["live_admission"]["error"] == "client_policy_bundle_strategy_hash_mismatch"
    assert report["client_policy_bundle_contract"]["ok"] is False
    assert report["client_policy_bundle_contract"]["error"] == "client_policy_bundle_strategy_hash_mismatch"


def test_autotrader_live_cli_rejects_policy_artifact_hash_mismatch(tmp_path: Path) -> None:
    privkey = 21
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    policy_path, pools_path, receipt_path = _policy_and_market(tmp_path, owner_pubkey=owner_pubkey)
    artifact_path, tau_path = _write_policy_artifact_and_tau_policy_bundle(
        tmp_path,
        owner_pubkey=owner_pubkey,
        privkey=privkey,
    )
    payload = json.loads(artifact_path.read_text(encoding="utf-8"))
    payload["policy_artifact_hash"] = "0xdeadbeef"
    artifact_path.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")

    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            *_LIVE_ACK_ARGS,
            "--policy-file",
            str(policy_path),
            "--receipt-file",
            str(receipt_path),
            "--pools-file",
            str(pools_path),
            "--policy-artifact-file",
            str(artifact_path),
            "--tau-policy-bundle-file",
            str(tau_path),
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

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["decision"]["tag"] == "reject"
    assert report["decision"]["reason"] == "policy_artifact_load_rejected"
    assert "policy artifact hash mismatch" in report["decision"]["explain"][-1]
    assert report["live_admission"]["ok"] is False
    assert report["live_admission"]["error"] == "policy_artifact_load_rejected"
    assert report["policy_artifact_contract"]["ok"] is False
    assert report["policy_artifact_contract"]["error"] == "policy_artifact_load_rejected"
    assert report["policy_artifact"] is None


def test_autotrader_live_cli_rejects_tau_policy_bundle_hash_mismatch(tmp_path: Path) -> None:
    privkey = 21
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    policy_path, pools_path, receipt_path = _policy_and_market(tmp_path, owner_pubkey=owner_pubkey)
    artifact_path, tau_path = _write_policy_artifact_and_tau_policy_bundle(
        tmp_path,
        owner_pubkey=owner_pubkey,
        privkey=privkey,
    )
    payload = json.loads(tau_path.read_text(encoding="utf-8"))
    payload["tau_policy_bundle_hash"] = "0xdeadbeef"
    tau_path.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")

    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            *_LIVE_ACK_ARGS,
            "--policy-file",
            str(policy_path),
            "--receipt-file",
            str(receipt_path),
            "--pools-file",
            str(pools_path),
            "--policy-artifact-file",
            str(artifact_path),
            "--tau-policy-bundle-file",
            str(tau_path),
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

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["decision"]["tag"] == "reject"
    assert report["decision"]["reason"] == "tau_policy_bundle_load_rejected"
    assert "tau policy bundle hash mismatch" in report["decision"]["explain"][-1]
    assert report["live_admission"]["ok"] is False
    assert report["live_admission"]["error"] == "tau_policy_bundle_load_rejected"
    assert report["tau_policy_bundle_contract"]["ok"] is False
    assert report["tau_policy_bundle_contract"]["error"] == "tau_policy_bundle_load_rejected"
    assert report["tau_policy_bundle"] is None


def test_autotrader_live_cli_requires_experimental_risk_acknowledgement(tmp_path: Path) -> None:
    privkey = 21
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
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
    assert "autotrader_live_requires_risk_acknowledgement" in report["error"]
    assert report["risk_disclosure"]["requires_explicit_acknowledgement"] is True
    assert report["risk_disclosure"]["user_acknowledged"] is False


def test_autotrader_live_cli_rejects_tampered_typed_signal_source_registry_payload(
    tmp_path: Path,
) -> None:
    privkey = 21
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    policy_path, pools_path, receipt_path = _policy_and_market(tmp_path, owner_pubkey=owner_pubkey)
    registry_path = _write_tampered_signal_source_registry(tmp_path)

    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            *_LIVE_ACK_ARGS,
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

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["decision"]["tag"] == "reject"
    assert report["decision"]["reason"] == "signal_source_registry_load_rejected"
    assert (
        "signal source registry payload rejected: "
        "external signal source registry payload mismatch"
    ) in report["decision"]["explain"][-1]
    assert report["live_admission"]["ok"] is False
    assert report["live_admission"]["error"] == "signal_source_registry_load_rejected"


def test_live_report_to_dict_includes_new_tau_receipts() -> None:
    privkey = 21
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    strategy = compile_policy_candidate(_candidate(owner_pubkey=owner_pubkey)).strategy
    client_policy_bundle = sign_autotrader_client_policy_bundle(
        build_autotrader_client_policy_bundle(
            bundle_name="bundle.serializer",
            built_at="2026-04-09T12:00:00Z",
            client_policy_surface=build_autotrader_client_policy_surface(strategy=strategy),
        ),
        privkey=privkey,
    )
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
        client_policy_bundle=client_policy_bundle,
        client_policy_bundle_ok=True,
        client_policy_bundle_error=None,
        client_policy_bundle_signature_ok=True,
    )

    payload = autotrader_live_cli._live_report_to_dict(report)

    assert payload["risk_disclosure"]["advanced_feature"] is True
    assert payload["risk_disclosure"]["requires_explicit_acknowledgement"] is True
    assert payload["risk_disclosure"]["user_acknowledged"] is False
    assert payload["live_admission_tau_receipt"]["spec_id"] == "autotrader_system_compose_v1"
    assert payload["system_compose_tau_receipt"]["gate_output"] == "o3"
    assert payload["submit_bundle_tau_receipt"]["spec_id"] == "autotrader_system_compose_v1"
    assert payload["emit_finalize_tau_receipt"]["spec_id"] == "autotrader_system_compose_v1"
    assert payload["session_state"]["session_id"] == "session.1"
    assert payload["session_state_tau_receipt"]["spec_id"] == "autotrader_system_compose_v1"
    assert payload["external_signal_source_registry_tau_receipts"][0]["signal_id"] == "sig.oracle.1"
    assert payload["client_policy_bundle"]["schema"] == "zenodex/autotrader-client-policy-bundle/v1"
    assert payload["client_policy_bundle_contract"] == {"ok": True, "error": None, "signature_ok": True}
    assert payload["krr_explanation"] is None
    assert payload["user_rule_summary"] is None
    assert payload["actionability_explanation"] is None
    assert payload["actionability_summary"] is None
    assert payload["client_policy_bundle_hash"] == client_policy_bundle.client_policy_bundle_hash_hex()
    assert payload["client_policy_surface_hash"] == (
        client_policy_bundle.client_policy_surface.client_policy_surface_hash_hex()
    )
    assert payload["stage_certificate"] is None
    assert payload["live_release_certificate"] is None


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
            *_LIVE_ACK_ARGS,
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

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["decision"]["tag"] == "reject"
    assert report["decision"]["reason"] == "external_signals_load_rejected"
    assert "external signal contract rejected: attested_external_invalid" in report["decision"]["explain"][-1]
    assert report["live_admission"]["ok"] is False
    assert report["live_admission"]["error"] == "external_signals_load_rejected"


def test_autotrader_live_cli_accepts_krr_bundle_file(tmp_path: Path) -> None:
    privkey = 21
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    policy_path, pools_path, receipt_path = _policy_and_market(tmp_path, owner_pubkey=owner_pubkey)
    bundle_path = _write_krr_bundle(tmp_path)

    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            *_LIVE_ACK_ARGS,
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
    assert report["krr_bundle_contract"] == {"ok": True, "error": None}
    assert report["history_check_stats_contract"] == {"ok": None, "error": None}
    assert len(report["external_signals"]) == 1
    assert report["signal_source_registry"]["entry_count"] == 1
    assert report["krr_advice"] is not None
    assert report["krr_advice"]["backend_used"] == "python"


def test_autotrader_live_cli_degrades_on_krr_bundle_hash_mismatch(tmp_path: Path) -> None:
    privkey = 21
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    policy_path, pools_path, receipt_path = _policy_and_market(tmp_path, owner_pubkey=owner_pubkey)
    bundle_path = _write_krr_bundle(tmp_path)
    payload = json.loads(bundle_path.read_text(encoding="utf-8"))
    payload["bundle_hash"] = "0x" + ("de" * 32)
    bundle_path.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")

    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            *_LIVE_ACK_ARGS,
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
            *_LIVE_ACK_ARGS,
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


def test_autotrader_live_cli_degrades_on_bad_history_check_stats_file(tmp_path: Path) -> None:
    privkey = 26
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    policy_path, pools_path, receipt_path = _policy_and_market(tmp_path, owner_pubkey=owner_pubkey)
    history_path = tmp_path / "bad_history_check_stats.json"
    history_path.write_text(json.dumps(["bad"]), encoding="utf-8")

    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            *_LIVE_ACK_ARGS,
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
            "--last-used-nonce",
            "0",
            "--signer-privkey",
            str(privkey),
            "--krr-backend",
            "python",
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
    assert "history-check-stats file must be an object" in report["history_check_stats_contract"]["error"]
    assert report["krr_advice"] is not None


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
            *_LIVE_ACK_ARGS,
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
            *_LIVE_ACK_ARGS,
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


def test_autotrader_live_cli_rejects_wallet_capability_string_enabled(tmp_path: Path) -> None:
    privkey = 43
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    policy_path, pools_path, receipt_path = _policy_and_market(tmp_path, owner_pubkey=owner_pubkey)
    capability_path = tmp_path / "bad_wallet_capability.json"
    capability_path.write_text(
        json.dumps(
            {
                "session_id": "session.cli.bad.wallet",
                "owner_pubkey": owner_pubkey,
                "chain_id": "tau-local",
                "valid_from_epoch": 1,
                "valid_until_epoch": 100,
                "notional_remaining": 500,
                "allowed_assets": ["A", "B"],
                "allowed_actions": ["place_swap_exact_in"],
                "enabled": "false",
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
            *_LIVE_ACK_ARGS,
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
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["decision"]["tag"] == "reject"
    assert report["decision"]["reason"] == "wallet_capability_load_rejected"
    assert "enabled must be a bool" in report["decision"]["explain"][-1]
    assert report["live_admission"]["ok"] is False
    assert report["live_admission"]["error"] == "wallet_capability_load_rejected"


def test_autotrader_live_cli_rejects_session_state_string_enabled(tmp_path: Path) -> None:
    privkey = 44
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    policy_path, pools_path, receipt_path = _policy_and_market(tmp_path, owner_pubkey=owner_pubkey)
    session_state_path = tmp_path / "bad_enabled_session_state.json"
    session_state_path.write_text(
        json.dumps(
            {
                "session_id": "session.cli.bad.enabled",
                "owner_pubkey": owner_pubkey,
                "chain_id": "tau-local",
                "enabled": "false",
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
            *_LIVE_ACK_ARGS,
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

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["decision"]["tag"] == "reject"
    assert report["decision"]["reason"] == "session_state_load_rejected"
    assert "enabled must be a bool" in report["decision"]["explain"][-1]
    assert report["live_admission"]["ok"] is False
    assert report["live_admission"]["error"] == "session_state_load_rejected"


def test_autotrader_live_cli_rejects_controller_state_string_kill_switch(tmp_path: Path) -> None:
    privkey = 45
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    policy_path, pools_path, receipt_path = _policy_and_market(tmp_path, owner_pubkey=owner_pubkey)
    controller_state_path = tmp_path / "bad_controller_state.json"
    controller_state_path.write_text(
        json.dumps(
            {
                "controller_state": {
                    "budget_state": {
                        "window_id": 0,
                        "spent_in_window": 0,
                        "kill_switch_on": "false",
                    },
                    "lifetime_spent": 0,
                    "live_orders": 0,
                }
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
            *_LIVE_ACK_ARGS,
            "--policy-file",
            str(policy_path),
            "--receipt-file",
            str(receipt_path),
            "--pools-file",
            str(pools_path),
            "--controller-state-file",
            str(controller_state_path),
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

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["decision"]["tag"] == "reject"
    assert report["decision"]["reason"] == "controller_state_load_rejected"
    assert "budget_state.kill_switch_on must be a bool" in report["decision"]["explain"][-1]
    assert report["live_admission"]["ok"] is False
    assert report["live_admission"]["error"] == "controller_state_load_rejected"


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
            *_LIVE_ACK_ARGS,
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

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["decision"]["tag"] == "reject"
    assert report["decision"]["reason"] == "session_state_load_rejected"
    assert "session_state must be an object" in report["decision"]["explain"][-1]
    assert report["live_admission"]["ok"] is False
    assert report["live_admission"]["error"] == "session_state_load_rejected"


def test_autotrader_live_cli_rejects_signer_mismatch(tmp_path: Path) -> None:
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(22)
    policy_path, pools_path, receipt_path = _policy_and_market(tmp_path, owner_pubkey=owner_pubkey)

    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            *_LIVE_ACK_ARGS,
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


def test_autotrader_live_cli_bad_receipt_file_fails(tmp_path: Path) -> None:
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(25)
    policy_path, pools_path, _ = _policy_and_market(tmp_path, owner_pubkey=owner_pubkey)
    bad_receipt_path = tmp_path / "bad_receipt.json"
    bad_receipt_path.write_text(json.dumps(["bad"]), encoding="utf-8")

    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            *_LIVE_ACK_ARGS,
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
            "--last-used-nonce",
            "0",
            "--signer-privkey",
            "25",
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["decision"]["tag"] == "reject"
    assert report["decision"]["reason"] == "receipt_file_load_rejected"
    assert "receipt file must be an object" in report["decision"]["explain"][-1]
    assert report["live_admission"]["ok"] is False
    assert report["live_admission"]["error"] == "receipt_file_load_rejected"


def test_autotrader_live_cli_bad_pools_file_fails(tmp_path: Path) -> None:
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(24)
    policy_path, _, receipt_path = _policy_and_market(tmp_path, owner_pubkey=owner_pubkey)
    bad_pools_path = tmp_path / "bad_pools.json"
    bad_pools_path.write_text(json.dumps({"pools": "bad"}), encoding="utf-8")

    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            *_LIVE_ACK_ARGS,
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

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["decision"]["tag"] == "reject"
    assert report["decision"]["reason"] == "pools_file_load_rejected"
    assert "pools file must be a map" in report["decision"]["explain"][-1]
    assert report["live_admission"]["ok"] is False
    assert report["live_admission"]["error"] == "pools_file_load_rejected"


def test_autotrader_live_cli_rejects_bad_candidate_file_structurally(tmp_path: Path) -> None:
    privkey = 26
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    _, pools_path, receipt_path = _policy_and_market(tmp_path, owner_pubkey=owner_pubkey)
    candidate_path = tmp_path / "bad_candidate.json"
    candidate_path.write_text(json.dumps(["bad"]), encoding="utf-8")

    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            *_LIVE_ACK_ARGS,
            "--candidate-file",
            str(candidate_path),
            "--owner-pubkey",
            owner_pubkey,
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
            str(privkey),
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["decision"]["tag"] == "reject"
    assert report["decision"]["reason"] == "strategy_source_load_rejected"
    assert "candidate file must be an object" in report["decision"]["explain"][-1]
    assert report["live_admission"]["ok"] is False
    assert report["live_admission"]["error"] == "strategy_source_load_rejected"
    assert report["strategy_source_contract"]["ok"] is False
    assert report["strategy_source_contract"]["source_kind"] == "candidate_file"


def test_autotrader_live_cli_rejects_bad_policy_text_file_structurally(tmp_path: Path) -> None:
    privkey = 27
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    _, pools_path, receipt_path = _policy_and_market(tmp_path, owner_pubkey=owner_pubkey)
    policy_text_path = tmp_path / "bad_policy.txt"
    policy_text_path.write_text("nonsense policy text", encoding="utf-8")

    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            *_LIVE_ACK_ARGS,
            "--policy-text-file",
            str(policy_text_path),
            "--owner-pubkey",
            owner_pubkey,
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
            str(privkey),
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["decision"]["tag"] == "reject"
    assert report["decision"]["reason"] == "strategy_source_load_rejected"
    assert "unsupported policy text" in report["decision"]["explain"][-1]
    assert report["live_admission"]["ok"] is False
    assert report["live_admission"]["error"] == "strategy_source_load_rejected"
    assert report["strategy_source_contract"]["ok"] is False
    assert report["strategy_source_contract"]["source_kind"] == "policy_text_file"


def test_autotrader_live_cli_rejects_bad_policy_file_structurally(tmp_path: Path) -> None:
    privkey = 28
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    _, pools_path, receipt_path = _policy_and_market(tmp_path, owner_pubkey=owner_pubkey)
    policy_path = tmp_path / "bad_policy.json"
    policy_path.write_text(json.dumps({"schema": "wrong"}), encoding="utf-8")

    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            *_LIVE_ACK_ARGS,
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
            str(privkey),
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["decision"]["tag"] == "reject"
    assert report["decision"]["reason"] == "strategy_source_load_rejected"
    assert "unsupported local policy schema" in report["decision"]["explain"][-1]
    assert report["live_admission"]["ok"] is False
    assert report["live_admission"]["error"] == "strategy_source_load_rejected"
    assert report["strategy_source_contract"]["ok"] is False
    assert report["strategy_source_contract"]["source_kind"] == "policy_file"


def test_autotrader_live_cli_rejects_bad_user_rule_bundle_file_structurally(tmp_path: Path) -> None:
    privkey = 29
    owner_pubkey = "0x" + bls_pubkey_hex_from_privkey(privkey)
    _, pools_path, receipt_path = _policy_and_market(tmp_path, owner_pubkey=owner_pubkey)
    bundle_path = tmp_path / "bad_user_rule_bundle.json"
    bundle_path.write_text(json.dumps({"schema": "wrong"}), encoding="utf-8")

    proc = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            *_LIVE_ACK_ARGS,
            "--user-rule-bundle-file",
            str(bundle_path),
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
            str(privkey),
            "--owner-pubkey",
            owner_pubkey,
        ],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0, proc.stderr
    report = json.loads(proc.stdout)
    assert report["decision"]["tag"] == "reject"
    assert report["decision"]["reason"] == "user_rule_bundle_load_rejected"
    assert "unsupported autotrader user rule bundle schema" in report["decision"]["explain"][-1]
    assert report["live_admission"]["ok"] is False
    assert report["live_admission"]["error"] == "user_rule_bundle_load_rejected"
    assert report["user_rule_bundle_contract"]["ok"] is False
    assert report["user_rule_bundle_contract"]["source_kind"] == "user_rule_bundle_file"
