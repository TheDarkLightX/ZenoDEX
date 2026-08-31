# [TESTER] v1
"""App-root/JMT production-promotion lane: replay and fail-closed grading.

Of the six production-promotion lanes, five require external evidence
(public-testnet broadcasts, hardware-device attestations, TEE attestations, a
24h+ supervisor run, a soundness audit). The ``app_root_jmt`` lane is different:
its evidence is LOCAL release-replay, so it is the one lane whose evidence a
local process can produce. This file characterizes that lane HONESTLY, including
a gate-integrity limitation worth hardening.

What IS true (genuine):
- ``tools/build_app_root_jmt_evidence.py::build_evidence`` exercises the REAL
  replay paths and binds the unified ``typed_app_root_jmt_v1`` root over every
  registered lane kind.
- The V2 evaluator independently hashes each source payload and re-derives its
  typed root through the exact registered derivation.
- The aggregate six-lane gate still blocks on the five external lanes (no
  bundle-level fail-green).

Claim ceiling: this lane authenticates bounded local replay artifacts. It does
not grant global production authority, external finality, or release mounting.
"""

from __future__ import annotations

from copy import deepcopy

from src.integration.production_promotion_evidence import (
    APP_ROOT_JMT_EVIDENCE_SCHEMA_V1,
    APP_ROOT_JMT_EVIDENCE_SCHEMA_V2,
    attach_production_app_root_jmt_hash_v2,
    evaluate_production_app_root_jmt_evidence_v2,
    evaluate_production_promotion_bundle_v1,
)
from src.state.app_root import APP_ROOT_LANE_KINDS
from tools.build_app_root_jmt_evidence import build_evidence

_PINNED_NOW = 1_781_395_200
_ALL_LANES = {
    "clob",
    "cross_shard",
    "governance",
    "oracle",
    "perps",
    "proof_mining",
    "spot",
    "vault",
    "zusd",
}


def test_build_evidence_produces_real_replay_unified_all_lane_root() -> None:
    """The PRODUCER genuinely exercises the real replay paths and binds the
    unified typed app-root JMT over all registered lane kinds (not spot-only/fixture).
    This is the real, local, autonomously-producible part — distinct from the
    five external lanes."""
    ev = build_evidence(now=_PINNED_NOW)
    assert ev["schema"] == APP_ROOT_JMT_EVIDENCE_SCHEMA_V2
    assert ev["root_system"] == "typed_app_root_jmt_v1"
    assert ev["evidence_kind"] == "live_replay"
    assert set(ev["required_lane_kinds"]) == set(APP_ROOT_LANE_KINDS) == _ALL_LANES
    assert len(ev["live_root_checks"]) == 2                 # plain / local-header
    assert all("tau" not in chk["mode"] for chk in ev["live_root_checks"])
    # Each live check carries a re-derivation pair + a source binding from the real path.
    for chk in ev["live_root_checks"]:
        assert chk["observed_root"] == chk["recomputed_root"]
        assert chk["source_state_hash"] and chk["live_path"]
    assert ev["negative_checks"][0]["rejected"] is True     # lane-tamper IS rejected
    assert isinstance(ev.get("evidence_hash"), str) and ev["evidence_hash"]


def test_lane_evaluator_accepts_the_real_replay_evidence() -> None:
    """The authoritative lane evaluator accepts the producer's real-replay
    evidence (ok, no gaps). So app_root_jmt is the one lane whose gate-acceptable
    evidence is autonomously producible."""
    ev = build_evidence(now=_PINNED_NOW)
    result = evaluate_production_app_root_jmt_evidence_v2(ev, now=_PINNED_NOW)
    assert result["ok"] is True, result.get("gaps")
    assert result["gaps"] == []
    assert "lane_tamper_rejected" in result.get("negative_mutations", [])


def test_lane_evaluator_rejects_self_consistent_forged_roots() -> None:
    # Arrange
    forged = deepcopy(build_evidence(now=_PINNED_NOW))
    forged.pop("evidence_hash")
    for index, check in enumerate(forged["live_root_checks"], start=1):
        filler = f"{index:02x}" * 32
        check["observed_root"] = filler
        check["recomputed_root"] = filler
    forged = attach_production_app_root_jmt_hash_v2(forged)

    # Act
    result = evaluate_production_app_root_jmt_evidence_v2(forged, now=_PINNED_NOW)

    # Assert
    assert result["ok"] is False
    assert any("evaluator-derived root" in gap for gap in result["gaps"])


def test_lane_evaluator_rejects_self_consistent_historical_tau_wrapper_mode() -> None:
    evidence = deepcopy(build_evidence(now=_PINNED_NOW))
    evidence.pop("evidence_hash")
    historical = deepcopy(evidence["live_root_checks"][0])
    historical["check_id"] = "historical-tau-wrapper"
    historical["mode"] = "tau_app_state_wrapper_live_root"
    evidence["live_root_checks"].append(historical)
    evidence = attach_production_app_root_jmt_hash_v2(evidence)

    result = evaluate_production_app_root_jmt_evidence_v2(
        evidence,
        now=_PINNED_NOW,
    )

    assert result["ok"] is False
    assert (
        "live_root_checks[2].mode: unsupported app-root live-root mode"
        in result["gaps"]
    )


def test_lane_evaluator_rejects_source_payload_hash_drift() -> None:
    # Arrange
    evidence = deepcopy(build_evidence(now=_PINNED_NOW))
    evidence.pop("evidence_hash")
    evidence["live_root_checks"][0]["source_payload"]["oracle"]["price_timestamp"] = 18
    evidence = attach_production_app_root_jmt_hash_v2(evidence)

    # Act
    result = evaluate_production_app_root_jmt_evidence_v2(evidence, now=_PINNED_NOW)

    # Assert
    assert result["ok"] is False
    assert any("source_state_hash" in gap for gap in result["gaps"])


def test_lane_evaluator_rejects_missing_source_payload() -> None:
    # Arrange
    evidence = deepcopy(build_evidence(now=_PINNED_NOW))
    evidence.pop("evidence_hash")
    evidence["live_root_checks"][0].pop("source_payload")
    evidence = attach_production_app_root_jmt_hash_v2(evidence)

    # Act
    result = evaluate_production_app_root_jmt_evidence_v2(evidence, now=_PINNED_NOW)

    # Assert
    assert result["ok"] is False
    assert any("source_payload" in gap for gap in result["gaps"])


def test_lane_evaluator_rejects_source_payload_over_byte_budget() -> None:
    # Arrange
    evidence = deepcopy(build_evidence(now=_PINNED_NOW))
    evidence.pop("evidence_hash")
    evidence["live_root_checks"][0]["source_payload"]["governance"] = {
        "padding": "x" * 1_000_000
    }
    evidence = attach_production_app_root_jmt_hash_v2(evidence)

    # Act
    result = evaluate_production_app_root_jmt_evidence_v2(evidence, now=_PINNED_NOW)

    # Assert
    assert result["ok"] is False
    assert any("cannot re-derive app root: ValueError" in gap for gap in result["gaps"])


def test_lane_evaluator_rejects_retired_v1_schema() -> None:
    # Arrange
    evidence = deepcopy(build_evidence(now=_PINNED_NOW))
    evidence["schema"] = APP_ROOT_JMT_EVIDENCE_SCHEMA_V1
    evidence.pop("evidence_hash")
    evidence = attach_production_app_root_jmt_hash_v2(evidence)

    # Act
    result = evaluate_production_app_root_jmt_evidence_v2(evidence, now=_PINNED_NOW)

    # Assert
    assert result["ok"] is False
    assert any("schema mismatch" in gap for gap in result["gaps"])


def test_six_lane_bundle_still_blocks_on_the_five_external_lanes() -> None:
    """No bundle-level fail-green: even with app_root_jmt satisfied, the aggregate
    gate stays not-ready because the five external lanes have no evidence."""
    bundle = {
        "oracle_authority": None, "hardware_wallet": None, "zk_wrapping": None,
        "autotrader": None, "confidential_runtime": None,
        "app_root_jmt": build_evidence(now=_PINNED_NOW),
    }
    result = evaluate_production_promotion_bundle_v1(bundle, now=_PINNED_NOW)
    assert result["lanes"]["app_root_jmt"]["ok"] is True
    assert result.get("promotion_ready") is False
    blocked = set(result.get("blocked_lanes", []))
    assert "app_root_jmt" not in blocked
    assert {"oracle_authority", "hardware_wallet", "zk_wrapping",
            "autotrader", "confidential_runtime"} <= blocked
