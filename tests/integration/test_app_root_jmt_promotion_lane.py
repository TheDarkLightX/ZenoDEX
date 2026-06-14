# [TESTER] v1
"""App-root/JMT production-promotion lane: what is and is NOT assured.

Of the six production-promotion lanes, five require external evidence
(public-testnet broadcasts, hardware-device attestations, TEE attestations, a
24h+ supervisor run, a soundness audit). The ``app_root_jmt`` lane is different:
its evidence is LOCAL release-replay, so it is the one lane whose evidence a
local process can produce. This file characterizes that lane HONESTLY, including
a gate-integrity limitation worth hardening.

What IS true (genuine):
- ``tools/build_app_root_jmt_evidence.py::build_evidence`` exercises the REAL
  replay paths (plain Dex snapshot root, Tau app-state wrapper root, local block
  pre-snapshot header root) and binds the unified ``typed_app_root_jmt_v1`` root
  over all eight lane kinds — not a spot-only or fixture root.
- The authoritative lane evaluator accepts that real evidence.
- The aggregate six-lane gate still blocks on the five external lanes (no
  bundle-level fail-green).

What is NOT assured (the finding — documented, not hidden):
- ``evaluate_production_app_root_jmt_evidence_v1`` validates structure, schema,
  ``root_system``, lane kinds, freshness, the self-binding hash, and that each
  check's ``observed_root == recomputed_root`` — but it does NOT independently
  re-derive the roots from source state. So a well-formed record with arbitrary
  matching roots also passes (see ``test_..._evaluator_is_consistency_only``,
  matching the repo's own ``_valid_app_root_jmt_evidence`` fixture which uses
  ``11/12/13``-filler roots). Therefore passing this lane reflects the
  PRODUCER's real replay, not gate-enforced root authenticity. Hardening
  recommendation: bind each live check to replayable source material and
  re-derive the three roots inside the evaluator (then forged-root evidence
  fails). Recorded as a finding; the gate evaluator is not changed here.
"""

from __future__ import annotations

from src.integration.production_promotion_evidence import (
    APP_ROOT_JMT_EVIDENCE_SCHEMA_V1,
    attach_production_app_root_jmt_hash_v1,
    evaluate_production_app_root_jmt_evidence_v1,
    evaluate_production_promotion_bundle_v1,
)
from src.state.app_root import APP_ROOT_LANE_KINDS
from tools.build_app_root_jmt_evidence import build_evidence

_PINNED_NOW = 1_781_395_200
_ALL_LANES = {"clob", "governance", "oracle", "perps", "proof_mining",
              "spot", "vault", "zusd"}


def test_build_evidence_produces_real_replay_unified_all_lane_root() -> None:
    """The PRODUCER genuinely exercises the real replay paths and binds the
    unified typed app-root JMT over all eight lane kinds (not spot-only/fixture).
    This is the real, local, autonomously-producible part — distinct from the
    five external lanes."""
    ev = build_evidence(now=_PINNED_NOW)
    assert ev["root_system"] == "typed_app_root_jmt_v1"
    assert ev["evidence_kind"] == "live_replay"
    assert set(ev["required_lane_kinds"]) == set(APP_ROOT_LANE_KINDS) == _ALL_LANES
    assert len(ev["live_root_checks"]) == 3                 # plain / tau-wrapper / local-header
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
    result = evaluate_production_app_root_jmt_evidence_v1(ev, now=_PINNED_NOW)
    assert result["ok"] is True, result.get("gaps")
    assert result["gaps"] == []
    assert "lane_tamper_rejected" in result.get("negative_mutations", [])


def test_lane_evaluator_is_consistency_only_not_root_reauthentication() -> None:
    """FINDING (documented, not hidden): the lane evaluator does NOT re-derive
    roots from source — a well-formed record with ARBITRARY matching roots also
    passes. So gate acceptance is consistency-only; root authenticity rests on the
    producer. If the evaluator is later hardened to re-derive roots, this test
    should be updated to assert such forged evidence FAILS."""
    lane_kinds = sorted(APP_ROOT_LANE_KINDS)

    def _check(check_id: str, mode: str, root: str, src: str, path: str) -> dict:
        return {
            "check_id": check_id, "mode": mode, "source_kind": "release_replay",
            "observed_root": root, "recomputed_root": root,      # self-consistent, NOT re-derived
            "source_state_hash": src, "required_lane_kinds": lane_kinds,
            "live_path": path, "checked_at": _PINNED_NOW - 30,
        }

    forged = attach_production_app_root_jmt_hash_v1({
        "schema": APP_ROOT_JMT_EVIDENCE_SCHEMA_V1,
        "evidence_kind": "live_replay",
        "root_system": "typed_app_root_jmt_v1",
        "required_lane_kinds": lane_kinds,
        "live_root_checks": [
            _check("plain-dex-snapshot", "plain_dex_snapshot_live_root", "11" * 32, "21" * 32, "p"),
            _check("tau-wrapper", "tau_app_state_wrapper_live_root", "12" * 32, "22" * 32, "t"),
            _check("pre-snapshot-header", "local_block_pre_snapshot_header", "13" * 32, "23" * 32, "h"),
        ],
        "negative_checks": [{
            "check_id": "lane-tamper", "mutation": "lane_tamper_rejected",
            "source_kind": "release_replay", "rejected": True, "checked_at": _PINNED_NOW - 30,
        }],
        "issued_at": _PINNED_NOW - 20,
    })
    result = evaluate_production_app_root_jmt_evidence_v1(forged, now=_PINNED_NOW)
    # Current behavior: forged-but-well-formed evidence is accepted -> the gap.
    assert result["ok"] is True
    # The roots are pure filler, proving the evaluator did not re-derive them.
    assert forged["live_root_checks"][0]["observed_root"] == "11" * 32


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
