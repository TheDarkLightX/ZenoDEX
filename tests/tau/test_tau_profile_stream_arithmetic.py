from __future__ import annotations

from pathlib import Path

from tools.check_tau_profile_stream_arithmetic import STRICT_TAU_BLOCKED_STATUS, build_report


ROOT = Path(__file__).resolve().parents[2]
REQUIRED_SETTLEMENT_ARITHMETIC_SPECS = {
    "src/tau_specs/recommended/settlement_price_stability_v1.tau",
    "src/tau_specs/recommended/settlement_price_rails_aligned_v1.tau",
    "src/tau_specs/recommended/settlement_v1_proof_gate.tau",
    "src/tau_specs/recommended/settlement_v2_buyback_proof_gate.tau",
    "src/tau_specs/recommended/settlement_v3_buyback_floor_proof_gate.tau",
    "src/tau_specs/recommended/settlement_v4_buyback_floor_rebate_lock_proof_gate.tau",
    "src/tau_specs/recommended/settlement_v5_aligned_compact_bundle.tau",
}


def test_profiled_stream_add_sub_specs_are_quarantined() -> None:
    report = build_report()
    assert report["ok"], "\n".join(report["errors"])
    assert report["findings"], "expected at least one profiled stream arithmetic finding"
    assert all(row["marker_ok"] for row in report["findings"])


def test_settlement_stream_arithmetic_specs_keep_tau_level_blocker() -> None:
    report = build_report()
    settlement_findings = [row for row in report["findings"] if row["component"] == "settlement"]
    assert settlement_findings, "expected profiled settlement stream arithmetic findings"
    assert all(row["status"] == STRICT_TAU_BLOCKED_STATUS for row in settlement_findings)
    profiled_paths = {row["spec_path"] for row in settlement_findings}
    assert REQUIRED_SETTLEMENT_ARITHMETIC_SPECS <= profiled_paths


def test_settlement_price_stability_remains_native_tau_arithmetic() -> None:
    direct_delta_patterns = (
        (
            "curr - prev < { #x0032 }:bv[16]",
            "prev - curr < { #x0032 }:bv[16]",
        ),
        (
            "i2[t]:bv[16] - i1[t]:bv[16] < { #x0032 }:bv[16]",
            "i1[t]:bv[16] - i2[t]:bv[16] < { #x0032 }:bv[16]",
        ),
    )

    for spec_rel in REQUIRED_SETTLEMENT_ARITHMETIC_SPECS:
        text = (ROOT / spec_rel).read_text(encoding="utf-8")
        assert "price_stability_ok" not in text
        assert "price_stability_flag" not in text
        assert "stable_ok (sbf)" not in text

    helper_specs = [
        "src/tau_specs/recommended/settlement_price_stability_v1.tau",
        "src/tau_specs/recommended/settlement_v1_proof_gate.tau",
        "src/tau_specs/recommended/settlement_v2_buyback_proof_gate.tau",
        "src/tau_specs/recommended/settlement_v3_buyback_floor_proof_gate.tau",
        "src/tau_specs/recommended/settlement_v4_buyback_floor_rebate_lock_proof_gate.tau",
    ]
    for spec_rel in helper_specs:
        text = (ROOT / spec_rel).read_text(encoding="utf-8")
        assert any(all(pattern in text for pattern in pair) for pair in direct_delta_patterns)

    compact_text = (ROOT / "src/tau_specs/recommended/settlement_v5_aligned_compact_bundle.tau").read_text(
        encoding="utf-8"
    )
    assert "i7[t]:bv[16] - i6[t]:bv[16] < { #x0032 }:bv[16]" in compact_text
    assert "i6[t]:bv[16] - i7[t]:bv[16] < { #x0032 }:bv[16]" in compact_text
