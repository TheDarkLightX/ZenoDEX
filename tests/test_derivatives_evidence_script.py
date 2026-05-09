from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_derivatives_evidence_runner_covers_decomposed_funding_rate_lane() -> None:
    script = (ROOT / "tools" / "run_derivatives_evidence.sh").read_text(encoding="utf-8")

    assert "tests/core/test_funding_rate_decomposed_parity.py" in script
    assert "src/kernels/dex/funding_rate_market_v1.yaml" in script
    assert "src/kernels/dex/funding_rate_settlement_witness_v1_1.yaml" in script
    assert "src/kernels/dex/funding_rate_market_v1_1.yaml" in script
    assert "$VERIFY_ROOT/funding_rate_settlement_witness_v1_1" in script
