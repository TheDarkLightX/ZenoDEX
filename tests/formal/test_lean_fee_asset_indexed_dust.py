from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PROOF = ROOT / "lean-mathlib" / "Proofs" / "FeeAssetIndexedDust.lean"
CLAIMS = (
    "target_asset_exact_conservation",
    "apply_one_preserves_conserved",
    "all_other_assets_unchanged",
    "admissible_after_distinct_update",
    "distinct_asset_updates_commute",
    "target_dust_claim_satisfies_asset_equation",
    "no_asset_a_dust_can_satisfy_asset_b_equation",
    "witness_target_conservation",
    "witness_cross_asset_dust_rejected",
)
FORBIDDEN_PROOF_TOKENS = ("sorry", "admit", "axiom", "unsafe")


def test_fee_asset_indexed_dust_theorems_compile() -> None:
    lake = shutil.which("lake")
    assert lake is not None, "formal claim gate requires the lake executable"
    result = subprocess.run(
        [lake, "env", "lean", str(PROOF)],
        cwd=ROOT / "lean-mathlib",
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=240,
        check=False,
    )
    assert result.returncode == 0, result.stdout + result.stderr


def test_fee_asset_indexed_dust_claim_surface_is_explicit_and_clean() -> None:
    source = PROOF.read_text(encoding="utf-8")
    lowered = source.lower()
    for token in FORBIDDEN_PROOF_TOKENS:
        assert re.search(rf"\b{re.escape(token)}\b", lowered) is None
    for claim in CLAIMS:
        assert re.search(rf"\btheorem\s+{re.escape(claim)}\b", source) is not None
    assert "Python immutable-map ownership" in source
    assert "full refinement from the runtime" in source
