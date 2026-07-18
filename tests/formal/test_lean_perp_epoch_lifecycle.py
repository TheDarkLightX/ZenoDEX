from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path

CLAIMS = (
    "published_price_blocks_epoch_advance",
    "open_allows_epoch_advance",
    "settled_allows_epoch_advance",
    "advance_allowed_iff_not_published",
    "unseen_oracle_blocks_settlement",
    "zero_index_blocks_settlement",
    "stale_by_one_blocks_settlement",
    "exact_freshness_boundary_allows_settlement",
    "same_epoch_oracle_blocks_settlement",
    "wrong_clearing_epoch_blocks_settlement",
    "missing_clearing_price_blocks_settlement",
)
FORBIDDEN_PROOF_TOKENS = ("sorry", "admit", "axiom", "unsafe", "native_decide")


def _paths() -> tuple[str, Path, Path]:
    lake = shutil.which("lake")
    if lake is None:
        raise AssertionError("formal claim gate requires the lake executable")
    root = Path(__file__).resolve().parents[2]
    lean_dir = root / "lean-mathlib"
    proof = lean_dir / "Proofs" / "PerpEpochLifecycle.lean"
    return lake, lean_dir, proof


def test_perp_epoch_lifecycle_theorems_compile() -> None:
    lake, lean_dir, proof = _paths()
    result = subprocess.run(
        [lake, "env", "lean", str(proof)],
        cwd=lean_dir,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=240,
        check=False,
    )
    assert result.returncode == 0, result.stdout + result.stderr


def test_perp_epoch_lifecycle_claim_surface_is_explicit_and_clean() -> None:
    _, _, proof = _paths()
    source = proof.read_text(encoding="utf-8")
    lowered = source.lower()
    for token in FORBIDDEN_PROOF_TOKENS:
        assert re.search(rf"\b{re.escape(token)}\b", lowered) is None
    for claim in CLAIMS:
        assert re.search(rf"\btheorem\s+{re.escape(claim)}\b", source) is not None
