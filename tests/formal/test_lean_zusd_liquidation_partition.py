from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path

DECLARATIONS = (
    "debtToOffset_le_debt",
    "debt_partition",
    "collateralToStabilityPool_le_collateral",
    "collateral_partition",
    "full_redistribution_when_pool_empty",
    "full_offset_when_debt_le_principal",
)
FORBIDDEN = ("sorry", "admit", "axiom", "unsafe", "native_decide")


def test_zusd_liquidation_partition_claim_surface_typechecks() -> None:
    lake = shutil.which("lake")
    assert lake is not None, "formal claim gate requires lake"
    root = Path(__file__).resolve().parents[2]
    lean_dir = root / "lean-mathlib"
    target = lean_dir / "Proofs" / "ZUSDLiquidationPartition.lean"
    source = target.read_text(encoding="utf-8")

    for declaration in DECLARATIONS:
        assert re.search(rf"\btheorem\s+{declaration}\b", source)
    for forbidden in FORBIDDEN:
        assert re.search(rf"\b{forbidden}\b", source) is None

    checked = subprocess.run(
        [lake, "env", "lean", str(target)],
        cwd=lean_dir,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=240,
        check=False,
    )
    assert checked.returncode == 0, checked.stdout + checked.stderr
