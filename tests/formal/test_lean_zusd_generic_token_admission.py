from __future__ import annotations

import ast
import re
import shutil
import subprocess
from itertools import product
from pathlib import Path

from src.core.zusd_generic_token_admission import (
    CanonicalZUSDRecipientClass,
    GenericTokenAction,
    GenericTokenAdmissionCommand,
    TokenAssetClass,
    TokenWriterRole,
    evaluate_generic_token_admission,
)

CLAIMS = (
    "generic_canonical_mint_rejected",
    "generic_canonical_burn_rejected",
    "stability_pool_transfer_rejected",
    "every_reserved_protocol_location_rejects_generic_canonical_transfer",
    "ordinary_canonical_transfer_admitted",
    "generic_canonical_admission_iff_ordinary_transfer",
    "monetary_authority_routes_to_separate_kernel",
    "every_step_preserves_canonical_supply",
    "every_step_has_zero_canonical_supply_delta",
    "every_rejection_is_exact_prestate_noop",
    "decision_cases_exhaustive",
)
FORBIDDEN_PROOF_TOKENS = ("sorry", "admit", "axiom", "unsafe", "native_decide")


def _paths() -> tuple[str, Path, Path]:
    lake = shutil.which("lake")
    if lake is None:
        raise AssertionError("formal claim gate requires the lake executable")
    root = Path(__file__).resolve().parents[2]
    lean_dir = root / "lean-mathlib"
    return lake, lean_dir, lean_dir / "Proofs" / "ZUSDGenericTokenAdmission.lean"


def test_zusd_generic_token_admission_theorems_compile() -> None:
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


def test_zusd_generic_token_admission_claim_surface_is_explicit_and_clean() -> None:
    _, _, proof = _paths()
    source = proof.read_text(encoding="utf-8")
    lowered = source.lower()
    for token in FORBIDDEN_PROOF_TOKENS:
        assert re.search(rf"\b{re.escape(token)}\b", lowered) is None
    for claim in CLAIMS:
        assert re.search(rf"\btheorem\s+{re.escape(claim)}\b", source) is not None


def test_lean_decision_vector_matches_executable_python_core(tmp_path: Path) -> None:
    lake, lean_dir, _proof = _paths()
    compile_result = subprocess.run(
        [lake, "build", "Proofs.ZUSDGenericTokenAdmission"],
        cwd=lean_dir,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=240,
        check=False,
    )
    assert compile_result.returncode == 0, compile_result.stdout + compile_result.stderr

    probe = tmp_path / "ZUSDGenericTokenAdmissionVector.lean"
    probe.write_text(
        "import Proofs.ZUSDGenericTokenAdmission\n"
        "#eval ZenoDEX.ZUSDGenericTokenAdmission.exhaustiveTransitionCSV\n",
        encoding="utf-8",
    )
    result = subprocess.run(
        [lake, "env", "lean", str(probe)],
        cwd=lean_dir,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=240,
        check=False,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    output_lines = [line.strip() for line in result.stdout.splitlines() if line.strip()]
    assert output_lines
    lean_transition_values = [
        int(value) for value in ast.literal_eval(output_lines[-1]).split(",")
    ]

    python_transition_values: list[int] = []
    for supply in (0, 1, (1 << 32) - 1):
        for action, asset, writer_role, recipient_class in product(
            GenericTokenAction,
            TokenAssetClass,
            TokenWriterRole,
            CanonicalZUSDRecipientClass,
        ):
            decision = evaluate_generic_token_admission(
                GenericTokenAdmissionCommand(
                    action=action,
                    asset_class=asset,
                    writer_role=writer_role,
                    recipient_class=recipient_class,
                )
            )
            python_transition_values.extend((int(decision.code), supply))

    assert len(lean_transition_values) == len(python_transition_values) == 648
    assert lean_transition_values == python_transition_values
