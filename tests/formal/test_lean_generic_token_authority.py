from __future__ import annotations

import ast
import re
import shutil
import subprocess
from itertools import product
from pathlib import Path

from src.core.generic_token_authority import (
    U32_MAX,
    GenericTokenAssetAuthority,
    GenericTokenAuthorityState,
    GenericTokenSupplyAction,
    GenericTokenSupplyCommand,
    GenericTokenSupplyRejectCode,
    apply_generic_token_supply_command,
)

CLAIMS = (
    "rejection_is_exact_prestate_noop",
    "accepted_transfer_preserves_supply",
    "accepted_mint_has_exact_delta",
    "accepted_burn_has_exact_delta",
    "accepted_mint_requires_committed_authority",
    "accepted_transition_preserves_u32_bound",
    "accepted_update_is_asset_local",
    "decision_cases_exhaustive",
)
FORBIDDEN_PROOF_TOKENS = ("sorry", "admit", "axiom", "unsafe", "native_decide")

ASSET = "11" * 32
AUTHORITY = "22" * 48
OTHER_ACTOR = "33" * 48
RECIPIENT = "44" * 48

REJECT_CODES = {
    GenericTokenSupplyRejectCode.INVALID_AMOUNT: 1,
    GenericTokenSupplyRejectCode.UNREGISTERED_ASSET: 2,
    GenericTokenSupplyRejectCode.RECIPIENT_REQUIRED: 3,
    GenericTokenSupplyRejectCode.SELF_TRANSFER: 4,
    GenericTokenSupplyRejectCode.MINT_DISABLED: 5,
    GenericTokenSupplyRejectCode.UNAUTHORIZED_MINT: 6,
    GenericTokenSupplyRejectCode.SUPPLY_OVERFLOW: 7,
    GenericTokenSupplyRejectCode.SUPPLY_UNDERFLOW: 8,
}


def _paths() -> tuple[str, Path, Path]:
    lake = shutil.which("lake")
    if lake is None:
        raise AssertionError("formal claim gate requires the lake executable")
    root = Path(__file__).resolve().parents[2]
    lean_dir = root / "lean-mathlib"
    return lake, lean_dir, lean_dir / "Proofs" / "GenericTokenAuthority.lean"


def test_generic_token_authority_theorems_compile() -> None:
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
    assert result.stdout == ""
    assert result.stderr == ""


def test_generic_token_authority_claim_surface_is_explicit_and_clean() -> None:
    _, _, proof = _paths()
    source = proof.read_text(encoding="utf-8")
    lowered = source.lower()
    for token in FORBIDDEN_PROOF_TOKENS:
        assert re.search(rf"\b{re.escape(token)}\b", lowered) is None
    for claim in CLAIMS:
        assert re.search(rf"\btheorem\s+{re.escape(claim)}\b", source) is not None


def _python_transition_vector() -> list[int]:
    values: list[int] = []
    booleans = (False, True)
    for supply in (0, 1, U32_MAX):
        for (
            action,
            amount,
            registered,
            recipient_present,
            self_transfer,
            mint_enabled,
            mint_authorized,
        ) in product(
            GenericTokenSupplyAction,
            (0, 1, 2, U32_MAX),
            booleans,
            booleans,
            booleans,
            booleans,
            booleans,
        ):
            state = GenericTokenAuthorityState(
                assets=(
                    GenericTokenAssetAuthority(
                        asset_id=ASSET,
                        total_supply_units=supply,
                        mint_authority_pubkey=AUTHORITY if mint_enabled else None,
                    ),
                )
                if registered
                else ()
            )
            actor = AUTHORITY if mint_authorized else OTHER_ACTOR
            recipient = (
                None
                if not recipient_present
                else actor
                if self_transfer
                else RECIPIENT
            )
            decision = apply_generic_token_supply_command(
                state,
                GenericTokenSupplyCommand(
                    action=action,
                    asset_id=ASSET,
                    actor_pubkey=actor,
                    amount_units=amount,
                    recipient_pubkey=recipient,
                ),
            )
            if decision.accepted:
                assert decision.next_state is not None
                post_asset = decision.next_state.get_asset(ASSET)
                post_supply = supply if post_asset is None else post_asset.total_supply_units
                values.extend((0, post_supply))
            else:
                assert decision.reject_code is not None
                values.extend((REJECT_CODES[decision.reject_code], supply))
    return values


def test_lean_decision_vector_matches_executable_python_core(tmp_path: Path) -> None:
    lake, lean_dir, _proof = _paths()
    compile_result = subprocess.run(
        [lake, "build", "Proofs.GenericTokenAuthority"],
        cwd=lean_dir,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=240,
        check=False,
    )
    assert compile_result.returncode == 0, compile_result.stdout + compile_result.stderr

    probe = tmp_path / "GenericTokenAuthorityVector.lean"
    probe.write_text(
        "import Proofs.GenericTokenAuthority\n"
        "#eval ZenoDEX.GenericTokenAuthority.exhaustiveTransitionCSV\n",
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
    lean_values = [int(value) for value in ast.literal_eval(output_lines[-1]).split(",")]
    python_values = _python_transition_vector()

    assert len(lean_values) == len(python_values) == 2304
    assert lean_values == python_values
