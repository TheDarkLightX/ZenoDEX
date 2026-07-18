from __future__ import annotations

import ast
import re
import shutil
import subprocess
from dataclasses import replace
from pathlib import Path

from src.core.zusd_monetary_policy_binding import (
    ZUSD_MONETARY_POLICY_FIELDS,
    ZUSDMonetaryPolicyBinding,
    evaluate_zusd_policy_binding,
)

CLAIMS = (
    "mismatches_eq_nil_iff",
    "decide_is_matched_iff",
    "decide_self_is_matched",
    "mismatch_fields_are_canonical",
    "mismatches_preserve_canonical_order",
    "mismatches_nodup",
    "chain_id_only_projection",
    "canonical_zusd_asset_only_projection",
    "oracle_pubkey_only_projection",
    "liquidation_gas_comp_fixed_only_projection",
    "liquidation_gas_comp_bps_only_projection",
    "borrow_fee_floor_only_projection",
    "borrow_fee_max_only_projection",
    "host_protocol_fee_share_only_projection",
    "fee_stake_asset_only_projection",
    "staking_activation_delay_only_projection",
)
FORBIDDEN_PROOF_TOKENS = ("sorry", "admit", "axiom", "unsafe", "native_decide")

ASSET_A = "0x" + "11" * 32
ASSET_B = "0x" + "22" * 32
STAKE_ASSET = "0x" + "33" * 32
ORACLE = "0x" + "44" * 48


def _paths() -> tuple[str, Path, Path]:
    lake = shutil.which("lake")
    if lake is None:
        raise AssertionError("formal claim gate requires the lake executable")
    root = Path(__file__).resolve().parents[2]
    lean_dir = root / "lean-mathlib"
    proof = lean_dir / "Proofs" / "ZUSDMonetaryPolicyBinding.lean"
    return lake, lean_dir, proof


def _base_binding() -> ZUSDMonetaryPolicyBinding:
    return ZUSDMonetaryPolicyBinding(
        chain_id="tau-policy-base",
        canonical_zusd_asset=ASSET_A,
        oracle_pubkey=None,
        liquidation_gas_comp_fixed_collateral_e8=0,
        liquidation_gas_comp_bps=0,
        borrow_fee_floor_bps=0,
        borrow_fee_max_bps=100,
        host_protocol_fee_share_bps=0,
        fee_stake_asset_id=None,
        staking_activation_delay_epochs=0,
    )


def _binding_for_mask(mask: int) -> ZUSDMonetaryPolicyBinding:
    base = _base_binding()
    replacements: dict[str, object] = {
        "chain_id": "tau-policy-other",
        "canonical_zusd_asset": ASSET_B,
        "oracle_pubkey": ORACLE,
        "liquidation_gas_comp_fixed_collateral_e8": 1,
        "liquidation_gas_comp_bps": 1,
        "borrow_fee_floor_bps": 1,
        "borrow_fee_max_bps": 101,
        "host_protocol_fee_share_bps": 1,
        "fee_stake_asset_id": STAKE_ASSET,
        "staking_activation_delay_epochs": 1,
    }
    return replace(
        base,
        **{
            field_name: replacements[field_name]
            for bit, field_name in enumerate(ZUSD_MONETARY_POLICY_FIELDS)
            if mask & (1 << bit)
        },
    )


def test_zusd_monetary_policy_binding_theorems_compile() -> None:
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


def test_zusd_monetary_policy_binding_claim_surface_is_explicit_and_clean() -> None:
    _, _, proof = _paths()
    source = proof.read_text(encoding="utf-8")
    lowered = source.lower()
    for token in FORBIDDEN_PROOF_TOKENS:
        assert re.search(rf"\b{re.escape(token)}\b", lowered) is None
    for claim in CLAIMS:
        assert re.search(rf"\btheorem\s+{re.escape(claim)}\b", source) is not None


def test_lean_mismatch_vector_matches_executable_python_core(tmp_path: Path) -> None:
    lake, lean_dir, _proof = _paths()
    compile_result = subprocess.run(
        [lake, "build", "Proofs.ZUSDMonetaryPolicyBinding"],
        cwd=lean_dir,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=240,
        check=False,
    )
    assert compile_result.returncode == 0, compile_result.stdout + compile_result.stderr

    probe = tmp_path / "ZUSDMonetaryPolicyBindingVector.lean"
    probe.write_text(
        "import Proofs.ZUSDMonetaryPolicyBinding\n"
        "#eval ZenoDEX.ZUSDMonetaryPolicyBinding.exhaustiveMismatchMaskCSV\n",
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
    lean_masks = [int(value) for value in ast.literal_eval(output_lines[-1]).split(",")]

    base = _base_binding()
    python_masks: list[int] = []
    for mask in range(1 << len(ZUSD_MONETARY_POLICY_FIELDS)):
        decision = evaluate_zusd_policy_binding(
            committed=base,
            configured=_binding_for_mask(mask),
        )
        observed_mask = sum(
            1 << ZUSD_MONETARY_POLICY_FIELDS.index(field_name)
            for field_name in decision.mismatch_fields
        )
        python_masks.append(observed_mask)

    assert len(lean_masks) == len(python_masks) == 1024
    assert lean_masks == python_masks == list(range(1024))
