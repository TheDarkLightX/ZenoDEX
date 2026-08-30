from __future__ import annotations

import os
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LEAN_PROJECT = ROOT / "lean-mathlib"
PROOF = LEAN_PROJECT / "Proofs" / "ZDEXSpotBuybackTransitionV1.lean"
PRICE_PROOF = LEAN_PROJECT / "Proofs" / "ZDEXBuybackPriceSafetyV1.lean"


def _pinned_lean_executable() -> Path:
    toolchain = (LEAN_PROJECT / "lean-toolchain").read_text(encoding="utf-8").strip()
    expected_version = toolchain.rsplit(":v", maxsplit=1)[-1]
    resolved = subprocess.run(
        ["elan", "which", "lean"],
        cwd=LEAN_PROJECT,
        check=True,
        capture_output=True,
        text=True,
    )
    lean = Path(resolved.stdout.strip())
    version = subprocess.run(
        [str(lean), "--version"],
        cwd=LEAN_PROJECT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout
    assert lean.is_file()
    assert f"version {expected_version}" in version
    return lean


def test_spot_buyback_proof_has_closed_command_specific_surface() -> None:
    # Arrange
    source = PROOF.read_text(encoding="utf-8")

    # Act / Assert
    assert re.search(r"\b(?:sorry|admit|axiom|unsafe)\b", source) is None
    for required_declaration in (
        "structure PoolDefinition",
        "theorem encodeNats_injective",
        "def derivePoolId",
        "theorem derivePoolId_injective",
        "structure SpotLaneState",
        "def SpotLaneStateWellFormed",
        "theorem spotLaneStateCommitment_injective",
        "def RegistryCanonical",
        "structure ProfileAuthorization",
        "theorem self_consistent_profile_id_no_alias",
        "structure OracleOccurrence",
        "theorem oracleRegistryCommitment_injective",
        "structure QuoteInputPort",
        "structure PriceEnvelope",
        "def purchasedZDEX",
        "theorem priceSafe_iff_existing_contract",
        "def PriceArithmeticFits",
        "structure Journal",
        "theorem releaseCommitment_injective",
        "theorem executionPolicyCommitment_injective",
        "theorem pricePolicyCommitment_no_alias",
        "theorem flowIdentityCommitment_injective",
        "theorem terminalObligationFullCommitment_injective",
        "def GuardHolds",
        "theorem firstReject_some_is_first_failure",
        "theorem rejected_is_exact_noop",
        "theorem valid_selected_definition_matches_policy",
        "theorem accepted_selected_pool_lookup_exact",
        "theorem accepted_preserves_every_sibling_pool",
        "theorem accepted_registry_remains_canonical",
        "theorem accepted_derives_exact_pool_effects_and_ports",
        "theorem accepted_price_safety_is_over_derived_output",
        "theorem accepted_cpmm_k_nondecreasing",
        "theorem accepted_journal_binds_exact_transition",
        "theorem accepted_spot_value_conservation",
        "theorem accepted_terminal_obligation_is_nonzero_and_context_bound",
        "theorem rounded_fee_fixture_is_live",
        "theorem one_atom_fixture_is_live",
        "theorem arithmetic_out_of_range_fixture_is_live",
        "theorem command_occurrence_separates_both_flow_ids",
        "theorem unauthorized_oracle_provider_rejects",
        "theorem tokenomics_source_provenance_is_required",
        "theorem registered_sibling_curve_is_live",
        "theorem unregistered_sibling_curve_rejects",
        "theorem revoked_sibling_curve_is_not_well_formed",
        "theorem oracle_freshness_boundary_is_exact",
        "theorem machine_height_boundary_is_exact",
        "theorem every_reject_family_has_a_concrete_witness",
        "theorem nonvacuity_accepts",
    ):
        assert required_declaration in source

    assert "protocolFeeShareBps := 0" in source
    assert "consumedObjectIds := []" in source
    assert "mustBurnPurchasedZDEX" in source
    assert "zdexTokenSupply" in source
    assert "It does not establish collision resistance" in source
    assert "Python/Rust parity" in source
    assert "RISC0 receipt validity" in source


def test_spot_buyback_proof_checks_with_pinned_lean(tmp_path: Path) -> None:
    # Arrange
    lean = _pinned_lean_executable()
    proof_cache = tmp_path / "lean"
    price_olean = proof_cache / "Proofs" / "ZDEXBuybackPriceSafetyV1.olean"
    price_olean.parent.mkdir(parents=True)
    subprocess.run(
        [
            str(lean),
            "-R",
            str(LEAN_PROJECT),
            "-o",
            str(price_olean),
            str(PRICE_PROOF),
        ],
        cwd=LEAN_PROJECT,
        check=True,
    )
    env = dict(os.environ)
    inherited_lean_path = env.get("LEAN_PATH")
    env["LEAN_PATH"] = os.pathsep.join(
        path for path in (str(proof_cache), inherited_lean_path) if path
    )

    # Act / Assert
    subprocess.run(
        [str(lean), "-R", str(LEAN_PROJECT), str(PROOF)],
        cwd=LEAN_PROJECT,
        check=True,
        env=env,
    )
