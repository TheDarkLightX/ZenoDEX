from __future__ import annotations

import os
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LEAN_PROJECT = ROOT / "lean-mathlib"
PROOF = LEAN_PROJECT / "Proofs" / "ZDEXTokenomicsBuybackTransitionV1.lean"
DEPENDENCIES = (
    LEAN_PROJECT / "Proofs" / "ZDEXBuybackPriceSafetyV1.lean",
    LEAN_PROJECT / "Proofs" / "ZDEXBuybackSpendV1.lean",
    LEAN_PROJECT / "Proofs" / "ZDEXSpotBuybackTransitionV1.lean",
)

# Theorems whose axiom footprint must stay inside the Lean core axioms. A
# `sorryAx` or `Lean.ofReduceBool` entry would mean the claim rests on an
# unproved placeholder or on compiler-level `native_decide` evaluation.
AXIOM_CHECKED_THEOREMS = (
    "accepted_transition_conserves_fee",
    "accepted_buyback_reserve_transition",
    "accepted_purchased_equals_burned",
    "accepted_supply_reduction_is_exact",
    "accepted_tokenomics_quote_conservation",
    "accepted_preserves_lane_well_formedness",
    "accepted_cadence_advances_to_the_execution_height",
    "accepted_discharges_the_exact_spot_obligation",
    "accepted_effect_rows_are_nonzero",
    "rejected_is_exact_noop",
    "nonvacuity_accepts",
    "route_ports_are_exactly_paired",
    "route_supply_reduction_matches_spot_output",
    "effect_plan_root_is_independent_of_the_consumed_obligation",
    "nonvacuity_valid",
    "cadence_boundary_is_live",
    "rounded_fee_fixture_is_live",
    "authority_malformed_witness_rejects",
    "release_mismatch_witness_rejects",
    "profile_mismatch_witness_rejects",
    "state_commitment_mismatch_witness_rejects",
    "policy_mismatch_witness_rejects",
    "lane_malformed_witness_rejects",
    "zero_fee_witness_rejects",
    "cadence_ineligible_witness_rejects",
    "arithmetic_out_of_range_witness_rejects",
    "amount_out_of_range_witness_rejects",
    "minimum_spend_mismatch_witness_rejects",
    "terminal_obligation_substitution_is_rejected",
    "purchased_port_substitution_is_rejected",
    "quote_port_amount_substitution_is_rejected",
    "command_occurrence_separates_the_quote_flow",
)

PERMITTED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})


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


def _cached_dependency_paths(lean: Path) -> tuple[Path, ...]:
    """Resolve the pinned Lake dependency cache without ambient LEAN_PATH."""

    packages = LEAN_PROJECT / ".lake" / "packages"
    package_builds = tuple(
        build
        for package in sorted(packages.iterdir(), key=lambda path: path.name)
        if (build := package.resolve() / ".lake" / "build" / "lib" / "lean").is_dir()
    )
    if not any((build / "Mathlib.olean").is_file() for build in package_builds):
        raise RuntimeError("pinned Mathlib build cache is unavailable")
    toolchain_lib = lean.parent.parent / "lib" / "lean"
    if not toolchain_lib.is_dir():
        raise RuntimeError("pinned Lean standard-library cache is unavailable")
    project_build = LEAN_PROJECT / ".lake" / "build" / "lib" / "lean"
    return package_builds + ((project_build,) if project_build.is_dir() else ()) + (
        toolchain_lib,
    )


def _build_dependency_cache(lean: Path, cache: Path) -> dict[str, str]:
    """Compile the imported proof modules with the pinned toolchain."""

    (cache / "Proofs").mkdir(parents=True, exist_ok=True)
    env = dict(os.environ)
    env["LEAN_PATH"] = os.pathsep.join(
        (str(cache), *(str(path) for path in _cached_dependency_paths(lean)))
    )
    for dependency in DEPENDENCIES:
        subprocess.run(
            [
                str(lean),
                "-R",
                str(LEAN_PROJECT),
                "-o",
                str(cache / "Proofs" / f"{dependency.stem}.olean"),
                str(dependency),
            ],
            cwd=LEAN_PROJECT,
            check=True,
            env=env,
        )
    return env


def test_tokenomics_buyback_proof_has_closed_successor_surface() -> None:
    # Arrange
    source = PROOF.read_text(encoding="utf-8")

    # Act / Assert
    assert re.search(r"\b(?:sorry|admit|axiom|native_decide|unsafe)\b", source) is None
    for required_declaration in (
        "structure TokenomicsState",
        "structure FeeAllocationPolicy",
        "structure DestinationAmounts",
        "structure TokenomicsBuybackRelease",
        "structure ProfileAuthorization",
        "structure ObligationDischarge",
        "structure Journal",
        "def feeCharged",
        "def allocationOf",
        "def quoteSpend",
        "def purchasedZDEX",
        "def acceptedPostState",
        "def acceptedEffects",
        "def acceptedDischarge",
        "def routeCoordinationObligationId",
        "def GuardHolds",
        "def rejectOrder",
        "theorem feeDestinationCode_injective",
        "theorem tokenomicsStateCommitment_injective",
        "theorem releaseCommitment_injective",
        "theorem feeAllocationPolicyCommitment_injective",
        "theorem destinationPrincipal_injective",
        "theorem self_consistent_profile_id_no_alias",
        "theorem nat_div_add_div_le",
        "theorem allocated_total_le_fee",
        "theorem accepted_fee_conservation",
        "theorem accepted_transition_conserves_fee",
        "theorem accepted_spend_respects_every_governed_limit",
        "theorem accepted_buyback_reserve_transition",
        "theorem accepted_quote_port_carries_the_derived_spend",
        "theorem accepted_purchased_equals_burned",
        "theorem accepted_supply_reduction_is_exact",
        "theorem accepted_tokenomics_quote_conservation",
        "theorem accepted_preserves_lane_well_formedness",
        "theorem accepted_cadence_advances_to_the_execution_height",
        "theorem accepted_preserves_unrelated_tokenomics_commitments",
        "theorem accepted_consumes_committed_fee_ingress",
        "theorem accepted_effect_rows_are_nonzero",
        "theorem accepted_emits_a_single_burn_row",
        "theorem accepted_effect_rows_use_declared_assets",
        "theorem accepted_emits_one_bound_tokenomics_lane_write",
        "theorem accepted_buyback_rows_are_gross_not_netted",
        "theorem post_state_is_independent_of_the_consumed_obligation",
        "theorem effect_plan_root_is_independent_of_the_consumed_obligation",
        "theorem derived_spend_is_independent_of_both_spot_ports",
        "theorem accepted_discharges_the_exact_spot_obligation",
        "theorem accepted_route_obligation_is_nonzero",
        "theorem accepted_journal_binds_exact_transition",
        "theorem transition_is_total",
        "theorem rejected_is_exact_noop",
        "theorem firstReject_some_is_first_failure",
        "theorem nonvacuity_valid",
        "theorem nonvacuity_accepts",
        "theorem nonvacuity_derived_values",
        "theorem cadence_boundary_is_live",
        "theorem rounded_fee_fixture_is_live",
        "theorem authority_malformed_witness_rejects",
        "theorem release_mismatch_witness_rejects",
        "theorem profile_mismatch_witness_rejects",
        "theorem state_commitment_mismatch_witness_rejects",
        "theorem policy_mismatch_witness_rejects",
        "theorem lane_malformed_witness_rejects",
        "theorem zero_fee_witness_rejects",
        "theorem cadence_ineligible_witness_rejects",
        "theorem arithmetic_out_of_range_witness_rejects",
        "theorem amount_out_of_range_witness_rejects",
        "theorem minimum_spend_mismatch_witness_rejects",
        "theorem terminal_obligation_substitution_is_rejected",
        "theorem purchased_port_substitution_is_rejected",
        "theorem quote_port_amount_substitution_is_rejected",
        "theorem rejected_witness_is_an_exact_noop",
        "theorem command_occurrence_separates_the_quote_flow",
        "theorem route_ports_are_exactly_paired",
        "theorem route_supply_reduction_matches_spot_output",
        "theorem route_discharges_the_spot_issued_obligation",
    ):
        assert required_declaration in source

    # The successor leaf consumes the Spot leaf's exact port and obligation
    # types rather than re-declaring them.
    assert "import Proofs.ZDEXSpotBuybackTransitionV1" in source
    assert "import Proofs.ZDEXBuybackSpendV1" in source
    assert "Proofs.ZDEXBuybackSpendV1.selectedQuoteSpend" in source
    assert "Proofs.ZDEXSpotBuybackTransitionV1.flowIdentityCommitment" in source
    assert "abbrev SpotObligation := Proofs.ZDEXSpotBuybackTransitionV1.TerminalObligation" in source
    assert "mustBurnPurchasedZDEX" in source
    assert "zdexTokenSupply" in source
    assert "consumedObjectIds := []" in source

    # Conservative claim ceiling.
    assert "does not establish canonical-byte encoding" in source
    assert "Python/Rust parity" in source
    assert "RISC0 receipt validity" in source
    assert "mount, settlement, production, or value-moving authority is created." in source


def test_tokenomics_buyback_proof_checks_with_pinned_lean(tmp_path: Path) -> None:
    # Arrange
    lean = _pinned_lean_executable()
    env = _build_dependency_cache(lean, tmp_path / "lean")

    # Act / Assert
    subprocess.run(
        [str(lean), "-R", str(LEAN_PROJECT), str(PROOF)],
        cwd=LEAN_PROJECT,
        check=True,
        env=env,
    )


def test_tokenomics_buyback_theorems_use_only_core_axioms(tmp_path: Path) -> None:
    # Arrange
    lean = _pinned_lean_executable()
    cache = tmp_path / "lean"
    env = _build_dependency_cache(lean, cache)
    subprocess.run(
        [
            str(lean),
            "-R",
            str(LEAN_PROJECT),
            "-o",
            str(cache / "Proofs" / f"{PROOF.stem}.olean"),
            str(PROOF),
        ],
        cwd=LEAN_PROJECT,
        check=True,
        env=env,
    )
    query = tmp_path / "AxiomQuery.lean"
    query.write_text(
        "import Proofs.ZDEXTokenomicsBuybackTransitionV1\n"
        "open Proofs.ZDEXTokenomicsBuybackTransitionV1\n"
        + "".join(f"#print axioms {name}\n" for name in AXIOM_CHECKED_THEOREMS),
        encoding="utf-8",
    )

    # Act
    printed = subprocess.run(
        [str(lean), "-R", str(LEAN_PROJECT), str(query)],
        cwd=LEAN_PROJECT,
        check=True,
        capture_output=True,
        text=True,
        env=env,
    ).stdout

    # Assert
    for name in AXIOM_CHECKED_THEOREMS:
        assert name in printed
    assert "sorryAx" not in printed
    assert "ofReduceBool" not in printed
    reported = set(re.findall(r"depends on axioms: \[([^\]]*)\]", printed))
    for group in reported:
        for axiom in (entry.strip() for entry in group.split(",")):
            assert axiom in PERMITTED_AXIOMS, axiom
