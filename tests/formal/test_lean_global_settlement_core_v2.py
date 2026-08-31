from __future__ import annotations

import hashlib
import inspect
import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path
from typing import TypedDict

import pytest

from src.core.global_economic_state_v2 import GlobalEconomicStateV2
from src.core.global_settlement_types_v2 import (
    ALL_LANE_IDS_V2,
    FEE_RESIDUE_CONTROL_DOMAIN_V2,
    FEE_RESIDUE_PRINCIPAL_V2,
    AssetConservationRowV2,
    EconomicEffectKindV2,
    EconomicEffectRowV2,
    ExternalOutboxEnqueueV2,
    FeeConservationRowV2,
    GlobalEconomicEffectPlanV2,
    LaneWriteV2,
    OracleOccurrenceDeltaV2,
    OracleOccurrenceStateV2,
    TerminalObligationDeltaV2,
    TerminalObligationV2,
)

ROOT = Path(__file__).resolve().parents[2]
LEAN_DIR = ROOT / "lean-mathlib"
CORE = LEAN_DIR / "Proofs" / "GlobalSettlementCoreV2.lean"
REFINEMENT = LEAN_DIR / "Proofs" / "GlobalEconomicStateRefinementV2.lean"
SCANNER = ROOT / "tools" / "scan_lean_proof_placeholders_v1.py"

CORE_NAMESPACE = "Proofs.GlobalSettlementCoreV2"
REFINEMENT_NAMESPACE = "Proofs.GlobalEconomicStateRefinementV2"
PINNED_TOOLCHAIN = "leanprover/lean4:v4.27.0"
PINNED_MODELED_RUNTIME_SOURCES = {
    "src/core/global_settlement_primitives_v2.py":
        "11a26694357812e91b398bddc2b6bbec0a93063731ccd5b23818de1d0c0ca01e",
    "src/core/global_settlement_effect_values_v2.py":
        "a366616f8a11f35d5c69d29c91e1d0b8598ac48499eb44d86d8011c73d30fb9a",
    "src/core/global_settlement_effect_plan_v2.py":
        "e352b67a13ac22e09d31d5aebf94d10aa7f540ef3149050ed2675854f6b839f0",
    "src/core/global_settlement_lifecycle_v2.py":
        "56e658e95dab1ffc7ea8c5358683699a9bc985f7910d03bdc3045838215f7796",
    "src/core/global_settlement_types_v2.py":
        "25624adb564c5b0c610638d707a8c09893afb754b3574299eb9a369d6cf73f39",
    "src/core/global_economic_state_v2.py":
        "2948531057e332a301c0cdd278771040a86eda38f34ca839cd1ec196fc75b12e",
    "src/core/global_economic_state_ownership_v2.py":
        "d29ca85f81d19843ffcc46d0d50270b22ef7d4fa5c3502965fd7c9e45369e4e8",
    "src/core/global_economic_proof_v2.py":
        "087b4df5295d82d112d552bac136b66cf0010f078915c29869d7a427fd8d5705",
    "src/core/global_economic_refinement_checks_v2.py":
        "f8084730492024764f9f2f2008e4e04c7c7d28455358885bd4f6c758eb99f1c6",
    "src/core/global_economic_state_effect_refinement_v2.py":
        "4663cbee5ff7485b65bc68e55058bbe49cbc0ddd0c6e2f9c6b9502928c9713b7",
}


class CompiledPacket(TypedDict):
    root: Path
    lean: Path
    env: dict[str, str]
    outputs: dict[str, subprocess.CompletedProcess[str]]

CORE_THEOREMS = (
    "zero_fits_u128",
    "zero_fits_i128",
    "zero_fits_u64",
    "allLaneIds_length",
    "allLaneIds_codes",
    "allLaneIds_indices",
    "allLaneIds_complete",
    "allLaneIds_noDuplicates",
    "LaneId.index_injective",
    "allEffectKinds_length",
    "allEffectKinds_codes",
    "allEffectKinds_complete",
    "allEffectKinds_noDuplicates",
    "effectPlan_empty_has_six_empty_fields",
    "EffectPlan.ext_six_fields",
    "projectionMatches_implies_net",
    "issuedFor_append",
    "burnedFor_append",
    "issue_ignores_other_asset",
    "burn_ignores_other_asset",
    "empty_effectPlan_admitted",
    "negative_fee_allocation_rejected",
    "fee_projection_mismatch_rejected",
    "netOnlyMutation_has_zero_net",
    "netOnlyMutation_projection_rejected",
)

REFINEMENT_THEOREMS = (
    "accepted_extracts_combined_witness",
    "accepted_preserves_owned_supply",
    "accepted_preserves_liability_backing",
    "accepted_open_terminal_totals_fit_exact_liability_rows",
    "accepted_fee_credit_and_residue_are_exact",
    "accepted_oracles_do_not_exceed_global_height",
    "accepted_has_independent_issue_burn_projections",
    "accepted_has_exact_table_and_supply_effects",
    "accepted_has_exact_lane_write_coverage",
    "accepted_has_exact_terminal_refinement",
    "accepted_has_exact_oracle_refinement",
    "accepted_has_exact_replay_refinement",
    "accepted_replay_is_ordered_and_one_step",
    "accepted_outbox_is_closed_before_o009",
    "accepted_zero_occurrence_is_static",
    "rejected_post_state_is_pre_state",
    "rejected_effect_plan_is_empty",
    "rejected_terminal_and_oracle_plans_are_empty",
    "rejected_consumes_no_occurrence",
    "rejected_is_no_op_bundle",
    "static_global_state_quantities_admitted",
    "static_global_state_verified",
    "combined_verified_relation_is_inhabited",
    "exact_lane_writes_ignore_list_order",
    "changed_lane_requires_exact_write",
    "terminal_delta_requires_owning_lane_write",
    "terminal_member_preserves_identity_and_status_progression",
    "oracle_delta_requires_oracle_lane_write",
    "oracle_member_preserves_height_finality_and_same_height_root",
    "disabled_lane_write_rejected",
    "empty_write_set_rejects_changed_lane",
    "zero_sparse_amount_row_rejected",
    "zero_sparse_supply_row_rejected",
    "replay_occurrence_alias_rejected",
    "oracle_lookup_key_mismatch_rejected",
    "state_bearing_annotation_overflow_rejected",
    "underbacked_claimant_liability_rejected",
    "undercredited_fee_allocation_rejected",
    "zero_fee_conservation_row_rejected",
    "wrong_fee_residue_location_rejected",
    "exact_fee_residue_location_is_admitted",
    "zero_open_terminal_amount_rejected",
    "future_oracle_observation_rejected",
    "open_terminal_total_above_exact_liability_rejected",
    "terminal_liability_aggregate_overflow_rejected",
    "terminal_claimant_mutation_rejected",
    "oracle_same_height_root_mutation_rejected",
    "duplicate_occurrence_order_rejected",
    "external_enqueue_rejected_before_o009",
    "zero_occurrence_changed_state_rejected",
)

ALLOWED_STANDARD_AXIOMS = frozenset({"propext", "Quot.sound", "Classical.choice"})


def _require_lake() -> str:
    lake = shutil.which("lake")
    assert lake is not None, "formal V2 gate requires lake"
    return lake


def _worktree_paths() -> tuple[Path, ...]:
    result = subprocess.run(
        ["git", "worktree", "list", "--porcelain"],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=30,
        check=False,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    return tuple(
        Path(line.removeprefix("worktree "))
        for line in result.stdout.splitlines()
        if line.startswith("worktree ")
    )


def _cached_lean_directory() -> Path:
    """Reuse one existing worktree cache; never materialize another mathlib."""

    candidates = (ROOT, *_worktree_paths())
    for worktree in candidates:
        lean_dir = worktree / "lean-mathlib"
        if (
            (lean_dir / "lean-toolchain").is_file()
            and (lean_dir / ".lake" / "packages" / "mathlib").exists()
            and (worktree / "external" / "mathlib4").exists()
        ):
            assert (lean_dir / "lean-toolchain").read_text(encoding="utf-8").strip() == (
                PINNED_TOOLCHAIN
            )
            return lean_dir
    raise AssertionError("no existing pinned Lean/mathlib cache was found")


def _lake_cached(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [_require_lake(), *args],
        cwd=_cached_lean_directory(),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=120,
        check=False,
    )


@pytest.fixture(scope="module")
def compiled_packet(tmp_path_factory: pytest.TempPathFactory) -> CompiledPacket:
    build_root = tmp_path_factory.mktemp("global-settlement-v2-lean")
    (build_root / "Proofs").mkdir()

    lean_result = _lake_cached("env", "which", "lean")
    assert lean_result.returncode == 0, lean_result.stdout + lean_result.stderr
    lean = Path(lean_result.stdout.strip())
    assert lean.is_file()

    version = subprocess.run(
        [str(lean), "--version"],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=30,
        check=False,
    )
    assert version.returncode == 0, version.stdout + version.stderr
    assert "version 4.27.0" in version.stdout

    path_result = _lake_cached("env", "printenv", "LEAN_PATH")
    assert path_result.returncode == 0, path_result.stdout + path_result.stderr
    environment = os.environ.copy()
    environment["LEAN_PATH"] = os.pathsep.join(
        (str(build_root), path_result.stdout.strip())
    )

    outputs: dict[str, subprocess.CompletedProcess[str]] = {}
    for name, target in (("core", CORE), ("refinement", REFINEMENT)):
        module_output = build_root / "Proofs" / f"{target.stem}.olean"
        result = subprocess.run(
            [
                str(lean),
                "-DwarningAsError=true",
                "-o",
                str(module_output),
                str(target),
            ],
            cwd=ROOT,
            env=environment,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=300,
            check=False,
        )
        assert result.returncode == 0, result.stdout + result.stderr
        assert result.stdout.strip() == ""
        assert result.stderr.strip() == ""
        assert module_output.is_file()
        outputs[name] = result

    return {"root": build_root, "lean": lean, "env": environment, "outputs": outputs}


def _run_probe(
    compiled_packet: CompiledPacket,
    path: Path,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [str(compiled_packet["lean"]), "-DwarningAsError=true", str(path)],
        cwd=ROOT,
        env=compiled_packet["env"],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=300,
        check=False,
    )


def _axiom_dependencies(output: str) -> set[str]:
    dependencies: set[str] = set()
    for body in re.findall(r"depends on axioms:\s*\[([^\]]*)\]", output, re.DOTALL):
        dependencies.update(item.strip() for item in body.split(",") if item.strip())
    return dependencies


def _structure_fields(source: str, structure_name: str) -> tuple[str, ...]:
    found = re.search(
        rf"^structure\s+{re.escape(structure_name)}\b.*?\bwhere\n"
        rf"(?P<body>.*?)(?=\n(?:/-!|structure |inductive |def |theorem |end ))",
        source,
        flags=re.MULTILINE | re.DOTALL,
    )
    assert found is not None, structure_name
    return tuple(
        match.group(1)
        for match in re.finditer(r"^\s{2}([A-Za-z][A-Za-z0-9]*)\s*:", found.group("body"), re.MULTILINE)
    )


def _wire_values(source: str, definition: str, next_definition: str) -> tuple[str, ...]:
    start = source.index(f"def {definition}")
    end = source.index(f"def {next_definition}", start)
    return tuple(re.findall(r'=>\s*"([A-Z_]+)"', source[start:end]))


def _theorem_names(source: str) -> tuple[str, ...]:
    return tuple(re.findall(r"^theorem\s+([A-Za-z0-9_.]+)", source, re.MULTILINE))


def test_packet_compiles_with_pinned_lean_and_warnings_as_errors(
    compiled_packet: CompiledPacket,
) -> None:
    assert set(compiled_packet["outputs"]) == {"core", "refinement"}


def test_modeled_runtime_sources_are_exactly_pinned() -> None:
    for relative_path, expected_sha256 in PINNED_MODELED_RUNTIME_SOURCES.items():
        source = ROOT / relative_path
        assert source.is_file(), relative_path
        assert hashlib.sha256(source.read_bytes()).hexdigest() == expected_sha256, (
            relative_path
        )


def test_repository_placeholder_scanner_checks_declarations_fail_closed() -> None:
    assert SCANNER.is_file()
    result = subprocess.run(
        [sys.executable, str(SCANNER), str(CORE), str(REFINEMENT), "--json"],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=120,
        check=False,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    payload = json.loads(result.stdout)
    assert payload["blocked"] is False
    assert payload["match_count"] == 0
    assert payload["axiom_check"] is True
    assert len(payload["scanned_files"]) == 2


def test_hand_maintained_theorem_surface_uses_only_standard_axioms(
    compiled_packet: CompiledPacket,
    tmp_path: Path,
) -> None:
    assert CORE_THEOREMS == _theorem_names(CORE.read_text(encoding="utf-8"))
    assert REFINEMENT_THEOREMS == _theorem_names(REFINEMENT.read_text(encoding="utf-8"))
    qualified = (
        *(f"{CORE_NAMESPACE}.{name}" for name in CORE_THEOREMS),
        *(f"{REFINEMENT_NAMESPACE}.{name}" for name in REFINEMENT_THEOREMS),
    )
    probe = tmp_path / "GlobalSettlementV2Axioms.lean"
    probe.write_text(
        "import Proofs.GlobalEconomicStateRefinementV2\n\n"
        + "\n".join(f"#print axioms {name}" for name in qualified)
        + "\n",
        encoding="utf-8",
    )
    result = _run_probe(compiled_packet, probe)
    assert result.returncode == 0, result.stdout + result.stderr
    for name in qualified:
        assert f"'{name}'" in result.stdout, name
    assert _axiom_dependencies(result.stdout) <= ALLOWED_STANDARD_AXIOMS


def test_semantic_mutation_signatures_are_compiler_bound(
    compiled_packet: CompiledPacket,
    tmp_path: Path,
) -> None:
    probe = tmp_path / "GlobalSettlementV2MutationSignatures.lean"
    probe.write_text(
        """import Proofs.GlobalEconomicStateRefinementV2

namespace Proofs.GlobalSettlementV2MutationSignatures
open GlobalSettlementCoreV2 GlobalEconomicStateRefinementV2

example : NetProjectionMatches netOnlyMutationPlan :=
  netOnlyMutation_has_zero_net
example : ¬ ProjectionMatches netOnlyMutationPlan :=
  netOnlyMutation_projection_rejected
example : ¬ EffectRowAdmitted negativeFeeAllocationRow :=
  negative_fee_allocation_rejected
example : ¬ FeeProjectionMatches feeProjectionMismatchPlan :=
  fee_projection_mismatch_rejected
example : ¬ ExactLaneWrites disabledLanePreState disabledLanePostState
    disabledLaneWritePlan :=
  disabled_lane_write_rejected
example : ¬ SparseAmountRowsAdmitted zeroSparseAmountRows :=
  zero_sparse_amount_row_rejected
example : ¬ SparseSupplyRowsAdmitted zeroSparseSupplyRows :=
  zero_sparse_supply_row_rejected
example : ¬ ReplayOccurrenceIdsInjective replayAliasState :=
  replay_occurrence_alias_rejected
example : ¬ OracleRegistryKeysMatch oracleKeyMismatchState :=
  oracle_lookup_key_mismatch_rejected
example : ¬ StateBearingAggregatesFitI128 stateBearingOverflowPlan :=
  state_bearing_annotation_overflow_rejected
example : ¬ (∀ asset,
    0 ≤ amountForAsset underbackedLiability asset ∧
    amountForAsset underbackedLiability asset ≤
      amountForAsset insufficientCustody asset) :=
  underbacked_claimant_liability_rejected
example : ¬ AnnotationMirrors undercreditedFeePlan :=
  undercredited_fee_allocation_rejected
example : ¬ AnnotationMirrors zeroFeeConservationPlan :=
  zero_fee_conservation_row_rejected
example : ¬ AnnotationMirrors wrongFeeResiduePlan :=
  wrong_fee_residue_location_rejected
example : AnnotationMirrors exactFeeResiduePlan :=
  exact_fee_residue_location_is_admitted
example : ¬ TerminalObligationAdmitted zeroOpenTerminal :=
  zero_open_terminal_amount_rejected
example : ¬ OracleOccurrenceWithinHeight 7 futureOracleOccurrence :=
  future_oracle_observation_rejected
example : ¬ (∀ owner asset domain,
    0 ≤ openTerminalAmountFor uncoveredOpenTerminals owner asset domain ∧
    openTerminalAmountFor uncoveredOpenTerminals owner asset domain ≤
      amountAt insufficientExactLiability owner asset domain) :=
  open_terminal_total_above_exact_liability_rejected
example : ¬ TerminalLiabilityAggregatesFitI128 terminalLiabilityOverflowPlan :=
  terminal_liability_aggregate_overflow_rejected
example : ¬ TerminalDeltaAdmitted terminalIdentityMutation :=
  terminal_claimant_mutation_rejected
example : ¬ OracleDeltaAdmitted oracleSameHeightRootMutation :=
  oracle_same_height_root_mutation_rejected
example : ¬ OrderedOccurrenceIds duplicateOccurrences :=
  duplicate_occurrence_order_rejected
example : ¬ PreO009OutboxClosed externalEnqueueMutation :=
  external_enqueue_rejected_before_o009
example : ∃ accepted : Accepted staticGlobalState,
    accepted.post = staticGlobalState ∧ accepted.occurrences = [] :=
  combined_verified_relation_is_inhabited
example {pre : GlobalState} (accepted : Accepted pre) :
    FeeAllocationCreditsMirrored accepted.effects ∧
      FeeProjectionMatches accepted.effects ∧
      FeeRowsCanonical accepted.effects ∧ FeeResidueExact accepted.effects :=
  accepted_fee_credit_and_residue_are_exact accepted

end Proofs.GlobalSettlementV2MutationSignatures
""",
        encoding="utf-8",
    )
    result = _run_probe(compiled_packet, probe)
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout.strip() == ""
    assert result.stderr.strip() == ""


def test_claim_ceiling_and_scope_are_explicit() -> None:
    source = " ".join((CORE.read_text(encoding="utf-8") + REFINEMENT.read_text(encoding="utf-8")).split())
    required = (
        "Roots and identifiers are opaque",
        "six fields of `GlobalEconomicEffectPlanV2`",
        "Issue and burn are projected independently",
        "no verifier authority",
        "publisher authority",
        "settlement authority",
        "value-moving authority",
        "no Python/Rust refinement",
        "no runtime reachability",
        "production readiness",
        "O-009 remains required",
        "no claim about SHA-256 injectivity",
        "order-independent changed-lane/write membership",
        "pre-enabled lanes",
        "per-asset fee-allocation projection",
        "sparse and nonzero",
        "injective stored occurrence IDs",
        "lookup-key identity",
        "running state-bearing annotation totals",
        "same-key state-bearing fee credit",
        "rejects zero fee rows",
        "bounds each Oracle observation by global height",
        "makes every open terminal amount positive",
        "exact claimant/asset/accounting-location liability row",
        "collection and byte resource ceilings",
        "private snapshot ownership",
        "exception classes and precedence",
    )
    for phrase in required:
        assert phrase.lower() in source.lower(), phrase


def test_lane_and_effect_wire_values_match_live_python_v2() -> None:
    core = CORE.read_text(encoding="utf-8")
    python_lanes = tuple(lane.value for lane in ALL_LANE_IDS_V2)
    python_effects = tuple(kind.value for kind in EconomicEffectKindV2)
    assert _wire_values(core, "LaneId.code", "LaneId.index") == python_lanes
    assert _wire_values(core, "EffectKind.code", "allEffectKinds") == python_effects
    assert len(python_lanes) == 12
    assert len(set(python_lanes)) == 12
    assert len(python_effects) == 9
    assert len(set(python_effects)) == 9


def test_fee_residue_coordinates_match_live_python_v2() -> None:
    refinement = REFINEMENT.read_text(encoding="utf-8")
    principal = re.search(
        r'def feeResiduePrincipal[^:]*:\s*Principal\s*:=\s*"([^"]+)"',
        refinement,
    )
    location = re.search(
        r'def feeResidueAccountingLocation[^:]*:\s*AccountingLocation\s*:=\s*\n?\s*"([^"]+)"',
        refinement,
    )
    assert principal is not None
    assert location is not None
    assert principal.group(1) == FEE_RESIDUE_PRINCIPAL_V2
    assert location.group(1) == FEE_RESIDUE_CONTROL_DOMAIN_V2


@pytest.mark.parametrize(
    ("python_type", "lean_structure", "field_map"),
    [
        (
            GlobalEconomicEffectPlanV2,
            "EffectPlan",
            {
                "rows": "rows",
                "asset_conservation": "assetConservation",
                "fee_conservation": "feeConservation",
                "lane_writes": "laneWrites",
                "occurrence_consumptions": "occurrenceConsumptions",
                "external_outbox_enqueue": "externalOutboxEnqueue",
            },
        ),
        (
            EconomicEffectRowV2,
            "EconomicEffectRow",
            {
                "kind": "kind",
                "principal": "principal",
                "asset": "asset",
                "custody_domain": "custodyDomain",
                "delta_atoms": "deltaAtoms",
            },
        ),
        (
            AssetConservationRowV2,
            "AssetConservationRow",
            {
                "asset": "asset",
                "owned_and_custodied_pre_atoms": "ownedAndCustodiedPreAtoms",
                "owned_and_custodied_post_atoms": "ownedAndCustodiedPostAtoms",
                "supply_pre_atoms": "supplyPreAtoms",
                "supply_post_atoms": "supplyPostAtoms",
                "authorized_issue_atoms": "authorizedIssueAtoms",
                "authorized_burn_atoms": "authorizedBurnAtoms",
            },
        ),
        (
            FeeConservationRowV2,
            "FeeConservationRow",
            {
                "asset": "asset",
                "fee_charged_atoms": "feeChargedAtoms",
                "current_allocations_atoms": "currentAllocationsAtoms",
                "carried_residue_atoms": "carriedResidueAtoms",
            },
        ),
        (
            LaneWriteV2,
            "LaneWrite",
            {"lane_id": "laneId", "pre_root": "preRoot", "post_root": "postRoot"},
        ),
        (
            ExternalOutboxEnqueueV2,
            "ExternalOutboxEnqueue",
            {
                "effect_id": "effectId",
                "destination_id": "destinationId",
                "payload_hash": "payloadHash",
                "adapter_profile_root": "adapterProfileRoot",
            },
        ),
    ],
)
def test_effect_plan_key_field_inventory_matches_live_python_v2(
    python_type: type[object],
    lean_structure: str,
    field_map: dict[str, str],
) -> None:
    assert tuple(inspect.signature(python_type).parameters) == tuple(field_map)
    assert _structure_fields(CORE.read_text(encoding="utf-8"), lean_structure) == tuple(
        field_map.values()
    )


@pytest.mark.parametrize(
    ("python_type", "lean_structure", "field_map"),
    [
        (
            TerminalObligationV2,
            "TerminalObligation",
            {
                "obligation_id": "obligationId",
                "lane_id": "laneId",
                "claimant": "claimant",
                "asset": "asset",
                "liability_domain": "liabilityDomain",
                "amount_atoms": "amountAtoms",
                "status": "status",
            },
        ),
        (
            TerminalObligationDeltaV2,
            "TerminalDelta",
            {
                "obligation_id": "obligationId",
                "pre_obligation": "preObligation",
                "post_obligation": "postObligation",
            },
        ),
        (
            OracleOccurrenceStateV2,
            "OracleOccurrence",
            {
                "oracle_id": "oracleId",
                "occurrence_root": "occurrenceRoot",
                "observed_height": "observedHeight",
                "finalized": "finality",
            },
        ),
        (
            OracleOccurrenceDeltaV2,
            "OracleDelta",
            {
                "oracle_id": "oracleId",
                "pre_occurrence": "preOccurrence",
                "post_occurrence": "postOccurrence",
            },
        ),
    ],
)
def test_lifecycle_key_field_inventory_matches_live_python_v2(
    python_type: type[object],
    lean_structure: str,
    field_map: dict[str, str],
) -> None:
    assert tuple(inspect.signature(python_type).parameters) == tuple(field_map)
    assert _structure_fields(REFINEMENT.read_text(encoding="utf-8"), lean_structure) == tuple(
        field_map.values()
    )


def test_global_state_key_field_inventory_matches_live_python_v2() -> None:
    live_fields = tuple(inspect.signature(GlobalEconomicStateV2).parameters)
    assert live_fields == (
        "chain_id",
        "deployment_root",
        "writer_epoch",
        "height",
        "profile_root",
        "lane_roots",
        "balances",
        "supplies",
        "custody",
        "liabilities",
        "reserves",
        "oracle_occurrences",
        "replay_state",
        "terminal_obligations",
        "history_root",
        "outbox",
    )
    modeled_fields = _structure_fields(
        REFINEMENT.read_text(encoding="utf-8"),
        "GlobalState",
    )
    expected_modeled = (
        "stateRoot",
        "chainId",
        "deploymentRoot",
        "writerEpoch",
        "height",
        "profileRoot",
        "laneRoots",
        "laneReleaseIds",
        "laneEnabled",
        "balances",
        "supplies",
        "custody",
        "liabilities",
        "reserves",
        "oracleOccurrences",
        "replayState",
        "terminalObligations",
        "historyRoot",
        "outbox",
    )
    assert modeled_fields == expected_modeled
    prose = " ".join(REFINEMENT.read_text(encoding="utf-8").split())
    for field in live_fields:
        assert f"`{field}`" in prose or field in {
            "balances",
            "supplies",
            "custody",
            "liabilities",
            "reserves",
            "outbox",
        }


def test_combined_witness_owns_every_required_obligation() -> None:
    fields = _structure_fields(REFINEMENT.read_text(encoding="utf-8"), "Verified")
    assert fields == (
        "fixedContext",
        "preQuantities",
        "postQuantities",
        "effectPlan",
        "laneWrites",
        "economicTables",
        "supplyEffects",
        "conservationCoverage",
        "conservationRows",
        "annotations",
        "ownedSupplyPre",
        "ownedSupplyPost",
        "liabilitiesPre",
        "liabilitiesPost",
        "terminal",
        "oracle",
        "replay",
        "outboxClosed",
        "zeroOccurrence",
    )
