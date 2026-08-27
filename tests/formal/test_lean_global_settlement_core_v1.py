from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path

import pytest

from src.core.global_settlement_types_v1 import (
    ALL_LANE_IDS_V1,
    AssetConservationRowV1,
    EconomicEffectKindV1,
    EconomicEffectRowV1,
    GlobalEconomicEffectPlanV1,
    LaneIdV1,
    LaneTransitionRejectCodeV1,
)

ROOT = Path(__file__).resolve().parents[2]
LEAN_DIR = ROOT / "lean-mathlib"
PROOF = LEAN_DIR / "Proofs" / "GlobalSettlementCoreV1.lean"
LEAN_MODULE = "Proofs.GlobalSettlementCoreV1"
SCANNER = Path.home() / ".codex" / "proof-engineering" / "scripts" / "scan_proof_placeholders.py"
SCANNER_ALT = (
    Path.home() / ".codex" / "skills" / "proof-engineering" / "scripts" / "scan_proof_placeholders.py"
)

CLAIMS = (
    "allLaneIds_complete",
    "allLaneIds_no_duplicates",
    "allEffectKinds_complete",
    "allRejectCodes_complete",
    "netIssuance_ignores_other_assets",
    "seqPlan_wellFormed",
    "seqPlan_assoc",
    "seqPlan_identity_left",
    "seqPlan_identity_right",
    "applies_preserves_holdingsMatchSupply",
    "wellFormed_applies_moves_by_netIssuance",
    "accepted_post_nonNegative",
    "accepted_outcome_carries_evidence",
    "outcome_postState_nonNegative",
    "outcome_dichotomy",
    "rejected_postState",
    "rejected_emits_empty_abstract_plan",
    "netPreservingSubstitution_not_wellFormed",
    "nonNegativity_premise_is_necessary",
    "seqPlan_journal_not_commutative",
)

# Every field of GlobalEconomicEffectPlanV1 that this proof does not represent.
UNMODELED_SURFACE = (
    "fee_conservation",
    "lane_writes",
    "occurrence_consumptions",
    "external_outbox_enqueue",
)

FORBIDDEN_PROOF_TOKENS = ("sorry", "admit", "axiom", "unsafe")

VECTOR_PROBE = """import Proofs.GlobalSettlementCoreV1

open Proofs.GlobalSettlementCoreV1

def main : IO Unit := do
  IO.println laneIdVectorV1
  IO.println effectKindVectorV1
  IO.println rejectCodeVectorV1
  IO.println signConventionVectorV1

#eval main
"""


def _require_lake() -> str:
    lake = shutil.which("lake")
    assert lake is not None, "formal claim gate requires the lake executable"
    return lake


def test_global_settlement_core_v1_compiles_without_warnings() -> None:
    lake = _require_lake()
    result = subprocess.run(
        [lake, "env", "lean", "-DwarningAsError=true", str(PROOF)],
        cwd=LEAN_DIR,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=600,
        check=False,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout.strip() == ""
    assert result.stderr.strip() == ""


def test_global_settlement_core_v1_has_no_proof_placeholders() -> None:
    scanner = SCANNER if SCANNER.exists() else SCANNER_ALT
    if not scanner.exists():
        pytest.skip("repository placeholder scanner is not installed here")
    result = subprocess.run(
        ["python3", str(scanner), str(PROOF.relative_to(ROOT)), "--json"],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=120,
        check=False,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert '"blocked": false' in result.stdout
    assert '"match_count": 0' in result.stdout


def test_global_settlement_core_v1_claim_surface_is_explicit_and_clean() -> None:
    source = PROOF.read_text(encoding="utf-8")
    lowered = source.lower()
    for token in FORBIDDEN_PROOF_TOKENS:
        assert re.search(rf"\b{re.escape(token)}\b", lowered) is None
    for claim in CLAIMS:
        assert re.search(rf"\btheorem\s+{re.escape(claim)}\b", source) is not None


def test_global_settlement_core_v1_declares_its_unmodeled_surface() -> None:
    source = PROOF.read_text(encoding="utf-8")
    # Doc prose is hard-wrapped, so compare against a whitespace-normalized copy.
    flat = " ".join(source.split())
    for field in UNMODELED_SURFACE:
        assert field in source, f"proof must name {field} as unmodeled"
    assert "not modeled at all" in flat
    assert "canonical ordering, deduplication, and aggregation" in flat
    assert "lower bound only" in flat
    assert "checked `i128` / `u128` arithmetic" in flat
    assert "is NOT the canonical `rows` tuple" in flat
    assert (
        "no statement here asserts custody, possession, title, control, or any "
        "enforceable claim over any asset" in flat
    )


def test_python_plan_has_exactly_the_fields_the_proof_accounts_for() -> None:
    fields = set(GlobalEconomicEffectPlanV1.__dataclass_fields__)
    assert fields == {
        "rows",
        "asset_conservation",
        "fee_conservation",
        "lane_writes",
        "occurrence_consumptions",
        "external_outbox_enqueue",
    }
    # The proof models `rows` (as a non-canonical journal) and the issue/burn
    # totals of `asset_conservation`; the rest must be declared unmodeled.
    assert set(UNMODELED_SURFACE).issubset(fields)


def _lean_vectors(tmp_path: Path) -> list[str]:
    lake = _require_lake()
    build = subprocess.run(
        [lake, "build", LEAN_MODULE],
        cwd=LEAN_DIR,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=600,
        check=False,
    )
    assert build.returncode == 0, build.stdout + build.stderr
    probe = tmp_path / "EvalVectors.lean"
    probe.write_text(VECTOR_PROBE, encoding="utf-8")
    result = subprocess.run(
        [lake, "env", "lean", str(probe)],
        cwd=LEAN_DIR,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=600,
        check=False,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    lines = [line.strip() for line in result.stdout.strip().splitlines() if line.strip()]
    assert len(lines) == 4, result.stdout
    return lines


def test_lean_lane_vector_matches_python_enum(tmp_path: Path) -> None:
    lanes = _lean_vectors(tmp_path)[0].split(",")
    assert lanes == [lane.value for lane in ALL_LANE_IDS_V1]
    assert lanes == [lane.value for lane in LaneIdV1]
    assert len(lanes) == 12


def test_lean_effect_kind_vector_matches_python_enum(tmp_path: Path) -> None:
    kinds = _lean_vectors(tmp_path)[1].split(",")
    assert kinds == [kind.value for kind in EconomicEffectKindV1]
    assert len(kinds) == 9


def test_lean_reject_code_vector_matches_python_enum(tmp_path: Path) -> None:
    codes = _lean_vectors(tmp_path)[2].split(",")
    assert codes == [code.value for code in LaneTransitionRejectCodeV1]
    assert len(codes) == 7


def test_lean_sign_convention_vector_matches_python_validation(tmp_path: Path) -> None:
    assert _lean_vectors(tmp_path)[3] == "ISSUE:positive,BURN:negative,ANY:nonzero"

    def row(kind: EconomicEffectKindV1, delta: int) -> EconomicEffectRowV1:
        return EconomicEffectRowV1(
            kind=kind,
            principal="treasury",
            asset="ZUSD",
            custody_domain="zenoledger:core",
            delta_atoms=delta,
        )

    # ISSUE:positive
    assert row(EconomicEffectKindV1.ISSUE, 250).delta_atoms == 250
    with pytest.raises(ValueError):
        row(EconomicEffectKindV1.ISSUE, -1)
    # BURN:negative
    assert row(EconomicEffectKindV1.BURN, -70).delta_atoms == -70
    with pytest.raises(ValueError):
        row(EconomicEffectKindV1.BURN, 1)
    # ANY:nonzero
    with pytest.raises(ValueError):
        row(EconomicEffectKindV1.ACCOUNT_MOVEMENT, 0)


def _issue_row() -> EconomicEffectRowV1:
    return EconomicEffectRowV1(
        kind=EconomicEffectKindV1.ISSUE,
        principal="treasury",
        asset="ZUSD",
        custody_domain="zenoledger:core",
        delta_atoms=250,
    )


def _conservation(issue: int, burn: int) -> AssetConservationRowV1:
    return AssetConservationRowV1(
        asset="ZUSD",
        owned_and_custodied_pre_atoms=1000,
        owned_and_custodied_post_atoms=1000 + issue - burn,
        supply_pre_atoms=1000,
        supply_post_atoms=1000 + issue - burn,
        authorized_issue_atoms=issue,
        authorized_burn_atoms=burn,
    )


def test_python_rejects_net_preserving_issue_burn_substitution() -> None:
    """The Python analogue of `netPreservingSubstitution_not_wellFormed`.

    A +1 issue / +1 burn substitution leaves the net delta unchanged, so the
    conservation row alone still validates. The plan rejects it because the
    stored totals must each equal the projection over the canonical rows.
    """
    row = _issue_row()

    honest = _conservation(issue=250, burn=0)
    plan = GlobalEconomicEffectPlanV1((row,), (honest,), (), (), (), ())
    assert plan.asset_conservation[0].authorized_issue_atoms == 250

    inflated = _conservation(issue=251, burn=1)
    # The row on its own is net-preserving and therefore valid in isolation.
    assert inflated.owned_and_custodied_post_atoms == honest.owned_and_custodied_post_atoms
    assert inflated.supply_post_atoms == honest.supply_post_atoms
    # The plan pins each stored total separately, exactly as PlanWellFormed does.
    with pytest.raises(ValueError):
        GlobalEconomicEffectPlanV1((row,), (inflated,), (), (), (), ())


def test_python_empty_plan_is_empty_in_every_field() -> None:
    """Bounds the rejection claim.

    The proof shows a rejection emits the empty *abstract* plan, covering the
    journal and the two authorized totals only. Python emptiness is stronger:
    it also covers the four fields the proof declares unmodeled.
    """
    empty = GlobalEconomicEffectPlanV1.empty()
    assert empty.is_empty
    assert empty.rows == ()
    assert empty.asset_conservation == ()
    for field in UNMODELED_SURFACE:
        assert getattr(empty, field) == ()
