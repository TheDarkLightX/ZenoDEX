from __future__ import annotations

import json
import re
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

from src.core.global_settlement_types_v1 import (
    ALL_LANE_IDS_V1,
    AssetConservationRowV1,
    EconomicEffectKindV1,
    EconomicEffectRowV1,
    GlobalEconomicEffectPlanV1,
    LaneIdV1,
    LaneTransitionAcceptedV1,
    LaneTransitionRejectCodeV1,
    LaneTransitionRejectedV1,
)

ROOT = Path(__file__).resolve().parents[2]
LEAN_DIR = ROOT / "lean-mathlib"
PROOF = LEAN_DIR / "Proofs" / "GlobalSettlementCoreV1.lean"
CHALLENGE = LEAN_DIR / "Proofs" / "GlobalSettlementCoreV1Challenge.lean"
CHALLENGE_MODULE = "Proofs.GlobalSettlementCoreV1Challenge"
SCANNER = ROOT / "tools" / "scan_lean_proof_placeholders_v1.py"

PRINCIPAL = "treasury"
ASSET = "ZUSD"
DOMAIN = "zenoledger:core"
ZERO_ROOT = "0x" + "00" * 32
DEMO_ROOT = "0x" + "11" * 32

CORE_CLAIMS = (
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

CHALLENGE_CLAIMS = (
    "challenge_accepted_evidence_construction",
    "challenge_accepted_outcome_carries_evidence",
    "challenge_accepted_outcome_is_nonNegative",
    "challenge_plan_identities",
    "challenge_plan_composition_preserves_wellFormedness",
    "challenge_rejection_reduces",
    "challenge_per_asset_projection",
    "challenge_asset_separation",
    "challenge_application_moves_by_projection",
    "challenge_net_preserving_substitution_rejected",
    "challenge_nonNegativity_is_separate",
    "entryAdmissible_iff",
    "weakIssue_is_strictly_weaker",
    "not_wellFormed_of_planWellFormedOn_false",
)

# GlobalEconomicEffectPlanV1 fields with no analogue in the proof.
UNMODELED_PLAN_FIELDS = (
    "fee_conservation",
    "lane_writes",
    "occurrence_consumptions",
    "external_outbox_enqueue",
)

# LaneTransitionAcceptedV1 fields with no analogue in the proof's Outcome.
UNMODELED_ACCEPTED_FIELDS = (
    "command_occurrence_id",
    "pre_state_root",
    "post_state_root",
    "private_ports_root",
    "receipt_root",
    "terminal_obligations",
)

FORBIDDEN_PROOF_TOKENS = ("sorry", "admit", "axiom", "unsafe")

REPORT_PROBE = """import Proofs.GlobalSettlementCoreV1Challenge

#eval IO.println Proofs.GlobalSettlementCoreV1Challenge.challengeReportV1
"""


def _require_lake() -> str:
    lake = shutil.which("lake")
    assert lake is not None, "formal claim gate requires the lake executable"
    return lake


def _lean(*args: str, timeout: int = 600) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [_require_lake(), *args],
        cwd=LEAN_DIR,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=timeout,
        check=False,
    )


# --------------------------------------------------------------------------
# Compilation and placeholder gates
# --------------------------------------------------------------------------


@pytest.mark.parametrize("target", [PROOF, CHALLENGE], ids=["core", "challenge"])
def test_lean_target_compiles_without_warnings(target: Path) -> None:
    result = _lean("env", "lean", "-DwarningAsError=true", str(target))
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout.strip() == ""
    assert result.stderr.strip() == ""


def test_placeholder_gate_is_repository_owned_and_fails_closed() -> None:
    assert SCANNER.is_file(), "the placeholder gate must be committed to this repository"


def test_lean_targets_have_no_placeholders_with_axiom_checking() -> None:
    result = subprocess.run(
        [sys.executable, str(SCANNER), str(PROOF), str(CHALLENGE), "--json"],
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


def test_claim_surface_is_explicit_and_clean() -> None:
    core = PROOF.read_text(encoding="utf-8")
    challenge = CHALLENGE.read_text(encoding="utf-8")
    for token in FORBIDDEN_PROOF_TOKENS:
        assert re.search(rf"\b{re.escape(token)}\b", core.lower()) is None
        assert re.search(rf"\b{re.escape(token)}\b", challenge.lower()) is None
    for claim in CORE_CLAIMS:
        assert re.search(rf"\btheorem\s+{re.escape(claim)}\b", core) is not None
    for claim in CHALLENGE_CLAIMS:
        assert re.search(rf"\btheorem\s+{re.escape(claim)}\b", challenge) is not None
    assert "import Proofs.GlobalSettlementCoreV1" in challenge


# --------------------------------------------------------------------------
# Omission inventory, verified against the live Python types
# --------------------------------------------------------------------------


def test_proof_names_every_unmodeled_plan_field() -> None:
    fields = set(GlobalEconomicEffectPlanV1.__dataclass_fields__)
    assert fields == {
        "rows",
        "asset_conservation",
        "fee_conservation",
        "lane_writes",
        "occurrence_consumptions",
        "external_outbox_enqueue",
    }
    core = PROOF.read_text(encoding="utf-8")
    for field in UNMODELED_PLAN_FIELDS:
        assert field in core, f"proof must name {field} as unmodeled"


def test_proof_names_every_unmodeled_accepted_transition_field() -> None:
    """Drift guard: if the live type gains a field, this fails until named."""
    fields = set(LaneTransitionAcceptedV1.__dataclass_fields__)
    assert fields == {
        "command_occurrence_id",
        "pre_state_root",
        "post_state_root",
        "effects",
        "private_ports_root",
        "receipt_root",
        "terminal_obligations",
    }
    core = PROOF.read_text(encoding="utf-8")
    modeled = {"effects"}
    for field in sorted(fields - modeled):
        assert field in core, f"proof must name {field} as unmodeled"
    assert set(UNMODELED_ACCEPTED_FIELDS) == fields - modeled


def test_proof_names_every_unmodeled_rejected_transition_field() -> None:
    fields = set(LaneTransitionRejectedV1.__dataclass_fields__)
    assert fields == {"code", "pre_state_root", "post_state_root", "effects"}
    core = PROOF.read_text(encoding="utf-8")
    for field in ("pre_state_root", "post_state_root"):
        assert field in core


def test_proof_declares_token_and_integer_width_omissions() -> None:
    flat = " ".join(PROOF.read_text(encoding="utf-8").split())
    assert "MAX_TOKEN_BYTES_V1" in flat
    assert "printable ASCII `0x21`–`0x7E`" in flat
    assert "MAX_ATOMS_V1" in flat
    assert "MIN_DELTA_ATOMS_V1" in flat
    assert "MAX_DELTA_ATOMS_V1" in flat
    assert "MAX_U64_V1" in flat
    assert "`Int` here is unbounded in both directions" in flat
    assert "lower bound only" in flat


def test_proof_keeps_legal_neutral_wording_and_bounded_claims() -> None:
    flat = " ".join(PROOF.read_text(encoding="utf-8").split())
    assert (
        "no statement here asserts custody, possession, title, control, or any "
        "enforceable claim over any asset" in flat
    )
    assert "is NOT the canonical `rows` tuple" in flat
    assert "canonical ordering, deduplication, and aggregation" in flat
    assert "not a full reject no-op claim" in flat
    assert "Nothing here confers receipt authority" in flat
    challenge_flat = " ".join(CHALLENGE.read_text(encoding="utf-8").split())
    assert "bounded source comparison, not a runtime refinement proof" in challenge_flat


# --------------------------------------------------------------------------
# Executable Lean report, compared against live Python behaviour
# --------------------------------------------------------------------------


@pytest.fixture(scope="module")
def report(tmp_path_factory: pytest.TempPathFactory) -> dict[str, list[list[str]]]:
    build = _lean("build", CHALLENGE_MODULE)
    assert build.returncode == 0, build.stdout + build.stderr
    probe = tmp_path_factory.mktemp("challenge") / "Report.lean"
    probe.write_text(REPORT_PROBE, encoding="utf-8")
    result = _lean("env", "lean", str(probe))
    assert result.returncode == 0, result.stdout + result.stderr
    sections: dict[str, list[list[str]]] = {}
    for line in result.stdout.strip().splitlines():
        line = line.strip()
        if not line:
            continue
        fields = line.split(",")
        sections.setdefault(fields[0], []).append(fields[1:])
    assert sections, result.stdout
    return sections


def test_report_lane_rows_match_python_enum(report) -> None:
    rows = report["LANE"]
    assert [r[0] for r in rows] == [lane.value for lane in ALL_LANE_IDS_V1]
    assert [r[0] for r in rows] == [lane.value for lane in LaneIdV1]
    assert [int(r[1]) for r in rows] == list(range(len(ALL_LANE_IDS_V1)))
    assert len(rows) == 12


def test_report_effect_kind_rows_match_python_enum(report) -> None:
    rows = report["KIND"]
    assert [r[0] for r in rows] == [kind.value for kind in EconomicEffectKindV1]
    assert len(rows) == 9


def test_report_reject_code_rows_match_python_enum(report) -> None:
    rows = report["REJECTCODE"]
    assert [r[0] for r in rows] == [code.value for code in LaneTransitionRejectCodeV1]
    assert len(rows) == 7


def _python_admits(kind: EconomicEffectKindV1, delta: int) -> bool:
    try:
        EconomicEffectRowV1(
            kind=kind,
            principal=PRINCIPAL,
            asset=ASSET,
            custody_domain=DOMAIN,
            delta_atoms=delta,
        )
    except ValueError:
        return False
    return True


def _python_sign_matrix() -> set[tuple[str, int, bool]]:
    return {
        (kind.value, delta, _python_admits(kind, delta))
        for kind in EconomicEffectKindV1
        for delta in (-1, 0, 1)
    }


def _lean_sign_matrix(rows: list[list[str]]) -> set[tuple[str, int, bool]]:
    return {(r[0], int(r[1]), r[2] == "true") for r in rows}


def test_sign_admission_matches_python_for_every_kind_and_bound(report) -> None:
    lean_matrix = _lean_sign_matrix(report["SIGN"])
    assert len(lean_matrix) == 27
    assert lean_matrix == _python_sign_matrix()


def test_paired_weakening_of_issue_positivity_is_killed(report) -> None:
    """The weakened rule must be observably wrong against Python."""
    strict = _lean_sign_matrix(report["SIGN"])
    weakened = _lean_sign_matrix(report["SIGNWEAK"])
    python = _python_sign_matrix()

    assert strict == python
    assert weakened != strict
    assert weakened != python

    # The single observable divergence is ISSUE at -1.
    assert ("ISSUE", -1, False) in strict
    assert ("ISSUE", -1, True) in weakened
    assert _python_admits(EconomicEffectKindV1.ISSUE, -1) is False
    assert (strict ^ weakened) == {("ISSUE", -1, False), ("ISSUE", -1, True)}


# The journal the Lean challenge projects over, mirrored field for field.
COMPARISON_ROWS = (
    (EconomicEffectKindV1.ISSUE, PRINCIPAL, "ZUSD", 250),
    (EconomicEffectKindV1.BURN, PRINCIPAL, "ZUSD", -70),
    (EconomicEffectKindV1.ACCOUNT_MOVEMENT, "alice", "ZUSD", -100),
    (EconomicEffectKindV1.ACCOUNT_MOVEMENT, "bob", "ZUSD", 100),
    (EconomicEffectKindV1.ISSUE, PRINCIPAL, "ZDEX", 40),
)
COMPARISON_ASSETS = ("ZUSD", "ZDEX", "ZBTC")
COMPARISON_BOOK = {"ZUSD": 1000, "ZDEX": 500, "ZBTC": 0}


def _python_projection(asset: str) -> tuple[int, int]:
    """Reproduces _validate_issue_burn_projection's per-asset totals."""
    issued = sum(
        row[3] for row in COMPARISON_ROWS
        if row[0] is EconomicEffectKindV1.ISSUE and row[2] == asset
    )
    burned = sum(
        -row[3] for row in COMPARISON_ROWS
        if row[0] is EconomicEffectKindV1.BURN and row[2] == asset
    )
    return issued, burned


def test_per_asset_projection_matches_python(report) -> None:
    rows = {r[0]: (int(r[1]), int(r[2]), int(r[3])) for r in report["PROJ"]}
    assert set(rows) == set(COMPARISON_ASSETS)
    for asset in COMPARISON_ASSETS:
        issued, burned = _python_projection(asset)
        assert rows[asset] == (issued, burned, issued - burned), asset
    # The absent asset is a real zero, not a missing row.
    assert rows["ZBTC"] == (0, 0, 0)
    # Unlike assets are never summed into one total.
    cross_asset_total = sum(net for _, _, net in rows.values())
    assert cross_asset_total == 220
    for asset in COMPARISON_ASSETS:
        assert rows[asset][2] != cross_asset_total, asset


def test_plan_application_matches_python_conservation_rows(report) -> None:
    rows = {r[0]: tuple(int(v) for v in r[1:]) for r in report["APPLY"]}
    assert set(rows) == set(COMPARISON_ASSETS)
    for asset in COMPARISON_ASSETS:
        issued, burned = _python_projection(asset)
        pre = COMPARISON_BOOK[asset]
        # AssetConservationRowV1 validates exactly this arithmetic.
        conservation = AssetConservationRowV1(
            asset=asset,
            owned_and_custodied_pre_atoms=pre,
            owned_and_custodied_post_atoms=pre + issued - burned,
            supply_pre_atoms=pre,
            supply_post_atoms=pre + issued - burned,
            authorized_issue_atoms=issued,
            authorized_burn_atoms=burned,
        )
        assert rows[asset] == (
            conservation.owned_and_custodied_pre_atoms,
            conservation.supply_pre_atoms,
            conservation.owned_and_custodied_post_atoms,
            conservation.supply_post_atoms,
        ), asset


def test_rejection_projection_matches_python_reject_discipline(report) -> None:
    rows = {r[0]: tuple(int(v) for v in r[1:]) for r in report["REJECT"]}
    assert set(rows) == {code.value for code in LaneTransitionRejectCodeV1}
    for code in LaneTransitionRejectCodeV1:
        rejected = LaneTransitionRejectedV1.reject(code, DEMO_ROOT)
        # Python: exact pre-state root back, and an empty effect plan.
        assert rejected.post_state_root == rejected.pre_state_root
        assert rejected.effects.is_empty
        holdings, supply, journal_len, auth_issue, auth_burn = rows[code.value]
        # Lean: the pre-book back unchanged, empty journal, zero totals.
        assert holdings == COMPARISON_BOOK["ZUSD"]
        assert supply == COMPARISON_BOOK["ZUSD"]
        assert journal_len == len(rejected.effects.rows) == 0
        assert auth_issue == 0
        assert auth_burn == 0


def test_net_preserving_substitution_witness_matches_python(report) -> None:
    rows = {r[0]: r[1] == "true" for r in report["SUBST"]}
    assert rows == {"honest": True, "inflated": False}

    row = EconomicEffectRowV1(
        kind=EconomicEffectKindV1.ISSUE,
        principal=PRINCIPAL,
        asset=ASSET,
        custody_domain=DOMAIN,
        delta_atoms=250,
    )

    def conservation(issue: int, burn: int) -> AssetConservationRowV1:
        return AssetConservationRowV1(
            asset=ASSET,
            owned_and_custodied_pre_atoms=1000,
            owned_and_custodied_post_atoms=1000 + issue - burn,
            supply_pre_atoms=1000,
            supply_post_atoms=1000 + issue - burn,
            authorized_issue_atoms=issue,
            authorized_burn_atoms=burn,
        )

    honest = conservation(250, 0)
    inflated = conservation(251, 1)
    # Net-preserving: the conservation rows agree on both post columns.
    assert inflated.owned_and_custodied_post_atoms == honest.owned_and_custodied_post_atoms
    assert inflated.supply_post_atoms == honest.supply_post_atoms
    # Python accepts the honest plan and rejects the substitution, matching Lean.
    GlobalEconomicEffectPlanV1((row,), (honest,), (), (), (), ())
    with pytest.raises(ValueError):
        GlobalEconomicEffectPlanV1((row,), (inflated,), (), (), (), ())


def test_python_empty_plan_is_stronger_than_the_modeled_rejection() -> None:
    empty = GlobalEconomicEffectPlanV1.empty()
    assert empty.is_empty
    assert empty.rows == ()
    assert empty.asset_conservation == ()
    for field in UNMODELED_PLAN_FIELDS:
        assert getattr(empty, field) == ()
    assert ZERO_ROOT != DEMO_ROOT
