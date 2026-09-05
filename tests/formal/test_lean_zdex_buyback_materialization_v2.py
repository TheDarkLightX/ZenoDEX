"""Integer-model proofs and finite comparisons with unmounted SHADOW functions.

The fixture bridge preserves every kind/principal/asset/domain coordinate. It
rejects the two runtime kinds absent from the model. Permutation comparisons
check full rows, including multiplicity, rather than per-asset totals. They
are bounded correspondence evidence, not universal Python/Rust refinement.
"""

from __future__ import annotations

import os
import re
import subprocess
from pathlib import Path

import pytest

from src.core.global_settlement_types_v1 import (
    MAX_DELTA_ATOMS_V1,
    MIN_DELTA_ATOMS_V1,
    ZERO_ROOT_V1,
    AssetConservationRowV1,
    FeeConservationRowV1,
    LaneIdV1,
    LaneWriteV1,
)
from src.core.global_settlement_types_v1 import (
    EconomicEffectKindV1 as Kind,
)
from src.core.global_settlement_types_v1 import (
    EconomicEffectRowV1 as Row,
)
from src.core.global_settlement_types_v1 import (
    GlobalEconomicEffectPlanV1 as Plan,
)
from src.core.zdex_atomic_buyback_lane_coordinator_v2 import (
    _materialize_fee_allocations_v2,
    _materialize_spot_custody_v2,
)
from src.core.zdex_atomic_buyback_lane_receipt_v2 import (
    snapshot_verified_zdex_buyback_lane_composition_v2,
)
from src.core.zdex_atomic_buyback_receipt_verification_v2 import (
    snapshot_verified_zdex_spot_buyback_leaf_v2,
    snapshot_verified_zdex_tokenomics_buyback_leaf_v2,
)
from src.core.zdex_atomic_buyback_route_composition_v2 import (
    ZDEXAtomicBuybackRouteAcceptedV2,
    _compose_effects_v2,
    compose_zdex_atomic_buyback_route_shadow_v2,
)
from src.core.zdex_purchase_burn_route_types_v1 import (
    AMM_POOL_CUSTODY_DOMAIN_V1,
    PROTOCOL_SUPPLY_CUSTODY_DOMAIN_V1,
    ZDEX_SUPPLY_PRINCIPAL_V1,
    zdex_pool_reserve_principal_v1,
)
from tests.core.test_zdex_atomic_buyback_route_composition_v2 import _verified_route_candidate
from tests.core.test_zdex_buyback_materialization_semantics_v2 import _plan
from tests.formal.test_lean_zdex_acquisition_burn_occurrence_v2 import _pinned_lean_executable

ROOT = Path(__file__).resolve().parents[2]
PROJECT = ROOT / "lean-mathlib"
PROOF = PROJECT / "Proofs/ZDEXBuybackMaterializationV2.lean"
DEPENDENCY = PROJECT / "Proofs/ZDEXAcquisitionBurnOccurrenceV2.lean"
NAMESPACE = "Proofs.ZDEXBuybackMaterializationV2"
PRELUDE = "\nopen Proofs.ZDEXAcquisitionBurnOccurrenceV2\nopen " + NAMESPACE + "\n"
KINDS = {
    Kind.ACCOUNT_MOVEMENT: "accountMovement", Kind.CUSTODY: "custody",
    Kind.RESERVE: "reserve", Kind.LIABILITY: "liability", Kind.ISSUE: "issue",
    Kind.BURN: "burn", Kind.FEE_ALLOCATION: "feeAllocation",
}
REQUIRED = {
    "keyedDelta_normalize", "normalized_keys_unique", "normalized_zero_key_absent",
    "materialized_custody_exact", "materialized_fee_allocation_is_separate",
    "admitted_occurrence_consumed_once", "normalized_route_no_foreign_zdex_row",
    "accepted_bound_route_exact_footprint", "matching_terminal_is_nonvacuous",
}


@pytest.fixture(scope="module")
def lean_context(tmp_path_factory: pytest.TempPathFactory) -> tuple[Path, Path]:
    """Compile the dependency from current source, without a cached project build."""
    directory = tmp_path_factory.mktemp("buyback_materialization_lean")
    (directory / "Proofs").mkdir()
    lean = _pinned_lean_executable()
    result = subprocess.run(
        [str(lean), "-DwarningAsError=true", "-o",
         str(directory / "Proofs/ZDEXAcquisitionBurnOccurrenceV2.olean"), str(DEPENDENCY)],
        cwd=PROJECT, capture_output=True, text=True, timeout=60, check=False,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    return lean, directory


def _check(context: tuple[Path, Path], name: str, source: str) -> subprocess.CompletedProcess[str]:
    lean, directory = context
    probe = directory / f"{name}.lean"
    probe.write_text(source, encoding="utf-8")
    return subprocess.run(
        [str(lean), "-DwarningAsError=true", str(probe)], cwd=PROJECT,
        env={**os.environ, "LEAN_PATH": str(directory)},
        capture_output=True, text=True, timeout=60, check=False,
    )


def test_proof_and_fixed_type_consumers_check_with_standard_axioms_only(
    lean_context: tuple[Path, Path],
) -> None:
    source = PROOF.read_text(encoding="utf-8")
    assert re.search(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b", source) is None
    names = re.findall(r"^theorem (\w+)", source, re.MULTILINE)
    assert REQUIRED <= set(names)
    consumers = """
example (key : EffectKey) (rows : Plan) :
    keyedDelta key (normalize rows) = keyedDelta key rows := keyedDelta_normalize key rows
example (rows : Plan) : ((normalize rows).map effectKey).Nodup := normalized_keys_unique rows
example (rows : Plan) (row : Row)
    (zero : keyedDelta (effectKey row) (normalize rows) = 0) : row ∉ normalize rows :=
  normalized_zero_key_absent rows row zero
example (key : Key) (rows : Plan) :
    keyedDelta (.custody, key) (materializeFees rows) =
      keyedDelta (.custody, key) rows + keyedDelta (.feeAllocation, key) rows :=
  materialized_custody_exact key rows
example (key : Key) (rows : Plan) :
    keyedDelta (.feeAllocation, key) (materializeFees rows) =
      keyedDelta (.feeAllocation, key) rows := materialized_fee_allocation_is_separate key rows
example (occurrence : Nat) (spot tokenomics : LanePlan)
    (admitted : admissibleOccurrence occurrence spot tokenomics = true) :
    (compose spot tokenomics).occurrences = [occurrence] ∧
      (compose spot tokenomics).occurrences.length = 1 :=
  admitted_occurrence_consumed_once occurrence spot tokenomics admitted
example (poolId gross purchased burned fee allocation otherAllocations residue spend tag : Nat)
    (row : Row) (assetBound : row.key.asset = zdexAsset)
    (notPool : effectKey row ≠ (.custody, poolZdexKey poolId))
    (notSupply : effectKey row ≠ (.burn, zdexSupplyKey)) :
    row ∉ normalize (routePlan poolId gross purchased burned fee allocation
      otherAllocations residue spend tag) :=
  normalized_route_no_foreign_zdex_row _ _ _ _ _ _ _ _ _ _ _ assetBound notPool notSupply
example (pair : TerminalPair) (gross fee allocation otherAllocations residue spend tag : Nat)
    (plan : LanePlan)
    (accepted : boundRoute pair gross fee allocation otherAllocations residue spend tag = some plan)
    (kind : Kind) (key : Key) (assetBound : key.asset = zdexAsset) :
    keyedDelta (kind, key) plan.rows =
      (if (kind, key) = (.custody, poolZdexKey pair.spotPool) then -(pair.acquired : Int) else 0) +
      (if (kind, key) = (.burn, zdexSupplyKey) then -(pair.acquired : Int) else 0) ∧
    plan.occurrences = [pair.occurrence] ∧ pair.burnPool = pair.spotPool ∧
    pair.discharged = pair.terminal ∧ pair.burnOccurrence = pair.spotOccurrence :=
  accepted_bound_route_exact_footprint _ _ _ _ _ _ _ _ _ accepted _ _ assetBound
"""
    directives = "\n".join(f"#print axioms {NAMESPACE}.{name}" for name in names)
    result = _check(lean_context, "TheoremConsumers", source + PRELUDE + consumers + directives)
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stderr == ""
    report = " ".join(result.stdout.split())
    for name in names:
        match = re.search(
            re.escape(f"'{NAMESPACE}.{name}' ")
            + r"(?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", report,
        )
        assert match, (name, report)
        axioms = {item.strip() for item in (match.group(1) or "").split(",") if item.strip()}
        assert axioms <= {"propext", "Quot.sound", "Classical.choice"}, (name, axioms)


def _terms(rows: tuple[Row, ...], universe: tuple[Row, ...]) -> str:
    # Each complete coordinate gets an injective, shared fixture-only encoding.
    principals = {value: i for i, value in enumerate(sorted({r.principal for r in universe}))}
    assets = {value: i for i, value in enumerate(sorted({r.asset for r in universe}))}
    domains = {value: i for i, value in enumerate(sorted({r.custody_domain for r in universe}))}
    terms = []
    for row in rows:
        if row.kind not in KINDS:
            raise ValueError("runtime effect kind is outside this Lean model")
        key = f"⟨.unbound {principals[row.principal]}, {assets[row.asset]}, {domains[row.custody_domain]}⟩"
        terms.append(f"⟨.{KINDS[row.kind]}, {key}, ({row.delta_atoms} : Int)⟩")
    return "[" + ", ".join(terms) + "]"


def test_fixture_translation_is_injective_and_rejects_unmodeled_kinds() -> None:
    rows = tuple(
        Row(kind, principal, asset, domain, -1 if kind is Kind.BURN else 1)
        for kind in KINDS for principal in ("alice", "bob")
        for asset in ("quote", "zdex") for domain in ("pool", "treasury")
    )
    assert len({_terms((row,), rows) for row in rows}) == len(rows) == 56
    assert set(Kind) - KINDS.keys() == {Kind.REWARD, Kind.SLASH}
    for kind in (Kind.REWARD, Kind.SLASH):
        row = Row(kind, "alice", "quote", "pool", 1)
        with pytest.raises(ValueError, match="outside this Lean model"):
            _terms((row,), (row,))


def _permutation(expression: str, expected: str) -> str:
    return f"example : ({expression}).Perm ({expected} : Plan) := by decide\n"


def _identity_nat(value: str) -> int:
    # Nonempty printable ASCII has no leading zero byte, so this is injective.
    assert value and all(32 <= ord(char) <= 126 for char in value)
    return int.from_bytes(value.encode("ascii"), "big")


def _route_zdex_terms(rows: tuple[Row, ...], asset: str, pool_id: str) -> str:
    pool = zdex_pool_reserve_principal_v1(pool_id=pool_id, asset_id=asset)
    principals = {pool: f".poolReserve {_identity_nat(pool_id)} zdexAsset",
                  ZDEX_SUPPLY_PRINCIPAL_V1: ".zdexSupply"}
    domains = {AMM_POOL_CUSTODY_DOMAIN_V1: 1, PROTOCOL_SUPPLY_CUSTODY_DOMAIN_V1: 2}
    terms = []
    for row in rows:
        if row.asset != asset:
            continue
        # Foreign coordinates remain distinguishable and must fail permutation.
        principal = principals.get(row.principal, f".unbound {_identity_nat(row.principal)}")
        domain = domains.get(row.custody_domain, 3 + _identity_nat(row.custody_domain))
        terms.append(f"⟨.{KINDS[row.kind]}, ⟨{principal}, zdexAsset, {domain}⟩, ({row.delta_atoms} : Int)⟩")
    return "[" + ", ".join(terms) + "]"


def test_actual_shadow_terminals_and_zdex_rows_instantiate_the_route_model(
    lean_context: tuple[Path, Path],
) -> None:
    fixture, candidate = _verified_route_candidate()
    result = compose_zdex_atomic_buyback_route_shadow_v2(candidate)
    assert type(result) is ZDEXAtomicBuybackRouteAcceptedV2
    spot = snapshot_verified_zdex_spot_buyback_leaf_v2(candidate.verified_spot_leaf).journal
    tokenomics = snapshot_verified_zdex_tokenomics_buyback_leaf_v2(candidate.verified_tokenomics_leaf).journal
    fields = (
        _identity_nat(fixture.occurrence.occurrence_id),
        _identity_nat(candidate.verified_spot_leaf.command_occurrence_id),
        _identity_nat(candidate.verified_tokenomics_leaf.command_occurrence_id),
        _identity_nat(spot.terminal_obligation_id), _identity_nat(tokenomics.discharged_obligation_id),
        _identity_nat(spot.selected_pool_id), _identity_nat(tokenomics.selected_pool_id),
        spot.purchased_zdex_atoms, tokenomics.purchased_zdex_atoms, tokenomics.burned_zdex_atoms,
    )
    checks = "def runtimePair : TerminalPair := ⟨" + ", ".join(map(str, fields)) + "⟩\n"
    # Quote accounting is intentionally outside this ZDEX-only comparison.
    checks += "def runtimeBound := boundRoute runtimePair 0 0 0 0 0 0 0\n"
    checks += "example : runtimeBound.isSome = true := by decide\n"
    checks += _permutation(
        "((runtimeBound.getD ⟨[], []⟩).rows.filter (fun r => r.key.asset == zdexAsset))",
        _route_zdex_terms(result.effects.rows, tokenomics.zdex_asset_id, spot.selected_pool_id),
    )
    actual_occurrences = "[" + ", ".join(str(_identity_nat(item)) for item in result.effects.occurrence_consumptions) + "]"
    checks += f"example : (runtimeBound.getD ⟨[], []⟩).occurrences = {actual_occurrences} := by decide\n"
    checked = _check(lean_context, "RouteSpecificRows", "import Init.Data.List.Perm\n" + PROOF.read_text() + PRELUDE + checks)
    assert checked.returncode == 0, checked.stdout + checked.stderr


def test_actual_shadow_composition_and_materializers_match_full_lean_rows(
    lean_context: tuple[Path, Path],
) -> None:
    fixture, candidate = _verified_route_candidate()
    result = compose_zdex_atomic_buyback_route_shadow_v2(candidate)
    assert type(result) is ZDEXAtomicBuybackRouteAcceptedV2
    spot = snapshot_verified_zdex_buyback_lane_composition_v2(candidate.verified_spot_lane)
    tokenomics = snapshot_verified_zdex_buyback_lane_composition_v2(candidate.verified_tokenomics_lane)
    spot_leaf = snapshot_verified_zdex_spot_buyback_leaf_v2(candidate.verified_spot_leaf)
    tokenomics_leaf = snapshot_verified_zdex_tokenomics_buyback_leaf_v2(candidate.verified_tokenomics_leaf)
    universe = (spot.effects.rows + tokenomics.effects.rows + result.effects.rows
                + spot_leaf.effects.rows + tokenomics_leaf.effects.rows)
    spot_terms = _terms(spot.effects.rows, universe)
    tokenomics_terms = _terms(tokenomics.effects.rows, universe)
    checks = _permutation(f"normalize ({spot_terms} ++ {tokenomics_terms})", _terms(result.effects.rows, universe))
    checks += _permutation(
        f"materializeFees {_terms(tokenomics_leaf.effects.rows, universe)}", tokenomics_terms,
    )
    checks += _permutation(
        f"({_terms(spot_leaf.effects.rows, universe)} : Plan).map (fun r => {{r with kind := .custody}})",
        spot_terms,
    )
    assert _materialize_spot_custody_v2(spot_leaf.effects) == spot.effects
    assert _materialize_fee_allocations_v2(tokenomics_leaf.effects) == tokenomics.effects
    assert result.effects.occurrence_consumptions == (fixture.occurrence.occurrence_id,)
    assert spot.effects.occurrence_consumptions == ()
    assert tokenomics.effects.occurrence_consumptions == result.effects.occurrence_consumptions
    checks += "example : (compose ⟨[], []⟩ ⟨[], [42]⟩).occurrences = [42] := by decide\n"
    checked = _check(lean_context, "ActualShadowRows", "import Init.Data.List.Perm\n" + PROOF.read_text() + PRELUDE + checks)
    assert checked.returncode == 0, checked.stdout + checked.stderr


def _synthetic_tokenomics(rows: tuple[Row, ...]) -> Plan:
    issues = sum(row.delta_atoms for row in rows if row.kind is Kind.ISSUE)
    burns = -sum(row.delta_atoms for row in rows if row.kind is Kind.BURN)
    fees = sum(row.delta_atoms for row in rows if row.kind is Kind.FEE_ALLOCATION)
    # These are local effect-shape fixtures; no economic pre-state is claimed.
    return Plan(tuple(sorted(rows, key=lambda row: row.key)),
                (AssetConservationRowV1("asset", burns, issues, burns, issues, issues, burns),) if issues or burns else (),
                (FeeConservationRowV1("asset", fees, fees, 0),) if fees else (),
                (LaneWriteV1(LaneIdV1.ZDEX_TOKENOMICS, ZERO_ROOT_V1, ZERO_ROOT_V1),),
                ("0x" + "01" * 32,), ())


def test_finite_arithmetic_and_key_corpus_matches_lean(
    lean_context: tuple[Path, Path],
) -> None:
    checks = []
    for amount in (1, 7, 2**64, MAX_DELTA_ATOMS_V1):
        # Simultaneous key-coordinate distinctions plus exact cancellation.
        fee = _synthetic_tokenomics((Row(Kind.FEE_ALLOCATION, "alice", "asset", "pool", amount),
                                    Row(Kind.CUSTODY, "alice", "asset", "pool", -amount),
                                    Row(Kind.CUSTODY, "bob", "asset", "pool", amount),
                                    Row(Kind.CUSTODY, "alice", "other", "pool", 1),
                                    Row(Kind.CUSTODY, "alice", "asset", "other", 1)))
        actual = _materialize_fee_allocations_v2(fee)
        universe = fee.rows + actual.rows
        checks.append(_permutation(f"materializeFees {_terms(fee.rows, universe)}", _terms(actual.rows, universe)))
    for kind in KINDS:
        amount = -7 if kind is Kind.BURN else 7
        tokenomics = _synthetic_tokenomics((Row(kind, "alice", "asset", "pool", amount),))
        spot = _plan((), lane=LaneIdV1.SPOT_LIQUIDITY)
        actual = _compose_effects_v2(spot, tokenomics)
        checks.append(_permutation(f"normalize {_terms(tokenomics.rows, actual.rows)}", _terms(actual.rows, actual.rows)))
    for left, right in ((MAX_DELTA_ATOMS_V1 - 1, 1), (MIN_DELTA_ATOMS_V1 + 1, -1), (7, -7)):
        spot = _plan((Row(Kind.CUSTODY, "alice", "asset", "pool", left),), lane=LaneIdV1.SPOT_LIQUIDITY)
        tokenomics = _synthetic_tokenomics((Row(Kind.CUSTODY, "alice", "asset", "pool", right),))
        actual = _compose_effects_v2(spot, tokenomics)
        universe = spot.rows + tokenomics.rows + actual.rows
        expression = f"normalize ({_terms(spot.rows, universe)} ++ {_terms(tokenomics.rows, universe)})"
        checks.append(_permutation(expression, _terms(actual.rows, universe)))
    assert len(checks) == 14
    checked = _check(lean_context, "FiniteCorpus", "import Init.Data.List.Perm\n" + PROOF.read_text() + PRELUDE + "\n".join(checks))
    assert checked.returncode == 0, checked.stdout + checked.stderr


@pytest.mark.parametrize(("old", "new"), (
    ("{ head with delta := head.delta + row.delta }", "{ head with delta := head.delta - row.delta }"),
    ("(row.kind, row.key)", "(row.kind, {row.key with domain := 0})"),
    ("row :: { row with kind := .custody } :: mirrorFees rows",
     "row :: { row with kind := .custody, delta := -row.delta } :: mirrorFees rows"),
    ("occurrences := tokenomics.occurrences",
     "occurrences := tokenomics.occurrences ++ tokenomics.occurrences"),
))
def test_semantic_source_mutants_break_preservation_theorems(
    lean_context: tuple[Path, Path], old: str, new: str,
) -> None:
    source = PROOF.read_text(encoding="utf-8")
    assert source.count(old) == 1
    checked = _check(lean_context, "SemanticMutant", source.replace(old, new))
    output = checked.stdout + checked.stderr
    assert checked.returncode != 0, "semantic mutant survived"
    assert "error:" in output
    assert "unexpected token" not in output and "Unknown identifier" not in output
