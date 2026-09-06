"""Checked aggregation: universal model plus finite actual Python comparisons.

Obligation: each stage checks every visited complete key after each addition;
accepted totals equal exact keyed sums. The grade-3 oracle sums immutable list
prefixes independently of the runtime dictionary and Lean accumulator. Grade-4
evidence is the compiled theorem packet, with every theorem type and axiom set
checked. RIPR reaches both real helpers with valid effect plans, crosses signed
boundaries or changes one identity coordinate, and observes exact errors/full
rows and unchanged input snapshots. Executable model mutants demonstrate guard
and complete-key sensitivity. Generic repeated-key traces are model inputs;
validated runtime plans have unique keys. Stage-local overflow is tested before
a later stage could cancel it. No runtime source, decoder, shell commit, Rust,
cryptographic, or publication refinement is claimed.
"""

from __future__ import annotations

import json
import re
import subprocess
from dataclasses import asdict, replace
from itertools import product
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
from src.core.zdex_atomic_buyback_lane_coordinator_v2 import _materialize_fee_allocations_v2
from src.core.zdex_atomic_buyback_route_composition_v2 import _compose_effects_v2

ROOT = Path(__file__).resolve().parents[2]
PROJECT = ROOT / "lean-mathlib"
PROOF = PROJECT / "Proofs/CheckedEconomicAggregationV1.lean"
NAMESPACE = "Proofs.CheckedEconomicAggregationV1"
LOWER = -(1 << 127)
UPPER = (1 << 127) - 1
OCCURRENCE = "0x" + "01" * 32
MATERIALIZE_ERROR = "ZDEX buyback coordinated effect exceeds signed i128"
COMPOSE_ERROR = "ZDEX atomic buyback aggregate exceeds signed i128"
KINDS = {
    Kind.ACCOUNT_MOVEMENT: "accountMovement", Kind.ISSUE: "issue", Kind.BURN: "burn",
    Kind.CUSTODY: "custody", Kind.LIABILITY: "liability", Kind.RESERVE: "reserve",
    Kind.FEE_ALLOCATION: "feeAllocation", Kind.REWARD: "reward", Kind.SLASH: "slash",
}
RawKey = tuple[str, str, str, str]
RawRow = tuple[RawKey, int]

# These independent consumer signatures prevent weakening a theorem while
# retaining its name. Every named theorem, including induction helpers, appears.
CLAIM_TYPES = {
    "i128_bounds_exact": "i128.lower = -(2 ^ 127 : Int) ∧ i128.upper = (2 ^ 127 : Int) - 1",
    "keyedSum_append": "∀ (k : Key) (xs ys : List Row), keyedSum k (xs ++ ys) = keyedSum k xs + keyedSum k ys",
    "advance_keyed_sum": "∀ (a : Totals) (r : Row) (xs : List Row) (k : Key), advance a r k + keyedSum k xs = a k + keyedSum k (r :: xs)",
    "prefixFits_nil": "∀ (b : Bounds) (a : Totals), PrefixFits b a []",
    "prefixFits_cons": "∀ (b : Bounds) (a : Totals) (r : Row) (xs : List Row), PrefixFits b a (r :: xs) ↔ Fits b (a r.key + r.delta) ∧ PrefixFits b (advance a r) xs",
    "checkedFold_ok_iff": "∀ (b : Bounds) (a : Totals) (xs : List Row) (out : Totals), checkedFold b a xs = .ok out ↔ PrefixFits b a xs ∧ ∀ k, out k = a k + keyedSum k xs",
    "checkedFold_success_iff": "∀ (b : Bounds) (a : Totals) (xs : List Row), (∃ out, checkedFold b a xs = .ok out) ↔ PrefixFits b a xs",
    "checkedFold_reject_iff": "∀ (b : Bounds) (a : Totals) (xs : List Row), checkedFold b a xs = .error .signedAggregationBounds ↔ ¬PrefixFits b a xs",
    "successful_complete_keyed_sums": "∀ (b : Bounds) (xs : List Row) (out : Totals), checkedFold b empty xs = .ok out → ∀ k, out k = keyedSum k xs",
    "materialization_success_iff": "∀ (b : Bounds) (xs : List Row), (∃ out, checkedMaterialize b xs = .ok out) ↔ PrefixFits b empty (mirrorFees xs)",
    "successful_materialization_keyed_sums": "∀ (b : Bounds) (xs : List Row) (out : Totals), checkedMaterialize b xs = .ok out → ∀ k, out k = keyedSum k (mirrorFees xs)",
    "out_of_range_prefix_rejects": "∀ (b : Bounds) (a : Totals) (xs : List Row) (r : Row) (ys : List Row), ¬Fits b (a r.key + keyedSum r.key xs + r.delta) → checkedFold b a (xs ++ r :: ys) = .error .signedAggregationBounds",
    "successful_composition_keyed_sums": "∀ (b : Bounds) (xs ys : List Row) (out : Totals), checkedCompose b xs ys = .ok out → ∀ k, out k = keyedSum k xs + keyedSum k ys",
    "upper_overflow_cancellation_rejects": "∀ k : Key, checkedFold i128 empty [⟨k, i128.upper⟩, ⟨k, 1⟩, ⟨k, -1⟩] = .error .signedAggregationBounds ∧ Fits i128 (keyedSum k [⟨k, i128.upper⟩, ⟨k, 1⟩, ⟨k, -1⟩])",
    "lower_overflow_cancellation_rejects": "∀ k : Key, checkedFold i128 empty [⟨k, i128.lower⟩, ⟨k, -1⟩, ⟨k, 1⟩] = .error .signedAggregationBounds ∧ Fits i128 (keyedSum k [⟨k, i128.lower⟩, ⟨k, -1⟩, ⟨k, 1⟩])",
    "cancellation_before_increment_accepts": "∀ k : Key, checkedFold i128 empty [⟨k, i128.upper⟩, ⟨k, -1⟩, ⟨k, 1⟩] = .ok (advance (advance (advance empty ⟨k, i128.upper⟩) ⟨k, -1⟩) ⟨k, 1⟩)",
}
OBSERVATIONS = f"""
open {NAMESPACE}
def observe (keys : List Key) : Except Reject Totals → String
  | .ok totals => "OK:" ++ reprStr (keys.map totals)
  | .error .signedAggregationBounds => "ERR"
"""


@pytest.fixture(scope="module")
def lean() -> Path:
    assert (PROJECT / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.27.0"
    # `elan which` locates the installed binary; it does not install packages.
    located = subprocess.run(
        ["elan", "which", "lean"], cwd=PROJECT, capture_output=True, text=True, check=True,
    )
    executable = Path(located.stdout.strip())
    version = subprocess.run([str(executable), "--version"], capture_output=True, text=True, check=True)
    assert "version 4.27.0," in version.stdout
    return executable


def _check(lean: Path, path: Path, source: str) -> subprocess.CompletedProcess[str]:
    path.write_text(source, encoding="utf-8")
    return subprocess.run(
        [str(lean), "-DwarningAsError=true", str(path)], cwd=PROJECT,
        capture_output=True, text=True, check=False, timeout=60,
    )


def test_all_theorem_types_compile_and_use_only_standard_axioms(lean: Path, tmp_path: Path) -> None:
    source = PROOF.read_text()
    assert re.search(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b", source) is None
    assert tuple(re.findall(r"^theorem (\w+)", source, re.MULTILINE)) == tuple(CLAIM_TYPES)
    consumers = "\n".join(
        f"example : {claim_type} := @{NAMESPACE}.{name}\n#print axioms {NAMESPACE}.{name}"
        for name, claim_type in CLAIM_TYPES.items()
    )
    result = _check(lean, tmp_path / "TheoremTypes.lean", source + f"\nopen {NAMESPACE}\n" + consumers)
    assert result.returncode == 0, result.stdout + result.stderr
    report = " ".join(result.stdout.split())
    for name in CLAIM_TYPES:
        match = re.search(
            re.escape(f"'{NAMESPACE}.{name}' ")
            + r"(?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", report,
        )
        assert match, (name, report)
        axioms = {a.strip() for a in (match.group(1) or "").split(",") if a.strip()}
        assert axioms <= {"propext", "Quot.sound", "Classical.choice"}, (name, axioms)


def _raw(row: Row) -> RawRow:
    return ((row.kind.value, row.asset, row.principal, row.custody_domain), row.delta_atoms)


def _key_term(key: RawKey) -> str:
    kind, asset, principal, domain = key
    fields = ", ".join(json.dumps(value) for value in (principal, asset, domain))
    return f"⟨.{KINDS[Kind(kind)]}, {fields}⟩"


def _terms(rows: tuple[RawRow, ...]) -> str:
    return "[" + ", ".join(f"⟨{_key_term(key)}, ({delta} : Int)⟩" for key, delta in rows) + "]"


def _keys(rows: tuple[RawRow, ...]) -> tuple[RawKey, ...]:
    # The extra absent key observes preservation of a zero cell.
    return tuple(sorted({key for key, _ in rows} | {("CUSTODY", "absent", "absent", "absent")}))


def _observation(expression: str, keys: tuple[RawKey, ...]) -> str:
    terms = "[" + ", ".join(_key_term(key) for key in keys) + "]"
    return f"#eval observe {terms} ({expression})\n"


def _prefix_oracle(
    rows: tuple[RawRow, ...], keys: tuple[RawKey, ...], lower: int = LOWER, upper: int = UPPER,
) -> list[int] | None:
    # Re-sum each immutable prefix; do not copy the checked accumulator loop.
    prefixes = [sum(d for k, d in rows[:i + 1] if k == key) for i, (key, _) in enumerate(rows)]
    if any(value < lower or value > upper for value in prefixes):
        return None
    return [sum(delta for row_key, delta in rows if row_key == key) for key in keys]


def _check_observations(
    lean: Path, path: Path, probes: list[str], expected: list[list[int] | None], source: str | None = None,
) -> None:
    result = _check(lean, path, (PROOF.read_text() if source is None else source) + OBSERVATIONS + "".join(probes))
    assert result.returncode == 0, result.stdout + result.stderr
    observations = [json.loads(line) for line in result.stdout.splitlines()]
    decoded = [None if line == "ERR" else json.loads(line.removeprefix("OK:")) for line in observations]
    assert decoded == expected


def _mirrored(rows: tuple[Row, ...]) -> tuple[RawRow, ...]:
    return tuple(
        addition
        for row in rows
        for addition in (
            (_raw(row), (("CUSTODY", row.asset, row.principal, row.custody_domain), row.delta_atoms))
            if row.kind is Kind.FEE_ALLOCATION else (_raw(row),)
        )
    )


def _plan(rows: tuple[Row, ...], lane: LaneIdV1 = LaneIdV1.ZDEX_TOKENOMICS) -> Plan:
    assets = sorted({row.asset for row in rows if row.kind in (Kind.ISSUE, Kind.BURN)})
    conservation = []
    for asset in assets:
        issues = sum(row.delta_atoms for row in rows if row.asset == asset and row.kind is Kind.ISSUE)
        burns = -sum(row.delta_atoms for row in rows if row.asset == asset and row.kind is Kind.BURN)
        conservation.append(AssetConservationRowV1(asset, burns, issues, burns, issues, issues, burns))
    fee_assets = sorted({row.asset for row in rows if row.kind is Kind.FEE_ALLOCATION})
    fees = [(asset, sum(r.delta_atoms for r in rows if r.asset == asset and r.kind is Kind.FEE_ALLOCATION))
            for asset in fee_assets]
    return Plan(
        tuple(sorted(rows, key=lambda row: row.key)), tuple(conservation),
        tuple(FeeConservationRowV1(asset, value, value, 0) for asset, value in fees),
        (LaneWriteV1(lane, ZERO_ROOT_V1, ZERO_ROOT_V1),),
        (OCCURRENCE,) if lane is LaneIdV1.ZDEX_TOKENOMICS else (), (),
    )


def _all_coordinates() -> tuple[Row, ...]:
    return tuple(
        Row(kind, principal, asset, domain, -1 if kind in (Kind.BURN, Kind.CUSTODY) else 1)
        for kind, principal, asset, domain in product(Kind, ("alice", "bob"), ("quote", "zdex"), ("pool", "treasury"))
    )


def _assert_output(actual: Plan, keys: tuple[RawKey, ...], expected: list[int]) -> None:
    assert tuple(_raw(row) for row in actual.rows) == tuple(
        (key, delta) for key, delta in zip(keys, expected, strict=True) if delta != 0
    )


def test_complete_key_bridge_covers_all_nine_kinds_and_each_coordinate() -> None:
    assert set(KINDS) == set(Kind)
    rows = _all_coordinates()
    assert len({_key_term(_raw(row)[0]) for row in rows}) == len(rows) == 72
    assert (LOWER, UPPER) == (MIN_DELTA_ATOMS_V1, MAX_DELTA_ATOMS_V1)


def test_real_materializer_matches_independent_prefix_sums_and_full_lean_keys(lean: Path, tmp_path: Path) -> None:
    anchors = (LOWER, LOWER + 1, -2, -1, 1, 2, UPPER - 1, UPPER)
    corpus = [(), _all_coordinates()] + [
        (Row(Kind.CUSTODY, "alice", "quote", "pool", delta),
         Row(Kind.FEE_ALLOCATION, "alice", "quote", "pool", fee))
        for delta, fee in product(anchors, (1, 2, UPPER - 1, UPPER))
    ]
    probes, expected = [], []
    for rows in corpus:
        plan = _plan(rows)
        before = asdict(plan)
        expanded = _mirrored(plan.rows)
        keys = _keys(expanded)
        oracle = _prefix_oracle(expanded, keys)
        if oracle is None:
            with pytest.raises(ValueError, match=f"^{MATERIALIZE_ERROR}$"):
                _materialize_fee_allocations_v2(plan)
        else:
            actual = _materialize_fee_allocations_v2(plan)
            _assert_output(actual, keys, oracle)
            assert replace(actual, rows=plan.rows) == plan
        assert asdict(plan) == before
        probes.append(_observation(f"checkedMaterialize i128 {_terms(tuple(map(_raw, plan.rows)))}", keys))
        expected.append(oracle)
    assert len(corpus) == 34 and None in expected and any(x is not None for x in expected)
    _check_observations(lean, tmp_path / "MaterializationCorpus.lean", probes, expected)


def test_real_composer_matches_independent_signed_boundaries_and_complete_rows(lean: Path, tmp_path: Path) -> None:
    anchors = (LOWER, LOWER + 1, -2, -1, 1, 2, UPPER - 1, UPPER)
    corpus: list[tuple[tuple[Row, ...], tuple[Row, ...]]] = [
        ((Row(Kind.CUSTODY, "alice", "quote", "pool", first),),
         (Row(Kind.CUSTODY, "alice", "quote", "pool", second),))
        for first, second in product(anchors, repeat=2)
    ]
    corpus += [((), ()), ((), _all_coordinates())]
    probes, expected = [], []
    for spot_rows, tokenomics_rows in corpus:
        spot = _plan(spot_rows, LaneIdV1.SPOT_LIQUIDITY)
        tokenomics = _plan(tokenomics_rows)
        before = (asdict(spot), asdict(tokenomics))
        rows = tuple(map(_raw, spot.rows + tokenomics.rows))
        keys = _keys(rows)
        oracle = _prefix_oracle(rows, keys)
        if oracle is None:
            with pytest.raises(ValueError, match=f"^{COMPOSE_ERROR}$"):
                _compose_effects_v2(spot, tokenomics)
        else:
            actual = _compose_effects_v2(spot, tokenomics)
            _assert_output(actual, keys, oracle)
            assert actual.occurrence_consumptions == (OCCURRENCE,)
            assert actual.lane_writes == spot.lane_writes + tokenomics.lane_writes
            assert actual.asset_conservation == tokenomics.asset_conservation
            assert actual.fee_conservation == tokenomics.fee_conservation
            assert actual.external_outbox_enqueue == ()
        assert (asdict(spot), asdict(tokenomics)) == before
        expression = f"checkedCompose i128 {_terms(tuple(map(_raw, spot.rows)))} {_terms(tuple(map(_raw, tokenomics.rows)))}"
        probes.append(_observation(expression, keys))
        expected.append(oracle)
    assert len(corpus) == 66 and None in expected and any(x is not None for x in expected)
    _check_observations(lean, tmp_path / "CompositionCorpus.lean", probes, expected)


def test_given_later_cancellation_when_materialization_overflows_then_stage_rejects(
    lean: Path, tmp_path: Path,
) -> None:
    spot = _plan((Row(Kind.CUSTODY, "alice", "quote", "pool", -1),), LaneIdV1.SPOT_LIQUIDITY)
    tokenomics = _plan((Row(Kind.CUSTODY, "alice", "quote", "pool", UPPER),
                       Row(Kind.FEE_ALLOCATION, "alice", "quote", "pool", 1)))
    before = (asdict(spot), asdict(tokenomics))
    expanded = _mirrored(tokenomics.rows)
    flattened = tuple(map(_raw, spot.rows)) + expanded
    keys = _keys(flattened)
    # A flattened pass would succeed. The actual earlier materialization rejects.
    assert _prefix_oracle(expanded, keys) is None
    assert _prefix_oracle(flattened, keys) is not None
    with pytest.raises(ValueError, match=f"^{MATERIALIZE_ERROR}$"):
        _materialize_fee_allocations_v2(tokenomics)
    assert (asdict(spot), asdict(tokenomics)) == before
    probes = [
        _observation(f"checkedMaterialize i128 {_terms(tuple(map(_raw, tokenomics.rows)))}", keys),
        _observation(f"checkedFold i128 empty {_terms(flattened)}", keys),
    ]
    _check_observations(lean, tmp_path / "StageBoundary.lean", probes,
                        [None, _prefix_oracle(flattened, keys)])


def test_given_materialized_boundary_when_route_adds_then_only_composition_overflows(
    lean: Path, tmp_path: Path,
) -> None:
    tokenomics = _plan((Row(Kind.CUSTODY, "alice", "quote", "pool", UPPER - 1),
                       Row(Kind.FEE_ALLOCATION, "alice", "quote", "pool", 1)))
    before_tokenomics = asdict(tokenomics)
    materialized = _materialize_fee_allocations_v2(tokenomics)
    probes, expected = [], []
    for delta in (-1, 1):
        spot = _plan((Row(Kind.CUSTODY, "alice", "quote", "pool", delta),), LaneIdV1.SPOT_LIQUIDITY)
        before = (asdict(spot), asdict(materialized))
        rows = tuple(map(_raw, spot.rows + materialized.rows))
        keys = _keys(rows)
        oracle = _prefix_oracle(rows, keys)
        if delta == 1:
            assert oracle is None
            with pytest.raises(ValueError, match=f"^{COMPOSE_ERROR}$"):
                _compose_effects_v2(spot, materialized)
        else:
            assert oracle is not None
            _assert_output(_compose_effects_v2(spot, materialized), keys, oracle)
        assert (asdict(spot), asdict(materialized)) == before
        probes.append(_observation(f"checkedCompose i128 {_terms(tuple(map(_raw, spot.rows)))} {_terms(tuple(map(_raw, materialized.rows)))}", keys))
        expected.append(oracle)
    assert asdict(tokenomics) == before_tokenomics
    _check_observations(lean, tmp_path / "TwoStageBoundary.lean", probes, expected)


def test_arbitrary_ordered_model_prefixes_match_independent_bounded_oracle(lean: Path, tmp_path: Path) -> None:
    keys = (("CUSTODY", "quote", "alice", "pool"), ("CUSTODY", "quote", "alice", "treasury"))
    alphabet = tuple(product(keys, (-2, -1, 1)))
    cases = [rows for length in range(4) for rows in product(alphabet, repeat=length)]
    probes = [_observation(f"checkedFold ⟨-2, 1⟩ empty {_terms(rows)}", keys) for rows in cases]
    expected = [_prefix_oracle(rows, keys, -2, 1) for rows in cases]
    assert len(cases) == 259
    _check_observations(lean, tmp_path / "OrderedPrefixes.lean", probes, expected)


@pytest.mark.parametrize("coordinate", ("guard", "kind", "principal", "asset", "domain"))
def test_executable_semantic_mutants_break_fixed_proofs_and_independent_observations(
    lean: Path, tmp_path: Path, coordinate: str,
) -> None:
    source = PROOF.read_text()
    definitions, theorems = source.split("\ntheorem ", maxsplit=1)
    key: RawKey = ("CUSTODY", "quote", "alice", "pool")
    rows: tuple[RawRow, ...]
    if coordinate == "guard":
        old = "if Fits bounds (initial row.key + row.delta) then"
        new = "if True then"
        rows = ((key, UPPER), (key, 1), (key, -1))
    else:
        old = "if row.key = key then row.delta else 0"
        kept = [name for name in ("kind", "principal", "asset", "domain") if name != coordinate]
        new = "if (" + ", ".join(f"row.key.{name}" for name in kept) + ") = ("
        new += ", ".join(f"key.{name}" for name in kept) + ") then row.delta else 0"
        # Mutate only the accumulator update, leaving the specification intact.
        start = definitions.index("def advance ")
        prefix, definitions = definitions[:start], definitions[start:]
        alternate = list(key)
        index = {"kind": 0, "asset": 1, "principal": 2, "domain": 3}[coordinate]
        alternate[index] = "LIABILITY" if coordinate == "kind" else "other"
        alternate_key: RawKey = (alternate[0], alternate[1], alternate[2], alternate[3])
        rows = ((key, 1), (alternate_key, 2))
    assert definitions.count(old) == 1
    mutated = definitions.replace(old, new, 1)
    if coordinate != "guard":
        mutated = prefix + mutated
    failed = _check(lean, tmp_path / "MutantProof.lean", mutated + "\ntheorem " + theorems)
    assert failed.returncode != 0, "semantic mutant survived unchanged theorem packet"
    output = failed.stdout + failed.stderr
    assert "error:" in output and "unexpected token" not in output and "Unknown identifier" not in output
    # Also execute the mutated definitions: proof-script failure alone is weak.
    executable = mutated + f"\nend {NAMESPACE}\n" + OBSERVATIONS
    keys = _keys(rows)
    observed = _check(lean, tmp_path / "MutantExecution.lean",
                      executable + _observation(f"checkedFold i128 empty {_terms(rows)}", keys))
    assert observed.returncode == 0, observed.stdout + observed.stderr
    value = json.loads(observed.stdout.strip())
    assert value.startswith("OK:")
    assert json.loads(value.removeprefix("OK:")) != _prefix_oracle(rows, keys)
