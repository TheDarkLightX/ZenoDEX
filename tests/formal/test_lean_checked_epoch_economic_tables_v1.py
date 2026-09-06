"""Universal table telescoping and finite Python epoch-row correspondence.

Grade-4 evidence checks every named theorem's independent consumer signature,
the source and its dependencies, and its axioms. The grade-3 arithmetic oracle
re-sums immutable prefixes and endpoint tables, independently of dictionary
accumulation. RIPR reaches the real composer with admitted plan shapes; full
rows, exact overflow errors and unchanged inputs expose lost key coordinates,
reordered addition and cancellation-masked overflow. Model-only mutants live in
temporary files. No shared runtime sources are changed.

The theorem assumes per-route ExactEconomicTables. Finite runtime comparisons
do not prove universal Python/Rust refinement, canonical tuple normalization,
route correctness, supply conservation, authentication or publication. The Lean
model deliberately has no command-count, metadata or whole-state admission gate.
"""

from __future__ import annotations

import json
import os
import re
import subprocess
from dataclasses import asdict, dataclass, replace
from pathlib import Path

import pytest

from src.core.epoch_effect_composition_v1 import compose_asset_lane_epoch_effect_plans_v1
from src.core.global_economic_state_delta_v1 import _require_amount_table_refinement_v1
from src.core.global_settlement_types_v1 import (
    ALL_LANE_IDS_V1,
    AssetConservationRowV1,
    EconomicAmountV1,
    EconomicEffectKindV1,
    EconomicEffectRowV1,
    FeeConservationRowV1,
    GlobalEconomicEffectPlanV1,
    GlobalEconomicStateV1,
    LaneIdV1,
    LaneStateRootV1,
    LaneWriteV1,
)

ROOT = Path(__file__).resolve().parents[2]
PROJECT = ROOT / "lean-mathlib"
MODULE = "CheckedEpochEconomicTablesV1"
NAMESPACE = f"Proofs.{MODULE}"
DEPENDENCIES = (
    "CheckedEconomicAggregationV1", "GlobalSettlementCoreV2", "GlobalEconomicStateRefinementV2",
)
LOWER, UPPER = -(1 << 127), (1 << 127) - 1
OVERFLOW = "epoch effect row total exceeds signed 128-bit atoms"
KINDS = {
    EconomicEffectKindV1.ACCOUNT_MOVEMENT: "accountMovement",
    EconomicEffectKindV1.ISSUE: "issue", EconomicEffectKindV1.BURN: "burn",
    EconomicEffectKindV1.CUSTODY: "custody", EconomicEffectKindV1.LIABILITY: "liability",
    EconomicEffectKindV1.RESERVE: "reserve", EconomicEffectKindV1.FEE_ALLOCATION: "feeAllocation",
    EconomicEffectKindV1.REWARD: "reward", EconomicEffectKindV1.SLASH: "slash",
}
TABLES = {
    "balances": EconomicEffectKindV1.ACCOUNT_MOVEMENT,
    "custody": EconomicEffectKindV1.CUSTODY,
    "liabilities": EconomicEffectKindV1.LIABILITY,
    "reserves": EconomicEffectKindV1.RESERVE,
}
RawKey = tuple[str, str, str, str]  # Python ordering: kind, asset, principal, domain.
RawRow = tuple[RawKey, int]
Commands = tuple[tuple[EconomicEffectRowV1, ...], ...]

# Independent signatures, including induction helpers: names alone are insufficient.
CLAIM_TYPES = {
    "encodeKind_eq_iff": "∀ a b : EffectKind, encodeKind a = encodeKind b ↔ a = b",
    "encodeKey_eq_iff": "∀ (a b : EffectKind) (p q : Principal) (x y : Asset) (d e : AccountingLocation), encodeKey a p x d = encodeKey b q y e ↔ a = b ∧ p = q ∧ x = y ∧ d = e",
    "encoded_keyed_sum": "∀ (rows : List EconomicEffectRow) (k : EffectKind) (p : Principal) (a : Asset) (d : AccountingLocation), keyedSum (encodeKey k p a d) (encodeRows rows) = (rows.map fun r => if r.kind = k ∧ r.principal = p ∧ r.asset = a ∧ r.custodyDomain = d then r.deltaAtoms else 0).sum",
    "encoded_plan_effect": "∀ (p : EffectPlan) (k : EffectKind) (o : Principal) (a : Asset) (d : AccountingLocation), keyedSum (encodeKey k o a d) (encodeRows p.rows) = effectFor k p o a d",
    "orderedRows_append": "∀ a b : List EffectPlan, orderedRows (a ++ b) = orderedRows a ++ orderedRows b",
    "exactEconomicTables_iff": "∀ (pre post : GlobalState) (p : EffectPlan), ExactEconomicTables pre post p ↔ ∀ t, ExactTableEffect (tableKind t) (tableRows t pre) (tableRows t post) p",
    "tableChain_append": "∀ {pre mid post : GlobalState} {a b : List EffectPlan}, TableChain pre a mid → TableChain mid b post → TableChain pre (a ++ b) post",
    "tableChain_telescopes": "∀ {pre post : GlobalState} {ps : List EffectPlan}, TableChain pre ps post → ∀ (t : Table) (p : Principal) (a : Asset) (d : AccountingLocation), amountAt (tableRows t post) p a d - amountAt (tableRows t pre) p a d = keyedSum (encodeKey (tableKind t) p a d) (orderedRows ps)",
    "checkedFold_append": "∀ (b : Bounds) (i : Totals) (xs ys : List Row), checkedFold b i (xs ++ ys) = (checkedFold b i xs).bind (fun m => checkedFold b m ys)",
    "checkedEpoch_success_iff": "∀ (b : Bounds) (ps : List EffectPlan), (∃ out, checkedEpoch b ps = .ok out) ↔ PrefixFits b empty (orderedRows ps)",
    "checkedEpoch_reject_iff": "∀ (b : Bounds) (ps : List EffectPlan), checkedEpoch b ps = .error .signedAggregationBounds ↔ ¬PrefixFits b empty (orderedRows ps)",
    "successful_epoch_complete_keys": "∀ (b : Bounds) (ps : List EffectPlan) (out : Totals), checkedEpoch b ps = .ok out → ∀ k : Key, out k = keyedSum k (orderedRows ps)",
    "successful_epoch_exact_tables": "∀ (b : Bounds) {pre post : GlobalState} {ps : List EffectPlan} (out : Totals), TableChain pre ps post → checkedEpoch b ps = .ok out → ∀ (t : Table) (p : Principal) (a : Asset) (d : AccountingLocation), amountAt (tableRows t post) p a d - amountAt (tableRows t pre) p a d = out (encodeKey (tableKind t) p a d)",
    "checked_epoch_table_composition_iff": "∀ (b : Bounds) {pre post : GlobalState} {ps : List EffectPlan}, TableChain pre ps post → ((∃ out, checkedEpoch b ps = .ok out ∧ ∀ t p a d, amountAt (tableRows t post) p a d - amountAt (tableRows t pre) p a d = out (encodeKey (tableKind t) p a d)) ↔ PrefixFits b empty (orderedRows ps))",
    "checked_ordered_prefix_equation": "∀ (b : Bounds) (xs ys : List EffectPlan) (out : Totals), checkedEpoch b (xs ++ ys) = .ok out → ∃ mid, checkedEpoch b xs = .ok mid ∧ checkedFold b mid (orderedRows ys) = .ok out ∧ ∀ k, mid k = keyedSum k (orderedRows xs) ∧ out k = mid k + keyedSum k (orderedRows ys)",
    "successful_prefix_exact_tables": "∀ (b : Bounds) {pre mid post : GlobalState} {xs ys : List EffectPlan} (out : Totals), TableChain pre xs mid → TableChain mid ys post → checkedEpoch b (xs ++ ys) = .ok out → ∃ m, checkedEpoch b xs = .ok m ∧ checkedFold b m (orderedRows ys) = .ok out ∧ ∀ t p a d, amountAt (tableRows t mid) p a d - amountAt (tableRows t pre) p a d = m (encodeKey (tableKind t) p a d) ∧ amountAt (tableRows t post) p a d - amountAt (tableRows t mid) p a d = out (encodeKey (tableKind t) p a d) - m (encodeKey (tableKind t) p a d)",
    "successful_within_route_prefix_fits": "∀ (b : Bounds) (xs ys : List EffectPlan) (p : EffectPlan) (rs ts : List EconomicEffectRow) (r : EconomicEffectRow), p.rows = rs ++ r :: ts → ∀ out : Totals, checkedEpoch b (xs ++ p :: ys) = .ok out → Fits b (keyedSum (encodeRow r).key (orderedRows xs) + keyedSum (encodeRow r).key (encodeRows rs) + r.deltaAtoms)",
    "out_of_range_route_prefix_rejects": "∀ (b : Bounds) (xs ys : List EffectPlan) (p : EffectPlan) (rs ts : List EconomicEffectRow) (r : EconomicEffectRow), p.rows = rs ++ r :: ts → ¬Fits b (keyedSum (encodeRow r).key (orderedRows xs) + keyedSum (encodeRow r).key (encodeRows rs) + r.deltaAtoms) → checkedEpoch b (xs ++ p :: ys) = .error .signedAggregationBounds",
    "example_route_tables": "∀ (h j : Nat) (a b : Int), ExactEconomicTables (exampleState h a) (exampleState j b) (examplePlan (b - a))",
    "positive_tables_same_epoch_example": "TableChain (exampleState 100 20) [examplePlan 3, examplePlan (-2)] (exampleState 101 21) ∧ checkedEpoch i128 [examplePlan 3, examplePlan (-2)] = .ok exampleOutput ∧ exampleOutput (encodeKey .accountMovement \"alice\" \"USD\" \"vault\") = 1 ∧ exampleOutput (encodeKey .custody \"alice\" \"USD\" \"vault\") = 2 ∧ exampleOutput (encodeKey .liability \"alice\" \"USD\" \"vault\") = 3 ∧ exampleOutput (encodeKey .reserve \"alice\" \"USD\" \"vault\") = 4 ∧ (∀ t, 0 < amountAt (tableRows t (exampleState 100 20)) \"alice\" \"USD\" \"vault\" ∧ 0 < amountAt (tableRows t (exampleState 101 23)) \"alice\" \"USD\" \"vault\" ∧ 0 < amountAt (tableRows t (exampleState 101 21)) \"alice\" \"USD\" \"vault\")",
}
OPENS = f"""
open Proofs.GlobalSettlementCoreV2 Proofs.GlobalEconomicStateRefinementV2
open Proofs.CheckedEconomicAggregationV1 {NAMESPACE}
"""
OBSERVE = """
def observe (keys : List Key) : Except Reject Totals → String
  | .ok totals => "OK:" ++ reprStr (keys.map totals)
  | .error .signedAggregationBounds => "ERR"
"""


@dataclass(frozen=True)
class LeanSubject:
    executable: Path
    source: Path
    library: Path


def _compile(subject: LeanSubject, path: Path, output: Path | None = None) -> subprocess.CompletedProcess[str]:
    command = [str(subject.executable), "-DwarningAsError=true", "-R", str(subject.source)]
    if output is not None:
        command.extend(("-o", str(output)))
    return subprocess.run(
        [*command, str(path)], cwd=subject.source,
        env=dict(os.environ, LEAN_PATH=str(subject.library)), capture_output=True,
        text=True, check=False, timeout=90,
    )


@pytest.fixture(scope="module")
def lean(tmp_path_factory: pytest.TempPathFactory) -> LeanSubject:
    assert (PROJECT / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.27.0"
    located = subprocess.run(["elan", "which", "lean"], cwd=PROJECT, capture_output=True,
                             text=True, check=True, timeout=30)
    executable = Path(located.stdout.strip())
    version = subprocess.run([str(executable), "--version"], capture_output=True,
                             text=True, check=True, timeout=30)
    assert "version 4.27.0," in version.stdout
    directory = tmp_path_factory.mktemp("checked-epoch-tables")
    source, library = directory / "source", directory / "library"
    (source / "Proofs").mkdir(parents=True)
    (library / "Proofs").mkdir(parents=True)
    subject = LeanSubject(executable, source, library)
    for name in (*DEPENDENCIES, MODULE):
        captured = source / "Proofs" / f"{name}.lean"
        captured.write_bytes((PROJECT / "Proofs" / f"{name}.lean").read_bytes())
        result = _compile(subject, captured, library / "Proofs" / f"{name}.olean")
        assert result.returncode == 0, result.stdout + result.stderr
        assert result.stdout == result.stderr == ""
    return subject


def _probe(lean: LeanSubject, name: str, body: str) -> str:
    path = lean.source / f"{name}.lean"
    path.write_text(f"import {NAMESPACE}\n{OPENS}\n{body}")
    result = _compile(lean, path)
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stderr == ""
    return result.stdout


def test_all_named_types_sources_and_axioms(lean: LeanSubject) -> None:
    source = (lean.source / "Proofs" / f"{MODULE}.lean").read_text()
    assert re.search(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b", source) is None
    assert tuple(re.findall(r"^theorem (\w+)", source, re.MULTILINE)) == tuple(CLAIM_TYPES)
    consumers = "\n".join(
        f"example : {signature} := @{NAMESPACE}.{name}\n#print axioms {NAMESPACE}.{name}"
        for name, signature in CLAIM_TYPES.items()
    )
    report = " ".join(_probe(lean, "TheoremConsumers", consumers).split())
    for name in CLAIM_TYPES:
        found = re.search(re.escape(f"'{NAMESPACE}.{name}' ") +
                          r"(?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", report)
        assert found, (name, report)
        axioms = {entry.strip() for entry in (found.group(1) or "").split(",") if entry.strip()}
        assert axioms <= {"propext", "Quot.sound", "Classical.choice"}, (name, axioms)
    imports = (PROJECT / "Proofs.lean").read_text().splitlines()
    assert f"import {NAMESPACE}" in imports
    assert "import Proofs.CheckedEconomicAggregationV1" in imports


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _raw(row: EconomicEffectRowV1) -> RawRow:
    return row.key, row.delta_atoms


def _plan(rows: tuple[EconomicEffectRowV1, ...], index: int) -> GlobalEconomicEffectPlanV1:
    rows = tuple(sorted(rows, key=lambda row: row.key))
    assets = sorted({row.asset for row in rows})
    conservation, fees = [], []
    for asset in assets:
        issued = sum(row.delta_atoms for row in rows if row.asset == asset and row.kind is EconomicEffectKindV1.ISSUE)
        burned = -sum(row.delta_atoms for row in rows if row.asset == asset and row.kind is EconomicEffectKindV1.BURN)
        allocated = sum(row.delta_atoms for row in rows if row.asset == asset and row.kind is EconomicEffectKindV1.FEE_ALLOCATION)
        if issued or burned:
            conservation.append(AssetConservationRowV1(asset, 100, 100 + issued - burned,
                                100, 100 + issued - burned, issued, burned))
        if allocated:
            fees.append(FeeConservationRowV1(asset, allocated, allocated, 0))
    return GlobalEconomicEffectPlanV1(rows, tuple(conservation), tuple(fees),
        (LaneWriteV1(LaneIdV1.ASSET_TRANSFER, _root(100 + index), _root(101 + index)),),
        (_root(1000 + index),), ())


def _oracle(commands: Commands) -> tuple[RawRow, ...] | None:
    rows = tuple(_raw(row) for command in commands for row in command)
    for index, (key, _) in enumerate(rows):
        prefix_total = sum(delta for other, delta in rows[:index + 1] if other == key)
        if not LOWER <= prefix_total <= UPPER:
            return None
    totals = ((key, sum(delta for other, delta in rows if other == key))
              for key in sorted({key for key, _ in rows}))
    return tuple((key, delta) for key, delta in totals if delta != 0)


def _row_term(row: EconomicEffectRowV1) -> str:
    values = ", ".join(json.dumps(v) for v in (row.principal, row.asset, row.custody_domain))
    return f"⟨.{KINDS[row.kind]}, {values}, ({row.delta_atoms} : Int)⟩"


def _plans_term(commands: Commands) -> str:
    plans = ["{ EffectPlan.empty with rows := [" + ", ".join(map(_row_term, rows)) + "] }"
             for rows in commands]
    return "[" + ", ".join(plans) + "]"


def _observation(commands: Commands) -> tuple[str, list[int] | None]:
    keys = sorted({row.key for rows in commands for row in rows} |
                  {("CUSTODY", "absent-asset", "absent-owner", "absent-domain")})
    terms = [f"encodeKey .{KINDS[EconomicEffectKindV1(kind)]} " +
             " ".join(json.dumps(v) for v in (owner, asset, domain))
             for kind, asset, owner, domain in keys]
    oracle = _oracle(commands)
    expected = None if oracle is None else [dict(oracle).get(key, 0) for key in keys]
    return f"#eval observe [{', '.join(terms)}] (checkedEpoch i128 {_plans_term(commands)})", expected


def _corpus() -> list[Commands]:
    corpus: list[Commands] = []
    traces = ((UPPER, 1, -1), (LOWER, -1, 1), (UPPER, -1, 1), (LOWER, 1, -1), (3, -3))
    for kind in TABLES.values():
        for deltas in traces:
            corpus.append(tuple((EconomicEffectRowV1(kind, "alice", "USD", "vault", delta),)
                                for delta in deltas))
    base = EconomicEffectRowV1(EconomicEffectKindV1.ACCOUNT_MOVEMENT, "alice", "USD", "vault", UPPER)
    for alternative in (
        replace(base, kind=EconomicEffectKindV1.CUSTODY, delta_atoms=1),
        replace(base, principal="bob", delta_atoms=1),
        replace(base, asset="EUR", delta_atoms=1),
        replace(base, custody_domain="escrow", delta_atoms=1),
    ):
        corpus.append(((base,), (alternative,)))
    corpus.append((tuple(EconomicEffectRowV1(kind, "alice", "USD", "vault",
                        -1 if kind is EconomicEffectKindV1.BURN else 1)
                        for kind in EconomicEffectKindV1),))
    corpus.append(tuple((replace(base, delta_atoms=1 if i % 2 == 0 else -1),) for i in range(64)))
    return corpus


def test_actual_composer_matches_independent_prefix_sums_and_lean(lean: LeanSubject) -> None:
    probes, expected = [], []
    corpus = _corpus()
    assert len(corpus) == 26
    for commands in corpus:
        plans = tuple(_plan(rows, i) for i, rows in enumerate(commands))
        ordered = tuple(plan.rows for plan in plans)
        before = tuple(asdict(plan) for plan in plans)
        oracle = _oracle(ordered)
        if oracle is None:
            with pytest.raises(ValueError, match=f"^{OVERFLOW}$"):
                compose_asset_lane_epoch_effect_plans_v1(plans)
        else:
            actual = compose_asset_lane_epoch_effect_plans_v1(plans)
            assert tuple(map(_raw, actual.rows)) == oracle
            assert actual.lane_writes == (LaneWriteV1(LaneIdV1.ASSET_TRANSFER,
                    plans[0].lane_writes[0].pre_root, plans[-1].lane_writes[0].post_root),)
            assert actual.occurrence_consumptions == tuple(sorted(p.occurrence_consumptions[0] for p in plans))
        assert tuple(asdict(plan) for plan in plans) == before
        # Every nonempty command prefix is observed, including prefixes that reject.
        for end in range(1, len(ordered) + 1):
            probe, observation = _observation(ordered[:end])
            probes.append(probe)
            expected.append(observation)
    lines = _probe(lean, "RuntimePrefixes", OBSERVE + "\n".join(probes)).splitlines()
    decoded = [json.loads(line) for line in lines]
    assert [None if value == "ERR" else json.loads(value.removeprefix("OK:"))
            for value in decoded] == expected
    assert expected.count(None) == 16


def _state(amount: int, height: int) -> GlobalEconomicStateV1:
    def rows(scale: int) -> tuple[EconomicAmountV1, ...]:
        values = (EconomicAmountV1("alice", "USD", "vault", scale * amount),
                  EconomicAmountV1("bob", "USD", "vault", 50),
                  EconomicAmountV1("alice", "EUR", "vault", 60),
                  EconomicAmountV1("alice", "USD", "escrow", 70))
        return tuple(sorted(values, key=lambda row: row.key))
    return GlobalEconomicStateV1("table-test", _root(1), 1, height, _root(2),
        tuple(LaneStateRootV1(lane, _root(10 + i), True, _root(30 + i))
              for i, lane in enumerate(ALL_LANE_IDS_V1)),
        balances=rows(1), custody=rows(2), liabilities=rows(3), reserves=rows(4))


def test_real_route_table_checks_compose_and_preserve_same_epoch_height(lean: LeanSubject) -> None:
    states = (_state(20, 100), _state(23, 101), _state(21, 101))
    commands = tuple(tuple(EconomicEffectRowV1(kind, "alice", "USD", "vault", scale * delta)
                     for scale, kind in enumerate(TABLES.values(), start=1)) for delta in (3, -2))
    plans = tuple(_plan(rows, i) for i, rows in enumerate(commands))
    snapshots = tuple(asdict(state) for state in states)
    for pre, post, plan in zip(states[:-1], states[1:], plans, strict=True):
        assert _require_amount_table_refinement_v1(pre, post, plan)
    composed = compose_asset_lane_epoch_effect_plans_v1(plans)
    actual = _require_amount_table_refinement_v1(states[0], states[-1], composed)
    expected = tuple(sorted((table, "alice", "USD", "vault", scale)
                            for scale, table in enumerate(TABLES, start=1)))
    assert tuple((r.table, r.owner, r.asset, r.custody_domain, r.delta_atoms) for r in actual) == expected
    assert states[1].height == states[2].height == states[0].height + 1
    assert tuple(asdict(state) for state in states) == snapshots
    # Wrong table identity reaches the real exact-tuple checker and fails specifically.
    wrong = replace(composed, rows=tuple(replace(r, custody_domain="escrow") for r in composed.rows))
    with pytest.raises(ValueError, match="^economic refinement balance delta mismatch$"):
        _require_amount_table_refinement_v1(states[0], states[-1], wrong)
    probe, expected_totals = _observation(commands)
    result = json.loads(_probe(lean, "TableEndpoints", OBSERVE + probe).strip())
    assert json.loads(result.removeprefix("OK:")) == expected_totals


def test_runtime_arity_guard_is_outside_the_model(lean: LeanSubject) -> None:
    empty = tuple(() for _ in range(65))
    for commands in ((), empty):
        plans = tuple(_plan(rows, i) for i, rows in enumerate(commands))
        with pytest.raises(ValueError, match="^asset-lane epoch requires between one and 64 route effect plans$"):
            compose_asset_lane_epoch_effect_plans_v1(plans)
        probe, expected = _observation(commands)
        result = json.loads(_probe(lean, f"Arity{len(commands)}", OBSERVE + probe).strip())
        assert json.loads(result.removeprefix("OK:")) == expected == [0]


@pytest.mark.parametrize(("start", "deltas"), (
    (0, (UPPER, 1, -1)), (UPPER + 2, (LOWER, -1, 1)),
))
def test_locally_exact_routes_reject_epoch_prefix_even_when_endpoint_fits(
    start: int, deltas: tuple[int, ...],
) -> None:
    template = _state(1, 100)
    commands = tuple((EconomicEffectRowV1(EconomicEffectKindV1.ACCOUNT_MOVEMENT,
                      "alice", "USD", "vault", delta),) for delta in deltas)
    plans = tuple(_plan(rows, i) for i, rows in enumerate(commands))
    states = tuple(replace(template, height=100 if i == 0 else 101,
                   balances=(EconomicAmountV1("alice", "USD", "vault", start + sum(deltas[:i])),))
                   for i in range(len(deltas) + 1))
    before = tuple(asdict(state) for state in states), tuple(asdict(plan) for plan in plans)
    for pre, post, plan in zip(states[:-1], states[1:], plans, strict=True):
        assert _require_amount_table_refinement_v1(pre, post, plan)
    final_delta = sum(deltas)
    assert LOWER <= final_delta <= UPPER
    final_plan = _plan((replace(commands[0][0], delta_atoms=final_delta),), 0)
    assert _require_amount_table_refinement_v1(states[0], states[-1], final_plan)
    assert _oracle(commands) is None
    with pytest.raises(ValueError, match=f"^{OVERFLOW}$"):
        compose_asset_lane_epoch_effect_plans_v1(plans)
    assert (tuple(asdict(state) for state in states), tuple(asdict(plan) for plan in plans)) == before


@pytest.mark.parametrize(("name", "old", "new"), (
    ("reverse_commands", "encodeRows plan.rows ++ orderedRows plans", "orderedRows plans ++ encodeRows plan.rows"),
    ("drop_domain", "⟨encodeKind kind, owner, asset, domain⟩", "⟨encodeKind kind, owner, asset, owner⟩"),
    ("swap_custody_liability", "| .custody, state => state.custody", "| .custody, state => state.liabilities"),
))
def test_semantic_model_mutants_fail_the_proof_packet(
    lean: LeanSubject, name: str, old: str, new: str,
) -> None:
    source = (lean.source / "Proofs" / f"{MODULE}.lean").read_text()
    assert source.count(old) == 1
    mutant = lean.source / f"Mutant_{name}.lean"
    # No shared source mutation; warnings disabled only to demand a proof error.
    mutant.write_text(source.replace(old, new).replace(
        f"namespace {NAMESPACE}", f"set_option linter.unusedVariables false\nnamespace {NAMESPACE}"))
    result = _compile(lean, mutant)
    assert result.returncode != 0
    assert "error:" in result.stdout and ("unsolved goals" in result.stdout or "Type mismatch" in result.stdout)
