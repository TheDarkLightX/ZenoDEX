"""Canonical epoch rows: universal value theorem and finite runtime evidence.

Grade-4 evidence compiles fresh pinned dependencies, independent theorem
consumer types and axiom audits. Grade-3 tuple expectations re-sum immutable
inputs and use the two explicit runtime sort orders. RIPR reaches actual
composer and endpoint-delta builders and observes complete tuples, exact
errors, unchanged inputs and duplicate-key rejection. Executed definitions-only
mutants are advisory negative controls, never substitute proof subjects.

Endpoint uniqueness is a premise of the universal theorem. Normal state
admission rejects duplicates; direct helper controls expose last-write versus
sum semantics. No universal Python/compiler, constructor-admission, canonical
byte/hash, conservation, performance or publication claim is made.
"""

from __future__ import annotations

import json
import re
import subprocess
from dataclasses import asdict, replace
from pathlib import Path

import pytest

from src.core.epoch_effect_composition_v1 import compose_asset_lane_epoch_effect_plans_v1
from src.core.global_economic_state_delta_v1 import (
    _amount_delta_rows_v1,
    _effect_amount_delta_rows_v1,
    _require_amount_table_refinement_v1,
)
from src.core.global_settlement_types_v1 import (
    EconomicAmountV1,
    EconomicEffectKindV1,
    EconomicEffectRowV1,
)
from tests.formal.test_lean_checked_epoch_economic_tables_v1 import (
    LOWER,
    OVERFLOW,
    PROJECT,
    TABLES,
    UPPER,
    Commands,
    LeanSubject,
    _compile,
    _corpus,
    _plan,
    _plans_term,
    _state,
)

MODULE = "CanonicalEpochEconomicRowsV1"
NAMESPACE = f"Proofs.{MODULE}"
DEPENDENCIES = (
    "CheckedEconomicAggregationV1", "GlobalSettlementCoreV2",
    "GlobalEconomicStateRefinementV2", "CheckedEpochEconomicTablesV1",
)
OPENS = f"""
open Proofs.GlobalSettlementCoreV2 Proofs.GlobalEconomicStateRefinementV2
open Proofs.CheckedEconomicAggregationV1 Proofs.CheckedEpochEconomicTablesV1 {NAMESPACE}
attribute [local instance] lexOrd
"""
OBSERVERS = """
def observeRows : Except Reject (List EconomicEffectRow) → String
  | .error _ => "ERR"
  | .ok rows => "OK:" ++ reprStr (rows.map fun r =>
      [r.kind.code, r.principal, r.asset, r.custodyDomain, toString r.deltaAtoms])
def observeDeltas : Except Reject (List DeltaRow) → String
  | .error _ => "ERR"
  | .ok rows => "OK:" ++ reprStr (rows.map fun r =>
      [tableCode r.table, r.owner, r.asset, r.domain, toString r.delta])
"""
CONTEXT = "∀ {pre post : GlobalState} {ps : List EffectPlan} (out : Totals), TableChain pre ps post → EndpointKeysUnique pre post → checkedEpoch i128 ps = .ok out → "
CLAIM_TYPES = {
    "mem_uniqueFirst": "∀ {α : Type} [DecidableEq α] (a : α) (xs : List α), a ∈ uniqueFirst xs ↔ a ∈ xs",
    "uniqueFirst_nodup": "∀ {α : Type} [DecidableEq α] (xs : List α), (uniqueFirst xs).Nodup",
    "sortOn_perm": "∀ {α β : Type} [Ord β] (f : α → β) (xs : List α), (sortOn f xs).Perm xs",
    "mem_sortOn": "∀ {α β : Type} [Ord β] (f : α → β) (a : α) (xs : List α), a ∈ sortOn f xs ↔ a ∈ xs",
    "sortOn_ordered": "∀ {α β : Type} [Ord β] [Std.TransOrd β] (f : α → β) (xs : List α), (sortOn f xs).Pairwise (fun a b => (compare (f a) (f b)).isLE = true)",
    "encode_decode_kind": "∀ k : Kind, encodeKind (decodeKind k) = k",
    "decode_encode_kind": "∀ k : EffectKind, decodeKind (encodeKind k) = k",
    "rowOf_key": "∀ (k : Key) (d : Int), (encodeRow (rowOf k d)).key = k",
    "rowOf_exemplar": "∀ (r : EconomicEffectRow) (d : Int), rowOf (encodeRow r).key d = {r with deltaAtoms := d}",
    "effect_code_injective": "∀ {a b : EffectKind}, a.code = b.code → a = b",
    "wireKey_injective": "∀ {a b : Key}, wireKey a = wireKey b → a = b",
    "mem_emissionKeys": "∀ (ps : List EffectPlan) (out : Totals) (k : Key), k ∈ emissionKeys ps out ↔ k ∈ sourceKeys ps ∧ out k ≠ 0",
    "emissionKeys_nodup": "∀ (ps : List EffectPlan) (out : Totals), (emissionKeys ps out).Nodup",
    "emissionKeys_ordered": "∀ (ps : List EffectPlan) (out : Totals), (emissionKeys ps out).Pairwise (fun a b => (compare (wireKey a) (wireKey b)).isLE = true)",
    "keyedSum_absent": "∀ (k : Key) (rs : List Row), k ∉ rs.map (fun r => r.key) → keyedSum k rs = 0",
    "successful_total_supported": "∀ (ps : List EffectPlan) (out : Totals), checkedEpoch i128 ps = .ok out → ∀ k : Key, out k ≠ 0 → k ∈ sourceKeys ps",
    "checkedFold_bounded": "∀ (b : Bounds) (a out : Totals) (rs : List Row), (∀ k, Fits b (a k)) → checkedFold b a rs = .ok out → ∀ k, Fits b (out k)",
    "successful_total_bounded": "∀ (ps : List EffectPlan) (out : Totals), checkedEpoch i128 ps = .ok out → ∀ k : Key, Fits i128 (out k)",
    "encode_rowOf": "∀ (k : Key) (d : Int), encodeRow (rowOf k d) = ⟨k, d⟩",
    "emitRows_keys": "∀ (ps : List EffectPlan) (out : Totals), (emitRows ps out).map (fun r => (encodeRow r).key) = emissionKeys ps out",
    "mem_emitRows": "∀ (ps : List EffectPlan) (out : Totals) (r : EconomicEffectRow), r ∈ emitRows ps out ↔ ∃ k, k ∈ sourceKeys ps ∧ out k ≠ 0 ∧ rowOf k (out k) = r",
    "emitted_row_value": "∀ (ps : List EffectPlan) (out : Totals) (r : EconomicEffectRow), r ∈ emitRows ps out → r.deltaAtoms = out (encodeRow r).key ∧ r.deltaAtoms ≠ 0",
    "keyedSum_unique_map": "∀ (ks : List Key) (out : Totals) (k : Key), ks.Nodup → keyedSum k (ks.map (fun q => (⟨q, out q⟩ : Row))) = if k ∈ ks then out k else 0",
    "emitted_complete_sums": "∀ (ps : List EffectPlan) (out : Totals), checkedEpoch i128 ps = .ok out → ∀ k : Key, keyedSum k (encodeRows (emitRows ps out)) = out k",
    "emissionKeys_strict": "∀ (ps : List EffectPlan) (out : Totals), (emissionKeys ps out).Pairwise (fun a b => compare (wireKey a) (wireKey b) = .lt)",
    "emitted_rows_canonical": "∀ (ps : List EffectPlan) (out : Totals), CanonicalEffectRows (emitRows ps out)",
    "emitted_rows_bounded": "∀ (ps : List EffectPlan) (out : Totals), checkedEpoch i128 ps = .ok out → ∀ r ∈ emitRows ps out, Fits i128 r.deltaAtoms",
    "amountSum_eq_amountAt": "∀ (k : AmountKey) (rs : List AmountRow), amountSum k rs = amountAt rs k.1 k.2.1 k.2.2",
    "amountSum_absent": "∀ (k : AmountKey) (rs : List AmountRow), k ∉ rs.map amountKey → amountSum k rs = 0",
    "lookupLast_absent": "∀ (k : AmountKey) (rs : List AmountRow), k ∉ rs.map amountKey → lookupLast k rs = 0",
    "lookupLast_eq_amountAt": "∀ (k : AmountKey) (rs : List AmountRow), (rs.map amountKey).Nodup → lookupLast k rs = amountAt rs k.1 k.2.1 k.2.2",
    "checkDeltaRows_of_bounded": "∀ rs : List DeltaRow, (∀ r ∈ rs, Fits i128 r.delta) → checkDeltaRows rs = .ok (rs.filter (fun r => decide (r.delta ≠ 0)))",
    "mem_endpointKeys": "∀ (pre post : List AmountRow) (k : AmountKey), k ∈ endpointKeys pre post ↔ k ∈ pre.map amountKey ∨ k ∈ post.map amountKey",
    "endpointKeys_nodup": "∀ pre post : List AmountRow, (endpointKeys pre post).Nodup",
    "endpoint_delta_equation": CONTEXT + "∀ (t : Table) (k : AmountKey), lookupLast k (tableRows t post) - lookupLast k (tableRows t pre) = out (encodeKey (tableKind t) k.1 k.2.1 k.2.2)",
    "endpoint_rows_bounded": CONTEXT + "∀ t : Table, ∀ r ∈ endpointRaw t (tableRows t pre) (tableRows t post), Fits i128 r.delta",
    "makeDelta_key": "∀ (t : Table) (k : AmountKey) (d : Int), deltaKey (makeDelta t k d) = k",
    "endpoint_delta_supported": "∀ (pre post : List AmountRow) (k : AmountKey), lookupLast k post - lookupLast k pre ≠ 0 → k ∈ endpointKeys pre post",
    "endpoint_nonzero_membership": "∀ (t : Table) (pre post : List AmountRow) (r : DeltaRow), r ∈ (endpointRaw t pre post).filter (fun x => decide (x.delta ≠ 0)) ↔ ∃ k, lookupLast k post - lookupLast k pre ≠ 0 ∧ makeDelta t k (lookupLast k post - lookupLast k pre) = r",
    "projected_emission_membership": "∀ (ps : List EffectPlan) (out : Totals), checkedEpoch i128 ps = .ok out → ∀ (t : Table) (r : DeltaRow), r ∈ projectRaw t (emitRows ps out) ↔ ∃ k : AmountKey, out (encodeKey (tableKind t) k.1 k.2.1 k.2.2) ≠ 0 ∧ makeDelta t k (out (encodeKey (tableKind t) k.1 k.2.1 k.2.2)) = r",
    "endpoint_projected_membership": CONTEXT + "∀ (t : Table) (r : DeltaRow), r ∈ (endpointRaw t (tableRows t pre) (tableRows t post)).filter (fun x => decide (x.delta ≠ 0)) ↔ r ∈ projectRaw t (emitRows ps out)",
    "endpointRaw_nodup": "∀ (t : Table) (pre post : List AmountRow), (endpointRaw t pre post).Nodup",
    "projectRaw_nodup": "∀ (t : Table) (ps : List EffectPlan) (out : Totals), (projectRaw t (emitRows ps out)).Nodup",
    "tableCode_injective": "∀ {a b : Table}, tableCode a = tableCode b → a = b",
    "deltaWire_injective": "∀ {a b : DeltaRow}, deltaWire a = deltaWire b → a = b",
    "sortOn_eq_of_membership": "∀ {α β : Type} [DecidableEq α] [Ord β] [Std.TransOrd β] [Std.LawfulEqOrd β] (f : α → β), (∀ {a b}, f a = f b → a = b) → ∀ xs ys : List α, xs.Nodup → ys.Nodup → (∀ a, a ∈ xs ↔ a ∈ ys) → sortOn f xs = sortOn f ys",
    "checked_epoch_canonical_amount_delta_rows": CONTEXT + "CanonicalEffectRows (emitRows ps out) ∧ (∀ r ∈ emitRows ps out, Fits i128 r.deltaAtoms) ∧ (∀ k, keyedSum k (encodeRows (emitRows ps out)) = out k) ∧ ∀ t, checkedStateDeltaRows t (tableRows t pre) (tableRows t post) = .ok (projectDeltaRows t (emitRows ps out))",
}


@pytest.fixture(scope="module")
def lean(tmp_path_factory: pytest.TempPathFactory) -> LeanSubject:
    assert (PROJECT / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.27.0"
    located = subprocess.run(["elan", "which", "lean"], cwd=PROJECT, capture_output=True,
                             text=True, check=True, timeout=30)
    executable = Path(located.stdout.strip())
    version = subprocess.run([str(executable), "--version"], capture_output=True,
                             text=True, check=True, timeout=30)
    assert "version 4.27.0," in version.stdout
    directory = tmp_path_factory.mktemp("canonical-epoch-rows")
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


def _probe(lean: LeanSubject, name: str, body: str, source: str | None = None) -> str:
    path = lean.source / f"{name}.lean"
    prefix = f"import {NAMESPACE}\n" if source is None else source
    path.write_text(prefix + OPENS + OBSERVERS + body)
    result = _compile(lean, path)
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stderr == ""
    return result.stdout


def _decode(output: str) -> list[list[list[str]] | None]:
    values = [json.loads(line) for line in output.splitlines()]
    return [None if value == "ERR" else json.loads(value.removeprefix("OK:")) for value in values]


def test_all_47_theorem_signatures_axioms_and_nonvacuous_application(lean: LeanSubject) -> None:
    source = (lean.source / "Proofs" / f"{MODULE}.lean").read_text()
    assert re.search(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b", source) is None
    assert tuple(re.findall(r"^theorem (\w+)", source, re.MULTILINE)) == tuple(CLAIM_TYPES)
    assert len(CLAIM_TYPES) == 47
    consumers = "\n".join(f"example : {signature} := @{NAMESPACE}.{name}\n#print axioms {NAMESPACE}.{name}"
                          for name, signature in CLAIM_TYPES.items())
    consumers += """
example : checkedStateDeltaRows .balances (exampleState 100 20).balances (exampleState 101 21).balances =
    .ok (projectDeltaRows .balances (emitRows [examplePlan 3, examplePlan (-2)] exampleOutput)) := by
  have unique : EndpointKeysUnique (exampleState 100 20) (exampleState 101 21) := by
    intro table
    cases table <;> decide
  exact (checked_epoch_canonical_amount_delta_rows exampleOutput
    positive_tables_same_epoch_example.1 unique positive_tables_same_epoch_example.2.1).2.2.2 .balances
"""
    report = " ".join(_probe(lean, "Consumers", consumers).split())
    for name in CLAIM_TYPES:
        found = re.search(re.escape(f"'{NAMESPACE}.{name}' ") +
                          r"(?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", report)
        assert found, (name, report)
        axioms = {a.strip() for a in (found.group(1) or "").split(",") if a.strip()}
        assert axioms <= {"propext", "Quot.sound", "Classical.choice"}, (name, axioms)


def _expected_rows(commands: Commands) -> list[list[str]] | None:
    rows = tuple(row for command in commands for row in command)
    for index, row in enumerate(rows):
        total = sum(other.delta_atoms for other in rows[:index + 1] if other.key == row.key)
        if not LOWER <= total <= UPPER:
            return None
    result = []
    for kind, asset, owner, domain in sorted({row.key for row in rows}):
        total = sum(row.delta_atoms for row in rows if row.key == (kind, asset, owner, domain))
        if total:
            result.append([kind, owner, asset, domain, str(total)])
    return result


def _emission_probe(commands: Commands) -> str:
    term = _plans_term(commands)
    return f"#eval observeRows ((checkedEpoch i128 {term}).map (emitRows {term}))\n"


def _sort_conflict() -> tuple[EconomicEffectRowV1, ...]:
    kind = EconomicEffectKindV1.ACCOUNT_MOVEMENT
    return (EconomicEffectRowV1(kind, "z", "A", "~", 2),
            EconomicEffectRowV1(kind, "A", "z", "!", 3),
            EconomicEffectRowV1(kind, "!", "~", "\\", 4))


def test_full_runtime_effect_tuples_cover_kind_order_keys_ascii_and_cancellation(lean: LeanSubject) -> None:
    corpus = _corpus()
    corpus.extend([
        (_sort_conflict(),),
        (tuple(EconomicEffectRowV1(kind, "owner", "asset", "domain", -i if kind is EconomicEffectKindV1.BURN else i)
               for i, kind in enumerate(EconomicEffectKindV1, start=1)),),
        ((EconomicEffectRowV1(EconomicEffectKindV1.CUSTODY, "!", "~" * 160, '"', 1),
          EconomicEffectRowV1(EconomicEffectKindV1.CUSTODY, "~", "!", "\\", 2)),),
        ((),),
    ])
    probes, expected = [], []
    for commands in corpus:
        plans = tuple(_plan(rows, i) for i, rows in enumerate(commands))
        ordered = tuple(plan.rows for plan in plans)
        snapshot = tuple(asdict(plan) for plan in plans)
        oracle = _expected_rows(ordered)
        if oracle is None:
            with pytest.raises(ValueError, match=f"^{OVERFLOW}$"):
                compose_asset_lane_epoch_effect_plans_v1(plans)
        else:
            actual = compose_asset_lane_epoch_effect_plans_v1(plans).rows
            assert [[r.kind.value, r.principal, r.asset, r.custody_domain, str(r.delta_atoms)] for r in actual] == oracle
        assert tuple(asdict(plan) for plan in plans) == snapshot
        probes.append(_emission_probe(ordered))
        expected.append(oracle)
    assert len(corpus) == 30
    assert _decode(_probe(lean, "FullEmissionTuples", "".join(probes))) == expected


def _amounts_term(rows: tuple[EconomicAmountV1, ...]) -> str:
    values = ["⟨" + ", ".join(json.dumps(x) for x in (r.owner, r.asset, r.custody_domain)) +
              f", ({r.amount_atoms} : Int)⟩" for r in rows]
    return "[" + ", ".join(values) + "]"


def _endpoint_probe(table: str, pre: tuple[EconomicAmountV1, ...], post: tuple[EconomicAmountV1, ...]) -> str:
    return f"#eval observeDeltas (checkedStateDeltaRows .{table} {_amounts_term(pre)} {_amounts_term(post)})\n"


def test_all_four_runtime_table_tuples_equal_constructed_endpoints_despite_sort_conflicts(lean: LeanSubject) -> None:
    coordinates = tuple((r.principal, r.asset, r.custody_domain) for r in _sort_conflict())
    amounts = ((40, 50, 60), (45, 47, 64), (42, 50, 59))
    states = []
    for index, values in enumerate(amounts):
        tables = {}
        for scale, table in enumerate(TABLES, start=1):
            tables[table] = tuple(sorted((EconomicAmountV1(*key, scale * amount)
                for key, amount in zip(coordinates, values, strict=True)), key=lambda row: row.key))
        states.append(replace(_state(1, 100 if index == 0 else 101),
            balances=tables["balances"], custody=tables["custody"],
            liabilities=tables["liabilities"], reserves=tables["reserves"]))
    commands = tuple(tuple(EconomicEffectRowV1(kind, *key, scale * (end - start))
        for scale, kind in enumerate(TABLES.values(), start=1)
        for key, start, end in zip(coordinates, amounts[i], amounts[i + 1], strict=True) if end != start)
        for i in range(2))
    plans = tuple(_plan(rows, i) for i, rows in enumerate(commands))
    snapshot = tuple(asdict(state) for state in states), tuple(asdict(plan) for plan in plans)
    for before, after, plan in zip(states[:-1], states[1:], plans, strict=True):
        assert _require_amount_table_refinement_v1(before, after, plan)
    composed = compose_asset_lane_epoch_effect_plans_v1(plans)
    assert _require_amount_table_refinement_v1(states[0], states[-1], composed)
    probes: list[str] = []
    expected: list[list[list[str]]] = []
    terms = _plans_term(tuple(plan.rows for plan in plans))
    for scale, (table, kind) in enumerate(TABLES.items(), start=1):
        oracle = sorted([[table, *key, str(scale * (end - start))]
            for key, start, end in zip(coordinates, amounts[0], amounts[-1], strict=True) if end != start])
        before_rows, after_rows = getattr(states[0], table), getattr(states[-1], table)
        actual = _amount_delta_rows_v1(table, before_rows, after_rows)
        projected = _effect_amount_delta_rows_v1(composed, table, kind)
        assert actual == projected
        assert [[r.table, r.owner, r.asset, r.custody_domain, str(r.delta_atoms)] for r in actual] == oracle
        probes.append(_endpoint_probe(table, before_rows, after_rows))
        probes.append(f"#eval observeDeltas ((checkedEpoch i128 {terms}).map (fun t => projectDeltaRows .{table} (emitRows {terms} t)))\n")
        expected.extend((oracle, oracle))
    assert _decode(_probe(lean, "EndpointProjectionTuples", "".join(probes))) == expected
    assert (tuple(asdict(state) for state in states), tuple(asdict(plan) for plan in plans)) == snapshot


def test_signed_endpoint_edges_zero_elision_and_exact_rejection(lean: LeanSubject) -> None:
    cases = ((0, UPPER), (0, UPPER + 1), (-LOWER, 0), (-LOWER + 1, 0), (0, 0), ((1 << 128) - 1, (1 << 128) - 1))
    probes, expected = [], []
    for before, after in cases:
        pre = (EconomicAmountV1("alice", "USD", "vault", before),)
        post = (EconomicAmountV1("alice", "USD", "vault", after),)
        delta = after - before
        if LOWER <= delta <= UPPER:
            oracle = [] if delta == 0 else [["balances", "alice", "USD", "vault", str(delta)]]
            rows = _amount_delta_rows_v1("balances", pre, post)
            assert [[r.table, r.owner, r.asset, r.custody_domain, str(r.delta_atoms)] for r in rows] == oracle
        else:
            oracle = None
            with pytest.raises(ValueError, match="^economic refinement state delta exceeds signed 128-bit bounds$"):
                _amount_delta_rows_v1("balances", pre, post)
        probes.append(_endpoint_probe("balances", pre, post))
        expected.append(oracle)
    assert _decode(_probe(lean, "EndpointBoundaries", "".join(probes))) == expected


def test_duplicate_endpoints_expose_last_write_and_uniqueness_premise(lean: LeanSubject) -> None:
    pre = (EconomicAmountV1("alice", "USD", "vault", 10), EconomicAmountV1("alice", "USD", "vault", 20))
    post = (EconomicAmountV1("alice", "USD", "vault", 25),)
    with pytest.raises(ValueError, match="^global state balances must be canonically ordered and unique$"):
        replace(_state(1, 100), balances=pre)
    rows = _amount_delta_rows_v1("balances", pre, post)
    assert len(rows) == 1 and rows[0].delta_atoms == 5
    assert _decode(_probe(lean, "DuplicateEndpoint", _endpoint_probe("balances", pre, post))) == [
        [["balances", "alice", "USD", "vault", "5"]]]
    values = _probe(lean, "DuplicateSemantics", f"""
#eval reprStr [lookupLast ("alice", "USD", "vault") {_amounts_term(pre)},
  amountAt {_amounts_term(pre)} "alice" "USD" "vault"]
#eval decide (({_amounts_term(pre)}.map amountKey).Nodup)
""")
    first, second = values.splitlines()
    assert json.loads(json.loads(first)) == [20, 30]
    assert json.loads(second) is False


@pytest.mark.parametrize(("name", "old", "new"), (
    ("effect_sort_coordinates", "((decodeKind key.kind).code, key.asset, key.principal, key.domain)",
     "((decodeKind key.kind).code, key.principal, key.asset, key.domain)"),
    ("delta_sort_coordinates", "(tableCode row.table, row.owner, row.asset, row.domain, row.delta)",
     "(tableCode row.table, row.asset, row.owner, row.domain, row.delta)"),
    ("retain_zero_effects", "decide (totals key ≠ 0)", "decide True"),
    ("sum_duplicate_endpoints", "if key ∈ rows.map amountKey then lookupLast key rows\n      else if amountKey row = key then row.amountAtoms else 0",
     "(if amountKey row = key then row.amountAtoms else 0) + lookupLast key rows"),
    ("ignore_endpoint_bounds", "if Fits i128 row.delta then", "if True then"),
))
def test_executed_model_mutants_disagree_with_real_tuple_oracles(
    lean: LeanSubject, name: str, old: str, new: str,
) -> None:
    source = (lean.source / "Proofs" / f"{MODULE}.lean").read_text()
    assert source.count(old) == 1
    # Run altered definitions, not failed proofs or admitted theorem placeholders.
    definitions = re.sub(r"^theorem .*?(?=^(?:theorem|def|abbrev|structure|end)\b)", "", source,
                         flags=re.MULTILINE | re.DOTALL)
    definitions = definitions.replace(old, new).replace(
        f"namespace {NAMESPACE}", f"set_option linter.unusedVariables false\nnamespace {NAMESPACE}")
    commands = (_sort_conflict(),)
    cancel = ((EconomicEffectRowV1(EconomicEffectKindV1.CUSTODY, "alice", "USD", "vault", 3),),
              (EconomicEffectRowV1(EconomicEffectKindV1.CUSTODY, "alice", "USD", "vault", -3),))
    pre = (EconomicAmountV1("z", "A", "~", 10), EconomicAmountV1("A", "z", "!", 20))
    post = (EconomicAmountV1("z", "A", "~", 12), EconomicAmountV1("A", "z", "!", 23))
    duplicate = (EconomicAmountV1("alice", "USD", "vault", 10), EconomicAmountV1("alice", "USD", "vault", 20))
    duplicate_post = (EconomicAmountV1("alice", "USD", "vault", 25),)
    zero = (EconomicAmountV1("alice", "USD", "vault", 0),)
    excessive = (EconomicAmountV1("alice", "USD", "vault", UPPER + 1),)
    probes = (_emission_probe(commands) + _emission_probe(cancel) +
              _endpoint_probe("balances", pre, post) + _endpoint_probe("balances", duplicate, duplicate_post) +
              _endpoint_probe("balances", zero, excessive))
    real_effects = [compose_asset_lane_epoch_effect_plans_v1(tuple(_plan(rows, i) for i, rows in enumerate(cs))).rows
                    for cs in (commands, cancel)]
    real_deltas = [_amount_delta_rows_v1("balances", a, b) for a, b in ((pre, post), (duplicate, duplicate_post))]
    expected: list[list[list[str]] | None] = [
        [[r.kind.value, r.principal, r.asset, r.custody_domain, str(r.delta_atoms)] for r in rows]
        for rows in real_effects]
    expected.extend([[r.table, r.owner, r.asset, r.custody_domain, str(r.delta_atoms)] for r in rows]
                    for rows in real_deltas)
    with pytest.raises(ValueError, match="^economic refinement state delta exceeds signed 128-bit bounds$"):
        _amount_delta_rows_v1("balances", zero, excessive)
    expected.append(None)
    assert _decode(_probe(lean, f"Mutant_{name}", probes, definitions)) != expected
