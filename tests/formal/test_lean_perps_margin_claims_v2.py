"""Universal modeled episode proofs plus finite correspondence to the Python helper.

The campaign derives each input once and runs the actual claim helper and Lean
``advance`` on that input. It compares complete account/binding/terminal outputs.
The domain has valid preprojection and one owner-preserving account replacement;
market arithmetic, command authorization, hashing and the global producer are
outside this bridge. In particular malformed missing-active-record behavior is
excluded (Python raises KeyError, while the model returns none).

Only the four Std-only source modules are compiled, into a fresh temporary tree,
with the installed pinned compiler. No Lake build, cache, network or Rust is used.
"""

from __future__ import annotations

import hashlib
import itertools
import json
from dataclasses import dataclass, replace
from pathlib import Path

import pytest

from src.core.global_settlement_types_v2 import (
    MAX_ATOMS_V2,
    LaneIdV2,
    TerminalObligationStatusV2,
    TerminalObligationV2,
)
from src.core.perps_margin_claims_v2 import advance_margin_claims_v2
from src.core.perps_margin_state_v2 import (
    PerpsMarginClaimBindingV2,
    PerpsMarginStateV2,
    margin_claim_id_v2,
)
from src.core.perps_margin_types_v1 import (
    PerpsMarginAccountStatusV1,
    PerpsMarginAccountV1,
    PerpsMarginStateV1,
)
from tests.core.test_perps_margin_module_v1 import _state
from tests.formal.lean_stdlib_gate_v1 import (
    FORBIDDEN_SOURCE_TOKENS,
    LEAN_PROJECT,
    TheoremReference,
    _check_axioms,
    _pinned_lean_executable,
    _run,
)

NS = "ZenoDEX.PerpsMarginClaimsV2"
MODULES = (
    "Proofs.GlobalSettlementCoreV2",
    "Proofs.GlobalEconomicStateRefinementV2",
    "Proofs.PerpsMarginTransitionV1",
    "Proofs.PerpsMarginClaimsV2",
)
PRELUDE = """import Proofs.PerpsMarginClaimsV2
open Proofs.GlobalSettlementCoreV2
open Proofs.GlobalEconomicStateRefinementV2
open ZenoDEX.PerpsMarginTransitionV1 (Account)
open ZenoDEX.PerpsMarginClaimsV2
"""
REFERENCES = tuple(TheoremReference(f"{NS}.{name}", kind) for name, kind in (
    ("advance_available", """∀ (s : State), WellFormed s → ∀ (a : Account)
      (fresh : Identifier),
      (activeId s a.id = none → a.collateral ≠ 0 → s.terminals fresh = none) →
      ∃ post, advance s a fresh = some post"""),
    ("correspondence_preserved", """∀ (s : State) (a : Account) (fresh : Identifier)
      (post : State), WellFormed s → OwnerPreserved s a → FitsU128 (a.collateral : Int) →
      advance s a fresh = some post → WellFormed post"""),
    ("advance_frame", """∀ (s : State) (a : Account) (fresh : Identifier) (post : State),
      advance s a fresh = some post → post.asset = s.asset ∧
      (∀ key, key ≠ a.id → post.entries key = s.entries key) ∧
      (∀ id, id ≠ (activeId s a.id).getD fresh → post.terminals id = s.terminals id)"""),
    ("drain_retains_last_amount", """∀ (s : State), WellFormed s → ∀ (a : Account)
      (fresh id : Identifier), activeId s a.id = some id → a.collateral = 0 →
      ∃ (old : TerminalObligation) (post : State), s.terminals id = some old ∧
      0 < old.amountAtoms ∧ advance s a fresh = some post ∧ activeId post a.id = none ∧
      post.terminals id = some { old with status := .drained }"""),
    ("refill_requires_fresh_record", """∀ (s : State) (a : Account) (fresh : Identifier)
      (post : State), activeId s a.id = none → 0 < a.collateral →
      advance s a fresh = some post → s.terminals fresh = none ∧
      activeId post a.id = some fresh ∧
      post.terminals fresh = some (openClaim s.asset fresh a)"""),
    ("refill_collision_rejected", """∀ (s : State) (a : Account) (fresh : Identifier)
      (old : TerminalObligation), activeId s a.id = none → 0 < a.collateral →
      s.terminals fresh = some old → advance s a fresh = none"""),
    ("inactive_history_preserved", """∀ (s : State), WellFormed s → ∀ (a : Account)
      (fresh : Identifier) (post : State) (id : Identifier) (old : TerminalObligation),
      s.terminals id = some old → old.status ≠ .open →
      advance s a fresh = some post → post.terminals id = some old"""),
    ("changed_terminal_admitted", """∀ (s : State), WellFormed s → ∀ (a : Account)
      (fresh : Identifier) (post : State), OwnerPreserved s a →
      FitsU128 (a.collateral : Int) → advance s a fresh = some post →
      ∀ (id : Identifier) (after : TerminalObligation), post.terminals id = some after →
      s.terminals id ≠ some after → TerminalDeltaAdmitted ⟨id, s.terminals id, after⟩"""),
    ("terminal_registry_retains", """∀ (s : State) (a : Account) (fresh : Identifier)
      (post : State), advance s a fresh = some post → ∀ (id : Identifier)
      (old : TerminalObligation), s.terminals id = some old →
      ∃ after, post.terminals id = some after"""),
    ("same_owner_state_well_formed", "WellFormed sameOwnerState"),
    ("same_owner_two_account_history", """∃ (drained refilled : State),
      advance sameOwnerState (aliceAccount "a" 0 2) "unused" = some drained ∧
      advance drained (aliceAccount "a" 1 3) "new-a" = some refilled ∧
      activeId refilled "a" = some "new-a" ∧
      refilled.entries "b" = sameOwnerState.entries "b" ∧
      refilled.terminals "old-b" = sameOwnerState.terminals "old-b" ∧
      refilled.terminals "old-a" = some
        { openClaim "usd" "old-a" (aliceAccount "a" 2 1) with status := .drained }"""),
))


@dataclass(frozen=True)
class Compiled:
    executable: Path
    directory: Path
    artifacts: dict[str, list[str]]
    source_hashes: dict[str, str]


def _setup(path: Path, module: str, artifacts: dict[str, list[str]]) -> Path:
    path.write_text(json.dumps({
        "name": module, "package?": None, "isModule": False, "imports?": None,
        "importArts": artifacts, "dynlibs": [], "plugins": [], "options": {},
    }), encoding="utf-8")
    return path


@pytest.fixture(scope="module")
def compiled(tmp_path_factory: pytest.TempPathFactory) -> Compiled:
    directory = tmp_path_factory.mktemp("lean-perps-claims-v2")
    executable = _pinned_lean_executable()
    artifacts: dict[str, list[str]] = {}
    hashes: dict[str, str] = {}
    for module in MODULES:
        relative = Path(*module.split(".")).with_suffix(".lean")
        source = (LEAN_PROJECT / relative).read_bytes()
        assert not FORBIDDEN_SOURCE_TOKENS.search(source.decode()), module
        captured = directory / relative
        captured.parent.mkdir(parents=True, exist_ok=True)
        captured.write_bytes(source)
        output = captured.with_suffix(".olean")
        setup = _setup(directory / f"{relative.stem}.json", module, artifacts)
        result = _run(executable, ["-DwarningAsError=true", "-R", str(directory),
            "--setup", str(setup), "-o", str(output), str(captured)], cwd=directory)
        assert not result.stdout and not result.stderr
        artifacts[module] = [str(output)]
        hashes[module] = hashlib.sha256(source).hexdigest()
    return Compiled(executable, directory, artifacts, hashes)


def _probe(compiled: Compiled, name: str, source: str) -> list[str]:
    path = compiled.directory / f"{name}.lean"
    path.write_text(PRELUDE + source, encoding="utf-8")
    setup = _setup(path.with_suffix(".json"), name, compiled.artifacts)
    result = _run(compiled.executable, ["-DwarningAsError=true", "-R", str(compiled.directory),
        "--setup", str(setup), str(path)], cwd=compiled.directory)
    assert not result.stderr
    return result.stdout.splitlines()


def test_universal_episode_theorems_have_independent_types_and_standard_axioms(compiled):
    source = "\n".join(
        f"example : {ref.type_expression} := @{ref.qualified_name}\n"
        f"#print axioms {ref.qualified_name}" for ref in REFERENCES
    )
    output = _probe(compiled, "TheoremConsumer", source)
    _check_axioms("\n".join(output), REFERENCES)


@dataclass(frozen=True)
class Case:
    name: str
    margin: PerpsMarginStateV2
    rows: tuple[TerminalObligationV2, ...]
    post: PerpsMarginStateV1
    account_id: str
    occurrence_id: str
    collision: bool = False


@dataclass(frozen=True)
class Observation:
    asset: str
    entries: tuple[tuple[PerpsMarginAccountV1, str | None], ...]
    rows: tuple[TerminalObligationV2, ...]


def _root(number: int) -> str:
    return f"0x{number:064x}"


def _row(identifier: str, owner: str, amount: int,
         status: TerminalObligationStatusV2 = TerminalObligationStatusV2.OPEN,
         lane: LaneIdV2 = LaneIdV2.PERPS_MARKET) -> TerminalObligationV2:
    asset, domain = ("zUSD", "perps_margin") if lane is LaneIdV2.PERPS_MARKET else ("OTHER", "other")
    return TerminalObligationV2(identifier, lane, owner, asset, domain, amount, status)


def _case(amounts: tuple[int, int], post_amount: int, selected: str, same_owner: bool,
          *, missing: bool = False, closed: bool = False) -> Case:
    accounts = tuple(PerpsMarginAccountV1(key, "alice" if key == "a" or same_owner else "bob",
        0, 0, amount, 1, PerpsMarginAccountStatusV1.OPEN)
        for key, amount in zip(("a", "b"), amounts, strict=True) if not (missing and key == selected))
    economic = _state(accounts=accounts)
    bindings = tuple(PerpsMarginClaimBindingV2(a.account_id, _root(100 + i))
        for i, a in enumerate(accounts) if a.collateral_atoms)
    claims = {b.account_id: b.obligation_id for b in bindings}
    rows = tuple(sorted((
        *(_row(claims[a.account_id], a.owner, a.collateral_atoms)
            for a in accounts if a.collateral_atoms),
        _row(_root(200), "alice", 7, TerminalObligationStatusV2.DRAINED),
        _row(_root(201), "alice", 0, TerminalObligationStatusV2.TOMBSTONED),
        _row(_root(202), "carol", 3, lane=LaneIdV2.ASSET_TRANSFER),
    ), key=lambda row: row.obligation_id))
    old = next((a for a in accounts if a.account_id == selected),
        PerpsMarginAccountV1(selected, "alice", 0, 0, 0, 0, PerpsMarginAccountStatusV1.OPEN))
    replacement = replace(old, collateral_atoms=post_amount, nonce=old.nonce + 1,
        status=PerpsMarginAccountStatusV1.CLOSED if closed else PerpsMarginAccountStatusV1.OPEN)
    post = replace(economic, accounts=tuple(sorted(
        (*(a for a in accounts if a.account_id != selected), replacement),
        key=lambda a: a.account_id)))
    return Case(f"{amounts}->{post_amount}/{selected}/same={same_owner}/new={missing}/close={closed}",
        PerpsMarginStateV2(economic, bindings), rows, post, selected, _root(300))


def _cases() -> tuple[Case, ...]:
    cases = [_case((left, right), amount, selected, same)
        for left, right, amount, selected, same in itertools.product(
            (0, 1, 2), (0, 1, 2), (0, 1, 2), ("a", "b"), (False, True))]
    cases.extend((
        _case((0, 2), 1, "a", True, missing=True),
        _case((0, 2), 0, "a", True, closed=True),
        _case((MAX_ATOMS_V2, 0), 0, "a", True),
        _case((0, 0), MAX_ATOMS_V2, "b", True),
    ))
    for status, lane in (
        (TerminalObligationStatusV2.DRAINED, LaneIdV2.PERPS_MARKET),
        (TerminalObligationStatusV2.TOMBSTONED, LaneIdV2.PERPS_MARKET),
        (TerminalObligationStatusV2.OPEN, LaneIdV2.ASSET_TRANSFER),
    ):
        case = _case((0, 2), 1, "a", True)
        fresh = margin_claim_id_v2(case.margin.economic_state, case.account_id, case.occurrence_id)
        cases.append(replace(case, name=f"occupied_fresh/{status}/{lane}", collision=True,
            rows=tuple(sorted((*case.rows, _row(fresh, "carol", 5, status, lane)),
                key=lambda row: row.obligation_id))))
    return tuple(cases)


def _observe(margin: PerpsMarginStateV2, rows: tuple[TerminalObligationV2, ...]) -> Observation:
    return Observation(margin.economic_state.collateral_asset,
        tuple((a, margin.claim_id(a.account_id)) for a in margin.economic_state.accounts), rows)


def _require_preprojection(case: Case) -> None:
    """Check campaign membership in the theorem's valid preprojection domain."""
    identifiers = tuple(row.obligation_id for row in case.rows)
    assert identifiers == tuple(sorted(set(identifiers)))
    claims = {row.obligation_id: row for row in case.rows
        if row.lane_id is LaneIdV2.PERPS_MARKET and row.status is TerminalObligationStatusV2.OPEN}
    assert set(claims) == {b.obligation_id for b in case.margin.active_claims}
    for account in case.margin.economic_state.accounts:
        identifier = case.margin.claim_id(account.account_id)
        if identifier is not None:
            assert claims[identifier] == _row(identifier, account.owner, account.collateral_atoms)
    before = case.margin.economic_state
    assert replace(before, accounts=case.post.accounts) == case.post
    assert tuple(a for a in before.accounts if a.account_id != case.account_id) == tuple(
        a for a in case.post.accounts if a.account_id != case.account_id)
    old, new = before.account(case.account_id), case.post.account(case.account_id)
    assert new is not None and (old is None or old.owner == new.owner)


def _run_python(case: Case) -> Observation | None:
    _require_preprojection(case)
    before = _observe(case.margin, case.rows)
    arguments = (case.margin, case.post, case.rows, case.account_id, case.occurrence_id)
    if case.collision:
        with pytest.raises(ValueError, match="^margin opening claim id already exists$"):
            advance_margin_claims_v2(*arguments)
        result = None
    else:
        margin, rows = advance_margin_claims_v2(*arguments)
        assert margin.economic_state == case.post
        result = _observe(margin, rows)
    assert _observe(case.margin, case.rows) == before
    return result


def _text(value: str) -> str:
    return json.dumps(value)


def _account_literal(account: PerpsMarginAccountV1) -> str:
    closed = str(account.status is PerpsMarginAccountStatusV1.CLOSED).lower()
    return (f"⟨{_text(account.account_id)}, {_text(account.owner)}, ({account.position_base}), "
        f"{account.entry_price_e8}, {account.collateral_atoms}, {account.nonce}, {closed}⟩")


def _entries_literal(observation: Observation) -> str:
    return "[" + ", ".join(f"⟨{_account_literal(account)}, "
        + ("none" if identifier is None else f"some {_text(identifier)}") + "⟩"
        for account, identifier in observation.entries) + "]"


def _rows_literal(rows: tuple[TerminalObligationV2, ...]) -> str:
    lanes = {LaneIdV2.PERPS_MARKET: "perpsMarket", LaneIdV2.ASSET_TRANSFER: "assetTransfer"}
    return "[" + ", ".join(
        f"⟨{_text(r.obligation_id)}, .{lanes[r.lane_id]}, {_text(r.claimant)}, {_text(r.asset)}, "
        f"{_text(r.liability_domain)}, {r.amount_atoms}, .{r.status.value.lower()}⟩" for r in rows) + "]"


def _observation_literal(observation: Observation | None) -> str:
    if observation is None:
        return "none"
    return (f"some ⟨{_text(observation.asset)}, {_entries_literal(observation)}, "
        f"{_rows_literal(observation.rows)}⟩")


BRIDGE = """
structure Snapshot where
  asset : Asset
  entries : List Entry
  terminals : List TerminalObligation
  deriving DecidableEq, Repr
def inputState (asset : Asset) (entries : List Entry)
    (rows : List TerminalObligation) : State :=
  ⟨asset, fun key => entries.find? (fun e => e.account.id == key),
    fun id => rows.find? (fun row => row.obligationId == id)⟩
def observeState (s : State) (keys ids : List Identifier) : Snapshot :=
  ⟨s.asset, keys.filterMap s.entries, ids.filterMap s.terminals⟩
def runCase (s : State) (a : Account) (fresh : Identifier)
    (keys ids : List Identifier) : Option Snapshot :=
  (advance s a fresh).map (fun post => observeState post keys ids)
"""


def _model_call(case: Case) -> str:
    before = _observe(case.margin, case.rows)
    fresh = margin_claim_id_v2(case.margin.economic_state, case.account_id, case.occurrence_id)
    keys = sorted({a.account_id for a, _ in before.entries} | {case.account_id})
    ids = sorted({r.obligation_id for r in case.rows} | {fresh})
    replacement = case.post.account(case.account_id)
    assert replacement is not None
    return (f"runCase (inputState {_text(before.asset)} {_entries_literal(before)} "
        f"{_rows_literal(before.rows)}) ({_account_literal(replacement)}) {_text(fresh)} "
        f"{json.dumps(keys)} {json.dumps(ids)}")


def test_finite_actual_python_helper_correspondence(compiled):
    cases = _cases()
    checks = [f"#eval decide ({_model_call(case)} = {_observation_literal(_run_python(case))})"
        for case in cases]
    output = _probe(compiled, "RuntimeCorrespondence", BRIDGE + "\n".join(checks))
    assert len(output) == len(cases)
    assert not [case.name for case, result in zip(cases, output, strict=True) if result != "true"]


def test_bridge_detects_history_loss_zeroed_drain_and_account_reassignment(compiled):
    case = _case((2, 2), 0, "a", True)
    actual = _run_python(case)
    assert actual is not None
    old_id = case.margin.claim_id("a")
    corruptions = (
        replace(actual, rows=tuple(row for row in actual.rows if row.obligation_id != old_id)),
        replace(actual, rows=tuple(replace(row, amount_atoms=0) if row.obligation_id == old_id
            else row for row in actual.rows)),
        replace(actual, rows=tuple(replace(row, status=TerminalObligationStatusV2.OPEN)
            if row.obligation_id == old_id else row for row in actual.rows)),
        replace(actual, entries=tuple((a, old_id if a.account_id == "b" else identifier)
            for a, identifier in actual.entries)),
    )
    checks = [f"#eval decide ({_model_call(case)} ≠ {_observation_literal(corrupt)})"
        for corrupt in corruptions]
    assert _probe(compiled, "NegativeControls", BRIDGE + "\n".join(checks)) == ["true"] * 4
