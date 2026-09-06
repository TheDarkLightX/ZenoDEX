"""Sparse transfer: kernel proof plus finite independent runtime observations.

RIPR reaches the real leaf and private row updater, observes complete economic
rows and exact rejects/no-op roots, then kills executed temporary model mutants.
The constructor/selected-policy bridge is finite evidence, not universal
Python/Rust/compiler refinement. Neither this row projection nor its sender
guard proves authenticated or complete route admission. In particular positive
sender-as-fee-owner allocations can fail the separate global fee-mirror guard.
"""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
from dataclasses import asdict, dataclass, replace
from pathlib import Path

import pytest

from src.core.asset_transfer_module_v1 import _post_balances, transition_asset_transfer_v1
from src.core.asset_transfer_types_v1 import (
    AssetTransferAcceptedV1,
    AssetTransferCommandV1,
    AssetTransferContextV1,
    AssetTransferPolicyV1,
    AssetTransferRejectCodeV1,
    AssetTransferRejectedV1,
    AssetTransferStateV1,
)
from src.core.global_economic_state_delta_v1 import _require_amount_table_refinement_v1
from src.core.global_economic_state_effect_refinement_v1 import _require_fee_mirror_v1
from src.core.global_settlement_types_v1 import AssetSupplyV1, EconomicAmountV1
from tests.formal.test_lean_checked_epoch_economic_tables_v1 import (
    PROJECT,
    LeanSubject,
    _compile,
    _state,
)

ROOT = PROJECT.parent
MODULE = "AssetTransferSparseTablesV1"
NAMESPACE = f"Proofs.{MODULE}"
DEPENDENCIES = (
    "CheckedEconomicAggregationV1", "GlobalSettlementCoreV2",
    "GlobalEconomicStateRefinementV2", "CheckedEpochEconomicTablesV1",
    "CanonicalEpochEconomicRowsV1", "AssetTransferRefinementV1",
    "AssetTransferCustodyCompletionV1", "CheckedSignedDeltaRefinementV1",
    "AssetTransferCustodyCompositionV1",
)
PINNED_SOURCES = {
    "src/core/asset_transfer_module_v1.py": "754d75a37ad70868bf20263fc189fc9e4f5a77cb864d8a1c7973afc253c938d7",
    "src/core/asset_transfer_types_v1.py": "5757c8b692820613e1eac30b7103e857a73b42efebbdda62d0a4469511f41277",
    "src/core/global_economic_state_delta_v1.py": "5b06120b14176985a2889b81cc784145339b7f72720d7b161c74b296cb4e5634",
}
OPENS = f"""
open Proofs.GlobalSettlementCoreV2 Proofs.GlobalEconomicStateRefinementV2 {NAMESPACE}
attribute [local instance] lexOrd
"""
ACCEPTED = "∀ {i : Input}, Unique i.pre.balances → PositiveAccounts i.pre.balances → (step i).verdict = .accepted → "
CONSUMERS = {
    "accepted_sparse_transfer": ACCEPTED + "ExactEconomicTables i.pre (step i).post (step i).plan ∧ ExactSupplyEffects i.pre (step i).post (step i).plan ∧ CanonicalBalances (step i).post.balances ∧ (step i).post = { i.pre with balances := (step i).post.balances } ∧ i.command.sender = i.context.subjectId",
    "accepted_balance_equation": ACCEPTED + "∀ owner asset domain, amountAt (step i).post.balances owner asset domain - amountAt i.pre.balances owner asset domain = if i.command.asset = asset ∧ accounts = domain then T.delta (localState i) i.command owner else 0",
    "disclosed_tables_refine": "∀ {i : Input} {post : GlobalState} {plan : EffectPlan}, Unique i.pre.balances → PositiveAccounts i.pre.balances → (step i).verdict = .accepted → post.balances = (step i).post.balances → post.custody = i.pre.custody → post.liabilities = i.pre.liabilities → post.reserves = i.pre.reserves → post.supplies = i.pre.supplies → plan.rows = (step i).plan.rows → ExactEconomicTables i.pre post plan ∧ ExactSupplyEffects i.pre post plan",
    "rejected_step_noop": "∀ {i : Input} {code : T.RejectCode}, (step i).verdict = .rejected code → (step i).post = i.pre ∧ (step i).plan = EffectPlan.empty",
    "checkedUpdate_equation": "∀ {rows out : List AmountRow} {asset owner : String} {d : Int}, Unique rows → checkedUpdate rows asset owner d = .ok out → ∀ q : C.AmountKey, C.amountSum q out = C.amountSum q rows + if accountKey asset owner = q then d else 0",
    "finishBalances_canonical": "∀ {rows out : List AmountRow}, Unique rows → PositiveAccounts rows → finishBalances rows = .ok out → CanonicalBalances out",
    "demo_owned_supply": "OwnedMatchesSupply demo.pre ∧ OwnedMatchesSupply (step demo).post",
}
OBSERVERS = """
def balancesView (rows : List AmountRow) : List (List String) :=
  rows.map fun row => [row.owner, row.asset, row.custodyDomain, toString row.amountAtoms]
def effectsView (rows : List EconomicEffectRow) : List (List String) :=
  rows.map fun row => [row.kind.code, row.principal, row.asset, row.custodyDomain, toString row.deltaAtoms]
def observe (out : Result) : String :=
  let verdict := match out.verdict with
    | .accepted => "ACCEPTED"
    | .rejected code => code.code
  reprStr ([[verdict]] ++ balancesView out.post.balances ++ [["EFFECTS"]] ++ effectsView out.plan.rows)
def observeUpdate : Except T.RejectCode (List AmountRow) → String
  | .error code => reprStr [[code.code]]
  | .ok rows => reprStr ([ ["ACCEPTED"] ] ++ balancesView rows)
def padded (n : Nat) : String :=
  String.ofList (List.replicate (4 - (toString n).length) '0') ++ toString n
def ceilingRows : List AmountRow :=
  ⟨"a_sender", "USD", "accounts", 2⟩ ::
    (List.range 4095).map (fun n => ⟨"p" ++ padded n, "USD", "accounts", 1⟩)
"""


@pytest.fixture(scope="module")
def lean(tmp_path_factory: pytest.TempPathFactory) -> LeanSubject:
    assert (PROJECT / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.27.0"
    located = subprocess.run(["elan", "which", "lean"], cwd=PROJECT, capture_output=True,
                             text=True, check=True, timeout=30)
    executable = Path(located.stdout.strip())
    version = subprocess.run([str(executable), "--version"], capture_output=True,
                             text=True, check=True, timeout=30)
    assert "version 4.27.0," in version.stdout
    directory = tmp_path_factory.mktemp("asset-transfer-sparse")
    source, library = directory / "source", directory / "library"
    (source / "Proofs").mkdir(parents=True)
    (library / "Proofs").mkdir(parents=True)
    subject = LeanSubject(executable, source, library)
    for name in (*DEPENDENCIES, MODULE):
        captured = source / "Proofs" / f"{name}.lean"
        captured.write_bytes((PROJECT / "Proofs" / f"{name}.lean").read_bytes())
        result = _compile(subject, captured, library / "Proofs" / f"{name}.olean")
        assert result.returncode == 0, result.stdout + result.stderr
    return subject


def _probe(lean: LeanSubject, name: str, body: str, definitions: str | None = None) -> str:
    source = f"import {NAMESPACE}\n" if definitions is None else definitions
    probe = lean.source / f"{name}.lean"
    probe.write_text(source + OPENS + OBSERVERS + body)
    result = _compile(lean, probe)
    assert result.returncode == 0, result.stdout + result.stderr
    return result.stdout


def _decode(output: str) -> list[list[list[str]]]:
    return [json.loads(json.loads(line)) for line in output.splitlines()]


def test_principal_contract_types_axioms_and_source_subject(lean: LeanSubject) -> None:
    source = (lean.source / "Proofs" / f"{MODULE}.lean").read_text()
    code = re.sub(r"/-.*?-/", "", source, flags=re.DOTALL)
    assert re.search(r"\b(sorry|admit|axiom|native_decide)\b", code) is None
    names = re.findall(r"^theorem (\w+)", code, flags=re.MULTILINE)
    assert len(names) == 41 and set(CONSUMERS) <= set(names)
    body = "\n".join(f"example : {signature} := {name}" for name, signature in CONSUMERS.items())
    body += "\n" + "\n".join(f"#print axioms {NAMESPACE}.{name}" for name in names)
    result = _probe(lean, "IndependentConsumers", body)
    assert len(re.findall("depends on axioms|does not depend on any axioms", result)) == len(names)
    axioms = {a.strip() for group in re.findall(r"depends on axioms:\s*\[([^\]]*)\]", result)
              for a in group.split(",") if a.strip()}
    assert axioms <= {"propext", "Quot.sound", "Classical.choice"}
    for path, digest in PINNED_SOURCES.items():
        assert hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == digest


@dataclass(frozen=True)
class Case:
    name: str
    context: AssetTransferContextV1
    pre: AssetTransferStateV1
    command: AssetTransferCommandV1
    error: str | None = None
    ceiling: bool = False


def _case(name: str, *, owner: str = "treasury", fee: int = 2, amount: int = 30,
          rows: tuple[tuple[str, str, int], ...] | None = None, sender: str = "alice",
          recipient: str = "bob", subject: str | None = None, error: str | None = None) -> Case:
    root = "0x" + "01" * 32
    raw = rows if rows is not None else (("alice", "USD", 100), ("bob", "USD", 10),
        ("treasury", "USD", 5), ("alice", "EUR", 7), ("zebra", "EUR", 9))
    balances = tuple(sorted((EconomicAmountV1(p, a, "accounts", n) for p, a, n in raw), key=lambda r: r.key))
    assets = sorted({"USD", *(r.asset for r in balances)})
    supplies = tuple(AssetSupplyV1(a, sum(r.amount_atoms for r in balances if r.asset == a)) for a in assets)
    policies = tuple(AssetTransferPolicyV1(a, owner, fee if a == "USD" else 0, True) for a in assets)
    return Case(name, AssetTransferContextV1("test", root, root, 1, root, root, subject or sender, root),
        AssetTransferStateV1(root, policies, balances, supplies),
        AssetTransferCommandV1("asset_transfer", "USD", sender, recipient, amount, fee), error)


def _amounts_term(rows: tuple[EconomicAmountV1, ...]) -> str:
    return "[" + ",".join("⟨" + ",".join(json.dumps(v) for v in
        (r.owner, r.asset, r.custody_domain)) + f",({r.amount_atoms} : Int)⟩" for r in rows) + "]"


def _term(case: Case) -> str:
    policy = next(p for p in case.pre.policies if p.asset == "USD")
    balances = "ceilingRows" if case.ceiling else _amounts_term(case.pre.balances)
    supplies = "[" + ",".join(f"⟨{json.dumps(r.asset)},({r.amount_atoms} : Int)⟩" for r in case.pre.supplies) + "]"
    c = case.command
    command = "⟨" + ",".join(json.dumps(v) for v in (c.command_kind, c.asset, c.sender, c.recipient))
    command += f",({c.amount_atoms} : Int),({c.max_fee_atoms} : Int)⟩"
    return "{ context := ⟨" + json.dumps(case.context.module_release_id) + "," + json.dumps(case.context.subject_id) + "⟩," + \
        " moduleReleaseId := " + json.dumps(case.pre.module_release_id) + ", policy := ⟨" + \
        json.dumps(policy.asset) + "," + json.dumps(policy.fee_owner) + f",({policy.transfer_fee_atoms} : Int)," + \
        str(policy.enabled).lower() + "⟩, command := " + command + \
        ", pre := { staticGlobalState with balances := " + balances + ", supplies := " + supplies + " } }"


def _balances_view(rows: tuple[EconomicAmountV1, ...]) -> list[list[str]]:
    return [[r.owner, r.asset, r.custody_domain, str(r.amount_atoms)] for r in rows]


def _runtime_and_oracle(case: Case) -> list[list[str]]:
    before = (asdict(case.pre), asdict(case.context), asdict(case.command))
    result = transition_asset_transfer_v1(case.context, case.pre, case.command)
    assert before == (asdict(case.pre), asdict(case.context), asdict(case.command))
    if case.error:
        assert isinstance(result, AssetTransferRejectedV1) and result.code.value == case.error
        assert result.pre_state_root == result.post_state_root == case.pre.state_root and result.effects.is_empty
        return [[case.error], *_balances_view(case.pre.balances), ["EFFECTS"]]
    assert isinstance(result, AssetTransferAcceptedV1)
    c = case.command
    policy = next(p for p in case.pre.policies if p.asset == c.asset)
    # Independent signed-event summation; role aliasing is not implemented by map updates.
    events = ((c.sender, -c.amount_atoms - policy.transfer_fee_atoms),
              (c.recipient, c.amount_atoms), (policy.fee_owner, policy.transfer_fee_atoms))
    keys = {(r.asset, r.owner) for r in case.pre.balances} | {(c.asset, p) for p, _ in events}
    expected = []
    for a, p in sorted(keys):
        atoms = sum(r.amount_atoms for r in case.pre.balances if (r.asset, r.owner) == (a, p))
        atoms += sum(d for q, d in events if a == c.asset and p == q)
        if atoms:
            expected.append([p, a, "accounts", str(atoms)])
    assert _balances_view(result.post_state.balances) == expected
    effect_rows = [["ACCOUNT_MOVEMENT", p, c.asset, "accounts", str(sum(d for q, d in events if q == p))]
                   for p in sorted({p for p, _ in events}) if sum(d for q, d in events if q == p)]
    if policy.transfer_fee_atoms:
        effect_rows.append(["FEE_ALLOCATION", policy.fee_owner, c.asset, "accounts", str(policy.transfer_fee_atoms)])
    effect_rows.sort(key=lambda r: (r[0], r[2], r[1], r[3]))
    assert [[r.kind.value, r.principal, r.asset, r.custody_domain, str(r.delta_atoms)]
            for r in result.effects.rows] == effect_rows
    assert result.post_state.policies == case.pre.policies and result.post_state.supplies == case.pre.supplies
    global_pre = replace(_state(1, 100), balances=case.pre.balances, supplies=case.pre.supplies)
    global_post = replace(global_pre, height=101, balances=result.post_state.balances)
    _require_amount_table_refinement_v1(global_pre, global_post, result.effects)
    return [["ACCEPTED"], *expected, ["EFFECTS"], *effect_rows]


def _corpus() -> tuple[Case, ...]:
    upper = (1 << 127) - 1
    base = _case("distinct")
    cases = [base, _case("sender_fee", owner="alice"), _case("recipient_fee", owner="bob"),
        _case("zero_fee", fee=0), _case("zero_delete", rows=(("alice", "USD", 32), ("alice", "EUR", 7))),
        _case("new_recipient", recipient="!new"),
        _case("high_absolute", fee=0, amount=1, rows=(("alice", "USD", (1 << 128) - 1),)),
        _case("min_delta", fee=1, amount=upper, rows=(("alice", "USD", upper + 1),)),
        _case("max_delta", fee=0, amount=upper, rows=(("alice", "USD", upper),)),
        _case("aliased_gross", owner="alice", fee=upper, amount=upper, rows=(("alice", "USD", upper),)),
        _case("signed_overflow", fee=0, amount=upper + 1, rows=(("alice", "USD", upper + 1),), error="EFFECT_DELTA_OVERFLOW"),
        _case("underflow", amount=114, error="INSUFFICIENT_BALANCE"),
        _case("unauthorized", subject="mallory", error="UNAUTHORIZED_SUBJECT"),
        _case("self", recipient="alice", error="SELF_TRANSFER"),
        _case("zero", amount=0, error="ZERO_AMOUNT")]
    cases.extend((replace(base, name="release", context=replace(base.context, module_release_id="0x" + "02" * 32), error="RELEASE_MISMATCH"),
        replace(base, name="fee_limit", command=replace(base.command, max_fee_atoms=1), error="FEE_LIMIT_EXCEEDED"),
        replace(base, name="unknown_command", command=replace(base.command, command_kind="other"), error="UNKNOWN_COMMAND"),
        replace(base, name="unknown_asset", command=replace(base.command, asset="MISSING"), error="UNKNOWN_ASSET")))
    return tuple(cases)


def test_complete_leaf_rows_match_independent_arithmetic_and_table_checker(lean: LeanSubject) -> None:
    cases = _corpus()
    expected = [_runtime_and_oracle(case) for case in cases]
    actual = _decode(_probe(lean, "RuntimeCorpus", "\n".join(f"#eval observe (step ({_term(cases[i])}))" for i in range(len(cases)))))
    assert actual == expected


def _ceiling_case(amount: int) -> Case:
    rows = (("a_sender", "USD", 2),) + tuple((f"p{i:04}", "USD", 1) for i in range(4095))
    case = _case(f"ceiling_{amount}", owner="a_sender", fee=0, amount=amount, rows=rows,
                 sender="a_sender", recipient="new", error="POST_STATE_RESOURCE_BOUND_EXCEEDED" if amount == 1 else None)
    return replace(case, ceiling=True)


def test_exact_4096_ceiling_allows_replacement_and_rejects_growth(lean: LeanSubject) -> None:
    cases = (_ceiling_case(2), _ceiling_case(1))
    expected = [_runtime_and_oracle(case) for case in cases]
    assert _decode(_probe(lean, "Ceiling", "\n".join(f"#eval observe (step ({_term(case)}))" for case in cases))) == expected


def test_private_row_updater_checks_u128_boundaries_and_zero_deletion(lean: LeanSubject) -> None:
    probes, expected = [], []
    for amount, delta in ((1, -2), (1, -1), (1, 0), ((1 << 128) - 1, 1), ((1 << 128) - 1, -1)):
        case = _case("holding", fee=0, rows=(("alice", "USD", amount),))
        result = _post_balances(case.pre, asset="USD", deltas={"alice": delta})
        if isinstance(result, AssetTransferRejectCodeV1):
            expected.append([[result.value]])
        else:
            expected.append([["ACCEPTED"], *_balances_view(result)])
        probes.append(f'#eval observeUpdate ((checkedUpdate {_amounts_term(case.pre.balances)} "USD" "alice" ({delta})).bind finishBalances)')
    assert _decode(_probe(lean, "HoldingBounds", "\n".join(probes))) == expected


def test_rejected_attempt_then_two_accepted_steps_matches_runtime(lean: LeanSubject) -> None:
    first = _case("first")
    rejected = replace(first, context=replace(first.context, subject_id="mallory"), error="UNAUTHORIZED_SUBJECT")
    out = transition_asset_transfer_v1(first.context, first.pre, first.command)
    assert isinstance(out, AssetTransferAcceptedV1)
    second = replace(first, name="second", pre=out.post_state)
    expected = [_runtime_and_oracle(c) for c in (rejected, first, second)]
    body = f"""
def start : Input := {_term(first)}
def failed : Input := {_term(rejected)}
#eval observe (step failed)
def firstOut := step {{ start with pre := (step failed).post }}
#eval observe firstOut
#eval observe (step {{ start with pre := firstOut.post }})
"""
    assert _decode(_probe(lean, "History", body)) == expected


def test_constructor_premises_and_fee_mirror_nonclaim_are_reachable() -> None:
    case = _case("sender_fee", owner="alice")
    with pytest.raises(ValueError, match="canonically ordered and unique"):
        replace(case.pre, balances=(case.pre.balances[0], *case.pre.balances))
    with pytest.raises(ValueError, match="wrong custody domain"):
        replace(case.pre, balances=(EconomicAmountV1("alice", "USD", "vault", 1),))
    out = transition_asset_transfer_v1(case.context, case.pre, case.command)
    assert isinstance(out, AssetTransferAcceptedV1)
    with pytest.raises(ValueError, match="^economic refinement fee allocation is not mirrored$"):
        _require_fee_mirror_v1(out.effects)


@pytest.mark.parametrize(("name", "old", "new", "case"), (
    ("zero_deletion", "if atoms = 0 then eraseKey key rows", "if False then eraseKey key rows", "zero"),
    ("asset_key", "C.amountKey row != key", "(C.amountKey row).1 != key.1", "zero"),
    ("row_ceiling", "if rows.length > maxBalanceRows then", "if False then", "ceiling"),
))
def test_executed_model_mutants_diverge_from_actual_leaf(
    lean: LeanSubject, name: str, old: str, new: str, case: str,
) -> None:
    source = (lean.source / "Proofs" / f"{MODULE}.lean").read_text()
    assert source.count(old) == 1
    definitions = re.sub(r"^theorem .*?(?=^(?:theorem|def|abbrev|structure|end)\b)", "", source,
                         flags=re.MULTILINE | re.DOTALL)
    definitions = definitions.replace(old, new)
    selected = _ceiling_case(1) if case == "ceiling" else _case("zero", rows=(("alice", "USD", 32), ("alice", "EUR", 7)))
    expected = _runtime_and_oracle(selected)
    actual = _decode(_probe(lean, f"Mutant_{name}", f"#eval observe (step ({_term(selected)}))", definitions))
    assert actual != [expected]
