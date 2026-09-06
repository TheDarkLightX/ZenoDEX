"""Accepted V1 leaf fee mirrors: a scoped theorem and independent runtime oracle.

The invariant is eligibility iff fee == 0 or owner != sender, with movement
sums derived from the leaf. RIPR reaches accepted effects (including sender fee
netting), propagates them to the unchanged global checker, and observes exact
refusal plus unchanged full values. Grade 4: Lean theorem consumers/axioms;
grade 3: signed-event arithmetic; grade 2: fixed alias/width decision table.
Finite comparisons do not establish universal runtime/compiler refinement,
authenticated admission, custody successor selection, receipt validity,
publication, settlement authority or production qualification.
"""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
from dataclasses import asdict, dataclass
from pathlib import Path

import pytest

from src.core.asset_transfer_module_v1 import transition_asset_transfer_v1
from src.core.asset_transfer_types_v1 import (
    AssetTransferAcceptedV1,
    AssetTransferCommandV1,
    AssetTransferContextV1,
    AssetTransferPolicyV1,
    AssetTransferRejectedV1,
    AssetTransferStateV1,
)
from src.core.global_economic_state_effect_refinement_v1 import _require_fee_mirror_v1
from src.core.global_settlement_types_v1 import (
    AssetSupplyV1,
    EconomicAmountV1,
    EconomicEffectKindV1,
    EconomicEffectRowV1,
    FeeConservationRowV1,
    GlobalEconomicEffectPlanV1,
)
from tests.formal.test_lean_checked_epoch_economic_tables_v1 import LeanSubject, _compile

ROOT = Path(__file__).resolve().parents[2]
PROJECT = ROOT / "lean-mathlib"
MODULE = "AssetTransferFeeMirrorEligibilityV1"
NAMESPACE = f"Proofs.{MODULE}"
DEPENDENCIES = (
    "AssetTransferRefinementV1", "AssetTransferCustodyCompletionV1",
    "CheckedSignedDeltaRefinementV1", "AssetTransferCustodyCompositionV1",
)
PINNED_SOURCES = {
    "src/core/asset_transfer_module_v1.py": "754d75a37ad70868bf20263fc189fc9e4f5a77cb864d8a1c7973afc253c938d7",
    "src/core/asset_transfer_types_v1.py": "5757c8b692820613e1eac30b7103e857a73b42efebbdda62d0a4469511f41277",
    "src/core/global_economic_state_effect_refinement_v1.py": "abf60faacdcd45def5163e618494a2202c9c1ab7e11bde1f44b7b29cd0057697",
    "lean-mathlib/Proofs/AssetTransferRefinementV1.lean": "2d9ed7beb6feb47b67afa63a40d1203bcca9004b49ba978b9927edded6a04932",
    "lean-mathlib/Proofs/AssetTransferCustodyCompletionV1.lean": "fc6869b223a427ef22d040e71276d57c1f7b5bca9b95b471d4059ae771a1f8dc",
    "lean-mathlib/Proofs/CheckedSignedDeltaRefinementV1.lean": "3a0b3e18a069b14c8fec4e705178a73cb1b3356d9813195e5e7c35b09cf74a4d",
    "lean-mathlib/Proofs/AssetTransferCustodyCompositionV1.lean": "37375e914576993767eae7484e620e54be300798785b2a57a9953e86be2f34d2",
}
OPENS = f"""
open Proofs.AssetTransferRefinementV1 {NAMESPACE}
open Proofs.AssetTransferCustodyCompositionV1 (movementDeltaSum)
"""
ACCEPTED = "∀ {ctx : Context} {pre : TransferState} {cmd : Command}, "
WELL_FORMED = "StateWellFormed pre → CommandWellFormed cmd → "
VERDICT = "(transition ctx pre cmd).verdict = .accepted → "
CONSUMERS = {
    "accepted_movement_sums_i128": ACCEPTED + VERDICT +
        "∀ p, IsI128 (movementDeltaSum p (transition ctx pre cmd).effects.movements)",
    "accepted_fee_owner_movement_sum": ACCEPTED + VERDICT +
        "movementDeltaSum pre.policy.feeOwner (transition ctx pre cmd).effects.movements = "
        "if pre.policy.feeOwner = cmd.sender then -cmd.amountAtoms else "
        "if pre.policy.feeOwner = cmd.recipient then cmd.amountAtoms + pre.policy.transferFeeAtoms "
        "else pre.policy.transferFeeAtoms",
    "accepted_fee_mirror_eligible_iff": ACCEPTED + WELL_FORMED + VERDICT +
        "(FeeMirrorEligible (transition ctx pre cmd).effects ↔ "
        "pre.policy.transferFeeAtoms = 0 ∨ pre.policy.feeOwner ≠ cmd.sender)",
    "positive_sender_fee_not_eligible": ACCEPTED + WELL_FORMED + VERDICT +
        "0 < pre.policy.transferFeeAtoms → pre.policy.feeOwner = cmd.sender → "
        "¬ FeeMirrorEligible (transition ctx pre cmd).effects",
}
UPPER = (1 << 127) - 1
NOT_MIRRORED = "economic refinement fee allocation is not mirrored"
SIGNED_OVERFLOW = "EFFECT_DELTA_OVERFLOW"


@dataclass(frozen=True)
class Case:
    name: str
    owner: str
    fee_atoms: int
    amount_atoms: int
    expected: str


# The accepted maximum depends on the alias: recipient amount + fee must fit
# i128::MAX; a distinct owner's sender debit may reach i128::MIN; sender fee
# netting admits amount == fee == i128::MAX. Each has an adjacent refusal.
CASES = (
    Case("zero_sender", "alice", 0, 1, "MIRRORED"),
    Case("zero_recipient", "bob", 0, 1, "MIRRORED"),
    Case("zero_distinct", "treasury", 0, 1, "MIRRORED"),
    Case("one_sender", "alice", 1, 1, NOT_MIRRORED),
    Case("one_recipient", "bob", 1, 1, "MIRRORED"),
    Case("one_distinct", "treasury", 1, 1, "MIRRORED"),
    Case("zero_max_amount_sender", "alice", 0, UPPER, "MIRRORED"),
    Case("zero_max_amount_recipient", "bob", 0, UPPER, "MIRRORED"),
    Case("zero_max_amount_distinct", "treasury", 0, UPPER, "MIRRORED"),
    Case("sender_max_pair", "alice", UPPER, UPPER, NOT_MIRRORED),
    Case("distinct_max_fee_min_debit", "treasury", UPPER, 1, "MIRRORED"),
    Case("distinct_max_amount_min_debit", "treasury", 1, UPPER, "MIRRORED"),
    Case("recipient_max_fee", "bob", UPPER - 1, 1, "MIRRORED"),
    Case("recipient_max_amount_positive_fee", "bob", 1, UPPER - 1, "MIRRORED"),
    Case("sender_fee_overflow_neighbor", "alice", UPPER + 1, 1, SIGNED_OVERFLOW),
    Case("sender_amount_overflow_neighbor", "alice", UPPER, UPPER + 1, SIGNED_OVERFLOW),
    Case("distinct_fee_overflow_neighbor", "treasury", UPPER + 1, 1, SIGNED_OVERFLOW),
    Case("distinct_debit_overflow_neighbor", "treasury", UPPER, 2, SIGNED_OVERFLOW),
    Case("recipient_fee_overflow_neighbor", "bob", UPPER, 1, SIGNED_OVERFLOW),
    Case("recipient_amount_overflow_neighbor", "bob", 1, UPPER, SIGNED_OVERFLOW),
    Case("zero_fee_amount_overflow_neighbor", "treasury", 0, UPPER + 1, SIGNED_OVERFLOW),
)

OBSERVERS = f"""
def rowView (rows : List MovementRow) : List (List String) :=
  (rows.mergeSort (fun a b => a.principal ≤ b.principal)).map
    (fun row => [row.principal, toString row.deltaAtoms])
def observe (s : Scenario) : String :=
  let out := s.run
  match out.verdict with
  | .rejected code => reprStr [[code.code], ["NO_FEE_MIRROR_CHECK"]]
  | .accepted =>
    let mirror := if FeeMirrorEligible out.effects then "MIRRORED" else {json.dumps(NOT_MIRRORED)}
    reprStr ([["ACCEPTED"], [mirror],
      [toString (movementDeltaSum s.pre.policy.feeOwner out.effects.movements)], ["MOVEMENTS"]] ++
      rowView out.effects.movements ++ [["ALLOCATIONS"]] ++ rowView out.effects.feeAllocations)
"""


@pytest.fixture(scope="module")
def lean(tmp_path_factory: pytest.TempPathFactory) -> LeanSubject:
    assert (PROJECT / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.27.0"
    # Resolve an installed toolchain directly: this fixture cannot fetch via elan/lake.
    executable = Path.home() / ".elan/toolchains/leanprover--lean4---v4.27.0/bin/lean"
    assert executable.is_file(), f"installed Lean 4.27.0 unavailable: {executable}"
    version = subprocess.run([str(executable), "--version"], capture_output=True,
                             text=True, check=True, timeout=30)
    assert "version 4.27.0," in version.stdout
    directory = tmp_path_factory.mktemp("asset-transfer-fee-mirror")
    source, library = directory / "source", directory / "library"
    (source / "Proofs").mkdir(parents=True)
    (library / "Proofs").mkdir(parents=True)
    subject = LeanSubject(executable, source, library)
    for path, digest in PINNED_SOURCES.items():
        assert hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == digest, path
    for name in (*DEPENDENCIES, MODULE):
        captured = source / "Proofs" / f"{name}.lean"
        captured.write_bytes((PROJECT / "Proofs" / f"{name}.lean").read_bytes())
        imports = re.findall(r"^import (\S+)", captured.read_text(), re.MULTILINE)
        assert all(i.startswith("Std.") or i.removeprefix("Proofs.") in DEPENDENCIES
                   for i in imports), imports
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


def test_theorem_consumers_axioms_and_source_pins(lean: LeanSubject) -> None:
    source = (lean.source / "Proofs" / f"{MODULE}.lean").read_text()
    code = re.sub(r"/-.*?-/", "", source, flags=re.DOTALL)
    assert re.search(r"\b(sorry|admit|axiom|unsafe|native_decide)\b", code) is None
    assert re.findall(r"^theorem (\w+)", code, re.MULTILINE) == list(CONSUMERS)
    body = "\n".join(f"example : {signature} := @{NAMESPACE}.{name}\n"
                     f"#print axioms {NAMESPACE}.{name}" for name, signature in CONSUMERS.items())
    report = " ".join(_probe(lean, "TheoremConsumers", body).split())
    for name in CONSUMERS:
        found = re.search(re.escape(f"'{NAMESPACE}.{name}' ") +
                          r"(?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", report)
        assert found, (name, report)
        axioms = {a.strip() for a in (found.group(1) or "").split(",") if a.strip()}
        assert axioms <= {"propext", "Quot.sound", "Classical.choice"}, (name, axioms)


def _inputs(case: Case) -> tuple[AssetTransferContextV1, AssetTransferStateV1, AssetTransferCommandV1]:
    root = "0x" + "01" * 32
    balance_atoms = case.amount_atoms + (0 if case.owner == "alice" else case.fee_atoms)
    pre = AssetTransferStateV1(
        root, (AssetTransferPolicyV1("USD", case.owner, case.fee_atoms, True),),
        (EconomicAmountV1("alice", "USD", "accounts", balance_atoms),),
        (AssetSupplyV1("USD", balance_atoms),),
    )
    context = AssetTransferContextV1("test", root, root, 1, root, root, "alice", root)
    command = AssetTransferCommandV1("asset_transfer", "USD", "alice", "bob",
                                     case.amount_atoms, case.fee_atoms)
    return context, pre, command


def _require_event_oracle(case: Case, pre: AssetTransferStateV1, out: AssetTransferAcceptedV1) -> int:
    # Independent event-list sums do not use the leaf's delta dictionary or row builder.
    events = (("alice", -case.amount_atoms - case.fee_atoms),
              ("bob", case.amount_atoms), (case.owner, case.fee_atoms))
    totals = [(p, sum(d for q, d in events if p == q)) for p in sorted({p for p, _ in events})]
    rows = [EconomicEffectRowV1(EconomicEffectKindV1.ACCOUNT_MOVEMENT, p, "USD", "accounts", d)
            for p, d in totals if d]
    if case.fee_atoms:
        rows.append(EconomicEffectRowV1(EconomicEffectKindV1.FEE_ALLOCATION, case.owner,
                                       "USD", "accounts", case.fee_atoms))
    assert out.effects.rows == tuple(sorted(rows, key=lambda r: r.key))
    fees = (FeeConservationRowV1("USD", case.fee_atoms, case.fee_atoms, 0),) if case.fee_atoms else ()
    assert out.effects.fee_conservation == fees
    balances = tuple(EconomicAmountV1(p, "USD", "accounts", pre.balance_atoms(p, "USD") + d)
                     for p, d in totals if pre.balance_atoms(p, "USD") + d)
    assert out.post_state.balances == balances
    assert out.post_state.policies == pre.policies and out.post_state.supplies == pre.supplies
    assert out.effects.external_outbox_enqueue == ()
    actual_sum = sum(row.delta_atoms for row in out.effects.rows
                     if row.kind is EconomicEffectKindV1.ACCOUNT_MOVEMENT and
                     (row.principal, row.asset, row.custody_domain) == (case.owner, "USD", "accounts"))
    assert actual_sum == sum(d for p, d in events if p == case.owner)
    return actual_sum


def _runtime_observation(case: Case) -> list[list[str]]:
    context, pre, command = _inputs(case)
    before = (asdict(context), asdict(pre), asdict(command), pre.state_root)
    out = transition_asset_transfer_v1(context, pre, command)
    assert before == (asdict(context), asdict(pre), asdict(command), pre.state_root)
    if case.expected == SIGNED_OVERFLOW:
        assert isinstance(out, AssetTransferRejectedV1), case.name
        assert out.code.value == SIGNED_OVERFLOW
        assert out.pre_state_root == out.post_state_root == pre.state_root
        assert out.effects == GlobalEconomicEffectPlanV1.empty()
        return [[SIGNED_OVERFLOW], ["NO_FEE_MIRROR_CHECK"]]
    assert isinstance(out, AssetTransferAcceptedV1), case.name
    owner_sum = _require_event_oracle(case, pre, out)
    complete_value = (asdict(out), out.effects.effect_plan_root, out.post_state.state_root)
    if case.expected == NOT_MIRRORED:
        with pytest.raises(ValueError) as exc:
            _require_fee_mirror_v1(out.effects)
        assert str(exc.value) == NOT_MIRRORED
    else:
        _require_fee_mirror_v1(out.effects)
    # The existing checker is read-only even for the retained positive sender fee refusal.
    assert complete_value == (asdict(out), out.effects.effect_plan_root, out.post_state.state_root)
    assert before == (asdict(context), asdict(pre), asdict(command), pre.state_root)
    movements = [[r.principal, str(r.delta_atoms)] for r in out.effects.rows
                 if r.kind is EconomicEffectKindV1.ACCOUNT_MOVEMENT]
    allocations = [[r.principal, str(r.delta_atoms)] for r in out.effects.rows
                   if r.kind is EconomicEffectKindV1.FEE_ALLOCATION]
    return [["ACCEPTED"], [case.expected], [str(owner_sum)], ["MOVEMENTS"],
            *movements, ["ALLOCATIONS"], *allocations]


def _term(case: Case) -> str:
    _, pre, _ = _inputs(case)
    balance_atoms = pre.balances[0].amount_atoms
    # The abstract root token is matched inside the model; this is no root/encoding proof.
    return (f"scenario {json.dumps(case.owner)} ({case.fee_atoms}) true "
            f"[(alice, ({balance_atoms}))] ({balance_atoms}) releaseA alice "
            f"assetTransferCommandKind usd alice bob ({case.amount_atoms}) ({case.fee_atoms})")


def _well_formed_witness(name: str) -> str:
    return f"""
example : StateWellFormed {name}.pre := by
  constructor
  · intro p
    simp only [{name}, scenario, ledger]
    split <;> decide
  · constructor <;> decide
  · constructor <;> decide
example : CommandWellFormed {name}.cmd := by
  constructor <;> constructor <;> decide
"""


def test_given_accepted_leaf_when_rows_checked_then_mirror_matches_alias_and_width_table(lean: LeanSubject) -> None:
    body = OBSERVERS
    observed = []
    for index, case in enumerate(CASES):
        name = f"case{index}"
        body += f"\ndef {name} : Scenario := {_term(case)}\n" + _well_formed_witness(name)
        if case.expected != SIGNED_OVERFLOW:
            # Non-vacuity: every accepted comparison inhabits all theorem premises.
            body += f"example : {name}.run.verdict = .accepted := by decide\n"
        body += f"#eval observe {name}\n"
        observed.append(_runtime_observation(case))
    output = _probe(lean, "ActualLeafComparisons", body)
    decoded = [json.loads(json.loads(line)) for line in output.splitlines()]
    assert decoded == observed


def test_given_positive_sender_fee_when_checked_then_unconditional_acceptance_is_refuted(lean: LeanSubject) -> None:
    case = Case("sender_positive_fee_counterexample", "alice", 1, 1, NOT_MIRRORED)
    assert _runtime_observation(case)[1] == [NOT_MIRRORED]
    condition = "def predictedEligible (effects : AbstractEffects) : Bool := decide (FeeMirrorEligible effects)"
    body = f"""
def counterexample : Scenario := {_term(case)}
{_well_formed_witness('counterexample')}
example : counterexample.run.verdict = .accepted := by decide
{condition}
example : predictedEligible counterexample.run.effects = false := by decide
"""
    assert _probe(lean, "SenderCounterexample", body) == ""
    # A temporary model-only mutant must fail the very same negative consumer.
    # No runtime source, checker, theorem, or authority-bearing peer API is replaced.
    mutant = body.replace(condition, "def predictedEligible (_effects : AbstractEffects) : Bool := true")
    assert mutant != body
    path = lean.source / "UnconditionalAcceptanceMutant.lean"
    path.write_text(f"import {NAMESPACE}\n{OPENS}\n{mutant}")
    result = _compile(lean, path)
    assert result.returncode != 0
    assert result.stdout.count("error:") == 1, result.stdout + result.stderr
    assert ("Tactic `decide` proved that the proposition\n"
            "  predictedEligible counterexample.run.effects = false\nis false") in result.stdout
