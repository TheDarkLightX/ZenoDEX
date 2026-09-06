"""Thin independent consumers for sparse state-quantity admission.

The Lean witness exercises the new state-admission preservation chain on a
nonempty model state. It includes account, custody, liability, reserve,
terminal, oracle, and replay entries, then runs a rejected request followed by
two accepted requests and checks a changed final account balance. The witness
is Lean-model-only: terminal liability domains and the global claimant
aggregation do not claim an exact Python state projection here.
It uses a static selected policy and pure row-update semantics; full policy
membership, authentication, canonical hashing, height, replay, publication,
and Python/Rust/compiler refinement remain outside this harness.

The contract lane spells every public theorem signature, checks transitive
axioms, rejects placeholders, and pins selected unchanged source subjects.
"""

from __future__ import annotations

import hashlib
import json
import re

import pytest

from tests.formal.test_lean_asset_transfer_sparse_supply_v1 import (
    lean as supply_subject,  # noqa: F401
)
from tests.formal.test_lean_checked_epoch_economic_tables_v1 import (
    PROJECT,
    LeanSubject,
    _compile,
)

MODULE = "AssetTransferSparseStateAdmissionV1"
NAMESPACE = f"Proofs.{MODULE}"
OPENS = f"""
open Proofs.GlobalSettlementCoreV2 Proofs.GlobalEconomicStateRefinementV2
open Proofs.AssetTransferRefinementV1 {NAMESPACE}
"""

# Independent consumers deliberately preserve the declaration surface instead
# of rebuilding signatures from the proof source.
THEOREM_TYPES = {
    "owner_first_to_state_key_injective":
        "Function.Injective ownerFirstToStateKey",
    "canonical_balances_state_keys_nodup":
        "∀ {rows : List G.AmountRow}, S.CanonicalBalances rows → (rows.map stateAmountKey).Nodup",
    "selected_is_u128_fits_u128":
        "∀ {amount : Int}, T.IsU128 amount → FitsU128 amount",
    "canonical_balances_sparse_amount_rows_admitted":
        "∀ {rows : List G.AmountRow}, S.CanonicalBalances rows → G.SparseAmountRowsAdmitted rows",
    "step_preserves_state_quantities_admitted":
        "∀ {input : S.Input}, S.CanonicalBalances input.pre.balances → G.StateQuantitiesAdmitted input.pre → G.StateQuantitiesAdmitted (S.step input).post",
    "step_preserves_claimant_liabilities_backed":
        "∀ {input : S.Input}, G.ClaimantLiabilitiesBacked input.pre → G.ClaimantLiabilitiesBacked (S.step input).post",
    "step_preserves_owned_supply_and_claimant_liabilities_backed":
        "∀ {input : S.Input}, S.CanonicalBalances input.pre.balances → G.OwnedMatchesSupply input.pre → G.ClaimantLiabilitiesBacked input.pre → G.OwnedMatchesSupply (S.step input).post ∧ G.ClaimantLiabilitiesBacked (S.step input).post",
    "run_preserves_state_quantities_admitted":
        "∀ (config : H.Config) (requests : List H.Request) (pre : G.GlobalState), S.CanonicalBalances pre.balances → G.StateQuantitiesAdmitted pre → G.StateQuantitiesAdmitted (H.run config requests pre).post",
    "run_preserves_owned_supply_and_claimant_liabilities_backed":
        "∀ (config : H.Config) (requests : List H.Request) (pre : G.GlobalState), S.CanonicalBalances pre.balances → G.OwnedMatchesSupply pre → G.ClaimantLiabilitiesBacked pre → G.OwnedMatchesSupply (H.run config requests pre).post ∧ G.ClaimantLiabilitiesBacked (H.run config requests pre).post",
}

SUBJECTS = {
    "lean-mathlib/Proofs/GlobalEconomicStateRefinementV2.lean":
        "c1be0fe70c2db99cb0fe0be584ef935e26079a66787e35aedb98057b5ceee1b1",
    "lean-mathlib/Proofs/AssetTransferSparseTablesV1.lean":
        "5d303c709501cfe0604c3e845a3b2814b8c5ebe4f0fcfd4090bda2d697f077c0",
    "lean-mathlib/Proofs/AssetTransferSparseTraceV1.lean":
        "5a77ac04b4e214ab7d0dc6cb4b77e2369e16a7914d02cffb5df1d0b88f119b83",
    "lean-mathlib/Proofs/AssetTransferSparseSupplyV1.lean":
        "e2c056cba91173f6c454f4b60c1adc228d9ffd7df58a9cebcdbbc0e9b46a683d",
    "src/core/asset_transfer_module_v1.py":
        "754d75a37ad70868bf20263fc189fc9e4f5a77cb864d8a1c7973afc253c938d7",
    "src/core/asset_transfer_types_v1.py":
        "5757c8b692820613e1eac30b7103e857a73b42efebbdda62d0a4469511f41277",
    "src/core/global_economic_state_effect_refinement_v1.py":
        "abf60faacdcd45def5163e618494a2202c9c1ab7e11bde1f44b7b29cd0057697",
}


@pytest.fixture(scope="module")
def lean(supply_subject: LeanSubject) -> LeanSubject:  # noqa: F811
    """Capture the fresh proof into the already-built sparse-supply closure."""
    captured = supply_subject.source / "Proofs" / f"{MODULE}.lean"
    captured.write_bytes((PROJECT / "Proofs" / f"{MODULE}.lean").read_bytes())
    result = _compile(
        supply_subject,
        captured,
        supply_subject.library / "Proofs" / f"{MODULE}.olean",
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout == result.stderr == ""
    return supply_subject


def _probe(lean: LeanSubject, name: str, body: str) -> str:
    path = lean.source / f"{name}.lean"
    path.write_text(f"import {NAMESPACE}\n" + OPENS + body)
    result = _compile(lean, path)
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stderr == ""
    return result.stdout


def test_independent_contracts_axioms_and_selected_sources(lean: LeanSubject) -> None:
    source = (lean.source / "Proofs" / f"{MODULE}.lean").read_text()
    code = re.sub(r"/-.*?-/", "", source, flags=re.DOTALL)
    assert re.search(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b", code) is None
    assert tuple(re.findall(r"^theorem (\w+)", code, flags=re.MULTILINE)) == tuple(THEOREM_TYPES)

    consumers = "\n".join(
        f"example : {signature} := @{NAMESPACE}.{name}\n"
        f"#print axioms {NAMESPACE}.{name}"
        for name, signature in THEOREM_TYPES.items()
    )
    report = " ".join(_probe(lean, "IndependentConsumers", consumers).split())
    for name in THEOREM_TYPES:
        found = re.search(
            re.escape(f"'{NAMESPACE}.{name}' ")
            + r"(?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",
            report,
        )
        assert found, (name, report)
        axioms = {
            entry.strip()
            for entry in (found.group(1) or "").split(",")
            if entry.strip()
        }
        assert axioms <= {"propext", "Quot.sound", "Classical.choice"}, (name, axioms)

    assert f"import {NAMESPACE}" in (PROJECT / "Proofs.lean").read_text().splitlines()
    for path, digest in SUBJECTS.items():
        assert hashlib.sha256((PROJECT.parent / path).read_bytes()).hexdigest() == digest


WITNESS = r'''
namespace StateAdmissionWitness

namespace T
export Proofs.AssetTransferRefinementV1 (Command)
end T

def oracleOccurrence : OracleOccurrence :=
  { oracleId := "oracle:usd"
    occurrenceRoot := "oracle-root:1"
    observedHeight := 7
    finality := .finalized }

def oracleRegistry (oracleId : Identifier) : Option OracleOccurrence :=
  if oracleId = "oracle:usd" then some oracleOccurrence else none

def replayRegistry (replayId : Identifier) : Option RootId :=
  if replayId = "replay:transfer:1" then some "occurrence:transfer:1" else none

def terminal : TerminalObligation :=
  { obligationId := "obligation:transfer:1"
    laneId := .assetTransfer
    claimant := "claimant"
    asset := "USD"
    liabilityDomain := "vault"
    amountAtoms := 5
    status := .open }

def initial : GlobalState :=
  { staticGlobalState with
    stateRoot := "state-root:admission"
    writerEpoch := 1
    height := 10
    balances := [
      ⟨"alice", "USD", "accounts", 10⟩,
      ⟨"bob", "USD", "accounts", 5⟩]
    supplies := [⟨"USD", 38⟩]
    custody := [⟨"custodian", "USD", "vault", 20⟩]
    liabilities := [⟨"claimant", "USD", "vault", 7⟩]
    reserves := [⟨"reserve", "USD", "reserve", 3⟩]
    oracleOccurrences := oracleRegistry
    replayState := replayRegistry
    terminalObligations := [terminal] }

def config : H.Config :=
  ⟨"admission-release", ⟨"USD", "treasury", 1, true⟩⟩

def command : Proofs.AssetTransferRefinementV1.Command :=
  ⟨"asset_transfer", "USD", "alice", "bob", 3, 1⟩

def acceptedRequest : H.Request :=
  ⟨⟨"admission-release", "alice"⟩, command⟩

def rejectedRequest : H.Request :=
  ⟨⟨"admission-release", "mallory"⟩, command⟩

def requests : List H.Request :=
  [rejectedRequest, acceptedRequest, acceptedRequest]

def acceptedInput : S.Input := H.inputFor config acceptedRequest initial
def rejectedInput : S.Input := H.inputFor config rejectedRequest initial
def history := H.run config requests initial

theorem initial_canonical : S.CanonicalBalances initial.balances := by
  refine ⟨?_, ?_, by decide, by decide⟩
  · unfold S.Unique
    decide
  · intro row member
    simp [initial] at member
    rcases member with rfl | rfl <;> decide

theorem initial_owned_supply : G.OwnedMatchesSupply initial := by
  intro asset
  by_cases h : "USD" = asset <;>
    simp [ownedFor, amountForAsset, supplyFor, initial, h]

theorem initial_claimant_backing : G.ClaimantLiabilitiesBacked initial := by
  constructor
  · intro asset domain
    by_cases h : "USD" = asset ∧ "vault" = domain <;>
      simp [amountForAssetDomain, initial, h]
  · intro owner asset domain
    by_cases h : "claimant" = owner ∧ "USD" = asset ∧ "vault" = domain <;>
      simp [openTerminalAmountFor, amountAt, initial, terminal, h]

theorem initial_replay_injective : ReplayOccurrenceIdsInjective initial := by
  intro left right occurrence leftFound rightFound
  by_cases leftKey : left = "replay:transfer:1" <;>
    by_cases rightKey : right = "replay:transfer:1" <;>
      simp [initial, replayRegistry, leftKey, rightKey] at leftFound rightFound ⊢

theorem initial_oracle_admitted : OracleRegistryAdmitted initial := by
  constructor
  · intro oracleId occurrence found
    by_cases key : oracleId = "oracle:usd"
    · subst oracleId
      simp [initial, oracleRegistry] at found
      cases found
      simp [initial, oracleOccurrence, OracleOccurrenceWithinHeight, FitsU64, maxU64]
    · simp [initial, oracleRegistry, key] at found
  · intro oracleId occurrence found
    by_cases key : oracleId = "oracle:usd"
    · subst oracleId
      simp [initial, oracleRegistry] at found
      cases found
      rfl
    · simp [initial, oracleRegistry, key] at found

theorem initial_state_admitted : G.StateQuantitiesAdmitted initial := by
  unfold StateQuantitiesAdmitted
  refine ⟨by simp [initial, FitsU64, maxU64], by simp [initial, FitsU64, maxU64],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    initial_replay_injective, initial_oracle_admitted⟩
  · simp [SparseAmountRowsAdmitted, initial, FitsU128, maxU128]
  · simp [SparseSupplyRowsAdmitted, initial, FitsU128, maxU128]
  · simp [SparseAmountRowsAdmitted, initial, FitsU128, maxU128]
  · simp [SparseAmountRowsAdmitted, initial, FitsU128, maxU128]
  · simp [SparseAmountRowsAdmitted, initial, FitsU128, maxU128]
  · decide
  · decide
  · decide
  · decide
  · decide
  · intro asset
    by_cases h : "USD" = asset <;>
      simp [initial, ownedFor, liabilityFor, amountForAsset, supplyFor, h,
        FitsU128, maxU128] <;> omega
  · simp [initial]
  · simp [initial, terminal, TerminalObligationAdmitted, FitsU128, maxU128]

example : G.OwnedMatchesSupply (S.step acceptedInput).post :=
  step_preserves_owned_supply_and_claimant_liabilities_backed
    initial_canonical initial_owned_supply initial_claimant_backing |>.1

example : G.ClaimantLiabilitiesBacked (S.step rejectedInput).post :=
  step_preserves_claimant_liabilities_backed initial_claimant_backing

example : G.StateQuantitiesAdmitted (S.step acceptedInput).post :=
  step_preserves_state_quantities_admitted initial_canonical initial_state_admitted

example : G.StateQuantitiesAdmitted (S.step rejectedInput).post :=
  step_preserves_state_quantities_admitted initial_canonical initial_state_admitted

example : G.OwnedMatchesSupply history.post ∧
    G.ClaimantLiabilitiesBacked history.post :=
  run_preserves_owned_supply_and_claimant_liabilities_backed config requests initial
    initial_canonical initial_owned_supply initial_claimant_backing

example : G.StateQuantitiesAdmitted history.post :=
  run_preserves_state_quantities_admitted config requests initial
    initial_canonical initial_state_admitted

example : (S.step rejectedInput).verdict = .rejected .unauthorizedSubject := by
  decide

example : (S.step acceptedInput).verdict = .accepted := by
  decide

#eval IO.println (reprStr [
  ["INITIAL_ALICE", toString (amountAt initial.balances "alice" "USD" "accounts")],
  ["FINAL_ALICE", toString (amountAt history.post.balances "alice" "USD" "accounts")],
  ["FINAL_BOB", toString (amountAt history.post.balances "bob" "USD" "accounts")],
  ["ACCEPTED_PLANS", toString history.acceptedPlans.length],
  ["TERMINALS", toString initial.terminalObligations.length],
  ["ORACLE", toString (match initial.oracleOccurrences "oracle:usd" with
    | some occurrence => occurrence.oracleId
    | none => "NONE")],
  ["REPLAY", toString (match initial.replayState "replay:transfer:1" with
    | some occurrenceId => occurrenceId
    | none => "NONE")]])

end StateAdmissionWitness
'''


def test_nonempty_witness_consumes_step_and_history_preservation(lean: LeanSubject) -> None:
    expected = [
        ["INITIAL_ALICE", "10"],
        ["FINAL_ALICE", "2"],
        ["FINAL_BOB", "11"],
        ["ACCEPTED_PLANS", "2"],
        ["TERMINALS", "1"],
        ["ORACLE", "oracle:usd"],
        ["REPLAY", "occurrence:transfer:1"],
    ]
    actual = json.loads(_probe(lean, "NonemptyWitness", WITNESS).strip())
    assert actual == expected


def test_initial_admission_and_key_coordinate_controls(lean: LeanSubject) -> None:
    body = r'''
namespace StateAdmissionCounterexample

namespace S
export Proofs.AssetTransferSparseTablesV1 (demo demo_source
  demo_deletes_zero_and_frames_other_asset)
end S

def overflowEpochDemo : S.Input :=
  { S.demo with pre := { S.demo.pre with writerEpoch := 2 ^ 64 } }

example : S.CanonicalBalances overflowEpochDemo.pre.balances := by
  change S.CanonicalBalances S.demo.pre.balances
  exact ⟨S.demo_source.1, S.demo_source.2, by decide, by decide⟩

example : (S.step overflowEpochDemo).verdict = .accepted := by
  change (S.step S.demo).verdict = .accepted
  exact S.demo_deletes_zero_and_frames_other_asset.1

example : ¬ StateQuantitiesAdmitted overflowEpochDemo.pre := by
  intro admitted
  have overflow : (2 ^ 64 : Nat) ≤ 2 ^ 64 - 1 := by
    simpa only [FitsU64, overflowEpochDemo, Proofs.AssetTransferSparseTablesV1.demo,
      maxU64] using admitted.1
  omega

example : ¬ StateQuantitiesAdmitted (S.step overflowEpochDemo).post := by
  intro admitted
  have epochBound := admitted.1
  rw [Proofs.AssetTransferSparseTablesV1.step_frame overflowEpochDemo] at epochBound
  change (2 ^ 64 : Nat) ≤ 2 ^ 64 - 1 at epochBound
  omega

def sameAssetDifferentOwners : List AmountRow :=
  [⟨"alice", "USD", "accounts", 1⟩, ⟨"bob", "USD", "accounts", 2⟩]

example :
    sameAssetDifferentOwners.map
        Proofs.AssetTransferSparseStateAdmissionV1.stateAmountKey =
      [("USD", "alice", "accounts"), ("USD", "bob", "accounts")] ∧
    (sameAssetDifferentOwners.map
      Proofs.AssetTransferSparseStateAdmissionV1.stateAmountKey).Nodup := by
  decide

end StateAdmissionCounterexample
'''
    _probe(lean, "AdmissionControls", body)


def test_state_key_owner_erasure_mutant_rejected_by_unchanged_proof(
    lean: LeanSubject,
) -> None:
    captured_path = lean.source / "Proofs" / f"{MODULE}.lean"
    original_path = PROJECT / "Proofs" / f"{MODULE}.lean"
    original_bytes = original_path.read_bytes()
    assert captured_path.read_bytes() == original_bytes
    source = captured_path.read_text()
    needle = "(row.asset, row.owner, row.custodyDomain)"
    replacement = '(row.asset, "", row.custodyDomain)'
    assert source.count(needle) == 1
    mutated = source.replace(needle, replacement, 1)

    first_theorem = "theorem owner_first_to_state_key_injective"
    prefix = mutated[:mutated.index(first_theorem)]
    prefix += '''
#eval IO.println (reprStr [
  decide (Proofs.AssetTransferSparseStateAdmissionV1.stateAmountKey
    ⟨"alice", "USD", "accounts", 1⟩ = ("USD", "", "accounts")),
  decide (Proofs.AssetTransferSparseStateAdmissionV1.stateAmountKey
    ⟨"bob", "USD", "accounts", 2⟩ = ("USD", "", "accounts"))])

end AssetTransferSparseStateAdmissionV1
end Proofs
'''
    prefix_path = lean.source / "MutantOwnerErasurePrefix.lean"
    prefix_path.write_text(prefix)
    prefix_result = _compile(lean, prefix_path)
    assert prefix_result.returncode == 0, prefix_result.stdout + prefix_result.stderr
    assert json.loads(prefix_result.stdout.strip()) == [True, True]

    full_path = lean.source / "MutantOwnerErasure.lean"
    full_path.write_text(mutated)
    full_result = _compile(lean, full_path)
    output = full_result.stdout + full_result.stderr
    assert full_result.returncode != 0
    assert "unexpected token" not in output
    assert "unknown identifier" not in output.lower()
    error_lines = {
        int(line)
        for line in re.findall(rf"{re.escape(str(full_path))}:(\d+):\d+: error:", output)
    }
    lines = mutated.splitlines()
    failed_theorem = "theorem canonical_balances_state_keys_nodup"
    first = next(i + 1 for i, line in enumerate(lines) if line.startswith(failed_theorem))
    following = next(
        (i + 1 for i, line in enumerate(lines[first:], first)
         if re.match(r"^(?:theorem|def|abbrev|structure|end) ", line)),
        len(lines) + 1,
    )
    assert any(first <= line < following for line in error_lines), output
    assert captured_path.read_bytes() == original_bytes
    assert original_path.read_bytes() == original_bytes
