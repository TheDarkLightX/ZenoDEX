"""Independent multi-asset policy-selection consumers.

The Lean model owns the first-match policy table, per-request lookup, sparse
transfer lift, and quantitative state-admission premises.  The Python lane
replays the public ``transition_asset_transfer_v1`` entry point on fixed
two-asset vectors and compares only the modeled verdict, policies, balances,
supplies, and effect rows.  Runtime journals, receipt roots, canonical root
construction, governed-profile membership, authentication, and full
Python/Rust refinement remain outside this harness.
"""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import asdict, dataclass, replace

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
from src.core.global_settlement_types_v1 import (
    AssetSupplyV1,
    EconomicAmountV1,
    EconomicEffectKindV1,
    EconomicEffectRowV1,
    canonical_global_bytes_v1,
)
from tests.formal.test_lean_asset_transfer_sparse_state_admission_v1 import (
    lean as state_admission_subject,  # noqa: F401 -- fresh dependency fixture.
)
from tests.formal.test_lean_asset_transfer_sparse_supply_v1 import (
    lean as supply_subject,  # noqa: F401 -- dependency of state_admission_subject.
)
from tests.formal.test_lean_asset_transfer_sparse_tables_v1 import (
    _amounts_term,
    _balances_view,
)
from tests.formal.test_lean_checked_epoch_economic_tables_v1 import (
    PROJECT,
    LeanSubject,
    _compile,
)

MODULE = "AssetTransferPolicySelectionV1"
NAMESPACE = f"Proofs.{MODULE}"
ROOT = "0x" + "01" * 32
OTHER_ROOT = "0x" + "02" * 32

OPENS = f"""
open Proofs.GlobalSettlementCoreV2 Proofs.GlobalEconomicStateRefinementV2
open Proofs.CheckedEconomicAggregationV1 Proofs.CheckedEpochEconomicTablesV1
open {NAMESPACE}
"""

# These are written independently of the proof source.  Names and signatures
# are the consumer contract; theorem enumeration below detects additions or
# deletions instead of silently accepting a weaker declaration surface.
THEOREM_TYPES = {
    "policyFor_some":
        "∀ {policies : List T.Policy} {asset : String} {policy : T.Policy}, policyFor policies asset = some policy → policy ∈ policies ∧ policy.asset = asset",
    "policyFor_none_iff":
        "∀ (policies : List T.Policy) (asset : String), policyFor policies asset = none ↔ ∀ policy ∈ policies, policy.asset ≠ asset",
    "policyFor_none_of_no_selection":
        "∀ {policies : List T.Policy} {asset : String}, (¬ ∃ policy, policyFor policies asset = some policy) → policyFor policies asset = none",
    "policy_asset_unique":
        "∀ {policies : List T.Policy} {left right : T.Policy}, (policies.map policyKey).Nodup → left ∈ policies → right ∈ policies → left.asset = right.asset → left = right",
    "policyFor_unique":
        "∀ {policies : List T.Policy} {asset : String} {selected candidate : T.Policy}, PoliciesAdmitted policies → policyFor policies asset = some selected → candidate ∈ policies → candidate.asset = asset → selected = candidate",
    "supplyFor_zero_of_absent":
        "∀ (supplies : List G.SupplyRow) (asset : String), (∀ supply ∈ supplies, supply.asset ≠ asset) → G.supplyFor supplies asset = 0",
    "amountForAsset_nonnegative":
        "∀ (rows : List G.AmountRow), (∀ row ∈ rows, T.IsU128 row.amountAtoms) → ∀ asset, 0 ≤ G.amountForAsset rows asset",
    "amountForAsset_positive_of_member":
        "∀ {rows : List G.AmountRow} {row : G.AmountRow}, (∀ candidate ∈ rows, T.IsU128 candidate.amountAtoms ∧ candidate.amountAtoms ≠ 0) → row ∈ rows → 0 < G.amountForAsset rows row.asset",
    "admitted_balance_asset_has_policy":
        "∀ {state : State} (admitted : StateAdmitted state) {row : G.AmountRow} (member : row ∈ state.economic.balances), ∃ policy ∈ state.policies, policy.asset = row.asset",
    "amountForAsset_zero_of_absent":
        "∀ (rows : List G.AmountRow) (asset : String), (∀ row ∈ rows, row.asset ≠ asset) → G.amountForAsset rows asset = 0",
    "supplyFor_nonnegative":
        "∀ (supplies : List G.SupplyRow), (∀ supply ∈ supplies, T.IsU128 supply.amountAtoms) → ∀ asset, 0 ≤ G.supplyFor supplies asset",
    "supplyFor_eq_member_amount":
        "∀ {supplies : List G.SupplyRow} {supply : G.SupplyRow}, (supplies.map supplyKey).Nodup → supply ∈ supplies → G.supplyFor supplies supply.asset = supply.amountAtoms",
    "all_asset_coverage_iff_runtime_clauses":
        "∀ {balances : List G.AmountRow} {supplies : List G.SupplyRow}, S.PositiveAccounts balances → (supplies.map supplyKey).Nodup → (∀ supply ∈ supplies, T.IsU128 supply.amountAtoms) → ((∀ asset, G.amountForAsset balances asset ≤ G.supplyFor supplies asset) ↔ ((∀ row ∈ balances, row.asset ∈ supplies.map supplyKey) ∧ ∀ supply ∈ supplies, G.amountForAsset balances supply.asset ≤ supply.amountAtoms))",
    "lookupLast_is_u128":
        "∀ (key : C.AmountKey) (rows : List G.AmountRow), (∀ row ∈ rows, T.IsU128 row.amountAtoms) → T.IsU128 (C.lookupLast key rows)",
    "selectedInput_state_well_formed":
        "∀ {input : Input} {policy : T.Policy}, StateAdmitted input.pre → policyFor input.pre.policies input.command.asset = some policy → T.StateWellFormed (S.localState (selectedInput input policy))",
    "step_release_mismatch":
        "∀ {input : Input}, input.context.moduleReleaseId ≠ input.pre.moduleReleaseId → step input = reject input .releaseMismatch",
    "step_unknown_command":
        "∀ {input : Input}, input.context.moduleReleaseId = input.pre.moduleReleaseId → input.command.commandKind ≠ T.assetTransferCommandKind → step input = reject input .unknownCommand",
    "step_unknown_asset":
        "∀ {input : Input}, input.context.moduleReleaseId = input.pre.moduleReleaseId → input.command.commandKind = T.assetTransferCommandKind → policyFor input.pre.policies input.command.asset = none → step input = reject input .unknownAsset",
    "step_selected":
        "∀ {input : Input} {policy : T.Policy}, input.context.moduleReleaseId = input.pre.moduleReleaseId → input.command.commandKind = T.assetTransferCommandKind → policyFor input.pre.policies input.command.asset = some policy → step input = lift input (S.step (selectedInput input policy))",
    "accepted_selected_step":
        "∀ {input : Input}, (step input).verdict = .accepted → ∃ policy, policyFor input.pre.policies input.command.asset = some policy ∧ (S.step (selectedInput input policy)).verdict = .accepted ∧ step input = lift input (S.step (selectedInput input policy)) ∧ policy ∈ input.pre.policies ∧ policy.asset = input.command.asset",
    "rejected_step_noop":
        "∀ {input : Input} {code : T.RejectCode}, (step input).verdict = .rejected code → (step input).post = input.pre ∧ (step input).plan = EffectPlan.empty",
    "lift_selected_step_preserves_state_admitted":
        "∀ {input : Input} {policy : T.Policy}, StateAdmitted input.pre → StateAdmitted (lift input (S.step (selectedInput input policy))).post",
    "step_preserves_state_admitted":
        "∀ {input : Input}, StateAdmitted input.pre → StateAdmitted (step input).post",
    "accepted_decrease_authorized":
        "∀ {input : Input}, StateAdmitted input.pre → T.CommandWellFormed input.command → (step input).verdict = .accepted → ∀ {owner asset domain : String}, amountAt (step input).post.economic.balances owner asset domain < amountAt input.pre.economic.balances owner asset domain → owner = input.command.sender ∧ input.command.sender = input.context.subjectId ∧ input.command.asset = asset ∧ S.accounts = domain",
    "run_preserves_state_admitted":
        "∀ (requests : List Request) (pre : State), StateAdmitted pre → StateAdmitted (run requests pre).post",
    "run_table_chain":
        "∀ (requests : List Request) (pre : State), StateAdmitted pre → TableChain pre.economic (run requests pre).acceptedPlans (run requests pre).post.economic ∧ S.CanonicalBalances (run requests pre).post.economic.balances",
    "step_preserves_state_quantities_admitted":
        "∀ {input : Input}, StateAdmitted input.pre → G.StateQuantitiesAdmitted input.pre.economic → G.StateQuantitiesAdmitted (step input).post.economic",
    "step_preserves_owned_supply_and_claimant_liabilities_backed":
        "∀ {input : Input}, StateAdmitted input.pre → G.OwnedMatchesSupply input.pre.economic → G.ClaimantLiabilitiesBacked input.pre.economic → G.OwnedMatchesSupply (step input).post.economic ∧ G.ClaimantLiabilitiesBacked (step input).post.economic",
    "run_preserves_state_quantities_admitted":
        "∀ (requests : List Request) (pre : State), StateAdmitted pre → G.StateQuantitiesAdmitted pre.economic → G.StateQuantitiesAdmitted (run requests pre).post.economic",
    "run_preserves_owned_supply_and_claimant_liabilities_backed":
        "∀ (requests : List Request) (pre : State), StateAdmitted pre → G.OwnedMatchesSupply pre.economic → G.ClaimantLiabilitiesBacked pre.economic → G.OwnedMatchesSupply (run requests pre).post.economic ∧ G.ClaimantLiabilitiesBacked (run requests pre).post.economic",
}

SUBJECTS = {
    "lean-mathlib/Proofs/GlobalEconomicStateRefinementV2.lean":
        "c1be0fe70c2db99cb0fe0be584ef935e26079a66787e35aedb98057b5ceee1b1",
    "lean-mathlib/Proofs/AssetTransferSparseTablesV1.lean":
        "5d303c709501cfe0604c3e845a3b2814b8c5ebe4f0fcfd4090bda2d697f077c0",
    "lean-mathlib/Proofs/AssetTransferSparseTraceV1.lean":
        "5a77ac04b4e214ab7d0dc6cb4b77e2369e16a7914d02cffb5df1d0b88f119b83",
    "lean-mathlib/Proofs/AssetTransferSparseStateAdmissionV1.lean":
        "82f54f4d5a5ba5e28a2ed2a96cd6b4155e70458c05d104b31eea0717aaae8649",
    "lean-mathlib/Proofs/AssetTransferSparseAuthorizationV1.lean":
        "91d41486e814f80a876746a1d8a542daeda77599415792b0915f4a2fccc495fa",
    "src/core/asset_transfer_module_v1.py":
        "754d75a37ad70868bf20263fc189fc9e4f5a77cb864d8a1c7973afc253c938d7",
    "src/core/asset_transfer_types_v1.py":
        "5757c8b692820613e1eac30b7103e857a73b42efebbdda62d0a4469511f41277",
    "src/core/global_economic_state_effect_refinement_v1.py":
        "abf60faacdcd45def5163e618494a2202c9c1ab7e11bde1f44b7b29cd0057697",
}


@pytest.fixture(scope="module")
def lean(state_admission_subject: LeanSubject) -> LeanSubject:  # noqa: F811
    """Compile the new source after the sparse-state dependency closure."""
    authorization = state_admission_subject.source / "Proofs" / "AssetTransferSparseAuthorizationV1.lean"
    authorization.write_bytes((PROJECT / "Proofs" / authorization.name).read_bytes())
    authorization_result = _compile(
        state_admission_subject,
        authorization,
        state_admission_subject.library / "Proofs" / authorization.with_suffix(".olean").name,
    )
    assert authorization_result.returncode == 0, authorization_result.stdout + authorization_result.stderr
    assert authorization_result.stdout == authorization_result.stderr == ""

    captured = state_admission_subject.source / "Proofs" / f"{MODULE}.lean"
    captured.write_bytes((PROJECT / "Proofs" / f"{MODULE}.lean").read_bytes())
    result = _compile(
        state_admission_subject,
        captured,
        state_admission_subject.library / "Proofs" / f"{MODULE}.olean",
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout == result.stderr == ""
    return state_admission_subject


def _probe(lean: LeanSubject, name: str, body: str) -> str:
    path = lean.source / f"{name}.lean"
    path.write_text(f"import {NAMESPACE}\n" + OPENS + body)
    result = _compile(lean, path)
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stderr == ""
    return result.stdout


def _decode(output: str) -> list[list[list[str]]]:
    return [json.loads(json.loads(line)) for line in output.splitlines()]


def test_independent_contract_axioms_placeholders_and_source_pins(lean: LeanSubject) -> None:
    source = (lean.source / "Proofs" / f"{MODULE}.lean").read_text()
    code = re.sub(r"/-.*?-/", "", source, flags=re.DOTALL)
    assert re.search(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b", code) is None
    assert tuple(re.findall(r"^theorem (\w+)", code, flags=re.MULTILINE)) == tuple(THEOREM_TYPES)

    consumers = "set_option linter.unusedVariables false\n" + "\n".join(
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


def _policy_term(policy: AssetTransferPolicyV1) -> str:
    return "⟨" + ",".join(
        (
            json.dumps(policy.asset),
            json.dumps(policy.fee_owner),
            f"({policy.transfer_fee_atoms} : Int)",
            str(policy.enabled).lower(),
        )
    ) + "⟩"


def _policies_term(policies: tuple[AssetTransferPolicyV1, ...]) -> str:
    return "[" + ",".join(_policy_term(policy) for policy in policies) + "]"


def _supplies_term(supplies: tuple[AssetSupplyV1, ...]) -> str:
    return "[" + ",".join(
        f"⟨{json.dumps(supply.asset)},({supply.amount_atoms} : Int)⟩"
        for supply in supplies
    ) + "]"


@dataclass(frozen=True)
class Case:
    name: str
    context: AssetTransferContextV1
    pre: AssetTransferStateV1
    command: AssetTransferCommandV1
    error: str | None = None


def _rows(*values: tuple[str, str, int]) -> tuple[EconomicAmountV1, ...]:
    return tuple(sorted(
        (EconomicAmountV1(owner, asset, "accounts", amount) for owner, asset, amount in values),
        key=lambda row: row.key,
    ))


def _case(
    name: str,
    *,
    policies: tuple[AssetTransferPolicyV1, ...] | None = None,
    rows: tuple[tuple[str, str, int], ...] | None = None,
    supplies: tuple[AssetSupplyV1, ...] | None = None,
    context_release: str = ROOT,
    subject: str = "alice",
    command_kind: str = "asset_transfer",
    asset: str = "USD",
    sender: str = "alice",
    recipient: str = "bob",
    amount: int = 4,
    max_fee: int = 1,
    error: str | None = None,
) -> Case:
    selected_policies = policies if policies is not None else (
        AssetTransferPolicyV1("EUR", "eur_treasury", 2, True),
        AssetTransferPolicyV1("USD", "usd_treasury", 1, True),
    )
    selected_rows = rows if rows is not None else (
        ("alice", "EUR", 40), ("bob", "EUR", 5),
        ("alice", "USD", 50), ("bob", "USD", 7),
    )
    balances = _rows(*selected_rows)
    selected_supplies = supplies if supplies is not None else tuple(
        AssetSupplyV1(policy.asset, 100) for policy in selected_policies
    )
    state = AssetTransferStateV1(ROOT, selected_policies, balances, selected_supplies)
    context = AssetTransferContextV1(
        "selection", ROOT, ROOT, 1, context_release, ROOT, subject, ROOT,
    )
    command = AssetTransferCommandV1(
        command_kind, asset, sender, recipient, amount, max_fee,
    )
    return Case(name, context, state, command, error)


def _state_term(case: Case) -> str:
    return (
        "{ moduleReleaseId := " + json.dumps(case.pre.module_release_id)
        + ", policies := " + _policies_term(case.pre.policies)
        + ", economic := { staticGlobalState with balances := "
        + _amounts_term(case.pre.balances)
        + ", supplies := " + _supplies_term(case.pre.supplies) + " } }"
    )


def _input_term(case: Case) -> str:
    command = case.command
    return (
        "{ context := ⟨" + json.dumps(case.context.module_release_id) + ","
        + json.dumps(case.context.subject_id) + "⟩, command := ⟨"
        + ",".join(
            (
                json.dumps(command.command_kind),
                json.dumps(command.asset),
                json.dumps(command.sender),
                json.dumps(command.recipient),
                f"({command.amount_atoms} : Int)",
                f"({command.max_fee_atoms} : Int)",
            )
        ) + "⟩, pre := " + _state_term(case) + " }"
    )


def _policy_view(policies: tuple[AssetTransferPolicyV1, ...]) -> list[list[str]]:
    return [
        [policy.asset, policy.fee_owner, str(policy.transfer_fee_atoms), str(policy.enabled).lower()]
        for policy in policies
    ]


def _supplies_view(supplies: tuple[AssetSupplyV1, ...]) -> list[list[str]]:
    return [[supply.asset, str(supply.amount_atoms)] for supply in supplies]


def _effects_view(rows: tuple[EconomicEffectRowV1, ...]) -> list[list[str]]:
    return [
        [row.kind.value, row.principal, row.asset, row.custody_domain, str(row.delta_atoms)]
        for row in rows
    ]


def _expected_view(case: Case) -> list[list[str]]:
    before = (
        canonical_global_bytes_v1(case.context),
        canonical_global_bytes_v1(case.pre),
        canonical_global_bytes_v1(case.command),
        asdict(case.context),
        asdict(case.pre),
        asdict(case.command),
    )
    result = transition_asset_transfer_v1(case.context, case.pre, case.command)
    after = (
        canonical_global_bytes_v1(case.context),
        canonical_global_bytes_v1(case.pre),
        canonical_global_bytes_v1(case.command),
        asdict(case.context),
        asdict(case.pre),
        asdict(case.command),
    )
    assert before == after
    if case.error is not None:
        assert isinstance(result, AssetTransferRejectedV1)
        assert result.code.value == case.error
        assert result.pre_state_root == result.post_state_root == case.pre.state_root
        assert result.effects.is_empty
        post = case.pre
        effects: list[list[str]] = []
    else:
        assert isinstance(result, AssetTransferAcceptedV1)
        policy = next(policy for policy in case.pre.policies if policy.asset == case.command.asset)
        events = (
            (case.command.sender, -case.command.amount_atoms - policy.transfer_fee_atoms),
            (case.command.recipient, case.command.amount_atoms),
            (policy.fee_owner, policy.transfer_fee_atoms),
        )
        values = {(row.asset, row.owner): row.amount_atoms for row in case.pre.balances}
        for owner, delta in events:
            key = (case.command.asset, owner)
            values[key] = values.get(key, 0) + delta
        expected_rows = tuple(
            EconomicAmountV1(owner, asset, "accounts", amount)
            for (asset, owner), amount in sorted(values.items())
            if amount
        )
        assert result.post_state.balances == expected_rows
        assert result.post_state.policies == case.pre.policies
        assert result.post_state.supplies == case.pre.supplies
        movement_deltas = {
            owner: sum(delta for event_owner, delta in events if event_owner == owner)
            for owner, _ in events
        }
        expected_effect_rows = [
            [EconomicEffectKindV1.ACCOUNT_MOVEMENT.value, owner, case.command.asset,
             "accounts", str(delta)]
            for owner, delta in movement_deltas.items() if delta
        ]
        if policy.transfer_fee_atoms:
            expected_effect_rows.append([
                EconomicEffectKindV1.FEE_ALLOCATION.value, policy.fee_owner,
                case.command.asset, "accounts", str(policy.transfer_fee_atoms),
            ])
        expected_effect_rows.sort(key=lambda row: (row[0], row[2], row[1], row[3], row[4]))
        effects = expected_effect_rows
        assert _effects_view(result.effects.rows) == effects
        post = result.post_state
    verdict = case.error or "ACCEPTED"
    return [
        [verdict],
        ["POLICIES"], *_policy_view(post.policies),
        ["SUPPLIES"], *_supplies_view(post.supplies),
        ["BALANCES"], *_balances_view(post.balances),
        ["EFFECTS"], *effects,
    ]


def _corpus() -> tuple[Case, ...]:
    upper = (1 << 127) - 1
    base = _case("usd_later_row")
    disabled = (
        AssetTransferPolicyV1("EUR", "eur_treasury", 2, True),
        AssetTransferPolicyV1("USD", "usd_treasury", 1, False),
    )
    return (
        base,
        _case("eur_later_or_first", asset="EUR", amount=3, max_fee=2),
        _case("unknown_asset", asset="GBP", error="UNKNOWN_ASSET"),
        _case("disabled_asset", policies=disabled, error="DISABLED_ASSET"),
        _case("release_precedes_command_and_asset", context_release=OTHER_ROOT,
              command_kind="other", asset="MISSING", error="RELEASE_MISMATCH"),
        _case("command_precedes_asset", command_kind="other", asset="MISSING",
              error="UNKNOWN_COMMAND"),
        _case("asset_precedes_subject_and_self", asset="MISSING", subject="mallory",
              sender="alice", recipient="alice", amount=0, max_fee=0,
              error="UNKNOWN_ASSET"),
        _case("eur_fee_limit", asset="EUR", amount=3, max_fee=1,
              error="FEE_LIMIT_EXCEEDED"),
        _case("usd_fee_limit", max_fee=0, error="FEE_LIMIT_EXCEEDED"),
        _case("fee_owner_sender", policies=(
            AssetTransferPolicyV1("EUR", "alice", 2, True),
            AssetTransferPolicyV1("USD", "usd_treasury", 1, True),
        ), asset="EUR", amount=3, max_fee=2),
        _case("fee_owner_recipient", policies=(
            AssetTransferPolicyV1("EUR", "eur_treasury", 2, True),
            AssetTransferPolicyV1("USD", "bob", 1, True),
        ), amount=4, max_fee=1),
        _case("signed_i128_max", policies=(
            AssetTransferPolicyV1("USD", "treasury", 0, True),
        ), rows=(("alice", "USD", upper),),
              supplies=(AssetSupplyV1("USD", upper),), amount=upper, max_fee=0),
        _case("signed_i128_overflow", policies=(
            AssetTransferPolicyV1("USD", "treasury", 0, True),
        ), rows=(("alice", "USD", upper + 1),),
              supplies=(AssetSupplyV1("USD", upper + 1),), amount=upper + 1,
              max_fee=0, error="EFFECT_DELTA_OVERFLOW"),
    )


def test_public_transition_multi_asset_corpus_matches_complete_modeled_rows(
    lean: LeanSubject,
) -> None:
    cases = _corpus()
    expected = [_expected_view(case) for case in cases]
    probes = "\n".join(
        f"#eval IO.println (reprStr (reprStr (observe ({_input_term(case)}))))"
        for case in cases
    )
    actual = _decode(_probe(lean, "RuntimeCorpus", OBSERVERS + probes))
    assert actual == expected


OBSERVERS = r'''
def verdictCode : T.Verdict → String
  | .accepted => "ACCEPTED"
  | .rejected code => code.code

def policyView (rows : List T.Policy) : List (List String) :=
  rows.map fun policy =>
    [policy.asset, policy.feeOwner, toString policy.transferFeeAtoms,
      toString policy.enabled]

def suppliesView (rows : List G.SupplyRow) : List (List String) :=
  rows.map fun supply => [supply.asset, toString supply.amountAtoms]

def balancesView (rows : List G.AmountRow) : List (List String) :=
  rows.map fun row => [row.owner, row.asset, row.custodyDomain, toString row.amountAtoms]

def effectsView (rows : List EconomicEffectRow) : List (List String) :=
  rows.map fun row =>
    [row.kind.code, row.principal, row.asset, row.custodyDomain, toString row.deltaAtoms]

def observe (input : Input) : List (List String) :=
  let output := step input
  [[verdictCode output.verdict], ["POLICIES"]] ++ policyView output.post.policies ++
    [["SUPPLIES"]] ++ suppliesView output.post.economic.supplies ++
    [["BALANCES"]] ++ balancesView output.post.economic.balances ++
    [["EFFECTS"]] ++ effectsView output.plan.rows
'''


def test_nonempty_two_asset_witness_uses_admission_and_preservation_theorems(
    lean: LeanSubject,
) -> None:
    body = r'''
namespace NonemptyWitness

def eurPolicy : T.Policy := ⟨"EUR", "eur_treasury", 2, true⟩
def usdPolicy : T.Policy := ⟨"USD", "usd_treasury", 1, true⟩

def initial : State :=
  { moduleReleaseId := "0x0101010101010101010101010101010101010101010101010101010101010101"
    policies := [eurPolicy, usdPolicy]
    economic := { staticGlobalState with
      balances := [
        ⟨"alice", "EUR", "accounts", 40⟩,
        ⟨"bob", "EUR", "accounts", 5⟩,
        ⟨"alice", "USD", "accounts", 50⟩,
        ⟨"bob", "USD", "accounts", 7⟩]
      supplies := [⟨"EUR", 45⟩, ⟨"USD", 57⟩] } }

def eurRequest : Request :=
  ⟨⟨initial.moduleReleaseId, "alice"⟩,
   ⟨"asset_transfer", "EUR", "alice", "bob", 3, 2⟩⟩
def usdRequest : Request :=
  ⟨⟨initial.moduleReleaseId, "alice"⟩,
   ⟨"asset_transfer", "USD", "alice", "bob", 4, 1⟩⟩
def rejectedRequest : Request :=
  ⟨⟨initial.moduleReleaseId, "alice"⟩,
   ⟨"asset_transfer", "GBP", "alice", "bob", 1, 1⟩⟩

def eurInput : Input := inputFor eurRequest initial
def usdInput : Input := inputFor usdRequest initial
def history : History := run [rejectedRequest, eurRequest, usdRequest] initial

theorem initial_state_admitted : StateAdmitted initial := by
  refine ⟨?_, ?_, ?_, by decide, ?_⟩
  · refine ⟨?_, ?_, by decide, by decide⟩
    · unfold S.Unique
      decide
    · intro row member
      simp [initial] at member
      rcases member with rfl | rfl | rfl | rfl <;> decide
  · refine ⟨?_, ?_, by decide, ?_⟩
    · decide
    · decide
    · intro policy member
      simp [initial] at member
      rcases member with rfl | rfl <;> decide
  · refine ⟨?_, ?_, by decide, ?_⟩
    · decide
    · decide
    · intro supply member
      simp [initial] at member
      rcases member with rfl | rfl <;> decide
  · intro asset
    by_cases eur : "EUR" = asset
    · subst asset
      decide
    · by_cases usd : "USD" = asset
      · subst asset
        decide
      · simp [initial, amountForAsset, supplyFor, eur, usd] <;> omega

theorem initial_economic_admitted : StateQuantitiesAdmitted initial.economic := by
  unfold StateQuantitiesAdmitted
  refine ⟨by simp [initial, staticGlobalState, FitsU64, maxU64],
    by simp [initial, staticGlobalState, FitsU64, maxU64],
    ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide, by decide,
    ?_, by simp [initial, staticGlobalState],
    by simp [initial, staticGlobalState, TerminalObligationAdmitted,
      FitsU128, maxU128],
    by simp [initial, staticGlobalState, ReplayOccurrenceIdsInjective],
    by simp [initial, staticGlobalState, OracleRegistryAdmitted,
      OracleRegistryWithinGlobalHeight, OracleRegistryKeysMatch]⟩
  · simp [SparseAmountRowsAdmitted, initial, staticGlobalState, FitsU128, maxU128]
  · simp [SparseSupplyRowsAdmitted, initial, staticGlobalState, FitsU128, maxU128]
  · simp [SparseAmountRowsAdmitted, initial, staticGlobalState, FitsU128, maxU128]
  · simp [SparseAmountRowsAdmitted, initial, staticGlobalState, FitsU128, maxU128]
  · simp [SparseAmountRowsAdmitted, initial, staticGlobalState, FitsU128, maxU128]
  · intro asset
    by_cases eur : "EUR" = asset
    · subst asset
      simp [ownedFor, liabilityFor, amountForAsset, supplyFor, initial,
        staticGlobalState, FitsU128, maxU128]
    · by_cases usd : "USD" = asset
      · subst asset
        simp [ownedFor, liabilityFor, amountForAsset, supplyFor, initial,
          staticGlobalState, FitsU128, maxU128]
      · simp [ownedFor, liabilityFor, amountForAsset, supplyFor, initial,
          staticGlobalState, eur, usd, FitsU128, maxU128] <;> omega

theorem initial_owned_supply : G.OwnedMatchesSupply initial.economic := by
  intro asset
  by_cases eur : "EUR" = asset
  · subst asset
    simp [ownedFor, amountForAsset, supplyFor, initial, staticGlobalState]
  · by_cases usd : "USD" = asset
    · subst asset
      simp [ownedFor, amountForAsset, supplyFor, initial, staticGlobalState]
    · simp [ownedFor, amountForAsset, supplyFor, initial, staticGlobalState,
        eur, usd] <;> omega

theorem initial_claimant_backed : G.ClaimantLiabilitiesBacked initial.economic := by
  simp [ClaimantLiabilitiesBacked, OpenTerminalLiabilitiesCovered,
    amountForAssetDomain, openTerminalAmountFor, amountAt, initial,
    staticGlobalState]

example : eurPolicy.transferFeeAtoms ≠ usdPolicy.transferFeeAtoms := by decide
example : eurPolicy.feeOwner ≠ usdPolicy.feeOwner := by decide
example : (step eurInput).verdict = .accepted := by decide
example : (step usdInput).verdict = .accepted := by decide
example : (step (inputFor rejectedRequest initial)).verdict = .rejected .unknownAsset := by decide

example : T.StateWellFormed (S.localState (selectedInput eurInput eurPolicy)) :=
  selectedInput_state_well_formed initial_state_admitted (by
    simp [eurInput, eurRequest, inputFor, initial, policyFor, eurPolicy])
example : StateAdmitted (step eurInput).post :=
  step_preserves_state_admitted initial_state_admitted
example : StateAdmitted history.post :=
  run_preserves_state_admitted [rejectedRequest, eurRequest, usdRequest]
    initial initial_state_admitted
example : G.StateQuantitiesAdmitted history.post.economic :=
  run_preserves_state_quantities_admitted
    [rejectedRequest, eurRequest, usdRequest] initial initial_state_admitted
    initial_economic_admitted
example : G.OwnedMatchesSupply history.post.economic ∧
    G.ClaimantLiabilitiesBacked history.post.economic :=
  run_preserves_owned_supply_and_claimant_liabilities_backed
    [rejectedRequest, eurRequest, usdRequest] initial initial_state_admitted
    initial_owned_supply initial_claimant_backed

example :
    "alice" = eurInput.command.sender ∧
      eurInput.command.sender = eurInput.context.subjectId ∧
      eurInput.command.asset = "EUR" ∧ S.accounts = "accounts" :=
  accepted_decrease_authorized (input := eurInput) initial_state_admitted
    (by exact ⟨by decide, by decide⟩) (by decide) (owner := "alice") (asset := "EUR")
    (domain := "accounts") (by
      have selection : policyFor eurInput.pre.policies eurInput.command.asset = some eurPolicy := by
        simp [eurInput, eurRequest, inputFor, initial, policyFor, eurPolicy]
      have frontDoor : step eurInput =
          lift eurInput (S.step (selectedInput eurInput eurPolicy)) :=
        step_selected (input := eurInput) (policy := eurPolicy) (by rfl) (by rfl) selection
      rw [frontDoor]
      simp only [lift]
      have equation := Proofs.AssetTransferSparseTablesV1.accepted_balance_equation
        (input := selectedInput eurInput eurPolicy)
        initial_state_admitted.1.1 initial_state_admitted.1.2.1 (by decide)
        "alice" "EUR" "accounts"
      have equation' :
          amountAt (S.step (selectedInput eurInput eurPolicy)).post.balances
              "alice" "EUR" "accounts" -
            amountAt eurInput.pre.economic.balances "alice" "EUR" "accounts" = -5 := by
        simpa [selectedInput, eurInput, eurRequest, initial, inputFor, eurPolicy,
          Proofs.AssetTransferSparseTablesV1.localState,
          Proofs.AssetTransferRefinementV1.delta,
          Proofs.AssetTransferRefinementV1.indicator] using equation
      omega)

example : StateQuantitiesAdmitted (S.step (selectedInput eurInput eurPolicy)).post :=
  A.step_preserves_state_quantities_admitted
    initial_state_admitted.1 initial_economic_admitted

example : ∃ policy ∈ initial.policies, policy.asset = "USD" :=
  admitted_balance_asset_has_policy initial_state_admitted
    (row := ⟨"alice", "USD", "accounts", 50⟩) (by decide)

#eval IO.println (reprStr (reprStr (
  [["COUNT", toString history.acceptedPlans.length],
   ["ALICE_EUR", toString (amountAt history.post.economic.balances "alice" "EUR" "accounts")],
   ["BOB_EUR", toString (amountAt history.post.economic.balances "bob" "EUR" "accounts")],
   ["ALICE_USD", toString (amountAt history.post.economic.balances "alice" "USD" "accounts")],
   ["BOB_USD", toString (amountAt history.post.economic.balances "bob" "USD" "accounts")]])))

end NonemptyWitness
'''
    assert json.loads(json.loads(_probe(lean, "NonemptyWitness", body).strip())) == [
        ["COUNT", "2"],
        ["ALICE_EUR", "35"],
        ["BOB_EUR", "8"],
        ["ALICE_USD", "45"],
        ["BOB_USD", "11"],
    ]


def test_stateful_policy_lookup_history_has_independent_endpoint_sums(lean: LeanSubject) -> None:
    initial = _case("history")
    current = initial.pre
    accepted: list[tuple[AssetTransferCommandV1, AssetTransferAcceptedV1]] = []
    for case in (
        replace(initial, command=replace(initial.command, asset="GBP"), error="UNKNOWN_ASSET"),
        replace(initial, command=replace(initial.command, asset="EUR", amount_atoms=3, max_fee_atoms=2)),
        replace(initial, command=replace(initial.command, asset="USD", amount_atoms=4, max_fee_atoms=1)),
    ):
        before = canonical_global_bytes_v1(current)
        result = transition_asset_transfer_v1(case.context, current, case.command)
        assert canonical_global_bytes_v1(current) == before
        if isinstance(result, AssetTransferRejectedV1):
            assert result.code.value == case.error == "UNKNOWN_ASSET"
            assert result.pre_state_root == result.post_state_root == current.state_root
            assert result.effects.is_empty
        else:
            assert isinstance(result, AssetTransferAcceptedV1)
            accepted.append((case.command, result))
            current = result.post_state

    endpoint = {(row.asset, row.owner): row.amount_atoms for row in initial.pre.balances}
    for command, _result in accepted:
        policy = next(policy for policy in initial.pre.policies if policy.asset == command.asset)
        for owner, delta in (
            (command.sender, -command.amount_atoms - policy.transfer_fee_atoms),
            (command.recipient, command.amount_atoms),
            (policy.fee_owner, policy.transfer_fee_atoms),
        ):
            key = (command.asset, owner)
            endpoint[key] = endpoint.get(key, 0) + delta
    endpoint = {key: amount for key, amount in endpoint.items() if amount}
    assert endpoint == {(row.asset, row.owner): row.amount_atoms for row in current.balances}
    assert current.policies == initial.pre.policies
    assert current.supplies == initial.pre.supplies

    body = f'''
def initial : State := {_state_term(initial)}
def rejectedRequest : Request :=
  ⟨⟨initial.moduleReleaseId, "alice"⟩,
    ⟨"asset_transfer", "GBP", "alice", "bob", 4, 1⟩⟩
def eurRequest : Request :=
  ⟨⟨initial.moduleReleaseId, "alice"⟩,
    ⟨"asset_transfer", "EUR", "alice", "bob", 3, 2⟩⟩
def usdRequest : Request :=
  ⟨⟨initial.moduleReleaseId, "alice"⟩,
    ⟨"asset_transfer", "USD", "alice", "bob", 4, 1⟩⟩
def history := run [rejectedRequest, eurRequest, usdRequest] initial
#eval IO.println (reprStr (reprStr (
  [["COUNT", toString history.acceptedPlans.length],
   ["POLICIES", toString history.post.policies.length],
   ["SUPPLIES", toString history.post.economic.supplies.length]] ++
  history.post.economic.balances.map fun row =>
    [row.owner, row.asset, row.custodyDomain, toString row.amountAtoms])))
'''
    observed = json.loads(json.loads(_probe(lean, "StatefulHistory", body).strip()))
    assert observed == [
        ["COUNT", "2"], ["POLICIES", "2"], ["SUPPLIES", "2"],
        ["alice", "EUR", "accounts", "35"],
        ["bob", "EUR", "accounts", "8"],
        ["eur_treasury", "EUR", "accounts", "2"],
        ["alice", "USD", "accounts", "45"],
        ["bob", "USD", "accounts", "11"],
        ["usd_treasury", "USD", "accounts", "1"],
    ]


def test_zero_supply_row_is_admitted_and_duplicate_supply_sum_is_rejected(
    lean: LeanSubject,
) -> None:
    initial = _case("admission_controls")
    body = f'''
def initial : State := {_state_term(initial)}
def zeroSupplyState : State := {{ initial with
  policies := initial.policies ++ [⟨"ZZZ", "zero_treasury", 0, true⟩]
  economic := {{ initial.economic with
    supplies := initial.economic.supplies ++ [⟨"ZZZ", 0⟩] }} }}

theorem zero_supply_row_admitted : StateAdmitted zeroSupplyState := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold S.CanonicalBalances
    refine ⟨?_, ?_, by decide, ?_⟩
    · unfold S.Unique
      decide
    · intro row member
      simp [zeroSupplyState, initial] at member
      rcases member with rfl | rfl | rfl | rfl <;> decide
    · decide
  · unfold PoliciesAdmitted
    refine ⟨by decide, by decide, by decide, ?_⟩
    intro policy member
    simp [zeroSupplyState, initial] at member
    rcases member with rfl | rfl | rfl <;> decide
  · unfold SuppliesAdmitted
    refine ⟨by decide, by decide, by decide, ?_⟩
    intro supply member
    simp [zeroSupplyState, initial] at member
    rcases member with rfl | rfl | rfl <;> decide
  · decide
  intro asset
  by_cases eur : "EUR" = asset
  · subst asset
    decide
  · by_cases usd : "USD" = asset
    · subst asset
      decide
    · by_cases zzz : "ZZZ" = asset
      · subst asset
        decide
      · simp [zeroSupplyState, initial, amountForAsset, supplyFor, eur, usd, zzz]

def duplicateSupplies : List G.SupplyRow := [⟨"EUR", 100⟩, ⟨"EUR", 100⟩]
example : G.supplyFor duplicateSupplies "EUR" = 200 := by decide
example : ¬ G.supplyFor duplicateSupplies "EUR" ≤ 100 := by decide
example : ¬ SuppliesAdmitted duplicateSupplies := by
  intro admitted
  have unique : ¬ (duplicateSupplies.map supplyKey).Nodup := by decide
  exact unique admitted.1
'''
    _probe(lean, "SupplyAdmissionControls", body)


def test_first_row_lookup_mutant_is_well_typed_then_killed_by_lookup_theorem(
    lean: LeanSubject,
) -> None:
    captured_path = lean.source / "Proofs" / f"{MODULE}.lean"
    original_path = PROJECT / "Proofs" / f"{MODULE}.lean"
    original_bytes = original_path.read_bytes()
    assert captured_path.read_bytes() == original_bytes
    source = captured_path.read_text()
    lookup_definition = re.search(
        r"^def policyFor \(policies : List T\.Policy\) \(asset : String\) : Option T\.Policy :=\n"
        r"  policies\.find\? fun policy => policy\.asset == asset$",
        source,
        flags=re.MULTILINE,
    )
    assert lookup_definition is not None
    definition = lookup_definition.group(0)
    mutated_definition = definition.replace(
        "policy.asset == asset", "(policy.asset == asset || true)", 1
    )
    mutated = source.replace(definition, mutated_definition, 1)

    theorem_blocks = list(re.finditer(
        r"^theorem (\w+).*?(?=^theorem \w+|^end AssetTransferPolicySelectionV1$)",
        mutated, flags=re.MULTILINE | re.DOTALL,
    ))
    lookup_block = next(block for block in theorem_blocks if block.group(1) == "policyFor_some")
    first_theorem = theorem_blocks[0]
    prefix = mutated[:first_theorem.start()]
    prefix += r'''
def earlier : T.Policy := ⟨"EUR", "eur_treasury", 2, true⟩
def later : T.Policy := ⟨"USD", "usd_treasury", 1, true⟩
#eval IO.println (reprStr (reprStr (match policyFor [earlier, later] "USD" with
  | some policy => [policy.asset, policy.feeOwner, toString policy.transferFeeAtoms]
  | none => ["NONE"])))

end AssetTransferPolicySelectionV1
end Proofs
'''
    prefix_path = lean.source / "MutantFirstPolicyPrefix.lean"
    prefix_path.write_text(prefix)
    prefix_result = _compile(lean, prefix_path)
    assert prefix_result.returncode == 0, prefix_result.stdout + prefix_result.stderr
    assert json.loads(json.loads(prefix_result.stdout.strip())) == [
        "EUR", "eur_treasury", "2"
    ]

    full_path = lean.source / "MutantFirstPolicy.lean"
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
    first = mutated.count("\n", 0, lookup_block.start()) + 1
    following = mutated.count("\n", 0, lookup_block.end()) + 1
    assert any(first <= line < following for line in error_lines), output
    assert captured_path.read_bytes() == original_bytes
    assert original_path.read_bytes() == original_bytes
