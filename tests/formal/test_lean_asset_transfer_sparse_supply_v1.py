"""Constructed sparse supply preservation and finite physical-row observations.

The kernel theorem derives account totals and preserves the physical frame;
the independent oracle sums actual Python balances/custody/reserves by asset.
Liabilities are observed separately. Complete route admission, claimant
backing, authenticated context, receipt conservation annotations, and universal
Python/Rust refinement remain outside this packet. The old leaf's accounting
annotation omits external custody; these tests make no claim that its complete
effect plan passes global admission with nonzero custody.
"""
from __future__ import annotations

import hashlib
import json
import re
import subprocess
from dataclasses import asdict, replace
from pathlib import Path

import pytest

from src.core.asset_transfer_module_v1 import transition_asset_transfer_v1
from src.core.asset_transfer_types_v1 import (
    AssetTransferAcceptedV1,
    AssetTransferPolicyV1,
    AssetTransferRejectedV1,
)
from src.core.global_economic_state_effect_refinement_v1 import _amount_totals_by_asset_v1
from src.core.global_settlement_types_v1 import (
    AssetSupplyV1,
    EconomicAmountV1,
    GlobalEconomicStateV1,
)
from tests.formal.test_lean_asset_transfer_sparse_tables_v1 import (
    DEPENDENCIES,
    Case,
    _amounts_term,
    _balances_view,
    _case,
    _term,
)
from tests.formal.test_lean_checked_epoch_economic_tables_v1 import (
    PROJECT,
    LeanSubject,
    _compile,
    _state,
)

MODULE = "AssetTransferSparseSupplyV1"
NAMESPACE = f"Proofs.{MODULE}"
OPENS = f"open Proofs.GlobalSettlementCoreV2 Proofs.GlobalEconomicStateRefinementV2 {NAMESPACE}\n"
SUBJECTS = {
    "lean-mathlib/Proofs/AssetTransferSparseTablesV1.lean": "5d303c709501cfe0604c3e845a3b2814b8c5ebe4f0fcfd4090bda2d697f077c0",
    "lean-mathlib/Proofs/AssetTransferSparseTraceV1.lean": "5a77ac04b4e214ab7d0dc6cb4b77e2369e16a7914d02cffb5df1d0b88f119b83",
    "src/core/asset_transfer_module_v1.py": "754d75a37ad70868bf20263fc189fc9e4f5a77cb864d8a1c7973afc253c938d7",
    "src/core/asset_transfer_types_v1.py": "5757c8b692820613e1eac30b7103e857a73b42efebbdda62d0a4469511f41277",
    "src/core/global_economic_state_effect_refinement_v1.py": "abf60faacdcd45def5163e618494a2202c9c1ab7e11bde1f44b7b29cd0057697",
}
TYPES = {
    "amountForAsset_eraseKey": "∀ (key : C.AmountKey) (rows : List AmountRow) (asset : String), amountForAsset (S.eraseKey key rows) asset = amountForAsset rows asset - (if key.2.1 = asset then C.amountSum key rows else 0)",
    "amountForAsset_putAmount": "∀ (key : C.AmountKey) (atoms : Int) (rows : List AmountRow) (asset : String), amountForAsset (S.putAmount key atoms rows) asset = amountForAsset rows asset + (if key.2.1 = asset then atoms - C.amountSum key rows else 0)",
    "checkedUpdate_amountForAsset": "∀ {rows out : List AmountRow} {asset owner : String} {delta : Int}, S.Unique rows → S.checkedUpdate rows asset owner delta = .ok out → ∀ query : String, amountForAsset out query = amountForAsset rows query + (if asset = query then delta else 0)",
    "updateRoles_amountForAsset": "∀ {asset : String} {delta : String → Int} {owners : List String} {rows out : List AmountRow}, S.Unique rows → S.updateRoles asset delta owners rows = .ok out → ∀ query : String, amountForAsset out query = amountForAsset rows query + (if asset = query then T.sumOver delta owners else 0)",
    "roleOrder_delta_zero": "∀ (pre : T.TransferState) (cmd : T.Command), cmd.sender ≠ cmd.recipient → T.sumOver (T.delta pre cmd) (T.roleOrder pre cmd) = 0",
    "accepted_account_totals": "∀ {i : S.Input}, S.Unique i.pre.balances → (S.step i).verdict = .accepted → ∀ asset : String, amountForAsset (S.step i).post.balances asset = amountForAsset i.pre.balances asset",
    "accepted_owned_totals": "∀ {i : S.Input}, S.Unique i.pre.balances → (S.step i).verdict = .accepted → ∀ asset : String, ownedFor (S.step i).post asset = ownedFor i.pre asset",
    "step_supply_frame": "∀ (i : S.Input) (asset : String), supplyFor (S.step i).post.supplies asset = supplyFor i.pre.supplies asset",
    "accepted_preserves_owned_supply": "∀ {i : S.Input}, S.Unique i.pre.balances → OwnedMatchesSupply i.pre → (S.step i).verdict = .accepted → OwnedMatchesSupply (S.step i).post",
    "accepted_owned_supply_and_canonical": "∀ {i : S.Input}, S.Unique i.pre.balances → S.PositiveAccounts i.pre.balances → OwnedMatchesSupply i.pre → (S.step i).verdict = .accepted → OwnedMatchesSupply (S.step i).post ∧ S.CanonicalBalances (S.step i).post.balances",
    "rejected_owned_supply": "∀ {i : S.Input} {code : T.RejectCode}, OwnedMatchesSupply i.pre → (S.step i).verdict = .rejected code → OwnedMatchesSupply (S.step i).post",
    "history_preserves_owned_supply": "∀ (config : H.Config) (requests : List H.Request) (pre : GlobalState), S.CanonicalBalances pre.balances → OwnedMatchesSupply pre → OwnedMatchesSupply (H.run config requests pre).post",
}
OBSERVERS = """
def physicalView (state : GlobalState) (assets : List String) : List (List String) :=
  assets.map fun asset => [asset, toString (amountForAsset state.balances asset),
    toString (amountForAsset state.custody asset), toString (amountForAsset state.reserves asset),
    toString (ownedFor state asset), toString (supplyFor state.supplies asset),
    toString (amountForAsset state.liabilities asset)]
def observe (input : S.Input) (assets : List String) : String :=
  let output := S.step input
  let verdict := match output.verdict with
    | .accepted => "ACCEPTED"
    | .rejected code => code.code
  reprStr ([[verdict]] ++ physicalView input.pre assets ++ [["POST"]] ++
    physicalView output.post assets ++ [["BALANCES"]] ++
    output.post.balances.map (fun row =>
      [row.owner, row.asset, row.custodyDomain, toString row.amountAtoms]))
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
    directory = tmp_path_factory.mktemp("asset-transfer-sparse-supply")
    source, library = directory / "source", directory / "library"
    (source / "Proofs").mkdir(parents=True)
    (library / "Proofs").mkdir(parents=True)
    subject = LeanSubject(executable, source, library)
    captured_hashes = {}
    for name in (*DEPENDENCIES, "AssetTransferSparseTablesV1", "AssetTransferSparseTraceV1", MODULE):
        captured = source / "Proofs" / f"{name}.lean"
        captured.write_bytes((PROJECT / "Proofs" / f"{name}.lean").read_bytes())
        captured_hashes[name] = hashlib.sha256(captured.read_bytes()).hexdigest()
        result = _compile(subject, captured, library / "Proofs" / f"{name}.olean")
        assert result.returncode == 0, result.stdout + result.stderr
    (directory / "source-hashes.json").write_text(json.dumps(captured_hashes, indent=2) + "\n")
    return subject


def _probe(lean: LeanSubject, name: str, body: str) -> str:
    path = lean.source / f"{name}.lean"
    path.write_text(f"import {NAMESPACE}\n" + OPENS + OBSERVERS + body)
    result = _compile(lean, path)
    assert result.returncode == 0, result.stdout + result.stderr
    return result.stdout


def test_independent_theorem_types_axioms_and_runtime_subjects(lean: LeanSubject) -> None:
    source = (lean.source / "Proofs" / f"{MODULE}.lean").read_text()
    code = re.sub(r"/-.*?-/", "", source, flags=re.DOTALL)
    assert re.search(r"\b(sorry|admit|axiom|native_decide)\b", code) is None
    assert set(re.findall(r"^theorem (\w+)", code, flags=re.MULTILINE)) == set(TYPES)
    body = "\n".join(f"example : {signature} := {name}" for name, signature in TYPES.items())
    body += "\n" + "\n".join(f"#print axioms {NAMESPACE}.{name}" for name in TYPES)
    output = _probe(lean, "IndependentConsumers", body)
    assert len(re.findall("depends on axioms|does not depend on any axioms", output)) == len(TYPES)
    axioms = {a.strip() for group in re.findall(r"depends on axioms:\s*\[([^\]]*)\]", output)
              for a in group.split(",") if a.strip()}
    assert axioms <= {"propext", "Quot.sound", "Classical.choice"}
    for name, digest in SUBJECTS.items():
        assert hashlib.sha256((PROJECT.parent / name).read_bytes()).hexdigest() == digest


def test_existing_nonempty_example_satisfies_derived_endpoint(lean: LeanSubject) -> None:
    _probe(lean, "PositiveConsumer", """
namespace X
export Proofs.AssetTransferSparseTablesV1 (demo demo_source demo_owned_supply
  demo_deletes_zero_and_frames_other_asset)
end X
example : OwnedMatchesSupply (S.step X.demo).post ∧
    S.CanonicalBalances (S.step X.demo).post.balances :=
  accepted_owned_supply_and_canonical X.demo_source.1 X.demo_source.2
    X.demo_owned_supply.1 X.demo_deletes_zero_and_frames_other_asset.1
""")


def _rows(*values: tuple[str, str, str, int]) -> tuple[EconomicAmountV1, ...]:
    return tuple(sorted((EconomicAmountV1(*row) for row in values), key=lambda row: row.key))


def _physical_case(case: Case) -> tuple[Case, GlobalEconomicStateV1]:
    custody = _rows(("vault", "USD", "vault", 11), ("vault", "EUR", "escrow", 5),
                    ("vault", "ONLY_CUSTODY", "vault", 7))
    reserves = _rows(("reserve", "USD", "reserve", 3), ("reserve", "ZZZ", "reserve", 7))
    liabilities = _rows(("claimant", "USD", "vault", 9), ("claimant", "EUR", "escrow", 2))
    physical = (*case.pre.balances, *custody, *reserves)
    supplies = tuple(AssetSupplyV1(asset, sum(row.amount_atoms for row in physical if row.asset == asset))
                     for asset in sorted({row.asset for row in physical}))
    policies = {policy.asset: policy for policy in case.pre.policies}
    for supply in supplies:
        if supply.asset not in policies:
            policies[supply.asset] = AssetTransferPolicyV1(supply.asset, "treasury", 0, True)
    case = replace(case, pre=replace(case.pre, supplies=supplies,
                   policies=tuple(policies[supply.asset] for supply in supplies)))
    state = replace(_state(1, 100), balances=case.pre.balances, custody=custody,
                    reserves=reserves, liabilities=liabilities, supplies=supplies)
    return case, state


def _view(state: GlobalEconomicStateV1, assets: list[str]) -> list[list[str]]:
    def total(rows: tuple[EconomicAmountV1, ...], asset: str) -> int:
        return sum(row.amount_atoms for row in rows if row.asset == asset)

    return [[asset, str(total(state.balances, asset)), str(total(state.custody, asset)),
             str(total(state.reserves, asset)),
             str(sum(total(rows, asset) for rows in (state.balances, state.custody, state.reserves))),
             str(sum(row.amount_atoms for row in state.supplies if row.asset == asset)),
             str(total(state.liabilities, asset))] for asset in assets]


def _input(case: Case, state: GlobalEconomicStateV1) -> str:
    return (f"(let input : S.Input := {_term(case)}; "
            "{ input with pre := { input.pre with "
            f"custody := {_amounts_term(state.custody)}, reserves := {_amounts_term(state.reserves)}, "
            f"liabilities := {_amounts_term(state.liabilities)} " + "} })")


def test_actual_sparse_leaf_preserves_independent_physical_totals(lean: LeanSubject) -> None:
    cases = (_case("distinct"), _case("sender_fee", owner="alice"),
        _case("recipient_fee", owner="bob"), _case("zero_fee", fee=0),
        _case("delete", rows=(("alice", "USD", 32), ("alice", "EUR", 7))),
        _case("new_owner", recipient="!new"),
        _case("u128_total", fee=0, amount=1, rows=(("alice", "USD", (1 << 128) - 15),)),
        _case("i128_min", amount=(1 << 127) - 1, fee=1, rows=(("alice", "USD", 1 << 127),)),
        _case("reject_subject", subject="mallory", error="UNAUTHORIZED_SUBJECT"),
        _case("reject_balance", amount=999, error="INSUFFICIENT_BALANCE"))
    expected, probes = [], []
    for case in cases:
        case, pre = _physical_case(case)
        snapshot = (asdict(case.pre), asdict(pre))
        result = transition_asset_transfer_v1(case.context, case.pre, case.command)
        if case.error:
            assert isinstance(result, AssetTransferRejectedV1) and result.code.value == case.error
            assert result.pre_state_root == result.post_state_root == case.pre.state_root
            assert result.effects.is_empty
            post = pre
        else:
            assert isinstance(result, AssetTransferAcceptedV1)
            post = replace(pre, balances=result.post_state.balances)
            assert result.post_state.supplies == pre.supplies
        assets = sorted({row.asset for row in pre.supplies} | {"ABSENT"})
        before, after = _view(pre, assets), _view(post, assets)
        # This oracle directly re-sums immutable physical rows, independently of
        # the runtime checked dictionary accumulation and Lean sparse updater.
        assert before == after
        for state in (pre, post):
            observed_totals = _amount_totals_by_asset_v1(state)
            assert [observed_totals.get(asset, 0) for asset in assets] == [int(row[4]) for row in before]
            assert all(row[4] == row[5] for row in _view(state, assets))
        assert snapshot == (asdict(case.pre), asdict(pre))
        expected.append([[case.error or "ACCEPTED"], *before, ["POST"], *after,
                         ["BALANCES"], *_balances_view(post.balances)])
        probes.append(f"#eval observe {_input(case, pre)} {json.dumps(assets)}")
    actual = [json.loads(json.loads(line)) for line in _probe(lean, "PhysicalRows", "\n".join(probes)).splitlines()]
    assert actual == expected


def test_global_owned_width_guard_is_a_separate_runtime_boundary() -> None:
    case = _case("global_overflow", fee=0, amount=1, rows=(("alice", "USD", (1 << 128) - 1),))
    pre = replace(_state(1, 100), balances=case.pre.balances, supplies=case.pre.supplies,
                  custody=_rows(("vault", "USD", "vault", 1)), reserves=(), liabilities=())
    result = transition_asset_transfer_v1(case.context, case.pre, case.command)
    assert isinstance(result, AssetTransferAcceptedV1)
    post = replace(pre, balances=result.post_state.balances)
    assert _view(pre, ["USD"]) == _view(post, ["USD"])
    for state in (pre, post):
        with pytest.raises(ValueError, match="^economic refinement owned total exceeds unsigned 128-bit bounds$"):
            _amount_totals_by_asset_v1(state)


def test_rejected_then_accepted_history_preserves_all_physical_assets(lean: LeanSubject) -> None:
    case, pre = _physical_case(_case("history"))
    current = case.pre
    for subject in ("mallory", "alice", "alice"):
        result = transition_asset_transfer_v1(replace(case.context, subject_id=subject), current, case.command)
        if subject == "mallory":
            assert isinstance(result, AssetTransferRejectedV1) and result.code.value == "UNAUTHORIZED_SUBJECT"
            assert result.pre_state_root == result.post_state_root == current.state_root
            assert result.effects.is_empty
        else:
            assert isinstance(result, AssetTransferAcceptedV1)
            current = result.post_state
    post = replace(pre, balances=current.balances)
    assets = sorted({row.asset for row in pre.supplies} | {"ABSENT"})
    assert _view(pre, assets) == _view(post, assets)
    assert _amount_totals_by_asset_v1(pre) == _amount_totals_by_asset_v1(post)
    body = f"""
def start : S.Input := {_input(case, pre)}
def config : H.Config := ⟨start.moduleReleaseId, start.policy⟩
def good : H.Request := ⟨start.context, start.command⟩
def bad : H.Request := ⟨{{ start.context with subjectId := "mallory" }}, start.command⟩
def history := H.run config [bad, good, good] start.pre
#eval reprStr (physicalView history.post {json.dumps(assets)} ++
  [["ACCEPTED_PLANS", toString history.acceptedPlans.length]] ++
  history.post.balances.map (fun row =>
    [row.owner, row.asset, row.custodyDomain, toString row.amountAtoms]))
"""
    observed = json.loads(json.loads(_probe(lean, "PhysicalHistory", body).strip()))
    assert observed == [*_view(post, assets), ["ACCEPTED_PLANS", "2"], *_balances_view(post.balances)]


def test_duplicate_source_requires_uniqueness_and_runtime_constructor_rejects(lean: LeanSubject) -> None:
    case = _case("duplicate", rows=(("alice", "USD", 32),))
    duplicate_rows = (*case.pre.balances, *case.pre.balances)
    with pytest.raises(ValueError, match="canonically ordered and unique"):
        replace(case.pre, balances=duplicate_rows, supplies=(AssetSupplyV1("USD", 64),))
    body = f"""
def sourceInput : S.Input := {_term(case)}
def duplicated : S.Input := {{ sourceInput with pre := {{ staticGlobalState with
  balances := {_amounts_term(duplicate_rows)}, supplies := [⟨"USD", 64⟩] }} }}
example : ¬ S.Unique duplicated.pre.balances := by
  unfold S.Unique
  decide
example : (S.step duplicated).verdict = .accepted := by decide
#eval observe duplicated ["USD"]
"""
    actual = json.loads(json.loads(_probe(lean, "DuplicatePremise", body).strip()))
    assert actual == [["ACCEPTED"], ["USD", "64", "0", "0", "64", "64", "0"],
                      ["POST"], ["USD", "32", "0", "0", "32", "64", "0"], ["BALANCES"],
                      ["bob", "USD", "accounts", "30"], ["treasury", "USD", "accounts", "2"]]
