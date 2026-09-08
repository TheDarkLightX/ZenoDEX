"""Finite-row differential consumers for the V2 transfer leaf.

The worker theorem is source-pinned and compiled into the existing fresh
managed-accounting closure.  Fixed rows and effect plans are independent
expectations for the actual Python transition.  This qualifies arithmetic row
materialization only; the V2 leaf remains a SHADOW candidate with production
authority ``NONE`` and no runtime, authentication, or publication claim.
"""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import dataclass, replace
from pathlib import Path

import pytest

from src.core.global_settlement_types_v2 import AssetConservationRowV2, FeeConservationRowV2
from tests.core import test_asset_transfer_module_v2 as runtime
from tests.formal import test_lean_managed_asset_finite_accounting_v2 as finite
from tests.formal.test_lean_registered_supply_support_v1 import LeanSubject, _compile
from tests.formal.test_lean_registered_supply_support_v1 import lean as lean

accounting_lean = finite.accounting_lean

MODULE = "AssetTransferFiniteAccountingV2"
NAMESPACE = f"Proofs.{MODULE}"
TRANSFER_SOURCE = Path(__file__).resolve().parents[2] / "lean-mathlib" / "Proofs" / f"{MODULE}.lean"
SOURCE_SHA256 = "ad3257cfdfbd1b9040e8312fc17c5181645c51e1637006df3641c156e4630b7d"
OPEN = f"""open Proofs.GlobalSettlementCoreV2 Proofs.GlobalEconomicStateRefinementV2
open {NAMESPACE}
"""

Row = tuple[str, str, int]
Effect = tuple[str, str, str, str, int]


@dataclass(frozen=True)
class TransferVector:
    fee_owner: str
    sender: str
    recipient: str
    amount_atoms: int
    fee_atoms: int
    usd_supply: int
    rows: tuple[Row, ...]
    expected_rows: tuple[Row, ...]
    expected_effects: tuple[Effect, ...]


DISTINCT = TransferVector(
    "treasury",
    "alice",
    "bob",
    7,
    2,
    10,
    (("EUR", "carol", 5), ("USD", "alice", 9), ("USD", "bob", 1)),
    (("EUR", "carol", 5), ("USD", "bob", 8), ("USD", "treasury", 2)),
    (
        ("ACCOUNT_MOVEMENT", "alice", "USD", "accounts", -9),
        ("ACCOUNT_MOVEMENT", "bob", "USD", "accounts", 7),
        ("ACCOUNT_MOVEMENT", "treasury", "USD", "accounts", 2),
        ("FEE_ALLOCATION", "treasury", "USD", "accounts", 2),
    ),
)
SENDER_ALIAS = TransferVector(
    "alice",
    "alice",
    "bob",
    7,
    2,
    8,
    (("EUR", "carol", 5), ("USD", "alice", 7), ("USD", "bob", 1)),
    (("EUR", "carol", 5), ("USD", "bob", 8)),
    (
        ("ACCOUNT_MOVEMENT", "alice", "USD", "accounts", -7),
        ("ACCOUNT_MOVEMENT", "bob", "USD", "accounts", 7),
        ("FEE_ALLOCATION", "alice", "USD", "accounts", 2),
    ),
)
RECIPIENT_ALIAS = TransferVector(
    "bob",
    "alice",
    "bob",
    7,
    2,
    10,
    (("EUR", "carol", 5), ("USD", "alice", 9), ("USD", "bob", 1)),
    (("EUR", "carol", 5), ("USD", "bob", 10)),
    (
        ("ACCOUNT_MOVEMENT", "alice", "USD", "accounts", -9),
        ("ACCOUNT_MOVEMENT", "bob", "USD", "accounts", 9),
        ("FEE_ALLOCATION", "bob", "USD", "accounts", 2),
    ),
)
RECREATE = TransferVector(
    "treasury",
    "bob",
    "alice",
    6,
    2,
    10,
    DISTINCT.expected_rows,
    (("EUR", "carol", 5), ("USD", "alice", 6), ("USD", "treasury", 4)),
    (
        ("ACCOUNT_MOVEMENT", "alice", "USD", "accounts", 6),
        ("ACCOUNT_MOVEMENT", "bob", "USD", "accounts", -8),
        ("ACCOUNT_MOVEMENT", "treasury", "USD", "accounts", 2),
        ("FEE_ALLOCATION", "treasury", "USD", "accounts", 2),
    ),
)
VECTORS = (DISTINCT, SENDER_ALIAS, RECIPIENT_ALIAS, RECREATE)


def _state(vector: TransferVector) -> runtime.AssetTransferStateV2:
    selected = replace(
        runtime._policy(asset="USD", transfer_fee_atoms=vector.fee_atoms),
        fee_owner=vector.fee_owner,
    )
    untouched = runtime._policy(asset="EUR", transfer_fee_atoms=0)
    balances = tuple(
        runtime.EconomicAmountV2(
            owner,
            asset,
            runtime.ACCOUNT_CUSTODY_DOMAIN_V2,
            amount,
        )
        for asset, owner, amount in vector.rows
    )
    return runtime.AssetTransferStateV2(
        module_release_id=runtime._root("asset-release"),
        policies=tuple(sorted((untouched, selected), key=lambda policy: policy.asset)),
        balances=balances,
        supplies=(runtime.AssetSupplyV2("EUR", 5), runtime.AssetSupplyV2("USD", vector.usd_supply)),
    )


def _command(vector: TransferVector) -> runtime.AssetTransferCommandV2:
    return runtime._command(
        asset="USD",
        sender=vector.sender,
        recipient=vector.recipient,
        amount_atoms=vector.amount_atoms,
        max_fee_atoms=vector.fee_atoms,
    )


def _row_view(rows: tuple[runtime.EconomicAmountV2, ...]) -> list[list[str]]:
    return [[row.owner, row.asset, row.custody_domain, str(row.amount_atoms)] for row in rows]


def _expected_view(rows: tuple[Row, ...]) -> list[list[str]]:
    return [
        [owner, asset, runtime.ACCOUNT_CUSTODY_DOMAIN_V2, str(amount)]
        for asset, owner, amount in rows
    ]


def _effect_view(result: runtime.AssetTransferAcceptedV2) -> tuple[Effect, ...]:
    return tuple(
        (
            row.kind.value,
            row.principal,
            row.asset,
            row.custody_domain,
            row.delta_atoms,
        )
        for row in result.effects.rows
    )


def _lean_rows(rows: tuple[Row, ...]) -> str:
    return (
        "["
        + ", ".join(
            f'⟨{json.dumps(owner)}, {json.dumps(asset)}, "accounts", ({amount} : Int)⟩'
            for asset, owner, amount in rows
        )
        + "]"
    )


def _materialization_body(vectors: tuple[TransferVector, ...], *, evaluate: bool = True) -> str:
    body = """
def rowView (rows : List AmountRow) : List (List String) :=
  rows.map (fun row => [row.owner, row.asset, row.custodyDomain, toString row.amountAtoms])
def policyFor (feeOwner : String) (fee : Int) : T.Policy :=
  { asset := "USD"
    feeOwner := feeOwner
    transferFeeAtoms := fee
    enabled := true
    assetClass := .registeredOrdinaryToken
    assetOriginRoot := some "origin:USD"
    atomDecimals := 8 }
def commandFor (sender recipient : String) (amount fee : Int) : T.Command :=
  { commandKind := "asset_transfer"
    commandBodyHash := "body"
    asset := "USD"
    sender := sender
    recipient := recipient
    amountAtoms := amount
    maxFeeAtoms := fee
    assetOriginRoot := some "origin:USD" }
"""
    for index, vector in enumerate(vectors):
        body += f"""
def policy{index} : T.Policy := policyFor {json.dumps(vector.fee_owner)} {vector.fee_atoms}
def rows{index} : List AmountRow := {_lean_rows(vector.rows)}
def pre{index} : T.TransferState := project "release-v2" policy{index} rows{index} {vector.usd_supply}
def command{index} : T.Command := commandFor {json.dumps(vector.sender)} {json.dumps(vector.recipient)} {vector.amount_atoms} {vector.fee_atoms}
"""
        if evaluate:
            body += f"#eval IO.println (reprStr (rowView (transferRows pre{index} command{index} rows{index})))\n"
    return body


@pytest.fixture(scope="module")
def transfer_lean(accounting_lean: LeanSubject) -> LeanSubject:
    source = TRANSFER_SOURCE.read_bytes()
    assert hashlib.sha256(source).hexdigest() == SOURCE_SHA256
    captured = accounting_lean.source / "Proofs" / f"{MODULE}.lean"
    captured.write_bytes(source)
    checked = _compile(
        accounting_lean, captured, accounting_lean.library / "Proofs" / f"{MODULE}.olean"
    )
    assert checked.returncode == 0, checked.stdout + checked.stderr
    assert checked.stdout == checked.stderr == ""
    return accounting_lean


def _probe(subject: LeanSubject, name: str, body: str) -> str:
    path = subject.source / f"{name}.lean"
    path.write_text(f"import {NAMESPACE}\n{OPEN}{body}")
    checked = _compile(subject, path)
    assert checked.returncode == 0, checked.stdout + checked.stderr
    assert checked.stderr == ""
    return checked.stdout


def test_transfer_contract_has_strong_consumers_and_no_forbidden_axioms(
    transfer_lean: LeanSubject,
) -> None:
    accepted_binders = """∀ {roots : T.RootModel} {ctx : T.Context}
      {moduleReleaseId : String} {policy : T.Policy} {rows : List AmountRow}
      {supplyAtoms : Int} {command : T.Command}, """
    contracts = {
        "transferRows_lookup": """∀ (pre : T.TransferState) (command : T.Command)
          (rows : List AmountRow), S.Unique rows →
          command.sender ≠ command.recipient →
          ∀ queryAsset queryOwner : String,
          C.lookupLast (S.accountKey queryAsset queryOwner)
              (transferRows pre command rows) =
            C.lookupLast (S.accountKey queryAsset queryOwner) rows +
              (if command.asset = queryAsset then T.delta pre command queryOwner else 0)""",
        "transferRows_totals": """∀ (pre : T.TransferState) (command : T.Command)
          (rows : List AmountRow), S.Unique rows →
          command.sender ≠ command.recipient → ∀ query : String,
          amountForAsset (transferRows pre command rows) query =
            amountForAsset rows query""",
        "accepted_materialization": accepted_binders
        + """S.Unique rows →
          (T.transition roots ctx (project moduleReleaseId policy rows supplyAtoms) command).verdict = .accepted →
          (T.transition roots ctx (project moduleReleaseId policy rows supplyAtoms) command).post =
            project moduleReleaseId policy
              (transferRows (project moduleReleaseId policy rows supplyAtoms) command rows)
              supplyAtoms""",
        "accepted_rows_preserve_accounts": accepted_binders
        + """S.Unique rows →
          S.PositiveAccounts rows →
          T.StateWellFormed (project moduleReleaseId policy rows supplyAtoms) →
          (T.transition roots ctx (project moduleReleaseId policy rows supplyAtoms) command).verdict = .accepted →
          S.Unique (transferRows (project moduleReleaseId policy rows supplyAtoms) command rows) ∧
          S.PositiveAccounts
            (transferRows (project moduleReleaseId policy rows supplyAtoms) command rows)""",
    }
    body = (
        "example : (String → T.Policy → List AmountRow → Int → T.TransferState) := project\n"
        "example : (T.TransferState → T.Command → List AmountRow → List AmountRow) := transferRows\n"
        + "\n".join(
            f"example : {signature} := @{NAMESPACE}.{name}\n#print axioms {NAMESPACE}.{name}"
            for name, signature in contracts.items()
        )
    )
    output = _probe(transfer_lean, "TransferFiniteAccountingContracts", body)
    assert output.count("depends on axioms") + output.count("does not depend on any axioms") == len(
        contracts
    )
    axioms = {
        item.strip()
        for group in re.findall(r"depends on axioms:\s*\[([^]]*)\]", output)
        for item in group.split(",")
        if item.strip()
    }
    assert axioms <= {"propext", "Quot.sound", "Classical.choice"}
    code = re.sub(r"/-.*?-/", "", TRANSFER_SOURCE.read_text(), flags=re.DOTALL)
    assert re.search(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b", code) is None


FALSE_LAWS = {
    "CrossAssetLeak": (
        DISTINCT,
        'example : amountForAsset (transferRows pre0 command0 rows0) "EUR" = 6 := by\n'
        "  rw [transferRows_totals pre0 command0 rows0 (by unfold S.Unique; decide) "
        '(by decide) "EUR"]\n  decide\n',
    ),
    "FeeOwnerAlias": (
        SENDER_ALIAS,
        'example : C.lookupLast (S.accountKey "USD" "alice") '
        "(transferRows pre0 command0 rows0) = -2 := by\n"
        "  rw [transferRows_lookup pre0 command0 rows0 (by unfold S.Unique; decide) "
        '(by decide) "USD" "alice"]\n  decide\n',
    ),
    "StaleRecipient": (
        DISTINCT,
        'example : C.lookupLast (S.accountKey "USD" "bob") '
        "(transferRows pre0 command0 rows0) = 7 := by\n"
        "  rw [transferRows_lookup pre0 command0 rows0 (by unfold S.Unique; decide) "
        '(by decide) "USD" "bob"]\n  decide\n',
    ),
}


@pytest.mark.parametrize("name", tuple(FALSE_LAWS))
def test_kernel_rejects_false_transfer_materialization_laws(
    transfer_lean: LeanSubject,
    name: str,
) -> None:
    path = transfer_lean.source / f"{name}.lean"
    vector, law = FALSE_LAWS[name]
    path.write_text(
        f"import {NAMESPACE}\n{OPEN}{_materialization_body((vector,), evaluate=False)}{law}"
    )
    checked = _compile(transfer_lean, path)
    assert checked.returncode != 0
    assert checked.stdout.count("error:") == 1, checked.stdout
    assert "Tactic `decide` proved that the proposition" in checked.stdout
    assert "is false" in checked.stdout


def test_actual_v2_transfer_rows_match_lean_materialization(
    transfer_lean: LeanSubject,
) -> None:
    expected_views: list[list[list[str]]] = []
    body = _materialization_body(VECTORS)
    for vector in VECTORS:
        state = _state(vector)
        command = _command(vector)
        context = runtime._context(state, command)
        state_bytes = runtime.canonical_global_bytes_v2(state)
        state_root = state.state_root
        command_bytes = runtime.canonical_global_bytes_v2(command)
        context_bytes = runtime.canonical_global_bytes_v2(context)
        if vector is RECREATE:
            first_state = _state(DISTINCT)
            first_command = _command(DISTINCT)
            first = runtime.transition_asset_transfer_v2(
                runtime._context(first_state, first_command), first_state, first_command
            )
            assert isinstance(first, runtime.AssetTransferAcceptedV2)
            assert first.post_state == state
        result = runtime.transition_asset_transfer_v2(context, state, command)
        assert isinstance(result, runtime.AssetTransferAcceptedV2)
        assert _row_view(result.post_state.balances) == _expected_view(vector.expected_rows)
        assert _effect_view(result) == vector.expected_effects
        assert result.post_state.policies == state.policies
        assert result.post_state.supplies == state.supplies
        assert result.post_state.supply_atoms("USD") == vector.usd_supply
        assert result.post_state.supply_atoms("EUR") == 5
        assert result.effects.asset_conservation == (
            AssetConservationRowV2(
                "USD",
                vector.usd_supply,
                vector.usd_supply,
                vector.usd_supply,
                vector.usd_supply,
                0,
                0,
            ),
        )
        assert result.effects.fee_conservation == (FeeConservationRowV2("USD", 2, 2, 0),)
        assert result.production_authority == "NONE"
        assert runtime.canonical_global_bytes_v2(state) == state_bytes
        assert state.state_root == state_root
        assert runtime.canonical_global_bytes_v2(command) == command_bytes
        assert runtime.canonical_global_bytes_v2(context) == context_bytes
        expected_views.append(_expected_view(vector.expected_rows))
    output = _probe(transfer_lean, "ActualV2TransferFiniteRows", body)
    observed = [json.loads(line) for line in output.splitlines() if line.strip()]
    assert observed == expected_views
