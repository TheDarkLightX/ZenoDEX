"""Source-pinned custody-row model and finite runtime observation controls.

The theorem oracle covers constructed row materialization, physical accounting,
complete supply support and exact rejection frames. Runtime vectors observe the
four new state fields with actual V2 origin/occurrence inputs. They establish
finite correspondence, without codec, guest, authentication or publication claims.
"""

from __future__ import annotations

import hashlib
import re
from dataclasses import replace
from pathlib import Path

import pytest

from tests.formal.test_lean_asset_transfer_finite_accounting_v2 import SOURCE_SHA256 as TRANSFER_SHA
from tests.formal.test_lean_managed_asset_finite_accounting_v2 import (
    accounting_lean as accounting_lean,
)
from tests.formal.test_lean_managed_asset_registered_accounting_v2 import (
    composition_lean as composition_lean,
)
from tests.formal.test_lean_registered_supply_support_v1 import LeanSubject, _compile
from tests.formal.test_lean_registered_supply_support_v1 import lean as lean

MODULE = "AssetLaneCustodyRefinementV2"
NAMESPACE = f"Proofs.{MODULE}"
PROOFS = Path(__file__).resolve().parents[2] / "lean-mathlib" / "Proofs"
SOURCE_SHA256 = "df3cf08fc7b108d08efc78ab7cecbc5f86e221a80c210e6c9b5ad229699a8de9"
OPEN = f"""open Proofs.GlobalSettlementCoreV2 Proofs.GlobalEconomicStateRefinementV2
open Proofs.RegisteredSupplySupportV1 Proofs.RegisteredSupplyUpdateV1 {NAMESPACE}
"""


@pytest.fixture(scope="module")
def custody_lean(composition_lean: LeanSubject) -> LeanSubject:
    for name, digest in (("AssetTransferFiniteAccountingV2", TRANSFER_SHA), (MODULE, SOURCE_SHA256)):
        source = (PROOFS / f"{name}.lean").read_bytes()
        assert hashlib.sha256(source).hexdigest() == digest
        path = composition_lean.source / "Proofs" / f"{name}.lean"
        path.write_bytes(source)
        checked = _compile(
            composition_lean, path, composition_lean.library / "Proofs" / f"{name}.olean"
        )
        assert checked.returncode == 0, checked.stdout + checked.stderr
        assert checked.stdout == checked.stderr == ""
    return composition_lean


def _probe(subject: LeanSubject, name: str, body: str):
    path = subject.source / f"{name}.lean"
    path.write_text(f"import {NAMESPACE}\n{OPEN}{body}")
    return _compile(subject, path)


def test_exact_custody_lift_contracts_and_standard_axioms(custody_lean: LeanSubject) -> None:
    source = (PROOFS / f"{MODULE}.lean").read_bytes()
    assert hashlib.sha256(source).hexdigest() == SOURCE_SHA256
    contracts = {
        "managed_global_projection": """∀ (pre : State) (frame : GlobalState)
          (asset owner : String) (delta : Int),
          SourceAssetKeysUnique pre.transferState.supplies →
          SourceAssetKeysOrdered pre.transferState.supplies →
          asset ∈ pre.transferState.supplies.map V1SupplyRow.asset →
          globalView (managedPost pre asset owner delta) frame =
            Proofs.ManagedAssetRegisteredAccountingV2.accountingPost
              (globalView pre frame) asset owner delta""",
        "managed_physical_lift": """∀ (pre : State) (asset owner : String) (delta : Int),
          S.Unique pre.transferState.balances → SourceAssetKeysUnique pre.transferState.supplies →
          asset ∈ pre.transferState.supplies.map V1SupplyRow.asset → PhysicalBalanced pre →
          PhysicalBalanced (managedPost pre asset owner delta) ∧
          (managedPost pre asset owner delta).custody = pre.custody ∧
          (managedPost pre asset owner delta).transferState.supplies.map V1SupplyRow.asset =
            pre.transferState.supplies.map V1SupplyRow.asset""",
        "transfer_physical_lift": """∀ (pre : State) (policy : T.Policy) (command : T.Command),
          S.Unique pre.transferState.balances → command.sender ≠ command.recipient →
          PhysicalBalanced pre → PhysicalBalanced (transferPost pre policy command) ∧
          (transferPost pre policy command).custody = pre.custody ∧
          (transferPost pre policy command).transferState.supplies = pre.transferState.supplies""",
    }
    body = "\n".join(
        f"example : {signature} := @{NAMESPACE}.{name}"
        for name, signature in contracts.items()
    )
    names = (*contracts, "accepted_transfer_lift", "accepted_managed_lift",
             "rejected_transfer_noop", "rejected_managed_noop",
             "Controls.legal_custody_state_representable", "Controls.dormant_state_representable",
             "Controls.legal_custody_commands_accept", "Controls.dormant_issue_burn_support")
    body += "\n" + "\n".join(f"#print axioms {NAMESPACE}.{name}" for name in names)
    checked = _probe(custody_lean, "CustodyLiftContracts", body)
    assert checked.returncode == 0, checked.stdout + checked.stderr
    assert checked.stderr == ""
    assert checked.stdout.count("depends on axioms") + checked.stdout.count(
        "does not depend on any axioms"
    ) == len(names)
    axioms = {
        item.strip()
        for group in re.findall(r"depends on axioms:\s*\[([^]]*)\]", checked.stdout)
        for item in group.split(",")
        if item.strip()
    }
    assert axioms <= {"propext", "Quot.sound", "Classical.choice"}
    code = re.sub(r"/-.*?-/", "", source.decode(), flags=re.DOTALL)
    assert re.search(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b", code) is None


@pytest.mark.parametrize(
    "name,law",
    (
        ("DroppedCustody", 'physicalFor { Controls.pre with custody := [] } "ORD" = 120'),
        ("AccountsOnly", 'amountForAsset Controls.pre.transferState.balances "ORD" = 120'),
        ("DroppedDormantIdentity", 'Controls.dormant.originRegistry = ([] : List Asset)'),
        ("ChangedCustodyOwner", 'Controls.pre.custody = [⟨"mallory", "ORD", "escrow", 5⟩]'),
    ),
)
def test_kernel_rejects_custody_and_support_mutants(
    custody_lean: LeanSubject, name: str, law: str,
) -> None:
    checked = _probe(custody_lean, name, f"example : {law} := by decide\n")
    assert checked.returncode != 0
    assert checked.stdout.count("error:") == 1, checked.stdout
    assert "Tactic `decide` proved that the proposition" in checked.stdout
    assert "is false" in checked.stdout


def test_custody_state_fields_match_the_formal_legal_source_and_leaf_controls() -> None:
    from src.core.asset_lane_custody_coordinator_v2 import (
        AssetLaneCustodyAcceptedV2,
        transition_asset_lane_custody_v2,
    )
    from src.core.asset_lane_custody_state_v2 import AssetLaneCustodyStateV2
    from src.core.asset_transfer_types_v2 import AssetTransferStateV2
    from src.core.global_settlement_types_v2 import AssetSupplyV2, EconomicAmountV2
    from tests.core import test_asset_lane_coordinator_v2 as fixture

    keys = ("AUD", "EUR", "ORD")
    policies = tuple(
        fixture._transfer_policy(asset=asset, fee_owner="m_treasury", fee_atoms=2)
        for asset in keys
    )
    managed = (fixture._managed_policy(asset="ORD"),)
    balances = (
        EconomicAmountV2("dave", "EUR", "accounts", 7),
        EconomicAmountV2("alice", "ORD", "accounts", 100),
        EconomicAmountV2("bob", "ORD", "accounts", 15),
    )
    supplies = tuple(AssetSupplyV2(asset, amount) for asset, amount in zip(keys, (0, 7, 120), strict=True))
    custody = (EconomicAmountV2("vault", "ORD", "escrow", 5),)
    pre = AssetLaneCustodyStateV2(
        AssetTransferStateV2(fixture._root("module-release"), policies, balances, supplies),
        fixture._registry(policies, managed), managed, custody,
    )
    assert set(pre.to_canonical()) == {
        "schema", "transfer_state", "origin_registry", "managed_policies", "custody",
    }
    assert tuple(row.asset for row in pre.origin_registry.assets) == keys
    assert pre.transfer_state.balances == balances
    assert pre.transfer_state.supplies == supplies
    assert pre.managed_policies == managed
    assert pre.custody == custody
    assert (pre.account_atoms("ORD"), pre.physical_atoms("ORD")) == (115, 120)

    transfer = replace(
        fixture._transfer_command(amount_atoms=10),
        asset="ORD", asset_origin_root=fixture._root("origin:ORD"),
    )
    accepted = transition_asset_lane_custody_v2(fixture._context(transfer), pre, transfer)
    assert type(accepted) is AssetLaneCustodyAcceptedV2
    assert tuple((row.owner, row.amount_atoms) for row in accepted.post_state.transfer_state.balances) == (
        ("dave", 7), ("alice", 88), ("bob", 25), ("m_treasury", 2),
    )
    assert accepted.post_state.custody == custody
    assert accepted.post_state.transfer_state.supplies == supplies
    for kind, operation, accounts, supply in (
        (fixture.MANAGED_ASSET_ISSUE_COMMAND_KIND_V2, "issue", 122, 127),
        (fixture.MANAGED_ASSET_BURN_COMMAND_KIND_V2, "burn", 108, 113),
    ):
        command = replace(
            fixture._managed_command(kind=kind, amount_atoms=7), asset="ORD",
            asset_origin_root=fixture._root("origin:ORD"),
            authorization_root=fixture._root(f"{operation}:ORD"),
        )
        context = fixture._context(command, grant_root=command.authorization_root)
        result = transition_asset_lane_custody_v2(context, pre, command)
        assert type(result) is AssetLaneCustodyAcceptedV2
        assert result.post_state.account_atoms("ORD") == accounts
        assert result.post_state.transfer_state.supply_atoms("ORD") == supply
        assert result.post_state.custody == custody
