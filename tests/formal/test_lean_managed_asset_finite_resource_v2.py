"""Finite managed-leaf resource neighbors evaluated by the Lean model.

The boundary states use the same compact row recipe as the independent
runtime fixture. Lean computes each candidate, its resource predicate, and the
transition result; no POST state or resource decision is supplied to Lean.
"""

from __future__ import annotations

import json
from dataclasses import dataclass

from src.core.global_settlement_types_v2 import (
    AssetSupplyV2,
    EconomicAmountV2,
    canonical_global_bytes_v2,
)
from src.core.managed_asset_lifecycle_module_v2 import transition_managed_asset_lifecycle_v2
from src.core.managed_asset_lifecycle_result_v2 import (
    ManagedAssetLifecycleAcceptedV2,
    ManagedAssetLifecycleRejectCodeV2,
)
from src.core.managed_asset_lifecycle_types_v2 import ManagedAssetLifecycleStateV2
from tests.core import test_asset_lane_coordinator_v2 as fixture
from tests.core import test_managed_asset_leaf_byte_boundary_v2 as leaf
from tests.formal.test_lean_managed_asset_finite_outcome_v2 import (
    _consumer as outcome_consumer,
)
from tests.formal.test_lean_managed_asset_finite_outcome_v2 import (
    _lean_policy as outcome_lean_policy,
)
from tests.formal.test_lean_managed_asset_finite_outcome_v2 import (
    _lean_string as outcome_lean_string,
)
from tests.formal.test_lean_managed_asset_finite_outcome_v2 import (
    accounting_lean as accounting_lean,
)
from tests.formal.test_lean_managed_asset_finite_outcome_v2 import (
    byte_accounting_lean as byte_accounting_lean,
)
from tests.formal.test_lean_managed_asset_finite_outcome_v2 import (
    composition_lean as composition_lean,
)
from tests.formal.test_lean_managed_asset_finite_outcome_v2 import (
    finite_recomposition_lean as finite_recomposition_lean,
)
from tests.formal.test_lean_managed_asset_finite_outcome_v2 import (
    lean as lean,
)
from tests.formal.test_lean_managed_asset_finite_outcome_v2 import (
    outcome_lean as outcome_lean,
)
from tests.formal.test_lean_managed_asset_finite_outcome_v2 import (
    row_growth_lean as row_growth_lean,
)
from tests.formal.test_lean_managed_asset_finite_outcome_v2 import (
    shared_lean as shared_lean,
)
from tests.formal.test_lean_registered_supply_support_v1 import LeanSubject

BYTE_CAP = 1_048_576


def _candidate_wire_bytes(
    state: ManagedAssetLifecycleStateV2,
    *,
    owner: str | None = None,
    new_owner: str | None = None,
) -> bytes:
    wire = json.loads(canonical_global_bytes_v2(state))
    if owner is not None:
        for row in wire["balances"]:
            if row["owner"] == owner and row["asset"] == "USD":
                row["amount_atoms"] = 10
                break
        else:
            raise AssertionError("boundary owner absent from pre-state")
        for row in wire["supplies"]:
            if row["asset"] == "USD":
                row["amount_atoms"] = 99_999
                break
    elif new_owner is not None:
        wire["balances"].append(
            {
                "amount_atoms": 1,
                "asset": "USD",
                "custody_domain": "accounts",
                "owner": new_owner,
            }
        )
        wire["balances"].sort(key=lambda row: (row["asset"], row["owner"], row["custody_domain"]))
        for row in wire["supplies"]:
            if row["asset"] == "USD":
                row["amount_atoms"] += 1
                break
        else:
            raise AssertionError("dormant USD supply absent from pre-state")
    else:
        raise AssertionError("candidate update selector is required")
    return json.dumps(wire, sort_keys=True, separators=(",", ":")).encode("ascii")


@dataclass(frozen=True)
class ExpectedCase:
    name: str
    pre: ManagedAssetLifecycleStateV2
    command: object
    context: object
    fields: tuple[str, ...]


def _assert_boundary_rows_match(pre: ManagedAssetLifecycleStateV2) -> None:
    """Check the compact Lean recipe against every runtime source row."""
    assert len(pre.balances) == 4095
    quote_total = sum(row.owner.count('"') for row in pre.balances)
    for index, row in enumerate(pre.balances):
        quote_count = min(155, max(0, quote_total - 155 * index))
        expected_owner = f"o{index:04d}" + '"' * quote_count + "a" * (155 - quote_count)
        assert row.owner == expected_owner
        assert (row.asset, row.custody_domain, row.amount_atoms) == ("USD", "accounts", 9)


def _assert_dormant_rows_match(state: ManagedAssetLifecycleStateV2) -> None:
    """Check the compact 4096-row Lean recipe against every runtime row."""
    assert tuple(state.balances) == tuple(
        EconomicAmountV2(f"o{index:04d}", "USD", "accounts", 1) for index in range(4096)
    )


def _expected_fields(
    *,
    verdict: str,
    resource: str,
    pre_bytes: int,
    candidate_bytes: int,
    post_bytes: int,
    pre_rows: int,
    candidate_rows: int,
    post_rows: int,
    pre_supply_rows: int,
    candidate_supply_rows: int,
    post_supply_rows: int,
    pre_supply: int,
    candidate_supply: int,
    post_supply: int,
    pre_balance: int,
    candidate_balance: int,
    post_balance: int,
    post_same: bool,
    post_candidate: bool,
    effects_empty: bool,
    lane_writes: int,
    occurrence_consumptions: int,
) -> tuple[str, ...]:
    return tuple(
        str(value).lower() if isinstance(value, bool) else str(value)
        for value in (
            verdict,
            "ECONOMIC_OK",
            resource,
            pre_bytes,
            candidate_bytes,
            post_bytes,
            pre_rows,
            candidate_rows,
            post_rows,
            pre_supply_rows,
            candidate_supply_rows,
            post_supply_rows,
            pre_supply,
            candidate_supply,
            post_supply,
            pre_balance,
            candidate_balance,
            post_balance,
            post_same,
            post_candidate,
            effects_empty,
            lane_writes,
            occurrence_consumptions,
        )
    )


def _boundary_expected() -> tuple[ExpectedCase, ...]:
    cases: list[ExpectedCase] = []
    for headroom in (0, 1):
        pre = leaf._leaf_at_byte_headroom(headroom)
        _assert_boundary_rows_match(pre)
        owner = pre.balances[0].owner
        command = fixture._managed_command(owner=owner, amount_atoms=1)
        context = fixture._context(command).managed_context()
        before = canonical_global_bytes_v2(pre)
        candidate = _candidate_wire_bytes(pre, owner=owner)
        candidate_wire = json.loads(candidate)
        assert (
            next(row["amount_atoms"] for row in candidate_wire["supplies"] if row["asset"] == "USD")
            == 99_999
        )
        runtime = transition_managed_asset_lifecycle_v2(context, pre, command)
        verdict = "ACCEPTED" if headroom else "STATE_RESOURCE_LIMIT"
        assert (isinstance(runtime, ManagedAssetLifecycleAcceptedV2)) is bool(headroom)
        post = runtime.post_state if headroom else pre
        assert len(before) == BYTE_CAP - headroom
        assert len(candidate) == BYTE_CAP + 1 - headroom
        assert len(post.balances) == len(pre.balances) == 4095
        assert canonical_global_bytes_v2(post) == (candidate if headroom else before)
        cases.append(
            ExpectedCase(
                f"byte-headroom-{headroom}",
                pre,
                command,
                context,
                _expected_fields(
                    verdict=verdict,
                    resource="RESOURCE_OK" if headroom else "RESOURCE_REJECT",
                    pre_bytes=len(before),
                    candidate_bytes=len(candidate),
                    post_bytes=len(candidate if headroom else before),
                    pre_rows=4095,
                    candidate_rows=4095,
                    post_rows=4095,
                    pre_supply_rows=2,
                    candidate_supply_rows=2,
                    post_supply_rows=2,
                    pre_supply=99_998,
                    candidate_supply=99_999,
                    post_supply=99_999 if headroom else 99_998,
                    pre_balance=9 * 4095,
                    candidate_balance=9 * 4095 + 1,
                    post_balance=9 * 4095 + headroom,
                    post_same=not headroom,
                    post_candidate=bool(headroom),
                    effects_empty=not headroom,
                    lane_writes=headroom,
                    occurrence_consumptions=headroom,
                ),
            )
        )
    assert cases[0].command == cases[1].command
    assert cases[0].context == cases[1].context
    return tuple(cases)


def _dormant_expected() -> ExpectedCase:
    state = ManagedAssetLifecycleStateV2(
        fixture._root("module-release"),
        (fixture._managed_policy(),),
        tuple(EconomicAmountV2(f"o{index:04d}", "USD", "accounts", 1) for index in range(4096)),
        (AssetSupplyV2("USD", 4096),),
    )
    command = fixture._managed_command(owner="new-owner", amount_atoms=1)
    context = fixture._context(command).managed_context()
    before = canonical_global_bytes_v2(state)
    candidate = _candidate_wire_bytes(state, new_owner="new-owner")
    candidate_wire = json.loads(candidate)
    assert (
        next(row["amount_atoms"] for row in candidate_wire["supplies"] if row["asset"] == "USD")
        == 4_097
    )
    runtime = transition_managed_asset_lifecycle_v2(context, state, command)
    assert runtime.code is ManagedAssetLifecycleRejectCodeV2.STATE_RESOURCE_LIMIT
    assert runtime.effects.is_empty
    assert runtime.pre_state_root == runtime.post_state_root == state.state_root
    assert len(before) == 316_016
    assert len(candidate) > len(before)
    _assert_dormant_rows_match(state)
    return ExpectedCase(
        "dormant-row-cap-4096",
        state,
        command,
        context,
        _expected_fields(
            verdict="STATE_RESOURCE_LIMIT",
            resource="RESOURCE_REJECT",
            pre_bytes=len(before),
            candidate_bytes=len(candidate),
            post_bytes=len(before),
            pre_rows=4096,
            candidate_rows=4097,
            post_rows=4096,
            pre_supply_rows=1,
            candidate_supply_rows=1,
            post_supply_rows=1,
            pre_supply=4096,
            candidate_supply=4097,
            post_supply=4096,
            pre_balance=4096,
            candidate_balance=4097,
            post_balance=4096,
            post_same=True,
            post_candidate=False,
            effects_empty=True,
            lane_writes=0,
            occurrence_consumptions=0,
        ),
    )


def _lean_context(context: object) -> str:
    occurrence = context.occurrence
    if occurrence is None:
        occurrence_literal = "none"
    else:
        consumed = ", ".join(outcome_lean_string(item) for item in occurrence.consumed_object_ids)
        occurrence_literal = (
            "some ⟨"
            + ", ".join(
                (
                    outcome_lean_string(occurrence.pre_state_root),
                    f"[{consumed}]",
                    outcome_lean_string(occurrence.command_kind),
                    outcome_lean_string(occurrence.command_body_hash),
                    outcome_lean_string(occurrence.subject_id),
                    outcome_lean_string(occurrence.grant_root),
                    outcome_lean_string(occurrence.occurrence_id),
                )
            )
            + "⟩"
        )
    return (
        "⟨"
        + ", ".join(
            (
                outcome_lean_string(context.module_release_id),
                outcome_lean_string(context.global_pre_state_root),
                occurrence_literal,
            )
        )
        + "⟩"
    )


def _lean_body(cases: tuple[ExpectedCase, ...]) -> str:
    usd = fixture._managed_policy()
    zzz = fixture._managed_policy(asset="ZZZ")
    boundary_command = cases[0].command
    dormant_command = cases[-1].command
    boundary_context = cases[0].context
    dormant_context = cases[-1].context
    boundary_occurrence = boundary_context.occurrence
    dormant_occurrence = dormant_context.occurrence
    assert boundary_occurrence is not None
    assert dormant_occurrence is not None
    return f"""set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def digitPadding (n : Nat) : String :=
  String.ofList (List.replicate (4 - (toString n).length) '0') ++ toString n
def baseOwner (index : Nat) : String :=
  "o" ++ digitPadding index ++ String.ofList (List.replicate 155 'a')
def quoteOwner (extra index : Nat) : String :=
  let quotes := min 155 (extra - 155 * index)
  "o" ++ digitPadding index ++ String.ofList
    (List.replicate quotes '"' ++ List.replicate (155 - quotes) 'a')
def baseRows : List AmountRow :=
  (List.range 4095).map (fun index => ⟨baseOwner index, "USD", "accounts", 9⟩)
def release : String := {outcome_lean_string(fixture._root("module-release"))}
def usdPolicy : M.Policy := {outcome_lean_policy(usd)}
def zzzPolicy : M.Policy := {outcome_lean_policy(zzz)}
def baseState : State :=
  ⟨release, [usdPolicy, zzzPolicy], baseRows, [⟨"USD", 99998⟩, ⟨"ZZZ", 0⟩]⟩
def byteExtra (headroom : Nat) : Nat :=
  1048576 - headroom - (stateBytes baseState).length
def boundaryRows (headroom : Nat) : List AmountRow :=
  (List.range 4095).map (fun index =>
    ⟨quoteOwner (byteExtra headroom) index, "USD", "accounts", 9⟩)
def boundaryState (headroom : Nat) : State :=
  {{baseState with balances := boundaryRows headroom}}
def issueCommand (headroom : Nat) : M.Command :=
  ⟨"managed_asset_issue", {outcome_lean_string(boundary_command.command_body_hash)}, "USD",
    .registeredOrdinaryToken, some {outcome_lean_string(usd.asset_origin_root)}, 8,
    some {outcome_lean_string(usd.issue_authorization_root)},
    quoteOwner (byteExtra headroom) 0, 1⟩
def issueContext : M.Context :=
  {_lean_context(boundary_context)}
def dormantRows : List AmountRow :=
  (List.range 4096).map (fun index => ⟨"o" ++ digitPadding index, "USD", "accounts", 1⟩)
def dormantState : State :=
  ⟨release, [usdPolicy], dormantRows, [⟨"USD", 4096⟩]⟩
def dormantCommand : M.Command :=
  ⟨"managed_asset_issue", {outcome_lean_string(dormant_command.command_body_hash)}, "USD",
    .registeredOrdinaryToken, some {outcome_lean_string(usd.asset_origin_root)}, 8,
    some {outcome_lean_string(usd.issue_authorization_root)}, "new-owner", 1⟩
def dormantContext : M.Context :=
  {_lean_context(dormant_context)}
def digest (_ : B.Bytes) : M.Root := "same"
def verdictName : Verdict → String
  | .accepted => "ACCEPTED"
  | .rejected code => ManagedAssetFiniteOutcomeV2.RejectCode.code code
def economicName (ctx : M.Context) (state : State) (command : M.Command) : String :=
  match economicRejectCode ctx state command with
  | none => "ECONOMIC_OK"
  | some code => ManagedAssetLifecycleRefinementV2.RejectCode.code code
def boolName (value : Bool) : String := if value then "true" else "false"
def emit (name : String) (pre : State) (ctx : M.Context) (command : M.Command) : IO Unit := do
  let candidate := Proofs.ManagedAssetFiniteOutcomeV2.candidate pre command
  let result := transition digest ctx pre command
  let resource := if Resources candidate then "RESOURCE_OK" else "RESOURCE_REJECT"
  IO.println (String.intercalate "|" [
    "CASE", name, verdictName result.verdict, economicName ctx pre command, resource,
    toString (stateBytes pre).length, toString (stateBytes candidate).length,
    toString (stateBytes result.post).length,
    toString pre.balances.length, toString candidate.balances.length,
    toString result.post.balances.length,
    toString pre.supplies.length, toString candidate.supplies.length,
    toString result.post.supplies.length,
    toString (supplyFor (numericRows pre.supplies) "USD"),
    toString (supplyFor (numericRows candidate.supplies) "USD"),
    toString (supplyFor (numericRows result.post.supplies) "USD"),
    toString (amountForAsset pre.balances "USD"),
    toString (amountForAsset candidate.balances "USD"),
    toString (amountForAsset result.post.balances "USD"),
    boolName (result.post == pre), boolName (result.post == candidate),
    boolName (result.effects == AssetTransferRefinementV2.EffectEnvelope.empty),
    toString result.effects.laneWrites.length,
    toString result.effects.occurrenceConsumptions.length])
def runAll : IO Unit := do
  emit "byte-headroom-0" (boundaryState 0) issueContext (issueCommand 0)
  emit "byte-headroom-1" (boundaryState 1) issueContext (issueCommand 1)
  emit "dormant-row-cap-4096" dormantState dormantContext dormantCommand
#eval runAll
"""


def _parse_report(output: str) -> dict[str, tuple[str, ...]]:
    records: dict[str, tuple[str, ...]] = {}
    for line in output.splitlines():
        if not line.strip():
            continue
        fields = tuple(line.split("|"))
        assert fields[0] == "CASE" and len(fields) == 25, line
        assert fields[1] not in records
        records[fields[1]] = fields[2:]
    return records


def test_actual_leaf_resource_neighbors_are_computed_in_lean(
    outcome_lean: LeanSubject,
) -> None:
    cases = _boundary_expected() + (_dormant_expected(),)
    result = outcome_consumer(
        outcome_lean,
        "ManagedFiniteResourceBoundaries",
        _lean_body(cases),
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stderr == ""
    observed = _parse_report(result.stdout)
    assert tuple(observed) == tuple(case.name for case in cases)
    assert all(observed[case.name] == case.fields for case in cases)


def test_python_issue_candidate_updates_balance_and_supply() -> None:
    state = ManagedAssetLifecycleStateV2(
        fixture._root("module-release"),
        (fixture._managed_policy(),),
        (EconomicAmountV2("alice", "USD", "accounts", 1),),
        (AssetSupplyV2("USD", 1),),
    )
    wire = json.loads(_candidate_wire_bytes(state, new_owner="bob"))
    assert next(row["amount_atoms"] for row in wire["balances"] if row["owner"] == "bob") == 1
    assert next(row["amount_atoms"] for row in wire["supplies"] if row["asset"] == "USD") == 2
    assert len(str(1)) == len(str(2))
