"""Fresh complete custody encoding and finite-materialization evidence.

This gate tests concrete runtime-admitted values against the Lean encoder.
It does not prove universal Python/Rust codec, constructor or coordinator refinement.
"""
from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
from dataclasses import replace
from pathlib import Path

import pytest

import src.core.asset_lane_custody_coordinator_v2 as coordinator
import src.core.asset_transfer_types_v2 as transfer_types
import src.core.global_settlement_types_v2 as settlement
import tests.core.test_asset_lane_coordinator_v2 as lane_helpers
import tests.core.test_asset_lane_custody_bounds_v2 as bounds
import tests.core.test_asset_lane_custody_v2 as custody_helpers
import tests.formal.test_lean_asset_transfer_finite_outcome_v2 as transfer_lean
import tests.formal.test_lean_managed_asset_finite_outcome_v2 as managed_lean
from src.core.asset_lane_coordinator_values_v2 import AssetLaneCommandV2, AssetLaneRejectedV2
from src.core.asset_lane_custody_codec_v2 import decode_asset_lane_custody_state_v2
from src.core.asset_lane_custody_coordinator_v2 import (
    AssetLaneCustodyAcceptedV2,
    transition_asset_lane_custody_v2,
)
from src.core.asset_lane_custody_input_v2 import _decode_context
from src.core.asset_lane_custody_state_v2 import AssetLaneCustodyStateV2
from src.core.asset_origin_registry_types_v2 import (
    AssetOriginKindV2,
    AssetOriginRecordV2,
    AssetOriginRegistryStateV2,
)
from src.core.asset_transfer_module_v2 import transition_asset_transfer_v2
from src.core.asset_transfer_types_v2 import (
    AssetClassV2,
    AssetTransferAcceptedV2,
    AssetTransferRejectedV2,
)
from src.core.global_settlement_abi_v2_codec import (
    decode_asset_transfer_command_v2,
    decode_managed_asset_lifecycle_command_v2,
)
from src.core.global_settlement_types_v2 import EconomicAmountV2, canonical_global_bytes_v2
from src.core.managed_asset_lifecycle_module_v2 import transition_managed_asset_lifecycle_v2
from src.core.managed_asset_lifecycle_result_v2 import (
    ManagedAssetLifecycleAcceptedV2,
    ManagedAssetLifecycleRejectedV2,
)
from tests.core.test_asset_lane_custody_v2 import custody_state, multiasset_custody_state
from tests.formal.test_lean_asset_lane_custody_effect_plan_v2 import (
    GOLDEN_CASES,
    GOLDEN_FIXTURE,
    GOLDEN_FIXTURE_SHA256,
)
from tests.formal.test_lean_asset_lane_custody_finite_trace_v2 import (
    accounting_lean as accounting_lean,
)
from tests.formal.test_lean_asset_lane_custody_finite_trace_v2 import (
    byte_accounting_lean as byte_accounting_lean,
)
from tests.formal.test_lean_asset_lane_custody_finite_trace_v2 import (
    composition_lean as composition_lean,
)
from tests.formal.test_lean_asset_lane_custody_finite_trace_v2 import (
    custody_effect_plan_lean as custody_effect_plan_lean,
)
from tests.formal.test_lean_asset_lane_custody_finite_trace_v2 import (
    effect_plan_lean as effect_plan_lean,
)
from tests.formal.test_lean_asset_lane_custody_finite_trace_v2 import (
    finite_recomposition_lean as finite_recomposition_lean,
)
from tests.formal.test_lean_asset_lane_custody_finite_trace_v2 import (
    finite_trace_lean as finite_trace_lean,
)
from tests.formal.test_lean_asset_lane_custody_finite_trace_v2 import (
    lean as lean,
)
from tests.formal.test_lean_asset_lane_custody_finite_trace_v2 import (
    outcome_lean as outcome_lean,
)
from tests.formal.test_lean_asset_lane_custody_finite_trace_v2 import (
    row_growth_lean as row_growth_lean,
)
from tests.formal.test_lean_asset_lane_custody_finite_trace_v2 import (
    shared_lean as shared_lean,
)
from tests.formal.test_lean_asset_lane_custody_finite_trace_v2 import (
    transfer_consumer_lean as transfer_consumer_lean,
)
from tests.formal.test_lean_asset_lane_custody_finite_trace_v2 import (
    transfer_effect_plan_lean as transfer_effect_plan_lean,
)
from tests.formal.test_lean_asset_lane_custody_finite_trace_v2 import (
    transfer_outcome_lean as transfer_outcome_lean,
)
from tests.formal.test_lean_asset_lane_custody_structural_v2 import (
    custody_structural_lean as custody_structural_lean,
)
from tests.formal.test_lean_asset_origin_registry_refinement_v2 import (
    CompiledPacket,
    _compile_lean_file,
    _lake_cached,
)
from tests.formal.test_lean_asset_transfer_finite_outcome_v2 import (
    _LEAN_CLASSES,
    _lean_string,
    _wire,
)
from tests.formal.test_lean_asset_transfer_finite_outcome_v2 import _lean_state as _transfer_state
from tests.formal.test_lean_managed_asset_finite_outcome_v2 import _lean_list
from tests.formal.test_lean_managed_asset_finite_outcome_v2 import _lean_policy as _managed_policy
from tests.formal.test_lean_registered_supply_support_v1 import LeanSubject

REPO = Path(__file__).resolve().parents[2]
MODULE = "AssetLaneCustodyCompleteStateV2"
NAMESPACE = f"Proofs.{MODULE}"
SOURCE = REPO / "lean-mathlib/Proofs" / f"{MODULE}.lean"
SOURCE_SHA256 = "f7101c17778fe4bff9ca2481f184b2176307e4366141961ee8ac79fa9c7f1802"
ORIGIN_MODULE = "AssetOriginRegistryRefinementV2"
ORIGIN_SHA256 = "ea4f1c7afc674a2bcafd356d9479bc656e5560ecc2a96748da9fa4ae54e8d80c"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
CONTRACTS = {
    "erase_transfer_source": "∀ (state : FullState), E.transferSource (erase state) = state.transfer",
    "erase_step": """∀ (digest : B.Bytes → String) (pre : FullState) (action : F.Action),
      erase (step digest pre action) = F.step digest (erase pre) action""",
    "step_metadata": """∀ (digest : B.Bytes → String) (pre : FullState) (action : F.Action),
      (step digest pre action).originRegistry = pre.originRegistry ∧
      (step digest pre action).managedPolicies = pre.managedPolicies ∧
      (step digest pre action).custody = pre.custody""",
    "step_transfer_metadata": """∀ (digest : B.Bytes → String) (pre : FullState) (action : F.Action),
      (step digest pre action).transfer.moduleReleaseId = pre.transfer.moduleReleaseId ∧
      (step digest pre action).transfer.policies = pre.transfer.policies""",
    "step_state_bytes_length_relation": """∀ (digest : B.Bytes → String) (pre : FullState)
      (action : F.Action), (stateBytes (step digest pre action)).length +
      (FT.stateBytes pre.transfer).length = (stateBytes pre).length +
      (FT.stateBytes (step digest pre action).transfer).length""",
}


@pytest.fixture(scope="module")
def complete_state_lean(custody_structural_lean: LeanSubject) -> CompiledPacket:
    cache = _lake_cached("env", "printenv", "LEAN_PATH")
    assert cache.returncode == 0, cache.stdout + cache.stderr
    environment = dict(os.environ, LEAN_PATH=os.pathsep.join((str(custody_structural_lean.library), cache.stdout.strip())))
    subject = CompiledPacket(custody_structural_lean.source, custody_structural_lean.executable, environment)
    for name, expected in ((ORIGIN_MODULE, ORIGIN_SHA256), (MODULE, SOURCE_SHA256)):
        data = (REPO / "lean-mathlib/Proofs" / f"{name}.lean").read_bytes()
        assert hashlib.sha256(data).hexdigest() == expected
        target = subject.root / "Proofs" / f"{name}.lean"
        target.write_bytes(data)
        result = subprocess.run(
            [str(subject.lean), "-DwarningAsError=true", "-R", str(subject.root),
             "-o", str(custody_structural_lean.library / "Proofs" / f"{name}.olean"), str(target)],
            cwd=subject.root, env=subject.environment, capture_output=True, text=True, timeout=300, check=False,
        )
        assert result.returncode == 0, result.stdout + result.stderr
        assert result.stdout == result.stderr == ""
    return subject


def _consumer(subject: CompiledPacket, name: str, code: str) -> str:
    path = subject.root / f"{name}.lean"
    path.write_text(f"import {NAMESPACE}\nimport Lean.Data.Json\nopen {NAMESPACE}\n"
                    "set_option warningAsError true\nset_option maxRecDepth 100000\n" + code)
    result = _compile_lean_file(subject, path)
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stderr == ""
    return result.stdout


def test_complete_state_contracts_and_standard_axioms(complete_state_lean: CompiledPacket) -> None:
    source = SOURCE.read_text()
    assert tuple(re.findall(r"^theorem\s+(\w+)", source, re.MULTILINE)) == tuple(CONTRACTS)
    code = re.sub(r"/-.*?-/", "", source, flags=re.DOTALL)
    assert re.search(r"\b(?:sorry|sorryAx|admit|axiom|unsafe|native_decide|implemented_by)\b", code) is None
    text = "\n".join(f"example : {signature} := @{NAMESPACE}.{name}\n#print axioms {NAMESPACE}.{name}"
                     for name, signature in CONTRACTS.items())
    output = _consumer(complete_state_lean, "CompleteStateContracts", text)
    groups = re.findall(r"depends on axioms:\s*\[([^]]*)\]", output)
    assert {a.strip() for g in groups for a in g.split(",") if a.strip()} <= STANDARD_AXIOMS
    assert len(groups) + output.count("does not depend on any axioms") == len(CONTRACTS)


def _origin_record(row: AssetOriginRecordV2) -> str:
    kind = ".native" if row.origin_kind is AssetOriginKindV2.NATIVE else ".tauOriginated"
    fields = (_lean_string(row.asset), kind, _lean_string(row.origin_root),
              _lean_string(row.transfer_policy_root), _lean_string(row.issue_policy_root),
              str(row.decimals), "." + _LEAN_CLASSES[row.asset_class.value])
    return "⟨" + ", ".join(fields) + "⟩"


def _registry_value(registry: AssetOriginRegistryStateV2) -> str:
    policy = registry.policy
    fields = (_lean_string(policy.authority_subject), _lean_string(policy.authority_grant_root),
              str(policy.allow_native).lower(), str(policy.allow_tau_originated).lower())
    encoded_policy = "⟨" + ", ".join(fields) + "⟩"
    return f"⟨{_lean_string(registry.module_release_id)}, {encoded_policy}, " + _lean_list([_origin_record(r) for r in registry.assets]) + "⟩"


def _full_state(state: AssetLaneCustodyStateV2) -> str:
    custody = _lean_list([f"⟨{_lean_string(r.owner)}, {_lean_string(r.asset)}, "
                          f"{_lean_string(r.custody_domain)}, {r.amount_atoms}⟩" for r in state.custody])
    return "⟨" + ", ".join((_transfer_state(_wire(state.transfer_state)), _registry_value(state.origin_registry),
                              _lean_list([_managed_policy(p) for p in state.managed_policies]), custody)) + "⟩"


def _encoding_states() -> list[tuple[str, AssetLaneCustodyStateV2]]:
    assert hashlib.sha256(GOLDEN_FIXTURE.read_bytes()).hexdigest() == GOLDEN_FIXTURE_SHA256
    states = [("base", custody_state()), ("dormant", custody_state(0, 0)),
              ("multiasset", multiasset_custody_state())]
    base = states[0][1]
    escaped = AssetLaneCustodyStateV2(base.transfer_state, base.origin_registry, base.managed_policies,
        (EconomicAmountV2('vault"\\owner', "USD", 'escrow"\\domain', 20),))
    policy = replace(base.origin_registry.policy, authority_subject='registrar"\\subject', allow_native=True,
                     allow_tau_originated=False)
    registry = replace(base.origin_registry, policy=policy)
    changed_metadata = AssetLaneCustodyStateV2(base.transfer_state, registry, base.managed_policies, base.custody)
    states.extend((("escaped-custody", escaped), ("changed-registry-policy", changed_metadata)))
    empty = AssetLaneCustodyStateV2(
        transfer_types.AssetTransferStateV2(base.transfer_state.module_release_id, (), (), ()),
        replace(base.origin_registry, assets=()), (), (),
    )
    native_policy = replace(base.transfer_state.policies[0], asset="TAU", asset_class=AssetClassV2.TAU_NATIVE_COIN)
    native_row = replace(base.origin_registry.assets[0], asset="TAU",
        origin_kind=AssetOriginKindV2.NATIVE, asset_class=AssetClassV2.TAU_NATIVE_COIN,
        issue_policy_root=settlement.ZERO_ROOT_V2,
        transfer_policy_root=lane_helpers.asset_transfer_policy_root_v2(native_policy))
    native_state = AssetLaneCustodyStateV2(
        transfer_types.AssetTransferStateV2(base.transfer_state.module_release_id,
            (native_policy,), (), (settlement.AssetSupplyV2("TAU", 0),)),
        replace(base.origin_registry, assets=(native_row,)), (), ())
    null_transfer = replace(base.transfer_state.policies[0], asset_origin_root=None, enabled=False)
    null_managed = replace(base.managed_policies[0], asset_origin_root=None,
        issue_authority_subject=None, issue_authorization_root=None, burn_authorization_root=None, enabled=False)
    null_transfer_state = transfer_types.AssetTransferStateV2(base.transfer_state.module_release_id,
        (null_transfer,), base.transfer_state.balances, base.transfer_state.supplies)
    null_state = AssetLaneCustodyStateV2(null_transfer_state,
        lane_helpers._registry((null_transfer,), (null_managed,)), (null_managed,), base.custody)
    states.extend((("empty", empty), ("native-origin", native_state), ("null-policy-fields", null_state)))
    for case in GOLDEN_CASES:
        pre = decode_asset_lane_custody_state_v2(canonical_global_bytes_v2(case["pre_state"]))
        states.append((case["name"] + "-pre", pre))
    return states


def test_actual_full_canonical_bytes_and_runtime_enum_codes(complete_state_lean: CompiledPacket) -> None:
    states = _encoding_states()
    body = []
    for i, (name, state) in enumerate(states):
        expected = canonical_global_bytes_v2(state.to_canonical()).decode("ascii")
        body.append(f"def s{i} : FullState := {_full_state(state)}")
        body.append(f'#eval IO.println ((Lean.Json.mkObj [("name", Lean.toJson {_lean_string(name)}), '
                    f'("equal", Lean.toJson (stateBytes s{i} == B.raw {_lean_string(expected)})), '
                    f'("bytes", Lean.toJson (stateBytes s{i}).length), '
                    f'("resources", Lean.toJson (decide (Resources s{i}))) ]).compress)')
    output = _consumer(complete_state_lean, "CompleteStateBytes", "\n".join(body))
    observed = [json.loads(line) for line in output.splitlines()]
    assert observed == [{"name": name, "equal": True,
                         "bytes": len(canonical_global_bytes_v2(state.to_canonical())), "resources": True}
                        for name, state in states]
    enums = '#eval IO.println ((Lean.toJson (([.native, .tauOriginated] : List O.OriginKind).map originKindCode)).compress)\n'
    enums += '#eval IO.println ((Lean.toJson (([.tauNativeCoin, .canonicalZusd, .lpShare, .zdexProtocolToken, '
    enums += '.sealedBidPaymentOrInventory, .registeredOrdinaryToken] : List O.AssetClass).map assetClassCode)).compress)'
    observed_enums = [json.loads(line) for line in _consumer(complete_state_lean, "CompleteStateEnums", enums).splitlines()]
    assert observed_enums == [[e.value for e in AssetOriginKindV2], [e.value for e in AssetClassV2]]


LIMIT = 1_048_576


def _boundary_case(last_domain_bytes: int):
    base = custody_helpers.custody_state()
    policies = (lane_helpers._transfer_policy(asset="EUR"), *base.transfer_state.policies)
    registry = lane_helpers._registry(policies, base.managed_policies)
    custody = tuple(
        settlement.EconomicAmountV2(
            (prefix := f"v{index:04d}") + "x" * (settlement.MAX_TOKEN_BYTES_V2 - len(prefix)),
            "EUR",
            "e" * (settlement.MAX_TOKEN_BYTES_V2 if index < 2_723 else last_domain_bytes),
            1,
        )
        for index in range(2_724)
    )
    transfer = transfer_types.AssetTransferStateV2(
        base.transfer_state.module_release_id,
        policies,
        base.transfer_state.balances,
        (settlement.AssetSupplyV2("EUR", 2_724), *base.transfer_state.supplies),
    )
    state = coordinator.AssetLaneCustodyStateV2(
        transfer, registry, base.managed_policies, (*custody, *base.custody)
    )
    command = lane_helpers._managed_command(
        owner="i" * settlement.MAX_TOKEN_BYTES_V2, amount_atoms=1
    )
    context = lane_helpers._context(command)
    leaf = coordinator.transition_managed_asset_lifecycle_v2(
        context.managed_context(), state.managed_leaf_state(), command
    )
    assert type(leaf) is coordinator.ManagedAssetLifecycleAcceptedV2
    expected = transfer_types.AssetTransferStateV2(
        transfer.module_release_id,
        transfer.policies,
        leaf.post_state.balances,
        (transfer.supplies[0], *leaf.post_state.supplies),
    )
    return state, context, command, expected


def _managed_context(context) -> str:
    occurrence = context.occurrence
    assert occurrence is not None
    consumed = managed_lean._lean_list(
        [transfer_lean._lean_string(item) for item in occurrence.consumed_object_ids]
    )
    occurrence_value = (
        "some ⟨"
        + ", ".join(
            (
                transfer_lean._lean_string(occurrence.pre_state_root),
                consumed,
                transfer_lean._lean_string(occurrence.command_kind),
                transfer_lean._lean_string(occurrence.command_body_hash),
                transfer_lean._lean_string(occurrence.subject_id),
                transfer_lean._lean_string(occurrence.grant_root),
                transfer_lean._lean_string(occurrence.occurrence_id),
            )
        )
        + "⟩"
    )
    return (
        f"⟨{transfer_lean._lean_string(context.module_release_id)}, "
        f"{transfer_lean._lean_string(context.global_pre_state_root)}, {occurrence_value}⟩"
    )


def _lean_boundary_source(
    state, context, command, expected: transfer_types.AssetTransferStateV2
) -> str:
    base_custody = state.custody[-1]
    row = (
        f"⟨{transfer_lean._lean_string(base_custody.owner)}, "
        f"{transfer_lean._lean_string(base_custody.asset)}, "
        f"{transfer_lean._lean_string(base_custody.custody_domain)}, "
        f"{base_custody.amount_atoms}⟩"
    )
    expected_bytes = settlement.canonical_global_bytes_v2(expected).decode("ascii")
    return f"""
def repeatChar (n : Nat) (c : Char) : String := String.ofList (List.replicate n c)
def paddedIndex (n : Nat) : String :=
  let digits := toString n
  repeatChar (4 - digits.length) '0' ++ digits
def boundaryOwner (n : Nat) : String :=
  let baseText := "v" ++ paddedIndex n
  baseText ++ repeatChar (160 - baseText.length) 'x'
def boundaryCustody (last : Nat) : List Proofs.GlobalEconomicStateRefinementV2.AmountRow :=
  (List.range 2724).map (fun n =>
    ⟨boundaryOwner n, "EUR", repeatChar (if n < 2723 then 160 else last) 'e', 1⟩) ++ [{row}]
def boundaryTransfer : FT.State := {transfer_lean._lean_state(transfer_lean._wire(state.transfer_state))}
def boundaryRegistry : O.State := {_registry_value(state.origin_registry)}
def boundaryPolicies : List M.Policy := {managed_lean._lean_list([managed_lean._lean_policy(p) for p in state.managed_policies])}
def boundaryPre (last : Nat) : FullState :=
  ⟨boundaryTransfer, boundaryRegistry, boundaryPolicies, boundaryCustody last⟩
def boundaryContext : Proofs.ManagedAssetLifecycleRefinementV2.Context := {_managed_context(context)}
def boundaryCommand : Proofs.ManagedAssetLifecycleRefinementV2.Command := {managed_lean._lean_command(command)}
def boundaryDigest (bytes : B.Bytes) : String := toString bytes.length
def boundaryAction : F.Action := .managed boundaryContext boundaryCommand
def boundaryPost (last : Nat) : FullState := step boundaryDigest (boundaryPre last) boundaryAction
def expectedTransferBytes : B.Bytes := B.raw {transfer_lean._lean_string(expected_bytes)}
def leafAccepted (last : Nat) : Bool := decide
  ((Proofs.ManagedAssetFiniteOutcomeV2.transition boundaryDigest boundaryContext
    (Proofs.AssetLaneCustodyEffectPlanV2.managedSource (erase (boundaryPre last)))
    boundaryCommand).verdict = Proofs.ManagedAssetFiniteOutcomeV2.Verdict.accepted)
def observations (last : Nat) : List Bool :=
  [leafAccepted last, decide (Resources (boundaryPre last)),
   decide ((boundaryPost last).originRegistry = (boundaryPre last).originRegistry ∧
     (boundaryPost last).managedPolicies = (boundaryPre last).managedPolicies ∧
     (boundaryPost last).custody = (boundaryPre last).custody),
   decide (FT.stateBytes (boundaryPost last).transfer = expectedTransferBytes),
   decide (Resources (boundaryPost last))]
def emit (last : Nat) : IO Unit := IO.println ((Lean.toJson
  (last, observations last, [(stateBytes (boundaryPre last)).length,
    (stateBytes (boundaryPost last)).length])).compress)
#eval emit 53
#eval emit 54
"""


def test_exact_complete_state_resource_boundary(
    complete_state_lean: CompiledPacket,
) -> None:
    """Compare exact full lengths; the 1 MiB cross-codec byte string is not embedded."""

    cases = {last: _boundary_case(last) for last in (53, 54)}
    state, context, command, expected = cases[53]
    output = _consumer(
        complete_state_lean,
        "CompleteStateResourceBoundary",
        _lean_boundary_source(state, context, command, expected),
    )
    assert [json.loads(line) for line in output.splitlines()] == [
        [53, [[True, True, True, True, True], [LIMIT - 232, LIMIT]]],
        [54, [[True, True, True, True, False], [LIMIT - 231, LIMIT + 1]]],
    ]
    for last, (pre, runtime_context, runtime_command, expected_post) in cases.items():
        original = settlement.canonical_global_bytes_v2(pre.to_canonical())
        expected_bytes = settlement.canonical_global_bytes_v2(
            pre.to_canonical() | {"transfer_state": expected_post}
        )
        assert len(original) == LIMIT - (232 if last == 53 else 231)
        assert len(expected_bytes) == LIMIT + (0 if last == 53 else 1)
        result = coordinator.transition_asset_lane_custody_v2(runtime_context, pre, runtime_command)
        if last == 53:
            assert type(result) is coordinator.AssetLaneCustodyAcceptedV2
            assert result.post_state.transfer_state == expected_post
            assert result.post_state.to_canonical() == (
                pre.to_canonical() | {"transfer_state": expected_post}
            )
            assert (
                len(settlement.canonical_global_bytes_v2(result.post_state.to_canonical())) == LIMIT
            )
        else:
            bounds._assert_exact_coordinator_noop(
                result, pre, coordinator.AssetLaneCoordinatorRejectCodeV2.STATE_RESOURCE_LIMIT
            )
        assert settlement.canonical_global_bytes_v2(pre.to_canonical()) == original


def _runtime_case(case):
    context = _decode_context(canonical_global_bytes_v2(case["context"]))
    pre = decode_asset_lane_custody_state_v2(canonical_global_bytes_v2(case["pre_state"]))
    command_raw = canonical_global_bytes_v2(case["command"])
    command: AssetLaneCommandV2
    leaf: AssetTransferAcceptedV2 | AssetTransferRejectedV2 | ManagedAssetLifecycleAcceptedV2 | ManagedAssetLifecycleRejectedV2
    if case["command_type"] == "TRANSFER":
        command = decode_asset_transfer_command_v2(command_raw)
        leaf = transition_asset_transfer_v2(context.transfer_context(), pre.transfer_state, command)
    else:
        command = decode_managed_asset_lifecycle_command_v2(command_raw)
        leaf = transition_managed_asset_lifecycle_v2(
            context.managed_context(), pre.managed_leaf_state(), command
        )
    complete = transition_asset_lane_custody_v2(context, pre, command)
    output = case["output"]
    assert complete.route.value == output["route"]
    if output["status"] == "ACCEPTED":
        assert type(complete) is AssetLaneCustodyAcceptedV2
        assert type(leaf) is AssetTransferAcceptedV2 or type(leaf) is ManagedAssetLifecycleAcceptedV2
        expected = decode_asset_lane_custody_state_v2(
            canonical_global_bytes_v2(output["post_state"])
        )
        assert complete.post_state == expected
        projected = expected.transfer_state if case["command_type"] == "TRANSFER" else expected.managed_leaf_state()
        assert leaf.post_state == projected
        expected_leaf = True
    else:
        assert type(complete) is AssetLaneRejectedV2
        assert type(leaf) is AssetTransferRejectedV2 or type(leaf) is ManagedAssetLifecycleRejectedV2
        assert leaf.code.value == output["code"]
        assert complete.code.value == output["code"]
        assert complete.effects.is_empty
        assert complete.pre_state_root == complete.post_state_root == pre.state_root
        leaf_pre_root = pre.transfer_state.state_root if case["command_type"] == "TRANSFER" else pre.managed_leaf_state().state_root
        assert leaf.pre_state_root == leaf.post_state_root == leaf_pre_root
        expected = pre
        expected_leaf = False
    return context, pre, command, expected, expected_leaf


def _lean_case(index: int, case, context, pre, command, expected) -> str:
    transfer = case["command_type"] == "TRANSFER"
    if transfer:
        context_expr = transfer_lean._lean_context(context.transfer_context())
        command_expr = transfer_lean._lean_command(command)
        context_type = "Proofs.AssetTransferRefinementV2.Context"
        command_type = "Proofs.AssetTransferRefinementV2.Command"
        leaf_transition = (
            "Proofs.AssetTransferFiniteOutcomeV2.transition digest context{0} "
            "(Proofs.AssetLaneCustodyEffectPlanV2.transferSource (erase pre{0})) command{0}"
        ).format(index)
        verdict = "Proofs.AssetTransferFiniteOutcomeV2.Verdict.accepted"
    else:
        context_expr = _managed_context(context)
        command_expr = managed_lean._lean_command(command)
        context_type = "Proofs.ManagedAssetLifecycleRefinementV2.Context"
        command_type = "Proofs.ManagedAssetLifecycleRefinementV2.Command"
        leaf_transition = (
            "Proofs.ManagedAssetFiniteOutcomeV2.transition digest context{0} "
            "(Proofs.AssetLaneCustodyEffectPlanV2.managedSource (erase pre{0})) command{0}"
        ).format(index)
        verdict = "Proofs.ManagedAssetFiniteOutcomeV2.Verdict.accepted"
    expected_bytes = canonical_global_bytes_v2(expected.to_canonical()).decode("ascii")
    return "\n".join(
        (
            f"def pre{index} : FullState := {_full_state(pre)}",
            f"def context{index} : {context_type} := {context_expr}",
            f"def command{index} : {command_type} := {command_expr}",
            f"def action{index} : F.Action := .{'transfer' if transfer else 'managed'} context{index} command{index}",
            f"def expected{index} : B.Bytes := B.raw {transfer_lean._lean_string(expected_bytes)}",
            f"def leafAccepted{index} : Bool := decide (({leaf_transition}).verdict = {verdict})",
            f"def stepEqual{index} : Bool := decide (stateBytes (step digest pre{index} action{index}) = expected{index})",
            f"def stepNoop{index} : Bool := decide (stateBytes (step digest pre{index} action{index}) = stateBytes pre{index})",
            f'#eval IO.println ((Lean.Json.mkObj [("name", Lean.toJson {transfer_lean._lean_string(case["name"])}), '
            f'("leaf_accepted", Lean.toJson (leafAccepted{index})), ("step_equal", Lean.toJson (stepEqual{index})), '
            f'("step_noop", Lean.toJson (stepNoop{index})), ("bytes", Lean.toJson (stateBytes (step digest pre{index} action{index})).length)]).compress)',
        )
    )


def test_runtime_goldens_then_complete_state_step_bytes(
    complete_state_lean: CompiledPacket,
) -> None:
    """Replay all ten goldens before checking the actual Lean step bytes."""

    assert hashlib.sha256(GOLDEN_FIXTURE.read_bytes()).hexdigest() == GOLDEN_FIXTURE_SHA256
    assert len(GOLDEN_CASES) == 10
    assert sum(case["output"]["status"] == "ACCEPTED" for case in GOLDEN_CASES) == 7

    body = ["def digest (bytes : B.Bytes) : String := toString bytes.length"]
    expected_observations = []
    for index, case in enumerate(GOLDEN_CASES):
        context, pre, command, expected, leaf_expected = _runtime_case(case)
        body.append(_lean_case(index, case, context, pre, command, expected))
        expected_observations.append(
            {
                "name": case["name"],
                "leaf_accepted": leaf_expected,
                "step_equal": True,
                "step_noop": not leaf_expected,
                "bytes": len(canonical_global_bytes_v2(expected.to_canonical())),
            }
        )

    output = _consumer(
        complete_state_lean,
        "CompleteStateStepGoldenAppendix",
        "\n".join(body),
    )
    assert [json.loads(line) for line in output.splitlines()] == expected_observations
