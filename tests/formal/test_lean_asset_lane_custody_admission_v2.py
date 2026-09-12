"""Fresh constructor-admission and bounded runtime-state evidence.

Root/namespace and commitment functions remain explicit proof parameters. These
controls establish no universal Python/Rust parser, hash, receipt or publication
refinement. Runtime controls use the existing state serializer and leaf fixtures.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
from pathlib import Path

import pytest

from src.core.asset_lane_custody_coordinator_v2 import (
    AssetLaneCustodyAcceptedV2,
    transition_asset_lane_custody_v2,
)
from src.core.asset_lane_custody_state_v2 import AssetLaneCustodyStateV2
from src.core.asset_origin_registry_v2 import (
    asset_transfer_policy_root_v2,
    managed_asset_policy_root_v2,
)
from src.core.asset_transfer_types_v2 import AssetTransferCommandV2
from src.core.managed_asset_lifecycle_types_v2 import ManagedAssetLifecycleCommandV2
from tests.core.test_asset_lane_coordinator_v2 import (
    _context,
    _managed_command,
    _root,
    _transfer_command,
)
from tests.core.test_asset_lane_custody_v2 import custody_state, multiasset_custody_state
from tests.formal.test_lean_asset_lane_custody_complete_state_v2 import (
    _full_state,
    _managed_context,
)
from tests.formal.test_lean_asset_lane_custody_complete_state_v2 import (
    accounting_lean as accounting_lean,
)
from tests.formal.test_lean_asset_lane_custody_complete_state_v2 import (
    byte_accounting_lean as byte_accounting_lean,
)
from tests.formal.test_lean_asset_lane_custody_complete_state_v2 import (
    complete_state_lean as complete_state_lean,
)
from tests.formal.test_lean_asset_lane_custody_complete_state_v2 import (
    composition_lean as composition_lean,
)
from tests.formal.test_lean_asset_lane_custody_complete_state_v2 import (
    custody_effect_plan_lean as custody_effect_plan_lean,
)
from tests.formal.test_lean_asset_lane_custody_complete_state_v2 import (
    custody_structural_lean as custody_structural_lean,
)
from tests.formal.test_lean_asset_lane_custody_complete_state_v2 import (
    effect_plan_lean as effect_plan_lean,
)
from tests.formal.test_lean_asset_lane_custody_complete_state_v2 import (
    finite_recomposition_lean as finite_recomposition_lean,
)
from tests.formal.test_lean_asset_lane_custody_complete_state_v2 import (
    finite_trace_lean as finite_trace_lean,
)
from tests.formal.test_lean_asset_lane_custody_complete_state_v2 import (
    lean as lean,
)
from tests.formal.test_lean_asset_lane_custody_complete_state_v2 import (
    outcome_lean as outcome_lean,
)
from tests.formal.test_lean_asset_lane_custody_complete_state_v2 import (
    row_growth_lean as row_growth_lean,
)
from tests.formal.test_lean_asset_lane_custody_complete_state_v2 import (
    shared_lean as shared_lean,
)
from tests.formal.test_lean_asset_lane_custody_complete_state_v2 import (
    transfer_consumer_lean as transfer_consumer_lean,
)
from tests.formal.test_lean_asset_lane_custody_complete_state_v2 import (
    transfer_effect_plan_lean as transfer_effect_plan_lean,
)
from tests.formal.test_lean_asset_lane_custody_complete_state_v2 import (
    transfer_outcome_lean as transfer_outcome_lean,
)
from tests.formal.test_lean_asset_origin_registry_refinement_v2 import (
    CompiledPacket,
    _compile_lean_file,
)
from tests.formal.test_lean_asset_transfer_finite_outcome_v2 import (
    _lean_command as _transfer_command_value,
)
from tests.formal.test_lean_asset_transfer_finite_outcome_v2 import (
    _lean_context as _transfer_context_value,
)
from tests.formal.test_lean_asset_transfer_finite_outcome_v2 import (
    _lean_policy as _transfer_policy,
)
from tests.formal.test_lean_asset_transfer_finite_outcome_v2 import _lean_string, _wire
from tests.formal.test_lean_managed_asset_finite_outcome_v2 import (
    _lean_command as _managed_command_value,
)
from tests.formal.test_lean_managed_asset_finite_outcome_v2 import (
    _lean_policy as _managed_policy,
)

REPO = Path(__file__).resolve().parents[2]
MODULE = "AssetLaneCustodyAdmissionV2"
NAMESPACE = f"Proofs.{MODULE}"
SOURCE = REPO / "lean-mathlib/Proofs" / f"{MODULE}.lean"
SOURCE_SHA256 = "8d3b78d134bbb00e566a73d47c132af571875afae8871d7c13e6c75c242cad64"
PROJECTION_SHA256 = "9486eb80bc01d6eb26c3ae0f86ba94c74c6e4b5ddeba6adc4538306459dce03b"
CONTROLS = REPO / "tests/formal/asset_lane_custody_admission_v2_controls.lean"
CONTROLS_SHA256 = "f215f353aaa18c6de3ed3c5f6c686f13ee5983f627561dfb89a1b01e5f78f32f"
WITNESS = REPO / "tests/formal/asset_lane_custody_admission_v2_witness.lean"
WITNESS_SHA256 = "e0415851508dfa5d2abdd9e476675ba29b8b041b604262b4ee89df7b1908f234"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
CONTRACTS = {
    "policy_origin_bindings_preserved": "∀ {transferCommit : T.Policy → String}\n      {managedCommit : M.Policy → String} (digest : B.Bytes → String) (pre : FullState)\n      (action : F.Action) (_h : PolicyOriginBindings transferCommit managedCommit pre),\n      PolicyOriginBindings transferCommit managedCommit (step digest pre action)",
    "step_preserves_constructor_admission": "∀ {rootSyntax : String → Prop}\n      {namespaceSyntax : String → T.AssetClass → Prop} (digest : B.Bytes → String)\n      {pre : FullState} {action : F.Action}\n      (_h : ConstructorAdmission rootSyntax namespaceSyntax pre)\n      (_input : X.ActionAdmission action)\n      (_postFits : Resources (step digest pre action)),\n      ConstructorAdmission rootSyntax namespaceSyntax (step digest pre action)",
    "transfer_accepted_full_projection": "∀ {digest : B.Bytes → String} {pre : FullState}\n      {context : T.Context} {command : T.Command}\n      (_accepted : (FT.transition digest context pre.transfer command).verdict = .accepted),\n      (step digest pre (.transfer context command)).transfer =\n        (FT.transition digest context pre.transfer command).post",
    "managed_accepted_full_projection": "∀ {digest : B.Bytes → String} {pre : FullState}\n      {context : M.Context} {command : M.Command}\n      (_structural : X.CompleteStructural (erase pre))\n      (_input : X.ActionAdmission (.managed context command))\n      (_accepted : (FM.transition digest context (E.managedSource (erase pre)) command).verdict =\n        .accepted),\n      E.managedSource (erase (step digest pre (.managed context command))) =\n        (FM.transition digest context (E.managedSource (erase pre)) command).post",
}


def _compile_module(packet: CompiledPacket, source: Path, name: str, expected: str) -> None:
    data = source.read_bytes()
    assert hashlib.sha256(data).hexdigest() == expected
    target = packet.root / f"{name}.lean"
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(data)
    library = Path(packet.environment["LEAN_PATH"].split(os.pathsep)[0])
    output = library / f"{name}.olean"
    output.parent.mkdir(parents=True, exist_ok=True)
    result = subprocess.run(
        [
            str(packet.lean),
            "-DwarningAsError=true",
            "-R",
            str(packet.root),
            "-o",
            str(output),
            str(target),
        ],
        cwd=packet.root,
        env=packet.environment,
        capture_output=True,
        text=True,
        timeout=300,
        check=False,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout == result.stderr == ""


@pytest.fixture(scope="module")
def admission_lean(complete_state_lean: CompiledPacket) -> CompiledPacket:
    packet = complete_state_lean
    projection = REPO / "lean-mathlib/Proofs/AssetLaneCustodyExactProjectionV2.lean"
    _compile_module(packet, projection, f"Proofs/{projection.stem}", PROJECTION_SHA256)
    _compile_module(packet, SOURCE, f"Proofs/{MODULE}", SOURCE_SHA256)
    return packet


@pytest.fixture(scope="module")
def admission_controls(admission_lean: CompiledPacket) -> CompiledPacket:
    _compile_module(admission_lean, CONTROLS, "AdmissionSemanticControls", CONTROLS_SHA256)
    return admission_lean


def _consumer(
    packet: CompiledPacket, name: str, code: str, *, extra_import: str | None = None
) -> str:
    path = packet.root / f"{name}.lean"
    path.write_text(
        f"import {NAMESPACE}\nimport Lean.Data.Json\n"
        + (f"import {extra_import}\n" if extra_import else "")
        + f"open {NAMESPACE}\n"
        + "open Proofs.AssetLaneCustodyCompleteStateV2 (FullState erase step Resources)\n"
        + "set_option warningAsError true\nset_option maxRecDepth 100000\n"
        + code
    )
    result = _compile_lean_file(packet, path)
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stderr == ""
    return result.stdout


def test_admission_contracts_and_standard_axioms(admission_lean: CompiledPacket) -> None:
    source = SOURCE.read_text()
    assert tuple(re.findall(r"^theorem\s+(\w+)", source, re.MULTILINE)) == tuple(CONTRACTS)
    code = re.sub(r"/-.*?-/", "", source, flags=re.DOTALL)
    assert (
        re.search(r"\b(?:sorry|sorryAx|admit|axiom|unsafe|native_decide|implemented_by)\b", code)
        is None
    )
    body = "\n".join(
        f"example : {signature} := @{NAMESPACE}.{name}\n#print axioms {NAMESPACE}.{name}"
        for name, signature in CONTRACTS.items()
    )
    output = _consumer(admission_lean, "AdmissionContracts", body)
    groups = re.findall(r"depends on axioms:\s*\[([^]]*)\]", output)
    assert {a.strip() for g in groups for a in g.split(",") if a.strip()} <= STANDARD_AXIOMS
    assert len(groups) + output.count("does not depend on any axioms") == len(CONTRACTS)


def test_complete_admission_order_and_zero_issue_root_controls(
    admission_controls: CompiledPacket,
) -> None:
    source = CONTROLS.read_text()
    code = re.sub(r"/-.*?-/", "", source, flags=re.DOTALL)
    assert (
        re.search(r"\b(?:sorry|sorryAx|admit|axiom|unsafe|native_decide|implemented_by)\b", code)
        is None
    )
    output = _consumer(
        admission_controls,
        "AdmissionControlAxioms",
        "\n".join(
            f"#print axioms AdmissionSemanticControls.{name}"
            for name in ("sortedAdmission", "reverseStructuralAndResources")
        ),
        extra_import="AdmissionSemanticControls",
    )
    groups = re.findall(r"depends on axioms:\s*\[([^]]*)\]", output)
    assert {a.strip() for g in groups for a in g.split(",") if a.strip()} <= STANDARD_AXIOMS
    assert len(groups) + output.count("does not depend on any axioms") == 2


def _binding_functions(state: AssetLaneCustodyStateV2) -> str:
    """Finite exact-policy commitments, computed independently of registry fields."""
    definitions = []
    transfers = [
        (_transfer_policy(_wire(p)), asset_transfer_policy_root_v2(p))
        for p in state.transfer_state.policies
    ]
    managed = [
        (_managed_policy(p), managed_asset_policy_root_v2(p)) for p in state.managed_policies
    ]
    for name, typ, entries in (
        ("transferCommit", "T.Policy", transfers),
        ("managedCommit", "M.Policy", managed),
    ):
        expression = "O.zeroRoot"
        for policy, commitment in reversed(entries):
            expression = (
                f"if policy = ({policy} : {typ}) then {_lean_string(commitment)} else {expression}"
            )
        definitions.append(f"def {name} (policy : {typ}) : String := {expression}")
    return "\n".join(definitions)


def test_actual_runtime_metadata_history_and_independent_falsifiers(
    admission_controls: CompiledPacket,
) -> None:
    pre = multiasset_custody_state()
    issue = _managed_command(amount_atoms=2)
    issued = transition_asset_lane_custody_v2(_context(issue), pre, issue)
    assert type(issued) is AssetLaneCustodyAcceptedV2
    burn = _managed_command(kind="managed_asset_burn", amount_atoms=2)
    burned = transition_asset_lane_custody_v2(_context(burn, nonce=2), issued.post_state, burn)
    assert type(burned) is AssetLaneCustodyAcceptedV2
    assert burned.post_state == pre
    assert dict((r.asset, r.amount_atoms) for r in pre.transfer_state.supplies)["AUD"] == 0
    assert (
        dict((r.asset, r.amount_atoms) for r in issued.post_state.transfer_state.supplies)["USD"]
        == 2
    )
    single = custody_state()
    command = _transfer_command(amount_atoms=10)
    transferred = transition_asset_lane_custody_v2(_context(command), single, command)
    assert type(transferred) is AssetLaneCustodyAcceptedV2
    assert transferred.post_state.transfer_state.balance_atoms("alice", "USD") == 68
    states = (pre, issued.post_state, burned.post_state, single, transferred.post_state)
    definitions = "\n".join(
        f"def state{i} : FullState := {_full_state(state)}" for i, state in enumerate(states)
    )
    other_root = _lean_string(_root("admission-independent-drift"))
    code = (
        definitions
        + "\n"
        + _binding_functions(single)
        + f"""
local instance bindingDecision (state : FullState) :
    Decidable (PolicyOriginBindings transferCommit managedCommit state) := by
  unfold PolicyOriginBindings
  infer_instance

def missingManaged : FullState := {{state3 with managedPolicies := []}}
def extraManaged : FullState := {{state3 with managedPolicies := state3.managedPolicies ++ state3.managedPolicies}}
def releaseDrift : FullState := {{state3 with originRegistry :=
  {{state3.originRegistry with moduleReleaseId := {other_root}}}}}
def identityDrift : FullState := {{state3 with managedPolicies :=
  (List.map (fun policy => {{policy with assetOriginRoot := some {other_root}}}) state3.managedPolicies)}}
def bindingDrift : FullState := {{state3 with originRegistry :=
  {{state3.originRegistry with assets := (List.map (fun record => {{record with transferPolicyRoot := {other_root}}}) state3.originRegistry.assets)}}}}
def managedBindingDrift : FullState := {{state3 with originRegistry :=
  {{state3.originRegistry with assets := (List.map (fun record => {{record with issuePolicyRoot := {other_root}}}) state3.originRegistry.assets)}}}}

def metadata (state : FullState) : Prop := ConstructorMetadata
  AdmissionSemanticControls.rootSyntax AdmissionSemanticControls.namespaceSyntax state
instance metadataDecision (state : FullState) : Decidable (metadata state) := by
  unfold metadata
  infer_instance
#eval IO.println ((Lean.toJson [
  decide (metadata state0), decide (metadata state1), decide (metadata state2),
  decide (metadata state3), decide (metadata state4),
  decide (metadata missingManaged), decide (metadata extraManaged),
  decide (metadata releaseDrift), decide (metadata identityDrift),
  decide (metadata bindingDrift),
  decide (PolicyOriginBindings transferCommit managedCommit state3),
  decide (metadata managedBindingDrift),
  decide (PolicyOriginBindings transferCommit managedCommit managedBindingDrift),
  decide (PolicyOriginBindings transferCommit managedCommit bindingDrift)]).compress)
"""
    )
    output = _consumer(
        admission_controls, "AdmissionRuntimeMetadata", code,
        extra_import="AdmissionSemanticControls",
    )
    assert [json.loads(line) for line in output.splitlines()] == [
        [True] * 5 + [False] * 4 + [True] * 3 + [False] * 2
    ]


def test_actual_accepted_actions_preserve_complete_constructor(
    admission_lean: CompiledPacket,
) -> None:
    """All hypotheses are inhabited by three accepted positive-custody actions."""
    _compile_module(admission_lean, WITNESS, "ConstructorAdmissionWitness", WITNESS_SHA256)
    pre = custody_state()
    body = [f"example : AdmissionWitness.pre = ({_full_state(pre)}) := by rfl"]
    for name, command, nonce in (
        ("transfer", _transfer_command(amount_atoms=10, max_fee_atoms=2), 1),
        ("issue", _managed_command(amount_atoms=2), 1),
        ("burn", _managed_command(kind="managed_asset_burn", amount_atoms=2), 2),
    ):
        context = _context(command, nonce=nonce)
        result = transition_asset_lane_custody_v2(context, pre, command)
        assert type(result) is AssetLaneCustodyAcceptedV2
        if type(command) is AssetTransferCommandV2:
            lean_context = _transfer_context_value(context.transfer_context())
            lean_command = _transfer_command_value(command)
        else:
            assert type(command) is ManagedAssetLifecycleCommandV2
            lean_context = _managed_context(context)
            lean_command = _managed_command_value(command)
        body.extend((
            f"example : AdmissionWitness.{name}Context = ({lean_context}) := by rfl",
            f"example : AdmissionWitness.{name}Command = ({lean_command}) := by rfl",
            f"def {name}RuntimePost : FullState := {_full_state(result.post_state)}",
            f"example : (step AdmissionWitness.digest AdmissionWitness.pre "
            f"AdmissionWitness.{name}Action).transfer.balances = {name}RuntimePost.transfer.balances ∧ "
            f"(step AdmissionWitness.digest AdmissionWitness.pre "
            f"AdmissionWitness.{name}Action).transfer.supplies = {name}RuntimePost.transfer.supplies := "
            f"AdmissionWitness.{name}_post_rows",
        ))
    body.append(_binding_functions(pre))
    for name in ("transfer", "managed"):
        body.append(
            f"example : AdmissionWitness.{name}Commit AdmissionWitness.{name}Policy = "
            f"{name}Commit AdmissionWitness.{name}Policy := by rfl"
        )
    audited = ["constructor_admission_witness"] + [
        f"{name}_{suffix}"
        for name in ("transfer", "issue", "burn")
        for suffix in (
            "leaf_accepted", "action_admitted", "post_resources", "post_admitted",
            "full_projection", "post_rows", "policy_origin_bindings",
        )
    ]
    body.extend(f"#print axioms AdmissionWitness.{name}" for name in audited)
    output = _consumer(
        admission_lean, "AdmissionAcceptedActions", "\n".join(body),
        extra_import="ConstructorAdmissionWitness",
    )
    groups = re.findall(r"depends on axioms:\s*\[([^]]*)\]", output)
    assert {a.strip() for g in groups for a in g.split(",") if a.strip()} <= STANDARD_AXIOMS
    assert len(groups) + output.count("does not depend on any axioms") == len(audited)
