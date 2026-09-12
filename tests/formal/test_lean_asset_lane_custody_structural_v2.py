"""Initial complete-row structure supplies both leaves at every finite prefix.

Canonical resource/metadata admission and full runtime refinement remain separate.
The replay includes independent complete tables and state/action-admission
counterexamples; no new runtime behavior is introduced by this proof.
"""
from __future__ import annotations

import hashlib
import re
from pathlib import Path

import pytest

from tests.formal.test_lean_asset_lane_custody_finite_trace_v2 import (
    CONTROLS_PATH,
    CONTROLS_SHA256,
    FINITE_CONTROLS_PATH,
    FINITE_CONTROLS_SHA256,
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
from tests.formal.test_lean_registered_supply_support_v1 import LeanSubject, _compile

REPO = Path(__file__).resolve().parents[2]
MODULE = "AssetLaneCustodyStructuralV2"
NAMESPACE = f"Proofs.{MODULE}"
SOURCE = REPO / "lean-mathlib/Proofs" / f"{MODULE}.lean"
SOURCE_SHA256 = "a1d6e09ff74cbca8627a6f7add05c897b732f17e09f2110c5bd2550a9bf170fd"
CONTROLS = Path(__file__).with_name("asset_lane_custody_structural_v2_controls.lean")
CONTROL_SHA256 = "3884a410f8240ca952a577bae9477f334f08711950b875de023188b5cd8733c8"
STANDARD_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
CONTRACTS = {
    "transfer_source_structural": """∀ {pre : C.State}, CompleteStructural pre →
      FT.Structural (E.transferSource pre)""",
    "managed_source_structural": """∀ {pre : C.State}, CompleteStructural pre →
      FM.Structural (E.managedSource pre)""",
    "step_preserves_complete": """∀ (digest : B.Bytes → String) {pre : C.State}
      {action : F.Action}, CompleteStructural pre → ActionAdmission action →
      CompleteStructural (F.step digest pre action)""",
    "run_preserves_complete": """∀ (digest : B.Bytes → String) (actions : List F.Action)
      {pre : C.State}, CompleteStructural pre → (∀ action ∈ actions, ActionAdmission action) →
      CompleteStructural (F.run digest pre actions)""",
    "every_prefix_complete_and_sources": """∀ (digest : B.Bytes → String)
      (actions : List F.Action) {pre : C.State}, CompleteStructural pre →
      (∀ action ∈ actions, ActionAdmission action) → ∀ length,
      CompleteStructural (F.run digest pre (actions.take length)) ∧
      FT.Structural (E.transferSource (F.run digest pre (actions.take length))) ∧
      FM.Structural (E.managedSource (F.run digest pre (actions.take length)))""",
}


@pytest.fixture(scope="module")
def custody_structural_lean(finite_trace_lean: LeanSubject) -> LeanSubject:
    source = SOURCE.read_bytes()
    assert hashlib.sha256(source).hexdigest() == SOURCE_SHA256
    target = finite_trace_lean.source / "Proofs" / f"{MODULE}.lean"
    target.write_bytes(source)
    checked = _compile(finite_trace_lean, target, finite_trace_lean.library / "Proofs" / f"{MODULE}.olean")
    assert checked.returncode == 0, checked.stdout + checked.stderr
    assert checked.stdout == checked.stderr == ""
    return finite_trace_lean


def test_initial_structure_contracts_and_standard_axioms(custody_structural_lean: LeanSubject) -> None:
    source = SOURCE.read_text()
    controls = CONTROLS.read_text()
    code = re.sub(r"/-.*?-/", "", source + chr(10) + controls, flags=re.DOTALL)
    assert re.search(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b", code) is None
    assert tuple(re.findall(r"^theorem\s+(\w+)", source, flags=re.MULTILINE)) == tuple(CONTRACTS)
    body = "\n".join(
        f"example : {signature} := @{NAMESPACE}.{name}\n#print axioms {NAMESPACE}.{name}"
        for name, signature in CONTRACTS.items()
    )
    path = custody_structural_lean.source / "CustodyStructuralContracts.lean"
    path.write_text(f"import {NAMESPACE}\nopen {NAMESPACE}\n{body}")
    checked = _compile(custody_structural_lean, path)
    assert checked.returncode == 0, checked.stdout + checked.stderr
    assert checked.stderr == ""
    groups = re.findall(r"depends on axioms:\s*\[([^]]*)\]", checked.stdout)
    axioms = {item.strip() for group in groups for item in group.split(",") if item.strip()}
    assert axioms <= STANDARD_AXIOMS
    assert len(groups) + checked.stdout.count("does not depend on any axioms") == len(CONTRACTS)


def test_complete_initial_state_and_mixed_history_have_both_leaf_structures(
    custody_structural_lean: LeanSubject,
) -> None:
    parts = []
    for path, expected in (
        (CONTROLS_PATH, CONTROLS_SHA256),
        (FINITE_CONTROLS_PATH, FINITE_CONTROLS_SHA256),
        (CONTROLS, CONTROL_SHA256),
    ):
        data = path.read_bytes()
        assert hashlib.sha256(data).hexdigest() == expected
        parts.append(data.decode())
    path = custody_structural_lean.source / "CustodyStructuralControls.lean"
    path.write_text(f"import {NAMESPACE}\n" + "\n".join(parts))
    checked = _compile(custody_structural_lean, path)
    assert checked.returncode == 0, checked.stdout + checked.stderr
    assert checked.stderr == ""
