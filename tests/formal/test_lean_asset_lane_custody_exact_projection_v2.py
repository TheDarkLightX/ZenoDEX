"""Exact full leaf reprojection with independent complete-state controls.

Fresh Lean source replay closes ordered state equality for the finite model;
complete metadata, resources, runtime codecs and publication remain separate.
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
from tests.formal.test_lean_asset_lane_custody_structural_v2 import (
    CONTROL_SHA256 as STRUCTURAL_CONTROLS_SHA256,
)
from tests.formal.test_lean_asset_lane_custody_structural_v2 import (
    CONTROLS as STRUCTURAL_CONTROLS_PATH,
)
from tests.formal.test_lean_asset_lane_custody_structural_v2 import (
    custody_structural_lean as custody_structural_lean,
)
from tests.formal.test_lean_registered_supply_support_v1 import LeanSubject, _compile

REPO = Path(__file__).resolve().parents[2]
MODULE = "AssetLaneCustodyExactProjectionV2"
NAMESPACE = f"Proofs.{MODULE}"
SOURCE = REPO / "lean-mathlib/Proofs" / f"{MODULE}.lean"
SOURCE_SHA256 = "9486eb80bc01d6eb26c3ae0f86ba94c74c6e4b5ddeba6adc4538306459dce03b"
CONTROLS = Path(__file__).with_name("asset_lane_custody_exact_projection_v2_controls.lean")
CONTROL_SHA256 = "bf9f385e2add6b76e0596291731ce82e147e4c1284308ba11f51f5990052c528"
STANDARD_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
CONTRACTS = {
    "transfer_post_from_leaf_exact": """∀ (pre : G.State) (leafPost : FT.State),
      E.transferSource (E.transferPostFromLeaf pre leafPost) = leafPost""",
    "transfer_accepted_step_exact": """∀ {digest : B.Bytes → String} {pre : G.State}
      {context : T.Context} {command : T.Command},
      (FT.transition digest context (E.transferSource pre) command).verdict = .accepted →
      E.transferSource (F.step digest pre (.transfer context command)) =
      (FT.transition digest context (E.transferSource pre) command).post""",
    "managed_accepted_post_exact": """∀ {digest : B.Bytes → String} {pre : G.State}
      {context : M.Context} {command : M.Command}, X.CompleteStructural pre →
      X.ActionAdmission (.managed context command) →
      (FM.transition digest context (E.managedSource pre) command).verdict = .accepted →
      E.managedSource (E.managedPostFromLeaf pre
        (FM.transition digest context (E.managedSource pre) command).post) =
      (FM.transition digest context (E.managedSource pre) command).post""",
    "managed_accepted_step_exact": """∀ {digest : B.Bytes → String} {pre : G.State}
      {context : M.Context} {command : M.Command}, X.CompleteStructural pre →
      X.ActionAdmission (.managed context command) →
      (FM.transition digest context (E.managedSource pre) command).verdict = .accepted →
      E.managedSource (F.step digest pre (.managed context command)) =
      (FM.transition digest context (E.managedSource pre) command).post""",
}


@pytest.fixture(scope="module")
def exact_projection_lean(custody_structural_lean: LeanSubject) -> LeanSubject:
    source = SOURCE.read_bytes()
    assert hashlib.sha256(source).hexdigest() == SOURCE_SHA256
    target = custody_structural_lean.source / "Proofs" / f"{MODULE}.lean"
    target.write_bytes(source)
    checked = _compile(
        custody_structural_lean, target, custody_structural_lean.library / "Proofs" / f"{MODULE}.olean"
    )
    assert checked.returncode == 0, checked.stdout + checked.stderr
    assert checked.stdout == checked.stderr == ""
    return custody_structural_lean


def test_exact_projection_signatures_and_standard_axioms(exact_projection_lean: LeanSubject) -> None:
    source = SOURCE.read_text()
    controls = CONTROLS.read_text()
    code = re.sub(r"/-.*?-/", "", source + chr(10) + controls, flags=re.DOTALL)
    assert re.search(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b", code) is None
    assert tuple(re.findall(r"^theorem\s+(\w+)", source, flags=re.MULTILINE)) == tuple(CONTRACTS)
    body = "\n".join(
        f"example : {signature} := @{NAMESPACE}.{name}\n#print axioms {NAMESPACE}.{name}"
        for name, signature in CONTRACTS.items()
    )
    path = exact_projection_lean.source / "CustodyExactProjectionContracts.lean"
    path.write_text(f"import {NAMESPACE}\nopen {NAMESPACE}\n{body}")
    checked = _compile(exact_projection_lean, path)
    assert checked.returncode == 0, checked.stdout + checked.stderr
    assert checked.stderr == ""
    groups = re.findall(r"depends on axioms:\s*\[([^]]*)\]", checked.stdout)
    axioms = {item.strip() for group in groups for item in group.split(",") if item.strip()}
    assert axioms <= STANDARD_AXIOMS
    assert len(groups) + checked.stdout.count("does not depend on any axioms") == len(CONTRACTS)


def test_exact_reprojection_controls_keep_full_siblings_and_terminal_zero(
    exact_projection_lean: LeanSubject,
) -> None:
    parts = []
    for path, expected in (
        (CONTROLS_PATH, CONTROLS_SHA256),
        (FINITE_CONTROLS_PATH, FINITE_CONTROLS_SHA256),
        (STRUCTURAL_CONTROLS_PATH, STRUCTURAL_CONTROLS_SHA256),
        (CONTROLS, CONTROL_SHA256),
    ):
        data = path.read_bytes()
        assert hashlib.sha256(data).hexdigest() == expected
        parts.append(data.decode())
    path = exact_projection_lean.source / "CustodyExactProjectionControls.lean"
    path.write_text(f"import {NAMESPACE}\n" + "\n".join(parts))
    checked = _compile(exact_projection_lean, path)
    assert checked.returncode == 0, checked.stdout + checked.stderr
    assert checked.stderr == ""
