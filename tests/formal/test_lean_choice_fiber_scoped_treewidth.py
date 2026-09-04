from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LEAN_ROOT = ROOT / "lean-mathlib"
TARGET = "Proofs/ChoiceFiberScopedTreewidth.lean"
CHALLENGE = "Proofs/ChoiceFiberScopedTreewidthChallenge.lean"
OBJECT = (
    LEAN_ROOT / ".lake" / "build" / "lib" / "lean" / "Proofs" / ("ChoiceFiberScopedTreewidth.olean")
)

REQUIRED_DECLARATIONS = (
    "scope_substitution_correct",
    "complete_extends",
    "complete_eq_of_extends",
    "restricted_minimum_iff",
    "eliminationMessage_correct",
    "ExactMessageRecurrence.sound",
    "exactPartition_minimum_iff",
    "scoped_treewidth_partition_composition",
    "separatorCounterexample_exact_minimum",
    "independent_owner_bag_minima_report_minus_three",
    "independent_owner_bag_value_is_unattainable",
)
FORBIDDEN = re.compile(r"\b(sorry|admit|axiom|unsafe|sorryAx|native_decide)\b")


def test_choice_fiber_scoped_treewidth_claim_surface_is_closed() -> None:
    source = (LEAN_ROOT / TARGET).read_text(encoding="utf-8")
    normalized_source = " ".join(source.split())
    challenge = (LEAN_ROOT / CHALLENGE).read_text(encoding="utf-8")
    aggregator = (LEAN_ROOT / "Proofs.lean").read_text(encoding="utf-8")

    for declaration in REQUIRED_DECLARATIONS:
        assert re.search(rf"\btheorem\s+{re.escape(declaration)}\b", source)
    assert FORBIDDEN.search(source) is None
    assert "import Proofs.ChoiceFiberScopedTreewidth" in aggregator
    assert "import Proofs.ChoiceFiberScopedTreewidthChallenge" in aggregator

    for declaration in (
        "scope_substitution_correct",
        "restricted_minimum_iff",
        "ExactMessageRecurrence.sound",
        "exactPartition_minimum_iff",
        "scoped_treewidth_partition_composition",
        "separatorCounterexample_exact_minimum",
        "independent_owner_bag_minima_report_minus_three",
        "independent_owner_bag_value_is_unattainable",
    ):
        assert re.search(rf"#check\s+\({re.escape(declaration)}\s*:", challenge)

    for required_nonclaim in (
        "Python decomposition algorithm",
        "canonical encoding or roots",
        "Python/Rust refinement",
        "RISC0 receipt soundness",
        "ZRPF guest",
        "M6 closure",
        "settlement authority",
        "canonical argmin tie-breaking",
        "induced-width correctness",
        "separator or factor ownership",
        "resource-preflight bounds",
        "Python-bitmask-to-Lean-scope projection",
        "Tree-decomposition validity",
        "running-intersection property",
        "local-factor plus child-message decomposition",
        "runtime message-table verification",
    ):
        assert required_nonclaim in normalized_source


def test_choice_fiber_scoped_treewidth_typechecks() -> None:
    lake = shutil.which("lake")
    assert lake is not None, "formal claim gate requires lake"
    assert (ROOT / "external" / "mathlib4").exists(), "formal claim gate requires mathlib4"

    OBJECT.parent.mkdir(parents=True, exist_ok=True)

    checked = subprocess.run(
        [
            lake,
            "env",
            "lean",
            "-R",
            ".",
            "-o",
            str(OBJECT.relative_to(LEAN_ROOT)),
            TARGET,
        ],
        cwd=LEAN_ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=240,
        check=False,
    )
    assert checked.returncode == 0, checked.stdout + checked.stderr
    assert "error:" not in (checked.stdout + checked.stderr).lower()

    challenged = subprocess.run(
        [lake, "env", "lean", CHALLENGE],
        cwd=LEAN_ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=240,
        check=False,
    )
    assert challenged.returncode == 0, challenged.stdout + challenged.stderr
    challenge_output = challenged.stdout + challenged.stderr
    assert "error:" not in challenge_output.lower()
    assert "sorryAx" not in challenge_output
