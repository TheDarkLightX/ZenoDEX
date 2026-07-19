from __future__ import annotations

import ast
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"

REMOVED_SUPPORT_BUILDERS = frozenset(
    {
        "sample_autonomous_governance_q_policy_v1",
        "sample_autonomous_governance_surface_q_policy_v1",
        "sample_autonomous_governance_next_policy_v1",
        "sample_autonomous_governance_pi_policy_v1",
        "sample_autonomous_governance_ebrm_policy_v1",
        "sample_local_sandbox_profile_v0",
        "sample_zeno_sovereign_testnet_profile_v0",
        "sample_tau_exclusive_release_profile_v0",
        "clone_profile_with_new_id_v0",
    }
)


def test_sample_policy_and_profile_builders_are_absent_from_shipped_src() -> None:
    violations: list[str] = []
    for path in SRC.rglob("*.py"):
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        for node in ast.walk(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                if node.name in REMOVED_SUPPORT_BUILDERS:
                    violations.append(
                        f"{path.relative_to(ROOT)}:{node.lineno}:{node.name}"
                    )
    assert violations == []


def test_production_src_does_not_depend_on_tooling_support_package() -> None:
    violations: list[str] = []
    for path in SRC.rglob("*.py"):
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        for node in ast.walk(tree):
            module: str | None = None
            if isinstance(node, ast.ImportFrom):
                module = node.module
            elif isinstance(node, ast.Import):
                for alias in node.names:
                    if alias.name == "tools.support" or alias.name.startswith(
                        "tools.support."
                    ):
                        violations.append(
                            f"{path.relative_to(ROOT)}:{node.lineno}:{alias.name}"
                        )
            if module == "tools.support" or (
                module is not None and module.startswith("tools.support.")
            ):
                violations.append(
                    f"{path.relative_to(ROOT)}:{node.lineno}:{module}"
                )
    assert violations == []
