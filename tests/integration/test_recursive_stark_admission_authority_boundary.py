from __future__ import annotations

import ast
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PRODUCTION_ROOTS = tuple(ROOT / name for name in ("src", "tools", "bin", "scripts"))
PRODUCTION_FILES = (ROOT / "sitecustomize.py",)
CORE = ROOT / "src/core/recursive_stark_admission.py"
PINNED_ADAPTER = ROOT / "src/integration/recursive_stark_verifier_adapter.py"

PRIVATE_CAPABILITY_TYPE = "_AuthenticatedRecursiveStarkRootFacts"
PRIVATE_SEAL = "_AUTHENTICATED_FACTS_SEAL"
PRIVATE_MINT = "_mint_recursive_stark_root_facts_after_verification"
PRIVATE_ADMISSION = "_admit_authenticated_recursive_stark_root"
PRIVATE_AUTHORITY_NAMES = frozenset(
    {PRIVATE_CAPABILITY_TYPE, PRIVATE_SEAL, PRIVATE_MINT, PRIVATE_ADMISSION}
)
PRIVATE_ADAPTER_CALLS = frozenset({PRIVATE_MINT, PRIVATE_ADMISSION})
RETIRED_PUBLIC_AUTHORITY_NAMES = frozenset(
    {
        "VerifiedRecursiveStarkRootFacts",
        "admit_verified_recursive_stark_root",
        "parse_authenticated_recursive_facts",
    }
)
DATA_ONLY_ADMISSION_RESULT = "RecursiveStarkAdmissionResult"


def test_private_admission_symbols_are_absent_from_other_production_modules() -> None:
    violations: list[str] = []
    for path in _production_python_paths():
        if path in {CORE, PINNED_ADAPTER}:
            continue
        tree = _parse(path)
        for node in ast.walk(tree):
            name = _private_authority_reference(node)
            if name is not None:
                violations.append(f"{path.relative_to(ROOT)}:{_line(node)}:{name}")

    assert violations == []


def test_automatic_root_python_hook_is_in_governed_inventory() -> None:
    assert ROOT / "sitecustomize.py" in _production_python_paths()


def test_pinned_adapter_has_one_exact_post_parse_mint_and_admission_path() -> None:
    tree = _parse(PINNED_ADAPTER)
    verifier = _class(tree, "PinnedRecursiveStarkVerifier")
    method = _method(verifier, "verify_and_admit")

    private_imports = {
        (imported.name, imported.asname)
        for node in tree.body
        if isinstance(node, ast.ImportFrom)
        and node.module == "src.core.recursive_stark_admission"
        for imported in node.names
        if imported.name in PRIVATE_AUTHORITY_NAMES
    }
    assert private_imports == {(name, None) for name in PRIVATE_ADAPTER_CALLS}
    assert _reserved_adapter_binding_violations(tree) == []

    calls: dict[str, list[ast.Call]] = {}
    for name in ("parse_recursive_stark_root_facts", PRIVATE_MINT, PRIVATE_ADMISSION):
        calls[name] = [
            node
            for node in ast.walk(method)
            if isinstance(node, ast.Call) and _call_name(node) == name
        ]
    assert {name: len(nodes) for name, nodes in calls.items()} == {
        "parse_recursive_stark_root_facts": 1,
        PRIVATE_MINT: 1,
        PRIVATE_ADMISSION: 1,
    }
    assert _line(calls["parse_recursive_stark_root_facts"][0]) < _line(
        calls[PRIVATE_MINT][0]
    ) < _line(calls[PRIVATE_ADMISSION][0])

    assert _private_adapter_reference_violations(tree, method) == []


def test_architecture_ratchet_rejects_public_adapter_bypass_mutant() -> None:
    source = PINNED_ADAPTER.read_text(encoding="utf-8")
    mutant = ast.parse(
        source
        + "\n\ndef public_unverified_admission(state, facts, policy):\n"
        + f"    cap = {PRIVATE_MINT}(facts, policy)\n"
        + f"    return {PRIVATE_ADMISSION}(state, cap)\n",
        filename=str(PINNED_ADAPTER),
    )
    verifier = _class(mutant, "PinnedRecursiveStarkVerifier")
    method = _method(verifier, "verify_and_admit")

    assert _private_adapter_reference_violations(mutant, method) != []


def test_architecture_ratchet_rejects_adapter_shadow_and_qualified_call_mutants() -> None:
    source = PINNED_ADAPTER.read_text(encoding="utf-8")
    for name in sorted(PRIVATE_ADAPTER_CALLS):
        shadow = ast.parse(
            source + f"\n\ndef {name}(*_args, **_kwargs):\n    return None\n",
            filename=str(PINNED_ADAPTER),
        )
        assert _reserved_adapter_binding_violations(shadow) != []

        qualified_source = source.replace(f"{name}(", f"alternate.{name}(", 1)
        assert qualified_source != source
        qualified = ast.parse(qualified_source, filename=str(PINNED_ADAPTER))
        verifier = _class(qualified, "PinnedRecursiveStarkVerifier")
        method = _method(verifier, "verify_and_admit")
        assert _private_adapter_reference_violations(qualified, method) != []


def test_core_exposes_no_public_capability_constructor_or_admission_wrapper() -> None:
    tree = _parse(CORE)
    top_level_names = {
        node.name
        for node in tree.body
        if isinstance(node, (ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef))
    }
    top_level_names.update(
        target.id
        for node in tree.body
        if isinstance(node, ast.Assign)
        for target in node.targets
        if isinstance(target, ast.Name)
    )
    assert PRIVATE_AUTHORITY_NAMES <= top_level_names

    violations: list[str] = []
    for node in tree.body:
        if not isinstance(node, (ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        if node.name.startswith("_"):
            continue
        for descendant in ast.walk(node):
            name = _node_name(descendant)
            if name in PRIVATE_AUTHORITY_NAMES:
                violations.append(f"{node.name}:{_line(descendant)}:{name}")
    violations.extend(_public_top_level_authority_reachability(tree))
    violations.extend(_public_authority_alias_violations(tree))
    violations.extend(_private_authority_all_exports(tree))
    assert violations == []


def test_architecture_detector_rejects_public_wrapper_through_private_bridge() -> None:
    tree = ast.parse(
        """
def _admit_authenticated_recursive_stark_root():
    return None

def _private_bridge():
    return _admit_authenticated_recursive_stark_root()

def admit_without_verification():
    return _private_bridge()
"""
    )

    assert _public_top_level_authority_reachability(tree) == [
        "admit_without_verification"
    ]


def test_architecture_detector_rejects_public_method_through_private_bridge() -> None:
    tree = ast.parse(
        """
def _admit_authenticated_recursive_stark_root():
    return None

def _private_bridge():
    return _admit_authenticated_recursive_stark_root()

class PublicAdmission:
    def admit_without_verification(self):
        return _private_bridge()
"""
    )

    assert _public_top_level_authority_reachability(tree) == [
        "PublicAdmission.admit_without_verification"
    ]


def test_architecture_detector_rejects_public_alias_and_all_export_mutants() -> None:
    tree = ast.parse(
        """
def _admit_authenticated_recursive_stark_root():
    return None

_private_alias = _admit_authenticated_recursive_stark_root
public_admit_alias = _private_alias
public_lambda = lambda: _admit_authenticated_recursive_stark_root()
__all__ = ["_private_alias"]
"""
    )

    assert _public_authority_alias_violations(tree) == [
        "public_admit_alias:_private_alias",
        "public_lambda:_admit_authenticated_recursive_stark_root",
    ]
    assert _private_authority_all_exports(tree) == [
        "__all__:_private_alias"
    ]


def test_architecture_detector_rejects_public_async_wrapper_mutant() -> None:
    tree = ast.parse(
        """
def _admit_authenticated_recursive_stark_root():
    return None

async def admit_without_verification():
    return _admit_authenticated_recursive_stark_root()
"""
    )

    assert _public_top_level_authority_reachability(tree) == [
        "admit_without_verification"
    ]


def test_public_shape_parser_cannot_mint_or_admit_authority() -> None:
    tree = _parse(PINNED_ADAPTER)
    parser = _function(tree, "parse_recursive_stark_root_facts")
    references = {
        name
        for node in ast.walk(parser)
        if (name := _node_name(node)) is not None
    }

    assert references.isdisjoint(PRIVATE_AUTHORITY_NAMES)


def test_retired_public_authority_symbols_do_not_reappear() -> None:
    violations: list[str] = []
    for path in _production_python_paths():
        source = path.read_text(encoding="utf-8")
        for name in sorted(RETIRED_PUBLIC_AUTHORITY_NAMES):
            if name in source:
                violations.append(f"{path.relative_to(ROOT)}:{name}")

    assert violations == []


def test_data_only_admission_result_has_no_production_consumer() -> None:
    violations: list[str] = []
    for path in _production_python_paths():
        if path in {CORE, PINNED_ADAPTER}:
            continue
        tree = _parse(path)
        for node in ast.walk(tree):
            if (
                isinstance(node, ast.Attribute)
                and node.attr == "verify_and_admit"
            ):
                violations.append(
                    f"{path.relative_to(ROOT)}:{_line(node)}:verify_and_admit"
                )
            if _node_name(node) == DATA_ONLY_ADMISSION_RESULT:
                violations.append(
                    f"{path.relative_to(ROOT)}:{_line(node)}:{DATA_ONLY_ADMISSION_RESULT}"
                )
            if isinstance(node, ast.ImportFrom) and any(
                imported.name == DATA_ONLY_ADMISSION_RESULT for imported in node.names
            ):
                violations.append(
                    f"{path.relative_to(ROOT)}:{_line(node)}:{DATA_ONLY_ADMISSION_RESULT}"
                )

    assert violations == []


def test_production_consumer_detector_rejects_normal_and_aliased_method_use() -> None:
    tree = ast.parse(
        """
result = verifier.verify_and_admit(state=state, proof=proof, recursive_input=input)
admit = verifier.verify_and_admit
store.commit(result.state)
"""
    )

    references = [
        node
        for node in ast.walk(tree)
        if isinstance(node, ast.Attribute) and node.attr == "verify_and_admit"
    ]
    assert len(references) == 2


def _production_python_paths() -> tuple[Path, ...]:
    return tuple(
        sorted(
            set(PRODUCTION_FILES)
            | {
                path
                for root in PRODUCTION_ROOTS
                if root.is_dir()
                for path in root.rglob("*.py")
            }
        )
    )


def _parse(path: Path) -> ast.Module:
    return ast.parse(path.read_text(encoding="utf-8"), filename=str(path))


def _private_authority_reference(node: ast.AST) -> str | None:
    if isinstance(node, ast.ImportFrom):
        for imported in node.names:
            if imported.name in PRIVATE_AUTHORITY_NAMES:
                return imported.name
    name = _node_name(node)
    return name if name in PRIVATE_AUTHORITY_NAMES else None


def _node_name(node: ast.AST) -> str | None:
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        return node.attr
    return None


def _is_direct_call_target(node: ast.AST, parents: dict[ast.AST, ast.AST]) -> bool:
    parent = parents.get(node)
    return isinstance(parent, ast.Call) and parent.func is node


def _call_name(node: ast.Call) -> str | None:
    return _node_name(node.func)


def _public_top_level_authority_reachability(tree: ast.Module) -> list[str]:
    function_names = {
        node.name
        for node in tree.body
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
    }
    authority_reaching = _authority_reaching_top_level_function_names(tree)
    violations = {
        name
        for name in function_names
        if not name.startswith("_") and name in authority_reaching
    }
    for node in tree.body:
        if not isinstance(node, ast.ClassDef) or node.name.startswith("_"):
            continue
        method_graph = {
            method.name: {
                name
                for descendant in ast.walk(method)
                if isinstance(descendant, ast.Call)
                if (name := _call_name(descendant)) is not None
            }
            for method in node.body
            if isinstance(method, (ast.FunctionDef, ast.AsyncFunctionDef))
        }
        reaching_methods = {
            name
            for name, calls in method_graph.items()
            if not calls.isdisjoint(authority_reaching)
        }
        while True:
            discovered = {
                name
                for name, calls in method_graph.items()
                if name not in reaching_methods and not calls.isdisjoint(reaching_methods)
            }
            if not discovered:
                break
            reaching_methods.update(discovered)
        violations.update(
            f"{node.name}.{name}"
            for name in reaching_methods
            if not name.startswith("_")
        )
    return sorted(violations)


def _public_authority_alias_violations(tree: ast.Module) -> list[str]:
    authority_names = _authority_alias_names(tree)
    violations: set[str] = set()
    for node in tree.body:
        if not isinstance(node, (ast.Assign, ast.AnnAssign)):
            continue
        sources = (
            _expression_names(node.value) & authority_names
            if node.value is not None
            else set()
        )
        if not sources:
            continue
        violations.update(
            f"{target}:{source}"
            for target in _assignment_names(node)
            if not target.startswith("_")
            for source in sources
        )
    return sorted(violations)


def _private_authority_all_exports(tree: ast.Module) -> list[str]:
    authority_names = _authority_alias_names(tree)
    violations: list[str] = []
    for node in tree.body:
        if not isinstance(node, (ast.Assign, ast.AnnAssign)):
            continue
        if "__all__" not in _assignment_names(node) or node.value is None:
            continue
        if not isinstance(node.value, (ast.List, ast.Tuple, ast.Set)):
            violations.append("__all__:dynamic")
            continue
        for element in node.value.elts:
            if (
                isinstance(element, ast.Constant)
                and isinstance(element.value, str)
                and element.value in authority_names
            ):
                violations.append(f"__all__:{element.value}")
    return sorted(violations)


def _authority_alias_names(tree: ast.Module) -> set[str]:
    authority_names = set(PRIVATE_AUTHORITY_NAMES)
    authority_names.update(_authority_reaching_top_level_function_names(tree))
    assignments = tuple(
        node
        for node in tree.body
        if isinstance(node, (ast.Assign, ast.AnnAssign))
    )
    while True:
        discovered = {
            target
            for node in assignments
            if node.value is not None
            if not _expression_names(node.value).isdisjoint(authority_names)
            for target in _assignment_names(node)
            if target not in authority_names
        }
        if not discovered:
            return authority_names
        authority_names.update(discovered)


def _authority_reaching_top_level_function_names(tree: ast.Module) -> set[str]:
    call_graph = {
        node.name: {
            name
            for descendant in ast.walk(node)
            if isinstance(descendant, ast.Call)
            if (name := _call_name(descendant)) is not None
        }
        for node in tree.body
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
    }
    authority_reaching = set(PRIVATE_AUTHORITY_NAMES)
    while True:
        discovered = {
            name
            for name, calls in call_graph.items()
            if name not in authority_reaching and not calls.isdisjoint(authority_reaching)
        }
        if not discovered:
            return authority_reaching
        authority_reaching.update(discovered)


def _assignment_names(node: ast.Assign | ast.AnnAssign) -> tuple[str, ...]:
    targets = node.targets if isinstance(node, ast.Assign) else (node.target,)
    return tuple(name for target in targets for name in _target_names(target))


def _target_names(target: ast.expr) -> tuple[str, ...]:
    if isinstance(target, ast.Name):
        return (target.id,)
    if isinstance(target, ast.Attribute):
        return (target.attr,)
    if isinstance(target, (ast.List, ast.Tuple)):
        return tuple(name for element in target.elts for name in _target_names(element))
    return ()


def _expression_names(value: ast.expr) -> set[str]:
    return {
        name
        for node in ast.walk(value)
        if (name := _node_name(node)) is not None
    }


def _private_adapter_reference_violations(
    tree: ast.Module,
    allowed_method: ast.FunctionDef,
) -> list[str]:
    method_nodes = frozenset(ast.walk(allowed_method))
    parents = _parent_map(tree)
    violations: list[str] = []
    for node in ast.walk(tree):
        reference = _node_name(node)
        if reference not in PRIVATE_AUTHORITY_NAMES:
            continue
        if (
            not isinstance(node, ast.Name)
            or node not in method_nodes
            or not _is_direct_call_target(node, parents)
        ):
            violations.append(f"{_line(node)}:{reference}")
    return violations


def _reserved_adapter_binding_violations(tree: ast.Module) -> list[str]:
    parents = _parent_map(tree)
    violations: list[str] = []
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            if node.name in PRIVATE_AUTHORITY_NAMES:
                violations.append(f"{_line(node)}:definition:{node.name}")
        elif isinstance(node, ast.arg) and node.arg in PRIVATE_AUTHORITY_NAMES:
            violations.append(f"{_line(node)}:argument:{node.arg}")
        elif (
            isinstance(node, ast.Name)
            and isinstance(node.ctx, ast.Store)
            and node.id in PRIVATE_AUTHORITY_NAMES
        ):
            violations.append(f"{_line(node)}:binding:{node.id}")
        elif isinstance(node, ast.alias):
            local_name = node.asname or node.name.rsplit(".", 1)[-1]
            if local_name not in PRIVATE_AUTHORITY_NAMES:
                continue
            parent = parents.get(node)
            is_exact_allowed_import = (
                isinstance(parent, ast.ImportFrom)
                and parent.module == "src.core.recursive_stark_admission"
                and node.name in PRIVATE_ADAPTER_CALLS
                and node.asname is None
            )
            if not is_exact_allowed_import:
                violations.append(f"{_line(node)}:import:{local_name}")
    return violations


def _line(node: ast.AST) -> int:
    return int(getattr(node, "lineno", 0))


def _class(tree: ast.Module, name: str) -> ast.ClassDef:
    for node in tree.body:
        if isinstance(node, ast.ClassDef) and node.name == name:
            return node
    raise AssertionError(f"missing class {name}")


def _method(class_node: ast.ClassDef, name: str) -> ast.FunctionDef:
    for node in class_node.body:
        if isinstance(node, ast.FunctionDef) and node.name == name:
            return node
    raise AssertionError(f"missing method {name}")


def _function(tree: ast.Module, name: str) -> ast.FunctionDef:
    for node in tree.body:
        if isinstance(node, ast.FunctionDef) and node.name == name:
            return node
    raise AssertionError(f"missing function {name}")


def _parent_map(tree: ast.AST) -> dict[ast.AST, ast.AST]:
    return {
        child: parent
        for parent in ast.walk(tree)
        for child in ast.iter_child_nodes(parent)
    }
