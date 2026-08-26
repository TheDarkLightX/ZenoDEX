"""Close the decoded launcher set over static import and dispatch edges.

Every edge the decoder cannot resolve becomes a typed closure gap, so an
unmodelled dispatch shape widens a reported gap set instead of silently
shrinking the scanned surface.

The result is an inventory aid.  Static edges do not establish runtime
reachability, sole-publisher mediation, or cross-language coverage.
"""

from __future__ import annotations

import ast
import hashlib
import re
from dataclasses import dataclass
from pathlib import Path, PurePosixPath

from tools.m6_value_sinks.launchers import (
    INSTALL_SCRIPT,
    ClosureFindingV2,
    DeployedEntrypointV2,
    RepositorySnapshotV2,
    canonical_relative_path,
    classify_unscannable_candidate,
    contained_file,
    derive_deployed_entrypoints,
    read_bounded_text,
    safe_relative,
)
from tools.m6_value_sinks.operations import (
    EXECUTABLE_MODULE_FUNCTIONS,
    callable_expression_may_target_executable,
    resolve_callable_expression,
    resolve_import_bindings,
    unresolved_receiver_writer_provenance,
    unresolved_writer_provenance,
)

MAX_CLOSURE_MODULES = 4096
MAX_SOURCE_BYTES = 4 * 1024 * 1024
MAX_AST_NODES = 400_000

_DOTTED_MODULE_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*\Z")
_PYTHON_COMMAND_RE = re.compile(r"(?:\A|/)python[0-9.]*\Z")

_SUBPROCESS_CALLERS = frozenset({"run", "Popen", "call", "check_call", "check_output"})
_DYNAMIC_IMPORT_ATTRIBUTES = frozenset({"exec_module", "import_module", "load_module"})
_EXECUTABLE_MODULE_ATTRIBUTES: dict[str, dict[str, str]] = {
    "asyncio": {
        "create_subprocess_exec": "asyncio_subprocess_dispatch",
        "create_subprocess_shell": "asyncio_subprocess_dispatch",
    },
    "os": {
        name: "os_process_dispatch"
        for name in {
            "execl",
            "execle",
            "execlp",
            "execlpe",
            "execv",
            "execve",
            "execvp",
            "execvpe",
            "popen",
            "posix_spawn",
            "posix_spawnp",
            "spawnl",
            "spawnle",
            "spawnlp",
            "spawnlpe",
            "spawnv",
            "spawnve",
            "spawnvp",
            "spawnvpe",
            "startfile",
            "system",
        }
    },
    "runpy": {
        "run_module": "runpy_run_module",
        "run_path": "runpy_run_path",
    },
}


@dataclass(frozen=True, slots=True)
class DeploymentClosureV2:
    entrypoints: tuple[DeployedEntrypointV2, ...]
    modules: tuple[str, ...]
    module_digests: tuple[tuple[str, str], ...]
    unscanned_modules: tuple[str, ...]
    observed_gaps: tuple[tuple[str, str], ...]
    findings: tuple[ClosureFindingV2, ...]


def _module_candidates(root: Path | RepositorySnapshotV2, module: str) -> tuple[Path, ...]:
    parts = module.split(".")
    # CPython's FileFinder selects a package directory before a same-named
    # source module.  Reversing this order scans code Python will not import and
    # omits the package initializer that actually runs.
    return (root.joinpath(*parts, "__init__.py"), root.joinpath(*parts).with_suffix(".py"))


@dataclass(frozen=True, slots=True)
class ModuleResolutionV2:
    """A dotted module resolved into its parent chain and its leaf.

    The two are separate because a present parent chain with an absent leaf is
    not a resolved module; conflating them would let the last initializer stand
    in for code that does not exist.
    """

    parents: tuple[Path, ...]
    leaf: Path | None
    leaf_reason: str | None
    parent_reasons: tuple[str, ...]

    def scannable(self) -> tuple[Path, ...]:
        return (*self.parents, self.leaf) if self.leaf is not None else self.parents


def _parent_package_initializers(
    root: Path | RepositorySnapshotV2, module: str
) -> tuple[tuple[Path, ...], tuple[str, ...]]:
    """Return the ordered ``__init__.py`` chain executed before the leaf.

    Importing ``a.b.c`` runs ``a/__init__.py`` then ``a/b/__init__.py`` before
    the leaf, and those initializers hold writers and dynamic dispatch of their
    own.  An initializer that exists but cannot be scanned is reported rather
    than skipped.
    """

    parts = module.split(".")
    chain: list[Path] = []
    reasons: list[str] = []
    for depth in range(1, len(parts)):
        candidate = root.joinpath(*parts[:depth], "__init__.py")
        initializer = contained_file(candidate, root)
        if initializer is not None:
            chain.append(initializer)
            continue
        reason = classify_unscannable_candidate(candidate, root)
        if reason is not None:
            reasons.append(reason)
    return tuple(chain), tuple(reasons)


def resolve_module_candidate(
    root: Path | RepositorySnapshotV2, module: str
) -> ModuleResolutionV2:
    """Resolve a dotted module to its parent-initializer chain and leaf."""

    if _DOTTED_MODULE_RE.fullmatch(module) is None:
        return ModuleResolutionV2((), None, None, ())
    parents, parent_reasons = _parent_package_initializers(root, module)
    reason: str | None = None
    for candidate in _module_candidates(root, module):
        contained = contained_file(candidate, root)
        if contained is not None:
            return ModuleResolutionV2(parents, contained, None, parent_reasons)
        reason = reason or classify_unscannable_candidate(candidate, root)
    return ModuleResolutionV2(parents, None, reason, parent_reasons)


def resolve_module(root: Path | RepositorySnapshotV2, module: str) -> Path | None:
    """Resolve a dotted module to the leaf regular file inside the exact root."""

    return resolve_module_candidate(root, module).leaf


def resolve_module_execution_candidate(
    root: Path | RepositorySnapshotV2, module: str
) -> ModuleResolutionV2:
    """Resolve the code executed by ``python -m module``.

    A source module executes directly.  A package executes its ``__init__.py``
    and then its contained ``__main__.py``; an initializer alone is therefore
    not a complete ``-m`` target.
    """

    imported = resolve_module_candidate(root, module)
    leaf = imported.leaf
    if leaf is None or leaf.name != "__init__.py":
        return imported
    main = leaf.parent / "__main__.py"
    contained = contained_file(main, root)
    if contained is not None:
        return ModuleResolutionV2(
            parents=(*imported.parents, leaf),
            leaf=contained,
            leaf_reason=None,
            parent_reasons=imported.parent_reasons,
        )
    return ModuleResolutionV2(
        parents=(*imported.parents, leaf),
        leaf=None,
        leaf_reason=classify_unscannable_candidate(main, root),
        parent_reasons=imported.parent_reasons,
    )


def _package_parts(relative: str) -> tuple[str, ...]:
    path = PurePosixPath(relative)
    return path.parent.parts if path.name != "__init__.py" else path.parent.parts


def _relative_import_targets(node: ast.ImportFrom, relative: str) -> tuple[str, ...]:
    """Resolve a package-relative ImportFrom against the importing module."""

    package = _package_parts(relative)
    if node.level > len(package):
        return ()
    base = package[: len(package) - (node.level - 1)] if node.level > 1 else package
    prefix = list(base) + (node.module.split(".") if node.module else [])
    if not prefix:
        return ()
    dotted = ".".join(prefix)
    return (dotted, *(f"{dotted}.{alias.name}" for alias in node.names))


def _absolute_import_targets(node: ast.ImportFrom) -> tuple[str, ...]:
    if not node.module:
        return ()
    return (node.module, *(f"{node.module}.{alias.name}" for alias in node.names))


def _import_targets(node: ast.AST, relative: str) -> tuple[str, ...]:
    if isinstance(node, ast.Import):
        return tuple(alias.name for alias in node.names)
    if not isinstance(node, ast.ImportFrom):
        return ()
    if node.level == 0:
        return _absolute_import_targets(node)
    return _relative_import_targets(node, relative)


def _imported_modules(tree: ast.Module, relative: str) -> tuple[str, ...]:
    modules: set[str] = set()
    for node in ast.walk(tree):
        modules.update(_import_targets(node, relative))
    return tuple(sorted(modules))


def _string_constants(node: ast.AST) -> tuple[str, ...]:
    return tuple(
        child.value
        for child in ast.walk(node)
        if isinstance(child, ast.Constant) and isinstance(child.value, str)
    )


def _simple_assignment_edges(
    tree: ast.Module,
) -> tuple[tuple[tuple[str, str], ...], tuple[tuple[str, str, str], ...]]:
    """Return ``target = source`` and ``target = base.attribute`` alias edges."""

    names: list[tuple[str, str]] = []
    attributes: list[tuple[str, str, str]] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Assign):
            targets = [target.id for target in node.targets if isinstance(target, ast.Name)]
            value = node.value
        elif isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name) and node.value is not None:
            targets = [node.target.id]
            value = node.value
        else:
            continue
        if isinstance(value, ast.Name):
            names.extend((target, value.id) for target in targets)
        elif isinstance(value, ast.Attribute) and isinstance(value.value, ast.Name):
            attributes.extend((target, value.value.id, value.attr) for target in targets)
    return tuple(names), tuple(attributes)


def _propagate_callable_aliases(
    tree: ast.Module,
    module_seeds: set[str],
    direct_seeds: set[str],
    attributes: frozenset[str],
) -> tuple[frozenset[str], frozenset[str]]:
    """Propagate module and callable aliases to a monotone fixpoint."""

    modules = set(module_seeds)
    direct = set(direct_seeds)
    name_edges, attribute_edges = _simple_assignment_edges(tree)
    changed = True
    while changed:
        changed = False
        for target, source in name_edges:
            if source in modules and target not in modules:
                modules.add(target)
                changed = True
            if source in direct and target not in direct:
                direct.add(target)
                changed = True
        for target, base, attribute in attribute_edges:
            if base in modules and attribute in attributes and target not in direct:
                direct.add(target)
                changed = True
    return frozenset(modules), frozenset(direct)


def _subprocess_bindings(tree: ast.Module) -> tuple[frozenset[str], frozenset[str]]:
    """Bind names for ``subprocess`` and for its runners imported directly."""

    module_seeds: set[str] = set()
    direct_seeds: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            module_seeds.update(alias.asname or alias.name for alias in node.names if alias.name == "subprocess")
        elif isinstance(node, ast.ImportFrom) and node.level == 0 and node.module == "subprocess":
            direct_seeds.update(
                alias.asname or alias.name for alias in node.names if alias.name in _SUBPROCESS_CALLERS
            )
    return _propagate_callable_aliases(tree, module_seeds, direct_seeds, _SUBPROCESS_CALLERS)


def _is_subprocess_call(call: ast.Call, modules: frozenset[str], direct: frozenset[str]) -> bool:
    function = call.func
    if isinstance(function, ast.Attribute):
        base = function.value
        return isinstance(base, ast.Name) and base.id in modules and function.attr in _SUBPROCESS_CALLERS
    return isinstance(function, ast.Name) and function.id in direct


def _precise_callable_consumption(
    node: ast.expr,
    parent: ast.AST | None,
    direct: frozenset[str],
) -> bool:
    if isinstance(parent, ast.Call) and parent.func is node:
        return True
    if isinstance(parent, ast.Assign) and parent.value is node:
        targets = [target for target in parent.targets if isinstance(target, ast.Name)]
        return bool(targets) and len(targets) == len(parent.targets) and all(
            target.id in direct for target in targets
        )
    if isinstance(parent, ast.AnnAssign) and parent.value is node:
        return isinstance(parent.target, ast.Name) and parent.target.id in direct
    return False


def _unresolved_subprocess_provenance(tree: ast.Module) -> bool:
    """Detect subprocess dispatch that leaves the closed direct-call grammar."""

    modules, direct = _subprocess_bindings(tree)
    parents = {
        id(child): parent
        for parent in ast.walk(tree)
        for child in ast.iter_child_nodes(parent)
    }
    for node in ast.walk(tree):
        parent = parents.get(id(node))
        if isinstance(node, ast.Attribute):
            base = node.value
            if (
                isinstance(base, ast.Name)
                and base.id in modules
                and node.attr in _SUBPROCESS_CALLERS
                and not _precise_callable_consumption(node, parent, direct)
            ):
                return True
        elif isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load):
            if node.id in direct and not _precise_callable_consumption(node, parent, direct):
                return True
            if node.id not in modules:
                continue
            if isinstance(parent, ast.Attribute) and parent.value is node:
                continue
            return True
    return False


def _argv_expression(call: ast.Call) -> ast.expr | None:
    if call.args:
        return call.args[0]
    for keyword in call.keywords:
        if keyword.arg == "args":
            return keyword.value
    return None


def _is_python_executable(element: ast.expr) -> bool:
    """Recognize ``sys.executable`` as a Python interpreter head."""

    return (
        isinstance(element, ast.Attribute)
        and element.attr == "executable"
        and isinstance(element.value, ast.Name)
        and element.value.id == "sys"
    )


@dataclass(frozen=True, slots=True)
class ArgvDecodeV2:
    """One structurally decoded argv expression."""

    modules: tuple[str, ...]
    scripts: tuple[str, ...]
    status: str
    source_bound: bool


def _is_source_bound(interpreter: str, target: str) -> bool:
    """Report whether the executed code is fixed by the source alone.

    A bare ``python3`` is resolved through PATH, ``sys.executable`` is whatever
    interpreter happens to be running, and both ``-m`` and a relative script are
    resolved against the working directory.  None of those are fixed by the
    call site, so the decoder records a gap while still scanning the local
    candidate.
    """

    return interpreter.startswith("/") and target.startswith("/")


def _decode_argv(call: ast.Call, root: Path | RepositorySnapshotV2) -> ArgvDecodeV2:
    """Structurally decode one argv expression into modelled dispatch.

    Full literal decoding is not modelled dispatch: ``["bash", "writer.sh"]``
    and ``["python3", "-c", ...]`` are entirely literal yet reach code this
    scanner does not model, so they report ``UNSUPPORTED`` rather than
    resolving.  A resolved target still reports whether the source alone fixes
    the interpreter and the executed path.
    """

    argv = _argv_expression(call)
    if not isinstance(argv, (ast.List, ast.Tuple)) or not argv.elts:
        return ArgvDecodeV2((), (), "UNRESOLVED", source_bound=False)
    literals: list[str] = []
    for index, element in enumerate(argv.elts):
        if isinstance(element, ast.Constant) and isinstance(element.value, str):
            literals.append(element.value)
        elif index == 0 and _is_python_executable(element):
            literals.append("python3")
        else:
            return ArgvDecodeV2((), (), "UNRESOLVED", source_bound=False)
    if _PYTHON_COMMAND_RE.search(literals[0]) is None:
        return _unsupported()
    rest = literals[1:]
    if not rest:
        return _unsupported()
    if rest[0] == "-m":
        if len(rest) < 2 or _DOTTED_MODULE_RE.fullmatch(rest[1]) is None:
            return _unsupported()
        if resolve_module_execution_candidate(root, rest[1]).leaf is None:
            return ArgvDecodeV2((rest[1],), (), "MISSING_MODULE", source_bound=False)
        # ``-m`` is resolved through sys.path, never fixed by the call site.
        return ArgvDecodeV2((rest[1],), (), "RESOLVED", source_bound=False)
    if rest[0].endswith(".py") and canonical_relative_path(rest[0]) is not None:
        if contained_file(root / rest[0], root) is None:
            return _unsupported()
        return ArgvDecodeV2(
            (), (rest[0],), "RESOLVED", source_bound=_is_source_bound(literals[0], rest[0])
        )
    return _unsupported()


def _unsupported() -> ArgvDecodeV2:
    return ArgvDecodeV2((), (), "UNSUPPORTED", source_bound=False)


def _dispatch_edges(
    tree: ast.Module,
    *,
    module_path: Path,
    root: Path | RepositorySnapshotV2,
    relative: str,
) -> tuple[tuple[Path, ...], tuple[tuple[str, str], ...]]:
    """Resolve script and module dispatch, recording undecodable dispatch as a gap."""

    targets: set[Path] = set()
    gaps: set[tuple[str, str]] = set()
    bases = (module_path.parent, root)

    def _add_script(value: str) -> None:
        reason: str | None = None
        for base in bases:
            candidate = contained_file(base / value, root)
            if candidate is not None:
                targets.add(candidate)
                return
            reason = reason or classify_unscannable_candidate(base / value, root)
        if reason is not None:
            gaps.add((relative, f"dispatch_target_{reason}"))

    for value in _string_constants(tree):
        if value.endswith(".py") and canonical_relative_path(value) is not None:
            _add_script(value)
    modules, direct = _subprocess_bindings(tree)
    for node in ast.walk(tree):
        if not isinstance(node, ast.Call) or not _is_subprocess_call(node, modules, direct):
            continue
        decoded = _decode_argv(node, root)
        for module in decoded.modules:
            # ``python -m a.b`` runs ``a/__init__.py`` first, so the dispatch
            # seeds the ordered chain rather than the leaf alone.
            resolution = resolve_module_execution_candidate(root, module)
            targets.update(resolution.scannable())
            if resolution.leaf_reason is not None:
                gaps.add((relative, f"import_target_{resolution.leaf_reason}"))
            for reason in resolution.parent_reasons:
                gaps.add((relative, f"package_initializer_{reason}"))
        for script in decoded.scripts:
            _add_script(script)
        if decoded.status == "UNRESOLVED":
            gaps.add((relative, "unresolved_subprocess_dispatch"))
        elif decoded.status == "UNSUPPORTED":
            gaps.add((relative, "unsupported_subprocess_dispatch"))
        elif decoded.status == "MISSING_MODULE":
            gaps.add((relative, "dispatch_module_absent"))
        elif not decoded.source_bound:
            # The local candidate is still scanned; the gap records that PATH and
            # the working directory decide what actually executes.
            gaps.add((relative, "unbound_dispatch_environment"))
    return tuple(sorted(targets)), tuple(sorted(gaps))


def _dynamic_import_alias_names(tree: ast.Module) -> frozenset[str]:
    """Bind names that reach dynamic import machinery without an attribute call.

    ``from importlib import import_module as load`` and
    ``load = importlib.import_module`` both hide the attribute form.
    """

    module_seeds: set[str] = set()
    direct_seeds: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            module_seeds.update(
                alias.asname or alias.name
                for alias in node.names
                if alias.name in {"importlib", "importlib.util"}
            )
        elif isinstance(node, ast.ImportFrom) and node.level == 0 and node.module in {"importlib", "importlib.util"}:
            direct_seeds.update(
                alias.asname or alias.name
                for alias in node.names
                if alias.name in _DYNAMIC_IMPORT_ATTRIBUTES
            )
    _, direct = _propagate_callable_aliases(
        tree, module_seeds, direct_seeds, _DYNAMIC_IMPORT_ATTRIBUTES
    )
    return direct


def _dynamic_import_gaps(tree: ast.Module, relative: str) -> tuple[tuple[str, str], ...]:
    gaps: set[tuple[str, str]] = set()
    aliases = _dynamic_import_alias_names(tree)
    for node in ast.walk(tree):
        if not isinstance(node, ast.Call):
            continue
        function = node.func
        if isinstance(function, ast.Name):
            if function.id == "__import__":
                gaps.add((relative, "__import__"))
            elif function.id in aliases:
                gaps.add((relative, "dynamic_import_alias"))
        elif isinstance(function, ast.Attribute) and function.attr in _DYNAMIC_IMPORT_ATTRIBUTES:
            gaps.add((relative, function.attr))
    return tuple(sorted(gaps))


def _module_callable_bindings(
    tree: ast.Module, module: str, attributes: frozenset[str]
) -> tuple[frozenset[str], frozenset[str]]:
    module_seeds: set[str] = set()
    direct_seeds: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                if alias.name == module:
                    module_seeds.add(alias.asname or alias.name)
                elif module == "os" and alias.name.startswith("os.") and alias.asname is None:
                    module_seeds.add("os")
        elif isinstance(node, ast.ImportFrom) and node.level == 0 and node.module == module:
            direct_seeds.update(
                alias.asname or alias.name
                for alias in node.names
                if alias.name in attributes
            )
    return _propagate_callable_aliases(tree, module_seeds, direct_seeds, attributes)


def _executable_edge_gaps(
    tree: ast.Module, relative: str
) -> tuple[tuple[str, str], ...]:
    """Keep every recognized executable-code edge visible as a typed gap."""

    gaps: set[tuple[str, str]] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.ImportFrom) and any(alias.name == "*" for alias in node.names):
            gaps.add((relative, "unresolved_star_import"))

    bindings = resolve_import_bindings(tree)
    all_direct: set[str] = set(bindings.executable_aliases)
    all_modules: set[str] = {
        name for name, module in bindings.module_aliases.items() if module == "builtins"
    }
    executable_attributes: set[tuple[str, str]] = set()
    executable_attributes.update(
        (name, attribute)
        for name in all_modules
        for module, attribute in EXECUTABLE_MODULE_FUNCTIONS
        if module == "builtins"
    )
    for node in ast.walk(tree):
        if not isinstance(node, ast.Call):
            continue
        resolution = resolve_callable_expression(node.func, bindings)
        target = resolution.target
        if target is not None and target in EXECUTABLE_MODULE_FUNCTIONS:
            gaps.add((relative, EXECUTABLE_MODULE_FUNCTIONS[target]))
        elif callable_expression_may_target_executable(node.func, bindings):
            gaps.add((relative, "unresolved_executable_provenance"))

    executable_modules: set[str] = set()
    for module, mapping in _EXECUTABLE_MODULE_ATTRIBUTES.items():
        attributes = frozenset(mapping)
        modules, direct = _module_callable_bindings(tree, module, attributes)
        all_modules.update(modules)
        all_direct.update(direct)
        executable_attributes.update((name, attribute) for name in modules for attribute in attributes)
        executable_modules.update(modules)
        for node in ast.walk(tree):
            if not isinstance(node, ast.Call):
                continue
            function = node.func
            if isinstance(function, ast.Attribute):
                base = function.value
                if isinstance(base, ast.Name) and base.id in modules and function.attr in mapping:
                    gaps.add((relative, mapping[function.attr]))
            elif isinstance(function, ast.Name) and function.id in direct:
                mechanisms = {
                    mapping[alias.name]
                    for imported in ast.walk(tree)
                    if isinstance(imported, ast.ImportFrom)
                    and imported.level == 0
                    and imported.module == module
                    for alias in imported.names
                    if (alias.asname or alias.name) == function.id and alias.name in mapping
                }
                gaps.update((relative, mechanism) for mechanism in mechanisms or set(mapping.values()))
    parents = {
        id(child): parent
        for parent in ast.walk(tree)
        for child in ast.iter_child_nodes(parent)
    }
    for node in ast.walk(tree):
        if not isinstance(node, ast.Call) or not isinstance(node.func, ast.Name):
            continue
        if node.func.id != "getattr" or not node.args:
            continue
        base = node.args[0]
        if isinstance(base, ast.Name) and base.id in executable_modules:
            gaps.add((relative, "unresolved_executable_provenance"))
    precise_direct = frozenset(all_direct)

    def closed_reflective_module_use(node: ast.Name, parent: ast.AST | None) -> bool:
        expression: ast.expr | None = None
        if (
            isinstance(parent, ast.Call)
            and isinstance(parent.func, ast.Name)
            and parent.func.id == "getattr"
            and parent.args
            and parent.args[0] is node
        ):
            expression = parent
        elif (
            isinstance(parent, ast.Call)
            and isinstance(parent.func, ast.Name)
            and parent.func.id == "vars"
            and len(parent.args) == 1
            and parent.args[0] is node
        ):
            grandparent = parents.get(id(parent))
            if isinstance(grandparent, ast.Subscript) and grandparent.value is parent:
                expression = grandparent
        return (
            expression is not None
            and resolve_callable_expression(expression, bindings).target is not None
        )

    for node in ast.walk(tree):
        parent = parents.get(id(node))
        if isinstance(node, (ast.Attribute, ast.Subscript, ast.Call)):
            resolution = resolve_callable_expression(node, bindings)
            if (
                resolution.target in EXECUTABLE_MODULE_FUNCTIONS
                and not _precise_callable_consumption(node, parent, precise_direct)
            ):
                gaps.add((relative, "unresolved_executable_provenance"))
        if isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name):
            if (node.value.id, node.attr) not in executable_attributes:
                continue
            if not _precise_callable_consumption(node, parent, precise_direct):
                gaps.add((relative, "unresolved_executable_provenance"))
        elif isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load):
            if node.id in all_direct and not _precise_callable_consumption(
                node, parent, precise_direct
            ):
                gaps.add((relative, "unresolved_executable_provenance"))
            if node.id not in all_modules:
                continue
            if isinstance(parent, ast.Attribute) and parent.value is node:
                continue
            if closed_reflective_module_use(node, parent):
                continue
            if isinstance(parent, ast.Assign) and parent.value is node:
                targets = [target.id for target in parent.targets if isinstance(target, ast.Name)]
                if targets and len(targets) == len(parent.targets) and all(
                    target in all_modules for target in targets
                ):
                    continue
            gaps.add((relative, "unresolved_executable_provenance"))
    return tuple(sorted(gaps))


def _entrypoint_seeds(
    root: Path | RepositorySnapshotV2, entrypoints: tuple[DeployedEntrypointV2, ...]
) -> tuple[list[Path], list[tuple[str, str]]]:
    """Seed the closure from decoded launchers.

    ``python -m a.b`` executes ``a/__init__.py`` before ``a/b``, so a module
    launcher seeds the whole ordered chain rather than the leaf alone.
    """

    seeds: list[Path] = []
    gaps: list[tuple[str, str]] = []
    for entrypoint in entrypoints:
        if not entrypoint.target.startswith("-m "):
            contained = contained_file(root / entrypoint.target, root)
            if contained is not None:
                seeds.append(contained)
            continue
        origin = (
            entrypoint.entrypoint_id
            if canonical_relative_path(entrypoint.entrypoint_id) == entrypoint.entrypoint_id
            else INSTALL_SCRIPT
        )
        resolution = resolve_module_execution_candidate(root, entrypoint.target[3:])
        seeds.extend(resolution.scannable())
        if resolution.leaf_reason is not None:
            gaps.append((origin, f"import_target_{resolution.leaf_reason}"))
        if resolution.leaf is None and resolution.leaf_reason is None:
            gaps.append((origin, "dispatch_module_absent"))
        gaps.extend((origin, f"package_initializer_{reason}") for reason in resolution.parent_reasons)
    return seeds, gaps


@dataclass(frozen=True, slots=True)
class _ModuleStepV2:
    """Outcome of visiting one reachable module."""

    digest: str | None
    edges: tuple[Path, ...]
    gaps: tuple[tuple[str, str], ...]


def _module_import_step(
    tree: ast.Module, relative: str, root: Path | RepositorySnapshotV2
) -> tuple[tuple[Path, ...], tuple[tuple[str, str], ...]]:
    edges: list[Path] = []
    gaps: list[tuple[str, str]] = []
    for module in _imported_modules(tree, relative):
        resolution = resolve_module_candidate(root, module)
        edges.extend(resolution.scannable())
        if resolution.leaf_reason is not None:
            gaps.append((relative, f"import_target_{resolution.leaf_reason}"))
        for reason in resolution.parent_reasons:
            gaps.append((relative, f"package_initializer_{reason}"))
    return tuple(edges), tuple(gaps)


def _scan_closure_module(
    current: Path, relative: str, root: Path | RepositorySnapshotV2
) -> _ModuleStepV2:
    """Read, parse, and expand one reachable module inside the ceilings.

    A ``None`` digest marks acknowledged incompleteness: the module is reachable
    but unscannable, which is never the same as an absence of writers.
    """

    text, _ = read_bounded_text(current, MAX_SOURCE_BYTES, root=root)
    if text is None:
        return _ModuleStepV2(None, (), ((relative, "source_unscannable"),))
    if isinstance(root, RepositorySnapshotV2):
        root.resource_meter.claim_source_bytes(len(text.encode("utf-8")))
    try:
        tree = ast.parse(text, filename=str(current))
    except (SyntaxError, ValueError, RecursionError):
        return _ModuleStepV2(None, (), ((relative, "source_unparsable"),))
    ast_nodes = sum(1 for _ in ast.walk(tree))
    if ast_nodes > MAX_AST_NODES:
        return _ModuleStepV2(None, (), ((relative, "ast_node_ceiling_exceeded"),))
    if isinstance(root, RepositorySnapshotV2):
        root.resource_meter.claim_ast_nodes(ast_nodes)
    import_edges, import_gaps = _module_import_step(tree, relative, root)
    dispatch_edges, dispatch_gaps = _dispatch_edges(
        tree, module_path=current, root=root, relative=relative
    )
    return _ModuleStepV2(
        digest=hashlib.sha256(text.encode("utf-8")).hexdigest(),
        edges=import_edges + dispatch_edges,
        gaps=(
            _dynamic_import_gaps(tree, relative)
            + _executable_edge_gaps(tree, relative)
            + import_gaps
            + dispatch_gaps
            + (((relative, "unresolved_subprocess_dispatch"),) if _unresolved_subprocess_provenance(tree) else ())
            + (((relative, "unresolved_writer_provenance"),) if unresolved_writer_provenance(tree) else ())
            + (((relative, "unresolved_receiver_writer_provenance"),) if unresolved_receiver_writer_provenance(tree) else ())
        ),
    )


def derive_python_deployment_closure(
    root: Path | RepositorySnapshotV2,
) -> DeploymentClosureV2:
    """Close the decoded launcher set over static import and dispatch edges."""

    if not isinstance(root, RepositorySnapshotV2):
        with RepositorySnapshotV2(root) as snapshot:
            closure = derive_python_deployment_closure(snapshot)
            snapshot.verify_stable()
            return closure
    root.assert_path_identity()
    entrypoints, findings, launcher_gaps = derive_deployed_entrypoints(root)
    pending, seed_gaps = _entrypoint_seeds(root, entrypoints)
    root.resource_meter.claim_closure_edges(len(pending))
    visited: dict[Path, str] = {}
    gaps: set[tuple[str, str]] = set(launcher_gaps) | set(seed_gaps)
    unscanned: set[str] = set()
    extra: list[ClosureFindingV2] = []
    seen: set[Path] = set()
    while pending:
        current = pending.pop()
        if current in seen:
            continue
        seen.add(current)
        relative = safe_relative(current, root)
        if relative is None:
            extra.append(
                ClosureFindingV2(current.name, "closure_path_escapes_repository_root", "resolution left the root")
            )
            continue
        if len(seen) > MAX_CLOSURE_MODULES:
            extra.append(ClosureFindingV2(relative, "closure_module_ceiling_exceeded", str(MAX_CLOSURE_MODULES)))
            break
        step = _scan_closure_module(current, relative, root)
        root.resource_meter.claim_closure_edges(len(step.edges))
        gaps.update(step.gaps)
        if step.digest is None:
            unscanned.add(relative)
            continue
        visited[current] = step.digest
        pending.extend(edge for edge in step.edges if edge not in seen)
    resolved_modules = {path: name for path in visited if (name := safe_relative(path, root)) is not None}
    digests = tuple(sorted((resolved_modules[path], digest) for path, digest in visited.items() if path in resolved_modules))
    closure = DeploymentClosureV2(
        entrypoints=entrypoints,
        modules=tuple(sorted(resolved_modules.values())),
        module_digests=digests,
        unscanned_modules=tuple(sorted(unscanned)),
        observed_gaps=tuple(sorted(gaps)),
        findings=tuple(sorted(list(findings) + extra)),
    )
    root.assert_path_identity()
    return closure
