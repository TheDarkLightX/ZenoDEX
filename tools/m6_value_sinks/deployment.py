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
    ClosureFindingV2,
    DeployedEntrypointV2,
    canonical_relative_path,
    classify_unscannable_candidate,
    contained_file,
    derive_deployed_entrypoints,
    read_bounded_text,
    safe_relative,
)

MAX_CLOSURE_MODULES = 4096
MAX_SOURCE_BYTES = 4 * 1024 * 1024
MAX_AST_NODES = 400_000

_DOTTED_MODULE_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*\Z")
_PYTHON_COMMAND_RE = re.compile(r"(?:\A|/)python[0-9.]*\Z")

_SUBPROCESS_CALLERS = frozenset({"run", "Popen", "call", "check_call", "check_output"})
_DYNAMIC_IMPORT_ATTRIBUTES = frozenset({"exec_module", "import_module", "load_module"})


@dataclass(frozen=True, slots=True)
class DeploymentClosureV2:
    entrypoints: tuple[DeployedEntrypointV2, ...]
    modules: tuple[str, ...]
    module_digests: tuple[tuple[str, str], ...]
    unscanned_modules: tuple[str, ...]
    observed_gaps: tuple[tuple[str, str], ...]
    findings: tuple[ClosureFindingV2, ...]


def _module_candidates(root: Path, module: str) -> tuple[Path, ...]:
    parts = module.split(".")
    return (root.joinpath(*parts).with_suffix(".py"), root.joinpath(*parts, "__init__.py"))


def resolve_module_candidate(root: Path, module: str) -> tuple[Path | None, str | None]:
    """Resolve a dotted module, reporting why a local candidate was rejected."""

    if _DOTTED_MODULE_RE.fullmatch(module) is None:
        return None, None
    reason: str | None = None
    for candidate in _module_candidates(root, module):
        contained = contained_file(candidate, root)
        if contained is not None:
            return contained, None
        reason = reason or classify_unscannable_candidate(candidate, root)
    return None, reason


def resolve_module(root: Path, module: str) -> Path | None:
    """Resolve a dotted module to a regular file inside the exact root."""

    return resolve_module_candidate(root, module)[0]


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


def _subprocess_bindings(tree: ast.Module) -> tuple[frozenset[str], frozenset[str]]:
    """Bind names for ``subprocess`` and for its runners imported directly."""

    modules: set[str] = set()
    direct: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            modules.update(
                alias.asname or alias.name for alias in node.names if alias.name == "subprocess"
            )
        elif isinstance(node, ast.ImportFrom) and node.level == 0 and node.module == "subprocess":
            direct.update(
                alias.asname or alias.name
                for alias in node.names
                if alias.name in _SUBPROCESS_CALLERS
            )
    return frozenset(modules), frozenset(direct)


def _is_subprocess_call(call: ast.Call, modules: frozenset[str], direct: frozenset[str]) -> bool:
    function = call.func
    if isinstance(function, ast.Attribute):
        base = function.value
        return (
            isinstance(base, ast.Name)
            and base.id in modules
            and function.attr in _SUBPROCESS_CALLERS
        )
    return isinstance(function, ast.Name) and function.id in direct


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


def _decode_argv(call: ast.Call, root: Path) -> tuple[tuple[str, ...], tuple[str, ...], str]:
    """Structurally decode one argv expression into modelled dispatch.

    Returns dotted module targets, script targets, and a status.  Full literal
    decoding is not modelled dispatch: ``["bash", "writer.sh"]`` and
    ``["python3", "-c", ...]`` are entirely literal yet reach code this scanner
    does not model, so they report ``UNSUPPORTED`` rather than resolving.
    """

    argv = _argv_expression(call)
    if not isinstance(argv, (ast.List, ast.Tuple)) or not argv.elts:
        return (), (), "UNRESOLVED"
    literals: list[str] = []
    for index, element in enumerate(argv.elts):
        if isinstance(element, ast.Constant) and isinstance(element.value, str):
            literals.append(element.value)
        elif index == 0 and _is_python_executable(element):
            literals.append("python3")
        else:
            return (), (), "UNRESOLVED"
    if _PYTHON_COMMAND_RE.search(literals[0]) is None:
        return (), (), "UNSUPPORTED"
    rest = literals[1:]
    if not rest:
        return (), (), "UNSUPPORTED"
    if rest[0] == "-m":
        if len(rest) < 2 or _DOTTED_MODULE_RE.fullmatch(rest[1]) is None:
            return (), (), "UNSUPPORTED"
        return (
            ((rest[1],), (), "RESOLVED")
            if resolve_module(root, rest[1]) is not None
            else ((), (), "UNSUPPORTED")
        )
    if rest[0].endswith(".py") and canonical_relative_path(rest[0]) is not None:
        return (
            ((), (rest[0],), "RESOLVED")
            if contained_file(root / rest[0], root) is not None
            else ((), (), "UNSUPPORTED")
        )
    return (), (), "UNSUPPORTED"


def _dispatch_edges(
    tree: ast.Module, *, module_path: Path, root: Path, relative: str
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
        module_targets, script_targets, status = _decode_argv(node, root)
        for module in module_targets:
            resolved_module = resolve_module(root, module)
            if resolved_module is not None:
                targets.add(resolved_module)
        for script in script_targets:
            _add_script(script)
        if status == "UNRESOLVED":
            gaps.add((relative, "unresolved_subprocess_dispatch"))
        elif status == "UNSUPPORTED":
            gaps.add((relative, "unsupported_subprocess_dispatch"))
    return tuple(sorted(targets)), tuple(sorted(gaps))


def _dynamic_import_gaps(tree: ast.Module, relative: str) -> tuple[tuple[str, str], ...]:
    gaps: set[tuple[str, str]] = set()
    for node in ast.walk(tree):
        if not isinstance(node, ast.Call):
            continue
        function = node.func
        if isinstance(function, ast.Name) and function.id == "__import__":
            gaps.add((relative, "__import__"))
        elif isinstance(function, ast.Attribute) and function.attr in _DYNAMIC_IMPORT_ATTRIBUTES:
            gaps.add((relative, function.attr))
    return tuple(sorted(gaps))


def _entrypoint_seeds(root: Path, entrypoints: tuple[DeployedEntrypointV2, ...]) -> list[Path]:
    seeds: list[Path] = []
    for entrypoint in entrypoints:
        if entrypoint.target.startswith("-m "):
            resolved = resolve_module(root, entrypoint.target[3:])
            if resolved is not None:
                seeds.append(resolved)
            continue
        contained = contained_file(root / entrypoint.target, root)
        if contained is not None:
            seeds.append(contained)
    return seeds


@dataclass(frozen=True, slots=True)
class _ModuleStepV2:
    """Outcome of visiting one reachable module."""

    digest: str | None
    edges: tuple[Path, ...]
    gaps: tuple[tuple[str, str], ...]


def _module_import_step(
    tree: ast.Module, relative: str, root: Path
) -> tuple[tuple[Path, ...], tuple[tuple[str, str], ...]]:
    edges: list[Path] = []
    gaps: list[tuple[str, str]] = []
    for module in _imported_modules(tree, relative):
        resolved, reason = resolve_module_candidate(root, module)
        if resolved is not None:
            edges.append(resolved)
        elif reason is not None:
            gaps.append((relative, f"import_target_{reason}"))
    return tuple(edges), tuple(gaps)


def _scan_closure_module(current: Path, relative: str, root: Path) -> _ModuleStepV2:
    """Read, parse, and expand one reachable module inside the ceilings.

    A ``None`` digest marks acknowledged incompleteness: the module is reachable
    but unscannable, which is never the same as an absence of writers.
    """

    text, _ = read_bounded_text(current, MAX_SOURCE_BYTES)
    if text is None:
        return _ModuleStepV2(None, (), ((relative, "source_unscannable"),))
    try:
        tree = ast.parse(text, filename=str(current))
    except (SyntaxError, ValueError, RecursionError):
        return _ModuleStepV2(None, (), ((relative, "source_unparsable"),))
    if sum(1 for _ in ast.walk(tree)) > MAX_AST_NODES:
        return _ModuleStepV2(None, (), ((relative, "ast_node_ceiling_exceeded"),))
    import_edges, import_gaps = _module_import_step(tree, relative, root)
    dispatch_edges, dispatch_gaps = _dispatch_edges(
        tree, module_path=current, root=root, relative=relative
    )
    return _ModuleStepV2(
        digest=hashlib.sha256(text.encode("utf-8")).hexdigest(),
        edges=import_edges + dispatch_edges,
        gaps=_dynamic_import_gaps(tree, relative) + import_gaps + dispatch_gaps,
    )


def derive_python_deployment_closure(root: Path) -> DeploymentClosureV2:
    """Close the decoded launcher set over static import and dispatch edges."""

    root = root.resolve()
    entrypoints, findings = derive_deployed_entrypoints(root)
    pending = _entrypoint_seeds(root, entrypoints)
    visited: dict[Path, str] = {}
    gaps: set[tuple[str, str]] = set()
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
                ClosureFindingV2(
                    current.name, "closure_path_escapes_repository_root", "resolution left the root"
                )
            )
            continue
        if len(seen) > MAX_CLOSURE_MODULES:
            extra.append(
                ClosureFindingV2(
                    relative, "closure_module_ceiling_exceeded", str(MAX_CLOSURE_MODULES)
                )
            )
            break
        step = _scan_closure_module(current, relative, root)
        gaps.update(step.gaps)
        if step.digest is None:
            unscanned.add(relative)
            continue
        visited[current] = step.digest
        pending.extend(edge for edge in step.edges if edge not in seen)
    resolved_modules = {
        path: name for path in visited if (name := safe_relative(path, root)) is not None
    }
    digests = tuple(
        sorted(
            (resolved_modules[path], digest)
            for path, digest in visited.items()
            if path in resolved_modules
        )
    )
    return DeploymentClosureV2(
        entrypoints=entrypoints,
        modules=tuple(sorted(resolved_modules.values())),
        module_digests=digests,
        unscanned_modules=tuple(sorted(unscanned)),
        observed_gaps=tuple(sorted(gaps)),
        findings=tuple(sorted(list(findings) + extra)),
    )
