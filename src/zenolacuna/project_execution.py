"""Stdlib-only pre-import sealing for the fresh project CLI worker.

This module must be loaded by the source script before application imports.
It does not retroactively authenticate modules in an existing Python process.
"""

import ast
import hashlib
import sys
from pathlib import Path

_SEAL_ATTRIBUTE = "_zenolacuna_source_execution_seal"
_MAX_FILES = 2048
_MAX_BYTES = 32 * 1024 * 1024


def _literal_paths(root: Path, name: str, constant: str) -> tuple[str, ...]:
    tree = ast.parse((root / name).read_bytes(), filename=name)
    for statement in tree.body:
        value: ast.expr | None
        if isinstance(statement, ast.Assign):
            names = [target.id for target in statement.targets if isinstance(target, ast.Name)]
            value = statement.value
        elif isinstance(statement, ast.AnnAssign) and isinstance(statement.target, ast.Name):
            names, value = [statement.target.id], statement.value
        else:
            continue
        if constant in names and value is not None:
            paths = ast.literal_eval(value)
            if type(paths) is tuple and all(type(p) is str and not Path(p).is_absolute()
                                           and ".." not in Path(p).parts for p in paths):
                return paths
    raise ValueError("invalid source manifest")


def _module_files(root: Path, parts: tuple[str, ...]) -> tuple[str, ...]:
    if not parts or parts[0] not in ("src", "tools"):
        return ()
    paths = [Path(*parts[:index]) / "__init__.py" for index in range(1, len(parts) + 1)]
    paths.append(Path(*parts).with_suffix(".py"))
    return tuple(path.as_posix() for path in paths if (root / path).is_file())


def execution_manifest(root: Path) -> tuple[tuple[str, str], ...]:
    """Conservatively seal local static imports, including package initializers.

    Function-local and type-checking imports are included. Dynamic imports that
    escape this set reject on the post-import check; they never extend a seal.
    """
    paths = set(_literal_paths(root, "src/zenolacuna/project_bindings.py", "CHECKER_PATHS"))
    paths.update(_literal_paths(root, "src/zenolacuna/signal_migration.py", "SOURCE_PATHS"))
    pending, hashes = list(paths), {}
    resolved: dict[tuple[str, ...], tuple[str, ...]] = {}
    total = 0

    def include(parts: tuple[str, ...]) -> None:
        if parts not in resolved:
            resolved[parts] = _module_files(root, parts)
        for name in resolved[parts]:
            if name not in paths:
                paths.add(name)
                pending.append(name)

    while pending:
        if len(paths) > _MAX_FILES:
            raise ValueError("source import budget")
        name = pending.pop()
        raw = (root / name).read_bytes()
        total += len(raw)
        if total > _MAX_BYTES:
            raise ValueError("source byte budget")
        hashes[name] = hashlib.sha256(raw).hexdigest()
        path = Path(name)
        include(path.with_suffix("").parts)
        package = path.parent.parts
        for node in ast.walk(ast.parse(raw, filename=name)):
            if isinstance(node, ast.Import):
                for alias in node.names:
                    include(tuple(alias.name.split(".")))
            elif isinstance(node, ast.ImportFrom):
                prefix = package[:len(package) - node.level + 1] if node.level else ()
                parts = prefix + (tuple(node.module.split(".")) if node.module else ())
                include(parts)
                for alias in node.names:
                    if alias.name != "*":
                        include(parts + tuple(alias.name.split(".")))
    return tuple(sorted(hashes.items()))


def current_execution_manifest(root: Path) -> tuple[tuple[str, str], ...]:
    seal = getattr(sys, _SEAL_ATTRIBUTE, None)
    if seal is None:
        return execution_manifest(root)
    return tuple((name, hashlib.sha256((root / name).read_bytes()).hexdigest()) for name, _ in seal)


def check_imported_sources(root: Path, manifest: tuple[tuple[str, str], ...]) -> None:
    """Every loaded local source must already have been sealed before import."""
    allowed = {name for name, _ in manifest}
    for module_name, module in tuple(sys.modules.items()):
        local_name = module_name in ("src", "tools") or module_name.startswith(("src.", "tools."))
        filename = getattr(module, "__file__", None)
        if type(filename) is not str:
            if local_name:
                # A namespace package is allowed only at its canonical local
                # directory; it cannot add an outside search path.
                expected = root.joinpath(*module_name.split("."))
                locations = getattr(module, "__path__", ())
                if list(locations) != [str(expected)] or expected.resolve() != expected or not expected.is_dir():
                    raise ValueError("unsealed namespace import")
            continue
        path = Path(filename).absolute()
        try:
            relative = path.relative_to(root).as_posix()
        except ValueError:
            if local_name:
                raise ValueError("outside local module origin") from None
            continue
        if relative not in allowed and not local_name and sys.prefix != sys.base_prefix:
            # A repository-local venv belongs to the explicitly trusted Python
            # dependency environment, not to the application source tree.
            if path.is_relative_to(Path(sys.prefix).resolve()):
                continue
        if relative not in allowed or path.resolve() != path or path.suffix != ".py" or not path.is_file():
            raise ValueError("unsealed local import")


def seal_before_import(root: Path) -> tuple[tuple[str, str], ...]:
    if any(name in sys.modules for name in ("src.zenolacuna.model", "src.zenolacuna.project",
                                            "src.integration.autotrader_signals")):
        raise ValueError("application already imported")
    if not sys.flags.isolated or not sys.dont_write_bytecode or sys.pycache_prefix is None:
        raise ValueError("source-only worker required")
    prefix = Path(sys.pycache_prefix)
    if prefix.exists() and any(prefix.rglob("*.pyc")):
        raise ValueError("empty bytecode cache required")
    manifest = execution_manifest(root)
    setattr(sys, _SEAL_ATTRIBUTE, manifest)
    return manifest


def execution_context() -> str:
    return "FRESH_SOURCE_PROCESS" if hasattr(sys, _SEAL_ATTRIBUTE) else "IMMUTABLE_HOST_PREMISE"


def check_execution_seal(root: Path) -> None:
    seal = getattr(sys, _SEAL_ATTRIBUTE, None)
    if seal is not None:
        if current_execution_manifest(root) != seal:
            raise ValueError("pre-import source drift")
        check_imported_sources(root, seal)
