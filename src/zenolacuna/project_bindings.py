"""Identity of the installed checker and explicitly selected external tools."""

import hashlib
import importlib.util
import os
import shutil
import sys
from pathlib import Path

from .filesystem import _checked_directory, _read_regular
from .model import LacunaError
from .project_execution import check_execution_seal, current_execution_manifest

ROOT = Path(__file__).resolve().parents[2]
CHECKER_PATHS = (
    "src/zenolacuna/model.py", "src/zenolacuna/codec.py", "src/zenolacuna/relations.py",
    "src/zenolacuna/questions.py", "src/zenolacuna/engine.py", "src/zenolacuna/check.py",
    "src/zenolacuna/authority.py", "src/zenolacuna/project_types.py",
    "src/zenolacuna/project_core.py", "src/zenolacuna/project_storage.py",
    "src/zenolacuna/project_bindings.py", "src/zenolacuna/project_runtime.py",
    "src/zenolacuna/project.py", "src/zenolacuna/filesystem.py",
    "src/zenolacuna/ports/programs.py", "src/zenolacuna/ports/tau.py",
    "src/tau_workbench/programs.py", "src/tau_composition/runtime.py",
    "src/integration/tau_runner.py",
    "src/zenolacuna/signal_migration.py", "src/zenolacuna/ports/signal_graph_esso.py",
    "src/zenolacuna/project_solvers.py",
    "src/zenolacuna/project_execution.py", "src/zenolacuna/project_cli.py",
    "tools/zenolacuna_project_entry.py",
    "src/zenolacuna/ports/migration_tau.py",
)


def _manifest(root: Path, paths: tuple[str, ...]) -> tuple[tuple[str, str], ...]:
    return tuple((name, hashlib.sha256(_read_regular(root / name, "CHECKER_MISSING", 1024 * 1024)).hexdigest())
                 for name in paths)


def _hash_manifest(manifest: tuple[tuple[str, str], ...]) -> str:
    return hashlib.sha256(b"zenolacuna/installed-source/v1\0" +
                          b"".join(name.encode("utf-8") + b"\0" + sha.encode("ascii") + b"\n"
                                   for name, sha in manifest)).hexdigest()


# Captured when this installed module is loaded. Later edits require a fresh
# process; current file hashes alone do not identify cached Python functions.
_LOADED = current_execution_manifest(ROOT)


def checker_fingerprint() -> str:
    try:
        check_execution_seal(ROOT)
    except ValueError as exc:
        raise LacunaError("CHECKER_DRIFT") from exc
    if tuple((name, hashlib.sha256(_read_regular(ROOT / name, "CHECKER_MISSING", 1024 * 1024)).hexdigest())
             for name, _ in _LOADED) != _LOADED:
        raise LacunaError("CHECKER_DRIFT")
    return _hash_manifest(_LOADED)


def esso_fingerprint(root: Path) -> str:
    """Pin ESSO, Z3, the selected cvc5 executable and the Python interpreter.

    Platform shared libraries and installed Python infrastructure remain host
    premises. No self-reported version or git ID substitutes for these hashes.
    """
    root = _checked_directory(root, "SOLVER_MISSING")
    package = _checked_directory(root / "ESSO", "SOLVER_MISSING")
    paths = tuple(sorted(path.relative_to(root).as_posix() for path in package.rglob("*.py")))
    if not paths or len(paths) > 2048:
        raise LacunaError("SOLVER_SOURCE_LIMIT")
    for name in paths:
        _checked_directory((root / name).parent, "SOLVER_MISSING")
    manifest = list(_manifest(root, paths))
    z3_spec = importlib.util.find_spec("z3")
    cvc5 = shutil.which(os.environ.get("CVC5_PATH", "cvc5"))
    if z3_spec is None or z3_spec.origin is None or cvc5 is None:
        raise LacunaError("SOLVER_UNKNOWN:DEPENDENCY_MISSING")
    z3_root = Path(z3_spec.origin).parent
    z3_paths = tuple(sorted(path for path in z3_root.rglob("*") if path.is_file() and (
        path.suffix in (".py", ".so", ".dll", ".dylib") or ".so." in path.name
    )))
    if not z3_paths or len(z3_paths) > 512:
        raise LacunaError("SOLVER_SOURCE_LIMIT")
    for path in z3_paths:
        manifest.append(("z3/" + path.relative_to(z3_root).as_posix(), _binary_hash(path)))
    manifest.extend((("host/cvc5", _binary_hash(Path(cvc5))), ("host/python", _binary_hash(Path(sys.executable)))))
    return _hash_manifest(tuple(manifest))


def _binary_hash(path: Path) -> str:
    path = path.resolve(strict=True)
    if not path.is_file() or path.stat().st_size > 128 * 1024 * 1024:
        raise LacunaError("SOLVER_SOURCE_LIMIT")
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        while chunk := stream.read(65536):
            digest.update(chunk)
    return digest.hexdigest()
