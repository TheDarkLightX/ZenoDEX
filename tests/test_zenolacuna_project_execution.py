"""Regression evidence for the fresh source-only project CLI worker.

A direct Python import reports ``IMMUTABLE_HOST_PREMISE``.  It does not
retroactively authenticate imports, so an in-process caller relies on immutable
installation bytes for the lifetime of that process.
"""

from __future__ import annotations

import contextlib
import json
import os
import py_compile
import runpy
import subprocess
import sys
from pathlib import Path

import pytest

_ROOT = Path(__file__).resolve().parents[1]
_ENTRY_SOURCE = _ROOT / "tools" / "zenolacuna_project_entry.py"
_EXECUTION_SOURCE = _ROOT / "src" / "zenolacuna" / "project_execution.py"
_LAUNCHER = _ROOT / "tools" / "zenolacuna.py"
_TIMESTAMP = 1_700_000_000

_BINDINGS = '''\
import hashlib
from pathlib import Path

from .model import LacunaError
from .project_execution import check_execution_seal

ROOT = Path(__file__).resolve().parents[2]
CHECKER_PATHS = (
    "src/zenolacuna/model.py",
    "src/zenolacuna/project_execution.py",
    "src/zenolacuna/project_bindings.py",
    "src/zenolacuna/project_cli.py",
    "tools/zenolacuna_project_entry.py",
)


def _manifest(root: Path) -> tuple[tuple[str, str], ...]:
    return tuple(
        (name, hashlib.sha256((root / name).read_bytes()).hexdigest())
        for name in CHECKER_PATHS
    )


_LOADED = _manifest(ROOT)


def checker_fingerprint() -> str:
    try:
        check_execution_seal(ROOT)
    except ValueError as exc:
        raise LacunaError("CHECKER_DRIFT") from exc
    if _manifest(ROOT) != _LOADED:
        raise LacunaError("CHECKER_DRIFT")
    return "fixture-checker"
'''

_MODEL = '''\
class LacunaError(ValueError):
    def __init__(self, code: str) -> None:
        self.code = code
        super().__init__(code)
'''

_SIGNAL_MIGRATION = '''\
SOURCE_PATHS = ("src/zenolacuna/seal_only.py",)
'''

_HOSTILE_SRC_INITIALIZER = '''\
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
(ROOT / "src" / "zenolacuna" / "seal_only.py").write_text(
    "SEALED = 'mutated'\\n",
    encoding="utf-8",
)
'''


def _marker_cli(marker: str) -> bytes:
    return f'''\
from __future__ import annotations

import json


def main(_argv: list[str]) -> int:
    print(json.dumps({{"marker": "{marker}"}}, separators=(",", ":"), sort_keys=True))
    return 0
'''.encode("utf-8")


_DRIFTING_CLI = b'''\
from __future__ import annotations

import json
from pathlib import Path

from .model import LacunaError
from .project_bindings import checker_fingerprint

ROOT = Path(__file__).resolve().parents[2]


def main(_argv: list[str]) -> int:
    source = ROOT / "src" / "zenolacuna" / "seal_only.py"
    original = source.read_bytes()
    try:
        source.write_bytes(original + b"# changed while the worker is running\\n")
        checker_fingerprint()
    except LacunaError as error:
        print(json.dumps({"code": error.code, "status": "REJECTED"}, separators=(",", ":"), sort_keys=True))
        return 2
    finally:
        source.write_bytes(original)
    return 99
'''

_OUTSIDE_ORIGIN_CLI = b'''\
from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path

from .model import LacunaError
from .project_bindings import checker_fingerprint

ROOT = Path(__file__).resolve().parents[2]


def main(_argv: list[str]) -> int:
    outside = ROOT.parent / "outside_origin.py"
    outside.write_text("VALUE = 1\\n", encoding="utf-8")
    spec = importlib.util.spec_from_file_location("src.outside_origin", outside)
    if spec is None or spec.loader is None:
        return 99
    module = importlib.util.module_from_spec(spec)
    sys.modules["src.outside_origin"] = module
    try:
        spec.loader.exec_module(module)
        checker_fingerprint()
    except LacunaError as error:
        print(json.dumps({"code": error.code, "status": "REJECTED"}, separators=(",", ":"), sort_keys=True))
        return 2
    finally:
        sys.modules.pop("src.outside_origin", None)
    return 99
'''

_UNSEALED_ROOT_CLI = b'''\
from __future__ import annotations

import json
import unsealed_dependency


def main(_argv: list[str]) -> int:
    print(json.dumps({"marker": "UNSEALED_ROOT_SUCCESS"}, separators=(",", ":"), sort_keys=True))
    return 0
'''

_UNSEALED_ROOT_DEPENDENCY = '''\
print("UNSEALED_ROOT_DEPENDENCY_EXECUTED")
'''

_ROOT_HASHLIB_SHADOW = '''\
raise RuntimeError("ROOT_HASHLIB_SHADOW_EXECUTED")
'''


def _fixture_checkout(tmp_path: Path, project_cli: bytes) -> tuple[Path, Path]:
    root = tmp_path / "source-checkout"
    package = root / "src" / "zenolacuna"
    package.mkdir(parents=True)
    tools = root / "tools"
    tools.mkdir()
    (root / "src" / "__init__.py").write_text("", encoding="utf-8")
    (tools / "__init__.py").write_text("", encoding="utf-8")
    (package / "__init__.py").write_text("", encoding="utf-8")
    (package / "model.py").write_text(_MODEL, encoding="utf-8")
    (package / "project_bindings.py").write_text(_BINDINGS, encoding="utf-8")
    (package / "signal_migration.py").write_text(_SIGNAL_MIGRATION, encoding="utf-8")
    (package / "seal_only.py").write_text("SEALED = 'original'\n", encoding="utf-8")
    (package / "project_execution.py").write_bytes(_EXECUTION_SOURCE.read_bytes())
    (package / "project_cli.py").write_bytes(project_cli)
    (tools / "zenolacuna_project_entry.py").write_bytes(_ENTRY_SOURCE.read_bytes())
    return root, package / "project_cli.py"


def _run_sealed_entry(root: Path) -> subprocess.CompletedProcess[str]:
    cache = root / "fresh-worker-cache"
    assert not cache.exists()
    return subprocess.run(
        [
            sys.executable,
            "-I",
            "-B",
            "-X",
            f"pycache_prefix={cache}",
            str(root / "tools" / "zenolacuna_project_entry.py"),
        ],
        capture_output=True,
        check=False,
        cwd=root,
        text=True,
    )


def _report(result: subprocess.CompletedProcess[str]) -> dict[str, object]:
    lines = [line for line in result.stdout.splitlines() if line]
    assert len(lines) == 1, result.stderr
    value = json.loads(lines[0])
    assert type(value) is dict
    return value


def _write_timestamp_valid_stale_cache(project_cli: Path) -> None:
    stale = _marker_cli("STALE_BYTECODE")
    fresh = _marker_cli("FRESH_SOURCE__")
    assert len(stale) == len(fresh)
    project_cli.write_bytes(stale)
    os.utime(project_cli, (_TIMESTAMP, _TIMESTAMP))
    cache = project_cli.parent / "__pycache__" / f"project_cli.{sys.implementation.cache_tag}.pyc"
    cache.parent.mkdir()
    py_compile.compile(
        str(project_cli),
        cfile=str(cache),
        doraise=True,
        invalidation_mode=py_compile.PycInvalidationMode.TIMESTAMP,
    )
    project_cli.write_bytes(fresh)
    os.utime(project_cli, (_TIMESTAMP, _TIMESTAMP))
    header = cache.read_bytes()[:16]
    assert len(header) == 16
    assert int.from_bytes(header[4:8], "little") == 0
    assert int.from_bytes(header[8:12], "little") == _TIMESTAMP
    assert int.from_bytes(header[12:16], "little") == len(fresh)


def _run_unsealed_import(root: Path) -> subprocess.CompletedProcess[str]:
    program = "\n".join((
        "import sys",
        "sys.path.insert(0, sys.argv[1])",
        "from src.zenolacuna.project_cli import main",
        "raise SystemExit(main([]))",
    ))
    return subprocess.run(
        [sys.executable, "-I", "-B", "-c", program, str(root)],
        capture_output=True,
        check=False,
        cwd=root,
        text=True,
    )


def test_given_timestamp_valid_stale_project_cli_cache_when_sealed_worker_starts_then_source_marker_runs(
    tmp_path: Path,
) -> None:
    root, project_cli = _fixture_checkout(tmp_path, _marker_cli("STALE_BYTECODE"))
    _write_timestamp_valid_stale_cache(project_cli)

    unsealed = _run_unsealed_import(root)
    assert unsealed.returncode == 0, unsealed.stderr
    assert _report(unsealed) == {"marker": "STALE_BYTECODE"}

    sealed = _run_sealed_entry(root)
    assert sealed.returncode == 0, sealed.stderr
    assert _report(sealed) == {"marker": "FRESH_SOURCE__"}
    fresh_cache = root / "fresh-worker-cache"
    assert not fresh_cache.exists() or not tuple(fresh_cache.rglob("*.pyc"))


def test_given_sealed_source_changes_during_project_call_when_checker_runs_then_cli_reports_drift(
    tmp_path: Path,
) -> None:
    root, _project_cli = _fixture_checkout(tmp_path, _DRIFTING_CLI)
    sealed_source = root / "src" / "zenolacuna" / "seal_only.py"
    before = sealed_source.read_bytes()

    result = _run_sealed_entry(root)

    assert result.returncode == 2, result.stderr
    assert _report(result) == {"code": "CHECKER_DRIFT", "status": "REJECTED"}
    assert sealed_source.read_bytes() == before


def test_given_hostile_src_initializer_mutates_after_seal_when_project_imports_then_entry_rejects(
    tmp_path: Path,
) -> None:
    root, _project_cli = _fixture_checkout(tmp_path, _marker_cli("UNREACHABLE_MARKER"))
    sealed_source = root / "src" / "zenolacuna" / "seal_only.py"
    before = sealed_source.read_bytes()
    (root / "src" / "__init__.py").write_text(_HOSTILE_SRC_INITIALIZER, encoding="utf-8")

    result = _run_sealed_entry(root)

    assert result.returncode == 2, result.stderr
    assert _report(result) == {
        "authority": "NONE",
        "code": "SOURCE_EXECUTION_UNSEALED",
        "status": "REJECTED",
    }
    assert sealed_source.read_bytes() != before


def test_given_src_named_module_from_outside_origin_when_checker_runs_then_cli_reports_drift(
    tmp_path: Path,
) -> None:
    root, _project_cli = _fixture_checkout(tmp_path, _OUTSIDE_ORIGIN_CLI)

    result = _run_sealed_entry(root)

    assert result.returncode == 2, result.stderr
    assert _report(result) == {"code": "CHECKER_DRIFT", "status": "REJECTED"}


def test_given_unsealed_root_sibling_when_project_cli_imports_it_then_worker_never_reaches_success(
    tmp_path: Path,
) -> None:
    root, _project_cli = _fixture_checkout(tmp_path, _UNSEALED_ROOT_CLI)
    (root / "unsealed_dependency.py").write_text(_UNSEALED_ROOT_DEPENDENCY, encoding="utf-8")

    result = _run_sealed_entry(root)

    assert result.returncode != 0
    assert "UNSEALED_ROOT_DEPENDENCY_EXECUTED" not in result.stdout
    assert "UNSEALED_ROOT_SUCCESS" not in result.stdout


def test_given_root_hashlib_shadow_when_worker_bootstraps_then_shadow_never_executes(tmp_path: Path) -> None:
    root, _project_cli = _fixture_checkout(tmp_path, _marker_cli("HASHLIB_SAFE"))
    (root / "hashlib.py").write_text(_ROOT_HASHLIB_SHADOW, encoding="utf-8")

    result = _run_sealed_entry(root)

    assert result.returncode == 0, result.stderr
    assert _report(result) == {"marker": "HASHLIB_SAFE"}
    assert "ROOT_HASHLIB_SHADOW_EXECUTED" not in result.stdout + result.stderr


def test_given_direct_python_import_when_no_worker_seal_then_context_states_host_premise(tmp_path: Path) -> None:
    root, _project_cli = _fixture_checkout(tmp_path, _marker_cli("DIRECT_IMPORT"))
    program = "\n".join((
        "import sys",
        "sys.path.insert(0, sys.argv[1])",
        "from src.zenolacuna.project_execution import execution_context",
        "print(execution_context())",
    ))
    result = subprocess.run(
        [sys.executable, "-I", "-B", "-c", program, str(root)],
        capture_output=True,
        check=False,
        cwd=root,
        text=True,
    )
    assert result.returncode == 0, result.stderr
    assert result.stdout == "IMMUTABLE_HOST_PREMISE\n"


def test_given_project_command_when_launcher_starts_then_isolated_fresh_worker_receives_remaining_arguments(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    cache_root = tmp_path / "launcher-cache"
    prefixes: list[str] = []
    calls: list[list[str]] = []

    def temporary_directory(*, prefix: str):
        prefixes.append(prefix)
        cache_root.mkdir()
        return contextlib.nullcontext(str(cache_root))

    def call(command: list[str]) -> int:
        calls.append(command)
        return 17

    monkeypatch.setattr("tempfile.TemporaryDirectory", temporary_directory)
    monkeypatch.setattr(subprocess, "call", call)
    monkeypatch.setattr(sys, "argv", [str(_LAUNCHER), "project", "status", "--run", "run.sqlite"])

    with pytest.raises(SystemExit) as exited:
        runpy.run_path(str(_LAUNCHER), run_name="__main__")

    assert exited.value.code == 17
    assert prefixes == ["zenolacuna-cli-"]
    assert calls == [[
        sys.executable,
        "-I",
        "-B",
        "-X",
        f"pycache_prefix={cache_root / 'pycache'}",
        str(_ENTRY_SOURCE),
        "status",
        "--run",
        "run.sqlite",
    ]]
