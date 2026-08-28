#!/usr/bin/env python3
"""Replay and check the exact research-only current-Tau incompatibility artifact."""

# ruff: noqa: E402 -- the isolated-path bootstrap must precede all non-builtin imports.

from __future__ import annotations

import sys as _bootstrap_sys


def _require_isolated_python_main_v1() -> None:
    """Install a conditional post-bootstrap code-object binding guard.

    The entrypoint itself has already executed.  Git, the interpreter, and the
    filesystem are therefore explicit external replay premises, never an
    in-repository self-authentication claim.
    """

    if (
        not _bootstrap_sys.flags.isolated
        or not _bootstrap_sys.flags.no_site
        or not _bootstrap_sys.flags.safe_path
    ):
        _bootstrap_sys.stdout.write(
            '{"artifact_root":null,"artifact_sha256":"",'
            '"current_tau_compatible":false,"findings":'
            '[{"code":"PYTHON_NOT_ISOLATED","path":"python"}],"o002_implemented":false,'
            '"o003a_evidence_complete":false,'
            '"o003a_reviewed_current_tau_incompatibility_research_only":false,'
            '"direct_python_replay_conditional":false,'
            '"external_replay_trust_root_blocked":true,"ok":false,'
            '"production_authority":"NONE","release_authority":"NONE",'
            '"route_quarantine_implemented":false,"schema":'
            '"zenodex/current-tau-compatibility-check/v1",'
            '"settlement_authority":"NONE","value_movement_authority":"NONE",'
            '"value_movement_claim_allowed":false,"vm_gates_closed":[]}\n'
        )
        raise SystemExit(1)
    import hashlib as bootstrap_hashlib
    import importlib.util as bootstrap_importlib_util
    import marshal as bootstrap_marshal
    import os as bootstrap_os
    import stat as bootstrap_stat
    import subprocess as bootstrap_subprocess
    from types import CodeType as bootstrap_code_type

    repo_root = bootstrap_os.path.dirname(
        bootstrap_os.path.dirname(bootstrap_os.path.realpath(__file__))
    )
    trusted_runtime_paths = [
        entry
        for entry in _bootstrap_sys.path
        if entry
        and "site-packages" not in entry
        and "dist-packages" not in entry
    ]
    _bootstrap_sys.path[:] = [*trusted_runtime_paths, repo_root]
    allowed_repository_exec = frozenset(
        {
            "tools/__init__.py",
            "tools/build_current_tau_compatibility_v1.py",
            "tools/check_current_tau_compatibility_v1.py",
            "tools/current_tau_compatibility_core_v1.py",
            "tools/current_tau_compatibility_pins_v1.py",
            "tools/current_tau_replay_io_v1.py",
            "tools/current_tau_source_analysis_v1.py",
        }
    )
    repository_module_paths = {
        (relative[: -len("/__init__.py")] if relative.endswith("/__init__.py") else relative[:-3])
        .replace("/", "."): relative
        for relative in allowed_repository_exec
    }

    def reject_unbound_runtime_source(code: str = "IMPLEMENTATION_RUNTIME_CODE_UNBOUND") -> None:
        _bootstrap_sys.stdout.write(
            '{"artifact_root":null,"artifact_sha256":"",'
            '"current_tau_compatible":false,"findings":'
            '[{"code":"' + code + '","path":"runtime"}],'
            '"o002_implemented":false,"o003a_evidence_complete":false,'
            '"o003a_reviewed_current_tau_incompatibility_research_only":false,'
            '"direct_python_replay_conditional":false,'
            '"external_replay_trust_root_blocked":true,"ok":false,'
            '"production_authority":"NONE","release_authority":"NONE",'
            '"route_quarantine_implemented":false,"schema":'
            '"zenodex/current-tau-compatibility-check/v1",'
            '"settlement_authority":"NONE","value_movement_authority":"NONE",'
            '"value_movement_claim_allowed":false,"vm_gates_closed":[]}\n'
        )
        _bootstrap_sys.stdout.flush()
        bootstrap_os._exit(1)

    def git_source_bytes(relative: str) -> bytes | None:
        try:
            completed = bootstrap_subprocess.run(
                [
                    "git",
                    "-c",
                    "core.hooksPath=/dev/null",
                    "-c",
                    "core.fsmonitor=false",
                    "-C",
                    repo_root,
                    "show",
                    f"{captured_commit}:{relative}",
                ],
                check=False,
                stdin=bootstrap_subprocess.DEVNULL,
                stdout=bootstrap_subprocess.PIPE,
                stderr=bootstrap_subprocess.PIPE,
                env={
                    "GIT_CONFIG_GLOBAL": bootstrap_os.devnull,
                    "GIT_CONFIG_NOSYSTEM": "1",
                    "GIT_NO_LAZY_FETCH": "1",
                    "GIT_NO_REPLACE_OBJECTS": "1",
                    "GIT_OPTIONAL_LOCKS": "0",
                    "LC_ALL": "C",
                    "PATH": bootstrap_os.defpath,
                },
                timeout=5,
            )
        except (OSError, bootstrap_subprocess.TimeoutExpired):
            return None
        if (
            completed.returncode != 0
            or completed.stderr
            or len(completed.stdout) > 131_072
        ):
            return None
        return completed.stdout

    def worktree_source_bytes(relative: str) -> bytes | None:
        """Read one regular source file through a non-symlink descriptor."""

        try:
            nofollow = bootstrap_os.O_NOFOLLOW
        except AttributeError:
            return None
        descriptor: int | None = None
        try:
            descriptor = bootstrap_os.open(
                bootstrap_os.path.join(repo_root, relative),
                bootstrap_os.O_RDONLY | nofollow,
            )
            metadata = bootstrap_os.fstat(descriptor)
            if (
                not bootstrap_stat.S_ISREG(metadata.st_mode)
                or metadata.st_size < 0
                or metadata.st_size > 131_072
            ):
                return None
            raw = bytearray()
            while len(raw) < metadata.st_size:
                chunk = bootstrap_os.read(descriptor, min(65_536, metadata.st_size - len(raw)))
                if not chunk:
                    return None
                raw.extend(chunk)
            return bytes(raw)
        except OSError:
            return None
        finally:
            if descriptor is not None:
                bootstrap_os.close(descriptor)

    def worktree_source_matches_captured_git(relative: str, expected: bytes) -> bool:
        observed = worktree_source_bytes(relative)
        return observed is not None and observed == expected

    def load_captured_commit() -> str | None:
        try:
            completed = bootstrap_subprocess.run(
                ["git", "-C", repo_root, "rev-parse", "--verify", "HEAD^{commit}"],
                check=False,
                stdin=bootstrap_subprocess.DEVNULL,
                stdout=bootstrap_subprocess.PIPE,
                stderr=bootstrap_subprocess.PIPE,
                env={
                    "GIT_CONFIG_GLOBAL": bootstrap_os.devnull,
                    "GIT_CONFIG_NOSYSTEM": "1",
                    "GIT_NO_LAZY_FETCH": "1",
                    "GIT_NO_REPLACE_OBJECTS": "1",
                    "GIT_OPTIONAL_LOCKS": "0",
                    "LC_ALL": "C",
                    "PATH": bootstrap_os.defpath,
                },
                timeout=5,
            )
        except (OSError, bootstrap_subprocess.TimeoutExpired):
            return None
        value = completed.stdout.decode("ascii", "ignore").strip()
        return value if completed.returncode == 0 and not completed.stderr and len(value) == 40 else None

    captured_commit = load_captured_commit()
    if captured_commit is None:
        reject_unbound_runtime_source("IMPLEMENTATION_RUNTIME_TRUST_ROOT_UNAVAILABLE")
    expected_code_cache: dict[tuple[str, str], bytes] = {}

    def code_matches_captured_source(code: object, filename: str, relative: str) -> bool:
        if type(code) is not bootstrap_code_type:
            return False
        cache_key = (filename, relative)
        expected_marshaled = expected_code_cache.get(cache_key)
        if expected_marshaled is None:
            raw = git_source_bytes(relative)
            if raw is None:
                return False
            try:
                expected = compile(
                    raw.decode("utf-8"),
                    filename,
                    "exec",
                    dont_inherit=True,
                    optimize=_bootstrap_sys.flags.optimize,
                )
                expected_marshaled = bootstrap_marshal.dumps(expected)
            except (UnicodeDecodeError, TypeError, ValueError):
                return False
            expected_code_cache[cache_key] = expected_marshaled
        observed = bootstrap_marshal.dumps(code)
        return bootstrap_hashlib.sha256(observed).digest() == bootstrap_hashlib.sha256(
            expected_marshaled
        ).digest()

    def audit_repository_exec(event: str, args: tuple[object, ...]) -> None:
        if event != "exec" or not args:
            return
        code = args[0]
        filename = code.co_filename if type(code) is bootstrap_code_type else None
        if type(filename) is not str:
            reject_unbound_runtime_source()
        if not bootstrap_os.path.isabs(filename):
            if filename in allowed_repository_exec:
                reject_unbound_runtime_source()
            return
        resolved = bootstrap_os.path.realpath(filename)
        try:
            common = bootstrap_os.path.commonpath((repo_root, resolved))
        except ValueError:
            return
        if common != repo_root:
            return
        relative = bootstrap_os.path.relpath(resolved, repo_root)
        if relative not in allowed_repository_exec:
            reject_unbound_runtime_source()
        if not code_matches_captured_source(code, filename, relative):
            reject_unbound_runtime_source()

    _bootstrap_sys.addaudithook(audit_repository_exec)

    class SelectedRepositoryLoaderV1:
        """Execute only selected Git bytes after the explicit bootstrap premise."""

        def __init__(self, relative: str) -> None:
            self._relative = relative

        def create_module(self, _spec: object) -> None:
            return None

        def exec_module(self, module: object) -> None:
            raw = git_source_bytes(self._relative)
            if raw is None or not worktree_source_matches_captured_git(self._relative, raw):
                reject_unbound_runtime_source()
            filename = bootstrap_os.path.join(repo_root, self._relative)
            try:
                code = compile(
                    raw.decode("utf-8"),
                    filename,
                    "exec",
                    dont_inherit=True,
                    optimize=_bootstrap_sys.flags.optimize,
                )
            except (UnicodeDecodeError, TypeError, ValueError):
                reject_unbound_runtime_source()
            exec(code, module.__dict__)

    class SelectedRepositoryFinderV1:
        """Bypass repository bytecode caches for the closed runtime import set."""

        def find_spec(
            self,
            fullname: str,
            _path: object = None,
            _target: object = None,
        ) -> object:
            relative = repository_module_paths.get(fullname)
            if relative is None:
                if fullname == "tools" or fullname.startswith("tools."):
                    reject_unbound_runtime_source()
                return None
            filename = bootstrap_os.path.join(repo_root, relative)
            submodule_locations = (
                [bootstrap_os.path.dirname(filename)] if relative.endswith("/__init__.py") else None
            )
            return bootstrap_importlib_util.spec_from_file_location(
                fullname,
                filename,
                loader=SelectedRepositoryLoaderV1(relative),
                submodule_search_locations=submodule_locations,
            )

    _bootstrap_sys.meta_path.insert(0, SelectedRepositoryFinderV1())


if __name__ == "__main__":
    _require_isolated_python_main_v1()

import json
import sys
from pathlib import Path
from typing import Final

REPO_ROOT: Final = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.build_current_tau_compatibility_v1 import (  # noqa: E402
    JSON_OUTPUT,
    MAX_ARTIFACT_BYTES_V1,
    TauReplayPathsV1,
    load_current_tau_compatibility_snapshot_v1,
)
from tools.current_tau_compatibility_core_v1 import (  # noqa: E402
    CHECK_SCHEMA_V1,
    CurrentTauCompatibilityRejectV1,
    canonical_json_bytes_v1,
    check_current_tau_compatibility_artifact_v1,
    decode_json_object_v1,
)
from tools.current_tau_compatibility_pins_v1 import (  # noqa: E402
    RUNTIME_EXECUTABLE_SOURCE_PATHS_V1,
)
from tools.current_tau_replay_io_v1 import (  # noqa: E402
    FailClosedArgumentParserV1,
    ShellRejectV1,
    _read_bounded_regular_file_v1,
    _unbound_runtime_repository_imports_v1,
)


def _failure_report(code: str, path: str) -> dict[str, object]:
    return {
        "schema": CHECK_SCHEMA_V1,
        "ok": False,
        "findings": [{"code": code, "path": path}],
        "artifact_sha256": "",
        "artifact_root": None,
        "o003a_evidence_complete": False,
        "o003a_reviewed_current_tau_incompatibility_research_only": False,
        "direct_python_replay_conditional": False,
        "external_replay_trust_root_blocked": True,
        "route_quarantine_implemented": False,
        "current_tau_compatible": False,
        "production_authority": "NONE",
        "release_authority": "NONE",
        "settlement_authority": "NONE",
        "value_movement_authority": "NONE",
        "value_movement_claim_allowed": False,
        "o002_implemented": False,
        "vm_gates_closed": [],
    }


def check_current_tau_compatibility_v1(
    *,
    paths: TauReplayPathsV1,
    artifact_path: Path | None = None,
) -> dict[str, object]:
    """Recompute source facts, then compare one canonical artifact byte-for-byte."""

    source = artifact_path or paths.root / JSON_OUTPUT
    try:
        raw_artifact = _read_bounded_regular_file_v1(
            source,
            MAX_ARTIFACT_BYTES_V1,
            "current Tau compatibility artifact",
        )
        artifact = decode_json_object_v1(raw_artifact, "current Tau compatibility artifact")
        if canonical_json_bytes_v1(artifact) != raw_artifact:
            return _failure_report("NONCANONICAL_ARTIFACT", str(source))
        snapshot = load_current_tau_compatibility_snapshot_v1(paths)
        return check_current_tau_compatibility_artifact_v1(
            artifact,
            raw_artifact,
            snapshot,
        )
    except (CurrentTauCompatibilityRejectV1, ShellRejectV1) as exc:
        return _failure_report(exc.code, exc.path)
    except (MemoryError, OSError, RecursionError, TypeError, ValueError) as exc:
        return _failure_report("CHECKER_INPUT_ERROR", type(exc).__name__)
    except Exception:
        return _failure_report("CHECKER_INTERNAL_ERROR", "internal")


def main(argv: list[str] | None = None) -> int:
    parser = FailClosedArgumentParserV1(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    parser.add_argument("--tau-testnet-repo", type=Path, required=True)
    parser.add_argument("--tau-lang-repo", type=Path, required=True)
    parser.add_argument("--historical-bridge-repo", type=Path)
    try:
        if _bootstrap_sys.flags.isolated and _bootstrap_sys.flags.no_site:
            unbound = _unbound_runtime_repository_imports_v1(
                REPO_ROOT,
                RUNTIME_EXECUTABLE_SOURCE_PATHS_V1,
            )
            if unbound:
                report = _failure_report(
                    "IMPLEMENTATION_RUNTIME_SOURCE_UNBOUND",
                    unbound[0],
                )
                print(json.dumps(report, sort_keys=True))
                return 1
        args = parser.parse_args(argv)
        bridge_repo = args.historical_bridge_repo or args.tau_testnet_repo
        paths = TauReplayPathsV1(
            args.root,
            args.tau_testnet_repo,
            args.tau_lang_repo,
            bridge_repo,
        )
        report = check_current_tau_compatibility_v1(paths=paths)
    except ShellRejectV1 as exc:
        report = _failure_report(exc.code, exc.path)
    except Exception:
        report = _failure_report("CHECKER_INTERNAL_ERROR", "internal")
    print(json.dumps(report, sort_keys=True))
    return 0 if report["ok"] is True else 1


if __name__ == "__main__":
    raise SystemExit(main())
