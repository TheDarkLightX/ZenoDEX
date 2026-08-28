#!/usr/bin/env python3
"""Build replayable research evidence for the current-Tau compatibility gap."""

# ruff: noqa: E402 -- the isolated-path bootstrap must precede all non-builtin imports.

from __future__ import annotations

import sys as _bootstrap_sys


def _require_isolated_python_main_v1() -> None:
    """Install a conditional post-bootstrap code-object binding guard.

    This is defense in depth only.  The Python process has already executed
    this entrypoint before it can install the hook, and Git/interpreter/filesystem
    selection remains an external replay trust premise.
    """

    if (
        not _bootstrap_sys.flags.isolated
        or not _bootstrap_sys.flags.no_site
        or not _bootstrap_sys.flags.safe_path
    ):
        _bootstrap_sys.stdout.write(
            '{"finding":"PYTHON_NOT_ISOLATED","o002_implemented":false,'
            '"o003a_evidence_complete":false,'
            '"o003a_reviewed_current_tau_incompatibility_research_only":false,'
            '"direct_python_replay_conditional":false,'
            '"external_replay_trust_root_blocked":true,"ok":false,'
            '"production_authority":"NONE","release_authority":"NONE",'
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
            '{"finding":"' + code + '",'
            '"o002_implemented":false,"o003a_evidence_complete":false,'
            '"o003a_reviewed_current_tau_incompatibility_research_only":false,'
            '"direct_python_replay_conditional":false,'
            '"external_replay_trust_root_blocked":true,"ok":false,'
            '"production_authority":"NONE","release_authority":"NONE",'
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

import hashlib
import json
import os
import stat
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Final, NoReturn

REPO_ROOT: Final = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.current_tau_compatibility_core_v1 import (  # noqa: E402
    CurrentTauCompatibilityRejectV1,
    CurrentTauCompatibilitySnapshotV1,
    SourcePinV1,
    build_current_tau_compatibility_artifact_v1,
    canonical_json_bytes_v1,
)
from tools.current_tau_compatibility_pins_v1 import (  # noqa: E402
    ACTIVE_PLAN_COMMIT_V1,
    ACTIVE_PLAN_SHA256_V1,
    ACTIVE_REGISTRY_SHA256_V1,
    ADMISSION_RECEIPT_PAYLOAD_SHA256_V1,
    ADMISSION_RECEIPT_SHA256_V1,
    CURRENT_TAU_COMMIT_V1,
    CURRENT_TAU_LANG_COMMIT_V1,
    CURRENT_TAU_LANG_SOURCE_SHA256_V1,
    CURRENT_TAU_LANG_TREE_LISTING_SHA256_V1,
    CURRENT_TAU_SOURCE_SHA256_V1,
    CURRENT_TAU_TREE_LISTING_SHA256_V1,
    HISTORICAL_BRIDGE_COMMIT_V1,
    HISTORICAL_BRIDGE_SOURCE_SHA256_V1,
    HISTORICAL_BRIDGE_TREE_LISTING_SHA256_V1,
    HISTORICAL_LOCAL_PROFILE_COMMIT_V1,
    HISTORICAL_LOCAL_PROFILE_SOURCE_SHA256_V1,
    HISTORICAL_LOCAL_PROFILE_TREE_LISTING_SHA256_V1,
    REPLAY_IMPLEMENTATION_EVIDENCE_PATHS_V1,
    RUNTIME_EXECUTABLE_SOURCE_PATHS_V1,
)
from tools.current_tau_replay_io_v1 import (  # noqa: E402
    FailClosedArgumentParserV1,
    ShellRejectV1,
    _atomic_replace_regular_file_v1,
    _git_head_v1,
    _git_is_ancestor_v1,
    _git_scalar_v1,
    _git_tree_v1,
    _read_bounded_regular_file_v1,
    _run_git_v1,
    _unbound_runtime_repository_imports_v1,
)
from tools.current_tau_source_analysis_v1 import (  # noqa: E402
    LEGACY_OPERATION_KEYS_V1,
    class_methods_v1,
    command_registry_keys_v1,
    compose_service_environment_value_v1,
    force_test_requires_test_env_v1,
    historical_apply_app_tx_bridge_v1,
    historical_force_test_enters_mock_v1,
    legacy_prefix_parser_accepts_v1,
    literal_int_set_v1,
    literal_string_assignments_v1,
    python_env_default_v1,
    require_success_envelope_v1,
    server_uses_default_command_registry_v1,
    shell_forwards_force_test_v1,
    signing_vector_sha256_v1,
    source_references_identifier_v1,
    success_envelope_sha256_v1,
    success_envelope_v1,
    user_tx_signing_fields_v1,
)

JSON_OUTPUT: Final = Path("docs/research/ZENODEX_CURRENT_TAU_COMPATIBILITY_V1.json")
MAX_SOURCE_BYTES_V1: Final = 131_072
MAX_ARTIFACT_BYTES_V1: Final = 524_288
ACTIVE_REGISTRY_PATH_V1: Final = Path("docs/research/ZENODEX_ACTIVE_WHOLE_PROGRAM_PLAN_V1.json")
ADMISSION_RECEIPT_PATH_V1: Final = Path(
    "docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_ADMISSION_V1.json"
)


@dataclass(frozen=True)
class TauReplayPathsV1:
    root: Path
    tau_testnet_repo: Path
    tau_lang_repo: Path
    historical_bridge_repo: Path


@dataclass(frozen=True, slots=True)
class ReplayCheckoutBindingV1:
    """One externally supplied source checkout observed during replay capture.

    The binding detects ordinary symlink/checkout replacement during this run.
    It cannot make Python or the filesystem self-authenticating; that premise is
    recorded as an external trust-root blocker in the artifact.
    """

    role: str
    configured_path: Path
    resolved_path: Path
    device: int
    inode: int
    commit: str


@dataclass(frozen=True)
class ReplaySourcesV1:
    implementation_pin: SourcePinV1
    current_tau_pin: SourcePinV1
    current_tau_lang_pin: SourcePinV1
    historical_pin: SourcePinV1
    historical_local_profile_pin: SourcePinV1
    implementation: SourceCorpusV1
    current_tau: SourceCorpusV1
    historical: SourceCorpusV1
    historical_local_profile: SourceCorpusV1


@dataclass(frozen=True, slots=True)
class SourceCorpusV1:
    entries: tuple[tuple[str, bytes], ...]

    def __post_init__(self) -> None:
        if type(self.entries) is not tuple:
            raise TypeError("source corpus entries must be an exact tuple")
        paths: list[str] = []
        for entry in self.entries:
            if (
                type(entry) is not tuple
                or len(entry) != 2
                or type(entry[0]) is not str
                or type(entry[1]) is not bytes
            ):
                raise TypeError("source corpus entries must be exact (str, bytes) pairs")
            paths.append(entry[0])
        if paths != sorted(paths) or len(paths) != len(set(paths)):
            raise ValueError("source corpus paths must be unique and sorted")

    @classmethod
    def from_dict(cls, sources: dict[str, bytes]) -> SourceCorpusV1:
        return cls(tuple(sorted(sources.items())))

    def __getitem__(self, path: str) -> bytes:
        for candidate, raw in self.entries:
            if candidate == path:
                return raw
        raise KeyError(path)


@dataclass(frozen=True)
class SigningFactsV1:
    current_fields: tuple[str, ...]
    local_fields: tuple[str, ...]
    historical_fields: tuple[str, ...]


@dataclass(frozen=True)
class RpcFactsV1:
    current_absent: tuple[str, ...]
    local_methods: tuple[str, ...]
    historical_present: tuple[str, ...]


@dataclass(frozen=True)
class ProfileFactsV1:
    force_test: str
    runner_forwards_force_test: bool
    default_tau_env: str
    current_requires_test_env: bool
    historical_enters_mock: bool


def _reject(code: str, path: str, detail: str) -> NoReturn:
    raise CurrentTauCompatibilityRejectV1(code, path, detail)


def _sha256_v1(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _git_source_bytes_v1(repo: Path, commit: str, path: str) -> bytes:
    _, stdout, stderr = _run_git_v1(repo, ("show", f"{commit}:{path}"))
    if stderr:
        _reject("GIT_SOURCE_STDERR", path, "source replay emitted stderr")
    return stdout.encode("utf-8")


def _source_pin_v1(
    repo: Path,
    commit: str,
    expected_tree_listing_sha256: str | None,
    expected_sources: tuple[tuple[str, str], ...],
) -> tuple[SourcePinV1, SourceCorpusV1]:
    tree = _git_tree_v1(repo, commit)
    tree_listing_sha256 = _git_tree_listing_sha256_v1(repo, commit)
    if (
        expected_tree_listing_sha256 is not None
        and tree_listing_sha256 != expected_tree_listing_sha256
    ):
        _reject("SOURCE_TREE_LISTING_DRIFT", str(repo), "exact Git tree listing drift")
    sources: dict[str, bytes] = {}
    observed_hashes: list[tuple[str, str]] = []
    for path, expected_sha in expected_sources:
        raw = _git_source_bytes_v1(repo, commit, path)
        if len(raw) > MAX_SOURCE_BYTES_V1:
            _reject("SOURCE_SIZE_LIMIT", path, "source exceeds replay byte ceiling")
        observed_sha = _sha256_v1(raw)
        if observed_sha != expected_sha:
            _reject("SOURCE_SHA256_DRIFT", path, "exact upstream source bytes drift")
        sources[path] = raw
        observed_hashes.append((path, observed_sha))
    return (
        SourcePinV1(commit, tree, tree_listing_sha256, tuple(observed_hashes)),
        SourceCorpusV1.from_dict(sources),
    )


def _git_tree_listing_sha256_v1(repo: Path, commit: str) -> str:
    _, stdout, stderr = _run_git_v1(repo, ("ls-tree", "-z", "--full-tree", commit))
    if stderr:
        _reject("GIT_TREE_LISTING_STDERR", str(repo), "tree replay emitted stderr")
    return _sha256_v1(stdout.encode("utf-8"))


def _implementation_subject_commit_v1(root: Path, captured_head: str) -> str:
    status, stdout, stderr = _run_git_v1(
        root,
        ("log", "-1", "--format=%H", "--", str(JSON_OUTPUT)),
        allowed_statuses=frozenset({0}),
    )
    if status != 0 or stderr:
        _reject("EVIDENCE_COMMIT_LOOKUP", str(JSON_OUTPUT), "Git lookup drift")
    evidence_commit = stdout.strip()
    if not evidence_commit:
        return captured_head
    if not _git_is_ancestor_v1(root, evidence_commit, captured_head):
        _reject("EVIDENCE_COMMIT_ANCESTRY", str(JSON_OUTPUT), "artifact commit is off lineage")
    parent = _git_scalar_v1(
        root,
        ("rev-parse", "--verify", f"{evidence_commit}^{{commit}}^"),
        "evidence parent",
    )
    _, changed, changed_stderr = _run_git_v1(
        root,
        ("diff-tree", "--no-commit-id", "--name-only", "-r", parent, evidence_commit),
    )
    changed_paths = tuple(line for line in changed.splitlines() if line)
    if changed_stderr or changed_paths != (str(JSON_OUTPUT),):
        _reject(
            "EVIDENCE_COMMIT_SHAPE",
            evidence_commit,
            "artifact commit must change exactly the compatibility artifact",
        )
    return parent if evidence_commit == captured_head else captured_head


def _implementation_source_hashes_v1(
    root: Path,
    commit: str,
) -> tuple[tuple[str, str], ...]:
    return tuple(
        (path, _sha256_v1(_git_source_bytes_v1(root, commit, path)))
        for path in REPLAY_IMPLEMENTATION_EVIDENCE_PATHS_V1
    )


def _require_unchanged_head_v1(root: Path, captured_head: str) -> None:
    if _git_head_v1(root) != captured_head:
        _reject("HEAD_CHANGED_DURING_CAPTURE", "HEAD", "Git HEAD changed during replay")


def _require_capture_unchanged_v1(
    paths: TauReplayPathsV1,
    captured_head: str,
    snapshot: CurrentTauCompatibilitySnapshotV1,
    checkout_bindings: tuple[
        ReplayCheckoutBindingV1,
        ReplayCheckoutBindingV1,
        ReplayCheckoutBindingV1,
    ],
) -> None:
    _require_unchanged_head_v1(paths.root, captured_head)
    _require_worktree_sources_match_v1(
        paths.root,
        snapshot.implementation.source_sha256,
        "implementation final",
    )
    current_tau, current_tau_lang, historical_bridge = checkout_bindings
    _require_checkout_binding_unchanged_v1(
        current_tau,
        expected_sources=CURRENT_TAU_SOURCE_SHA256_V1,
    )
    _require_checkout_binding_unchanged_v1(
        current_tau_lang,
        expected_sources=CURRENT_TAU_LANG_SOURCE_SHA256_V1,
    )
    _require_checkout_binding_unchanged_v1(
        historical_bridge,
        expected_sources=HISTORICAL_BRIDGE_SOURCE_SHA256_V1,
    )
    plan, registry, admission, payload = _load_active_plan_binding_v1(paths.root)
    if (
        plan != snapshot.active_plan_sha256
        or registry != snapshot.active_registry_sha256
        or admission != snapshot.admission_receipt_sha256
        or payload != snapshot.admission_receipt_payload_sha256
    ):
        _reject("CAPTURE_CHANGED_DURING_REPLAY", "active plan", "binding changed during replay")


def _require_worktree_sources_match_v1(
    root: Path,
    expected_sources: tuple[tuple[str, str], ...],
    role: str,
) -> None:
    for path, expected_sha in expected_sources:
        raw = _read_bounded_regular_file_v1(root / path, MAX_SOURCE_BYTES_V1, f"{role}:{path}")
        if _sha256_v1(raw) != expected_sha:
            _reject("WORKTREE_SOURCE_DRIFT", path, f"{role} working source differs from pin")


def _capture_checkout_binding_v1(
    repo: Path,
    *,
    role: str,
    expected_commit: str,
    expected_sources: tuple[tuple[str, str], ...],
) -> ReplayCheckoutBindingV1:
    """Capture one checkout after binding its path, HEAD, and selected bytes.

    This is a bounded race detector for the three explicit external replay
    inputs.  Git, the interpreter, and filesystem remain external premises.
    """

    configured = Path(os.path.abspath(os.fspath(repo)))
    try:
        resolved = configured.resolve(strict=True)
        metadata = os.stat(resolved, follow_symlinks=False)
    except OSError as exc:
        _reject("REPLAY_CHECKOUT_UNAVAILABLE", str(configured), f"{role}:{type(exc).__name__}")
    if not stat.S_ISDIR(metadata.st_mode):
        _reject("REPLAY_CHECKOUT_TYPE", str(configured), f"{role}: checkout must be a directory")
    observed_head = _git_head_v1(resolved)
    if observed_head != expected_commit:
        _reject("REPLAY_CHECKOUT_HEAD_DRIFT", f"{role}.HEAD", "exact checkout commit drift")
    _require_worktree_sources_match_v1(resolved, expected_sources, role)
    return ReplayCheckoutBindingV1(
        role=role,
        configured_path=configured,
        resolved_path=resolved,
        device=metadata.st_dev,
        inode=metadata.st_ino,
        commit=observed_head,
    )


def _require_checkout_binding_unchanged_v1(
    binding: ReplayCheckoutBindingV1,
    *,
    expected_sources: tuple[tuple[str, str], ...],
) -> None:
    """Re-resolve a captured checkout and reject a path, HEAD, or byte switch."""

    refreshed = _capture_checkout_binding_v1(
        binding.configured_path,
        role=binding.role,
        expected_commit=binding.commit,
        expected_sources=expected_sources,
    )
    if (
        refreshed.resolved_path != binding.resolved_path
        or refreshed.device != binding.device
        or refreshed.inode != binding.inode
        or refreshed.commit != binding.commit
    ):
        _reject("REPLAY_CHECKOUT_SWITCHED", binding.role, "checkout identity changed during replay")


def _capture_replay_checkouts_v1(
    paths: TauReplayPathsV1,
) -> tuple[ReplayCheckoutBindingV1, ReplayCheckoutBindingV1, ReplayCheckoutBindingV1]:
    """Bind only current external upstream inputs, never the historical profile path."""

    return (
        _capture_checkout_binding_v1(
            paths.tau_testnet_repo,
            role="current_tau",
            expected_commit=CURRENT_TAU_COMMIT_V1,
            expected_sources=CURRENT_TAU_SOURCE_SHA256_V1,
        ),
        _capture_checkout_binding_v1(
            paths.tau_lang_repo,
            role="current_tau_lang",
            expected_commit=CURRENT_TAU_LANG_COMMIT_V1,
            expected_sources=CURRENT_TAU_LANG_SOURCE_SHA256_V1,
        ),
        _capture_checkout_binding_v1(
            paths.historical_bridge_repo,
            role="historical_bridge",
            expected_commit=HISTORICAL_BRIDGE_COMMIT_V1,
            expected_sources=HISTORICAL_BRIDGE_SOURCE_SHA256_V1,
        ),
    )


def _load_sources_v1(paths: TauReplayPathsV1, implementation_commit: str) -> ReplaySourcesV1:
    implementation_sources = _implementation_source_hashes_v1(paths.root, implementation_commit)
    implementation_pin, implementation = _source_pin_v1(
        paths.root,
        implementation_commit,
        None,
        implementation_sources,
    )
    current_tau_pin, current_tau = _source_pin_v1(
        paths.tau_testnet_repo,
        CURRENT_TAU_COMMIT_V1,
        CURRENT_TAU_TREE_LISTING_SHA256_V1,
        CURRENT_TAU_SOURCE_SHA256_V1,
    )
    current_tau_lang_pin, _ = _source_pin_v1(
        paths.tau_lang_repo,
        CURRENT_TAU_LANG_COMMIT_V1,
        CURRENT_TAU_LANG_TREE_LISTING_SHA256_V1,
        CURRENT_TAU_LANG_SOURCE_SHA256_V1,
    )
    historical_pin, historical = _source_pin_v1(
        paths.historical_bridge_repo,
        HISTORICAL_BRIDGE_COMMIT_V1,
        HISTORICAL_BRIDGE_TREE_LISTING_SHA256_V1,
        HISTORICAL_BRIDGE_SOURCE_SHA256_V1,
    )
    historical_local_profile_pin, historical_local_profile = _source_pin_v1(
        paths.root,
        HISTORICAL_LOCAL_PROFILE_COMMIT_V1,
        HISTORICAL_LOCAL_PROFILE_TREE_LISTING_SHA256_V1,
        HISTORICAL_LOCAL_PROFILE_SOURCE_SHA256_V1,
    )
    _require_worktree_sources_match_v1(
        paths.root,
        implementation_sources,
        "implementation",
    )
    return ReplaySourcesV1(
        implementation_pin,
        current_tau_pin,
        current_tau_lang_pin,
        historical_pin,
        historical_local_profile_pin,
        implementation,
        current_tau,
        historical,
        historical_local_profile,
    )


def _signing_facts_v1(sources: ReplaySourcesV1) -> SigningFactsV1:
    current_fields = user_tx_signing_fields_v1(
        sources.current_tau["commands/sendtx.py"],
        "current:commands/sendtx.py",
        "_get_signing_message_bytes",
    )
    local_fields = user_tx_signing_fields_v1(
        sources.historical_local_profile["src/integration/tau_net_client.py"],
        "historical-local-profile:src/integration/tau_net_client.py",
        "_tx_signing_message_bytes",
    )
    historical_fields = user_tx_signing_fields_v1(
        sources.historical["commands/sendtx.py"],
        "historical:commands/sendtx.py",
        "_get_signing_message_bytes",
    )
    return SigningFactsV1(current_fields, local_fields, historical_fields)


def _rpc_facts_v1(sources: ReplaySourcesV1) -> RpcFactsV1:
    names = ("apply_app_tx", "getappstate", "getstateproof")
    current_registry = command_registry_keys_v1(
        sources.current_tau["app/container.py"], "current:app/container.py"
    )
    historical_registry = command_registry_keys_v1(
        sources.historical["app/container.py"], "historical:app/container.py"
    )
    current_server_uses_default_registry = server_uses_default_command_registry_v1(
        sources.current_tau["server.py"], "current:server.py"
    )
    current_absent = (
        *(
            ()
            if not current_server_uses_default_registry
            or source_references_identifier_v1(
                sources.current_tau["commands/createblock.py"],
                "current:commands/createblock.py",
                "apply_app_tx",
            )
            else ("apply_app_tx",)
        ),
        *(
            name
            for name in names[1:]
            if current_server_uses_default_registry and name not in current_registry
        ),
    )
    historical_apply = (
        ("apply_app_tx",)
        if historical_apply_app_tx_bridge_v1(
            sources.historical["commands/createblock.py"],
            "historical:commands/createblock.py",
        )
        else ()
    )
    historical_present = (
        *historical_apply,
        *(name for name in names[1:2] if name in historical_registry),
    )
    local_method_set = class_methods_v1(
        sources.historical_local_profile["src/integration/tau_net_client.py"],
        "historical-local-profile:src/integration/tau_net_client.py",
        "TauNetTcpClient",
    )
    local_methods = tuple(name for name in names[1:] if name in local_method_set)
    return RpcFactsV1(current_absent, local_methods, historical_present)


def _profile_facts_v1(sources: ReplaySourcesV1) -> ProfileFactsV1:
    compose = sources.historical_local_profile["docker-compose.local-testnet.yml"]
    runner = sources.historical_local_profile["tools/run_local_tau_node_container.sh"]
    e2e = sources.historical_local_profile["tools/tau_testnet_local_e2e.py"]
    return ProfileFactsV1(
        force_test=compose_service_environment_value_v1(
            compose,
            "historical-local-profile:docker-compose.local-testnet.yml",
            "tau-local",
            "TAU_FORCE_TEST",
        ),
        runner_forwards_force_test=shell_forwards_force_test_v1(
            runner,
            "historical-local-profile:tools/run_local_tau_node_container.sh",
        ),
        default_tau_env=python_env_default_v1(
            e2e,
            "historical-local-profile:tools/tau_testnet_local_e2e.py",
        ),
        current_requires_test_env=force_test_requires_test_env_v1(
            sources.current_tau["tau_manager.py"],
            "current:tau_manager.py",
        ),
        historical_enters_mock=historical_force_test_enters_mock_v1(
            sources.historical["tau_manager.py"],
            "historical:tau_manager.py",
        ),
    )


def _load_active_plan_binding_v1(root: Path) -> tuple[str, str, str, str]:
    raw = _git_source_bytes_v1(
        root,
        ACTIVE_PLAN_COMMIT_V1,
        "docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V2.json",
    )
    observed = _sha256_v1(raw)
    if observed != ACTIVE_PLAN_SHA256_V1:
        _reject("PLAN_SHA256_DRIFT", "active plan", "admitted plan source bytes drift")
    registry_raw = _read_bounded_regular_file_v1(
        root / ACTIVE_REGISTRY_PATH_V1, MAX_ARTIFACT_BYTES_V1, "active plan registry"
    )
    admission_raw = _read_bounded_regular_file_v1(
        root / ADMISSION_RECEIPT_PATH_V1, MAX_ARTIFACT_BYTES_V1, "plan admission receipt"
    )
    registry_sha = _sha256_v1(registry_raw)
    admission_sha = _sha256_v1(admission_raw)
    if registry_sha != ACTIVE_REGISTRY_SHA256_V1 or admission_sha != ADMISSION_RECEIPT_SHA256_V1:
        _reject("ACTIVE_PLAN_ADMISSION_DRIFT", "active plan", "registry or receipt bytes drift")
    try:
        registry = json.loads(registry_raw)
        admission = json.loads(admission_raw)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        _reject("ACTIVE_PLAN_ADMISSION_DRIFT", "active plan", type(exc).__name__)
    if type(registry) is not dict or type(admission) is not dict:
        _reject("ACTIVE_PLAN_ADMISSION_DRIFT", "active plan", "objects required")
    active_plans = registry.get("active_plans")
    admitted_plan = admission.get("admitted_plan")
    if (
        registry.get("active_plan_count") != 1
        or type(active_plans) is not list
        or len(active_plans) != 1
        or type(active_plans[0]) is not dict
        or type(admitted_plan) is not dict
        or active_plans[0].get("plan_commit") != ACTIVE_PLAN_COMMIT_V1
        or active_plans[0].get("plan_sha256") != ACTIVE_PLAN_SHA256_V1
        or active_plans[0].get("admission_receipt_payload_sha256")
        != ADMISSION_RECEIPT_PAYLOAD_SHA256_V1
        or admitted_plan.get("commit") != ACTIVE_PLAN_COMMIT_V1
        or admitted_plan.get("plan_sha256") != ACTIVE_PLAN_SHA256_V1
        or admission.get("receipt_payload_sha256") != ADMISSION_RECEIPT_PAYLOAD_SHA256_V1
    ):
        _reject("ACTIVE_PLAN_ADMISSION_DRIFT", "active plan", "selection binding drift")
    return observed, registry_sha, admission_sha, ADMISSION_RECEIPT_PAYLOAD_SHA256_V1


def load_current_tau_compatibility_snapshot_v1(
    paths: TauReplayPathsV1,
    *,
    generation_source_commit: str | None = None,
) -> CurrentTauCompatibilitySnapshotV1:
    """Acquire exact Git objects and semantic observations for the pure core."""

    captured_head = _git_head_v1(paths.root)
    if generation_source_commit is not None and generation_source_commit != captured_head:
        _reject("GENERATION_SOURCE_DRIFT", "HEAD", "generation must bind current HEAD")
    implementation_commit = generation_source_commit or _implementation_subject_commit_v1(
        paths.root, captured_head
    )
    for ancestor, code in ((ACTIVE_PLAN_COMMIT_V1, "ACTIVE_PLAN_ANCESTRY"),):
        if not _git_is_ancestor_v1(paths.root, ancestor, captured_head):
            _reject(code, "HEAD", "required source commit is not on current lineage")
    if not _git_is_ancestor_v1(paths.root, implementation_commit, captured_head):
        _reject("IMPLEMENTATION_ANCESTRY", "HEAD", "implementation is off current lineage")
    checkout_bindings = _capture_replay_checkouts_v1(paths)
    sources = _load_sources_v1(paths, implementation_commit)
    signing = _signing_facts_v1(sources)
    rpc = _rpc_facts_v1(sources)
    profile = _profile_facts_v1(sources)
    require_success_envelope_v1(sources.current_tau["api_response.py"], "current:api_response.py")
    envelope = success_envelope_v1()
    plan_sha, registry_sha, admission_sha, admission_payload_sha = _load_active_plan_binding_v1(
        paths.root
    )
    snapshot = CurrentTauCompatibilitySnapshotV1(
        current_tau=sources.current_tau_pin,
        current_tau_lang=sources.current_tau_lang_pin,
        historical_bridge=sources.historical_pin,
        historical_local_profile=sources.historical_local_profile_pin,
        implementation=sources.implementation_pin,
        active_plan_sha256=plan_sha,
        active_registry_sha256=registry_sha,
        admission_receipt_sha256=admission_sha,
        admission_receipt_payload_sha256=admission_payload_sha,
        current_reserved_streams=literal_int_set_v1(
            sources.current_tau["tau_defs.py"], "current:tau_defs.py", "RESERVED_STREAMS"
        ),
        legacy_operation_streams=literal_string_assignments_v1(
            sources.historical_local_profile["src/integration/tau_testnet_dex_plugin.py"],
            "historical-local-profile:src/integration/tau_testnet_dex_plugin.py",
            LEGACY_OPERATION_KEYS_V1,
        ),
        current_user_tx_signing_fields=signing.current_fields,
        local_user_tx_signing_fields=signing.local_fields,
        historical_bridge_user_tx_signing_fields=signing.historical_fields,
        current_signing_sha256=signing_vector_sha256_v1(signing.current_fields),
        local_signing_sha256=signing_vector_sha256_v1(signing.local_fields),
        current_success_envelope_sha256=success_envelope_sha256_v1(),
        local_prefix_parser_accepts_current_envelope=legacy_prefix_parser_accepts_v1(
            sources.historical_local_profile["src/integration/tau_net_client.py"],
            envelope,
            "historical-local-profile:src/integration/tau_net_client.py",
        ),
        current_rpc_names_absent=rpc.current_absent,
        local_client_rpc_methods=rpc.local_methods,
        historical_bridge_rpc_names_present=rpc.historical_present,
        local_profile_force_test=profile.force_test,
        local_runner_forwards_force_test=profile.runner_forwards_force_test,
        local_runner_default_tau_env=profile.default_tau_env,
        current_tau_force_test_requires_test_env=profile.current_requires_test_env,
        historical_bridge_force_test_enters_mock_mode=profile.historical_enters_mock,
    )
    _require_capture_unchanged_v1(paths, captured_head, snapshot, checkout_bindings)
    return snapshot


def build_current_tau_compatibility_bytes_v1(
    paths: TauReplayPathsV1,
    *,
    generation_source_commit: str | None = None,
) -> bytes:
    snapshot = load_current_tau_compatibility_snapshot_v1(
        paths, generation_source_commit=generation_source_commit
    )
    return canonical_json_bytes_v1(build_current_tau_compatibility_artifact_v1(snapshot))


def main(argv: list[str] | None = None) -> int:
    parser = FailClosedArgumentParserV1(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    parser.add_argument("--tau-testnet-repo", type=Path, required=True)
    parser.add_argument("--tau-lang-repo", type=Path, required=True)
    parser.add_argument("--historical-bridge-repo", type=Path)
    parser.add_argument("--check", action="store_true")
    try:
        if _bootstrap_sys.flags.isolated and _bootstrap_sys.flags.no_site:
            unbound = _unbound_runtime_repository_imports_v1(
                REPO_ROOT,
                RUNTIME_EXECUTABLE_SOURCE_PATHS_V1,
            )
            if unbound:
                _reject(
                    "IMPLEMENTATION_RUNTIME_SOURCE_UNBOUND",
                    unbound[0],
                    "runtime repository import is absent from source manifest",
                )
        args = parser.parse_args(argv)
        paths = TauReplayPathsV1(
            args.root,
            args.tau_testnet_repo,
            args.tau_lang_repo,
            args.historical_bridge_repo or args.tau_testnet_repo,
        )
        generation_source_commit = None if args.check else _git_head_v1(args.root)
        data = build_current_tau_compatibility_bytes_v1(
            paths, generation_source_commit=generation_source_commit
        )
        target = args.root / JSON_OUTPUT
        if args.check:
            actual = _read_bounded_regular_file_v1(
                target,
                MAX_ARTIFACT_BYTES_V1,
                "current Tau compatibility artifact",
            )
            if actual != data:
                print(json.dumps(_builder_failure_report_v1("ARTIFACT_DRIFT"), sort_keys=True))
                return 1
        else:
            _atomic_replace_regular_file_v1(target, data)
        print(json.dumps({"ok": True, "json_sha256": _sha256_v1(data)}, sort_keys=True))
        return 0
    except (CurrentTauCompatibilityRejectV1, ShellRejectV1, OSError, TypeError, ValueError) as exc:
        code = (
            exc.code
            if isinstance(exc, (CurrentTauCompatibilityRejectV1, ShellRejectV1))
            else type(exc).__name__
        )
        print(json.dumps(_builder_failure_report_v1(code), sort_keys=True))
        return 1
    except Exception:
        print(json.dumps(_builder_failure_report_v1("BUILDER_INTERNAL_ERROR"), sort_keys=True))
        return 1


def _builder_failure_report_v1(code: str) -> dict[str, object]:
    return {
        "ok": False,
        "finding": code,
        "o003a_evidence_complete": False,
        "o003a_reviewed_current_tau_incompatibility_research_only": False,
        "direct_python_replay_conditional": False,
        "external_replay_trust_root_blocked": True,
        "o002_implemented": False,
        "production_authority": "NONE",
        "release_authority": "NONE",
        "settlement_authority": "NONE",
        "value_movement_authority": "NONE",
        "value_movement_claim_allowed": False,
        "vm_gates_closed": [],
    }


if __name__ == "__main__":
    raise SystemExit(main())
