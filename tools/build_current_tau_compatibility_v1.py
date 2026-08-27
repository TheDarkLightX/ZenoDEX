#!/usr/bin/env python3
"""Build replayable research evidence for the current-Tau compatibility gap."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Final, NoReturn

REPO_ROOT: Final = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.core.current_tau_compatibility_pins_v1 import (  # noqa: E402
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
    IMPLEMENTATION_SOURCE_PATHS_V1,
)
from src.core.current_tau_compatibility_v1 import (  # noqa: E402
    CurrentTauCompatibilityRejectV1,
    CurrentTauCompatibilitySnapshotV1,
    SourcePinV1,
    build_current_tau_compatibility_artifact_v1,
)
from src.integration.tau_net_client import tau_rpc_response_is_success  # noqa: E402
from tools.build_m6_normative_requirements_v1 import (  # noqa: E402
    ShellRejectV1,
    _atomic_replace_regular_file_v1,
    _git_head_v1,
    _git_is_ancestor_v1,
    _git_scalar_v1,
    _git_tree_v1,
    _read_bounded_regular_file_v1,
    _run_git_v1,
)
from tools.current_tau_source_analysis_v1 import (  # noqa: E402
    LEGACY_OPERATION_KEYS_V1,
    class_methods_v1,
    command_registry_keys_v1,
    force_test_requires_test_env_v1,
    historical_apply_app_tx_bridge_v1,
    historical_force_test_enters_mock_v1,
    literal_int_set_v1,
    literal_string_assignments_v1,
    require_success_envelope_v1,
    signing_vector_sha256_v1,
    single_profile_value_v1,
    success_envelope_sha256_v1,
    success_envelope_v1,
    user_tx_signing_fields_v1,
)
from tools.m6_normative_requirements_v1 import canonical_json_bytes_v1  # noqa: E402

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


@dataclass(frozen=True)
class ReplaySourcesV1:
    implementation_pin: SourcePinV1
    current_tau_pin: SourcePinV1
    current_tau_lang_pin: SourcePinV1
    historical_pin: SourcePinV1
    implementation: dict[str, bytes]
    current_tau: dict[str, bytes]
    historical: dict[str, bytes]


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
) -> tuple[SourcePinV1, dict[str, bytes]]:
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
    return SourcePinV1(commit, tree, tree_listing_sha256, tuple(observed_hashes)), sources


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
    return parent


def _implementation_source_hashes_v1(
    root: Path,
    commit: str,
) -> tuple[tuple[str, str], ...]:
    return tuple(
        (path, _sha256_v1(_git_source_bytes_v1(root, commit, path)))
        for path in IMPLEMENTATION_SOURCE_PATHS_V1
    )


def _require_worktree_sources_match_v1(
    root: Path,
    expected_sources: tuple[tuple[str, str], ...],
    role: str,
) -> None:
    for path, expected_sha in expected_sources:
        raw = _read_bounded_regular_file_v1(root / path, MAX_SOURCE_BYTES_V1, f"{role}:{path}")
        if _sha256_v1(raw) != expected_sha:
            _reject("WORKTREE_SOURCE_DRIFT", path, f"{role} working source differs from pin")


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
    if _git_head_v1(paths.historical_bridge_repo) != HISTORICAL_BRIDGE_COMMIT_V1:
        _reject(
            "HISTORICAL_BRIDGE_HEAD_DRIFT",
            "historical_bridge.HEAD",
            "selected bridge checkout is not the pinned historical source",
        )
    _require_worktree_sources_match_v1(
        paths.historical_bridge_repo,
        HISTORICAL_BRIDGE_SOURCE_SHA256_V1,
        "historical bridge",
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
        implementation,
        current_tau,
        historical,
    )


def _signing_facts_v1(sources: ReplaySourcesV1) -> SigningFactsV1:
    current_fields = user_tx_signing_fields_v1(
        sources.current_tau["commands/sendtx.py"],
        "current:commands/sendtx.py",
        "_get_signing_message_bytes",
    )
    local_fields = user_tx_signing_fields_v1(
        sources.implementation["src/integration/tau_net_client.py"],
        "implementation:src/integration/tau_net_client.py",
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
    current_absent = (
        "apply_app_tx",
        *(name for name in names[1:] if name not in current_registry),
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
        sources.implementation["src/integration/tau_net_client.py"],
        "implementation:src/integration/tau_net_client.py",
        "TauNetTcpClient",
    )
    local_methods = tuple(name for name in names[1:] if name in local_method_set)
    return RpcFactsV1(current_absent, local_methods, historical_present)


def _profile_facts_v1(sources: ReplaySourcesV1) -> ProfileFactsV1:
    compose = sources.implementation["docker-compose.local-testnet.yml"]
    runner_text = sources.implementation["tools/run_local_tau_node_container.sh"].decode("utf-8")
    e2e_text = sources.implementation["tools/tau_testnet_local_e2e.py"].decode("utf-8")
    return ProfileFactsV1(
        force_test=single_profile_value_v1(
            compose,
            "docker-compose.local-testnet.yml",
            "TAU_FORCE_TEST",
        ),
        runner_forwards_force_test=(
            '"${TAU_FORCE_TEST:-1}" == "1"' in runner_text and "ARGS+=(--force-test)" in runner_text
        ),
        default_tau_env=(
            "development"
            if 'env.setdefault("TAU_ENV", env.get("TAU_ENV", "development"))' in e2e_text
            else ""
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


def _require_profile_tau_source_bound_v1(paths: TauReplayPathsV1) -> None:
    configured = paths.root / "external" / "tau-testnet"
    try:
        configured_real = configured.resolve(strict=True)
        supplied_real = paths.historical_bridge_repo.resolve(strict=True)
    except OSError as exc:
        _reject("PROFILE_TAU_SOURCE_UNBOUND", str(configured), type(exc).__name__)
    if configured_real != supplied_real:
        _reject(
            "PROFILE_TAU_SOURCE_UNBOUND",
            str(configured),
            "local runtime path differs from reviewed historical source",
        )


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
    _require_profile_tau_source_bound_v1(paths)
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
        implementation=sources.implementation_pin,
        active_plan_sha256=plan_sha,
        active_registry_sha256=registry_sha,
        admission_receipt_sha256=admission_sha,
        admission_receipt_payload_sha256=admission_payload_sha,
        current_reserved_streams=literal_int_set_v1(
            sources.current_tau["tau_defs.py"], "current:tau_defs.py", "RESERVED_STREAMS"
        ),
        legacy_operation_streams=literal_string_assignments_v1(
            sources.implementation["src/integration/tau_testnet_dex_plugin.py"],
            "implementation:src/integration/tau_testnet_dex_plugin.py",
            LEGACY_OPERATION_KEYS_V1,
        ),
        current_user_tx_signing_fields=signing.current_fields,
        local_user_tx_signing_fields=signing.local_fields,
        historical_bridge_user_tx_signing_fields=signing.historical_fields,
        current_signing_sha256=signing_vector_sha256_v1(signing.current_fields),
        local_signing_sha256=signing_vector_sha256_v1(signing.local_fields),
        current_success_envelope_sha256=success_envelope_sha256_v1(),
        local_prefix_parser_accepts_current_envelope=tau_rpc_response_is_success(envelope),
        current_rpc_names_absent=rpc.current_absent,
        local_client_rpc_methods=rpc.local_methods,
        historical_bridge_rpc_names_present=rpc.historical_present,
        local_profile_force_test=profile.force_test,
        local_runner_forwards_force_test=profile.runner_forwards_force_test,
        local_runner_default_tau_env=profile.default_tau_env,
        current_tau_force_test_requires_test_env=profile.current_requires_test_env,
        historical_bridge_force_test_enters_mock_mode=profile.historical_enters_mock,
    )
    if _git_head_v1(paths.root) != captured_head:
        _reject("HEAD_CHANGED_DURING_CAPTURE", "HEAD", "Git HEAD changed during replay")
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
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    parser.add_argument("--tau-testnet-repo", type=Path, required=True)
    parser.add_argument("--tau-lang-repo", type=Path, required=True)
    parser.add_argument("--historical-bridge-repo", type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    paths = TauReplayPathsV1(
        args.root,
        args.tau_testnet_repo,
        args.tau_lang_repo,
        args.historical_bridge_repo or args.tau_testnet_repo,
    )
    try:
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


def _builder_failure_report_v1(code: str) -> dict[str, object]:
    return {
        "ok": False,
        "finding": code,
        "o003a_evidence_complete": False,
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
