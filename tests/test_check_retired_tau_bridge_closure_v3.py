from __future__ import annotations

import json
import subprocess
from dataclasses import replace
from pathlib import Path
from typing import Callable, cast

import pytest

from tools import build_retired_tau_bridge_closure_v3 as closure_builder
from tools import check_retired_tau_bridge_closure_v3 as closure_checker
from tools import retired_tau_bridge_closure_v3 as closure_core
from tools.retired_tau_bridge_closure_v3 import (
    ARTIFACT_SCHEMA_V3,
    BASELINE_COMMIT_V3,
    BASELINE_DISCOVERY_PATH_COUNT_V3,
    BASELINE_DISCOVERY_PATH_SET_SHA256_V3,
    BASELINE_PIN_PATHS_V3,
    BASELINE_TREE_V3,
    CURRENT_OPERATION_IDS_V3,
    DIRECT_CONSUMER_PATH_SET_SHA256_V3,
    DIRECT_CONSUMER_PATHS_V3,
    EXPECTED_BASELINE_EDGE_ROOT_V3,
    EXPECTED_CURRENT_EDGE_ROOT_V3,
    EXPECTED_CURRENT_ROUTE_SOURCE_ROOT_V3,
    RESEARCH_OPERATION_IDS_V3,
    SUBJECT_PIN_PATHS_V3,
    ClosureRejectV3,
    ImportEdgeV3,
    PythonImportDiscoveryV3,
    SourceFileV3,
    SourceSnapshotV3,
    SubjectSnapshotV3,
    _git_blob_sha,
    _operation_registry,
    _path_set_sha256,
    build_artifact_v3,
    canonical_json_bytes_v3,
    check_artifact_v3,
    derive_closure_v3,
)

ROOT = Path(__file__).resolve().parents[1]


def _git_output(*arguments: str) -> bytes:
    return subprocess.check_output(  # noqa: S603 - fixed test-only Git command
        ("git", *arguments),  # noqa: S607 - test environment resolves Git
        cwd=ROOT,
    )


def _temp_git_output(root: Path, *arguments: str) -> bytes:
    return subprocess.check_output(  # noqa: S603 - fixed test-only Git command
        ("git", *arguments),  # noqa: S607 - test environment resolves Git
        cwd=root,
    )


def _temp_git(root: Path, *arguments: str) -> None:
    subprocess.run(  # noqa: S603 - fixed test-only Git command
        ("git", *arguments),  # noqa: S607 - test environment resolves Git
        cwd=root,
        check=True,
        stdout=subprocess.DEVNULL,
    )


def _stage_a_repo(root: Path) -> tuple[str, str]:
    _temp_git(root, "init", "--quiet")
    _temp_git(root, "config", "user.email", "o003b-test@example.invalid")
    _temp_git(root, "config", "user.name", "O003B Test")
    (root / "stage_a.txt").write_text("stage-a\n", encoding="utf-8")
    _temp_git(root, "add", "stage_a.txt")
    _temp_git(root, "commit", "--quiet", "-m", "stage A")
    commit = _temp_git_output(root, "rev-parse", "HEAD").decode("ascii").strip()
    tree = _temp_git_output(root, "rev-parse", "HEAD^{tree}").decode("ascii").strip()
    return commit, tree


def _loader_subject_repo(
    root: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> tuple[str, str]:
    _temp_git(root, "init", "--quiet")
    _temp_git(root, "config", "user.email", "o003b-test@example.invalid")
    _temp_git(root, "config", "user.name", "O003B Test")
    pinned = root / "pinned.py"
    pinned.write_text("BASELINE = True\n", encoding="utf-8")
    _temp_git(root, "add", "pinned.py")
    _temp_git(root, "commit", "--quiet", "-m", "baseline")
    baseline_commit = _temp_git_output(root, "rev-parse", "HEAD").decode("ascii").strip()
    baseline_tree = _temp_git_output(root, "rev-parse", "HEAD^{tree}").decode("ascii").strip()
    pinned.write_text("STAGE_A = True\n", encoding="utf-8")
    _temp_git(root, "add", "pinned.py")
    _temp_git(root, "commit", "--quiet", "-m", "stage A")
    evidence_commit = _temp_git_output(root, "rev-parse", "HEAD").decode("ascii").strip()
    monkeypatch.setattr(closure_builder, "BASELINE_COMMIT_V3", baseline_commit)
    monkeypatch.setattr(closure_builder, "BASELINE_TREE_V3", baseline_tree)
    monkeypatch.setattr(closure_builder, "BASELINE_PIN_PATHS_V3", ("pinned.py",))
    monkeypatch.setattr(closure_builder, "SUBJECT_PIN_PATHS_V3", ("pinned.py",))
    return baseline_commit, evidence_commit


def _commit_stage_b(root: Path, artifact_path: Path, raw: bytes, *extra: str) -> str:
    output = root / artifact_path
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_bytes(raw)
    for relative_path in extra:
        extra_path = root / relative_path
        extra_path.parent.mkdir(parents=True, exist_ok=True)
        extra_path.write_text("unexpected\n", encoding="utf-8")
    _temp_git(root, "add", artifact_path.as_posix(), *extra)
    _temp_git(root, "commit", "--quiet", "-m", "stage B")
    return _temp_git_output(root, "rev-parse", "HEAD").decode("ascii").strip()


def _source(path: str, data: bytes) -> SourceFileV3:
    return SourceFileV3(path=path, git_blob_sha=_git_blob_sha(data), data=data)


@pytest.fixture(scope="module")
def exact_snapshot() -> SubjectSnapshotV3:
    baseline_files = tuple(
        _source(path, _git_output("show", f"{BASELINE_COMMIT_V3}:{path}"))
        for path in BASELINE_PIN_PATHS_V3
    )
    subject_files = tuple(
        _source(path, (ROOT / path).read_bytes()) for path in SUBJECT_PIN_PATHS_V3
    )
    head = _git_output("rev-parse", "HEAD").decode("ascii").strip()
    tree = _git_output("rev-parse", "HEAD^{tree}").decode("ascii").strip()
    baseline_discovery = closure_builder._git_python_discovery_v3(
        ROOT,
        BASELINE_COMMIT_V3,
    )
    subject_discovery = closure_builder._worktree_python_discovery_v3(ROOT)
    return SubjectSnapshotV3(
        captured_head=head,
        rechecked_head=head,
        baseline=SourceSnapshotV3(
            commit=BASELINE_COMMIT_V3,
            tree=BASELINE_TREE_V3,
            files=baseline_files,
            discovery=baseline_discovery,
        ),
        subject=SourceSnapshotV3(
            commit=head,
            tree=tree,
            files=subject_files,
            discovery=subject_discovery,
        ),
        baseline_is_subject_ancestor=True,
        subject_is_current_ancestor=True,
        current_discovery=subject_discovery,
    )


def _mutate_subject(
    snapshot: SubjectSnapshotV3,
    path: str,
    mutate: Callable[[bytes], bytes],
) -> SubjectSnapshotV3:
    files = list(snapshot.subject.files)
    index = next(index for index, item in enumerate(files) if item.path == path)
    data = mutate(files[index].data)
    files[index] = _source(path, data)
    return replace(snapshot, subject=replace(snapshot.subject, files=tuple(files)))


def _artifact_with_root(value: dict[str, object]) -> bytes:
    unsigned = dict(value)
    unsigned.pop("certificate_root", None)
    value["certificate_root"] = (
        __import__("hashlib").sha256(canonical_json_bytes_v3(unsigned)).hexdigest()
    )
    return canonical_json_bytes_v3(value)


def _reject_code(snapshot: SubjectSnapshotV3) -> str:
    with pytest.raises(ClosureRejectV3) as exc_info:
        build_artifact_v3(snapshot)
    return exc_info.value.code


def _assert_builder_failure_authority_none(report: dict[str, object]) -> None:
    assert report["ok"] is False
    assert report["artifact_sha256"] == ""
    assert report["closed_value_movement_gates"] == 0
    assert report["production_authority"] == "NONE"
    assert report["release_authority"] == "NONE"
    assert report["settlement_authority"] == "NONE"
    assert report["value_movement_authority"] == "NONE"


def test_source_loaders_accept_pinned_executable_regular_blob() -> None:
    path = "tools/check_production_promotion_evidence_manifest.py"
    head = _git_output("rev-parse", "HEAD").decode("ascii").strip()

    baseline = closure_builder._tree_source_file_v3(ROOT, BASELINE_COMMIT_V3, path)
    subject = closure_builder._subject_source_file_v3(
        ROOT,
        captured_head=head,
        subject_commit=head,
        path=path,
    )

    assert _git_output("ls-tree", BASELINE_COMMIT_V3, "--", path).startswith(b"100755 blob ")
    assert _git_output("ls-tree", head, "--", path).startswith(b"100755 blob ")
    assert baseline.path == subject.path == path


def test_exact_import_projection_and_closed_operation_registry(
    exact_snapshot: SubjectSnapshotV3,
) -> None:
    _, _, rows, projection = derive_closure_v3(exact_snapshot)

    assert projection["direct_consumer_path_count"] == 36
    assert projection["direct_consumer_path_set_sha256"] == (DIRECT_CONSUMER_PATH_SET_SHA256_V3)
    assert projection["baseline_edge_count"] == 128
    assert projection["current_edge_count"] == 92
    assert projection["unchanged_edge_count"] == 92
    assert projection["removed_edge_count"] == 36
    assert projection["current_only_edge_count"] == 0
    assert projection["baseline_python_path_count"] == (BASELINE_DISCOVERY_PATH_COUNT_V3)
    assert projection["baseline_python_path_set_sha256"] == (BASELINE_DISCOVERY_PATH_SET_SHA256_V3)
    assert projection["baseline_discovered_consumer_count"] == 36
    assert projection["baseline_discovered_edge_count"] == 128
    assert projection["subject_discovered_consumer_count"] == 19
    assert projection["subject_discovered_edge_count"] == 92
    assert projection["python_discovery_scope"] == (
        "GIT_TREE_BASELINE_AND_SUBJECT_PLUS_CURRENT_INDEX_OR_UNTRACKED_"
        "NONIGNORED_NONTEST_NONGENERATED_STATIC_PYTHON_IMPORTS"
    )
    assert "tests/integration/test_zusd_tau_token.py" in SUBJECT_PIN_PATHS_V3
    assert projection["baseline_edge_root_sha256"] == EXPECTED_BASELINE_EDGE_ROOT_V3
    assert projection["current_edge_root_sha256"] == EXPECTED_CURRENT_EDGE_ROOT_V3
    assert projection["current_route_source_root_sha256"] == (EXPECTED_CURRENT_ROUTE_SOURCE_ROOT_V3)
    assert projection["import_classification_counts"] == {
        "QUARANTINED": 0,
        "RESEARCH_ORACLE": 92,
        "REMOVED": 36,
    }
    assert _path_set_sha256(DIRECT_CONSUMER_PATHS_V3) == (DIRECT_CONSUMER_PATH_SET_SHA256_V3)
    assert {
        operation_id
        for row in rows
        for operation_id in cast(list[str], row["current_operation_ids"])
    } == set(CURRENT_OPERATION_IDS_V3)
    assert {
        operation_id
        for row in rows
        for operation_id in cast(list[str], row["research_operation_ids"])
    } == set(RESEARCH_OPERATION_IDS_V3)


def test_certificate_is_canonical_deterministic_and_authority_free(
    exact_snapshot: SubjectSnapshotV3,
) -> None:
    first = build_artifact_v3(exact_snapshot)
    second = build_artifact_v3(exact_snapshot)
    artifact = json.loads(first)

    assert first == second
    assert artifact["schema"] == ARTIFACT_SCHEMA_V3
    assert artifact["claim_ceiling"] == {
        "closed_value_movement_gates": 0,
        "production_authority": "NONE",
        "release_authority": "NONE",
        "settlement_authority": "NONE",
        "value_movement_authority": "NONE",
        "value_movement_claim_allowed": False,
    }
    report = check_artifact_v3(first, exact_snapshot)
    assert report["ok"] is True
    assert report["current_only_import_edge_count"] == 0
    assert report["closed_value_movement_gates"] == 0


@pytest.mark.parametrize(
    ("path", "statement"),
    (
        (
            "src/agents/intent_signer.py",
            b"\nfrom src.integration.tau_net_client import TauNetTcpClient\n",
        ),
        (
            "src/integration/confidential_sealed_bid_api.py",
            b"\nfrom .tau_net_client import TauNetTcpClient as injected\n",
        ),
        (
            "src/integration/confidential_sealed_bid_api.py",
            b"\nfrom ..integration.tau_net_client import TauNetTcpClient as injected\n",
        ),
        (
            "src/agents/intent_signer.py",
            b"\nfrom src.integration import tau_net_client as injected\n",
        ),
        (
            "src/agents/intent_signer.py",
            b"\nimport src.integration.tau_net_client as injected\n",
        ),
    ),
)
def test_new_absolute_relative_and_module_imports_fail_with_exact_code(
    exact_snapshot: SubjectSnapshotV3,
    path: str,
    statement: bytes,
) -> None:
    mutated = _mutate_subject(exact_snapshot, path, lambda data: data + statement)

    assert _reject_code(mutated) == "UNCLASSIFIED_RETIRED_TAU_BRIDGE_IMPORT"


def test_restoring_removed_autotrader_import_fails_route_witness_first(
    exact_snapshot: SubjectSnapshotV3,
) -> None:
    path = "src/integration/api_server.py"
    restored = b"from src.integration.autotrader_live_api import handle_autotrader_live_request\n"
    mutated = _mutate_subject(
        exact_snapshot,
        path,
        lambda data: data + b"\n" + restored,
    )

    assert _reject_code(mutated) == "API_AUTOTRADER_STARTUP_REFUSAL"


def test_new_bridge_import_outside_baseline_seed_fails_closed(
    exact_snapshot: SubjectSnapshotV3,
) -> None:
    path = "src/integration/o003b_out_of_seed_mutant.py"
    edge = ImportEdgeV3(
        source_path=path,
        scope="<module>",
        dependency_kind="FROM",
        target_module="src.integration.tau_net_client",
        imported_member="TauNetTcpClient",
        bound_name="TauNetTcpClient",
    )
    discovery = exact_snapshot.subject.discovery
    assert discovery is not None
    mutated_discovery = replace(
        discovery,
        paths=tuple(sorted((*discovery.paths, path))),
        edges=tuple(sorted((*discovery.edges, edge))),
    )
    mutated = replace(
        exact_snapshot,
        subject=replace(
            exact_snapshot.subject,
            discovery=mutated_discovery,
        ),
        current_discovery=mutated_discovery,
    )

    assert _reject_code(mutated) == "UNCLASSIFIED_RETIRED_TAU_BRIDGE_IMPORT"


def test_baseline_discovery_path_set_mutation_fails_closed(
    exact_snapshot: SubjectSnapshotV3,
) -> None:
    discovery = exact_snapshot.baseline.discovery
    assert discovery is not None
    mutated_discovery = replace(
        discovery,
        paths=tuple(sorted((*discovery.paths, "baseline-mutant.py"))),
    )
    mutated = replace(
        exact_snapshot,
        baseline=replace(
            exact_snapshot.baseline,
            discovery=mutated_discovery,
        ),
    )

    assert _reject_code(mutated) == "BASELINE_DISCOVERY_PATH_SET"


@pytest.mark.parametrize(
    ("path", "needle", "code"),
    (
        (
            "src/integration/api_server.py",
            b"AUTOTRADER_LIVE_API_ENABLED is unavailable",
            "API_AUTOTRADER_STARTUP_REFUSAL",
        ),
        (
            "tools/zenodex_local_signer.py",
            b"raise ValueError(RETIRED_TAU_TRANSACTION_SIGNING_ROUTE_ERROR)",
            "LOCAL_SIGNER_RETIREMENT_GUARD",
        ),
        (
            "tools/zenoctl_testnet_local/lifecycle.py",
            b'refuse_current_local_operator_operation_v1("historical_seed_api_state_donor")',
            "LIFECYCLE_DONOR_GUARD",
        ),
        (
            "tools/check_production_boundary.py",
            b"retired_tau_bridge_classified_without_production_authority",
            "PRODUCTION_BOUNDARY_NONAUTHORITY",
        ),
    ),
)
def test_route_witness_mutations_fail_before_artifact_replay(
    exact_snapshot: SubjectSnapshotV3,
    path: str,
    needle: bytes,
    code: str,
) -> None:
    mutated = _mutate_subject(
        exact_snapshot,
        path,
        lambda data: data.replace(needle, b"MUTATED_WITNESS"),
    )

    assert _reject_code(mutated) == code


@pytest.mark.parametrize(
    ("path", "needle", "inserted", "code"),
    (
        (
            "src/integration/api_server.py",
            b"    if type(config) is not ApiServerConfig or any(\n",
            b"    httpd.compromised = True\n",
            "API_AUTOTRADER_ATTACHMENT_GUARD",
        ),
        (
            "src/integration/zenodex_local_signer.py",
            b"        raise RetiredTauTransactionSigningRouteError(\n",
            b"        self.compromised = True\n",
            "LOCAL_SIGNER_RETIREMENT_GUARD",
        ),
        (
            "tools/zenoctl_testnet_local/lifecycle.py",
            b'    return refuse_current_local_operator_operation_v1("seed_api_state")\n',
            b"    engine.compromised = True\n",
            "LIFECYCLE_DONOR_GUARD",
        ),
    ),
)
def test_route_guard_rejects_mutation_inserted_before_refusal(
    exact_snapshot: SubjectSnapshotV3,
    path: str,
    needle: bytes,
    inserted: bytes,
    code: str,
) -> None:
    mutated = _mutate_subject(
        exact_snapshot,
        path,
        lambda data: data.replace(needle, inserted + needle, 1),
    )

    assert _reject_code(mutated) == code


def test_api_attachment_guard_rejects_nested_safe_decoy_after_unsafe_real_function(
    exact_snapshot: SubjectSnapshotV3,
) -> None:
    path = "src/integration/api_server.py"
    guard = b"    if type(config) is not ApiServerConfig or any(\n"
    decoy = b"""

def _o003b_api_attachment_decoy() -> object:
    def _attach_api_server_state(httpd, config):
        if type(config) is not ApiServerConfig or any(
            value is not False for value in (
                config.perps_wallet_enabled,
                config.zusd_tau_wallet_enabled,
                config.zusd_monetary_wallet_enabled,
                config.autotrader_live_enabled,
                config.confidential_sealed_bid_asset_settlement_enabled,
            )
        ):
            refuse_current_local_operator_operation_v1("api_server_state_attachment")
    return _attach_api_server_state
"""
    mutated = _mutate_subject(
        exact_snapshot,
        path,
        lambda data: (
            data.replace(
                guard,
                b"    httpd.compromised = True\n" + guard,
                1,
            )
            + decoy
        ),
    )

    assert _reject_code(mutated) == "API_AUTOTRADER_ATTACHMENT_GUARD"


def test_lifecycle_guard_rejects_nested_safe_decoy_after_unsafe_real_function(
    exact_snapshot: SubjectSnapshotV3,
) -> None:
    path = "tools/zenoctl_testnet_local/lifecycle.py"
    refusal = b'    return refuse_current_local_operator_operation_v1("seed_api_state")\n'
    decoy = b"""

def _o003b_lifecycle_decoy() -> object:
    def _seed_api_state():
        return refuse_current_local_operator_operation_v1("seed_api_state")
    return _seed_api_state
"""
    mutated = _mutate_subject(
        exact_snapshot,
        path,
        lambda data: (
            data.replace(
                refusal,
                b"    engine.compromised = True\n" + refusal,
                1,
            )
            + decoy
        ),
    )

    assert _reject_code(mutated) == "LIFECYCLE_DONOR_GUARD"


def test_direct_signer_guard_rejects_nested_safe_class_decoy_after_unsafe_real_method(
    exact_snapshot: SubjectSnapshotV3,
) -> None:
    path = "src/integration/zenodex_local_signer.py"
    refusal = b"        raise RetiredTauTransactionSigningRouteError(\n"
    decoy = b"""

def _o003b_signer_class_decoy() -> object:
    class LocalSignerVault:
        def sign_tau_transaction_payload(self):
            raise RetiredTauTransactionSigningRouteError(
                RETIRED_TAU_TRANSACTION_SIGNING_ROUTE_ERROR
            )
    return LocalSignerVault
"""
    mutated = _mutate_subject(
        exact_snapshot,
        path,
        lambda data: (
            data.replace(
                refusal,
                b"        self.compromised = True\n" + refusal,
                1,
            )
            + decoy
        ),
    )

    assert _reject_code(mutated) == "LOCAL_SIGNER_RETIREMENT_GUARD"


@pytest.mark.parametrize(
    ("path", "appended", "code"),
    (
        (
            "tools/zenodex_local_signer.py",
            b"\n\ndef _unsafe_rebound_post(self):\n"
            b"    self.server.vault\n\n"
            b"_LocalSignerHttpHandler.do_POST = _unsafe_rebound_post\n",
            "LOCAL_SIGNER_RETIREMENT_GUARD",
        ),
        (
            "tools/zenodex_local_signer.py",
            b"\nHandlerAlias = _LocalSignerHttpHandler\n"
            b"HandlerAlias.do_POST = lambda self: self.server.vault\n",
            "LOCAL_SIGNER_RETIREMENT_GUARD",
        ),
        (
            "tools/zenodex_local_signer.py",
            b'\nexec("_LocalSignerHttpHandler.do_POST = unsafe")\n',
            "LOCAL_SIGNER_RETIREMENT_GUARD",
        ),
        (
            "tools/zenodex_local_signer.py",
            b"\n\ndef _unsafe_rebound_post(self):\n"
            b"    self.server.vault\n\n"
            b'type.__setattr__(_LocalSignerHttpHandler, "do_POST", _unsafe_rebound_post)\n',
            "LOCAL_SIGNER_RETIREMENT_GUARD",
        ),
        (
            "tools/zenodex_local_signer.py",
            b"\ncmd_sign_tau_transaction_payload = "
            b"lambda args: read_local_signer_vault(args.vault)\n",
            "LOCAL_SIGNER_RETIREMENT_GUARD",
        ),
        (
            "src/integration/zenodex_local_signer.py",
            b"\n\ndef _unsafe_direct_signer(self, **kwargs):\n"
            b'    return self._unlock_private_key_hex(kwargs["passphrase"])\n\n'
            b"LocalSignerVault.sign_tau_transaction_payload = _unsafe_direct_signer\n",
            "LOCAL_SIGNER_RETIREMENT_GUARD",
        ),
        (
            "src/integration/api_server.py",
            b"\n_attach_api_server_state = lambda httpd, config: "
            b"setattr(httpd, 'compromised', True)\n",
            "API_AUTOTRADER_ATTACHMENT_GUARD",
        ),
        (
            "tools/zenoctl_testnet_local/lifecycle.py",
            b"\ndel _seed_api_state\n",
            "LIFECYCLE_DONOR_GUARD",
        ),
    ),
    ids=(
        "http-attribute-assignment",
        "http-direct-alias",
        "http-exec-rebind",
        "http-type-setattr",
        "cli-name-assignment",
        "direct-signer-attribute-assignment",
        "api-name-assignment",
        "lifecycle-name-delete",
    ),
)
def test_mounted_route_guard_rejects_post_definition_binding_rewrite(
    exact_snapshot: SubjectSnapshotV3,
    path: str,
    appended: bytes,
    code: str,
) -> None:
    mutated = _mutate_subject(
        exact_snapshot,
        path,
        lambda data: data + appended,
    )

    assert _reject_code(mutated) == code


@pytest.mark.parametrize(
    "appended",
    (
        b"\n\ndef _unsafe_rebound_post(self):\n"
        b"    self.server.vault\n\n"
        b"HandlerAlias, = (_LocalSignerHttpHandler,)\n"
        b"HandlerAlias.do_POST = _unsafe_rebound_post\n",
        b"\n\ndef _unsafe_rebound_post(self):\n"
        b"    self.server.vault\n\n"
        b'type.__setattr__(globals()["_LocalSignerHttpHandler"], '
        b'"do_POST", _unsafe_rebound_post)\n',
    ),
    ids=("tuple-alias", "globals-subscript"),
)
def test_fixed_route_source_root_rejects_binding_alias_indirection(
    exact_snapshot: SubjectSnapshotV3,
    appended: bytes,
) -> None:
    mutated = _mutate_subject(
        exact_snapshot,
        "tools/zenodex_local_signer.py",
        lambda data: data + appended,
    )

    assert _reject_code(mutated) == "CURRENT_ROUTE_SOURCE_SET"


def test_api_route_guard_rejects_delete_inserted_before_refusal(
    exact_snapshot: SubjectSnapshotV3,
) -> None:
    path = "src/integration/api_server.py"
    needle = b"    if type(config) is not ApiServerConfig or any(\n"
    mutated = _mutate_subject(
        exact_snapshot,
        path,
        lambda data: data.replace(
            needle,
            b"    del httpd.compromised\n" + needle,
            1,
        ),
    )

    assert _reject_code(mutated) == "API_AUTOTRADER_ATTACHMENT_GUARD"


def test_http_signer_guard_rejects_server_access_before_retired_route(
    exact_snapshot: SubjectSnapshotV3,
) -> None:
    path = "tools/zenodex_local_signer.py"
    needle = b'        if urlsplit(self.path).path == "/sign-tau-transaction-payload":\n'
    mutated = _mutate_subject(
        exact_snapshot,
        path,
        lambda data: data.replace(
            needle,
            b'        getattr(self.server, "vault")\n' + needle,
            1,
        ),
    )

    assert _reject_code(mutated) == "LOCAL_SIGNER_RETIREMENT_GUARD"


def test_http_signer_guard_rejects_allowed_origin_else_effect(
    exact_snapshot: SubjectSnapshotV3,
) -> None:
    path = "tools/zenodex_local_signer.py"
    needle = (
        b"        if self._reject_disallowed_origin(require_origin=True):\n"
        b"            return\n"
        b'        if urlsplit(self.path).path == "/sign-tau-transaction-payload":\n'
    )
    mutated = _mutate_subject(
        exact_snapshot,
        path,
        lambda data: data.replace(
            needle,
            b"        if self._reject_disallowed_origin(require_origin=True):\n"
            b"            return\n"
            b"        else:\n"
            b"            self.server.vault\n"
            b'        if urlsplit(self.path).path == "/sign-tau-transaction-payload":\n',
            1,
        ),
    )

    assert _reject_code(mutated) == "LOCAL_SIGNER_RETIREMENT_GUARD"


def test_http_signer_guard_rejects_raw_path_comparison(
    exact_snapshot: SubjectSnapshotV3,
) -> None:
    path = "tools/zenodex_local_signer.py"
    normalized = b'urlsplit(self.path).path == "/sign-tau-transaction-payload"'
    mutated = _mutate_subject(
        exact_snapshot,
        path,
        lambda data: data.replace(
            normalized,
            b'self.path == "/sign-tau-transaction-payload"',
            1,
        ),
    )

    assert _reject_code(mutated) == "LOCAL_SIGNER_RETIREMENT_GUARD"


@pytest.mark.parametrize(
    ("needle", "replacement"),
    (
        (
            b"    def do_POST(self) -> None:\n",
            b"    async def do_POST(self) -> None:\n",
        ),
        (
            b"    def do_POST(self) -> None:\n",
            b"    def do_POST(self, required: object) -> None:\n",
        ),
        (
            b"    def do_POST(self) -> None:\n",
            b"    @staticmethod\n    def do_POST(self) -> None:\n",
        ),
        (
            b"class _LocalSignerHttpHandler(BaseHTTPRequestHandler):\n",
            b"class _LocalSignerHttpHandler(object):\n",
        ),
        (
            b"class _LocalSignerHttpHandler(BaseHTTPRequestHandler):\n",
            b"@staticmethod\nclass _LocalSignerHttpHandler(BaseHTTPRequestHandler):\n",
        ),
    ),
    ids=(
        "async-method",
        "required-argument",
        "staticmethod",
        "wrong-base",
        "decorated-class",
    ),
)
def test_http_signer_guard_rejects_uncallable_handler_shape(
    exact_snapshot: SubjectSnapshotV3,
    needle: bytes,
    replacement: bytes,
) -> None:
    mutated = _mutate_subject(
        exact_snapshot,
        "tools/zenodex_local_signer.py",
        lambda data: data.replace(needle, replacement, 1),
    )

    assert _reject_code(mutated) == "LOCAL_SIGNER_RETIREMENT_GUARD"


def test_http_signer_guard_rejects_nested_safe_decoy_after_unsafe_real_method(
    exact_snapshot: SubjectSnapshotV3,
) -> None:
    path = "tools/zenodex_local_signer.py"
    guard = b'        if urlsplit(self.path).path == "/sign-tau-transaction-payload":\n'
    decoy = b"""

def _o003b_decoy_handler() -> object:
    def do_POST(self) -> None:
        if self._reject_disallowed_origin(require_origin=True):
            return
        if urlsplit(self.path).path == "/sign-tau-transaction-payload":
            self._write_json(
                410,
                {
                    "ok": False,
                    "error": RETIRED_TAU_TRANSACTION_SIGNING_ROUTE_ERROR,
                },
            )
            return
    return do_POST
"""
    mutated = _mutate_subject(
        exact_snapshot,
        path,
        lambda data: (
            data.replace(
                guard,
                b"        self.server.vault\n" + guard,
                1,
            )
            + decoy
        ),
    )

    assert _reject_code(mutated) == "LOCAL_SIGNER_RETIREMENT_GUARD"


def test_http_signer_guard_rejects_server_access_after_retired_response(
    exact_snapshot: SubjectSnapshotV3,
) -> None:
    path = "tools/zenodex_local_signer.py"
    needle = b"            )\n            return\n        vault = self.server.vault"
    mutated = _mutate_subject(
        exact_snapshot,
        path,
        lambda data: data.replace(
            needle,
            b"            )\n"
            b"            self.server.vault\n"
            b"            return\n"
            b"        vault = self.server.vault",
            1,
        ),
    )

    assert _reject_code(mutated) == "LOCAL_SIGNER_RETIREMENT_GUARD"


def test_cli_signer_guard_rejects_vault_access_before_retired_route(
    exact_snapshot: SubjectSnapshotV3,
) -> None:
    path = "tools/zenodex_local_signer.py"
    needle = b"    raise ValueError(RETIRED_TAU_TRANSACTION_SIGNING_ROUTE_ERROR)\n"
    mutated = _mutate_subject(
        exact_snapshot,
        path,
        lambda data: data.replace(
            needle,
            b"    read_local_signer_vault(args.vault)\n" + needle,
            1,
        ),
    )

    assert _reject_code(mutated) == "LOCAL_SIGNER_RETIREMENT_GUARD"


def test_cli_signer_guard_rejects_nested_safe_decoy_after_unsafe_real_function(
    exact_snapshot: SubjectSnapshotV3,
) -> None:
    path = "tools/zenodex_local_signer.py"
    refusal = b"    raise ValueError(RETIRED_TAU_TRANSACTION_SIGNING_ROUTE_ERROR)\n"
    decoy = b"""

def _o003b_decoy_cli() -> object:
    def cmd_sign_tau_transaction_payload(args: argparse.Namespace) -> int:
        raise ValueError(RETIRED_TAU_TRANSACTION_SIGNING_ROUTE_ERROR)
    return cmd_sign_tau_transaction_payload
"""
    mutated = _mutate_subject(
        exact_snapshot,
        path,
        lambda data: (
            data.replace(
                refusal,
                b"    read_local_signer_vault(args.vault)\n" + refusal,
                1,
            )
            + decoy
        ),
    )

    assert _reject_code(mutated) == "LOCAL_SIGNER_RETIREMENT_GUARD"


def test_api_attachment_guard_rejects_autotrader_flag_omission(
    exact_snapshot: SubjectSnapshotV3,
) -> None:
    path = "src/integration/api_server.py"
    needle = b"            config.autotrader_live_enabled,\n"
    mutated = _mutate_subject(
        exact_snapshot,
        path,
        lambda data: data.replace(needle, b"", 1),
    )

    assert _reject_code(mutated) == "API_AUTOTRADER_ATTACHMENT_GUARD"


def test_api_attachment_guard_rejects_dead_exact_condition(
    exact_snapshot: SubjectSnapshotV3,
) -> None:
    path = "src/integration/api_server.py"

    def disable_guard(data: bytes) -> bytes:
        opened = data.replace(
            b"    if type(config) is not ApiServerConfig or any(\n",
            b"    if False and (type(config) is not ApiServerConfig or any(\n",
            1,
        )
        return opened.replace(
            b'    ):\n        refuse_current_local_operator_operation_v1("api_server_state_attachment")\n',
            b'    )):\n        refuse_current_local_operator_operation_v1("api_server_state_attachment")\n',
            1,
        )

    mutated = _mutate_subject(exact_snapshot, path, disable_guard)

    assert _reject_code(mutated) == "API_AUTOTRADER_ATTACHMENT_GUARD"


def test_api_startup_guard_rejects_dead_condition_with_marker_decoy(
    exact_snapshot: SubjectSnapshotV3,
) -> None:
    path = "src/integration/api_server.py"
    needle = b"    if config.autotrader_live_enabled:\n"
    replacement = b"    if config.autotrader_live_enabled and False:\n"
    mutated = _mutate_subject(
        exact_snapshot,
        path,
        lambda data: (
            data.replace(needle, replacement, 1) + b"\n# if config.autotrader_live_enabled:\n"
        ),
    )

    assert _reject_code(mutated) == "API_AUTOTRADER_STARTUP_REFUSAL"


def test_artifact_rejects_research_oracle_current_operation_contamination(
    exact_snapshot: SubjectSnapshotV3,
) -> None:
    artifact = json.loads(build_artifact_v3(exact_snapshot))
    row = next(
        row
        for row in artifact["dependency_projection"]["dependency_rows"]
        if row["classification"] == "RESEARCH_ORACLE"
    )
    row["current_operation_ids"] = [CURRENT_OPERATION_IDS_V3[0]]
    raw = _artifact_with_root(artifact)

    with pytest.raises(ClosureRejectV3) as exc_info:
        check_artifact_v3(raw, exact_snapshot)
    assert exc_info.value.code == ("RESEARCH_ORACLE_REACHABLE_FROM_CURRENT_OPERATION")


def test_artifact_rejects_missing_quarantine_witness(
    exact_snapshot: SubjectSnapshotV3,
) -> None:
    artifact = json.loads(build_artifact_v3(exact_snapshot))
    row = next(
        row
        for row in artifact["dependency_projection"]["dependency_rows"]
        if row["classification"] == "QUARANTINED"
    )
    row["quarantine_evidence_ids"] = []
    raw = _artifact_with_root(artifact)

    with pytest.raises(ClosureRejectV3) as exc_info:
        check_artifact_v3(raw, exact_snapshot)
    assert exc_info.value.code == "QUARANTINE_WITNESS_MISSING"


def test_artifact_rejects_duplicate_dependency_before_byte_replay(
    exact_snapshot: SubjectSnapshotV3,
) -> None:
    artifact = json.loads(build_artifact_v3(exact_snapshot))
    rows = artifact["dependency_projection"]["dependency_rows"]
    rows.append(dict(rows[0]))
    artifact["dependency_projection"]["dependency_count"] += 1
    classification = rows[0]["classification"]
    artifact["dependency_projection"]["classification_counts"][classification] += 1
    artifact["operation_registry"]["operation_rows"] = _operation_registry(rows)
    raw = _artifact_with_root(artifact)

    with pytest.raises(ClosureRejectV3) as exc_info:
        check_artifact_v3(raw, exact_snapshot)
    assert exc_info.value.code == "DUPLICATE_DEPENDENCY"


@pytest.mark.parametrize(
    ("field", "value", "code"),
    (
        ("closed_value_movement_gates", 1, "VM_GATE_PROMOTION"),
        ("production_authority", "GRANTED", "AUTHORITY_PROMOTION"),
        ("release_authority", "GRANTED", "AUTHORITY_PROMOTION"),
        ("settlement_authority", "GRANTED", "AUTHORITY_PROMOTION"),
        ("value_movement_authority", "GRANTED", "AUTHORITY_PROMOTION"),
    ),
)
def test_artifact_rejects_any_authority_promotion(
    exact_snapshot: SubjectSnapshotV3,
    field: str,
    value: object,
    code: str,
) -> None:
    artifact = json.loads(build_artifact_v3(exact_snapshot))
    artifact["claim_ceiling"][field] = value
    raw = _artifact_with_root(artifact)

    with pytest.raises(ClosureRejectV3) as exc_info:
        check_artifact_v3(raw, exact_snapshot)
    assert exc_info.value.code == code


def test_artifact_rejects_operation_registry_mutation(
    exact_snapshot: SubjectSnapshotV3,
) -> None:
    artifact = json.loads(build_artifact_v3(exact_snapshot))
    artifact["operation_registry"]["current_operation_ids"].append("FOREIGN")
    raw = _artifact_with_root(artifact)

    with pytest.raises(ClosureRejectV3) as exc_info:
        check_artifact_v3(raw, exact_snapshot)
    assert exc_info.value.code == "OPERATION_REGISTRY_DRIFT"


def test_artifact_rejects_negative_dependency_occurrence_count(
    exact_snapshot: SubjectSnapshotV3,
) -> None:
    artifact = json.loads(build_artifact_v3(exact_snapshot))
    artifact["dependency_projection"]["dependency_rows"][0]["baseline_occurrences"] = -1
    raw = _artifact_with_root(artifact)

    with pytest.raises(ClosureRejectV3) as exc_info:
        check_artifact_v3(raw, exact_snapshot)

    assert exc_info.value.code == "OCCURRENCE_COUNT"


def test_artifact_rejects_semantically_valid_row_deletion_by_replay(
    exact_snapshot: SubjectSnapshotV3,
) -> None:
    artifact = json.loads(build_artifact_v3(exact_snapshot))
    rows = artifact["dependency_projection"]["dependency_rows"]
    index = next(
        index
        for index, row in enumerate(rows)
        if row["classification"] == "RESEARCH_ORACLE"
        and sum(
            candidate["research_operation_ids"] == row["research_operation_ids"]
            for candidate in rows
        )
        > 1
    )
    removed = rows.pop(index)
    artifact["dependency_projection"]["dependency_count"] -= 1
    artifact["dependency_projection"]["classification_counts"][removed["classification"]] -= 1
    artifact["operation_registry"]["operation_rows"] = _operation_registry(rows)
    raw = _artifact_with_root(artifact)

    with pytest.raises(ClosureRejectV3) as exc_info:
        check_artifact_v3(raw, exact_snapshot)
    assert exc_info.value.code == "ARTIFACT_REPLAY_MISMATCH"


def test_stage_b_topology_accepts_exact_single_artifact_commit(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    artifact_path = Path("docs/research/o003b.json")
    raw = b'{"bounded":"stage-b"}\n'
    evidence_commit, evidence_tree = _stage_a_repo(tmp_path)
    stage_b_commit = _commit_stage_b(tmp_path, artifact_path, raw)
    monkeypatch.setattr(closure_checker, "OUTPUT_PATH", artifact_path)

    observed_head, observed_tree = closure_checker._require_stage_b_topology(
        tmp_path,
        raw=raw,
        evidence_commit=evidence_commit,
        evidence_tree=evidence_tree,
    )

    assert observed_head == stage_b_commit
    assert observed_tree == (
        _temp_git_output(tmp_path, "rev-parse", "HEAD^{tree}").decode("ascii").strip()
    )


def test_stage_b_topology_rejects_merge_artifact_commit(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    artifact_path = Path("docs/research/o003b.json")
    raw = b'{"bounded":"stage-b"}\n'
    evidence_commit, evidence_tree = _stage_a_repo(tmp_path)
    _temp_git(tmp_path, "checkout", "--quiet", "-b", "o003b-side")
    (tmp_path / "side.txt").write_text("side\n", encoding="utf-8")
    _temp_git(tmp_path, "add", "side.txt")
    _temp_git(tmp_path, "commit", "--quiet", "-m", "side parent")
    side_commit = _temp_git_output(tmp_path, "rev-parse", "HEAD").decode("ascii").strip()
    _temp_git(
        tmp_path,
        "checkout",
        "--quiet",
        "-b",
        "o003b-artifact-merge",
        evidence_commit,
    )
    _temp_git(tmp_path, "merge", "--quiet", "--no-ff", "--no-commit", side_commit)
    output = tmp_path / artifact_path
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_bytes(raw)
    _temp_git(tmp_path, "add", artifact_path.as_posix())
    _temp_git(tmp_path, "commit", "--quiet", "-m", "merge artifact Stage B")
    monkeypatch.setattr(closure_checker, "OUTPUT_PATH", artifact_path)

    with pytest.raises(ClosureRejectV3) as exc_info:
        closure_checker._require_stage_b_topology(
            tmp_path,
            raw=raw,
            evidence_commit=evidence_commit,
            evidence_tree=evidence_tree,
        )

    assert exc_info.value.code == "STAGE_B_PARENT_CARDINALITY"


def test_stage_b_topology_rejects_executable_artifact_mode(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    artifact_path = Path("docs/research/o003b.json")
    raw = b'{"bounded":"stage-b"}\n'
    evidence_commit, evidence_tree = _stage_a_repo(tmp_path)
    output = tmp_path / artifact_path
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_bytes(raw)
    output.chmod(0o755)
    _temp_git(tmp_path, "add", artifact_path.as_posix())
    _temp_git(tmp_path, "commit", "--quiet", "-m", "executable artifact Stage B")
    monkeypatch.setattr(closure_checker, "OUTPUT_PATH", artifact_path)

    with pytest.raises(ClosureRejectV3) as exc_info:
        closure_checker._require_stage_b_topology(
            tmp_path,
            raw=raw,
            evidence_commit=evidence_commit,
            evidence_tree=evidence_tree,
        )

    assert exc_info.value.code == "STAGE_B_ARTIFACT_ENTRY"


def test_stage_b_topology_rejects_substituted_evidence_tree(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    artifact_path = Path("docs/research/o003b.json")
    raw = b'{"bounded":"stage-b"}\n'
    evidence_commit, _ = _stage_a_repo(tmp_path)
    _commit_stage_b(tmp_path, artifact_path, raw)
    monkeypatch.setattr(closure_checker, "OUTPUT_PATH", artifact_path)

    with pytest.raises(ClosureRejectV3) as exc_info:
        closure_checker._require_stage_b_topology(
            tmp_path,
            raw=raw,
            evidence_commit=evidence_commit,
            evidence_tree="f" * 40,
        )

    assert exc_info.value.code == "EVIDENCE_TREE"


def test_stage_b_topology_rejects_extra_tree_delta(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    artifact_path = Path("docs/research/o003b.json")
    raw = b'{"bounded":"stage-b"}\n'
    evidence_commit, evidence_tree = _stage_a_repo(tmp_path)
    _commit_stage_b(tmp_path, artifact_path, raw, "unexpected.txt")
    monkeypatch.setattr(closure_checker, "OUTPUT_PATH", artifact_path)

    with pytest.raises(ClosureRejectV3) as exc_info:
        closure_checker._require_stage_b_topology(
            tmp_path,
            raw=raw,
            evidence_commit=evidence_commit,
            evidence_tree=evidence_tree,
        )

    assert exc_info.value.code == "STAGE_B_TREE_DELTA"


def test_stage_b_topology_rejects_nonadjacent_stage_a_parent(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    artifact_path = Path("docs/research/o003b.json")
    raw = b'{"bounded":"stage-b"}\n'
    evidence_commit, evidence_tree = _stage_a_repo(tmp_path)
    (tmp_path / "intervening.txt").write_text("intervening\n", encoding="utf-8")
    _temp_git(tmp_path, "add", "intervening.txt")
    _temp_git(tmp_path, "commit", "--quiet", "-m", "intervening")
    _commit_stage_b(tmp_path, artifact_path, raw)
    monkeypatch.setattr(closure_checker, "OUTPUT_PATH", artifact_path)

    with pytest.raises(ClosureRejectV3) as exc_info:
        closure_checker._require_stage_b_topology(
            tmp_path,
            raw=raw,
            evidence_commit=evidence_commit,
            evidence_tree=evidence_tree,
        )

    assert exc_info.value.code == "STAGE_B_PARENT_MISMATCH"


def test_stage_b_topology_rejects_uncommitted_artifact_bytes(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    artifact_path = Path("docs/research/o003b.json")
    committed_raw = b'{"bounded":"stage-b"}\n'
    observed_raw = b'{"bounded":"working-tree-mutation"}\n'
    evidence_commit, evidence_tree = _stage_a_repo(tmp_path)
    _commit_stage_b(tmp_path, artifact_path, committed_raw)
    monkeypatch.setattr(closure_checker, "OUTPUT_PATH", artifact_path)

    with pytest.raises(ClosureRejectV3) as exc_info:
        closure_checker._require_stage_b_topology(
            tmp_path,
            raw=observed_raw,
            evidence_commit=evidence_commit,
            evidence_tree=evidence_tree,
        )

    assert exc_info.value.code == "STAGE_B_ARTIFACT_BLOB"


def test_stage_a_loader_accepts_unrelated_descendant_with_pins_unchanged(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _, evidence_commit = _loader_subject_repo(tmp_path, monkeypatch)
    (tmp_path / "later-obligation.txt").write_text("later\n", encoding="utf-8")
    _temp_git(tmp_path, "add", "later-obligation.txt")
    _temp_git(tmp_path, "commit", "--quiet", "-m", "later obligation")

    snapshot = closure_builder.load_subject_snapshot_v3(
        tmp_path,
        evidence_commit=evidence_commit,
    )

    assert snapshot.subject.commit == evidence_commit
    assert snapshot.subject_is_current_ancestor is True
    assert snapshot.captured_head != evidence_commit


@pytest.mark.parametrize(
    "source",
    (
        b"from src.integration.tau_net_client import TauNetTcpClient\n",
        "import src.integration.tau_net_ｃlient as injected\n".encode("utf-8"),
        b"# coding: unicode_escape\nimport src.integration.tau_net_\\x63lient as injected\n",
    ),
    ids=("plain", "nfkc-identifier", "encoding-cookie-escape"),
)
def test_stage_a_loader_propagates_real_out_of_seed_bridge_import(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    source: bytes,
) -> None:
    _loader_subject_repo(tmp_path, monkeypatch)
    relative_path = "src/o003b_out_of_seed_mutant.py"
    source_path = tmp_path / relative_path
    source_path.parent.mkdir(parents=True, exist_ok=True)
    source_path.write_bytes(source)
    _temp_git(tmp_path, "add", relative_path)
    _temp_git(tmp_path, "commit", "--quiet", "-m", "out-of-seed bridge import")
    mutant_commit = _temp_git_output(tmp_path, "rev-parse", "HEAD").decode("ascii").strip()

    snapshot = closure_builder.load_subject_snapshot_v3(
        tmp_path,
        evidence_commit=mutant_commit,
    )
    monkeypatch.setattr(closure_core, "BASELINE_DISCOVERY_PATH_COUNT_V3", 1)
    monkeypatch.setattr(
        closure_core,
        "BASELINE_DISCOVERY_PATH_SET_SHA256_V3",
        _path_set_sha256(("pinned.py",)),
    )
    monkeypatch.setattr(closure_core, "DIRECT_CONSUMER_PATHS_V3", ())
    baseline, subject, current = closure_core._snapshot_discoveries(snapshot)

    with pytest.raises(ClosureRejectV3) as exc_info:
        closure_core._require_discovery_closure(
            baseline_direct=(),
            subject_direct=(),
            baseline_discovery=baseline,
            subject_discovery=subject,
            current_discovery=current,
        )

    assert exc_info.value.code == "UNCLASSIFIED_RETIRED_TAU_BRIDGE_IMPORT"
    assert exc_info.value.path == relative_path


def test_stage_a_loader_rejects_pinned_descendant_change(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _, evidence_commit = _loader_subject_repo(tmp_path, monkeypatch)
    (tmp_path / "pinned.py").write_text("DESCENDANT = True\n", encoding="utf-8")
    _temp_git(tmp_path, "add", "pinned.py")
    _temp_git(tmp_path, "commit", "--quiet", "-m", "mutate pinned source")

    with pytest.raises(ClosureRejectV3) as exc_info:
        closure_builder.load_subject_snapshot_v3(
            tmp_path,
            evidence_commit=evidence_commit,
        )

    assert exc_info.value.code == "STAGE_A_SOURCE_DRIFT"


def test_stage_a_loader_rejects_uncommitted_pinned_change(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _, evidence_commit = _loader_subject_repo(tmp_path, monkeypatch)
    (tmp_path / "pinned.py").write_text("DIRTY = True\n", encoding="utf-8")

    with pytest.raises(ClosureRejectV3) as exc_info:
        closure_builder.load_subject_snapshot_v3(
            tmp_path,
            evidence_commit=evidence_commit,
        )

    assert exc_info.value.code == "WORKTREE_SOURCE_DRIFT"


def _empty_snapshot_for_head(head: str) -> SubjectSnapshotV3:
    empty = SourceSnapshotV3(commit="a" * 40, tree="b" * 40, files=())
    return SubjectSnapshotV3(
        captured_head=head,
        rechecked_head=head,
        baseline=empty,
        subject=empty,
        baseline_is_subject_ancestor=True,
        subject_is_current_ancestor=True,
    )


def test_public_checker_rejects_head_change_between_topology_and_source_capture(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    observed_head = "1" * 40
    monkeypatch.setattr(
        closure_checker,
        "_require_inert_path_v1",
        lambda root, _label: Path(root),
    )
    monkeypatch.setattr(
        closure_checker,
        "_read_bounded_regular_file_v1",
        lambda *_args: b"{}\n",
    )
    monkeypatch.setattr(
        closure_checker,
        "_artifact_subject",
        lambda _raw: ("a" * 40, "b" * 40),
    )
    monkeypatch.setattr(
        closure_checker,
        "_require_stage_b_topology",
        lambda *_args, **_kwargs: (observed_head, "2" * 40),
    )
    monkeypatch.setattr(
        closure_checker,
        "load_subject_snapshot_v3",
        lambda *_args, **_kwargs: _empty_snapshot_for_head("3" * 40),
    )
    monkeypatch.setattr(
        closure_checker,
        "check_artifact_v3",
        lambda *_args: pytest.fail("mixed-head snapshot reached artifact acceptance"),
    )

    report = closure_checker.check_retired_tau_bridge_closure_v3(tmp_path)

    assert report["ok"] is False
    assert report["findings"] == [
        {
            "code": "HEAD_CHANGED",
            "detail": "HEAD changed between Stage-B topology and source capture",
            "path": observed_head,
        }
    ]
    assert report["production_authority"] == "NONE"
    assert report["value_movement_authority"] == "NONE"


def test_public_checker_rejects_terminal_head_change(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    observed_head = "1" * 40
    monkeypatch.setattr(
        closure_checker,
        "_require_inert_path_v1",
        lambda root, _label: Path(root),
    )
    monkeypatch.setattr(
        closure_checker,
        "_read_bounded_regular_file_v1",
        lambda *_args: b"{}\n",
    )
    monkeypatch.setattr(
        closure_checker,
        "_artifact_subject",
        lambda _raw: ("a" * 40, "b" * 40),
    )
    monkeypatch.setattr(
        closure_checker,
        "_require_stage_b_topology",
        lambda *_args, **_kwargs: (observed_head, "2" * 40),
    )
    monkeypatch.setattr(
        closure_checker,
        "load_subject_snapshot_v3",
        lambda *_args, **_kwargs: _empty_snapshot_for_head(observed_head),
    )
    monkeypatch.setattr(
        closure_checker,
        "check_artifact_v3",
        lambda *_args: {"ok": True},
    )
    monkeypatch.setattr(closure_checker, "_git_head_v1", lambda _root: "4" * 40)

    report = closure_checker.check_retired_tau_bridge_closure_v3(tmp_path)

    assert report["ok"] is False
    assert report["findings"] == [
        {
            "code": "HEAD_CHANGED",
            "detail": "HEAD changed before terminal checker acceptance",
            "path": observed_head,
        }
    ]


def test_public_checker_rejects_terminal_artifact_replacement(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    observed_head = "1" * 40
    artifact_path = tmp_path / closure_checker.OUTPUT_PATH
    artifact_path.parent.mkdir(parents=True)
    artifact_path.write_bytes(b"{}\n")
    monkeypatch.setattr(
        closure_checker,
        "_artifact_subject",
        lambda _raw: ("a" * 40, "b" * 40),
    )
    monkeypatch.setattr(
        closure_checker,
        "_require_stage_b_topology",
        lambda *_args, **_kwargs: (observed_head, "2" * 40),
    )
    snapshot = _empty_snapshot_for_head(observed_head)
    monkeypatch.setattr(
        closure_checker,
        "load_subject_snapshot_v3",
        lambda *_args, **_kwargs: snapshot,
    )

    def accept_then_replace(*_args: object) -> dict[str, object]:
        replacement = artifact_path.with_suffix(".replacement")
        replacement.write_bytes(b'{"mutated_after_capture":true}\n')
        replacement.replace(artifact_path)
        return {"ok": True}

    monkeypatch.setattr(closure_checker, "check_artifact_v3", accept_then_replace)
    monkeypatch.setattr(closure_checker, "_git_head_v1", lambda _root: observed_head)

    report = closure_checker.check_retired_tau_bridge_closure_v3(tmp_path)

    assert report["ok"] is False
    assert report["findings"] == [
        {
            "code": "STAGE_B_ARTIFACT_CHANGED",
            "detail": "artifact bytes changed before terminal acceptance",
            "path": closure_checker.OUTPUT_PATH.as_posix(),
        }
    ]


@pytest.mark.parametrize(
    ("terminal_snapshot", "code"),
    (
        (
            replace(
                _empty_snapshot_for_head("1" * 40),
                subject=SourceSnapshotV3(
                    commit="a" * 40,
                    tree="b" * 40,
                    files=(_source("route.txt", b"changed\n"),),
                ),
            ),
            "WORKTREE_SOURCE_CHANGED",
        ),
        (
            replace(
                _empty_snapshot_for_head("1" * 40),
                current_discovery=PythonImportDiscoveryV3(
                    paths=("late_importer.py",),
                    edges=(),
                    source_root_sha256="0" * 64,
                ),
            ),
            "CURRENT_DISCOVERY_CHANGED",
        ),
    ),
    ids=("pinned-source", "python-discovery"),
)
def test_public_checker_rejects_terminal_live_input_change(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    terminal_snapshot: SubjectSnapshotV3,
    code: str,
) -> None:
    observed_head = "1" * 40
    initial_snapshot = _empty_snapshot_for_head(observed_head)
    snapshots = iter((initial_snapshot, terminal_snapshot))
    monkeypatch.setattr(
        closure_checker,
        "_require_inert_path_v1",
        lambda root, _label: Path(root),
    )
    monkeypatch.setattr(
        closure_checker,
        "_read_bounded_regular_file_v1",
        lambda *_args: b"{}\n",
    )
    monkeypatch.setattr(
        closure_checker,
        "_artifact_subject",
        lambda _raw: ("a" * 40, "b" * 40),
    )
    monkeypatch.setattr(
        closure_checker,
        "_require_stage_b_topology",
        lambda *_args, **_kwargs: (observed_head, "2" * 40),
    )
    monkeypatch.setattr(
        closure_checker,
        "load_subject_snapshot_v3",
        lambda *_args, **_kwargs: next(snapshots),
    )
    monkeypatch.setattr(
        closure_checker,
        "check_artifact_v3",
        lambda *_args: {"ok": True},
    )
    monkeypatch.setattr(closure_checker, "_git_head_v1", lambda _root: observed_head)

    report = closure_checker.check_retired_tau_bridge_closure_v3(tmp_path)

    assert report["ok"] is False
    findings = cast(list[dict[str, object]], report["findings"])
    assert findings[0]["code"] == code


def test_builder_check_rejects_terminal_artifact_replacement(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    artifact_path = tmp_path / closure_builder.OUTPUT_PATH
    artifact_path.parent.mkdir(parents=True)
    artifact_path.write_bytes(canonical_json_bytes_v3({"evidence_subject": {"commit": "a" * 40}}))
    snapshot = _empty_snapshot_for_head("1" * 40)
    snapshot = replace(
        snapshot,
        subject=replace(snapshot.subject, commit="a" * 40),
    )
    monkeypatch.setattr(
        closure_builder,
        "load_subject_snapshot_v3",
        lambda *_args, **_kwargs: snapshot,
    )

    def accept_then_replace(*_args: object) -> dict[str, object]:
        replacement = artifact_path.with_suffix(".replacement")
        replacement.write_bytes(b'{"mutated_after_capture":true}\n')
        replacement.replace(artifact_path)
        return {"ok": True}

    monkeypatch.setattr(closure_builder, "check_artifact_v3", accept_then_replace)
    monkeypatch.setattr(closure_builder, "_git_head_v1", lambda _root: "1" * 40)

    assert closure_builder.main(["--root", str(tmp_path), "--check"]) == 2
    report = json.loads(capsys.readouterr().out)
    assert report["finding"]["code"] == "STAGE_B_ARTIFACT_CHANGED"
    _assert_builder_failure_authority_none(report)


@pytest.mark.parametrize(
    ("terminal_snapshot", "code"),
    (
        (
            replace(
                _empty_snapshot_for_head("1" * 40),
                subject=SourceSnapshotV3(
                    commit="a" * 40,
                    tree="b" * 40,
                    files=(_source("route.txt", b"changed\n"),),
                ),
            ),
            "WORKTREE_SOURCE_CHANGED",
        ),
        (
            replace(
                _empty_snapshot_for_head("1" * 40),
                subject=replace(
                    _empty_snapshot_for_head("1" * 40).subject,
                    commit="a" * 40,
                ),
                current_discovery=PythonImportDiscoveryV3(
                    paths=("late_importer.py",),
                    edges=(),
                    source_root_sha256="0" * 64,
                ),
            ),
            "CURRENT_DISCOVERY_CHANGED",
        ),
    ),
    ids=("pinned-source", "python-discovery"),
)
def test_builder_check_rejects_terminal_live_input_change(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
    terminal_snapshot: SubjectSnapshotV3,
    code: str,
) -> None:
    artifact_path = tmp_path / closure_builder.OUTPUT_PATH
    artifact_path.parent.mkdir(parents=True)
    artifact_path.write_bytes(canonical_json_bytes_v3({"evidence_subject": {"commit": "a" * 40}}))
    initial_snapshot = _empty_snapshot_for_head("1" * 40)
    initial_snapshot = replace(
        initial_snapshot,
        subject=replace(initial_snapshot.subject, commit="a" * 40),
    )
    snapshots = iter((initial_snapshot, terminal_snapshot))
    monkeypatch.setattr(
        closure_builder,
        "load_subject_snapshot_v3",
        lambda *_args, **_kwargs: next(snapshots),
    )
    monkeypatch.setattr(
        closure_builder,
        "check_artifact_v3",
        lambda *_args: {"ok": True},
    )
    monkeypatch.setattr(closure_builder, "_git_head_v1", lambda _root: "1" * 40)

    assert closure_builder.main(["--root", str(tmp_path), "--check"]) == 2
    report = json.loads(capsys.readouterr().out)
    assert report["finding"]["code"] == code
    _assert_builder_failure_authority_none(report)


@pytest.mark.parametrize(
    ("case", "code"),
    (("root", "ROOT_CHANGED"), ("head", "HEAD_CHANGED")),
)
def test_builder_check_rejects_terminal_repository_change(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
    case: str,
    code: str,
) -> None:
    artifact_path = tmp_path / closure_builder.OUTPUT_PATH
    artifact_path.parent.mkdir(parents=True)
    artifact_path.write_bytes(canonical_json_bytes_v3({"evidence_subject": {"commit": "a" * 40}}))
    snapshot = _empty_snapshot_for_head("1" * 40)
    snapshot = replace(
        snapshot,
        subject=replace(snapshot.subject, commit="a" * 40),
    )
    monkeypatch.setattr(
        closure_builder,
        "load_subject_snapshot_v3",
        lambda *_args, **_kwargs: snapshot,
    )
    monkeypatch.setattr(
        closure_builder,
        "check_artifact_v3",
        lambda *_args: {"ok": True},
    )
    if case == "root":
        roots = iter(((1, 2), (3, 4)))
        monkeypatch.setattr(
            closure_builder,
            "_repository_root_identity_v3",
            lambda _root: next(roots),
        )
        monkeypatch.setattr(
            closure_builder,
            "_git_head_v1",
            lambda _root: "1" * 40,
        )
    else:
        heads = iter(("2" * 40,))
        monkeypatch.setattr(
            closure_builder,
            "_git_head_v1",
            lambda _root: next(heads),
        )

    assert closure_builder.main(["--root", str(tmp_path), "--check"]) == 2
    report = json.loads(capsys.readouterr().out)
    assert report["finding"]["code"] == code
    _assert_builder_failure_authority_none(report)


def test_public_checker_rejects_terminal_root_identity_change(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    observed_head = "1" * 40
    roots = iter(((1, 2), (3, 4)))
    monkeypatch.setattr(
        closure_checker,
        "_repository_root_identity_v3",
        lambda _root: next(roots),
    )
    monkeypatch.setattr(
        closure_checker,
        "_require_inert_path_v1",
        lambda root, _label: Path(root),
    )
    monkeypatch.setattr(
        closure_checker,
        "_read_bounded_regular_file_v1",
        lambda *_args: b"{}\n",
    )
    monkeypatch.setattr(
        closure_checker,
        "_artifact_subject",
        lambda _raw: ("a" * 40, "b" * 40),
    )
    monkeypatch.setattr(
        closure_checker,
        "_require_stage_b_topology",
        lambda *_args, **_kwargs: (observed_head, "2" * 40),
    )
    snapshot = _empty_snapshot_for_head(observed_head)
    monkeypatch.setattr(
        closure_checker,
        "load_subject_snapshot_v3",
        lambda *_args, **_kwargs: snapshot,
    )
    monkeypatch.setattr(
        closure_checker,
        "check_artifact_v3",
        lambda *_args: {"ok": True},
    )

    report = closure_checker.check_retired_tau_bridge_closure_v3(tmp_path)

    assert report["ok"] is False
    findings = cast(list[dict[str, object]], report["findings"])
    assert findings[0]["code"] == "ROOT_CHANGED"


def test_public_checker_accepts_quiescent_real_stage_pair() -> None:
    artifact_path = ROOT / closure_checker.OUTPUT_PATH
    if not artifact_path.is_file():
        pytest.skip("requires the committed Stage-B O-003B certificate")

    report = closure_checker.check_retired_tau_bridge_closure_v3(ROOT)

    assert report["ok"] is True
    assert report["observed_head"] == _git_output("rev-parse", "HEAD").decode("ascii").strip()
    assert (
        report["observed_tree"] == _git_output("rev-parse", "HEAD^{tree}").decode("ascii").strip()
    )


@pytest.mark.parametrize(
    ("case", "code"),
    (
        ("artifact", "STAGE_B_ARTIFACT_CHANGED"),
        ("pinned-source", "WORKTREE_SOURCE_DRIFT"),
        ("tracked-discovery", "CURRENT_DISCOVERY_CHANGED"),
        ("tracked-byte-only", "CURRENT_DISCOVERY_CHANGED"),
        ("late-untracked", "CURRENT_DISCOVERY_CHANGED"),
    ),
)
def test_public_checker_rejects_real_post_semantic_worktree_mutation(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    case: str,
    code: str,
) -> None:
    artifact_path = ROOT / closure_checker.OUTPUT_PATH
    if not artifact_path.is_file():
        pytest.skip("requires the committed Stage-B O-003B certificate")
    clone = tmp_path / "raced-repo"
    subprocess.run(  # noqa: S603 - fixed test-only Git command
        ("git", "clone", "--quiet", "--shared", str(ROOT), str(clone)),  # noqa: S607
        check=True,
    )
    expected_head = _temp_git_output(clone, "rev-parse", "HEAD").decode("ascii").strip()
    original_check = closure_checker.check_artifact_v3
    events: list[str] = []

    def accept_then_mutate(raw: bytes, snapshot: SubjectSnapshotV3) -> dict[str, object]:
        report = original_check(raw, snapshot)
        assert report["ok"] is True
        events.append("semantic_acceptance")
        if case == "artifact":
            target = clone / closure_checker.OUTPUT_PATH
            replacement = target.with_suffix(".replacement")
            replacement.write_bytes(b'{"mutated_after_capture":true}\n')
            replacement.replace(target)
        elif case == "pinned-source":
            target = clone / "src/integration/api_server.py"
            target.write_bytes(
                target.read_bytes() + b"\nfrom src.integration import tau_testnet_dex_plugin\n"
            )
        elif case == "tracked-discovery":
            target = clone / "src/core/__init__.py"
            target.write_bytes(
                target.read_bytes() + b"\nfrom src.integration import tau_testnet_dex_plugin\n"
            )
        elif case == "tracked-byte-only":
            target = clone / "src/core/__init__.py"
            target.write_bytes(target.read_bytes() + b"\n# late byte drift\n")
        else:
            target = clone / "src/o003b_late_untracked_bridge.py"
            target.write_bytes(b"from src.integration.tau_net_client import TauNetTcpClient\n")
        events.append("worktree_mutation")
        return report

    monkeypatch.setattr(closure_checker, "check_artifact_v3", accept_then_mutate)

    report = closure_checker.check_retired_tau_bridge_closure_v3(clone)

    assert report["ok"] is False
    findings = cast(list[dict[str, object]], report["findings"])
    assert findings[0]["code"] == code
    assert events == ["semantic_acceptance", "worktree_mutation"]
    assert _temp_git_output(clone, "rev-parse", "HEAD").decode("ascii").strip() == expected_head


def test_public_checker_propagates_new_bridge_import_from_real_stage_pair(
    tmp_path: Path,
) -> None:
    artifact_path = ROOT / closure_checker.OUTPUT_PATH
    if not artifact_path.is_file():
        pytest.skip("requires the committed Stage-B O-003B certificate")
    original_raw = artifact_path.read_bytes()
    artifact = json.loads(original_raw)
    evidence_commit = artifact["evidence_subject"]["commit"]
    clone = tmp_path / "mutant-repo"
    subprocess.run(  # noqa: S603 - fixed test-only Git command
        ("git", "clone", "--quiet", "--shared", "--no-checkout", str(ROOT), str(clone)),  # noqa: S607
        check=True,
    )
    _temp_git(clone, "config", "user.email", "o003b-test@example.invalid")
    _temp_git(clone, "config", "user.name", "O003B Test")
    _temp_git(clone, "checkout", "--quiet", "--detach", evidence_commit)
    relative_source_path = "src/integration/o003b_out_of_seed_mutant.py"
    source_path = clone / relative_source_path
    source_path.write_bytes(b"from src.integration.tau_net_client import TauNetTcpClient\n")
    _temp_git(clone, "add", relative_source_path)
    _temp_git(clone, "commit", "--quiet", "-m", "mutant Stage A")
    mutant_commit = _temp_git_output(clone, "rev-parse", "HEAD").decode("ascii").strip()
    mutant_tree = _temp_git_output(clone, "rev-parse", "HEAD^{tree}").decode("ascii").strip()
    artifact["evidence_subject"] = {
        "commit": mutant_commit,
        "tree": mutant_tree,
    }
    mutant_raw = _artifact_with_root(artifact)
    mutant_artifact_path = clone / closure_checker.OUTPUT_PATH
    mutant_artifact_path.parent.mkdir(parents=True, exist_ok=True)
    mutant_artifact_path.write_bytes(mutant_raw)
    _temp_git(clone, "add", closure_checker.OUTPUT_PATH.as_posix())
    _temp_git(clone, "commit", "--quiet", "-m", "mutant Stage B")

    report = closure_checker.check_retired_tau_bridge_closure_v3(clone)

    assert report["ok"] is False
    findings = cast(list[dict[str, object]], report["findings"])
    assert findings[0]["code"] == ("UNCLASSIFIED_RETIRED_TAU_BRIDGE_IMPORT")
    assert report["production_authority"] == "NONE"
    assert report["release_authority"] == "NONE"
    assert report["settlement_authority"] == "NONE"
    assert report["value_movement_authority"] == "NONE"
    assert _temp_git_output(clone, "status", "--porcelain") == b""
    assert artifact_path.read_bytes() == original_raw
