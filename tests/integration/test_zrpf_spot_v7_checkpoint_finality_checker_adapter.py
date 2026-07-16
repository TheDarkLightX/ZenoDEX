"""CBC tests for the pinned checkpoint-finality Rust cross-checker."""

from __future__ import annotations

import ast
import copy
import functools
import hashlib
import os
import pickle
import shutil
import subprocess
import tempfile
from dataclasses import replace
from pathlib import Path
from typing import Any, Callable, Iterator

import pytest

import src.integration.zrpf_spot_v7_checkpoint_finality_checker_adapter as checker_adapter
import tests.integration.test_zrpf_spot_v7_operational_policy_v3 as policy_test
from src.integration._zrpf_spot_v7_operational_mechanics import (
    _encode_checkpoint_finality_certificate_v2,
    _finality_certificate_root_v2,
)
from src.integration._zrpf_spot_v7_operational_policy_v3 import (
    _GovernedSpotV7OperationalPolicyV3,
)
from src.integration.zrpf_spot_v7_checkpoint_finality_checker_adapter import (
    CHECKPOINT_FINALITY_CHECKER_AUTHORITY_SCHEMA_V1,
    CheckpointFinalityCheckerAdapterRejectedV1,
    CheckpointFinalityCheckerAdapterRejectV1,
    PinnedSpotV7CheckpointFinalityCheckerV1,
    _CrossCheckedAuthenticatedCheckpointFinalityTransitionV1,
)
from src.integration.zrpf_spot_v7_zeno_ledger_finality_adapter import (
    _AUTHENTICATED_CHECKPOINT_FINALITY_SEAL_V3,
    _AuthenticatedCheckpointFinalityProjectionV3,
    _AuthenticatedExactCheckpointFinalityTransitionV3,
)
from src.state.canonical import canonical_json_bytes

ROOT = Path(__file__).resolve().parents[2]
CHECKER_MANIFEST = ROOT / "zk/zrpf_checkpoint_finality_checker/Cargo.toml"
CHECKER_PACKAGE = "zenodex-zrpf-checkpoint-finality-checker-v1"


def _root(label: str) -> str:
    return "0x" + hashlib.sha256(label.encode("ascii")).hexdigest()


@pytest.fixture(scope="session")
def rust_checker(tmp_path_factory: pytest.TempPathFactory) -> Iterator[Path]:
    target = tmp_path_factory.mktemp("checkpoint-finality-rust-target")
    yield _build_rust_checker(target)


def _build_rust_checker(target: Path) -> Path:
    cargo = shutil.which("cargo")
    if cargo is None:
        raise FileNotFoundError("cargo is required for the checkpoint-finality fixture")
    cargo_path = Path(cargo)
    home = os.environ.get("HOME", str(Path.home()))
    environment = {
        "CARGO_HOME": os.environ.get("CARGO_HOME", f"{home}/.cargo"),
        "CARGO_NET_OFFLINE": "true",
        "CARGO_TARGET_DIR": str(target),
        "CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS": "-C target-feature=+crt-static",
        "HOME": home,
        "PATH": f"{cargo_path.parent}:/usr/bin:/bin",
        "RUSTUP_HOME": os.environ.get("RUSTUP_HOME", f"{home}/.rustup"),
        "TMPDIR": os.environ.get("TMPDIR", "/tmp"),
    }
    subprocess.run(
        (
            str(cargo_path),
            "build",
            "--locked",
            "--release",
            "--target",
            "x86_64-unknown-linux-gnu",
            "--manifest-path",
            str(CHECKER_MANIFEST),
            "-p",
            CHECKER_PACKAGE,
        ),
        cwd=ROOT,
        env=environment,
        check=True,
        capture_output=True,
    )
    executable = (
        target / "x86_64-unknown-linux-gnu" / "release" / "zrpf-checkpoint-finality-checker-v1"
    )
    assert executable.is_file()
    executable.chmod(0o555)
    return executable


def _governed_policy() -> _GovernedSpotV7OperationalPolicyV3:
    registry = policy_test._registry()
    raw = policy_test._manifest(registry)
    return policy_test._load(raw, registry)


def _authenticated_finality(policy: object) -> _AuthenticatedExactCheckpointFinalityTransitionV3:
    store_policy = policy._base_store_policy_for_finality_v3()  # type: ignore[attr-defined]
    epoch = policy_test.POLICY_ACTIVATION_EPOCH
    sequence = store_policy.genesis_application_checkpoint_sequence + 1
    parent_hash = store_policy.genesis_application_checkpoint_hash
    checkpoint_hash = _root("checkpoint-finality-checker-next")
    proof_journal_hash = _root("checkpoint-finality-checker-journal")
    post_state_root = _root("checkpoint-finality-checker-post-state")
    evidence = b'{"schema":"test-only-checkpoint-finality-evidence-v1"}'
    evidence_root = "0x" + hashlib.sha256(evidence).hexdigest()
    policy_root = store_policy.checkpoint_finality_policy_root
    certificate_root = _finality_certificate_root_v2(
        policy=store_policy,
        epoch_id=epoch,
        proof_journal_hash=proof_journal_hash,
        post_state_root=post_state_root,
        sequence=sequence,
        checkpoint_hash=checkpoint_hash,
        parent_hash=parent_hash,
        evidence_root=evidence_root,
        policy_root=policy_root,
    )
    certificate = _encode_checkpoint_finality_certificate_v2(
        policy=store_policy,
        epoch_id=epoch,
        proof_journal_hash=proof_journal_hash,
        post_state_root=post_state_root,
        sequence=sequence,
        checkpoint_hash=checkpoint_hash,
        parent_hash=parent_hash,
        evidence_root=evidence_root,
        policy_root=policy_root,
        certificate_root=certificate_root,
    )
    projection = _AuthenticatedCheckpointFinalityProjectionV3(
        application_id=store_policy.application_id,
        chain_or_domain_id=store_policy.chain_or_domain_id,
        epoch_id=epoch,
        proof_journal_hash=proof_journal_hash,
        post_state_root=post_state_root,
        policy_root=policy_root,
        certificate_root=certificate_root,
        finality_evidence_root=evidence_root,
        prior_application_checkpoint_sequence=sequence - 1,
        prior_application_checkpoint_hash=parent_hash,
        next_application_checkpoint_sequence=sequence,
        next_application_checkpoint_hash=checkpoint_hash,
    )
    return _AuthenticatedExactCheckpointFinalityTransitionV3(
        projection,
        exact_certificate_bytes=certificate,
        exact_finality_evidence_bytes=evidence,
        seal=_AUTHENTICATED_CHECKPOINT_FINALITY_SEAL_V3,
    )


def _manifest(executable: Path, **changes: object) -> bytes:
    document: dict[str, object] = {
        "schema": CHECKPOINT_FINALITY_CHECKER_AUTHORITY_SCHEMA_V1,
        "checker_protocol_version": 1,
        "request_schema": "zenodex.zrpf.checkpoint_finality_checker.request.v1",
        "response_schema": "zenodex.zrpf.checkpoint_finality_checker.response.v1",
        "executable_sha256": hashlib.sha256(executable.read_bytes()).hexdigest(),
        "executable_format": "static_elf_x86_64",
        "release_authority": False,
        "settlement_authority": False,
        "production_authority": False,
    }
    document.update(changes)
    return canonical_json_bytes(document)


def _checker(
    executable: Path,
    **manifest_changes: object,
) -> PinnedSpotV7CheckpointFinalityCheckerV1:
    manifest = _manifest(executable, **manifest_changes)
    return PinnedSpotV7CheckpointFinalityCheckerV1(
        executable=executable,
        authority_manifest_json=manifest,
        authority_manifest_sha256=hashlib.sha256(manifest).hexdigest(),
    )


@functools.cache
def _downstream_checker_fixture() -> tuple[
    tempfile.TemporaryDirectory[str],
    PinnedSpotV7CheckpointFinalityCheckerV1,
]:
    """Retain one auto-cleaned static checker fixture for this test process."""

    directory = tempfile.TemporaryDirectory(prefix="zrpf-checkpoint-finality-target-")
    checker = _checker(_build_rust_checker(Path(directory.name)))
    return directory, checker


def _checker_for_downstream_tests() -> PinnedSpotV7CheckpointFinalityCheckerV1:
    return _downstream_checker_fixture()[1]


def test_pinned_checker_cross_checks_exact_bls_transition_once(
    rust_checker: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    policy = _governed_policy()
    finality = _authenticated_finality(policy)
    calls = 0
    original = checker_adapter.execute_pinned_verifier_once

    def counted(**kwargs: Any) -> bytes:
        nonlocal calls
        calls += 1
        return original(**kwargs)

    monkeypatch.setattr(checker_adapter, "execute_pinned_verifier_once", counted)
    result = _checker(rust_checker).cross_check_authenticated(
        policy=policy,
        finality=finality,
    )

    assert calls == 1
    assert type(result) is _CrossCheckedAuthenticatedCheckpointFinalityTransitionV1
    assert result._finality_for_operational_join_v3(policy) is finality
    assert result.cryptographic_checkpoint_quorum_supported is True
    assert result.manifest_pinned_checker_cross_check_executed is True
    assert result.release_governed_checker_identity_verified is False
    assert result.hostile_same_interpreter_resistance_established is False
    assert result.release_authority is False
    assert result.settlement_authority is False
    assert result.production_authority is False


def test_plain_objects_reject_before_checker_execution(
    rust_checker: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    called = False

    def forbidden(**_kwargs: object) -> bytes:
        nonlocal called
        called = True
        raise AssertionError("checker process must not execute")

    monkeypatch.setattr(checker_adapter, "execute_pinned_verifier_once", forbidden)
    with pytest.raises(CheckpointFinalityCheckerAdapterRejectedV1) as rejected:
        _checker(rust_checker).cross_check_authenticated(
            policy={"governed": True},
            finality={"risc0_verified": True},
        )

    assert rejected.value.reason is (
        CheckpointFinalityCheckerAdapterRejectV1.AUTHENTICATED_INPUT_INVALID
    )
    assert called is False


def test_certificate_mutation_is_rejected_by_rust_checker(rust_checker: Path) -> None:
    policy = _governed_policy()
    valid = _authenticated_finality(policy)
    mutated = _AuthenticatedExactCheckpointFinalityTransitionV3(
        valid._projection,
        exact_certificate_bytes=(
            valid._exact_certificate_bytes[:-1] + bytes([valid._exact_certificate_bytes[-1] ^ 1])
        ),
        exact_finality_evidence_bytes=valid._exact_finality_evidence_bytes,
        seal=_AUTHENTICATED_CHECKPOINT_FINALITY_SEAL_V3,
    )

    with pytest.raises(CheckpointFinalityCheckerAdapterRejectedV1) as rejected:
        _checker(rust_checker).cross_check_authenticated(
            policy=policy,
            finality=mutated,
        )

    assert rejected.value.reason is CheckpointFinalityCheckerAdapterRejectV1.CHECKER_REJECTED


def test_invalid_checker_response_cannot_mint_cross_checked_result(
    rust_checker: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    policy = _governed_policy()
    finality = _authenticated_finality(policy)
    monkeypatch.setattr(
        checker_adapter,
        "execute_pinned_verifier_once",
        lambda **_kwargs: bytes(330),
    )

    with pytest.raises(CheckpointFinalityCheckerAdapterRejectedV1) as rejected:
        _checker(rust_checker).cross_check_authenticated(
            policy=policy,
            finality=finality,
        )

    assert rejected.value.reason is (
        CheckpointFinalityCheckerAdapterRejectV1.CHECKER_RESPONSE_INVALID
    )


@pytest.mark.parametrize(
    "changes",
    (
        {"release_authority": True},
        {"settlement_authority": 0},
        {"production_authority": True},
        {"checker_protocol_version": 2},
        {"executable_format": "test_script"},
        {"unknown": "field"},
    ),
)
def test_authority_manifest_rejects_claim_expansion_and_schema_drift(
    rust_checker: Path,
    changes: dict[str, object],
) -> None:
    with pytest.raises(CheckpointFinalityCheckerAdapterRejectedV1) as rejected:
        _checker(rust_checker, **changes)

    assert rejected.value.reason is (
        CheckpointFinalityCheckerAdapterRejectV1.AUTHORITY_MANIFEST_INVALID
    )


def test_cross_checked_result_is_nontransferable_and_policy_identity_bound(
    rust_checker: Path,
) -> None:
    policy = _governed_policy()
    result = _checker(rust_checker).cross_check_authenticated(
        policy=policy,
        finality=_authenticated_finality(policy),
    )

    with pytest.raises(TypeError):
        copy.copy(result)
    with pytest.raises(TypeError):
        copy.deepcopy(result)
    with pytest.raises(TypeError):
        pickle.dumps(result)
    with pytest.raises(TypeError):
        result._policy = policy
    with pytest.raises(ValueError, match="different governed policy"):
        result._finality_for_operational_join_v3(_governed_policy())


def test_cross_checked_result_rejects_retained_manifest_mutation(
    rust_checker: Path,
) -> None:
    policy = _governed_policy()
    result = _checker(rust_checker).cross_check_authenticated(
        policy=policy,
        finality=_authenticated_finality(policy),
    )
    object.__setattr__(
        result,
        "_exact_authority_manifest_bytes",
        result._exact_authority_manifest_bytes + b"\n",
    )

    with pytest.raises(ValueError, match="authority manifest digest drift"):
        result._finality_for_operational_join_v3(policy)


def test_manifest_digest_mismatch_rejects(rust_checker: Path) -> None:
    manifest = _manifest(rust_checker)
    with pytest.raises(CheckpointFinalityCheckerAdapterRejectedV1) as rejected:
        PinnedSpotV7CheckpointFinalityCheckerV1(
            executable=rust_checker,
            authority_manifest_json=manifest,
            authority_manifest_sha256="00" * 32,
        )

    assert rejected.value.reason is (
        CheckpointFinalityCheckerAdapterRejectV1.AUTHORITY_MANIFEST_INVALID
    )


@pytest.mark.parametrize(
    "mutate",
    (
        lambda raw: raw.replace(
            b'{"checker_protocol_version":1,',
            b'{"checker_protocol_version":1,"checker_protocol_version":1,',
            1,
        ),
        lambda raw: raw.replace(
            b'{"checker_protocol_version":1,',
            b'{"checker_protocol_version":1.0,',
            1,
        ),
        lambda raw: raw + b"\n",
    ),
    ids=("duplicate-key", "floating-number", "noncanonical-trailing-byte"),
)
def test_authority_manifest_rejects_ambiguous_or_noncanonical_json(
    rust_checker: Path,
    mutate: Callable[[bytes], bytes],
) -> None:
    valid = _manifest(rust_checker)
    raw = mutate(valid)

    with pytest.raises(CheckpointFinalityCheckerAdapterRejectedV1) as rejected:
        PinnedSpotV7CheckpointFinalityCheckerV1(
            executable=rust_checker,
            authority_manifest_json=raw,
            authority_manifest_sha256=hashlib.sha256(raw).hexdigest(),
        )

    assert rejected.value.reason is (
        CheckpointFinalityCheckerAdapterRejectV1.AUTHORITY_MANIFEST_INVALID
    )


def test_cross_checked_result_has_no_direct_constructor_or_module_seal() -> None:
    assert not hasattr(
        checker_adapter,
        "_CROSS_CHECKED_CHECKPOINT_FINALITY_SEAL_V1",
    )
    with pytest.raises(TypeError, match="requires exact checker execution"):
        _CrossCheckedAuthenticatedCheckpointFinalityTransitionV1()


def test_pinned_checker_exposes_no_zero_execution_capability_mint(
    rust_checker: Path,
) -> None:
    checker = _checker(rust_checker)

    assert not hasattr(checker, "_seal_cross_checked_result_after_execution")
    assert not hasattr(checker_adapter, "_seal_cross_checked_result_after_execution")


def test_cross_checked_capability_has_one_lexical_mint_after_native_execution() -> None:
    source_path = Path(checker_adapter.__file__).resolve()
    tree = ast.parse(source_path.read_text(encoding="utf-8"))
    minting_sites: list[tuple[str, int]] = []
    execution_sites: list[int] = []
    for node in ast.walk(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        for child in ast.walk(node):
            if (
                node.name == "cross_check_authenticated"
                and isinstance(child, ast.Call)
                and isinstance(child.func, ast.Attribute)
                and child.func.attr == "_execute_checker"
            ):
                execution_sites.append(child.lineno)
            if not isinstance(child, ast.Call) or len(child.args) != 1:
                continue
            callee = child.func
            target = child.args[0]
            if (
                isinstance(callee, ast.Attribute)
                and isinstance(callee.value, ast.Name)
                and callee.value.id == "object"
                and callee.attr == "__new__"
                and isinstance(target, ast.Name)
                and target.id == "_CrossCheckedAuthenticatedCheckpointFinalityTransitionV1"
            ):
                minting_sites.append((node.name, child.lineno))

    assert len(execution_sites) == 1
    assert len(minting_sites) == 1
    assert minting_sites[0][0] == "cross_check_authenticated"
    assert execution_sites[0] < minting_sites[0][1]


def test_pinned_checker_rejects_instance_method_shadowing(rust_checker: Path) -> None:
    checker = _checker(rust_checker)

    assert not hasattr(checker, "__dict__")
    with pytest.raises((AttributeError, TypeError)):
        object.__setattr__(
            checker,
            "cross_check_authenticated",
            lambda **_kwargs: object(),
        )


def test_checker_manifest_drift_rejects_before_execution(
    rust_checker: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    checker = _checker(rust_checker)
    object.__setattr__(checker, "authority_manifest_json", _manifest(rust_checker) + b"\n")
    called = False

    def forbidden(**_kwargs: object) -> bytes:
        nonlocal called
        called = True
        raise AssertionError("checker process must not execute")

    monkeypatch.setattr(checker_adapter, "execute_pinned_verifier_once", forbidden)
    policy = _governed_policy()
    with pytest.raises(CheckpointFinalityCheckerAdapterRejectedV1) as rejected:
        checker.cross_check_authenticated(
            policy=policy,
            finality=_authenticated_finality(policy),
        )

    assert rejected.value.reason is (
        CheckpointFinalityCheckerAdapterRejectV1.AUTHORITY_MANIFEST_INVALID
    )
    assert called is False


def test_finality_scope_mutation_rejects_before_checker_execution(
    rust_checker: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    policy = _governed_policy()
    valid = _authenticated_finality(policy)
    altered = replace(valid._projection, policy_root=_root("wrong-policy"))
    mutated = _AuthenticatedExactCheckpointFinalityTransitionV3(
        altered,
        exact_certificate_bytes=valid._exact_certificate_bytes,
        exact_finality_evidence_bytes=valid._exact_finality_evidence_bytes,
        seal=_AUTHENTICATED_CHECKPOINT_FINALITY_SEAL_V3,
    )
    called = False

    def forbidden(**_kwargs: object) -> bytes:
        nonlocal called
        called = True
        raise AssertionError("checker process must not execute")

    monkeypatch.setattr(checker_adapter, "execute_pinned_verifier_once", forbidden)
    with pytest.raises(CheckpointFinalityCheckerAdapterRejectedV1) as rejected:
        _checker(rust_checker).cross_check_authenticated(
            policy=policy,
            finality=mutated,
        )

    assert rejected.value.reason is (
        CheckpointFinalityCheckerAdapterRejectV1.AUTHENTICATED_INPUT_INVALID
    )
    assert called is False
