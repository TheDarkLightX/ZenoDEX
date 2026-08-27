from __future__ import annotations

import json
import os
import subprocess
import sys
from dataclasses import replace
from pathlib import Path
from typing import Callable, cast

import pytest

from tools import build_current_tau_compatibility_v1 as builder_module
from tools import check_current_tau_compatibility_v1 as checker_module
from tools import current_tau_source_analysis_v1 as analysis_module
from tools.build_current_tau_compatibility_v1 import REPO_ROOT, TauReplayPathsV1
from tools.current_tau_compatibility_core_v1 import (
    ACTIVE_PLAN_SHA256_V1,
    ACTIVE_REGISTRY_SHA256_V1,
    ADMISSION_RECEIPT_PAYLOAD_SHA256_V1,
    ADMISSION_RECEIPT_SHA256_V1,
    CURRENT_TAU_COMMIT_V1,
    CURRENT_TAU_LANG_COMMIT_V1,
    CURRENT_TAU_LANG_SOURCE_SHA256_V1,
    CURRENT_TAU_LANG_TREE_LISTING_SHA256_V1,
    CURRENT_TAU_LANG_TREE_V1,
    CURRENT_TAU_SOURCE_SHA256_V1,
    CURRENT_TAU_TREE_LISTING_SHA256_V1,
    CURRENT_TAU_TREE_V1,
    EXPECTED_CURRENT_RESERVED_STREAMS_V1,
    EXPECTED_CURRENT_SIGNING_SHA256_V1,
    EXPECTED_CURRENT_SUCCESS_ENVELOPE_SHA256_V1,
    EXPECTED_CURRENT_USER_TX_SIGNING_FIELDS_V1,
    EXPECTED_LEGACY_OPERATION_STREAMS_V1,
    EXPECTED_LEGACY_SIGNING_SHA256_V1,
    EXPECTED_LEGACY_USER_TX_SIGNING_FIELDS_V1,
    EXPECTED_REMOVED_RPC_NAMES_V1,
    HISTORICAL_BRIDGE_COMMIT_V1,
    HISTORICAL_BRIDGE_SOURCE_SHA256_V1,
    HISTORICAL_BRIDGE_TREE_LISTING_SHA256_V1,
    HISTORICAL_BRIDGE_TREE_V1,
    CurrentTauCompatibilityRejectV1,
    CurrentTauCompatibilitySnapshotV1,
    SourcePinV1,
    build_current_tau_compatibility_artifact_v1,
)
from tools.current_tau_compatibility_pins_v1 import (
    IMPLEMENTATION_EVIDENCE_PATHS_V1,
    LOCAL_PROFILE_SOURCE_SHA256_V1,
)
from tools.current_tau_replay_io_v1 import _git_environment_v1

_UNUSED_PATHS = TauReplayPathsV1(
    REPO_ROOT,
    Path("unused-current-tau"),
    Path("unused-tau-lang"),
    Path("unused-historical-bridge"),
)


def _snapshot() -> CurrentTauCompatibilitySnapshotV1:
    return CurrentTauCompatibilitySnapshotV1(
        current_tau=SourcePinV1(
            CURRENT_TAU_COMMIT_V1,
            CURRENT_TAU_TREE_V1,
            CURRENT_TAU_TREE_LISTING_SHA256_V1,
            CURRENT_TAU_SOURCE_SHA256_V1,
        ),
        current_tau_lang=SourcePinV1(
            CURRENT_TAU_LANG_COMMIT_V1,
            CURRENT_TAU_LANG_TREE_V1,
            CURRENT_TAU_LANG_TREE_LISTING_SHA256_V1,
            CURRENT_TAU_LANG_SOURCE_SHA256_V1,
        ),
        historical_bridge=SourcePinV1(
            HISTORICAL_BRIDGE_COMMIT_V1,
            HISTORICAL_BRIDGE_TREE_V1,
            HISTORICAL_BRIDGE_TREE_LISTING_SHA256_V1,
            HISTORICAL_BRIDGE_SOURCE_SHA256_V1,
        ),
        implementation=SourcePinV1(
            "1" * 40,
            "2" * 40,
            "3" * 64,
            (
                *LOCAL_PROFILE_SOURCE_SHA256_V1,
                *((path, "4" * 64) for path in IMPLEMENTATION_EVIDENCE_PATHS_V1),
            ),
        ),
        active_plan_sha256=ACTIVE_PLAN_SHA256_V1,
        active_registry_sha256=ACTIVE_REGISTRY_SHA256_V1,
        admission_receipt_sha256=ADMISSION_RECEIPT_SHA256_V1,
        admission_receipt_payload_sha256=ADMISSION_RECEIPT_PAYLOAD_SHA256_V1,
        current_reserved_streams=EXPECTED_CURRENT_RESERVED_STREAMS_V1,
        legacy_operation_streams=EXPECTED_LEGACY_OPERATION_STREAMS_V1,
        current_user_tx_signing_fields=EXPECTED_CURRENT_USER_TX_SIGNING_FIELDS_V1,
        local_user_tx_signing_fields=EXPECTED_LEGACY_USER_TX_SIGNING_FIELDS_V1,
        historical_bridge_user_tx_signing_fields=EXPECTED_LEGACY_USER_TX_SIGNING_FIELDS_V1,
        current_signing_sha256=EXPECTED_CURRENT_SIGNING_SHA256_V1,
        local_signing_sha256=EXPECTED_LEGACY_SIGNING_SHA256_V1,
        current_success_envelope_sha256=EXPECTED_CURRENT_SUCCESS_ENVELOPE_SHA256_V1,
        local_prefix_parser_accepts_current_envelope=False,
        current_rpc_names_absent=EXPECTED_REMOVED_RPC_NAMES_V1,
        local_client_rpc_methods=("getappstate", "getstateproof"),
        historical_bridge_rpc_names_present=("apply_app_tx", "getappstate"),
        local_profile_force_test="1",
        local_runner_forwards_force_test=True,
        local_runner_default_tau_env="development",
        current_tau_force_test_requires_test_env=True,
        historical_bridge_force_test_enters_mock_mode=True,
    )


def _artifact() -> dict[str, object]:
    return build_current_tau_compatibility_artifact_v1(_snapshot())


def _assert_no_authority(report: dict[str, object]) -> None:
    assert report["o003a_evidence_complete"] is False
    assert report["o002_implemented"] is False
    assert report["production_authority"] == "NONE"
    assert report["release_authority"] == "NONE"
    assert report["settlement_authority"] == "NONE"
    assert report["value_movement_authority"] == "NONE"
    assert report["value_movement_claim_allowed"] is False
    assert report["vm_gates_closed"] == []


def _assert_success_without_promotion(report: dict[str, object]) -> None:
    assert report["ok"] is True
    assert report["o003a_evidence_complete"] is True
    assert report["o002_implemented"] is False
    assert report["route_quarantine_implemented"] is False
    assert report["current_tau_compatible"] is False
    assert report["production_authority"] == "NONE"
    assert report["release_authority"] == "NONE"
    assert report["settlement_authority"] == "NONE"
    assert report["value_movement_authority"] == "NONE"
    assert report["value_movement_claim_allowed"] is False
    assert report["vm_gates_closed"] == []


def _write_canonical(tmp_path: Path, value: object) -> Path:
    target = tmp_path / "compatibility.json"
    target.write_text(json.dumps(value, sort_keys=True, separators=(",", ":")), encoding="utf-8")
    return target


def test_bdd_given_exact_sources_when_replayed_then_o003a_evidence_is_research_complete(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    # Arrange
    monkeypatch.setattr(
        checker_module,
        "load_current_tau_compatibility_snapshot_v1",
        lambda *_args: _snapshot(),
    )

    # Act
    artifact_path = _write_canonical(tmp_path, _artifact())
    report = checker_module.check_current_tau_compatibility_v1(
        paths=_UNUSED_PATHS,
        artifact_path=artifact_path,
    )

    # Assert
    _assert_success_without_promotion(report)


def test_differential_given_current_and_historical_signing_when_built_then_hashes_diverge() -> None:
    # Arrange / Act
    artifact = build_current_tau_compatibility_artifact_v1(_snapshot())
    witnesses = cast(list[dict[str, object]], artifact["witnesses"])
    witness = next(
        row
        for row in witnesses
        if row["witness_id"] == "signature_preimage_differential"
    )

    # Assert
    assert witness["differential"] is True
    assert witness["current_tau_vector_sha256"] != witness["historical_zenodex_vector_sha256"]
    current_fields = cast(list[str], witness["current_tau_user_tx_fields"])
    historical_fields = cast(list[str], witness["historical_zenodex_user_tx_fields"])
    assert "tx_type" in current_fields
    assert "tx_type" not in historical_fields


def test_mutation_given_reserved_stream_source_byte_changes_when_classified_then_rejects() -> None:
    # Arrange: mutate the exact semantic literal from 11 to 12.
    source = b"RESERVED_STREAMS = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11}\n"
    mutated_source = source.replace(b", 11}", b", 12}")
    observed = analysis_module.literal_int_set_v1(
        mutated_source,
        "mutated:tau_defs.py",
        "RESERVED_STREAMS",
    )
    mutated_snapshot = replace(_snapshot(), current_reserved_streams=observed)

    # Act / Assert
    with pytest.raises(CurrentTauCompatibilityRejectV1) as raised:
        build_current_tau_compatibility_artifact_v1(mutated_snapshot)
    assert raised.value.code == "RESERVED_STREAM_DRIFT"


def test_mutation_given_tx_type_source_byte_is_removed_when_classified_then_rejects() -> None:
    # Arrange
    source = b"""\
def _get_signing_message_bytes(payload):
    tx_type = payload.get("tx_type", "user_tx")
    signing_dict = {
        "sender_pubkey": payload["sender_pubkey"],
        "sequence_number": payload["sequence_number"],
        "expiration_time": payload["expiration_time"],
        "fee_limit": payload["fee_limit"],
        "tx_type": tx_type,
    }
    if tx_type == "user_tx":
        signing_dict["operations"] = payload.get("operations", {})
    return json.dumps(signing_dict, sort_keys=True, separators=(",", ":")).encode()
"""
    mutated_source = source.replace(b'        "tx_type": tx_type,\n', b"")
    observed = analysis_module.user_tx_signing_fields_v1(
        mutated_source,
        "mutated:commands/sendtx.py",
        "_get_signing_message_bytes",
    )
    mutated_snapshot = replace(_snapshot(), current_user_tx_signing_fields=observed)

    # Act / Assert
    with pytest.raises(CurrentTauCompatibilityRejectV1) as raised:
        build_current_tau_compatibility_artifact_v1(mutated_snapshot)
    assert raised.value.code == "CURRENT_SIGNING_FIELDS_DRIFT"


@pytest.mark.parametrize(
    ("mutate", "code"),
    [
        (
            lambda snapshot: replace(
                snapshot, local_prefix_parser_accepts_current_envelope=True
            ),
            "RPC_PARSER_DIFFERENTIAL_DRIFT",
        ),
        (lambda snapshot: replace(snapshot, local_profile_force_test="0"), "FORCE_TEST_PROFILE_DRIFT"),
        (
            lambda snapshot: replace(snapshot, local_runner_forwards_force_test=False),
            "FORCE_TEST_SEMANTIC_DRIFT",
        ),
        (
            lambda snapshot: replace(snapshot, current_tau_force_test_requires_test_env=False),
            "FORCE_TEST_SEMANTIC_DRIFT",
        ),
        (
            lambda snapshot: replace(
                snapshot, historical_bridge_force_test_enters_mock_mode=False
            ),
            "FORCE_TEST_SEMANTIC_DRIFT",
        ),
    ],
)
def test_mutation_given_rpc_or_force_test_fact_drifts_when_built_then_typed_rejects(
    mutate: Callable[
        [CurrentTauCompatibilitySnapshotV1], CurrentTauCompatibilitySnapshotV1
    ],
    code: str,
) -> None:
    # Arrange
    mutated = mutate(_snapshot())

    # Act / Assert
    with pytest.raises(CurrentTauCompatibilityRejectV1) as raised:
        build_current_tau_compatibility_artifact_v1(mutated)
    assert raised.value.code == code


def test_mutation_given_upstream_source_hash_changes_when_built_then_pin_rejects() -> None:
    # Arrange
    current = _snapshot().current_tau
    first_path, _ = current.source_sha256[0]
    mutated_hashes = ((first_path, "0" * 64), *current.source_sha256[1:])
    mutated = replace(_snapshot(), current_tau=replace(current, source_sha256=mutated_hashes))

    # Act / Assert
    with pytest.raises(CurrentTauCompatibilityRejectV1) as raised:
        build_current_tau_compatibility_artifact_v1(mutated)
    assert raised.value.code == "SOURCE_SHA256_DRIFT"


def test_mutation_given_current_rpc_reappears_when_built_then_absence_witness_rejects() -> None:
    # Arrange
    mutated = replace(
        _snapshot(),
        current_rpc_names_absent=("apply_app_tx", "getstateproof"),
    )

    # Act / Assert
    with pytest.raises(CurrentTauCompatibilityRejectV1) as raised:
        build_current_tau_compatibility_artifact_v1(mutated)
    assert raised.value.code == "CURRENT_RPC_ABSENCE_DRIFT"


def test_mutation_given_artifact_verdict_changes_when_checked_then_exact_projection_rejects(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    # Arrange
    mutated = _artifact()
    route = cast(dict[str, object], mutated["route_disposition"])
    route["current_tau_compatible"] = True
    artifact_path = _write_canonical(tmp_path, mutated)
    monkeypatch.setattr(
        checker_module,
        "load_current_tau_compatibility_snapshot_v1",
        lambda *_args: _snapshot(),
    )

    # Act
    report = checker_module.check_current_tau_compatibility_v1(
        paths=_UNUSED_PATHS,
        artifact_path=artifact_path,
    )

    # Assert
    assert report["ok"] is False
    findings = cast(list[dict[str, object]], report["findings"])
    assert findings[0]["code"] == "ARTIFACT_BINDING_DRIFT"
    _assert_no_authority(report)


def test_bva_given_noncanonical_artifact_when_checked_then_rejects_before_replay(
    tmp_path: Path,
) -> None:
    # Arrange
    target = tmp_path / "pretty.json"
    target.write_text(json.dumps(_artifact(), indent=2), encoding="utf-8")

    # Act
    report = checker_module.check_current_tau_compatibility_v1(
        paths=_UNUSED_PATHS,
        artifact_path=target,
    )

    # Assert
    assert report["ok"] is False
    findings = cast(list[dict[str, object]], report["findings"])
    assert findings[0]["code"] == "NONCANONICAL_ARTIFACT"
    _assert_no_authority(report)


def test_rejection_given_artifact_is_missing_when_checked_then_fails_closed(tmp_path: Path) -> None:
    # Arrange / Act
    report = checker_module.check_current_tau_compatibility_v1(
        paths=_UNUSED_PATHS,
        artifact_path=tmp_path / "missing.json",
    )

    # Assert
    assert report["ok"] is False
    _assert_no_authority(report)


def test_bva_given_bool_reserved_stream_when_built_then_exact_element_type_rejects() -> None:
    # Arrange: bool aliases integer one under Python equality and must still reject.
    streams = cast(tuple[int, ...], (0, True, *range(2, 12)))
    mutated = replace(_snapshot(), current_reserved_streams=streams)

    # Act / Assert
    with pytest.raises(CurrentTauCompatibilityRejectV1) as raised:
        build_current_tau_compatibility_artifact_v1(mutated)
    assert raised.value.code == "RESERVED_STREAM_ELEMENT_TYPE"
    assert raised.value.path == "current_reserved_streams[1]"


def test_mutation_given_active_registry_hash_drifts_then_admission_binding_rejects() -> None:
    # Arrange
    mutated = replace(_snapshot(), active_registry_sha256="0" * 64)

    # Act / Assert
    with pytest.raises(CurrentTauCompatibilityRejectV1) as raised:
        build_current_tau_compatibility_artifact_v1(mutated)
    assert raised.value.code == "ACTIVE_PLAN_ADMISSION_DRIFT"


def test_rejection_given_profile_runtime_path_is_unbound_then_typed_rejects(
    tmp_path: Path,
) -> None:
    # Arrange
    root = tmp_path / "root"
    supplied = tmp_path / "reviewed-source"
    root.mkdir()
    supplied.mkdir()
    paths = TauReplayPathsV1(root, supplied, supplied, supplied)

    # Act / Assert
    with pytest.raises(CurrentTauCompatibilityRejectV1) as raised:
        builder_module._require_profile_tau_source_bound_v1(paths)
    assert raised.value.code == "PROFILE_TAU_SOURCE_UNBOUND"


def test_given_profile_runtime_path_resolves_to_reviewed_source_then_binding_accepts(
    tmp_path: Path,
) -> None:
    # Arrange
    root = tmp_path / "root"
    supplied = tmp_path / "reviewed-source"
    (root / "external").mkdir(parents=True)
    supplied.mkdir()
    (root / "external" / "tau-testnet").symlink_to(supplied)
    paths = TauReplayPathsV1(root, supplied, supplied, supplied)

    # Act / Assert
    builder_module._require_profile_tau_source_bound_v1(paths)


def test_mutation_given_profile_binding_call_is_deleted_then_loader_test_fails(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange
    head = "a" * 40
    monkeypatch.setattr(builder_module, "_git_head_v1", lambda _root: head)
    monkeypatch.setattr(
        builder_module,
        "_implementation_subject_commit_v1",
        lambda _root, _head: head,
    )
    monkeypatch.setattr(builder_module, "_git_is_ancestor_v1", lambda *_args: True)

    def reject_binding(_paths: TauReplayPathsV1) -> None:
        raise CurrentTauCompatibilityRejectV1(
            "PROFILE_TAU_SOURCE_UNBOUND", "external/tau-testnet", "test sentinel"
        )

    monkeypatch.setattr(builder_module, "_require_profile_tau_source_bound_v1", reject_binding)
    monkeypatch.setattr(
        builder_module,
        "_load_sources_v1",
        lambda *_args: (_ for _ in ()).throw(AssertionError("binding guard skipped")),
    )

    # Act / Assert
    with pytest.raises(CurrentTauCompatibilityRejectV1) as raised:
        builder_module.load_current_tau_compatibility_snapshot_v1(_UNUSED_PATHS)
    assert raised.value.code == "PROFILE_TAU_SOURCE_UNBOUND"


def test_mutation_given_historical_checkout_guard_call_is_deleted_then_loader_test_fails(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange
    pin = SourcePinV1("a" * 40, "b" * 40, "c" * 64, ())
    monkeypatch.setattr(builder_module, "_implementation_source_hashes_v1", lambda *_args: ())
    monkeypatch.setattr(builder_module, "_source_pin_v1", lambda *_args: (pin, {}))

    def reject_checkout(_repo: Path) -> None:
        raise CurrentTauCompatibilityRejectV1(
            "HISTORICAL_BRIDGE_HEAD_DRIFT", "historical_bridge.HEAD", "test sentinel"
        )

    monkeypatch.setattr(
        builder_module, "_require_historical_bridge_checkout_v1", reject_checkout
    )
    monkeypatch.setattr(builder_module, "_require_worktree_sources_match_v1", lambda *_args: None)

    # Act / Assert
    with pytest.raises(CurrentTauCompatibilityRejectV1) as raised:
        builder_module._load_sources_v1(_UNUSED_PATHS, "a" * 40)
    assert raised.value.code == "HISTORICAL_BRIDGE_HEAD_DRIFT"


def test_mutation_given_historical_worktree_guard_is_deleted_then_helper_test_fails(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange
    monkeypatch.setattr(
        builder_module,
        "_git_head_v1",
        lambda _root: HISTORICAL_BRIDGE_COMMIT_V1,
    )

    def reject_worktree(*_args: object) -> None:
        raise CurrentTauCompatibilityRejectV1(
            "WORKTREE_SOURCE_DRIFT", "tau_manager.py", "test sentinel"
        )

    monkeypatch.setattr(builder_module, "_require_worktree_sources_match_v1", reject_worktree)

    # Act / Assert
    with pytest.raises(CurrentTauCompatibilityRejectV1) as raised:
        builder_module._require_historical_bridge_checkout_v1(Path("historical"))
    assert raised.value.code == "WORKTREE_SOURCE_DRIFT"


def test_mutation_given_active_registry_bytes_drift_when_loaded_then_shell_rejects(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    # Arrange
    plan_path = REPO_ROOT / "docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V2.json"
    registry_path = REPO_ROOT / builder_module.ACTIVE_REGISTRY_PATH_V1
    admission_path = REPO_ROOT / builder_module.ADMISSION_RECEIPT_PATH_V1
    target_registry = tmp_path / builder_module.ACTIVE_REGISTRY_PATH_V1
    target_admission = tmp_path / builder_module.ADMISSION_RECEIPT_PATH_V1
    target_registry.parent.mkdir(parents=True)
    registry = json.loads(registry_path.read_text(encoding="utf-8"))
    registry["active_plan_count"] = 0
    target_registry.write_text(json.dumps(registry), encoding="utf-8")
    target_admission.write_bytes(admission_path.read_bytes())
    monkeypatch.setattr(
        builder_module,
        "_git_source_bytes_v1",
        lambda _root, _commit, _path: plan_path.read_bytes(),
    )

    # Act / Assert
    with pytest.raises(CurrentTauCompatibilityRejectV1) as raised:
        builder_module._load_active_plan_binding_v1(tmp_path)
    assert raised.value.code == "ACTIVE_PLAN_ADMISSION_DRIFT"


def test_mutation_given_reserved_stream_is_overwritten_then_ast_rejects() -> None:
    # Arrange
    source = (
        b"RESERVED_STREAMS = {0, 1, 2}\n"
        b"RESERVED_STREAMS = set()\n"
    )

    # Act / Assert
    with pytest.raises(CurrentTauCompatibilityRejectV1) as raised:
        analysis_module.literal_int_set_v1(source, "mutant:tau_defs.py", "RESERVED_STREAMS")
    assert raised.value.code == "INT_SET_SHAPE"


def test_mutation_given_nested_reserved_stream_overwrite_then_ast_rejects() -> None:
    # Arrange
    source = (
        b"RESERVED_STREAMS = {0, 1, 2}\n"
        b"if True:\n"
        b"    RESERVED_STREAMS = set()\n"
    )

    # Act / Assert
    with pytest.raises(CurrentTauCompatibilityRejectV1) as raised:
        analysis_module.literal_int_set_v1(source, "mutant:tau_defs.py", "RESERVED_STREAMS")
    assert raised.value.code == "INT_SET_SHAPE"


def test_mutation_given_signing_field_is_deleted_before_return_then_ast_rejects() -> None:
    # Arrange
    source = b'''\
def _get_signing_message_bytes(payload):
    tx_type = payload.get("tx_type", "user_tx")
    signing_dict = {
        "sender_pubkey": payload["sender_pubkey"],
        "sequence_number": payload["sequence_number"],
        "expiration_time": payload["expiration_time"],
        "fee_limit": payload["fee_limit"],
        "tx_type": tx_type,
    }
    if tx_type == "user_tx":
        signing_dict["operations"] = payload.get("operations", {})
    del signing_dict["tx_type"]
    return json.dumps(signing_dict, sort_keys=True, separators=(",", ":")).encode()
'''

    # Act / Assert
    with pytest.raises(CurrentTauCompatibilityRejectV1) as raised:
        analysis_module.user_tx_signing_fields_v1(
            source, "mutant:sendtx.py", "_get_signing_message_bytes"
        )
    assert raised.value.code == "SIGNING_MUTATION_SHAPE"


def test_mutation_given_signing_has_nested_early_return_then_ast_rejects() -> None:
    # Arrange
    source = b'''\
def _get_signing_message_bytes(payload):
    signing_dict = {
        "sender_pubkey": payload["sender_pubkey"],
        "sequence_number": payload["sequence_number"],
        "expiration_time": payload["expiration_time"],
        "operations": payload["operations"],
        "fee_limit": payload["fee_limit"],
    }
    if True:
        return b"legacy"
    return json.dumps(signing_dict, sort_keys=True, separators=(",", ":")).encode()
'''

    # Act / Assert
    with pytest.raises(CurrentTauCompatibilityRejectV1) as raised:
        analysis_module.user_tx_signing_fields_v1(
            source, "mutant:sendtx.py", "_get_signing_message_bytes"
        )
    assert raised.value.code == "SIGNING_RETURN_SHAPE"


def test_mutation_given_success_envelope_is_dead_code_then_ast_rejects() -> None:
    # Arrange
    source = b'''\
def success_response(command, data):
    return json.dumps({"status": "wrong"})
    envelope = {"status": "ok", "command": command, "data": dict(data)}
'''

    # Act / Assert
    with pytest.raises(CurrentTauCompatibilityRejectV1) as raised:
        analysis_module.require_success_envelope_v1(source, "mutant:api_response.py")
    assert raised.value.code == "SUCCESS_ENVELOPE_SHAPE"


def test_mutation_given_current_force_test_has_extra_true_path_then_analyzer_rejects() -> None:
    # Arrange
    source = b'''\
def is_force_test_enabled():
    requested = os.environ.get("TAU_FORCE_TEST", "0") == "1"
    if not requested:
        return False
    runtime_env = os.environ.get("TAU_ENV", "development")
    if runtime_env == "test":
        return True
    if runtime_env == "development":
        return True
    return False
'''

    # Act / Assert
    assert analysis_module.force_test_requires_test_env_v1(
        source, "mutant:tau_manager.py"
    ) is False


def test_mutation_given_current_runtime_env_is_constant_test_then_analyzer_rejects() -> None:
    # Arrange
    source = b'''\
def is_force_test_enabled():
    requested = os.environ.get("TAU_FORCE_TEST", "0") == "1"
    if not requested:
        return False
    runtime_env = "test"
    if runtime_env == "test":
        return True
    return False
'''

    # Act / Assert
    assert analysis_module.force_test_requires_test_env_v1(
        source, "mutant:tau_manager.py"
    ) is False


def test_mutation_given_historical_force_condition_is_negated_then_analyzer_rejects() -> None:
    # Arrange
    source = b'''\
def start_and_manage_tau_process():
    tau_test_mode = False
    if os.environ.get("TAU_FORCE_TEST", "0") != "1":
        tau_test_mode = True
        return
'''

    # Act / Assert
    assert analysis_module.historical_force_test_enters_mock_v1(
        source, "mutant:tau_manager.py"
    ) is False


def test_mutation_given_command_name_is_computed_then_registry_analyzer_rejects() -> None:
    # Arrange
    source = b'''\
class ServiceContainer:
    @classmethod
    def build(cls, overrides=None):
        command_handlers = overrides or {"get" + "appstate": handler}
        return cls(command_handlers)
'''

    # Act / Assert
    with pytest.raises(CurrentTauCompatibilityRejectV1) as raised:
        analysis_module.command_registry_keys_v1(source, "mutant:app/container.py")
    assert raised.value.code == "COMMAND_REGISTRY_KEY"


def test_mutation_given_command_is_added_after_registry_then_analyzer_rejects() -> None:
    # Arrange
    source = b'''\
class ServiceContainer:
    @classmethod
    def build(cls, overrides=None):
        command_handlers = overrides or {"sendtx": handler}
        command_handlers["get" + "appstate"] = handler
        return cls(command_handlers)
'''

    # Act / Assert
    with pytest.raises(CurrentTauCompatibilityRejectV1) as raised:
        analysis_module.command_registry_keys_v1(source, "mutant:app/container.py")
    assert raised.value.code == "COMMAND_REGISTRY_MUTATION"


def test_mutation_given_bridge_call_is_dead_then_analyzer_rejects() -> None:
    # Arrange
    source = b'''\
def _call_app_bridge(bridge):
    try:
        if False:
            bridge.apply_app_tx()
        return None
    except Exception:
        return None
'''

    # Act / Assert
    assert analysis_module.historical_apply_app_tx_bridge_v1(
        source, "mutant:createblock.py"
    ) is False


def test_builder_failure_report_closes_every_authority_surface() -> None:
    # Arrange / Act
    report = builder_module._builder_failure_report_v1("GIT_OBJECT_MISSING")

    # Assert
    _assert_no_authority(report)


def test_git_environment_forbids_lazy_fetch_and_ambient_configuration() -> None:
    # Arrange / Act
    environment = _git_environment_v1()

    # Assert
    assert environment["GIT_NO_LAZY_FETCH"] == "1"
    assert environment["GIT_CONFIG_GLOBAL"] == "/dev/null"
    assert environment["GIT_CONFIG_NOSYSTEM"] == "1"
    assert environment["GIT_NO_REPLACE_OBJECTS"] == "1"
    assert environment["GIT_OPTIONAL_LOCKS"] == "0"
    assert "HOME" not in environment


def test_runtime_import_closure_contains_only_manifested_repository_files() -> None:
    # Arrange
    script = f'''\
from pathlib import Path
import sys
root = Path({str(REPO_ROOT)!r}).resolve()
sys.path.insert(0, str(root))
import tools.check_current_tau_compatibility_v1
paths = set()
for module in sys.modules.values():
    path = getattr(module, "__file__", None)
    if path is None:
        continue
    try:
        paths.add(str(Path(path).resolve().relative_to(root)))
    except ValueError:
        pass
print("\\n".join(sorted(paths)))
'''

    # Act
    result = subprocess.run(
        [sys.executable, "-I", "-c", script],
        cwd=REPO_ROOT,
        env={
            "LC_ALL": "C",
            "PATH": os.defpath,
            "PYTHONDONTWRITEBYTECODE": "1",
        },
        check=False,
        capture_output=True,
        text=True,
        timeout=10,
    )

    # Assert
    assert result.returncode == 0, result.stderr
    assert tuple(result.stdout.splitlines()) == (
        "tools/__init__.py",
        "tools/build_current_tau_compatibility_v1.py",
        "tools/check_current_tau_compatibility_v1.py",
        "tools/current_tau_compatibility_core_v1.py",
        "tools/current_tau_compatibility_pins_v1.py",
        "tools/current_tau_replay_io_v1.py",
        "tools/current_tau_source_analysis_v1.py",
    )


def test_checker_internal_fault_returns_complete_no_authority_report(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    # Arrange
    artifact_path = _write_canonical(tmp_path, _artifact())
    monkeypatch.setattr(
        checker_module,
        "load_current_tau_compatibility_snapshot_v1",
        lambda *_args: (_ for _ in ()).throw(RuntimeError("injected")),
    )

    # Act
    report = checker_module.check_current_tau_compatibility_v1(
        paths=_UNUSED_PATHS, artifact_path=artifact_path
    )

    # Assert
    findings = cast(list[dict[str, object]], report["findings"])
    assert findings[0]["code"] == "CHECKER_INTERNAL_ERROR"
    _assert_no_authority(report)


def test_cli_missing_arguments_returns_typed_no_authority_reports(
    capsys: pytest.CaptureFixture[str],
) -> None:
    # Arrange / Act
    checker_status = checker_module.main([])
    checker_report = json.loads(capsys.readouterr().out)
    builder_status = builder_module.main([])
    builder_report = json.loads(capsys.readouterr().out)

    # Assert
    assert checker_status == 1
    assert checker_report["findings"][0]["code"] == "CLI_INPUT"
    _assert_no_authority(checker_report)
    assert builder_status == 1
    assert builder_report["finding"] == "CLI_INPUT"
    _assert_no_authority(builder_report)


def test_builder_internal_fault_returns_complete_no_authority_report(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    # Arrange
    monkeypatch.setattr(
        builder_module,
        "build_current_tau_compatibility_bytes_v1",
        lambda *_args, **_kwargs: (_ for _ in ()).throw(RuntimeError("injected")),
    )

    # Act
    status = builder_module.main(
        [
            "--check",
            "--tau-testnet-repo",
            "current",
            "--tau-lang-repo",
            "lang",
            "--historical-bridge-repo",
            "historical",
        ]
    )
    report = json.loads(capsys.readouterr().out)

    # Assert
    assert status == 1
    assert report["finding"] == "BUILDER_INTERNAL_ERROR"
    _assert_no_authority(report)
