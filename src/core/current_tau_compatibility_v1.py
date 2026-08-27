"""Pure classification for the current-Tau versus historical-bridge boundary.

This module owns no network, Git, filesystem, Tau, settlement, or publication
capability.  Its input is an immutable source snapshot produced by the shell.
It returns one research-only incompatibility artifact or a typed rejection.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from typing import NoReturn

from src.state.canonical import canonical_json_bytes

from .current_tau_compatibility_pins_v1 import (
    ACTIVE_PLAN_COMMIT_V1,
    ACTIVE_PLAN_SHA256_V1,
    ACTIVE_REGISTRY_SHA256_V1,
    ADMISSION_RECEIPT_PAYLOAD_SHA256_V1,
    ADMISSION_RECEIPT_SHA256_V1,
    CHECK_SCHEMA_V1,
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
    IMPLEMENTATION_SOURCE_PATHS_V1,
    LOCAL_PROFILE_SOURCE_SHA256_V1,
    SCHEMA_V1,
)


@dataclass(frozen=True)
class CurrentTauCompatibilityRejectV1(ValueError):
    """Stable rejection from the pure compatibility classifier."""

    code: str
    path: str
    detail: str

    def __str__(self) -> str:
        return f"{self.code} at {self.path}: {self.detail}"


@dataclass(frozen=True)
class SourcePinV1:
    commit: str
    tree: str
    tree_listing_sha256: str
    source_sha256: tuple[tuple[str, str], ...]


@dataclass(frozen=True)
class CurrentTauCompatibilitySnapshotV1:
    current_tau: SourcePinV1
    current_tau_lang: SourcePinV1
    historical_bridge: SourcePinV1
    implementation: SourcePinV1
    active_plan_sha256: str
    active_registry_sha256: str
    admission_receipt_sha256: str
    admission_receipt_payload_sha256: str
    current_reserved_streams: tuple[int, ...]
    legacy_operation_streams: tuple[int, ...]
    current_user_tx_signing_fields: tuple[str, ...]
    local_user_tx_signing_fields: tuple[str, ...]
    historical_bridge_user_tx_signing_fields: tuple[str, ...]
    current_signing_sha256: str
    local_signing_sha256: str
    current_success_envelope_sha256: str
    local_prefix_parser_accepts_current_envelope: bool
    current_rpc_names_absent: tuple[str, ...]
    local_client_rpc_methods: tuple[str, ...]
    historical_bridge_rpc_names_present: tuple[str, ...]
    local_profile_force_test: str
    local_runner_forwards_force_test: bool
    local_runner_default_tau_env: str
    current_tau_force_test_requires_test_env: bool
    historical_bridge_force_test_enters_mock_mode: bool


def _reject(code: str, path: str, detail: str) -> NoReturn:
    raise CurrentTauCompatibilityRejectV1(code, path, detail)


def _require_exact(value: object, expected: object, code: str, path: str) -> None:
    if type(value) is not type(expected) or value != expected:
        _reject(code, path, "exact source-derived value drift")


def _require_hex(value: object, length: int, code: str, path: str) -> None:
    if (
        type(value) is not str
        or len(value) != length
        or any(character not in "0123456789abcdef" for character in value)
    ):
        _reject(code, path, f"must be {length} lowercase hexadecimal characters")


def _require_exact_int_tuple(
    value: object,
    expected: tuple[int, ...],
    code: str,
    path: str,
) -> None:
    if type(value) is not tuple or len(value) != len(expected):
        _reject(code, path, "tuple shape drift")
    for index, (observed, _required) in enumerate(zip(value, expected, strict=True)):
        if type(observed) is not int:
            _reject(code, f"{path}[{index}]", "exact element type drift")


def _validate_pin(pin: SourcePinV1, expected: SourcePinV1, path: str) -> None:
    if type(pin) is not SourcePinV1:
        _reject("SOURCE_PIN_TYPE", path, "must be an exact SourcePinV1")
    _require_exact(pin.commit, expected.commit, "SOURCE_COMMIT_DRIFT", f"{path}.commit")
    _require_exact(pin.tree, expected.tree, "SOURCE_TREE_DRIFT", f"{path}.tree")
    _require_exact(
        pin.tree_listing_sha256,
        expected.tree_listing_sha256,
        "SOURCE_TREE_LISTING_DRIFT",
        f"{path}.tree_listing_sha256",
    )
    _require_exact(
        pin.source_sha256,
        expected.source_sha256,
        "SOURCE_SHA256_DRIFT",
        f"{path}.source_sha256",
    )


def _validate_implementation_pin(pin: SourcePinV1) -> None:
    if type(pin) is not SourcePinV1:
        _reject("SOURCE_PIN_TYPE", "implementation", "must be an exact SourcePinV1")
    _require_hex(pin.commit, 40, "SOURCE_COMMIT_TYPE", "implementation.commit")
    _require_hex(pin.tree, 40, "SOURCE_TREE_TYPE", "implementation.tree")
    _require_hex(
        pin.tree_listing_sha256,
        64,
        "SOURCE_TREE_LISTING_TYPE",
        "implementation.tree_listing_sha256",
    )
    if type(pin.source_sha256) is not tuple:
        _reject("SOURCE_SHA256_TYPE", "implementation.source_sha256", "must be a tuple")
    observed_paths: list[str] = []
    observed_hashes: dict[str, str] = {}
    for index, row in enumerate(pin.source_sha256):
        if type(row) is not tuple or len(row) != 2:
            _reject("SOURCE_SHA256_ROW", f"implementation.source_sha256[{index}]", "bad row")
        path, digest = row
        if type(path) is not str:
            _reject("SOURCE_PATH_TYPE", f"implementation.source_sha256[{index}]", "bad path")
        _require_hex(digest, 64, "SOURCE_SHA256_TYPE", f"implementation.source_sha256[{index}]" )
        observed_paths.append(path)
        observed_hashes[path] = digest
    _require_exact(
        tuple(observed_paths),
        IMPLEMENTATION_SOURCE_PATHS_V1,
        "IMPLEMENTATION_SOURCE_PATH_DRIFT",
        "implementation.source_sha256",
    )
    if len(observed_hashes) != len(observed_paths):
        _reject("SOURCE_PATH_DUPLICATE", "implementation.source_sha256", "duplicate path")
    for path, expected_digest in LOCAL_PROFILE_SOURCE_SHA256_V1:
        _require_exact(
            observed_hashes[path],
            expected_digest,
            "LOCAL_PROFILE_SOURCE_DRIFT",
            path,
        )


def _validate_source_pins(snapshot: CurrentTauCompatibilitySnapshotV1) -> None:
    _validate_pin(
        snapshot.current_tau,
        SourcePinV1(
            CURRENT_TAU_COMMIT_V1,
            CURRENT_TAU_TREE_V1,
            CURRENT_TAU_TREE_LISTING_SHA256_V1,
            CURRENT_TAU_SOURCE_SHA256_V1,
        ),
        "current_tau",
    )
    _validate_pin(
        snapshot.current_tau_lang,
        SourcePinV1(
            CURRENT_TAU_LANG_COMMIT_V1,
            CURRENT_TAU_LANG_TREE_V1,
            CURRENT_TAU_LANG_TREE_LISTING_SHA256_V1,
            CURRENT_TAU_LANG_SOURCE_SHA256_V1,
        ),
        "current_tau_lang",
    )
    _validate_pin(
        snapshot.historical_bridge,
        SourcePinV1(
            HISTORICAL_BRIDGE_COMMIT_V1,
            HISTORICAL_BRIDGE_TREE_V1,
            HISTORICAL_BRIDGE_TREE_LISTING_SHA256_V1,
            HISTORICAL_BRIDGE_SOURCE_SHA256_V1,
        ),
        "historical_bridge",
    )
    _validate_implementation_pin(snapshot.implementation)


def _validate_plan_binding(snapshot: CurrentTauCompatibilitySnapshotV1) -> None:
    checks = (
        (snapshot.active_plan_sha256, ACTIVE_PLAN_SHA256_V1, "PLAN_SHA256_DRIFT", "plan"),
        (snapshot.active_registry_sha256, ACTIVE_REGISTRY_SHA256_V1, "ACTIVE_PLAN_ADMISSION_DRIFT", "active_registry"),
        (snapshot.admission_receipt_sha256, ADMISSION_RECEIPT_SHA256_V1, "ACTIVE_PLAN_ADMISSION_DRIFT", "admission_receipt"),
        (snapshot.admission_receipt_payload_sha256, ADMISSION_RECEIPT_PAYLOAD_SHA256_V1, "ACTIVE_PLAN_ADMISSION_DRIFT", "admission_payload"),
    )
    for value, expected, code, path in checks:
        _require_exact(value, expected, code, path)


def _validate_signing_facts(snapshot: CurrentTauCompatibilitySnapshotV1) -> None:
    checks = (
        (
            snapshot.current_user_tx_signing_fields,
            EXPECTED_CURRENT_USER_TX_SIGNING_FIELDS_V1,
            "CURRENT_SIGNING_FIELDS_DRIFT",
            "current_user_tx_signing_fields",
        ),
        (
            snapshot.local_user_tx_signing_fields,
            EXPECTED_LEGACY_USER_TX_SIGNING_FIELDS_V1,
            "LOCAL_SIGNING_FIELDS_DRIFT",
            "local_user_tx_signing_fields",
        ),
        (
            snapshot.historical_bridge_user_tx_signing_fields,
            EXPECTED_LEGACY_USER_TX_SIGNING_FIELDS_V1,
            "BRIDGE_SIGNING_FIELDS_DRIFT",
            "historical_bridge_user_tx_signing_fields",
        ),
        (
            snapshot.current_signing_sha256,
            EXPECTED_CURRENT_SIGNING_SHA256_V1,
            "CURRENT_SIGNING_VECTOR_DRIFT",
            "current_signing_sha256",
        ),
        (
            snapshot.local_signing_sha256,
            EXPECTED_LEGACY_SIGNING_SHA256_V1,
            "LOCAL_SIGNING_VECTOR_DRIFT",
            "local_signing_sha256",
        ),
    )
    for value, expected, code, path in checks:
        _require_exact(value, expected, code, path)


def _validate_stream_facts(snapshot: CurrentTauCompatibilitySnapshotV1) -> None:
    _require_exact_int_tuple(
        snapshot.current_reserved_streams,
        EXPECTED_CURRENT_RESERVED_STREAMS_V1,
        "RESERVED_STREAM_ELEMENT_TYPE",
        "current_reserved_streams",
    )
    _require_exact(
        snapshot.current_reserved_streams,
        EXPECTED_CURRENT_RESERVED_STREAMS_V1,
        "RESERVED_STREAM_DRIFT",
        "current_reserved_streams",
    )
    _require_exact_int_tuple(
        snapshot.legacy_operation_streams,
        EXPECTED_LEGACY_OPERATION_STREAMS_V1,
        "LEGACY_STREAM_ELEMENT_TYPE",
        "legacy_operation_streams",
    )
    _require_exact(
        snapshot.legacy_operation_streams,
        EXPECTED_LEGACY_OPERATION_STREAMS_V1,
        "LEGACY_OPERATION_STREAM_DRIFT",
        "legacy_operation_streams",
    )


def _validate_rpc_and_profile_facts(snapshot: CurrentTauCompatibilitySnapshotV1) -> None:
    checks = (
        (
            snapshot.current_success_envelope_sha256,
            EXPECTED_CURRENT_SUCCESS_ENVELOPE_SHA256_V1,
            "RPC_ENVELOPE_VECTOR_DRIFT",
            "current_success_envelope_sha256",
        ),
        (
            snapshot.current_rpc_names_absent,
            EXPECTED_REMOVED_RPC_NAMES_V1,
            "CURRENT_RPC_ABSENCE_DRIFT",
            "current_rpc_names_absent",
        ),
        (
            snapshot.local_client_rpc_methods,
            ("getappstate", "getstateproof"),
            "LOCAL_RPC_METHOD_DRIFT",
            "local_client_rpc_methods",
        ),
        (
            snapshot.historical_bridge_rpc_names_present,
            ("apply_app_tx", "getappstate"),
            "BRIDGE_RPC_PRESENCE_DRIFT",
            "historical_bridge_rpc_names_present",
        ),
        (snapshot.local_profile_force_test, "1", "FORCE_TEST_PROFILE_DRIFT", "force_test"),
        (snapshot.local_runner_default_tau_env, "development", "TAU_ENV_DRIFT", "tau_env"),
    )
    for value, expected, code, path in checks:
        _require_exact(value, expected, code, path)
    for flag, flag_path in (
        (snapshot.local_runner_forwards_force_test, "local_runner_forwards_force_test"),
        (
            snapshot.current_tau_force_test_requires_test_env,
            "current_tau_force_test_requires_test_env",
        ),
        (
            snapshot.historical_bridge_force_test_enters_mock_mode,
            "historical_bridge_force_test_enters_mock_mode",
        ),
    ):
        _require_exact(flag, True, "FORCE_TEST_SEMANTIC_DRIFT", flag_path)
    _require_exact(
        snapshot.local_prefix_parser_accepts_current_envelope,
        False,
        "RPC_PARSER_DIFFERENTIAL_DRIFT",
        "local_prefix_parser_accepts_current_envelope",
    )


def _validate_snapshot(snapshot: CurrentTauCompatibilitySnapshotV1) -> None:
    if type(snapshot) is not CurrentTauCompatibilitySnapshotV1:
        _reject("SNAPSHOT_TYPE", "snapshot", "must be an exact snapshot")
    _validate_source_pins(snapshot)
    _validate_plan_binding(snapshot)
    _validate_signing_facts(snapshot)
    _validate_stream_facts(snapshot)
    _validate_rpc_and_profile_facts(snapshot)


def _reserved_stream_witness(snapshot: CurrentTauCompatibilitySnapshotV1) -> dict[str, object]:
    return {
        "witness_id": "reserved_stream_collision",
        "current_tau_reserved_streams": list(snapshot.current_reserved_streams),
        "historical_zenodex_operation_streams": list(snapshot.legacy_operation_streams),
        "collision": list(
            sorted(set(snapshot.current_reserved_streams) & set(snapshot.legacy_operation_streams))
        ),
        "verdict": "INCOMPATIBLE",
    }


def _signature_witness(snapshot: CurrentTauCompatibilitySnapshotV1) -> dict[str, object]:
    return {
        "witness_id": "signature_preimage_differential",
        "current_tau_user_tx_fields": list(snapshot.current_user_tx_signing_fields),
        "historical_zenodex_user_tx_fields": list(snapshot.local_user_tx_signing_fields),
        "current_tau_vector_sha256": snapshot.current_signing_sha256,
        "historical_zenodex_vector_sha256": snapshot.local_signing_sha256,
        "differential": snapshot.current_signing_sha256 != snapshot.local_signing_sha256,
        "verdict": "INCOMPATIBLE",
    }


def _rpc_witness(snapshot: CurrentTauCompatibilitySnapshotV1) -> dict[str, object]:
    return {
        "witness_id": "rpc_surface_differential",
        "current_tau_removed_rpc_names": list(snapshot.current_rpc_names_absent),
        "historical_client_rpc_methods": list(snapshot.local_client_rpc_methods),
        "current_success_envelope_sha256": snapshot.current_success_envelope_sha256,
        "historical_prefix_parser_accepts_current_envelope": (
            snapshot.local_prefix_parser_accepts_current_envelope
        ),
        "verdict": "INCOMPATIBLE",
    }


def _force_test_witness(snapshot: CurrentTauCompatibilitySnapshotV1) -> dict[str, object]:
    return {
        "witness_id": "force_test_disqualifier",
        "local_profile_force_test": snapshot.local_profile_force_test,
        "local_runner_forwards_force_test": snapshot.local_runner_forwards_force_test,
        "local_runner_default_tau_env": snapshot.local_runner_default_tau_env,
        "current_tau_requires_test_env": snapshot.current_tau_force_test_requires_test_env,
        "historical_bridge_enters_mock_mode": (
            snapshot.historical_bridge_force_test_enters_mock_mode
        ),
        "interpretation": (
            "The flag alone does not prove current-Tau mock execution. The selected historical "
            "bridge source consumes it as mock mode, so that local profile cannot evidence real "
            "Tau evaluation or current-Tau compatibility."
        ),
        "verdict": "DISQUALIFIES_REAL_TAU_EVIDENCE",
    }


def _source_pins_json(snapshot: CurrentTauCompatibilitySnapshotV1) -> dict[str, object]:
    return {
        "active_plan": {
            "commit": ACTIVE_PLAN_COMMIT_V1,
            "sha256": snapshot.active_plan_sha256,
            "registry_sha256": snapshot.active_registry_sha256,
            "admission_receipt_sha256": snapshot.admission_receipt_sha256,
            "admission_receipt_payload_sha256": snapshot.admission_receipt_payload_sha256,
        },
        "implementation": _pin_json(snapshot.implementation),
        "current_tau": _pin_json(snapshot.current_tau),
        "current_tau_lang": _pin_json(snapshot.current_tau_lang),
        "historical_bridge": _pin_json(snapshot.historical_bridge),
    }


def build_current_tau_compatibility_artifact_v1(
    snapshot: CurrentTauCompatibilitySnapshotV1,
) -> dict[str, object]:
    """Return the exact research-only artifact after all source facts validate."""

    _validate_snapshot(snapshot)
    artifact: dict[str, object] = {
        "schema": SCHEMA_V1,
        "status": "REPLAYED_CURRENT_TAU_INCOMPATIBILITY_RESEARCH_ONLY",
        "obligation": {
            "obligation_id": "O-003A",
            "status": "EVIDENCE_COMPLETE_RESEARCH_ONLY",
            "closed_gap_ids": ["current_tau_compatibility_gap"],
        },
        "source_pins": _source_pins_json(snapshot),
        "witnesses": [
            _reserved_stream_witness(snapshot),
            _signature_witness(snapshot),
            _rpc_witness(snapshot),
            _force_test_witness(snapshot),
        ],
        "route_disposition": {
            "current_tau_compatible": False,
            "route_quarantine_implemented": False,
            "next_obligation": "O-002",
        },
        "vm_ledger_contribution": {
            "contributes_to": [],
            "gate_closures": [],
            "status": "NO_VM_GATE_PROMOTION",
        },
        "authority": {
            "production_authority": "NONE",
            "release_authority": "NONE",
            "settlement_authority": "NONE",
            "value_movement_authority": "NONE",
        },
        "replay_command": (
            "python3 tools/check_current_tau_compatibility_v1.py --tau-testnet-repo "
            "<exact-local-current-tau-testnet-clone> --tau-lang-repo "
            "<exact-local-tau-lang-clone> --historical-bridge-repo "
            "<exact-local-historical-bridge-checkout>"
        ),
        "nonclaims": [
            "This evidence does not implement route quarantine or a current-Tau adapter.",
            "This evidence grants no settlement, publication, release, migration, or value-moving authority.",
            "Source compatibility does not establish Tau economic finality.",
            "No value-movement gate or release-evidence cell is promoted.",
        ],
    }
    artifact["artifact_root"] = hashlib.sha256(
        b"zenodex/current-tau-compatibility-root/v1\x00" + canonical_json_bytes(artifact)
    ).hexdigest()
    return artifact


def _pin_json(pin: SourcePinV1) -> dict[str, object]:
    return {
        "commit": pin.commit,
        "tree": pin.tree,
        "tree_listing_sha256": pin.tree_listing_sha256,
        "source_sha256": {path: digest for path, digest in pin.source_sha256},
    }


def check_current_tau_compatibility_artifact_v1(
    artifact: object,
    raw_artifact: bytes,
    snapshot: CurrentTauCompatibilitySnapshotV1,
) -> dict[str, object]:
    """Compare untrusted artifact bytes to the sole pure source projection."""

    expected = canonical_json_bytes(build_current_tau_compatibility_artifact_v1(snapshot))
    observed_sha = hashlib.sha256(raw_artifact).hexdigest()
    if type(artifact) is not dict or raw_artifact != expected:
        return _check_report(
            ok=False,
            artifact_sha256=observed_sha,
            artifact_root=None,
            code="ARTIFACT_BINDING_DRIFT",
        )
    artifact_root = artifact.get("artifact_root")
    if type(artifact_root) is not str:
        return _check_report(
            ok=False,
            artifact_sha256=observed_sha,
            artifact_root=None,
            code="ARTIFACT_ROOT_TYPE",
        )
    return _check_report(
        ok=True,
        artifact_sha256=observed_sha,
        artifact_root=artifact_root,
        code=None,
    )


def _check_report(
    *,
    ok: bool,
    artifact_sha256: str,
    artifact_root: str | None,
    code: str | None,
) -> dict[str, object]:
    findings = [] if code is None else [{"code": code, "path": "artifact"}]
    return {
        "schema": CHECK_SCHEMA_V1,
        "ok": ok,
        "findings": findings,
        "artifact_sha256": artifact_sha256,
        "artifact_root": artifact_root,
        "o003a_evidence_complete": ok,
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
