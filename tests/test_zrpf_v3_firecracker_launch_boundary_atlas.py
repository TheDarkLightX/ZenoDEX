from __future__ import annotations

import hashlib
import sys
from dataclasses import dataclass
from functools import partial
from types import FrameType
from typing import Any, Callable

from tests.test_zrpf_v3_firecracker_candidate_plan import build_intent_document
from tests.test_zrpf_v3_firecracker_runtime_manifest import build_manifest_document
from tools import zrpf_v3_firecracker_candidate_plan as candidate_plan
from tools import zrpf_v3_firecracker_runtime_manifest as runtime


@dataclass(frozen=True)
class ManifestMutation:
    case_id: str
    path: tuple[str, ...]
    replacement: Any
    expected_error: str


MANIFEST_MUTATIONS = (
    ManifestMutation(
        "claim_promotion",
        ("authority", "root_launcher_ready"),
        True,
        "runtime_manifest_authority_mismatch",
    ),
    ManifestMutation(
        "integer_boolean",
        ("boot_contract", "rootfs_read_only"),
        1,
        "runtime_manifest_boot_contract_mismatch",
    ),
    ManifestMutation(
        "profile_rebinding",
        ("firecracker_profile_canonical_sha256",),
        "ab" * 32,
        "runtime_manifest_profile_binding_mismatch",
    ),
    ManifestMutation(
        "kernel_path_traversal",
        ("guest_kernel", "artifact_name"),
        "../vmlinux",
        "runtime_manifest_artifact_name_invalid",
    ),
    ManifestMutation(
        "dynamic_runtime_without_closure",
        ("guest_payload", "runtime_linkage"),
        "dynamic",
        "runtime_manifest_payload_contract_mismatch",
    ),
    ManifestMutation(
        "wrong_rootfs_compression",
        ("rootfs", "compression"),
        "gzip",
        "runtime_manifest_rootfs_geometry_mismatch",
    ),
    ManifestMutation(
        "artifact_set_rebinding",
        ("artifact_set_id",),
        "cd" * 32,
        "runtime_manifest_artifact_set_id_mismatch",
    ),
)


def test_manifest_boundary_atlas_preserves_distinct_reject_paths() -> None:
    signatures: set[tuple[str, str]] = set()
    for mutation in MANIFEST_MUTATIONS:
        document = build_manifest_document()
        _replace(document, mutation.path, mutation.replacement)
        raw = runtime.canonical_document_bytes(document)
        error, path_id = _trace_error(
            partial(runtime.parse_runtime_manifest_bytes, raw),
            runtime.RuntimeManifestError,
            runtime.__file__,
        )

        assert error == mutation.expected_error, mutation.case_id
        signatures.add((error, path_id))

    assert len(signatures) == len(MANIFEST_MUTATIONS)


def test_intent_boundary_atlas_reaches_semantic_rejects() -> None:
    cases = (
        ("unknown_field", ("path",), "/attacker", "candidate_intent_fields_mismatch"),
        (
            "integer_size",
            ("expected_output_payload_size_bytes",),
            True,
            "candidate_intent_output_payload_size_invalid",
        ),
        (
            "zero_digest",
            ("expected_output_payload_sha256",),
            "0" * 64,
            "candidate_intent_digest_invalid",
        ),
        (
            "wrong_schema",
            ("schema",),
            "attacker/v1",
            "candidate_intent_schema_mismatch",
        ),
    )
    signatures: set[tuple[str, str]] = set()
    for case_id, path, replacement, expected in cases:
        document = build_intent_document()
        _replace(document, path, replacement)
        raw = runtime.canonical_document_bytes(document)
        error, path_id = _trace_error(
            partial(candidate_plan.parse_replay_intent_bytes, raw),
            candidate_plan.CandidatePlanError,
            candidate_plan.__file__,
        )
        assert error == expected, case_id
        signatures.add((error, path_id))

    assert len(signatures) == len(cases)


def test_depth_two_mutations_preserve_fail_closed_precedence() -> None:
    manifest = build_manifest_document()
    manifest["authority"]["root_launcher_ready"] = True
    manifest["artifact_set_id"] = "ef" * 32
    error, _ = _trace_error(
        lambda: runtime.parse_runtime_manifest_bytes(runtime.canonical_document_bytes(manifest)),
        runtime.RuntimeManifestError,
        runtime.__file__,
    )
    assert error == "runtime_manifest_authority_mismatch"

    intent = build_intent_document()
    intent["unexpected"] = False
    intent["expected_output_payload_sha256"] = "0" * 64
    intent_error, _ = _trace_error(
        lambda: candidate_plan.parse_replay_intent_bytes(runtime.canonical_document_bytes(intent)),
        candidate_plan.CandidatePlanError,
        candidate_plan.__file__,
    )
    assert intent_error == "candidate_intent_fields_mismatch"


def _replace(document: dict[str, Any], path: tuple[str, ...], value: Any) -> None:
    cursor = document
    for component in path[:-1]:
        child = cursor[component]
        assert isinstance(child, dict)
        cursor = child
    cursor[path[-1]] = value


def _trace_error(
    action: Callable[[], object],
    error_type: type[Exception],
    target_file: str,
) -> tuple[str, str]:
    lines: list[int] = []

    def tracer(frame: FrameType, event: str, _argument: object):
        if event == "line" and frame.f_code.co_filename == target_file:
            lines.append(frame.f_lineno)
        return tracer

    previous = sys.gettrace()
    sys.settrace(tracer)
    try:
        try:
            action()
        except error_type as exc:
            code = str(exc)
        else:
            raise AssertionError("boundary mutation unexpectedly accepted")
    finally:
        sys.settrace(previous)
    path_id = hashlib.sha256(",".join(str(line) for line in lines).encode("ascii")).hexdigest()[:16]
    return code, path_id
