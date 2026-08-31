"""Pure builders for the Stage-A O-008 V2 bounded-core evidence packet.

The packet records a source-pinned wire ABI inventory.  It has no runtime,
release, settlement, verifier, or value-movement authority.
"""

from __future__ import annotations

import ast
import hashlib
import json
import os
import re
import subprocess
from pathlib import Path, PurePosixPath
from typing import Final, NoReturn, cast

SCHEMA_V2: Final = "zenodex/global-settlement-abi-v2/o008-bounded-core-evidence/v2"
STATUS_V2: Final = "BOUNDED_CORE_IMPLEMENTED_DEPENDENCY_BLOCKED"
STAGE_A_PARENT_V2: Final = "f20844d9e4c078df1aa0001104df4378c9467290"
MAX_GIT_BLOB_BYTES_V2: Final = 8 * 1_048_576
PLAN_PATH_V2: Final = "docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V2.json"
PLAN_COMMIT_V2: Final = "c52c71d01a3edf3e298a840d41345abdc2d6d26d"
ADMISSION_PATH_V2: Final = "docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_ADMISSION_V1.json"
ADMISSION_COMMIT_V2: Final = "c0fb36c62b20293ebc54fc530f3dfe2e8046576d"
PLAN_SHA256_V2: Final = "8bbd05a875317fb75e4853f7babc3a91351e581f6d1ec7ed75db0e660ae4542f"
ADMISSION_SHA256_V2: Final = "8d551e10a6a74ce46f39c611fe29960eeb4ef1b05c839702ce8b4779e474b87d"
REGISTRY_PATH_V2: Final = "docs/research/ZENODEX_ACTIVE_WHOLE_PROGRAM_PLAN_V1.json"
REGISTRY_SHA256_V2: Final = "b9996e69d56e179de01f54e1a81b9093ff366de45354fb18768421f57d7913c4"
WIRE_FIXTURE_PATH_V2: Final = "tests/data/global_settlement_abi_v2_wire_records_golden.json"
WIRE_FIXTURE_SHA256_V2: Final = "1355ef7a23f039e9884b720a60c16787350814e84287134194646fae7636b4c8"
V1_TEST_CORRECTION_PATH_V2: Final = (
    "tests/test_check_global_settlement_abi_v2_o008_evidence.py"
)
V1_TEST_CORRECTION_SHA256_V2: Final = (
    "08e8786979945fcee221e806070cb6f24d9b5f7f16d1ede68a0a2033f7a7aee5"
)

WIRE_RECORD_FIELDS_V2: Final[dict[str, tuple[str, ...]]] = {
    "GlobalAccepted": ("witness", "production_authority"),
    "GlobalRejected": ("reject_code", "pre_state_root", "post_state_root", "effect_plan", "terminal_plan", "oracle_plan", "consumed_occurrences", "outbox", "production_authority"),
    "ManagedAccepted": ("post_state", "effects", "module_journal", "receipt_root", "production_authority"),
    "ManagedRejected": ("code", "pre_state_root", "post_state_root", "effects", "terminal_obligations_root", "oracle_occurrence_plan_root", "production_authority"),
    "OriginAccepted": ("post_state", "effects", "module_journal", "production_authority"),
    "OriginRejected": ("code", "pre_state_root", "post_state_root", "effects"),
    "LaneContext": ("writer_epoch", "module_release_id", "global_pre_state_root", "occurrence"),
    "LaneAccepted": ("route", "source_leaf_journal_root", "post_state", "effects", "module_journal", "receipt_root", "production_authority", "profile_authentication"),
    "LaneRejected": ("route", "code", "pre_state_root", "post_state_root", "effects", "production_authority", "profile_authentication"),
    "Candidate": ("pre_state", "post_state", "effect_plan", "consumed_occurrences", "terminal_plan", "oracle_plan"),
    "Refinement": ("pre_state_root", "post_state_root", "effect_plan_root", "terminal_plan_root", "oracle_plan_root", "state_delta_root", "production_authority", "refinement_root"),
}

_RECORD_CLASS_NAMES: Final[dict[str, str]] = {
    "GlobalAccepted": "GlobalEconomicRefinementAcceptedWireV2",
    "GlobalRejected": "GlobalEconomicRefinementRejectedWireV2",
    "ManagedAccepted": "ManagedAssetLifecycleAcceptedWireV2",
    "ManagedRejected": "ManagedAssetLifecycleRejectedWireV2",
    "OriginAccepted": "AssetOriginRegistrationAcceptedWireV2",
    "OriginRejected": "AssetOriginRegistrationRejectedWireV2",
    "LaneContext": "AssetLaneContextWireV2",
    "LaneAccepted": "AssetLaneAcceptedWireV2",
    "LaneRejected": "AssetLaneRejectedWireV2",
    "Candidate": "GlobalEconomicStateEffectRefinementCandidateWireV2",
    "Refinement": "GlobalEconomicStateEffectRefinementWireV2",
}

STAGE_A_WRITE_SET_V2: Final[tuple[tuple[str, str], ...]] = (
    ("M", "lean-mathlib/Proofs/GlobalEconomicStateRefinementV2.lean"),
    ("M", "lean-mathlib/Proofs/GlobalEconomicStateRefinementV2Nonempty.lean"),
    ("M", "src/core/asset_lane_state_v2.py"),
    ("M", "src/core/asset_origin_registry_types_v2.py"),
    ("M", "src/core/asset_transfer_types_v2.py"),
    ("M", "src/core/global_economic_proof_v2.py"),
    ("M", "src/core/global_economic_refinement_checks_v2.py"),
    ("M", "src/core/global_economic_refinement_outcome_v2.py"),
    ("M", "src/core/global_economic_state_effect_refinement_v2.py"),
    ("A", "src/core/global_settlement_resource_limits_v2.py"),
    ("M", "src/core/global_settlement_types_v2.py"),
    ("A", "src/core/global_settlement_wire_codec_v2.py"),
    ("A", "src/core/global_settlement_wire_records_v2.py"),
    ("M", "src/core/managed_asset_lifecycle_state_v2.py"),
    ("M", "tests/core/test_global_economic_refinement_outcome_v2.py"),
    ("M", "tests/core/test_global_economic_state_effect_refinement_v2.py"),
    ("A", "tests/core/test_global_settlement_abi_v2_resource_bounds.py"),
    ("A", "tests/core/test_global_settlement_abi_v2_wire_records.py"),
    ("M", "tests/data/global_settlement_abi_v2_asset_lane_coordinator_golden.json"),
    ("M", "tests/data/global_settlement_abi_v2_asset_origin_golden.json"),
    ("M", "tests/data/global_settlement_abi_v2_global_core_golden.json"),
    ("M", "tests/data/global_settlement_abi_v2_managed_asset_golden.json"),
    ("A", WIRE_FIXTURE_PATH_V2),
    ("A", "tests/evidence/test_hygiene/THV1-20260831-o008-v2-bounded-core-evidence-v2.json"),
    ("M", "tests/formal/test_lean_asset_lane_refinement_v2.py"),
    ("M", "tests/formal/test_lean_asset_origin_registry_refinement_v2.py"),
    ("M", "tests/formal/test_lean_global_economic_refinement_outcome_v2.py"),
    ("M", "tests/formal/test_lean_global_economic_state_nonempty_v2.py"),
    ("M", "tests/formal/test_lean_global_settlement_core_v2.py"),
    ("M", "tests/test_check_global_settlement_abi_v2_o008_evidence.py"),
    ("A", "tests/test_global_settlement_abi_v2_o008_evidence_v2.py"),
    ("A", "tools/build_global_settlement_abi_v2_o008_evidence_v2.py"),
    ("A", "tools/check_global_settlement_abi_v2_o008_evidence_v2.py"),
    ("A", "tools/global_settlement_abi_v2_o008_evidence_v2.py"),
    ("M", "tools/render_global_settlement_abi_v2_global_core_golden.py"),
    ("A", "tools/render_global_settlement_abi_v2_wire_records_golden.py"),
    ("M", "zk/global_settlement_abi_v2/src/asset_lane_coordinator_types.rs"),
    ("M", "zk/global_settlement_abi_v2/src/asset_lane_state.rs"),
    ("M", "zk/global_settlement_abi_v2/src/asset_origin_registry_types.rs"),
    ("M", "zk/global_settlement_abi_v2/src/asset_transfer_types.rs"),
    ("M", "zk/global_settlement_abi_v2/src/effects.rs"),
    ("M", "zk/global_settlement_abi_v2/src/global_refinement.rs"),
    ("M", "zk/global_settlement_abi_v2/src/global_refinement_checks.rs"),
    ("M", "zk/global_settlement_abi_v2/src/lib.rs"),
    ("M", "zk/global_settlement_abi_v2/src/managed_asset_lifecycle_types.rs"),
    ("M", "zk/global_settlement_abi_v2/src/outcome.rs"),
    ("M", "zk/global_settlement_abi_v2/src/proof.rs"),
    ("A", "zk/global_settlement_abi_v2/src/resource_limits.rs"),
    ("A", "zk/global_settlement_abi_v2/src/wire_records.rs"),
    ("M", "zk/global_settlement_abi_v2/tests/global_refinement.rs"),
    ("M", "zk/global_settlement_abi_v2/tests/outcome.rs"),
    ("A", "zk/global_settlement_abi_v2/tests/resource_bounds.rs"),
    ("A", "zk/global_settlement_abi_v2/tests/wire_records_golden.rs"),
)
SOURCE_PATHS_V2: Final[tuple[str, ...]] = tuple(
    path for _status, path in STAGE_A_WRITE_SET_V2
)
HISTORICAL_V1_PATHS_V2: Final[tuple[str, ...]] = (
    "docs/research/GLOBAL_SETTLEMENT_ABI_V2_O008_BOUNDED_CORE_EVIDENCE_20260831.json",
    "docs/research/GLOBAL_SETTLEMENT_ABI_V2_O008_BOUNDED_CORE_EVIDENCE_20260831.md",
    "tools/check_global_settlement_abi_v2_o008_evidence.py",
)
DEPENDENCY_EXPECTATIONS_V2: Final[dict[str, dict[str, str]]] = {
    "O-006": {
        "path": "docs/research/M6_O006_COMMAND_LANE_COMPLETION_V2.json",
        "schema": "zenodex/m6-o006-command-lane-completion/v2",
        "sha256": "a78b187269264e37c2f18b896a90c4ebd6d50ebe66921749e3991a4d29e15988",
        "status": "RESEARCH_ONLY_O006_EXACT_COMMAND_MAP",
        "certificate_root": "fb69388e585b3408ffae3adc3976d9a9135758d9df2867513548fd71cb2b4f8e",
    },
    "O-007B": {
        "path": "docs/research/ZENODEX_O007B_CROSS_LANGUAGE_SINK_CLOSURE_V3.json",
        "schema": "zenodex/o007b-cross-language-sink-closure/v3",
        "sha256": "78588789509ecd00253ee4cb116a36e499851410966346fc726bfdbc9b07d88d",
        "status": "RESEARCH_ONLY_O007B_V3_CURRENT_SUBJECT_NO_VM_GATE",
        "certificate_root": "08d42e131097532aac17d5bd0c71c3f0b96d5c21c85799b3c7f7c57b572b7e98",
    },
    "O-007C": {
        "path": "docs/research/ZENODEX_O007C_INDIRECT_SINK_CLOSURE_V1.json",
        "schema": "zenodex/o007c-indirect-sink-closure/v1",
        "sha256": "365fa9111f5a69f0d000f2240f1890c68fd3bb4cfc32fb87fbb440f159dae075",
        "status": "RESEARCH_ONLY_O007C_V1_NO_VM_GATE",
        "certificate_root": "6786074bf4ab439aa99cad452324aedea7ca0cddf158ceb95adbdd6f618d6953",
    },
    "O-008A": {
        "path": "docs/research/ZENODEX_O008A_DEPENDENCY_POLICY_BLOCKER_V1.json",
        "schema": "zenodex/o008a-dependency-policy-blocker/v1",
        "sha256": "adea8492d5aa6f3369b202217f7b1baeb0961e3bf07b46594af0620e22cf2bfe",
        "status": "BLOCKED_DEPENDENCY_POLICY_CONFLICT",
        "certificate_root": "059d896a9b7c6b480d5289103f31003d30ce51f8449fcbca5b388f239d42289d",
    },
}
RESOURCE_LIMITS_V2: Final[dict[str, int]] = {
    "assets": 256,
    "balances": 4096,
    "rootable_asset_state_bytes": 1_048_576,
    "object_ids": 64,
    "refinement_occurrences": 64,
    "wire_transport_bytes": 1_048_576,
}
FIELD_PROFILES_V2: Final[dict[str, dict[str, object]]] = {
    "u8_decimals_fixed_8": {"value": 8, "scope": "AssetOriginRecordV2.decimals"},
    "u64_decimals_fixed_8": {"value": 8, "scope": "asset policy atom_decimals"},
    "u64_decimals_transition_guarded_8": {"value": 8, "scope": "managed/origin transition atom_decimals"},
    "profile_authentication_shadow": {"value": "SHADOW", "scope": "LaneAccepted,LaneRejected"},
    "bounded_candidate_records_max_64": {"value": 64, "scope": "Candidate,GlobalRejected consumed_occurrences"},
    "ordered_tokens_max_64": {"value": 64, "scope": "EconomicCommandOccurrenceV2.consumed_object_ids"},
}
AUTHORITY_V2: Final[dict[str, str]] = {
    "production": "NONE",
    "release": "NONE",
    "settlement": "NONE",
    "value_movement": "NONE",
    "verifier": "NONE",
    "profile": "SHADOW",
}
NONCLAIMS_V2: Final[tuple[str, ...]] = (
    "O-008 remains open and dependency-blocked while O-008A remains open.",
    "The bounded core does not establish per-lane economic attribution or effect provenance.",
    "The bounded core does not establish claimant-to-custody-principal allocation.",
    "The bounded core does not establish fee-residue ownership or disposition.",
    "The packet does not establish qualified Rust execution parity.",
    "The packet does not establish a proof guest or proof journal.",
    "The packet does not establish a runtime mount.",
    "A later O-007C artifact refresh is excluded from O-008 source applicability and must pass the independent O-007C checker.",
    "The packet grants no production, release, settlement, verifier, or value-movement authority.",
    "No value-movement gate is closed.",
)
_HEX40_RE: Final = re.compile(r"[0-9a-f]{40}")


class EvidenceV2Error(ValueError):
    """A malformed subject, source, or evidence packet."""


def _reject_float_v2(value: str) -> NoReturn:
    raise EvidenceV2Error(f"floating-point JSON number is forbidden: {value}")


def _reject_constant_v2(value: str) -> NoReturn:
    raise EvidenceV2Error(f"non-finite JSON number is forbidden: {value}")


def _closed_object_v2(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise EvidenceV2Error(f"duplicate JSON field: {key}")
        result[key] = value
    return result


def _validate_json_value_v2(value: object, *, context: str = "$") -> None:
    if value is None or type(value) in {bool, int, str}:
        return
    if type(value) is list:
        for index, item in enumerate(cast(list[object], value)):
            _validate_json_value_v2(item, context=f"{context}[{index}]")
        return
    if type(value) is dict:
        for key, item in cast(dict[object, object], value).items():
            if type(key) is not str:
                raise EvidenceV2Error(f"{context}: JSON object key is not a string")
            _validate_json_value_v2(item, context=f"{context}.{key}")
        return
    raise EvidenceV2Error(
        f"{context}: unsupported JSON value type {type(value).__name__}"
    )


def canonical_json_bytes_v2(value: object) -> bytes:
    """Return the one accepted evidence encoding, including a final newline."""

    _validate_json_value_v2(value)
    return (
        json.dumps(
            value,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
            allow_nan=False,
        )
        + "\n"
    ).encode("ascii")


def canonical_value_bytes_v2(value: object) -> bytes:
    """Match production canonical global bytes: compact ASCII, no newline."""

    _validate_json_value_v2(value)
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
        allow_nan=False,
    ).encode("ascii")


def decode_json_object_v2(
    raw: bytes, *, context: str, require_canonical: bool
) -> dict[str, object]:
    if len(raw) > MAX_GIT_BLOB_BYTES_V2:
        raise EvidenceV2Error(f"{context}: JSON input exceeds byte ceiling")
    try:
        value = json.loads(
            raw.decode("utf-8"),
            object_pairs_hook=_closed_object_v2,
            parse_float=_reject_float_v2,
            parse_constant=_reject_constant_v2,
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise EvidenceV2Error(
            f"{context}: malformed JSON: {type(exc).__name__}"
        ) from exc
    if type(value) is not dict:
        raise EvidenceV2Error(f"{context}: expected a JSON object")
    result = cast(dict[str, object], value)
    _validate_json_value_v2(result)
    if require_canonical and raw != canonical_json_bytes_v2(result):
        raise EvidenceV2Error(f"{context}: noncanonical JSON encoding")
    return result


def sha256_bytes_v2(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _safe_repo_path_v2(path: str) -> None:
    pure = PurePosixPath(path)
    if (
        not path
        or pure.is_absolute()
        or "." in pure.parts
        or ".." in pure.parts
        or "\\" in path
    ):
        raise EvidenceV2Error(f"unsafe repository path: {path}")


def _git_v2(root: Path, *args: str) -> bytes:
    env = os.environ.copy()
    env.update({"GIT_NO_LAZY_FETCH": "1", "GIT_LITERAL_PATHSPECS": "1"})
    try:
        return subprocess.run(
            ("git", "--no-replace-objects", *args),
            cwd=root,
            env=env,
            stdin=subprocess.DEVNULL,
            check=True,
            capture_output=True,
            timeout=20,
        ).stdout
    except (OSError, subprocess.SubprocessError) as exc:
        raise EvidenceV2Error(f"git command failed: {' '.join(args)}: {type(exc).__name__}") from exc


def resolve_repo_root_v2(root: Path) -> Path:
    if not root.is_absolute():
        raise EvidenceV2Error("--root must be an explicit absolute path")
    try:
        resolved = root.resolve(strict=True)
    except OSError as exc:
        raise EvidenceV2Error(
            f"repository root cannot be resolved: {type(exc).__name__}"
        ) from exc
    if not resolved.is_dir():
        raise EvidenceV2Error("repository root is not a directory")
    try:
        top = Path(
            _git_v2(resolved, "rev-parse", "--show-toplevel")
            .decode("utf-8")
            .strip()
        ).resolve(strict=True)
    except (OSError, UnicodeDecodeError) as exc:
        raise EvidenceV2Error(
            f"Git top-level cannot be resolved: {type(exc).__name__}"
        ) from exc
    if top != resolved:
        raise EvidenceV2Error("--root must equal the explicit Git top-level")
    return resolved


def _validate_commit_v2(root: Path, commit: str, *, context: str) -> None:
    if _HEX40_RE.fullmatch(commit) is None:
        raise EvidenceV2Error(f"{context} must be one full lowercase commit hash")
    actual = (
        _git_v2(root, "rev-parse", "--verify", f"{commit}^{{commit}}")
        .decode("ascii")
        .strip()
    )
    if actual != commit:
        raise EvidenceV2Error(f"{context} does not resolve to its exact hash")


def _tree_entry_v2(root: Path, commit: str, path: str) -> tuple[str, str, int]:
    _safe_repo_path_v2(path)
    raw = _git_v2(root, "ls-tree", "-z", "--full-tree", commit, "--", path)
    rows = [row for row in raw.split(b"\0") if row]
    if len(rows) != 1 or b"\t" not in rows[0]:
        raise EvidenceV2Error(f"subject path is missing or ambiguous: {path}")
    metadata, raw_path = rows[0].split(b"\t", 1)
    try:
        actual_path = raw_path.decode("utf-8")
        mode, object_type, git_blob = metadata.decode("ascii").split(" ")
    except (UnicodeDecodeError, ValueError) as exc:
        raise EvidenceV2Error(f"malformed Git tree entry: {path}") from exc
    if (
        actual_path != path
        or mode != "100644"
        or object_type != "blob"
        or _HEX40_RE.fullmatch(git_blob) is None
    ):
        raise EvidenceV2Error(f"subject path is not an exact 100644 blob: {path}")
    try:
        size = int(
            _git_v2(root, "cat-file", "-s", git_blob).decode("ascii").strip()
        )
    except (UnicodeDecodeError, ValueError) as exc:
        raise EvidenceV2Error(f"malformed Git blob size: {path}") from exc
    if size < 0 or size > MAX_GIT_BLOB_BYTES_V2:
        raise EvidenceV2Error(f"Git blob exceeds byte ceiling: {path}")
    return mode, git_blob, size


def _blob_v2(root: Path, commit: str, path: str) -> tuple[bytes, str, int]:
    _mode, git_blob, size = _tree_entry_v2(root, commit, path)
    blob = _git_v2(root, "cat-file", "blob", git_blob)
    if len(blob) != size:
        raise EvidenceV2Error(f"Git blob size changed while reading: {path}")
    return blob, git_blob, size


def _stage_topology_v2(root: Path, commit: str) -> list[dict[str, str]]:
    parents = (
        _git_v2(root, "rev-list", "--parents", "-n", "1", commit)
        .decode("ascii")
        .split()
    )
    if parents != [commit, STAGE_A_PARENT_V2]:
        raise EvidenceV2Error(f"Stage-A parent topology drift: {parents[1:]}")
    raw = _git_v2(
        root,
        "diff-tree",
        "--no-commit-id",
        "--name-status",
        "--no-renames",
        "-r",
        "-z",
        STAGE_A_PARENT_V2,
        commit,
    )
    parts = [part for part in raw.split(b"\0") if part]
    if len(parts) % 2:
        raise EvidenceV2Error("malformed Stage-A name-status output")
    actual: list[tuple[str, str]] = []
    for index in range(0, len(parts), 2):
        try:
            status = parts[index].decode("ascii")
            path = parts[index + 1].decode("utf-8")
        except UnicodeDecodeError as exc:
            raise EvidenceV2Error("non-UTF-8 Stage-A topology") from exc
        _safe_repo_path_v2(path)
        actual.append((status, path))
    actual_tuple = tuple(sorted(actual, key=lambda item: item[1]))
    expected_tuple = tuple(sorted(STAGE_A_WRITE_SET_V2, key=lambda item: item[1]))
    if actual_tuple != expected_tuple:
        raise EvidenceV2Error(
            f"Stage-A write-set drift: expected {expected_tuple!r}, got {actual_tuple!r}"
        )
    return [{"status": status, "path": path} for status, path in actual_tuple]


def _class_contracts_v2(
    source: bytes,
) -> tuple[dict[str, tuple[int, tuple[str, ...]]], tuple[str, ...]]:
    try:
        parsed = ast.parse(source.decode("utf-8"))
    except (UnicodeDecodeError, SyntaxError) as exc:
        raise EvidenceV2Error(
            f"wire record source is not parseable: {type(exc).__name__}"
        ) from exc
    extracted: dict[str, tuple[int, tuple[str, ...]]] = {}
    conversions: list[str] = []
    for node in parsed.body:
        if isinstance(node, ast.ClassDef):
            fields = tuple(
                item.target.id
                for item in node.body
                if isinstance(item, ast.AnnAssign)
                and isinstance(item.target, ast.Name)
            )
            if fields:
                extracted[node.name] = (node.lineno, fields)
            if any(
                isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef))
                and item.name == "to_domain_v2"
                for item in node.body
            ):
                conversions.append(node.name)
    return extracted, tuple(conversions)


def _require_candidate_order_preserved_v2(source: bytes) -> None:
    """Require the wire candidate to pass its supplied occurrence order through."""

    try:
        parsed = ast.parse(source.decode("utf-8"))
    except (UnicodeDecodeError, SyntaxError) as exc:
        raise EvidenceV2Error(
            f"wire record source is not parseable: {type(exc).__name__}"
        ) from exc
    candidate = next(
        (
            node
            for node in parsed.body
            if isinstance(node, ast.ClassDef)
            and node.name == "GlobalEconomicStateEffectRefinementCandidateWireV2"
        ),
        None,
    )
    if candidate is None:
        raise EvidenceV2Error("candidate wire class is absent")
    if any(
        isinstance(node, ast.Name) and node.id in {"sorted", "set", "frozenset"}
        for node in ast.walk(candidate)
    ):
        raise EvidenceV2Error("candidate wire occurrence order is canonicalized")
    stores_supplied_order = any(
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and isinstance(node.func.value, ast.Name)
        and node.func.value.id == "object"
        and node.func.attr == "__setattr__"
        and len(node.args) == 3
        and isinstance(node.args[1], ast.Constant)
        and node.args[1].value == "consumed_occurrences"
        and isinstance(node.args[2], ast.Name)
        and node.args[2].id == "occurrences"
        for node in ast.walk(candidate)
    )
    passes_stored_order = any(
        isinstance(node, ast.Return)
        and isinstance(node.value, ast.Call)
        and len(node.value.args) >= 4
        and isinstance(node.value.args[3], ast.Attribute)
        and isinstance(node.value.args[3].value, ast.Name)
        and node.value.args[3].value.id == "self"
        and node.value.args[3].attr == "consumed_occurrences"
        for node in ast.walk(candidate)
    )
    if not stores_supplied_order or not passes_stored_order:
        raise EvidenceV2Error("candidate wire supplied-order contract drift")


def _integer_constants_v2(source: bytes, *, context: str) -> dict[str, int]:
    try:
        parsed = ast.parse(source.decode("utf-8"))
    except (UnicodeDecodeError, SyntaxError) as exc:
        raise EvidenceV2Error(
            f"{context} source is not parseable: {type(exc).__name__}"
        ) from exc
    values: dict[str, int] = {}
    for node in parsed.body:
        if (
            isinstance(node, ast.AnnAssign)
            and isinstance(node.target, ast.Name)
            and isinstance(node.value, ast.Constant)
            and type(node.value.value) is int
        ):
            values[node.target.id] = node.value.value
    return values


def _string_constants_v2(source: bytes, *, context: str) -> dict[str, str]:
    try:
        parsed = ast.parse(source.decode("utf-8"))
    except (UnicodeDecodeError, SyntaxError) as exc:
        raise EvidenceV2Error(
            f"{context} source is not parseable: {type(exc).__name__}"
        ) from exc
    values: dict[str, str] = {}
    for node in parsed.body:
        if (
            isinstance(node, ast.AnnAssign)
            and isinstance(node.target, ast.Name)
            and isinstance(node.value, ast.Constant)
            and type(node.value.value) is str
        ):
            values[node.target.id] = node.value.value
    return values


def _limits_v2(root: Path, commit: str) -> dict[str, int]:
    values = _integer_constants_v2(
        _blob_v2(
            root, commit, "src/core/global_settlement_resource_limits_v2.py"
        )[0],
        context="resource limit",
    )
    codec = _integer_constants_v2(
        _blob_v2(root, commit, "src/core/global_settlement_wire_codec_v2.py")[0],
        context="wire codec",
    )
    actual = {
        "assets": values.get("MAX_ASSETS_PER_ASSET_STATE_V2"),
        "balances": values.get("MAX_BALANCE_ROWS_PER_ASSET_STATE_V2"),
        "rootable_asset_state_bytes": values.get("MAX_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2"),
        "object_ids": values.get("MAX_CONSUMED_OBJECT_IDS_PER_OCCURRENCE_V2"),
        "refinement_occurrences": values.get("MAX_CONSUMED_OCCURRENCES_PER_REFINEMENT_V2"),
        "wire_transport_bytes": codec.get(
            "MAX_GLOBAL_SETTLEMENT_WIRE_RECORD_CODEC_BYTES_V2"
        ),
    }
    if actual != RESOURCE_LIMITS_V2:
        raise EvidenceV2Error(f"resource limit drift: {actual}")
    return RESOURCE_LIMITS_V2.copy()


def _field_profiles_v2(root: Path, commit: str) -> dict[str, dict[str, object]]:
    transfer = _integer_constants_v2(
        _blob_v2(root, commit, "src/core/asset_transfer_types_v2.py")[0],
        context="asset transfer",
    )
    lane = _string_constants_v2(
        _blob_v2(root, commit, "src/core/asset_lane_state_v2.py")[0],
        context="asset lane",
    )
    if transfer.get("ASSET_ATOM_DECIMALS_V2") != 8:
        raise EvidenceV2Error("asset atom decimal profile drift")
    if lane.get("ASSET_LANE_PROFILE_AUTHENTICATION_V2") != "SHADOW":
        raise EvidenceV2Error("asset lane authentication profile drift")
    return {key: value.copy() for key, value in FIELD_PROFILES_V2.items()}


def _expect_exact_v2(actual: object, expected: object, *, context: str) -> None:
    if type(actual) is not type(expected) or actual != expected:
        raise EvidenceV2Error(f"{context} drift")


def _object_v2(value: object, *, context: str) -> dict[str, object]:
    if type(value) is not dict:
        raise EvidenceV2Error(f"{context}: expected object")
    return cast(dict[str, object], value)


def _dependency_v2(root: Path, commit: str, obligation: str) -> dict[str, str]:
    expected = DEPENDENCY_EXPECTATIONS_V2[obligation]
    blob = _blob_v2(root, commit, expected["path"])[0]
    _expect_exact_v2(
        sha256_bytes_v2(blob), expected["sha256"], context=f"{obligation} SHA-256"
    )
    value = decode_json_object_v2(
        blob, context=expected["path"], require_canonical=False
    )
    _expect_exact_v2(
        value.get("schema"), expected["schema"], context=f"{obligation} schema"
    )
    status = value.get("status")
    if obligation in {"O-007B", "O-007C"}:
        status = _object_v2(
            value.get("obligation"), context=f"{obligation} obligation"
        ).get("status")
    _expect_exact_v2(status, expected["status"], context=f"{obligation} status")
    _expect_exact_v2(
        value.get("certificate_root"),
        expected["certificate_root"],
        context=f"{obligation} certificate root",
    )
    claim = _object_v2(
        value.get("claim_ceiling"), context=f"{obligation} claim ceiling"
    )
    if obligation in {"O-006", "O-007B", "O-007C"}:
        for field in (
            "production_authority",
            "release_authority",
            "settlement_authority",
            "value_movement_authority",
            "verifier_authority",
        ):
            _expect_exact_v2(
                claim.get(field), "NONE", context=f"{obligation} {field}"
            )
        _expect_exact_v2(
            claim.get("closed_value_movement_gates"),
            0,
            context=f"{obligation} closed gates",
        )
        release_field = "release_backed" if obligation == "O-006" else "release_ready"
        _expect_exact_v2(
            claim.get(release_field),
            False,
            context=f"{obligation} release ceiling",
        )
    else:
        authority = _object_v2(claim.get("authority"), context="O-008A authority")
        for field in (
            "production_authority",
            "release_authority",
            "settlement_authority",
            "value_movement_authority",
            "verifier_authority",
        ):
            _expect_exact_v2(
                authority.get(field), "NONE", context=f"O-008A {field}"
            )
        _expect_exact_v2(
            claim.get("release_ready"), False, context="O-008A release ceiling"
        )
        _expect_exact_v2(
            claim.get("dependency_safe"),
            False,
            context="O-008A dependency ceiling",
        )
    return expected.copy()


def _active_plan_v2(root: Path, commit: str) -> dict[str, dict[str, str]]:
    bindings: dict[str, tuple[str, str, str | None]] = {
        "plan": (PLAN_PATH_V2, PLAN_SHA256_V2, PLAN_COMMIT_V2),
        "admission": (
            ADMISSION_PATH_V2,
            ADMISSION_SHA256_V2,
            ADMISSION_COMMIT_V2,
        ),
        "registry": (REGISTRY_PATH_V2, REGISTRY_SHA256_V2, None),
    }
    decoded: dict[str, dict[str, object]] = {}
    result: dict[str, dict[str, str]] = {}
    for label, (path, digest, provenance_commit) in bindings.items():
        blob = _blob_v2(root, commit, path)[0]
        _expect_exact_v2(
            sha256_bytes_v2(blob), digest, context=f"active {label} SHA-256"
        )
        if provenance_commit is not None:
            _validate_commit_v2(
                root, provenance_commit, context=f"active {label} commit"
            )
            provenance_blob = _blob_v2(root, provenance_commit, path)[0]
            _expect_exact_v2(
                sha256_bytes_v2(provenance_blob),
                digest,
                context=f"active {label} provenance SHA-256",
            )
        decoded[label] = decode_json_object_v2(
            blob, context=path, require_canonical=False
        )
        row = {"path": path, "sha256": digest}
        if provenance_commit is not None:
            row["commit"] = provenance_commit
        result[label] = row

    plan = decoded["plan"]
    _expect_exact_v2(
        plan.get("schema"), "zenodex/whole-program-plan/v2.1", context="plan schema"
    )
    _expect_exact_v2(
        plan.get("status"),
        "RESEARCH_ONLY_CANDIDATE_PENDING_ADMISSION",
        context="plan status",
    )
    plan_authority = _object_v2(plan.get("authority"), context="plan authority")
    _expect_exact_v2(
        plan_authority.get("production_authority"),
        "NONE",
        context="plan production authority",
    )
    _expect_exact_v2(
        plan_authority.get("settlement_authority"),
        "NONE",
        context="plan settlement authority",
    )
    _expect_exact_v2(
        plan_authority.get("release_ready"),
        False,
        context="plan release readiness",
    )

    admission = decoded["admission"]
    _expect_exact_v2(
        admission.get("schema"),
        "zenodex/plan-admission-receipt/v1",
        context="admission schema",
    )
    _expect_exact_v2(
        admission.get("status"),
        "ADMITTED_RESEARCH_IMPLEMENTATION_PLAN",
        context="admission status",
    )
    admitted = _object_v2(admission.get("admitted_plan"), context="admitted plan")
    _expect_exact_v2(
        admitted.get("commit"), PLAN_COMMIT_V2, context="admitted plan commit"
    )
    _expect_exact_v2(
        admitted.get("plan_path"), PLAN_PATH_V2, context="admitted plan path"
    )
    _expect_exact_v2(
        admitted.get("plan_sha256"),
        PLAN_SHA256_V2,
        context="admitted plan SHA-256",
    )
    for field, value in _object_v2(
        admission.get("authority"), context="admission authority"
    ).items():
        _expect_exact_v2(value, "NONE", context=f"admission {field}")

    registry = decoded["registry"]
    _expect_exact_v2(
        registry.get("schema"),
        "zenodex/active-whole-program-plan-registry/v1",
        context="registry schema",
    )
    _expect_exact_v2(registry.get("status"), "RESEARCH_ONLY", context="registry status")
    _expect_exact_v2(
        registry.get("active_plan_count"), 1, context="active plan count"
    )
    active_plans = registry.get("active_plans")
    if type(active_plans) is not list or len(active_plans) != 1:
        raise EvidenceV2Error("registry active plans drift")
    active = _object_v2(active_plans[0], context="registry active plan")
    _expect_exact_v2(
        active.get("plan_commit"), PLAN_COMMIT_V2, context="registry plan commit"
    )
    _expect_exact_v2(
        active.get("plan_path"), PLAN_PATH_V2, context="registry plan path"
    )
    _expect_exact_v2(
        active.get("plan_sha256"),
        PLAN_SHA256_V2,
        context="registry plan SHA-256",
    )
    _expect_exact_v2(
        active.get("admission_receipt_path"),
        ADMISSION_PATH_V2,
        context="registry admission path",
    )
    for field, value in _object_v2(
        registry.get("authority"), context="registry authority"
    ).items():
        _expect_exact_v2(value, "NONE", context=f"registry {field}")
    return result


def _manifest_row_v2(
    root: Path, commit: str, status: str, path: str
) -> dict[str, object]:
    blob, git_blob, size = _blob_v2(root, commit, path)
    return {
        "status": status,
        "path": path,
        "mode": "100644",
        "git_blob": git_blob,
        "sha256": sha256_bytes_v2(blob),
        "size": size,
    }


def build_evidence_v2(root: Path, stage_a_commit: str) -> dict[str, object]:
    """Extract one closed Stage-A packet from exact, bounded Git blobs."""

    root = resolve_repo_root_v2(root)
    _validate_commit_v2(root, stage_a_commit, context="Stage-A subject")
    write_set = _stage_topology_v2(root, stage_a_commit)
    source_manifest = [
        _manifest_row_v2(root, stage_a_commit, status, path)
        for status, path in sorted(STAGE_A_WRITE_SET_V2, key=lambda item: item[1])
    ]

    wire_source = _blob_v2(
        root, stage_a_commit, "src/core/global_settlement_wire_records_v2.py"
    )[0]
    _require_candidate_order_preserved_v2(wire_source)
    classes, conversions = _class_contracts_v2(wire_source)
    expected_conversions = (
        "AssetLaneContextWireV2",
        "GlobalEconomicStateEffectRefinementCandidateWireV2",
    )
    if conversions != expected_conversions:
        raise EvidenceV2Error(
            f"wire-to-domain conversion surface drift: {conversions}"
        )
    records: list[dict[str, object]] = []
    for label, expected_fields in WIRE_RECORD_FIELDS_V2.items():
        class_name = _RECORD_CLASS_NAMES[label]
        extracted = classes.get(class_name)
        if extracted is None or extracted[1] != expected_fields:
            raise EvidenceV2Error(f"wire DTO field drift: {label}")
        records.append(
            {
                "dto": label,
                "class": class_name,
                "source_line": extracted[0],
                "fields": list(extracted[1]),
            }
        )

    fixture_blob = _blob_v2(root, stage_a_commit, WIRE_FIXTURE_PATH_V2)[0]
    _expect_exact_v2(
        sha256_bytes_v2(fixture_blob),
        WIRE_FIXTURE_SHA256_V2,
        context="wire fixture whole-file SHA-256",
    )
    fixture = decode_json_object_v2(
        fixture_blob, context=WIRE_FIXTURE_PATH_V2, require_canonical=False
    )
    fixture_records = fixture.get("records")
    if (
        type(fixture_records) is not dict
        or set(fixture_records) != set(_RECORD_CLASS_NAMES.values())
    ):
        raise EvidenceV2Error("wire fixture record parity drift")
    per_record_sha256: dict[str, str] = {}
    record_map = cast(dict[str, object], fixture_records)
    for class_name in sorted(record_map):
        row = _object_v2(record_map[class_name], context=f"fixture {class_name}")
        if set(row) != {"canonical", "canonical_bytes_sha256"}:
            raise EvidenceV2Error(f"wire fixture row field drift: {class_name}")
        canonical = _object_v2(
            row.get("canonical"), context=f"fixture {class_name} canonical"
        )
        computed = sha256_bytes_v2(canonical_value_bytes_v2(canonical))
        _expect_exact_v2(
            row.get("canonical_bytes_sha256"),
            computed,
            context=f"fixture {class_name} canonical byte SHA-256",
        )
        per_record_sha256[class_name] = computed

    historical: dict[str, dict[str, object]] = {}
    for path in HISTORICAL_V1_PATHS_V2:
        blob, git_blob, size = _blob_v2(root, stage_a_commit, path)
        parent_blob, parent_git_blob, _parent_size = _blob_v2(
            root, STAGE_A_PARENT_V2, path
        )
        if blob != parent_blob or git_blob != parent_git_blob:
            raise EvidenceV2Error(f"historical V1 byte preservation drift: {path}")
        historical[path] = {
            "mode": "100644",
            "git_blob": git_blob,
            "sha256": sha256_bytes_v2(blob),
            "size": size,
        }
    v1_test_blob = _blob_v2(root, stage_a_commit, V1_TEST_CORRECTION_PATH_V2)[0]
    _expect_exact_v2(
        sha256_bytes_v2(v1_test_blob),
        V1_TEST_CORRECTION_SHA256_V2,
        context="allowed V1 sorted-union test correction",
    )
    dependencies = {
        key: _dependency_v2(root, stage_a_commit, key)
        for key in DEPENDENCY_EXPECTATIONS_V2
    }
    active_plan = _active_plan_v2(root, stage_a_commit)
    current_applicability_paths = sorted(
        {
            *SOURCE_PATHS_V2,
            *HISTORICAL_V1_PATHS_V2,
            PLAN_PATH_V2,
            ADMISSION_PATH_V2,
            REGISTRY_PATH_V2,
        }
    )
    checked_paths = sorted(
        {
            *current_applicability_paths,
            *(row["path"] for row in DEPENDENCY_EXPECTATIONS_V2.values()),
        }
    )
    if not set(SOURCE_PATHS_V2).issubset(checked_paths):
        raise EvidenceV2Error("changed-path checker coverage is incomplete")
    return {
        "schema": SCHEMA_V2,
        "stage_a": {
            "commit": stage_a_commit,
            "parent": STAGE_A_PARENT_V2,
            "write_set_count": len(STAGE_A_WRITE_SET_V2),
            "write_set": write_set,
        },
        "status": STATUS_V2,
        "release_ready": False,
        "authority": AUTHORITY_V2.copy(),
        "closed_value_movement_gates": 0,
        "required_value_movement_gates": 12,
        "checked_paths": checked_paths,
        "current_applicability_paths": current_applicability_paths,
        "current_applicability_scope": "STAGE_A_SOURCES_V1_PRESERVATION_AND_ACTIVE_PLAN; HISTORICAL_DEPENDENCY_ARTIFACTS_EXCLUDED",
        "active_plan": active_plan,
        "historical_stage_a_dependencies": dependencies,
        "historical_v1_preservation": historical,
        "source_manifest": source_manifest,
        "wire_dtos": records,
        "field_profiles": _field_profiles_v2(root, stage_a_commit),
        "resource_limits": _limits_v2(root, stage_a_commit),
        "resource_limit_nonclaim": "The wire transport byte limit does not constrain GlobalEconomicStateV2 construction.",
        "fixture": {
            "path": WIRE_FIXTURE_PATH_V2,
            "whole_sha256": WIRE_FIXTURE_SHA256_V2,
            "production_canonical_bytes": "COMPACT_SORTED_ASCII_WITHOUT_TRAILING_NEWLINE",
            "per_record_parity": per_record_sha256,
        },
        "accepted_witness_conversion": "OPAQUE_NO_WIRE_TO_DOMAIN_CONVERSION",
        "safe_domain_input_conversions": ["LaneContext", "Candidate"],
        "candidate_order": "SUPPLIED_ORDER_PRESERVED",
        "nonclaims": list(NONCLAIMS_V2),
    }


def current_path_sha256_v2(root: Path, path: str) -> str | None:
    """Hash one contained, regular, non-symlink current-worktree path."""

    _safe_repo_path_v2(path)
    lexical = root / path
    try:
        if lexical.is_symlink():
            return None
        resolved = lexical.resolve(strict=True)
        resolved.relative_to(root)
        stat = resolved.stat()
    except (OSError, ValueError):
        return None
    if not resolved.is_file() or stat.st_size > MAX_GIT_BLOB_BYTES_V2:
        return None
    try:
        raw = resolved.read_bytes()
    except OSError:
        return None
    if len(raw) != stat.st_size:
        return None
    return sha256_bytes_v2(raw)


def render_markdown_v2(evidence: dict[str, object]) -> str:
    """Render a human review companion without elevating the JSON claim ceiling."""

    stage_a = _object_v2(evidence.get("stage_a"), context="render stage_a")
    return "\n".join(
        (
            "# O-008 V2 bounded-core evidence",
            "",
            f"Stage-A subject: `{stage_a['commit']}`",
            f"Stage-A parent: `{stage_a['parent']}`",
            f"Status: `{STATUS_V2}`",
            "",
            "Authority: `NONE`; release readiness: `false`; value-movement gates: `0/12`.",
            "",
            "This source-pinned packet records a bounded implementation slice. O-008 remains open and dependency-blocked.",
        )
    ) + "\n"
