"""Recompute the exact unmounted C07 migration review packet.

This checker binds the retained C03/C04 values, the C05 Lean declaration
digests, and the B09 parity artifacts to one review packet.  It is a local
research verifier.  It does not construct runtime authority or mount a
migration caller.
"""
from __future__ import annotations

import hashlib
import json
import re
import subprocess
from pathlib import Path
from typing import Any, cast

from src.core.fcis_entitlement_key_v1 import EntitlementKeyV1
from src.core.fcis_entitlement_migration_codec_v1 import (
    canonical_sha256_migration_manifest_v1,
    decode_representation_migration_manifest_v1,
    encode_entitlement_state_v1,
    encode_representation_migration_manifest_v1,
)
from src.core.fcis_entitlement_migration_values_v1 import (
    EntitlementStateEntryV1,
    EntitlementStateV1,
    RepresentationMigrationManifestV1,
)
from src.core.fcis_entitlement_transport_v1 import transport_srgd_to_agqe_v1
from src.core.fcis_m6_profile_ids import (
    AGQE_REPRESENTATION_PROFILE_ID_V1,
    FIXED_ROLE_ORDER_ID_V1,
    SEMANTIC_ALLOCATOR_PROFILE_ID_V1,
    SRGD_REPRESENTATION_PROFILE_ID_V1,
)

_PACKET_PATH = Path("docs/research/m6_tasks/TASK_C07_MIGRATION_REVIEW_PACKET.json")
_C04_VECTOR_PATH = Path("docs/research/m6_tasks/TASK_C04_SIGN_DUAL_VECTOR.json")
_B09_RESULT_PATH = Path(
    "docs/research/m6_tasks/TASK_B09_ARTIFACTS/TASK_B09_PARITY_RESULT.json"
)
_B09_INDEX_PATH = Path(
    "docs/research/m6_tasks/TASK_B09_ARTIFACTS/TASK_B09_ARTIFACT_INDEX.json"
)
_LEAN_SOURCE_PATH = Path(
    "lean-mathlib/Proofs/FCISFeeApportionmentAGQESRGDTraceConjugacy.lean"
)
_DIGEST_RE = re.compile(r"^[0-9a-f]{64}$")
_GIT_RE = re.compile(r"^[0-9a-f]{40}$")
_THEOREM_RE = re.compile(r"(?m)^theorem\s+([A-Za-z0-9_]+)")
_NAMESPACE_END = chr(10) + "end FCISFeeApportionmentAGQESRGDTraceConjugacy"


def _sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _sha256_file(path: Path) -> str:
    return _sha256_bytes(path.read_bytes())


def _mapping(value: object, path: str) -> dict[str, Any]:
    if type(value) is not dict:
        raise AssertionError(f"{path} must be an object")
    return cast(dict[str, Any], value)


def _string(mapping: dict[str, Any], key: str, path: str) -> str:
    value = mapping.get(key)
    if type(value) is not str or not value:
        raise AssertionError(f"{path}.{key} must be a nonempty string")
    return value


def _assert_digest(actual: str, expected: object, path: str) -> None:
    if type(expected) is not str or not _DIGEST_RE.fullmatch(expected):
        raise AssertionError(f"{path} is not a lowercase SHA-256 digest")
    if actual != expected:
        raise AssertionError(f"{path} mismatch: {actual} != {expected}")


def _assert_commit_identity(commit: str, tree: str, path: str) -> None:
    if not _GIT_RE.fullmatch(commit) or not _GIT_RE.fullmatch(tree):
        raise AssertionError(f"{path} has a noncanonical Git identity")
    result = subprocess.run(
        ["git", "rev-parse", f"{commit}^{{commit}}", f"{commit}^{{tree}}"],
        check=True,
        capture_output=True,
        text=True,
    )
    resolved = result.stdout.splitlines()
    if resolved != [commit, tree]:
        raise AssertionError(f"{path} Git identity mismatch: {resolved}")


def _state_from_packet(
    packet_migration: dict[str, Any],
    state_name: str,
    key: EntitlementKeyV1,
    representation_id: str,
    mappings: list[dict[str, Any]],
    coordinate_key: str,
) -> EntitlementStateV1:
    entries: list[EntitlementStateEntryV1] = []
    for index, item in enumerate(mappings):
        entry_id = _string(item, "entry_id", f"migration.entry_mappings[{index}]")
        raw_coordinates = item.get(coordinate_key)
        if type(raw_coordinates) is not list or len(raw_coordinates) != 3:
            raise AssertionError(
                f"migration.entry_mappings[{index}].{coordinate_key} must be a three-list"
            )
        coordinates = tuple(raw_coordinates)
        if not all(type(coordinate) is int for coordinate in coordinates):
            raise AssertionError(
                f"migration.entry_mappings[{index}].{coordinate_key} must contain integers"
            )
        entries.append(EntitlementStateEntryV1(entry_id, coordinates))
    state = EntitlementStateV1(key, representation_id, tuple(entries))
    packet_state = _mapping(packet_migration[state_name], f"migration.{state_name}")
    if packet_state["representation_id"] != representation_id:
        raise AssertionError(f"migration.{state_name}.representation_id mismatch")
    if packet_state["root"] != state.state_root:
        raise AssertionError(f"migration.{state_name}.root mismatch")
    if packet_state["canonical_bytes_utf8"] != encode_entitlement_state_v1(state).decode(
        "utf-8"
    ):
        raise AssertionError(f"migration.{state_name}.canonical_bytes_utf8 mismatch")
    return state


def _check_migration(packet: dict[str, Any]) -> None:
    migration = _mapping(packet.get("migration"), "migration")
    key_data = _mapping(migration.get("key"), "migration.key")
    key = EntitlementKeyV1(
        _string(key_data, "fee_distribution_domain_id", "migration.key"),
        _string(key_data, "asset", "migration.key"),
        _string(key_data, "semantic_profile_id", "migration.key"),
        _string(key_data, "fixed_role_order_id", "migration.key"),
    )
    if key.semantic_profile_id != SEMANTIC_ALLOCATOR_PROFILE_ID_V1:
        raise AssertionError("semantic profile drifted from C02")
    if key.fixed_role_order_id != FIXED_ROLE_ORDER_ID_V1:
        raise AssertionError("fixed role order drifted from C02")
    mappings_value = migration.get("entry_mappings")
    if type(mappings_value) is not list:
        raise AssertionError("migration.entry_mappings must be a list")
    mappings = [_mapping(item, f"migration.entry_mappings[{i}]") for i, item in enumerate(mappings_value)]
    old_state = _state_from_packet(
        migration,
        "old_state",
        key,
        SRGD_REPRESENTATION_PROFILE_ID_V1,
        mappings,
        "source_coordinates",
    )
    new_state = _state_from_packet(
        migration,
        "new_state",
        key,
        AGQE_REPRESENTATION_PROFILE_ID_V1,
        mappings,
        "target_coordinates",
    )
    for index, item in enumerate(mappings):
        source = item.get("source_coordinates")
        target = item.get("target_coordinates")
        if type(source) is not list or type(target) is not list:
            raise AssertionError(f"entry mapping {index} coordinates must be lists")
        if target != [-coordinate for coordinate in source]:
            raise AssertionError(f"entry mapping {index} is not sign-dual")

    vector = _mapping(json.loads(_C04_VECTOR_PATH.read_text(encoding="utf-8")), "C04 vector")
    packet_old = _mapping(migration["old_state"], "migration.old_state")
    packet_new = _mapping(migration["new_state"], "migration.new_state")
    for vector_name, packet_state in (("old_state", packet_old), ("new_state", packet_new)):
        vector_state = _mapping(vector[vector_name], f"C04 vector.{vector_name}")
        if vector_state["canonical_bytes_utf8"] != packet_state["canonical_bytes_utf8"]:
            raise AssertionError(f"C07 {vector_name} bytes differ from the retained C04 vector")
        if vector_state["root"] != packet_state["root"]:
            raise AssertionError(f"C07 {vector_name} root differs from the retained C04 vector")
    if vector["entry_mappings"] != mappings:
        raise AssertionError("C07 entry mappings differ from the retained C04 vector")
    if transport_srgd_to_agqe_v1(old_state, expected_target=new_state) != new_state:
        raise AssertionError("C04 transport did not accept the packet states")

    activation = migration.get("activation_sequence")
    if type(activation) is not int:
        raise AssertionError("migration.activation_sequence must be an integer")
    authority_epoch_root = _string(
        migration,
        "authority_epoch_root",
        "migration",
    )
    migration_map_id = _string(migration, "migration_map_id", "migration")
    manifest = RepresentationMigrationManifestV1(
        old_state,
        new_state,
        migration_map_id,
        authority_epoch_root,
        activation,
    )
    encoded_manifest = encode_representation_migration_manifest_v1(manifest)
    manifest_data = _mapping(migration.get("manifest"), "migration.manifest")
    if manifest_data.get("canonical_bytes_utf8") != encoded_manifest.decode("utf-8"):
        raise AssertionError("migration manifest canonical bytes mismatch")
    _assert_digest(
        _sha256_bytes(encoded_manifest),
        str(manifest_data.get("sha256", "")).removeprefix("0x"),
        "migration.manifest.sha256",
    )
    if canonical_sha256_migration_manifest_v1(manifest) != manifest_data["sha256"]:
        raise AssertionError("migration manifest canonical helper mismatch")
    decoded = decode_representation_migration_manifest_v1(
        encoded_manifest,
        expected_old_state=old_state,
        expected_new_state=new_state,
    )
    if type(decoded) is not RepresentationMigrationManifestV1 or decoded != manifest:
        raise AssertionError("migration manifest did not round-trip through C03 decode")


def _declaration_hashes(source: str, names: list[str]) -> dict[str, str]:
    matches = list(_THEOREM_RE.finditer(source))
    starts = {match.group(1): match.start() for match in matches}
    selected_starts = {name: starts[name] for name in names if name in starts}
    namespace_end = source.index(_NAMESPACE_END)
    result: dict[str, str] = {}
    for name in names:
        if name not in starts:
            raise AssertionError(f"Lean theorem is missing: {name}")
        start = starts[name]
        following = [position for position in selected_starts.values() if position > start]
        end = min(following, default=namespace_end)
        declaration = source[start:end].replace("\r\n", "\n")
        result[name] = _sha256_bytes(declaration.encode("utf-8"))
    return result


def _check_lean(packet: dict[str, Any]) -> None:
    lean = _mapping(packet.get("lean_theorems"), "lean_theorems")
    source_hash = _string(lean, "source_sha256", "lean_theorems")
    _assert_digest(_sha256_file(_LEAN_SOURCE_PATH), source_hash, "lean_theorems.source_sha256")
    declarations = _mapping(lean.get("declarations"), "lean_theorems.declarations")
    names = list(declarations)
    actual = _declaration_hashes(
        _LEAN_SOURCE_PATH.read_text(encoding="utf-8").replace("\r\n", "\n"),
        names,
    )
    for name, expected in declarations.items():
        _assert_digest(actual[name], expected, f"lean_theorems.declarations.{name}")


def _check_parity(packet: dict[str, Any]) -> None:
    parity = _mapping(packet.get("parity_vectors"), "parity_vectors")
    result_path = Path(_string(parity, "parity_result_path", "parity_vectors"))
    index_path = Path(_string(parity, "artifact_index_path", "parity_vectors"))
    _assert_digest(
        _sha256_file(result_path),
        parity.get("parity_result_sha256"),
        "parity_vectors.parity_result_sha256",
    )
    _assert_digest(
        _sha256_file(index_path),
        parity.get("artifact_index_sha256"),
        "parity_vectors.artifact_index_sha256",
    )
    result = _mapping(json.loads(result_path.read_text(encoding="utf-8")), "B09 result")
    production = _mapping(result.get("production"), "B09 result.production")
    small = _mapping(result.get("small_domain"), "B09 result.small_domain")
    packet_production = _mapping(parity.get("production"), "parity_vectors.production")
    packet_small = _mapping(parity.get("small_domain"), "parity_vectors.small_domain")
    if production.get("total_vectors") != packet_production.get("vectors"):
        raise AssertionError("B09 production vector count mismatch")
    if production.get("exact_byte_match") is not True or packet_production.get("python_rust_julia_exact_byte_match") is not True:
        raise AssertionError("B09 production exact-byte parity is false")
    packet_output_digest = packet_production.get("output_sha256")
    for key in ("python_sha256", "rust_sha256", "julia_sha256"):
        if production.get(key) != packet_output_digest:
            raise AssertionError(f"B09 production parity drift for {key}")
    if packet_small["vectors"] != small["vectors"] or packet_small["output_sha256"] != small["python_sha256"]:
        raise AssertionError("B09 small-domain parity drift")
    if not small["exact_byte_match"] or packet_small.get("python_julia_exact_byte_match") is not True:
        raise AssertionError("B09 small-domain exact-byte parity is false")
        raise AssertionError("B09 small-domain exact-byte parity is false")
    index = _mapping(json.loads(index_path.read_text(encoding="utf-8")), "B09 index")
    if index.get("schema_version") != "zenodex.fcis.m6.b09-artifact-index.v1":
        raise AssertionError("B09 artifact index schema drift")
    indexed_result = next(
        (
            item
            for item in cast(list[Any], index.get("entries", []))
            if type(item) is dict and item.get("path") == result_path.name
        ),
        None,
    )
    if type(indexed_result) is not dict or indexed_result.get("sha256") != _sha256_file(result_path):
        raise AssertionError("B09 artifact index does not bind the parity result")


def main() -> int:
    packet = _mapping(json.loads(_PACKET_PATH.read_text(encoding="utf-8")), "packet")
    source_head = _mapping(packet.get("source_head"), "source_head")
    _assert_commit_identity(
        _string(source_head, "commit", "source_head"),
        _string(source_head, "tree", "source_head"),
        "source_head",
    )
    lineage = _mapping(packet.get("lineage_commits"), "lineage_commits")
    for name, value in lineage.items():
        entry = _mapping(value, f"lineage_commits.{name}")
        _assert_commit_identity(
            _string(entry, "commit", f"lineage_commits.{name}"),
            _string(entry, "tree", f"lineage_commits.{name}"),
            f"lineage_commits.{name}",
        )
    _check_migration(packet)
    _check_lean(packet)
    _check_parity(packet)
    print("C07_REVIEW_PACKET_MATCH")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
