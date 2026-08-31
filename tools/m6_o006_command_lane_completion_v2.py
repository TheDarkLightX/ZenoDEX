"""Pure O006 V2 exact-subject command-lane closure certificate.

The module certifies one bounded structural command map. It grants no runtime,
release, settlement, migration, verifier, or value-movement authority.
"""

from __future__ import annotations

import ast
import hashlib
import re
from dataclasses import dataclass
from typing import Final, NoReturn, cast

from src.core.m6_safe_mount_types_v1 import (
    M6_RESEARCH_DISABLED_COMMANDS_V1,
    GlobalCommandKindV1,
)
from tools.m6_normative_requirements_v1 import (
    RequirementsRejectV1,
    canonical_json_bytes_v1,
    decode_json_object_v1,
)

ARTIFACT_PATH_V2: Final = "docs/research/M6_O006_COMMAND_LANE_COMPLETION_V2.json"
ARTIFACT_SCHEMA_V2: Final = "zenodex/m6-o006-command-lane-completion/v2"
CHECK_SCHEMA_V2: Final = "zenodex/m6-o006-command-lane-completion-check/v2"
CERTIFICATE_DOMAIN_V2: Final = b"zenodex/m6-o006-command-lane-completion-root/v2"
SOURCE_MANIFEST_DOMAIN_V2: Final = b"zenodex/m6-o006-source-manifest-root/v2"
CAPABILITY_PROJECTION_DOMAIN_V2: Final = b"zenodex/m6-o006-capability-projection-root/v2"
COMMAND_DOMAIN_V2: Final = b"zenodex/m6-o006-command-domain-root/v2"
COMMAND_MAP_DOMAIN_V2: Final = b"zenodex/m6-o006-command-map-root/v2"
VM_GATE_DOMAIN_V2: Final = b"zenodex/m6-o006-vm-gate-domain-root/v2"

BASE_COMMIT_V2: Final = "553593e164e738824b67dc16a4bcd7a14f67a179"
BASE_TREE_V2: Final = "7986b9798342d1daf5715c2ab64e13e78b11b285"
EXPECTED_DECISION_ROOT_V2: Final = (
    "13a1d6a240991823d73af010cdc593234c3fde4652602d2b672ca1ff1a8a9d93"
)
EXPECTED_REGISTRY_ROOT_V2: Final = (
    "a19213bc19d0dac11379a7d82e04bfc8ed4a1ebeb0c133d076e81d0ae02061b7"
)
O005_ARTIFACT_COMMIT_V2: Final = "d4f6b11886ddf2cd80350e2cd527fa5920555d81"
O005_CERTIFICATE_ROOT_V2: Final = "a5305dc894b2548834ea564b0f44ef8a2604eda29e63fe156e37a320535ae105"
O005_EVIDENCE_SUBJECT_COMMIT_V2: Final = "5ffc76e784db3d0cc05a90c4d002e805f8724fe2"
O005_EVIDENCE_SUBJECT_TREE_V2: Final = "90b60bfaaabd7306dd94e88030fbb00e9a331afb"
CAPABILITY_MANIFEST_SHA256_V2: Final = (
    "34930be9d4d69c4c46c7c97f57fd492d4c95061f8960f936261a8a3415d5db95"
)
SAFE_MOUNT_SOURCE_PATH_V2: Final = "src/core/m6_safe_mount_types_v1.py"
GOVERNED_ROUTE_IDS_V2: Final = (
    "fee_funded_zdex_purchase_and_burn",
    "zusd_liquidation_settlement",
    "perps_epoch_settlement",
    "strategy_triggered_spot_swap",
)

COMMAND_REGISTRY_PATH_V2: Final = "docs/research/ZENODEX_M6_COMMAND_LANE_REGISTRY_V1.json"
CAPABILITY_MANIFEST_PATH_V2: Final = "docs/research/ZENODEX_M6_CAPABILITY_MANIFEST_V1.json"
NORMATIVE_REQUIREMENTS_PATH_V2: Final = "docs/research/ZENODEX_M6_NORMATIVE_REQUIREMENTS_V1.json"
O005_ARTIFACT_PATH_V2: Final = "docs/research/M6_O005_REQUIREMENTS_FLOOR_COMPLETION_V1.json"
PLAN_PATH_V2: Final = "docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V2.json"
RUNTIME_TRANSITION_PATH_V2: Final = "src/core/m6_safe_mount_transition_v1.py"
RUST_CORE_PATH_V2: Final = "zk/recursive_stark_v2_risc0/shared/src/m6_core_v1.rs"

MAX_SOURCE_BYTES_V2: Final = 524_288
MAX_ARTIFACT_BYTES_V2: Final = 524_288
MAX_SOURCE_COUNT_V2: Final = 32

STAGE_A_SOURCE_PATHS_V2: Final = (
    "tools/m6_o006_command_lane_completion_v2.py",
    "tools/build_m6_o006_command_lane_completion_v2.py",
    "tools/check_m6_o006_command_lane_completion_v2.py",
    "tests/test_check_m6_o006_command_lane_completion_v2.py",
    "tests/evidence/test_hygiene/THV1-20260831-m6-o006-current-subject-restage-v2.json",
)

# Path, Git blob SHA-1, SHA-256, and size for the exact admitted current base.
# Stage A must preserve every entry unchanged.
BASE_SOURCE_SPECS_V2: Final = (
    (
        O005_ARTIFACT_PATH_V2,
        "5d5f3b729d6605ce4ace527b31855d829ccd5c49",
        "5c6812d21509432cd3b54c84a7a85e08fe040c294655e1c5fca0e9a8c610e47a",
        9_668,
    ),
    (
        COMMAND_REGISTRY_PATH_V2,
        "013400e33e46c21d79f2cd52b65811970194483d",
        "c07b8dcaa995ee40ad9e677b243d64d133e723f4b5dc8cda2b934349af59094a",
        9_008,
    ),
    (
        CAPABILITY_MANIFEST_PATH_V2,
        "989965363d73b514362f36ce0088f7ba27c8825a",
        "34930be9d4d69c4c46c7c97f57fd492d4c95061f8960f936261a8a3415d5db95",
        6_565,
    ),
    (
        NORMATIVE_REQUIREMENTS_PATH_V2,
        "289fd40f77c9edbf30187676a00eddf0f9fca27e",
        "29d67d2c8ebd35d6e0003927c73043f3f282efe16b780b4493504d1d00db390f",
        262_425,
    ),
    (
        PLAN_PATH_V2,
        "6da997fe32f39a4c1bf0c89a3f6dfc87a16f863f",
        "8bbd05a875317fb75e4853f7babc3a91351e581f6d1ec7ed75db0e660ae4542f",
        37_512,
    ),
    (
        "docs/research/ZENODEX_ACTIVE_WHOLE_PROGRAM_PLAN_V1.json",
        "27bfcde8064a007b5c07fba8d6f09b8a8294e2bd",
        "b9996e69d56e179de01f54e1a81b9093ff366de45354fb18768421f57d7913c4",
        1_172,
    ),
    (
        "docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_ADMISSION_V1.json",
        "6bc9bc54b5145bbc044312878600e651031ed28d",
        "8d551e10a6a74ce46f39c611fe29960eeb4ef1b05c839702ce8b4779e474b87d",
        3_810,
    ),
    (
        "src/core/m6_command_lane_registry_v1.py",
        "8bd91d8c5033e67a879616cbecc38b6b7eaa9155",
        "028b4511a70abe0fdf80d49558686d0307dc59a5d8ffdb2a06ed3f08cb0b2fb1",
        30_577,
    ),
    (
        SAFE_MOUNT_SOURCE_PATH_V2,
        "06007c01c43076d3a43118209d7349ba928f0bf4",
        "e9dfe00abd72f20f6c49986dd5af5a7f37042ee100b9f6d26f6b719b8e5623f8",
        158_823,
    ),
    (
        RUNTIME_TRANSITION_PATH_V2,
        "c8d7e105f14677f1808edb03974a7c348d0d0044",
        "9355b083064439b2756ee1d9454710229eaa3fe31fd529587ea3ece66cba8ee2",
        81_523,
    ),
    (
        RUST_CORE_PATH_V2,
        "c82bfdf7daf8dfa5ef356dc89cdb5151ba6ac915",
        "1f9f2edd2745e5964a741a91c9ba7ae72cd1d23da429921d30ebb4408076e7c1",
        14_480,
    ),
    (
        "tools/build_m6_command_lane_registry_v1.py",
        "1439114842f5b0c0ff08961e1dff774046286b60",
        "daa8309c02cd0d238466dfddd40d46462c07a429b9df12085ecca88a3e012d62",
        11_156,
    ),
    (
        "tools/check_m6_command_lane_registry_v1.py",
        "b25c376e9e3070ae3982065ddeaecc710c83b6d2",
        "5bc728b1e5188c7dbc776083ea7ceb4b3b52dde2d1c5757be00a89da0ee86792",
        3_261,
    ),
    (
        "tools/build_m6_normative_requirements_v1.py",
        "8d56cdeb9141bd0b5fbcebe89ac7bb1044c821e1",
        "c27fe1dcb6b5ca6f583cbb30d82d33b413288f823ada7c74448f4d163a8e93b8",
        25_847,
    ),
    (
        "tools/m6_normative_requirements_v1.py",
        "56d8657e34c1aa6e854914cb153c3fc2838b53bc",
        "519ded69a8d537543056c6561e864323f3b27ecc6fcde227891b8b03250a6039",
        138_724,
    ),
    (
        "tools/m6_o005_requirements_floor_completion_v1.py",
        "8a2d7106609033f7bcfa7c7df91084d8bc8e9b18",
        "532a7b995ce122330ad82c46c94952dffe5528b1a44c2763b63c79f00a88f3d0",
        44_905,
    ),
    (
        "tools/build_m6_o005_requirements_floor_completion_v1.py",
        "158ee495ef651273e3593fff4cd73fc7273fd90d",
        "0549c802d784e299c56a303fdfc6de007d4d13a4cfeacfc6dbdb55a1256dcf98",
        6_509,
    ),
    (
        "tools/check_m6_o005_requirements_floor_completion_v1.py",
        "aa32db1e458c2aeeb60042f48b6418b220e0d92d",
        "11c9bbff5fbaace16f5e1eb4c1ea690f6fbd17946f924d9af330588bd76011f3",
        3_244,
    ),
    (
        "tests/core/test_m6_command_lane_registry_v1.py",
        "050f1c23ac290d3bdcacdc0535df19c54f8c6f3a",
        "a36d23c92846f5534d40cb0e4b0836c759490302f7a6d58433949a7cb29253fd",
        15_429,
    ),
    (
        "tests/test_check_m6_command_lane_registry_v1.py",
        "ef2d944f1538b2e831946773700f8162fcb398ad",
        "dbb39eae93a2c707081cbbade58efe3de00b88c041eb88ce2015bbe4be10b111",
        6_367,
    ),
    (
        "tests/core/test_external_custody_disabled_lane_v1.py",
        "827e6279dc06ef7323cd4ef2232aac228f4cd85c",
        "a9ee0bd115a4a599f6b5f70c470bb344cc5518bfc97de176ea748b28433ea616",
        4_856,
    ),
)

O006_REQUIRED_EVIDENCE_V2: Final = (
    "all registered commands mapped exactly once",
    "research-disabled commands cannot map to ACTIVE_NEW",
    "unmapped and duplicate mapping mutants",
    "map root bound by the capability manifest",
    "current-subject obligation and value-movement ledger rows initialized",
)


@dataclass(frozen=True)
class CommandLaneCompletionRejectV2(ValueError):
    code: str
    path: str
    detail: str

    def __str__(self) -> str:
        return f"{self.code} at {self.path}: {self.detail}"


def _reject(code: str, path: str, detail: str) -> NoReturn:
    raise CommandLaneCompletionRejectV2(code, path, detail)


def _is_lower_hex(value: object, length: int) -> bool:
    return (
        type(value) is str
        and len(value) == length
        and all(character in "0123456789abcdef" for character in value)
    )


@dataclass(frozen=True)
class SourcePinV2:
    path: str
    git_blob_sha: str
    sha256: str
    size_bytes: int

    def to_json(self) -> dict[str, object]:
        return {
            "git_blob_sha": self.git_blob_sha,
            "path": self.path,
            "sha256": self.sha256,
            "size_bytes": self.size_bytes,
        }


@dataclass(frozen=True)
class StageASnapshotV2:
    captured_git_head: str
    rechecked_git_head: str
    stage_a_commit: str
    stage_a_tree: str
    base_is_direct_parent: bool
    stage_a_delta: tuple[tuple[str, str], ...]
    base_source_pins: tuple[SourcePinV2, ...]
    stage_a_source_pins: tuple[SourcePinV2, ...]
    source_bytes: tuple[tuple[str, bytes], ...]


def canonical_json_bytes_v2(value: object) -> bytes:
    try:
        return canonical_json_bytes_v1(value)
    except RequirementsRejectV1 as exc:
        _reject("CANONICAL_" + exc.code, exc.path, exc.detail)


def _decode_object(raw: bytes, path: str, *, require_canonical: bool) -> dict[str, object]:
    if type(raw) is not bytes:
        _reject("JSON_BYTES_TYPE", path, "must be exact bytes")
    if len(raw) > MAX_SOURCE_BYTES_V2:
        _reject("JSON_BYTE_LIMIT", path, "source byte ceiling exceeded")
    try:
        value = decode_json_object_v1(raw, path)
    except RequirementsRejectV1 as exc:
        _reject("JSON_" + exc.code, path, exc.detail)
    if require_canonical and canonical_json_bytes_v2(value) != raw:
        _reject("JSON_NONCANONICAL", path, "must be canonical JSON bytes")
    return value


def _git_blob_sha(raw: bytes) -> str:
    header = f"blob {len(raw)}\0".encode("ascii")
    return hashlib.sha1(header + raw, usedforsecurity=False).hexdigest()


def _domain_root(domain: bytes, value: object) -> str:
    return hashlib.sha256(domain + b"\0" + canonical_json_bytes_v2(value)).hexdigest()


def source_manifest_root_v2(value: object) -> str:
    return _domain_root(SOURCE_MANIFEST_DOMAIN_V2, value)


def certificate_root_v2(unsigned: object) -> str:
    if type(unsigned) is not dict:
        _reject("CERTIFICATE_ROOT_INPUT", "certificate", "must be an exact object")
    if "certificate_root" in cast(dict[str, object], unsigned):
        _reject("CERTIFICATE_ROOT_INPUT", "certificate", "must omit certificate_root")
    return _domain_root(CERTIFICATE_DOMAIN_V2, unsigned)


def _owned_pin(pin: object, path: str) -> SourcePinV2:
    if type(pin) is not SourcePinV2:
        _reject("SOURCE_PIN_TYPE", path, "must be an exact SourcePinV2")
    exact = pin
    if type(exact.path) is not str or not exact.path or exact.path.startswith("/"):
        _reject("SOURCE_PATH", path, "must be a nonempty relative path")
    if not _is_lower_hex(exact.git_blob_sha, 40):
        _reject("SOURCE_GIT_BLOB", exact.path, "must be forty lowercase hex characters")
    if not _is_lower_hex(exact.sha256, 64):
        _reject("SOURCE_SHA256", exact.path, "must be sixty-four lowercase hex characters")
    if (
        type(exact.size_bytes) is not int
        or isinstance(exact.size_bytes, bool)
        or not 0 <= exact.size_bytes <= MAX_SOURCE_BYTES_V2
    ):
        _reject("SOURCE_SIZE", exact.path, "must be within the source byte ceiling")
    return SourcePinV2(
        path=exact.path,
        git_blob_sha=exact.git_blob_sha,
        sha256=exact.sha256,
        size_bytes=exact.size_bytes,
    )


def _owned_snapshot(snapshot: object) -> StageASnapshotV2:
    if type(snapshot) is not StageASnapshotV2:
        _reject("SNAPSHOT_TYPE", "snapshot", "must be an exact StageASnapshotV2")
    exact = snapshot
    if (
        type(exact.stage_a_delta) is not tuple
        or type(exact.base_source_pins) is not tuple
        or type(exact.stage_a_source_pins) is not tuple
        or type(exact.source_bytes) is not tuple
    ):
        _reject("SNAPSHOT_CONTAINER_TYPE", "snapshot", "containers must be exact tuples")
    if len(exact.base_source_pins) != len(BASE_SOURCE_SPECS_V2) or len(
        exact.stage_a_source_pins
    ) != len(STAGE_A_SOURCE_PATHS_V2):
        _reject("SOURCE_COUNT", "snapshot", "source pin cardinality drift")
    if len(exact.source_bytes) != len(BASE_SOURCE_SPECS_V2) + len(STAGE_A_SOURCE_PATHS_V2):
        _reject("SOURCE_COUNT", "snapshot.source_bytes", "source byte cardinality drift")
    delta_rows: list[tuple[str, str]] = []
    for index, delta_row in enumerate(exact.stage_a_delta):
        if (
            type(delta_row) is not tuple
            or len(delta_row) != 2
            or type(delta_row[0]) is not str
            or type(delta_row[1]) is not str
        ):
            _reject("STAGE_A_DELTA_TYPE", f"stage_a_delta[{index}]", "must be a string pair")
        delta_rows.append((delta_row[0], delta_row[1]))
    byte_rows: list[tuple[str, bytes]] = []
    for index, byte_row in enumerate(exact.source_bytes):
        if (
            type(byte_row) is not tuple
            or len(byte_row) != 2
            or type(byte_row[0]) is not str
            or type(byte_row[1]) is not bytes
        ):
            _reject("SOURCE_BYTES_TYPE", f"source_bytes[{index}]", "must be path and bytes")
        byte_rows.append((byte_row[0], byte_row[1]))
    return StageASnapshotV2(
        captured_git_head=exact.captured_git_head,
        rechecked_git_head=exact.rechecked_git_head,
        stage_a_commit=exact.stage_a_commit,
        stage_a_tree=exact.stage_a_tree,
        base_is_direct_parent=exact.base_is_direct_parent,
        stage_a_delta=tuple(delta_rows),
        base_source_pins=tuple(
            _owned_pin(pin, f"base_source_pins[{index}]")
            for index, pin in enumerate(exact.base_source_pins)
        ),
        stage_a_source_pins=tuple(
            _owned_pin(pin, f"stage_a_source_pins[{index}]")
            for index, pin in enumerate(exact.stage_a_source_pins)
        ),
        source_bytes=tuple(byte_rows),
    )


def _expected_base_pins() -> tuple[SourcePinV2, ...]:
    return tuple(SourcePinV2(*row) for row in BASE_SOURCE_SPECS_V2)


def _validate_snapshot(snapshot: StageASnapshotV2) -> dict[str, bytes]:
    for name in ("captured_git_head", "rechecked_git_head", "stage_a_commit", "stage_a_tree"):
        if not _is_lower_hex(getattr(snapshot, name), 40):
            _reject("GIT_ID", f"snapshot.{name}", "must be forty lowercase hex characters")
    if snapshot.captured_git_head != snapshot.rechecked_git_head:
        _reject("HEAD_CHANGED_DURING_CAPTURE", "HEAD", "Git HEAD changed during capture")
    if type(snapshot.base_is_direct_parent) is not bool or not snapshot.base_is_direct_parent:
        _reject("BASE_NOT_DIRECT_PARENT", "stage_a_commit", "exact admitted base must be parent")
    expected_delta = tuple(("A", path) for path in sorted(STAGE_A_SOURCE_PATHS_V2))
    if snapshot.stage_a_delta != expected_delta:
        _reject("STAGE_A_DELTA", "stage_a_commit", "Stage A must add only declared V2 paths")
    if snapshot.base_source_pins != _expected_base_pins():
        _reject("BASE_SOURCE_PIN_DRIFT", "base_source_pins", "exact admitted base pins drift")
    if tuple(pin.path for pin in snapshot.stage_a_source_pins) != STAGE_A_SOURCE_PATHS_V2:
        _reject("STAGE_A_SOURCE_SET", "stage_a_source_pins", "source set or order drift")
    all_pins = snapshot.base_source_pins + snapshot.stage_a_source_pins
    if len(all_pins) > MAX_SOURCE_COUNT_V2:
        _reject("SOURCE_COUNT", "source_pins", "source count ceiling exceeded")
    expected_paths = tuple(pin.path for pin in all_pins)
    if (
        type(snapshot.source_bytes) is not tuple
        or tuple(
            row[0] if type(row) is tuple and len(row) == 2 else None
            for row in snapshot.source_bytes
        )
        != expected_paths
    ):
        _reject("SOURCE_BYTES_SET", "source_bytes", "source byte set or order drift")
    owned: dict[str, bytes] = {}
    for index, ((path, raw), pin) in enumerate(zip(snapshot.source_bytes, all_pins, strict=True)):
        if type(path) is not str or type(raw) is not bytes:
            _reject("SOURCE_BYTES_TYPE", f"source_bytes[{index}]", "must be path and exact bytes")
        if path in owned:
            _reject("SOURCE_DUPLICATE", path, "source path occurs more than once")
        if len(raw) != pin.size_bytes:
            _reject("SOURCE_SIZE_DRIFT", path, "source byte size differs from pin")
        if hashlib.sha256(raw).hexdigest() != pin.sha256:
            _reject("SOURCE_SHA256_DRIFT", path, "source SHA-256 differs from pin")
        if _git_blob_sha(raw) != pin.git_blob_sha:
            _reject("SOURCE_GIT_BLOB_DRIFT", path, "source Git blob differs from pin")
        owned[path] = raw
    return owned


def _validate_plan(plan: dict[str, object]) -> None:
    obligations = plan.get("next_obligations")
    if type(obligations) is not list:
        _reject("PLAN_OBLIGATIONS", PLAN_PATH_V2, "next_obligations must be a list")
    matches = [
        row
        for row in obligations
        if type(row) is dict and cast(dict[str, object], row).get("obligation_id") == "O-006"
    ]
    if len(matches) != 1:
        _reject("PLAN_O006_COUNT", PLAN_PATH_V2, "expected one O-006 obligation")
    row = cast(dict[str, object], matches[0])
    if row.get("depends_on") != ["O-005"] or row.get("closes") != ["command_to_lane_mapping_gap"]:
        _reject("PLAN_O006_DEPENDENCY", PLAN_PATH_V2, "O-006 dependency or closure drift")
    if row.get("required_evidence") != list(O006_REQUIRED_EVIDENCE_V2):
        _reject("PLAN_O006_EVIDENCE", PLAN_PATH_V2, "required evidence drift")


def _vm_gate_ids(plan: dict[str, object]) -> list[str]:
    gates = plan.get("value_movement_gates")
    if type(gates) is not list:
        _reject("VM_GATE_DOMAIN", PLAN_PATH_V2, "value_movement_gates must be a list")
    ids: list[str] = []
    for index, row in enumerate(cast(list[object], gates)):
        if type(row) is not dict:
            _reject("VM_GATE_ROW", f"value_movement_gates[{index}]", "must be an object")
        gate_id = cast(dict[str, object], row).get("gate_id")
        if type(gate_id) is not str or re.fullmatch(r"VM-(0[1-9]|1[0-2])", gate_id) is None:
            _reject("VM_GATE_ID", f"value_movement_gates[{index}]", "gate ID drift")
        ids.append(gate_id)
    expected = [f"VM-{index:02d}" for index in range(1, 13)]
    if ids != expected:
        _reject("VM_GATE_DOMAIN", PLAN_PATH_V2, "expected the canonical twelve-gate domain")
    return ids


def _capability_projection(
    manifest: dict[str, object],
) -> tuple[dict[str, object], set[str], set[str]]:
    if manifest.get("schema") != "zenodex/m6-capability-manifest/v1":
        _reject("CAPABILITY_SCHEMA", CAPABILITY_MANIFEST_PATH_V2, "schema drift")
    lanes = manifest.get("lanes")
    routes = manifest.get("required_cross_lane_routes")
    if type(lanes) is not list or type(routes) is not list:
        _reject("CAPABILITY_SHAPE", CAPABILITY_MANIFEST_PATH_V2, "lanes or routes missing")
    lane_rows: list[dict[str, str]] = []
    for index, row in enumerate(cast(list[object], lanes)):
        if type(row) is not dict:
            _reject("CAPABILITY_LANE_ROW", f"lanes[{index}]", "must be an object")
        value = cast(dict[str, object], row)
        lane_id = value.get("lane_id")
        disposition = value.get("disposition")
        if type(lane_id) is not str or type(disposition) is not str:
            _reject("CAPABILITY_LANE_FIELD", f"lanes[{index}]", "lane fields must be strings")
        lane_rows.append({"disposition": disposition, "lane_id": lane_id})
    lane_ids = [row["lane_id"] for row in lane_rows]
    if len(lane_ids) != 12 or len(set(lane_ids)) != 12:
        _reject("CAPABILITY_LANE_DOMAIN", CAPABILITY_MANIFEST_PATH_V2, "lane domain drift")
    if routes != list(GOVERNED_ROUTE_IDS_V2):
        _reject("CAPABILITY_ROUTE_DOMAIN", CAPABILITY_MANIFEST_PATH_V2, "route domain drift")
    projection: dict[str, object] = {
        "lanes": lane_rows,
        "required_cross_lane_routes": list(GOVERNED_ROUTE_IDS_V2),
        "schema": "zenodex/m6-capability-projection/v2",
    }
    return projection, set(lane_ids), set(GOVERNED_ROUTE_IDS_V2)


def _rust_command_domain(raw: bytes) -> list[str]:
    try:
        source = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        _reject("RUST_UTF8", RUST_CORE_PATH_V2, f"invalid UTF-8 at {exc.start}")
    marker = "pub enum GlobalCommandKindV1 {\n"
    if source.count(marker) != 1:
        _reject("RUST_COMMAND_ENUM", RUST_CORE_PATH_V2, "expected one command enum")
    body = source.split(marker, 1)[1].split("\n}", 1)[0]
    variants = [line.strip()[:-1] for line in body.splitlines() if line.strip().endswith(",")]
    if not variants or any(re.fullmatch(r"[A-Z][A-Za-z0-9]*", value) is None for value in variants):
        _reject("RUST_COMMAND_ENUM", RUST_CORE_PATH_V2, "malformed enum variants")
    return [re.sub(r"(?<!^)(?=[A-Z])", "_", value).lower() for value in variants]


def _runtime_disabled_domain(raw: bytes) -> list[str]:
    try:
        tree = ast.parse(raw.decode("utf-8"), filename=RUNTIME_TRANSITION_PATH_V2)
    except (SyntaxError, UnicodeDecodeError) as exc:
        _reject("RUNTIME_GUARD_PARSE", RUNTIME_TRANSITION_PATH_V2, type(exc).__name__)
    functions = [
        node
        for node in tree.body
        if isinstance(node, ast.FunctionDef) and node.name == "_is_research_disabled_command_v1"
    ]
    if len(functions) != 1:
        _reject("RUNTIME_GUARD_COUNT", RUNTIME_TRANSITION_PATH_V2, "expected one guard")
    returns = [node for node in ast.walk(functions[0]) if isinstance(node, ast.Return)]
    if len(returns) != 1 or not isinstance(returns[0].value, ast.Compare):
        _reject("RUNTIME_GUARD_SHAPE", RUNTIME_TRANSITION_PATH_V2, "guard return drift")
    comparison = returns[0].value
    if (
        len(comparison.ops) != 1
        or not isinstance(comparison.ops[0], ast.In)
        or len(comparison.comparators) != 1
        or not isinstance(comparison.comparators[0], ast.Tuple)
    ):
        _reject(
            "RUNTIME_GUARD_SHAPE", RUNTIME_TRANSITION_PATH_V2, "guard must use tuple membership"
        )
    values: list[str] = []
    for element in comparison.comparators[0].elts:
        if (
            not isinstance(element, ast.Attribute)
            or not isinstance(element.value, ast.Name)
            or element.value.id != "GlobalCommandKindV1"
            or element.attr not in GlobalCommandKindV1.__members__
        ):
            _reject("RUNTIME_GUARD_MEMBER", RUNTIME_TRANSITION_PATH_V2, "guard member drift")
        values.append(GlobalCommandKindV1[element.attr].value)
    return values


def _cross_language_evidence(sources: dict[str, bytes]) -> dict[str, object]:
    python_commands = [command.value for command in GlobalCommandKindV1]
    rust_commands = _rust_command_domain(sources[RUST_CORE_PATH_V2])
    if rust_commands != python_commands:
        _reject("RUST_COMMAND_DOMAIN", RUST_CORE_PATH_V2, "Rust command enum differs from Python")
    runtime_disabled = _runtime_disabled_domain(sources[RUNTIME_TRANSITION_PATH_V2])
    expected_disabled = [
        command.value
        for command in GlobalCommandKindV1
        if command in M6_RESEARCH_DISABLED_COMMANDS_V1
    ]
    if runtime_disabled != expected_disabled:
        _reject(
            "RUNTIME_DISABLED_DOMAIN",
            RUNTIME_TRANSITION_PATH_V2,
            "runtime guard differs from research-disabled domain",
        )
    return {
        "python_command_domain_root": _domain_root(COMMAND_DOMAIN_V2, python_commands),
        "python_rust_command_domain_parity": True,
        "runtime_disabled_command_root": _domain_root(COMMAND_DOMAIN_V2, runtime_disabled),
        "runtime_disabled_guard_parity": True,
        "rust_command_domain_root": _domain_root(COMMAND_DOMAIN_V2, rust_commands),
    }


def _validate_o005(artifact: dict[str, object]) -> None:
    if artifact.get("schema") != "zenodex/m6-o005-requirements-floor-completion/v1":
        _reject("O005_SCHEMA", O005_ARTIFACT_PATH_V2, "completion schema drift")
    if artifact.get("status") != "RESEARCH_ONLY_O005_REQUIREMENTS_FLOOR_COMPLETE_ON_EXACT_SUBJECT":
        _reject("O005_STATUS", O005_ARTIFACT_PATH_V2, "completion status drift")
    if artifact.get("certificate_root") != O005_CERTIFICATE_ROOT_V2:
        _reject("O005_CERTIFICATE_ROOT", O005_ARTIFACT_PATH_V2, "certificate root drift")
    if artifact.get("evidence_subject") != {
        "commit": O005_EVIDENCE_SUBJECT_COMMIT_V2,
        "current_content_matches_subject": True,
        "evidence_subject_is_current_ancestor": True,
        "tree": O005_EVIDENCE_SUBJECT_TREE_V2,
    }:
        _reject("O005_EVIDENCE_SUBJECT", O005_ARTIFACT_PATH_V2, "evidence subject drift")
    expected_completion = {
        "closes_only": ["incomplete_requirements_registry"],
        "current_successor_o005_status": "COMPLETE_ON_EXACT_SUBJECT",
        "plan_baseline_gap_status": "OPEN",
        "plan_obligation_id": "O-005",
    }
    if artifact.get("o005_completion") != expected_completion:
        _reject("O005_COMPLETION", O005_ARTIFACT_PATH_V2, "bounded completion drift")
    ceiling = artifact.get("claim_ceiling")
    if type(ceiling) is not dict:
        _reject("O005_CLAIM_CEILING", O005_ARTIFACT_PATH_V2, "claim ceiling missing")
    expected_ceiling = {
        "closed_value_movement_gates": 0,
        "manifest_complete": False,
        "migration_authority": "NONE",
        "production_authority": "NONE",
        "release_authority": "NONE",
        "requirements_closed": False,
        "semantic_closure_complete": False,
        "semantic_policy_closure_complete": False,
        "semantic_target_inventory_complete": False,
        "settlement_authority": "NONE",
        "structural_mapping_complete": False,
        "value_movement_authority": "NONE",
    }
    if ceiling != expected_ceiling:
        _reject("O005_AUTHORITY_DRIFT", O005_ARTIFACT_PATH_V2, "O005 authority ceiling drift")


def _command_registry_rows(registry: dict[str, object]) -> list[object]:
    if registry.get("schema") != "zenodex/m6-command-lane-registry/v1":
        _reject("COMMAND_REGISTRY_SCHEMA", COMMAND_REGISTRY_PATH_V2, "schema drift")
    commands = registry.get("command_enum")
    decisions = registry.get("decisions")
    expected_commands = [command.value for command in GlobalCommandKindV1]
    if commands != expected_commands or type(decisions) is not list:
        _reject("COMMAND_DOMAIN", COMMAND_REGISTRY_PATH_V2, "closed command domain drift")
    rows = cast(list[object], decisions)
    row_commands = [
        cast(dict[str, object], row).get("command") if type(row) is dict else None for row in rows
    ]
    if any(type(command) is not str for command in row_commands):
        _reject("COMMAND_FIELD_TYPE", COMMAND_REGISTRY_PATH_V2, "command must be a string")
    if row_commands != expected_commands or len(set(cast(list[str], row_commands))) != len(
        expected_commands
    ):
        _reject("COMMAND_EXACT_ONCE", COMMAND_REGISTRY_PATH_V2, "mapping is not exact once")
    return rows


def _require_registry_manifest_and_authority(registry: dict[str, object]) -> None:
    pins = registry.get("source_pins")
    capability_pin = (
        cast(dict[str, object], pins).get("capability_manifest") if type(pins) is dict else None
    )
    if (
        type(capability_pin) is not dict
        or cast(dict[str, object], capability_pin).get("sha256") != CAPABILITY_MANIFEST_SHA256_V2
    ):
        _reject("COMMAND_CAPABILITY_BINDING", COMMAND_REGISTRY_PATH_V2, "manifest pin drift")
    for field in ("production_authority", "settlement_authority"):
        if registry.get(field) != "NONE":
            _reject("COMMAND_AUTHORITY", f"registry.{field}", "authority must remain NONE")
    if (
        registry.get("release_backed") is not False
        or registry.get("mounted") is not False
        or registry.get("value_movement_claim_allowed") is not False
    ):
        _reject("COMMAND_PROMOTION", COMMAND_REGISTRY_PATH_V2, "registry promotion drift")


def _project_command_rows(
    rows: list[object], lane_ids: set[str], route_ids: set[str]
) -> list[dict[str, str]]:
    disabled = {command.value for command in M6_RESEARCH_DISABLED_COMMANDS_V1}
    projected: list[dict[str, str]] = []
    for index, row in enumerate(rows):
        if type(row) is not dict:
            _reject("COMMAND_ROW_TYPE", f"decisions[{index}]", "must be an object")
        owned = cast(dict[str, object], row)
        if owned.get("status") == "ACTIVE_NEW":
            _reject("ACTIVE_NEW_MAPPING", f"decisions[{index}]", "ACTIVE_NEW is forbidden")
        if owned.get("command") in disabled and owned.get("status") != (
            "SOURCE_RESEARCH_DISABLED_NO_RELEASE"
        ):
            _reject("DISABLED_COMMAND_STATUS", f"decisions[{index}]", "disabled status drift")
        target_kind = owned.get("target_kind")
        target_id = owned.get("target_id")
        if target_kind == "LANE":
            declared = type(target_id) is str and target_id in lane_ids
        elif target_kind == "GOVERNED_ROUTE":
            declared = type(target_id) is str and target_id in route_ids
        else:
            declared = False
        if not declared:
            _reject("UNDECLARED_TARGET", f"decisions[{index}]", "target is absent from manifest")
        projected.append(
            {
                "command": cast(str, owned["command"]),
                "new_object_admission": "NOT_ACTIVE_NEW",
                "status": cast(str, owned["status"]),
                "target_id": cast(str, target_id),
                "target_kind": cast(str, target_kind),
            }
        )
    return projected


def _require_reviewed_registry_roots(registry: dict[str, object], rows: list[object]) -> None:
    decision_root = _domain_root(
        b"zenodex/m6-command-lane-decision-root/v1",
        {"decisions": rows, "schema": "zenodex/m6-command-lane-registry/v1"},
    )
    unsigned = {key: value for key, value in registry.items() if key != "registry_root"}
    derived_registry_root = _domain_root(b"zenodex/m6-command-lane-registry-root/v1", unsigned)
    if registry.get("decision_root") != EXPECTED_DECISION_ROOT_V2 or (
        decision_root != EXPECTED_DECISION_ROOT_V2
    ):
        _reject("COMMAND_DECISION_ROOT", COMMAND_REGISTRY_PATH_V2, "decision root drift")
    if registry.get("registry_root") != EXPECTED_REGISTRY_ROOT_V2:
        _reject("COMMAND_REGISTRY_ROOT", COMMAND_REGISTRY_PATH_V2, "registry root drift")
    if derived_registry_root != EXPECTED_REGISTRY_ROOT_V2:
        _reject("COMMAND_REGISTRY_ROOT_BINDING", COMMAND_REGISTRY_PATH_V2, "root is not canonical")


def _validate_command_registry(
    registry: dict[str, object],
    stage_a_commit: str,
    lane_ids: set[str],
    route_ids: set[str],
) -> list[dict[str, str]]:
    if stage_a_commit == BASE_COMMIT_V2:
        _reject("STAGE_A_IDENTITY", "stage_a_commit", "Stage A must be a distinct direct child")
    rows = _command_registry_rows(registry)
    _require_registry_manifest_and_authority(registry)
    projected = _project_command_rows(rows, lane_ids, route_ids)
    _require_reviewed_registry_roots(registry, rows)
    return projected


def _claim_ceiling() -> dict[str, object]:
    return {
        "closed_value_movement_gates": 0,
        "manifest_complete": False,
        "migration_authority": "NONE",
        "mounted": False,
        "production_authority": "NONE",
        "release_authority": "NONE",
        "release_backed": False,
        "requirements_closed": False,
        "semantic_closure_complete": False,
        "settlement_authority": "NONE",
        "value_movement_authority": "NONE",
        "value_movement_claim_allowed": False,
        "value_movement_gates": [],
        "verifier_authority": "NONE",
        "whole_economy_command_vocabulary_complete": False,
    }


def _ledger_rows(snapshot: StageASnapshotV2, vm_gate_ids: list[str]) -> list[dict[str, object]]:
    return [
        {
            "artifact_commit": O005_ARTIFACT_COMMIT_V2,
            "authority": "NONE",
            "certificate_root": O005_CERTIFICATE_ROOT_V2,
            "ledger": "OBLIGATION",
            "obligation_id": "O-005",
            "status": "COMPLETE_ON_EXACT_SUBJECT",
            "subject_commit": O005_EVIDENCE_SUBJECT_COMMIT_V2,
            "subject_tree": O005_EVIDENCE_SUBJECT_TREE_V2,
        },
        {
            "authority": "NONE",
            "closes_only": ["command_to_lane_mapping_gap"],
            "decision_root": EXPECTED_DECISION_ROOT_V2,
            "ledger": "OBLIGATION",
            "obligation_id": "O-006",
            "registry_root": EXPECTED_REGISTRY_ROOT_V2,
            "status": "COMPLETE_ON_EXACT_REGISTERED_COMMAND_DOMAIN",
            "subject_commit": snapshot.stage_a_commit,
            "subject_tree": snapshot.stage_a_tree,
        },
        {
            "authority": "NONE",
            "closed_gate_ids": [],
            "closed_gate_count": 0,
            "contributes_to": [],
            "dependency_artifact_commit": O005_ARTIFACT_COMMIT_V2,
            "dependency_subject_commit": O005_EVIDENCE_SUBJECT_COMMIT_V2,
            "ledger": "VALUE_MOVEMENT",
            "registered_gate_ids": vm_gate_ids,
            "registered_gate_ids_root": _domain_root(VM_GATE_DOMAIN_V2, vm_gate_ids),
            "status": "INITIALIZED_NO_VM_GATE_PROMOTION",
            "subject_commit": snapshot.stage_a_commit,
            "subject_tree": snapshot.stage_a_tree,
            "value_movement_claim_allowed": False,
        },
    ]


def _decode_build_sources(
    sources: dict[str, bytes],
) -> tuple[dict[str, object], dict[str, object], dict[str, object], dict[str, object]]:
    registry = _decode_object(
        sources[COMMAND_REGISTRY_PATH_V2], COMMAND_REGISTRY_PATH_V2, require_canonical=True
    )
    o005 = _decode_object(
        sources[O005_ARTIFACT_PATH_V2], O005_ARTIFACT_PATH_V2, require_canonical=True
    )
    plan = _decode_object(sources[PLAN_PATH_V2], PLAN_PATH_V2, require_canonical=False)
    manifest = _decode_object(
        sources[CAPABILITY_MANIFEST_PATH_V2],
        CAPABILITY_MANIFEST_PATH_V2,
        require_canonical=False,
    )
    return registry, o005, plan, manifest


def _source_manifest(
    snapshot: StageASnapshotV2,
) -> dict[str, object]:
    base_pins = [pin.to_json() for pin in snapshot.base_source_pins]
    stage_pins = [pin.to_json() for pin in snapshot.stage_a_source_pins]
    return {
        "base_source_pins": base_pins,
        "base_source_pins_root": source_manifest_root_v2(base_pins),
        "stage_a_source_pins": stage_pins,
        "stage_a_source_pins_root": source_manifest_root_v2(stage_pins),
    }


def _base_pin(snapshot: StageASnapshotV2, path: str) -> SourcePinV2:
    matches = [pin for pin in snapshot.base_source_pins if pin.path == path]
    if len(matches) != 1:
        _reject("BASE_SOURCE_LOOKUP", path, "expected one exact base source pin")
    return matches[0]


def _command_map(
    registry_pin: SourcePinV2,
    capability_projection: dict[str, object],
    rows: list[dict[str, str]],
    cross_language: dict[str, object],
) -> dict[str, object]:
    expected_commands = [command.value for command in GlobalCommandKindV1]
    capability_root = _domain_root(CAPABILITY_PROJECTION_DOMAIN_V2, capability_projection)
    command_domain_root = _domain_root(COMMAND_DOMAIN_V2, expected_commands)
    command_map_root = _domain_root(
        COMMAND_MAP_DOMAIN_V2,
        {
            "capability_projection_root": capability_root,
            "command_domain_root": command_domain_root,
            "rows": rows,
        },
    )
    command_count = len(GlobalCommandKindV1)
    return {
        "active_new_mapping_count": 0,
        "all_targets_declared_by_capability_manifest": True,
        "artifact_git_blob": registry_pin.git_blob_sha,
        "artifact_path": COMMAND_REGISTRY_PATH_V2,
        "artifact_sha256": registry_pin.sha256,
        "canonical_command_order": True,
        "capability_manifest_path": CAPABILITY_MANIFEST_PATH_V2,
        "capability_manifest_sha256": CAPABILITY_MANIFEST_SHA256_V2,
        "capability_projection": capability_projection,
        "capability_projection_root": capability_root,
        "command_count": command_count,
        "command_domain_root": command_domain_root,
        "command_map_root": command_map_root,
        "decision_root": EXPECTED_DECISION_ROOT_V2,
        "map_root_binds_capability_manifest": True,
        "mapping_count": command_count,
        **cross_language,
        "registered_commands_mapped_exactly_once": True,
        "registry_root": EXPECTED_REGISTRY_ROOT_V2,
        "research_disabled_command_count": len(M6_RESEARCH_DISABLED_COMMANDS_V1),
        "research_disabled_commands_active_new_count": 0,
        "rows": rows,
        "schema": "zenodex/m6-command-lane-registry/v1",
        "scope": "M6_SAFE_MOUNT_33_ONLY",
    }


def _dependency_projection(o005_pin: SourcePinV2) -> dict[str, object]:
    return {
        "artifact_commit": O005_ARTIFACT_COMMIT_V2,
        "artifact_git_blob": o005_pin.git_blob_sha,
        "artifact_path": O005_ARTIFACT_PATH_V2,
        "artifact_sha256": o005_pin.sha256,
        "authority": "NONE",
        "certificate_root": O005_CERTIFICATE_ROOT_V2,
        "obligation_id": "O-005",
        "status": "COMPLETE_ON_EXACT_SUBJECT",
        "subject_commit": O005_EVIDENCE_SUBJECT_COMMIT_V2,
        "subject_tree": O005_EVIDENCE_SUBJECT_TREE_V2,
    }


def _unsigned_artifact(
    snapshot: StageASnapshotV2,
    source_manifest: dict[str, object],
    command_map: dict[str, object],
    vm_gate_ids: list[str],
) -> dict[str, object]:
    return {
        "claim_ceiling": _claim_ceiling(),
        "command_map": command_map,
        "current_subject": {
            "commit": snapshot.stage_a_commit,
            "source_pins_root": source_manifest["stage_a_source_pins_root"],
            "status": "EXACT_STAGE_A_SOURCE_SUBJECT",
            "tree": snapshot.stage_a_tree,
        },
        "current_subject_ledger_rows": _ledger_rows(snapshot, vm_gate_ids),
        "dependency": _dependency_projection(_base_pin(snapshot, O005_ARTIFACT_PATH_V2)),
        "evidence_subject": {
            "base_commit": BASE_COMMIT_V2,
            "base_tree": BASE_TREE_V2,
            "stage_a_commit": snapshot.stage_a_commit,
            "stage_a_tree": snapshot.stage_a_tree,
        },
        "generator_command": "python3 tools/build_m6_o006_command_lane_completion_v2.py",
        "nonclaims": [
            "O006 closes only the exact registered-command structural mapping gap.",
            "No unresolved policy, whole-economy vocabulary, semantic launch, runtime mount, or release is completed.",
            "No value-movement gate or production, release, settlement, migration, verifier, or value-movement authority is promoted.",
        ],
        "o006_completion": {
            "closes_only": ["command_to_lane_mapping_gap"],
            "obligation_id": "O-006",
            "required_evidence": list(O006_REQUIRED_EVIDENCE_V2),
            "status": "COMPLETE_ON_EXACT_REGISTERED_COMMAND_DOMAIN",
            "structural_scope_only": True,
        },
        "schema": ARTIFACT_SCHEMA_V2,
        "source_manifest": source_manifest,
        "status": "RESEARCH_ONLY_O006_EXACT_COMMAND_MAP",
    }


def build_command_lane_completion_artifact_v2(snapshot: object) -> bytes:
    """Build canonical V2 bytes from one immutable Stage-A snapshot."""

    owned = _owned_snapshot(snapshot)
    sources = _validate_snapshot(owned)
    registry, o005, plan, manifest = _decode_build_sources(sources)
    capability_projection, lane_ids, route_ids = _capability_projection(manifest)
    rows = _validate_command_registry(registry, owned.stage_a_commit, lane_ids, route_ids)
    _validate_o005(o005)
    _validate_plan(plan)
    source_manifest = _source_manifest(owned)
    command_map = _command_map(
        _base_pin(owned, COMMAND_REGISTRY_PATH_V2),
        capability_projection,
        rows,
        _cross_language_evidence(sources),
    )
    unsigned = _unsigned_artifact(owned, source_manifest, command_map, _vm_gate_ids(plan))
    return canonical_json_bytes_v2({**unsigned, "certificate_root": certificate_root_v2(unsigned)})


def validate_command_lane_completion_artifact_v2(raw_artifact: object, snapshot: object) -> str:
    if type(raw_artifact) is not bytes:
        _reject("ARTIFACT_BYTES_TYPE", ARTIFACT_PATH_V2, "must be exact bytes")
    raw = raw_artifact
    if len(raw) > MAX_ARTIFACT_BYTES_V2:
        _reject("ARTIFACT_BYTE_LIMIT", ARTIFACT_PATH_V2, "artifact byte ceiling exceeded")
    expected = build_command_lane_completion_artifact_v2(snapshot)
    if raw != expected:
        _reject("ARTIFACT_BINDING_DRIFT", ARTIFACT_PATH_V2, "artifact differs from projection")
    artifact = _decode_object(raw, ARTIFACT_PATH_V2, require_canonical=True)
    root = artifact.get("certificate_root")
    if not _is_lower_hex(root, 64):
        _reject("CERTIFICATE_ROOT", ARTIFACT_PATH_V2, "certificate root is malformed")
    return cast(str, root)


__all__ = [
    "ARTIFACT_PATH_V2",
    "ARTIFACT_SCHEMA_V2",
    "BASE_COMMIT_V2",
    "BASE_SOURCE_SPECS_V2",
    "BASE_TREE_V2",
    "CHECK_SCHEMA_V2",
    "COMMAND_REGISTRY_PATH_V2",
    "CommandLaneCompletionRejectV2",
    "EXPECTED_DECISION_ROOT_V2",
    "EXPECTED_REGISTRY_ROOT_V2",
    "MAX_ARTIFACT_BYTES_V2",
    "MAX_SOURCE_BYTES_V2",
    "O005_ARTIFACT_COMMIT_V2",
    "O005_ARTIFACT_PATH_V2",
    "O005_EVIDENCE_SUBJECT_COMMIT_V2",
    "O005_EVIDENCE_SUBJECT_TREE_V2",
    "O006_REQUIRED_EVIDENCE_V2",
    "STAGE_A_SOURCE_PATHS_V2",
    "SourcePinV2",
    "StageASnapshotV2",
    "build_command_lane_completion_artifact_v2",
    "canonical_json_bytes_v2",
    "certificate_root_v2",
    "validate_command_lane_completion_artifact_v2",
]
