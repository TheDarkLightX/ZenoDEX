"""Exact static contract for the retained ZRPF V3 receipt replay lane."""

from __future__ import annotations

import hashlib
import importlib
import json
import stat
from pathlib import Path, PurePosixPath
from typing import Any, cast

REPO_ROOT = Path(__file__).resolve().parents[1]
EVIDENCE_PATH = (
    REPO_ROOT
    / "docs/research/ZRPF_V3_RETAINED_SOURCE_BUILT_REPLAY_EVIDENCE_20260710.json"
)
RECEIPT_DIRECTORY = (
    REPO_ROOT / "evidence/zrpf-v3-retained-structural-replay-v1/receipts"
)
WORKSPACE = REPO_ROOT / "zk/zrpf_risc0"

SCHEMA = "zenodex/zrpf_v3_retained_source_built_replay_evidence/v1"
REPORT_SCHEMA = "zenodex/zrpf_v3_retained_structural_replay/v1"
SOURCE_COMMIT = "d46f3e5614e39c41ebebd80b819bb2f1f6a5e522"
SOURCE_TREE = "3f1eb445d53e5c643e0ac70cf6648111a840cc86"
EXPECTED_STDOUT_SHA256 = (
    "7751395663a33c1ae58fa403346dc90618e842dd1df2f2fdc37f18599e50c288"
)
EXPECTED_STDOUT_SIZE = 5_920
EXPECTED_SOURCE_CLOSURE_FILES = 32
EXPECTED_SOURCE_CLOSURE_BYTES = 945_201
EXPECTED_SOURCE_CLOSURE_SHA256 = (
    "3a877c3f19b9141a44fa44d65ee1ef70795a0623c4bbfd103e5fafdcc41d7f73"
)
EMPTY_SHA256 = hashlib.sha256(b"").hexdigest()
ROOT_JOURNAL_HASH = (
    "2089ecc187077d4b719c8539076651753c1ead1415724c9bc788758bddfa3768"
)
ROOT_RECEIPT_SHA256 = (
    "edd25fca20b0205c2f778b866605b343922615623256abcc1a098957664c2d16"
)
MUTATION_RECEIPT_SHA256 = (
    "27c71152044124762efd5398fa6206a9627a5eae2ed9db851b1bb33783c6e985"
)
TOOLCHAIN_LOCK_PATH = "config/proof_profiles/risc0_recursive_toolchain_lock.json"
MAX_SOURCE_BYTES = 16 * 1024 * 1024
MAX_RECEIPT_BYTES = 16 * 1024 * 1024

SOURCE_FILES: tuple[tuple[str, str], ...] = (
    ("toolchain_policy", TOOLCHAIN_LOCK_PATH),
    ("state_workspace_manifest", "zk/state_proof_risc0/Cargo.toml"),
    ("state_shared_manifest", "zk/state_proof_risc0/shared/Cargo.toml"),
    ("state_shared_source", "zk/state_proof_risc0/shared/src/lib.rs"),
    ("state_shared_source", "zk/state_proof_risc0/shared/src/recursive.rs"),
    ("state_shared_source", "zk/state_proof_risc0/shared/src/surfaces.rs"),
    ("protocol_workspace_manifest", "zk/zrpf_protocol/Cargo.toml"),
    ("protocol_manifest", "zk/zrpf_protocol/protocol/Cargo.toml"),
    ("protocol_source", "zk/zrpf_protocol/protocol/src/lib.rs"),
    ("replay_workspace_config", "zk/zrpf_risc0/.cargo/config.toml"),
    ("replay_workspace_lock", "zk/zrpf_risc0/Cargo.lock"),
    ("replay_workspace_manifest", "zk/zrpf_risc0/Cargo.toml"),
    ("aggregate_manifest", "zk/zrpf_risc0/aggregate_shared/Cargo.toml"),
    ("aggregate_source", "zk/zrpf_risc0/aggregate_shared/src/input_v1.rs"),
    ("aggregate_source", "zk/zrpf_risc0/aggregate_shared/src/lib.rs"),
    ("aggregate_source", "zk/zrpf_risc0/aggregate_shared/src/structural_v1.rs"),
    ("replay_manifest", "zk/zrpf_risc0/replay_verifier/Cargo.toml"),
    ("replay_source", "zk/zrpf_risc0/replay_verifier/src/bundle.rs"),
    ("replay_source", "zk/zrpf_risc0/replay_verifier/src/error.rs"),
    ("replay_source", "zk/zrpf_risc0/replay_verifier/src/main.rs"),
    ("replay_source", "zk/zrpf_risc0/replay_verifier/src/profile.rs"),
    ("replay_test_source", "zk/zrpf_risc0/replay_verifier/src/tests.rs"),
    ("shared_manifest", "zk/zrpf_risc0/shared/Cargo.toml"),
    ("shared_source", "zk/zrpf_risc0/shared/src/adapter_input_v1.rs"),
    ("shared_source", "zk/zrpf_risc0/shared/src/hashing_v1.rs"),
    ("shared_source", "zk/zrpf_risc0/shared/src/lib.rs"),
    ("shared_source", "zk/zrpf_risc0/shared/src/risc0_binding_v1.rs"),
    ("shared_source", "zk/zrpf_risc0/shared/src/source_binding_v3.rs"),
    ("shared_source", "zk/zrpf_risc0/shared/src/source_policy_v1.rs"),
    ("shared_source", "zk/zrpf_risc0/shared/src/v1_leaf_adapter.rs"),
    ("verifier_manifest", "zk/zrpf_risc0/verifier/Cargo.toml"),
    ("verifier_source", "zk/zrpf_risc0/verifier/src/lib.rs"),
)

RECEIPTS: tuple[tuple[str, int, str], ...] = (
    (
        "adapter-leaf-0.receipt.json",
        593_416,
        "219e389be6ff9d035f86b6d73de8c4f95fae230956382d2fd63823167047b63a",
    ),
    (
        "adapter-leaf-1.receipt.json",
        593_399,
        "af45ec023d8939648c741389d9e766d5d1dd2945811652bae42e998d84bb3a82",
    ),
    (
        "adapter-leaf-2.receipt.json",
        593_136,
        "4e09c872617143e9ac360ea8059b6f2a20ab6e5ce05eb7cf51eead70f974965a",
    ),
    (
        "adapter-leaf-3.receipt.json",
        593_032,
        "7030c4a4818b31623fb137ebdac0eb8bb2af8cbeb9fdc1e8d3dcb75fc26ef8f4",
    ),
    (
        "structural-l1-left.receipt.json",
        593_161,
        "47b850237585faeee953b04dae72d21c5d87adfb710d4e914314d4a72e6c1cd5",
    ),
    (
        "structural-l1-right.receipt.json",
        593_280,
        "a6b8ceaa559bfe85fa9263fefcec9438e78ec721632fbd7a1cf651867d30348d",
    ),
    (
        "structural-l2-root.receipt.json",
        593_320,
        ROOT_RECEIPT_SHA256,
    ),
    (
        "structural-l2-root.seal-word-1-xor-lsb.receipt.json",
        593_320,
        MUTATION_RECEIPT_SHA256,
    ),
)

TRUE_CLAIMS = frozenset(
    {
        "all_expected_image_ids_verified",
        "exact_retained_artifact_bytes_bound",
        "exact_seal_mutation_rejected",
        "exact_l1_l2_journals_recomposed",
        "guest_binaries_required_by_replay_false",
        "local_cargo_rustc_rustdoc_match_pinned_artifacts",
        "normal_and_risc0_dev_mode_one_stdout_identical",
        "parent_environment_inputs_allowlisted",
        "private_source_snapshot_bound_to_anchor",
        "root_journal_and_topology_bound",
        "same_host_source_built_host_verifier_replay",
        "selected_dependency_graph_excludes_guest_build_paths",
        "seven_succinct_receipts_cryptographically_verified",
    }
)
FALSE_CLAIMS = frozenset(
    {
        "compiler_closure_identity_authenticated",
        "cross_host_reproducibility",
        "dependency_cache_identity_authenticated",
        "executing_binary_identity_authenticated",
        "guest_source_to_image_attested",
        "ledger_admission_authority",
        "linker_identity_authenticated",
        "privacy_or_zero_knowledge",
        "production_authority",
        "proof_generation_source_attested",
        "public_replay_promoted",
        "receipt_byte_determinism",
        "release_authority",
        "reproducible_build",
        "static_validation_reperforms_live_replay",
        "runtime_rootfs_identity_authenticated",
        "semantic_aggregation_or_value_conservation",
        "settlement_authority",
        "throughput_or_transaction_count",
    }
)
NON_CLAIMS = (
    "no proof-generation source or guest source-to-image provenance claim",
    "no authenticated compiler closure, linker, dependency cache, executing-binary identity, or runtime-rootfs claim",
    "no cross-host, reproducible-build, release, or public-replay promotion claim",
    "no semantic aggregation, conservation, data-availability, carry, or schedule claim",
    "no ledger-admission, settlement, production, privacy, or zero-knowledge claim",
    "no receipt-byte determinism claim",
    "operation counts are source-transition receipt counts, not transaction counts",
    "no TPS, throughput, latency, or proving-cost claim",
    "static validation does not reperform live replay; --live is required for current execution evidence",
)
EXPECTED_REPORT_AUTHORITY = {
    "guest_binaries_required_by_replay": False,
    "guest_source_to_image_attested": False,
    "ledger_admission_authority": False,
    "production_authority": False,
    "proof_generation_source_attested": False,
    "release_authority": False,
    "settlement_authority": False,
}
EXPECTED_REPORT_IMAGES = {
    "adapter": "71f282b5517fc6108988c1cc9b4601807a40ae331c0e0f0f5505d12b241e5574",
    "structural_l1": "4272be5165f65e29cb134f815d6c6fc40d7f492979f596082cac10c3f0d43c2b",
    "structural_l2": "3b858d113cb155b2946e1c733fdf5fe5592b6bf46c903d0a3cfb322099845736",
}
EXPECTED_REPORT_PROFILE = {
    "control_id": "53a7b23d07f99e5d5685e85874f5181e8486aa267a0ae607ffe9ba47c8bdda4a",
    "hashfn": "poseidon2",
    "profile_id": "risc0_succinct_poseidon2_resolve_3_0_5_v1",
    "receipt_kind": "succinct",
    "verifier_parameters": "ece5e9b8ae2cd6ea6b1827b464ff0348f9a7f4decd269c0087fdfd75098da013",
}


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def canonical_sha256(value: Any) -> str:
    raw = json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
    ).encode("ascii")
    return sha256_bytes(raw)


def canonical_evidence_bytes(value: dict[str, Any]) -> bytes:
    raw = json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n"
    return raw.encode("ascii")


def strict_json_loads(raw: bytes) -> Any:
    def unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                raise ValueError(f"duplicate JSON key: {key}")
            result[key] = value
        return result

    def reject_constant(value: str) -> None:
        raise ValueError(f"non-finite JSON number: {value}")

    return json.loads(
        raw.decode("utf-8"),
        object_pairs_hook=unique_object,
        parse_constant=reject_constant,
    )


def _safe_relative_path(value: str) -> bool:
    path = PurePosixPath(value)
    return bool(value) and not path.is_absolute() and ".." not in path.parts


def _regular_file_bytes(root: Path, relative: str, maximum: int) -> bytes:
    if not _safe_relative_path(relative):
        raise ValueError(f"unsafe relative path: {relative}")
    root = root.resolve(strict=True)
    candidate = root / relative
    cursor = root
    for part in PurePosixPath(relative).parts:
        cursor /= part
        if cursor.is_symlink():
            raise ValueError(f"symlinked path component: {relative}")
    metadata = candidate.lstat()
    resolved = candidate.resolve(strict=True)
    if (
        stat.S_ISLNK(metadata.st_mode)
        or not stat.S_ISREG(metadata.st_mode)
        or not resolved.is_relative_to(root)
        or metadata.st_size <= 0
        or metadata.st_size > maximum
    ):
        raise ValueError(f"unsafe or unbounded file: {relative}")
    raw = candidate.read_bytes()
    if len(raw) != metadata.st_size:
        raise ValueError(f"file changed while reading: {relative}")
    return raw


def source_closure(repo_root: Path = REPO_ROOT) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    hasher = hashlib.sha256()
    total_bytes = 0
    for role, relative in sorted(SOURCE_FILES, key=lambda item: item[1]):
        raw = _regular_file_bytes(repo_root, relative, MAX_SOURCE_BYTES)
        digest = sha256_bytes(raw)
        size = len(raw)
        rows.append({"path": relative, "role": role, "sha256": digest, "size_bytes": size})
        hasher.update(f"{role}\0{relative}\0{digest}\0{size}\n".encode("utf-8"))
        total_bytes += size
    return {
        "definition": (
            "sha256(rows ordered by path: "
            "role\\0path\\0sha256\\0size_bytes\\n)"
        ),
        "file_count": len(rows),
        "files": rows,
        "sha256": hasher.hexdigest(),
        "total_bytes": total_bytes,
    }


def retained_receipt_set(receipt_directory: Path = RECEIPT_DIRECTORY) -> dict[str, Any]:
    if receipt_directory.is_symlink() or not receipt_directory.is_dir():
        raise ValueError("retained receipt directory is not a real directory")
    expected_names = {name for name, _, _ in RECEIPTS}
    actual_names = {path.name for path in receipt_directory.iterdir()}
    if actual_names != expected_names:
        raise ValueError("retained receipt inventory mismatch")
    rows: list[dict[str, Any]] = []
    hasher = hashlib.sha256()
    total_bytes = 0
    for name, expected_size, expected_digest in RECEIPTS:
        raw = _regular_file_bytes(receipt_directory, name, MAX_RECEIPT_BYTES)
        digest = sha256_bytes(raw)
        if len(raw) != expected_size or digest != expected_digest:
            raise ValueError(f"retained receipt binding mismatch: {name}")
        strict_json_loads(raw)
        rows.append({"name": name, "sha256": digest, "size_bytes": len(raw)})
        hasher.update(f"{name}\0{len(raw)}\0{digest}\n".encode("utf-8"))
        total_bytes += len(raw)
    return {
        "artifact_count": len(rows),
        "artifacts": rows,
        "definition": "sha256(sorted name\\0size_bytes\\0sha256\\n)",
        "sha256": hasher.hexdigest(),
        "total_bytes": total_bytes,
    }


def expected_evidence(repo_root: Path = REPO_ROOT) -> dict[str, Any]:
    module_prefix = "tools." if __package__ else ""
    manifest = importlib.import_module(
        f"{module_prefix}zrpf_v3_replay_evidence_manifest"
    )
    return cast(dict[str, Any], manifest.expected_evidence(repo_root))


def validate_replay_report(raw: bytes) -> tuple[dict[str, Any] | None, list[str]]:
    errors: list[str] = []
    if len(raw) != EXPECTED_STDOUT_SIZE or sha256_bytes(raw) != EXPECTED_STDOUT_SHA256:
        errors.append("replay stdout binding mismatch")
    try:
        report = strict_json_loads(raw)
    except (UnicodeDecodeError, json.JSONDecodeError, ValueError) as exc:
        return None, errors + [f"replay stdout JSON rejected: {exc}"]
    if not isinstance(report, dict):
        return None, errors + ["replay stdout is not an object"]
    if report.get("schema") != REPORT_SCHEMA or report.get("ok") is not True:
        errors.append("replay report schema or acceptance mismatch")
    if report.get("status") != "retained_exact_four_leaf_two_level_receipts_verified":
        errors.append("replay report status mismatch")
    if report.get("authority") != EXPECTED_REPORT_AUTHORITY:
        errors.append("replay authority boundary mismatch")
    if report.get("expected_images") != EXPECTED_REPORT_IMAGES:
        errors.append("replay image boundary mismatch")
    if report.get("receipt_security_profile") != EXPECTED_REPORT_PROFILE:
        errors.append("replay receipt profile mismatch")
    leaf_hashes = _receipt_hashes(report.get("leaf_receipts"))
    level_one_hashes = _receipt_hashes(report.get("level_one_receipts"))
    if leaf_hashes != [digest for _, _, digest in RECEIPTS[:4]]:
        errors.append("leaf receipt report mismatch")
    if level_one_hashes != [digest for _, _, digest in RECEIPTS[4:6]]:
        errors.append("level-one receipt report mismatch")
    root = report.get("root")
    count_unit = root.get("count_unit") if isinstance(root, dict) else None
    if (
        not isinstance(root, dict)
        or not isinstance(count_unit, dict)
        or any(
            (
                root.get("journal_hash") != ROOT_JOURNAL_HASH,
                root.get("receipt_sha256") != ROOT_RECEIPT_SHA256,
                root.get("leaf_count") != 4,
                root.get("operation_count") != 4,
                root.get("subtree_node_count") != 7,
                count_unit.get("label") != "source_transition_receipt_v3",
            )
        )
    ):
        errors.append("root report mismatch")
    mutation = report.get("mutation_control")
    if not isinstance(mutation, dict) or any(
        (
            mutation.get("candidate_accepted") is not False,
            mutation.get("mutated_receipt_sha256") != MUTATION_RECEIPT_SHA256,
            mutation.get("reject_code") != "receipt_verification_failed",
            mutation.get("source_receipt_sha256") != ROOT_RECEIPT_SHA256,
        )
    ):
        errors.append("mutation report mismatch")
    return report, errors


def _receipt_hashes(value: Any) -> list[Any] | None:
    if not isinstance(value, list) or any(not isinstance(row, dict) for row in value):
        return None
    return [row.get("receipt_sha256") for row in value]
