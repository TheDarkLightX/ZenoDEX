#!/usr/bin/env python3
"""Validate the bounded current-image V1/V2 active reproof reference."""

from __future__ import annotations

import argparse
import base64
import hashlib
import json
import stat
import subprocess
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
REFERENCE = ROOT / "config/proof_profiles/risc0_recursive_active_reproof_reference_v3.json"
EVIDENCE = ROOT / "evidence/risc0-recursive-active-reproof-v3"
SCHEMA = "zenodex/risc0_recursive_active_reproof_reference/v3"
BASE_REVISION = "7b495df837e1a877d8c49da0f06ebce85661e39e"
INVENTORY_DOMAIN = b"zenodex.risc0.active_reproof.inventory.v3"
V1_CHILD_JOURNAL_HASH_DOMAIN = b"zenodex.risc0.recursive.child_journal_hash.v1"
V2_IMMEDIATE_CLAIMS_ROOT_DOMAIN = b"zenodex.risc0.recursive.immediate_child_claims_root.v2"
V2_IMMEDIATE_JOURNALS_ROOT_DOMAIN = b"zenodex.risc0.recursive.immediate_child_journals_root.v2"
MAX_JSON_BYTES = 16 * 1024 * 1024

PROMOTION_SOURCE_PATHS = (
    ".github/workflows/zrpf-assurance.yml",
    "config/proof_profiles/risc0_dependency_audit_policy_v2.json",
    "docs/RISC0_CIRCUIT_QUALITY_CBC_SPEC.md",
    "docs/research/RECURSIVE_STARK_ACTIVE_REPROOF_V3_SPEC_20260712.md",
    "docs/research/RECURSIVE_STARK_CBC_MATRIX_20260709.json",
    "docs/research/RECURSIVE_STARK_VERICODING_SPEC_20260709.md",
    "docs/research/RISC0_SPIN_099_LOCK_DELTA_20260804.patch",
    "docs/research/RISC0_SPIN_099_PROOF_IDENTITY_COMPARISON_20260804.json",
    "tests/integration/test_check_risc0_dependency_audit.py",
    "tests/test_check_recursive_stark_cbc_spec.py",
    "tests/test_check_risc0_recursive_active_reproof_v3.py",
    "tests/test_risc0_recursive_v2_active_reproof_harness.py",
    "tests/test_zrpf_assurance_workflow.py",
    "tools/build_risc0_recursive_active_reproof_reference_v3.py",
    "tools/check_recursive_stark_cbc_spec.py",
    "tools/check_risc0_dependency_audit.py",
    "tools/check_risc0_recursive_active_reproof_v3.py",
)

SOURCE_ROOTS = {
    "state_proof_risc0": (
        "zk/state_proof_risc0",
        34,
        "91c144aa63d406b0e3263155ccfda3b813c4d465c8963c8c54013ff49e3cb061",
    ),
    "recursive_stark_v2_risc0": (
        "zk/recursive_stark_v2_risc0",
        16,
        "715d8596e771bbe4b59157657f35fdb5134851bc0071c8c5438b42d724bcdf0f",
    ),
    "recursive_stark_v2_active_reproof_risc0": (
        "zk/recursive_stark_v2_active_reproof_risc0",
        6,
        "86b326d2aaf153d36479c9920081fa98b20c550b0c677996075976f3db93dda4",
    ),
}
EVIDENCE_COUNT = 25
EVIDENCE_ROOT = "dcca61fcbe665df1a8db28451401eca8fc71b5acbab05e154f6177b60aa31681"
V1_IDS = {
    "aggregate": "c4bde351d48e8e775c2e831fc37fb98a9e45ed59455afe761572d2e11ceed6c4",
    "spot": "59930b80d7f250923cf6d88aab34e431033f35f60343339c37e737fa30847dab",
    "zusd": "17d5dd12874cf18efc00869350bbc9c9b43c996629f52957e96e1a8c63e1cdef",
}
V2_ID = "0a678da608708af7bd6c35bf825ffe8815efd67f0a8041466929fb2fcda7ae68"
PROGRAMS = [
    {
        "image_id": V1_IDS["aggregate"],
        "image_id_words": [
            1373879748,
            2005831380,
            528690780,
            2327412675,
            1508722078,
            1996380741,
            3788665365,
            3302419996,
        ],
        "name": "v1_aggregate",
        "program_bytes": 273600,
        "program_sha256": "f139051c034a9db05725a739655a0de00a81ba79dbf22d1526018ca17af599d0",
    },
    {
        "image_id": V1_IDS["spot"],
        "image_id_words": [
            2148242265,
            2454778583,
            2329474620,
            837039275,
            4130684675,
            2620605187,
            4197967671,
            2877129776,
        ],
        "name": "v1_spot",
        "program_bytes": 757268,
        "program_sha256": "933ff2c73c9ed6eed4a9c145f89ae58792e03aca3cecd17da56e4919913a0bdf",
    },
    {
        "image_id": V1_IDS["zusd"],
        "image_id_words": [
            316527895,
            2398178439,
            2475032828,
            3385441104,
            1721318580,
            1462367529,
            2350542569,
            4023247203,
        ],
        "name": "v1_zusd",
        "program_bytes": 273732,
        "program_sha256": "c7f23f463408c3eaecd317fa76228fe34fb3a1477accb7763f54e7cbfe393b99",
    },
    {
        "image_id": V2_ID,
        "image_id_words": [
            2794284810,
            4153045000,
            3207949501,
            2298371970,
            2144792341,
            1178697738,
            804989289,
            1756276685,
        ],
        "name": "v2_aggregate",
        "program_bytes": 448868,
        "program_sha256": "2f94b5e0320c601f7cae96c7aac1e85604c433b475ad2a7edd86ba9da5845b35",
    },
]
HOST_BINARIES = [
    {
        "name": "v1_cli",
        "sha256": "a37fca109ed92667a530ba30db35da19884214ada49ca3246dd0d5214a672856",
        "size_bytes": 14171024,
    },
    {
        "name": "v2_active_harness",
        "sha256": "5fe237377d6db2ded3f8b91f4f9633d2bd7eb25b9ae1e9b063e2707ce5d1adcc",
        "size_bytes": 9754528,
    },
    {
        "name": "v1_active_verifier",
        "sha256": "3556844a1c760c9d0199aa1aa6a2de64d9d0c537bc8740e5a07cebe8b76f97cc",
        "size_bytes": 2856208,
    },
    {
        "name": "v2_pair_verifier",
        "sha256": "4230b474463ec1ff988fc12df2f2a123dec6db506cbda68c84a26502cb42bff9",
        "size_bytes": 2676184,
    },
]
TOOLCHAIN = {
    "cargo_risczero_sha256": "45aba69689cef25d81237f3ff62456fc96ff1e23f75adfcd16f7c8b8c1606619",
    "cargo_sha256": "b1d3a17e834a1cd593634d8f6e7866bbc498e56f5205560c7418bae6ee4447da",
    "r0vm_sha256": "36c016a5bb2ded5bd1f8f92cc487e6ffaeb1e95ec05850c983081a0f716b515b",
    "rust_version": "1.94.1-dev",
    "rustc_sha256": "e7fd8dcc397b4e4756cdb8ceb1851347daf326234b78abea3d42d4e61ad5e8e5",
    "rustdoc_sha256": "5e04b4833f32a4d9d07269a05f254a66591cb5ea1623221bfadac260671036cf",
}
SECURITY = {
    "control_id": "53a7b23d07f99e5d5685e85874f5181e8486aa267a0ae607ffe9ba47c8bdda4a",
    "hashfn": "poseidon2",
    "receipt_kind": "succinct",
    "verifier_parameters": "ece5e9b8ae2cd6ea6b1827b464ff0348f9a7f4decd269c0087fdfd75098da013",
}
V2_NONCLAIMS = [
    "migration profile: the transition leaf still uses the authenticated v1 leaf journal",
    "the harness-local v1 image allowlist has no release or registry authority",
    "one-leaf smoke does not establish production throughput or proving-cost bounds",
    "this harness does not grant release, settlement, or ledger-admission authority",
    "schedule and data-availability fields remain commitment-only in this profile",
    "strict closed subtrees do not support cross-subtree value or message flows",
    "this local run does not establish cross-host reproducibility or privacy",
]
CLAIMS = {
    "accepted_status": "same_host_bounded_current_image_two_leaf_reproof",
    "arbitrary_depth_recursion": False,
    "complete_build_input_closure_verified": False,
    "cross_host_reproducibility": False,
    "data_availability_verified": False,
    "durable_atomic_ledger_admission": False,
    "fresh_v1_leaf_receipts_verified": True,
    "fresh_v1_root_receipt_verified": True,
    "fresh_v2_inner_and_root_receipts_verified": True,
    "general_fanout_promotion": False,
    "guest_elf_hashes_recorded": True,
    "guest_elf_files_retained": False,
    "git_worktree_clean_verified": False,
    "host_binary_files_retained": False,
    "network_isolation": False,
    "privacy_or_zero_knowledge": False,
    "production_authority": False,
    "proofs_regenerated": True,
    "proof_byte_determinism": False,
    "proving_execution_provenance_authenticated": False,
    "public_replay": False,
    "release_authority": False,
    "reproducible_release": False,
    "sandbox_assurance": False,
    "semantic_asset_conservation": False,
    "settlement_authority": False,
    "source_inventory_verified": True,
    "toolchain_binary_hashes_recorded": True,
    "retained_receipt_replay_verified": True,
    "source_base_revision_verified": True,
    "toolchain_binaries_reauthenticated_by_checker": False,
}


class CheckError(ValueError):
    pass


def _pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise CheckError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def load_json(path: Path) -> Any:
    info = path.lstat()
    if not stat.S_ISREG(info.st_mode) or info.st_size > MAX_JSON_BYTES:
        raise CheckError(f"not a bounded regular file: {path}")
    data = path.read_bytes()
    value = json.loads(data, object_pairs_hook=_pairs)
    canonical = json.dumps(value, separators=(",", ":"), ensure_ascii=True).encode()
    if data != canonical:
        raise CheckError(f"noncanonical JSON: {path}")
    return value


def file_record(path: Path, *, repo_root: Path = ROOT) -> dict[str, Any]:
    data = path.read_bytes()
    return {
        "path": path.relative_to(repo_root).as_posix(),
        "sha256": hashlib.sha256(data).hexdigest(),
        "size_bytes": len(data),
    }


def inventory(base: Path, *, repo_root: Path = ROOT) -> list[dict[str, Any]]:
    records = []
    for path in sorted(base.rglob("*")):
        info = path.lstat()
        if stat.S_ISLNK(info.st_mode):
            raise CheckError(f"inventory symlink rejected: {path}")
        if path.name == "target" and stat.S_ISDIR(info.st_mode):
            raise CheckError(f"in-scope target directory rejected: {path}")
        if stat.S_ISDIR(info.st_mode):
            continue
        if not stat.S_ISREG(info.st_mode):
            raise CheckError(f"inventory special file rejected: {path}")
        records.append(file_record(path, repo_root=repo_root))
    return records


def explicit_inventory(
    relative_paths: tuple[str, ...], *, repo_root: Path = ROOT
) -> list[dict[str, Any]]:
    records = []
    for relative in relative_paths:
        path = repo_root / relative
        info = path.lstat()
        if not stat.S_ISREG(info.st_mode) or stat.S_ISLNK(info.st_mode):
            raise CheckError(f"promotion source is not a regular file: {path}")
        records.append(file_record(path, repo_root=repo_root))
    return records


def inventory_root(records: list[dict[str, Any]]) -> str:
    digest = hashlib.sha256(INVENTORY_DOMAIN)
    digest.update(len(records).to_bytes(4, "big"))
    for record in records:
        raw_path = record["path"].encode()
        digest.update(len(raw_path).to_bytes(4, "big"))
        digest.update(raw_path)
        digest.update(record["size_bytes"].to_bytes(8, "big"))
        digest.update(bytes.fromhex(record["sha256"]))
    return digest.hexdigest()


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise CheckError(message)


def _require_exact_typed(value: Any, expected: Any, message: str) -> None:
    if type(value) is not type(expected):
        raise CheckError(message)
    if isinstance(expected, dict):
        _require(set(value) == set(expected), message)
        for key, expected_item in expected.items():
            _require_exact_typed(value[key], expected_item, message)
        return
    if isinstance(expected, list):
        _require(len(value) == len(expected), message)
        for item, expected_item in zip(value, expected, strict=True):
            _require_exact_typed(item, expected_item, message)
        return
    _require(value == expected, message)


def _git_output(repo_root: Path, *args: str) -> str:
    completed = subprocess.run(
        ["git", "-C", str(repo_root), *args],
        check=False,
        capture_output=True,
        text=True,
        timeout=10,
    )
    if completed.returncode != 0:
        detail = completed.stderr.strip() or completed.stdout.strip() or "git command failed"
        raise CheckError(detail)
    return completed.stdout.strip()


def _check_git_base(repo_root: Path) -> None:
    _require(_git_output(repo_root, "rev-parse", "--show-toplevel") == str(repo_root), "repo root mismatch")
    _git_output(repo_root, "cat-file", "-e", f"{BASE_REVISION}^{{commit}}")
    _git_output(repo_root, "merge-base", "--is-ancestor", BASE_REVISION, "HEAD")


def _receipt_bytes(artifact: dict[str, Any]) -> bytes:
    encoded = artifact["proof"]
    _require(type(encoded) is str, "receipt proof must be base64 text")
    raw = base64.b64decode(encoded, validate=True)
    _require(base64.b64encode(raw).decode("ascii") == encoded, "receipt base64 is noncanonical")
    return raw


def _authenticated_journal_bytes(artifact: dict[str, Any]) -> bytes:
    receipt = _decode_canonical_receipt(artifact)
    values = receipt["journal"]["bytes"]
    _require(type(values) is list and bool(values), "authenticated journal bytes missing")
    _require(all(type(value) is int and 0 <= value <= 255 for value in values), "journal byte invalid")
    return bytes(values)


def _v1_claim_hash(image_id_words: Any, journal: bytes) -> str:
    _require(type(image_id_words) is list and len(image_id_words) == 8, "V1 image ID word count mismatch")
    digest = hashlib.sha256(b"zenodex.risc0.recursive.child_verification_claim_hash.v1")
    for word in image_id_words:
        _require(type(word) is int and 0 <= word <= 0xFFFFFFFF, "V1 image ID word invalid")
        digest.update(word.to_bytes(4, "big"))
    digest.update(len(journal).to_bytes(4, "big"))
    digest.update(journal)
    return digest.hexdigest()


def _v1_journal_hash(journal: bytes) -> str:
    _require(bool(journal), "V1 journal bytes empty")
    digest = hashlib.sha256(V1_CHILD_JOURNAL_HASH_DOMAIN)
    digest.update(len(journal).to_bytes(4, "big"))
    digest.update(journal)
    return digest.hexdigest()


def _root_list_hash(domain: bytes, values: list[str]) -> str:
    digest = hashlib.sha256(domain)
    digest.update(len(values).to_bytes(4, "big"))
    for value in values:
        _require(type(value) is str and len(value) == 64, "root-list value invalid")
        try:
            raw = bytes.fromhex(value)
        except ValueError as error:
            raise CheckError("root-list value invalid") from error
        _require(len(raw) == 32, "root-list value invalid")
        digest.update(raw)
    return digest.hexdigest()


def _v1_claims_root(claims: list[str]) -> str:
    digest = hashlib.sha256(b"zenodex.risc0.recursive.child_verification_claims_root.v1")
    digest.update(len(claims).to_bytes(4, "big"))
    for claim in claims:
        digest.update(bytes.fromhex(claim))
    return digest.hexdigest()


def _hex32(values: Any, message: str) -> str:
    _require(
        type(values) is list
        and len(values) == 32
        and all(type(value) is int and 0 <= value <= 255 for value in values),
        message,
    )
    return bytes(values).hex()


def _difference_paths(left: Any, right: Any, path: tuple[Any, ...] = ()) -> list[tuple[Any, ...]]:
    if type(left) is not type(right):
        return [path]
    if isinstance(left, dict):
        if set(left) != set(right):
            return [path]
        return [
            difference
            for key in left
            for difference in _difference_paths(left[key], right[key], (*path, key))
        ]
    if isinstance(left, list):
        if len(left) != len(right):
            return [path]
        return [
            difference
            for index, (left_item, right_item) in enumerate(zip(left, right, strict=True))
            for difference in _difference_paths(left_item, right_item, (*path, index))
        ]
    return [] if left == right else [path]


def _decode_canonical_receipt(artifact: dict[str, Any]) -> dict[str, Any]:
    raw = _receipt_bytes(artifact)
    receipt = json.loads(raw, object_pairs_hook=_pairs)
    canonical = json.dumps(receipt, separators=(",", ":"), ensure_ascii=True).encode()
    _require(raw == canonical, "receipt JSON is noncanonical")
    return receipt


def _risc0_digest_words_hex(value: Any, label: str) -> str:
    _require(type(value) is list and len(value) == 8, f"{label} word count mismatch")
    raw = bytearray()
    for word in value:
        _require(type(word) is int and 0 <= word <= 0xFFFFFFFF, f"{label} word invalid")
        raw.extend(word.to_bytes(4, "little"))
    return bytes(raw).hex()


def _check_succinct_security_profile(artifact: dict[str, Any]) -> None:
    receipt = _decode_canonical_receipt(artifact)
    inner = receipt.get("inner")
    if not isinstance(inner, dict):
        raise CheckError("receipt kind mismatch")
    _require(set(inner) == {"Succinct"}, "receipt kind mismatch")
    succinct = inner["Succinct"]
    metadata = receipt.get("metadata")
    if not isinstance(succinct, dict) or not isinstance(metadata, dict):
        raise CheckError("receipt security shape mismatch")
    _require(succinct.get("hashfn") == SECURITY["hashfn"], "receipt hash function mismatch")
    _require(
        _risc0_digest_words_hex(succinct.get("control_id"), "receipt control ID")
        == SECURITY["control_id"],
        "receipt control ID mismatch",
    )
    _require(
        _risc0_digest_words_hex(
            metadata.get("verifier_parameters"), "receipt verifier parameters"
        )
        == SECURITY["verifier_parameters"],
        "receipt verifier parameters mismatch",
    )


def _check_exact_seal_mutation(source: dict[str, Any], mutated: dict[str, Any]) -> None:
    _require(
        _difference_paths(source, mutated) == [("proof",)], "seal mutation changed outer fields"
    )
    source_receipt = _decode_canonical_receipt(source)
    mutated_receipt = _decode_canonical_receipt(mutated)
    expected_path = ("inner", "Succinct", "seal", 1)
    _require(
        _difference_paths(source_receipt, mutated_receipt) == [expected_path],
        "seal mutation changed fields outside word one",
    )
    source_word = source_receipt["inner"]["Succinct"]["seal"][1]
    mutated_word = mutated_receipt["inner"]["Succinct"]["seal"][1]
    _require(
        type(source_word) is int and mutated_word == source_word ^ 1, "seal mutation is not XOR-LSB"
    )


def _require_single_mutation(
    source: dict[str, Any], mutated: dict[str, Any], expected_path: tuple[Any, ...]
) -> None:
    _require(
        _difference_paths(source, mutated) == [expected_path], "control mutation surface mismatch"
    )


def _check_sources(reference: dict[str, Any], *, repo_root: Path) -> None:
    expected = []
    for workspace_id, (relative, count, root_hash) in SOURCE_ROOTS.items():
        records = inventory(repo_root / relative, repo_root=repo_root)
        _require(len(records) == count, f"{workspace_id} source count mismatch")
        _require(inventory_root(records) == root_hash, f"{workspace_id} source root mismatch")
        expected.append(
            {
                "file_count": count,
                "inventory_root": root_hash,
                "path": relative,
                "workspace_id": workspace_id,
            }
        )
    _require(reference["source_inventories"] == expected, "source inventory reference mismatch")

    promotion_records = explicit_inventory(PROMOTION_SOURCE_PATHS, repo_root=repo_root)
    expected_promotion = {
        "file_count": len(promotion_records),
        "files": promotion_records,
        "inventory_root": inventory_root(promotion_records),
    }
    _require(
        reference["promotion_source_inventory"] == expected_promotion,
        "promotion source inventory mismatch",
    )


def _check_evidence(reference: dict[str, Any], *, repo_root: Path) -> None:
    evidence = repo_root / "evidence/risc0-recursive-active-reproof-v3"
    records = inventory(evidence, repo_root=repo_root)
    _require(len(records) == EVIDENCE_COUNT, "evidence file count mismatch")
    _require(inventory_root(records) == EVIDENCE_ROOT, "evidence inventory root mismatch")
    _require(
        reference["evidence"]
        == {"file_count": EVIDENCE_COUNT, "files": records, "inventory_root": EVIDENCE_ROOT},
        "evidence reference mismatch",
    )

    spot = load_json(evidence / "receipts/v1-spot.proof.json")
    zusd = load_json(evidence / "receipts/v1-zusd.proof.json")
    root = load_json(evidence / "receipts/v1-root.proof.json")
    for artifact, image_id, profile in (
        (spot, V1_IDS["spot"], "recursive_spot_leaf_v1"),
        (zusd, V1_IDS["zusd"], "recursive_zusd_leaf_v1"),
        (root, V1_IDS["aggregate"], "recursive_epoch_v1"),
    ):
        meta = artifact["meta"]
        _require(
            meta["risc0_image_id"] == image_id and meta["proof_profile"] == profile,
            "V1 receipt identity mismatch",
        )
        _require(
            meta["receipt_kind"] == "succinct" and meta["receipt_hashfn"] == SECURITY["hashfn"],
            "V1 receipt security mismatch",
        )
    _require(
        type(root["meta"]["child_count"]) is int and root["meta"]["child_count"] == 2,
        "V1 root child count mismatch",
    )

    v1_request = load_json(evidence / "requests/v1-root.verify.request.json")
    _require(v1_request["proof"] == root, "V1 verification request proof mismatch")
    children = v1_request["recursive_input"]["children"]
    _require(type(children) is list and len(children) == 2, "V1 disclosure child count mismatch")

    leaf_artifacts = (spot, zusd)
    leaf_programs = (PROGRAMS[1], PROGRAMS[2])
    computed_claims = []
    computed_journals = []
    receipt_sha256s = []
    for child, artifact, program in zip(children, leaf_artifacts, leaf_programs, strict=True):
        journal = _authenticated_journal_bytes(artifact)
        _require(child["child_journal_bytes"] == list(journal), "V1 child journal disclosure mismatch")
        words = program["image_id_words"]
        _require(child["descriptor"]["child_image_id"] == words, "V1 child image disclosure mismatch")
        claim = _v1_claim_hash(words, journal)
        _require(
            child["descriptor"]["child_verification_claim_hash"] == list(bytes.fromhex(claim)),
            "V1 child verification claim mismatch",
        )
        computed_claims.append(claim)
        computed_journals.append(_v1_journal_hash(journal))
        receipt_sha256s.append(hashlib.sha256(_receipt_bytes(artifact)).hexdigest())

    v1_verify = load_json(evidence / "reports/v1-root.verify.json")
    expected_claims = [f"0x{claim}" for claim in computed_claims]
    root_journal = _authenticated_journal_bytes(root)
    root_journal_digest = hashlib.sha256(
        b"zenodex.risc0.recursive.epoch_journal_bytes_hash.v1"
        + len(root_journal).to_bytes(4, "big")
        + root_journal
    ).hexdigest()
    root_meta = root["meta"]
    expected_facts = {
        "accepted_receipt_ids": [],
        "accepted_receipts_root": f"0x{root_meta['accepted_receipts_root']}",
        "aggregate_image_id": V1_IDS["aggregate"],
        "chain_id": root_meta["chain_id"],
        "child_verification_claim_hashes": expected_claims,
        "child_verification_claims_root": f"0x{_v1_claims_root(computed_claims)}",
        "cross_shard_message_ids": [],
        "cross_shard_message_ids_root": f"0x{root_meta['cross_shard_message_ids_root']}",
        "epoch_id": root_meta["epoch_id"],
        "proof_profile": "recursive_epoch_v1",
        "public_policy_hash": f"0x{root_meta['public_policy_hash']}",
        "receipt_codec": "risc0_receipt_canonical_serde_json_depth128_v1",
        "receipt_control_id": SECURITY["control_id"],
        "receipt_hashfn": SECURITY["hashfn"],
        "receipt_kind": SECURITY["receipt_kind"],
        "receipt_verifier_parameters": SECURITY["verifier_parameters"],
        "root_journal_hash": f"0x{root_journal_digest}",
        "schema": "zenodex.verified_recursive_stark_root_facts.v1",
        "verifier_set_root": f"0x{root_meta['verifier_set_root']}",
    }
    _require_exact_typed(
        v1_verify,
        {"ok": True, "verified_recursive_facts": expected_facts},
        "V1 positive transcript mismatch",
    )
    v1_active_verify = load_json(evidence / "reports/v1-root.active-verifier.json")
    _require_exact_typed(
        v1_active_verify,
        {
            "aggregate_v1_image_id": V1_IDS["aggregate"],
            "child_verification_claims_root": root_meta["child_verification_claims_root"],
            "ok": True,
            "receipt_sha256": hashlib.sha256(_receipt_bytes(root)).hexdigest(),
            "root_journal_hash": root_journal_digest,
            "status": "recursive_v1_root_verified",
        },
        "V1 active verifier transcript mismatch",
    )

    inner = load_json(evidence / "receipts/v2-inner.proof.json")
    v2_root = load_json(evidence / "receipts/v2-root.proof.json")
    expected_nodes = (
        (inner, "recursive_closed_subtree_v2", "closed_subtree_over_leaves", 2, 2),
        (v2_root, "recursive_epoch_root_v2", "epoch_root_over_subtrees", 1, 2),
    )
    for artifact, profile, level, immediate, flat in expected_nodes:
        journal = artifact["journal"]
        _require(
            artifact["risc0_image_id"] == V2_ID and artifact["receipt_kind"] == "succinct",
            "V2 receipt identity mismatch",
        )
        _check_succinct_security_profile(artifact)
        _require(
            (
                journal["profile"],
                journal["level"],
                journal["immediate_child_count"],
                journal["flat_leaf_count"],
            )
            == (profile, level, immediate, flat),
            "V2 topology mismatch",
        )

    inner_journal = inner["journal"]
    _require(
        _hex32(
            inner_journal["immediate_child_claims_root"],
            "V2 inner immediate claim root invalid",
        )
        == _root_list_hash(V2_IMMEDIATE_CLAIMS_ROOT_DOMAIN, computed_claims),
        "V2 inner does not bind retained V1 leaf claims",
    )
    _require(
        _hex32(
            inner_journal["immediate_child_journals_root"],
            "V2 inner immediate journal root invalid",
        )
        == _root_list_hash(V2_IMMEDIATE_JOURNALS_ROOT_DOMAIN, computed_journals),
        "V2 inner does not bind retained V1 leaf journals",
    )

    pair = load_json(evidence / "reports/v2-pair.verify.json")
    _require_exact_typed(
        pair,
        {
            "aggregate_v2_image_id": V2_ID,
            "inner_receipt_sha256": inner["receipt_sha256"],
            "ok": True,
            "root_receipt_sha256": v2_root["receipt_sha256"],
            "status": "recursive_v2_pair_verified",
        },
        "V2 pair transcript mismatch",
    )
    forward = load_json(evidence / "reports/v2-forward.dry-run.json")
    reverse = load_json(evidence / "reports/v2-reversed.dry-run.json")
    _require_exact_typed(forward["ok"], True, "forward dry-run status mismatch")
    _require_exact_typed(reverse["ok"], True, "reverse dry-run status mismatch")
    _require(
        forward["input_leaf_receipt_sha256s"] == receipt_sha256s
        and reverse["input_leaf_receipt_sha256s"] == receipt_sha256s,
        "V2 dry runs do not bind retained V1 leaf receipts",
    )
    _require(
        forward["inner"] == reverse["inner"] and forward["epoch_root"] == reverse["epoch_root"],
        "leaf-order replay mismatch",
    )
    expected_report_nodes = []
    for report_node, artifact in (
        (forward["inner"], inner),
        (forward["epoch_root"], v2_root),
    ):
        journal = artifact["journal"]
        expected_summary = {
            "aggregation_scope_hash": _hex32(
                journal["aggregation_scope_hash"], "V2 aggregation scope hash invalid"
            ),
            "assigned_leaf_ids_root": _hex32(
                journal["assigned_leaf_ids_root"], "V2 assigned leaf root invalid"
            ),
            "descendant_claims_root": _hex32(
                journal["descendant_claims_root"], "V2 descendant claims root invalid"
            ),
            "flat_leaf_count": journal["flat_leaf_count"],
            "flat_v1_post_state_root": _hex32(
                journal["flat_v1_projection"]["post_state_root"],
                "V2 flat post-state root invalid",
            ),
            "flat_v1_statement_hash": _hex32(
                journal["flat_v1_projection"]["statement_hash"],
                "V2 flat statement hash invalid",
            ),
            "immediate_child_count": journal["immediate_child_count"],
            "journal_sha256": artifact["journal_sha256"],
            "leaf_disclosures_root": _hex32(
                journal["leaf_disclosures_root"], "V2 leaf disclosures root invalid"
            ),
            "partition_plan_root": _hex32(
                journal["partition_plan_root"], "V2 partition plan root invalid"
            ),
            "profile": journal["profile"],
            "protocol_journal_hash": artifact["protocol_journal_hash"],
            "statement_hash": _hex32(journal["statement_hash"], "V2 statement hash invalid"),
            "subtree_node_count": journal["subtree_node_count"],
            "tree_height": journal["tree_height"],
        }
        _require_exact_typed(report_node, expected_summary, "V2 dry-run journal mismatch")
        expected_report_nodes.append(expected_summary)

    def expected_dry_run(supplied: list[str]) -> dict[str, Any]:
        return {
            "aggregate_v2_image_id": V2_ID,
            "dry_run": True,
            "epoch_root": expected_report_nodes[1],
            "epoch_root_artifact": None,
            "epoch_root_receipt_sha256": None,
            "inner": expected_report_nodes[0],
            "inner_artifact": None,
            "inner_receipt_sha256": None,
            "input_leaf_count": 2,
            "input_leaf_receipt_sha256s": receipt_sha256s,
            "nonclaims": V2_NONCLAIMS,
            "ok": True,
            "supplied_leaf_receipt_sha256s": supplied,
        }

    _require_exact_typed(forward, expected_dry_run(receipt_sha256s), "forward dry-run mismatch")
    _require_exact_typed(
        reverse,
        expected_dry_run(list(reversed(receipt_sha256s))),
        "reverse dry-run mismatch",
    )

    controls = evidence / "controls"
    _check_exact_seal_mutation(root, load_json(controls / "v1-root.seal-word-1-xor-lsb.proof.json"))
    _check_exact_seal_mutation(
        v2_root, load_json(controls / "v2-root.seal-word-1-xor-lsb.proof.json")
    )
    _require_single_mutation(
        spot,
        load_json(controls / "v1-spot.wrong-image.proof.json"),
        ("meta", "risc0_image_id"),
    )
    _require_single_mutation(
        v2_root,
        load_json(controls / "v2-root.wrong-image.proof.json"),
        ("risc0_image_id",),
    )
    _require_single_mutation(
        v2_root,
        load_json(controls / "v2-root.journal-substitution.proof.json"),
        ("journal", "statement_hash", 0),
    )
    _require_single_mutation(
        v1_request,
        load_json(controls / "v1-root.profile-substitution.verify.request.json"),
        ("recursive_expectations", "proof_profile"),
    )

    rejects = {
        "v1-root.profile-substitution.reject.json": (
            "recursive_expectations.proof_profile mismatch",
            0,
        ),
        "v1-root.seal-mutation.reject.json": (
            "receipt verification failed: verification indicates proof is invalid",
            0,
        ),
        "v1-spot.wrong-image.reject.json": ("leaf meta.risc0_image_id mismatch", 1),
        "v2-duplicate-leaf.reject.json": ("leaf lane IDs must be unique", 1),
        "v2-root.journal-substitution.reject.json": (
            "artifact journal does not match the authenticated journal",
            1,
        ),
        "v2-root.seal-mutation.reject.json": (
            "receipt verification failed: verification indicates proof is invalid",
            1,
        ),
        "v2-root.wrong-image.reject.json": ("receipt artifact header mismatch", 1),
    }
    for name, (error, exit_code) in rejects.items():
        _require_exact_typed(
            load_json(evidence / "reports" / name),
            {"error": error, "exit_code": exit_code, "ok": False},
            f"{name} mismatch",
        )
    _require_exact_typed(
        load_json(evidence / "reports/v2-missing-assumption.reject.json"),
        {
            "aggregate_v2_image_id": V2_ID,
            "ok": True,
            "status": "missing_child_assumption_rejected",
        },
        "missing-assumption control mismatch",
    )


def validate(reference: dict[str, Any], *, repo_root: Path = ROOT) -> None:
    _require(
        set(reference)
        == {
            "claims",
            "evidence",
            "host_binaries",
            "promotion_source_inventory",
            "programs",
            "receipt_security",
            "schema",
            "sdk_version",
            "source_inventories",
            "source_base_revision",
            "toolchain",
        },
        "reference fields mismatch",
    )
    _require(
        reference["schema"] == SCHEMA
        and reference["source_base_revision"] == BASE_REVISION
        and reference["sdk_version"] == "3.0.5",
        "reference identity mismatch",
    )
    _require(set(reference["claims"]) == set(CLAIMS), "claim fields mismatch")
    for name, expected in CLAIMS.items():
        if type(expected) is bool:
            _require(type(reference["claims"][name]) is bool, f"{name} must be Boolean")
        else:
            _require(type(reference["claims"][name]) is str, f"{name} must be a string")
    _require(reference["claims"] == CLAIMS, "claim boundary mismatch")
    _require(reference["receipt_security"] == SECURITY, "receipt security reference mismatch")
    _require(reference["programs"] == PROGRAMS, "program identity reference mismatch")
    _require(reference["host_binaries"] == HOST_BINARIES, "host binary reference mismatch")
    _require(reference["toolchain"] == TOOLCHAIN, "toolchain reference mismatch")
    _check_git_base(repo_root)
    _check_sources(reference, repo_root=repo_root)
    _check_evidence(reference, repo_root=repo_root)


def check_reference(*, repository_root: Path = ROOT) -> dict[str, Any]:
    try:
        reference = load_json(
            repository_root
            / "config/proof_profiles/risc0_recursive_active_reproof_reference_v3.json"
        )
        validate(reference, repo_root=repository_root)
    except (CheckError, OSError, ValueError, KeyError, TypeError) as error:
        return {"error": str(error), "ok": False}
    return {"evidence_inventory_root": EVIDENCE_ROOT, "ok": True}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--reference", type=Path, default=REFERENCE)
    args = parser.parse_args()
    try:
        validate(load_json(args.reference))
    except (CheckError, OSError, ValueError, KeyError, TypeError) as error:
        print(json.dumps({"error": str(error), "ok": False}, sort_keys=True))
        return 1
    print(
        json.dumps(
            {
                "evidence_inventory_root": EVIDENCE_ROOT,
                "ok": True,
                "schema": SCHEMA,
                "source_base_revision": BASE_REVISION,
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
