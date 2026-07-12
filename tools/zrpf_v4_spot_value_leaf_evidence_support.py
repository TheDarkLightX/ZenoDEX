"""Exact constants and bounded helpers for retained V4 Spot leaf evidence."""

from __future__ import annotations

import copy
import hashlib
import importlib
from pathlib import Path
from typing import Any

_MODULE_PREFIX = "tools." if __package__ else ""
common = importlib.import_module(
    f"{_MODULE_PREFIX}zrpf_semantic_epoch_v1_evidence_support"
)

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MANIFEST = (
    REPO_ROOT
    / "docs/research/ZRPF_V4_SPOT_VALUE_LEAF_LOCAL_EVIDENCE_20260712.json"
)
EVIDENCE_ROOT_RELATIVE = "evidence/zrpf-v4-spot-value-leaf-v1"
REPORT_SCHEMA = "zenodex/zrpf_v4_spot_value_leaf_evidence_check/v1"
MANIFEST_SCHEMA = "zenodex/zrpf_v4_spot_value_leaf_local_evidence/v1"
EXPECTED_MANIFEST_SHA256 = "284e6eafdf83c2f1c0d930c8b27780dc5c297060c8cae8bdf6aaa991535ae62b"

PROOF_SOURCE_COMMIT = "247f40da13563990d3f9f687f706228c9283562f"
PROOF_SOURCE_TREE = "68792f420a54d96290add01c2c94e1b25032ae9c"
VERIFIER_SOURCE_COMMIT = "074e4a4327b4387606955a1ece868889ba50e502"
VERIFIER_SOURCE_TREE = "34684c47769ec69681ba13590ce76ba61fe48f70"
VERIFIER_BINARY_SHA256 = "61c99170466c15de7a10c94dd2a54828aca9d63b1d989d0b47d2df62e9593796"
VERIFIER_BINARY_SIZE_BYTES = 3_248_296

V4_IMAGE_ID = "dd58afedb9be399a3f9bbaa34229e5dc63c170873962e99307b52c5d25e7f743"
V4_IMAGE_ID_WORDS = [
    3_987_691_741,
    2_587_475_641,
    2_746_915_647,
    3_706_005_826,
    2_272_313_699,
    2_481_545_785,
    1_563_211_015,
    1_140_320_037,
]
VERIFIER_PARAMETERS = [
    3_102_336_492,
    3_939_904_686,
    3_022_461_035,
    1_208_221_540,
    3_740_575_737,
    10_233_549,
    1_979_579_783,
    329_288_969,
]
CONTROL_ID = [
    1_035_118_419,
    1_570_699_527,
    1_491_633_494,
    504_952_180,
    648_709_764,
    132_516_474,
    1_203_431_935,
    1_255_849_416,
]

PROGRAM = {
    "application_statement_hash": "35ebda5b6748cec7be31b04ad065231628ae642fdf1d23108bc04d2ceda9e9a0",
    "asset_flow_count": 0,
    "authority_use_count": 0,
    "claim_binding": "2fa0a2cf480701b2a377a8b15a98f1efbb5cad0156628dac921f2b457a90566c",
    "guest_elf_sha256": "195f1cd4bd4b6b4ddc4765d9ab33664834e64d58ee6c468dd0b254ea0012fa6e",
    "guest_elf_size_bytes": 499_312,
    "host_reconstructed_input_sha256": "2fe8630f5fdfab34a1fb128e307b28f8941eb40ed665383b11d3dff9fa791250",
    "host_reconstructed_input_size_bytes": 1_739,
    "image_id": V4_IMAGE_ID,
    "image_id_words": V4_IMAGE_ID_WORDS,
    "journal_canonical_hash": "d3b3b1616f9f90f80b3b67a904ce9b5561f238a4891746587b186ae840bd50c4",
    "journal_sha256": "4b177dccd6919caa03627d2440f38362700b9c3f4cc2267333d94e5fd597d7bc",
    "journal_size_bytes": 2_711,
    "represented_row_count": 0,
    "role": "spot_value_leaf_v4",
    "source_state_unchanged": True,
    "value_subtree_root": "839a52046406e3ee016bd339c07c9c1980a346f1f18b8035817a4dfebc8e06a4",
}

RECEIPT_PROFILE = {
    "control_id": CONTROL_ID,
    "dev_mode_disabled_by_rust_verifier": True,
    "hash_function": "poseidon2",
    "profile_id": "risc0_succinct_poseidon2_resolve_3_0_5_v1",
    "receipt_kind": "Succinct",
    "risc0_zkvm_version": "3.0.5",
    "verifier_parameters": VERIFIER_PARAMETERS,
}

ARTIFACTS = [
    {
        "encoding": "json_compact_insertion",
        "id": "spot-value-leaf-v4-positive",
        "journal_sha256": PROGRAM["journal_sha256"],
        "journal_size_bytes": PROGRAM["journal_size_bytes"],
        "kind": "risc0_succinct_receipt",
        "path": "receipts/spot-value-leaf-v4.receipt.json",
        "sha256": "794a69746b3f833f56e15c968c16ab7d4ee9089f555eb210d38a1c0ea37d18c7",
        "size_bytes": 601_394,
    },
    {
        "encoding": "json_compact_insertion",
        "id": "spot-value-leaf-v4-seal-mutation",
        "journal_sha256": PROGRAM["journal_sha256"],
        "journal_size_bytes": PROGRAM["journal_size_bytes"],
        "kind": "risc0_succinct_receipt_seal_mutation",
        "path": "receipts/spot-value-leaf-v4.seal-word-1-xor-lsb.receipt.json",
        "sha256": "2772e497dc94d937e5840bae87f2e606122269ffc8cb2a1d38667216747d2530",
        "size_bytes": 601_394,
    },
]

MUTATION_CONTROL = {
    "candidate_artifact_id": "spot-value-leaf-v4-seal-mutation",
    "journal_unchanged": True,
    "kind": "succinct_seal_word_1_xor_1_v1",
    "non_seal_receipt_bytes_unchanged": True,
    "seal_word_count": 55_667,
    "seal_word_index": 1,
    "source_artifact_id": "spot-value-leaf-v4-positive",
    "xor_mask": 1,
}

SUPPORTING_INPUTS = [
    {
        "embedded_receipt_sha256": "c6f365df966c98ef28f05e59c3e36533d0c16ca06475348a7bbb2863e41d58f6",
        "encoding": "json_compact_insertion",
        "id": "retained-spot-v1-source-wrapper",
        "kind": "spot_v1_source_proof_wrapper",
        "path": "evidence/zrpf-semantic-epoch-v1-local-proof-v1/source-inputs/source-ordinal-0.receipt.json",
        "sha256": "4ce7db31e6ae5e5af53b4ef67fb0cd6ebb1dcae9cf05ee9f73b4511c10db20b9",
        "size_bytes": 784_225,
    },
    {
        "encoding": "json_compact_insertion",
        "id": "retained-v1-adapter-ordinal-zero",
        "journal_sha256": "0b145b1bee53123458a3eab3568a11ebf01910e76034e5001ec8b27a247c6d5a",
        "journal_size_bytes": 1_547,
        "kind": "zrpf_v1_adapter_succinct_receipt",
        "path": "evidence/zrpf-semantic-epoch-v1-local-proof-v1/receipts/adapter-ordinal-0.receipt.json",
        "sha256": "67d792e018f94c354dc55184d562edb490e7c4262795ea69f9a747ce231b8ae9",
        "size_bytes": 593_192,
    },
]

POSITIVE_REPORT_NONCLAIMS = [
    "the retained source and adapter receipts were not regenerated",
    "the compiler-visible guest path is temporary and not release-governed",
    "the public policy and empty mint-grant set are local witness inputs without governance authority",
    "the retained source has zero asset rows and unchanged raw state",
    "this residual leaf does not prove closed-epoch conservation or semantic finality",
    "verify-only replay does not load, hash, or recompute the guest ELF and does not establish ELF-to-image provenance",
    "the host-reconstructed input hash is not a receipt-proven private-input commitment",
    "no data-availability, schedule, carry, ledger-admission, settlement, release, privacy, sandbox, reproducible-build, or production authority",
]

EXPECTED_POSITIVE_REPORT = {
    "adapter_image_id": "d2c2f1a321c53e0228455b2cf22942fde7595030a379c3fd5484af446ac75d64",
    "adapter_journal_sha256": "0b145b1bee53123458a3eab3568a11ebf01910e76034e5001ec8b27a247c6d5a",
    "adapter_receipt_sha256": "67d792e018f94c354dc55184d562edb490e7c4262795ea69f9a747ce231b8ae9",
    "application_statement_hash": PROGRAM["application_statement_hash"],
    "asset_flow_count": 0,
    "assigned_leaf_ordinal": 0,
    "authority_use_count": 0,
    "claim_binding": PROGRAM["claim_binding"],
    "exact_expected_journal_verified": True,
    "guest_artifact": {
        "expected_elf_bytes": PROGRAM["guest_elf_size_bytes"],
        "expected_elf_sha256": PROGRAM["guest_elf_sha256"],
        "loaded_and_matched": False,
        "observed_elf_bytes": None,
        "observed_elf_sha256": None,
        "source_to_elf_provenance_verified": False,
    },
    "host_reconstructed_input_bytes": PROGRAM["host_reconstructed_input_size_bytes"],
    "host_reconstructed_input_sha256": PROGRAM["host_reconstructed_input_sha256"],
    "journal_hash": PROGRAM["journal_canonical_hash"],
    "journal_sha256": PROGRAM["journal_sha256"],
    "nonclaims": POSITIVE_REPORT_NONCLAIMS,
    "ok": True,
    "outer_image_governance_verified": False,
    "production_authority": False,
    "receipt_bytes": ARTIFACTS[0]["size_bytes"],
    "receipt_proves_private_input_hash": False,
    "receipt_sha256": ARTIFACTS[0]["sha256"],
    "receipt_written_create_new": False,
    "release_authority": False,
    "represented_row_count": 0,
    "schema": "zenodex/zrpf_spot_value_leaf_v4_local_report/v2",
    "settlement_authority": False,
    "source_receipt_sha256": SUPPORTING_INPUTS[0]["embedded_receipt_sha256"],
    "source_state_unchanged": True,
    "status": "persisted_v4_spot_value_leaf_succinct_receipt_verified",
    "structural_journal_sha256": SUPPORTING_INPUTS[1]["journal_sha256"],
    "v4_image_id": V4_IMAGE_ID,
    "value_subtree_root": PROGRAM["value_subtree_root"],
    "zero_knowledge_privacy": False,
}

EXPECTED_REJECT_REPORT = {
    "candidate_accepted": False,
    "ok": False,
    "receipt_sha256": ARTIFACTS[1]["sha256"],
    "reject": {
        "boundary": "ExactSpotValueLeafReceiptV4::verify_exact_succinct_bytes",
        "code": "receipt_verification_failed",
        "outer_code": "spot_value_leaf_receipt_artifact_rejected",
        "variant": "ReceiptArtifact(ReceiptVerificationFailed)",
    },
    "schema": "zenodex/zrpf_spot_value_leaf_v4_receipt_reject/v1",
    "status": "persisted_v4_spot_value_leaf_receipt_rejected",
}

EXPECTED_DEV_MODE_REJECT_REPORT = {
    "candidate_accepted": False,
    "ok": False,
    "reject": {
        "boundary": "prove_spot_value_leaf_v4_process_start",
        "code": "ambient_risc0_dev_mode_forbidden",
        "variable": "RISC0_DEV_MODE",
    },
    "schema": "zenodex/zrpf_spot_value_leaf_v4_environment_reject/v1",
    "status": "ambient_dev_mode_environment_rejected",
}

CLAIMS = {
    "artifact_identity_and_exact_mutation_statically_checkable": True,
    "manifest_authorizes_ledger_admission": False,
    "manifest_authorizes_production": False,
    "manifest_authorizes_release": False,
    "manifest_authorizes_settlement": False,
    "source_anchored_retained_receipt_v4_value_leaf_replay_available": True,
    "static_checker_verifies_risc0_seals": False,
}

NON_CLAIMS = [
    "retained_source_and_adapter_receipts_not_regenerated",
    "v4_proof_receipt_not_regenerated_by_checker",
    "proof_generation_source_anchor_is_not_historical_execution_provenance",
    "complete_build_input_closure_not_verified",
    "same_uid_race_resistance_not_verified",
    "source_to_guest_elf_provenance_not_machine_verified",
    "cross_host_and_path_independent_reproducibility_not_verified",
    "proof_byte_determinism_not_verified",
    "zero_asset_rows_and_unchanged_source_state_only",
    "residual_leaf_without_closed_epoch_conservation_or_semantic_finality",
    "empty_grant_policy_has_no_governance_authority",
    "no_data_availability_schedule_or_carry_verification",
    "no_durable_atomic_ledger_admission",
    "no_public_release_settlement_or_production_authority",
    "no_zero_knowledge_privacy_claim",
    "no_sandbox_side_channel_or_covert_channel_claim",
    "no_throughput_latency_or_cost_claim",
    "static_checker_does_not_verify_risc0_seals",
    "live_checker_verifies_retained_receipts_and_does_not_regenerate_proofs",
    "checker_and_anchor_changes_require_external_review_governance",
]


def canonical_compact_newline(document: Any) -> bytes:
    """Return the exact one-line JSON ABI emitted by the Rust replay binary."""

    return common.canonical_artifact_bytes(document, "json_sorted_compact_newline")


def expected_manifest() -> dict[str, Any]:
    """Return the exact governed static evidence document."""

    positive_report = canonical_compact_newline(EXPECTED_POSITIVE_REPORT)
    reject_report = canonical_compact_newline(EXPECTED_REJECT_REPORT)
    dev_mode_reject = canonical_compact_newline(EXPECTED_DEV_MODE_REJECT_REPORT)
    return copy.deepcopy(
        {
            "artifacts": ARTIFACTS,
            "claims": CLAIMS,
            "evidence_date": "2026-07-12",
            "mutation_control": MUTATION_CONTROL,
            "native_replay": {
                "ambient_variants": ["RISC0_DEV_MODE_absent", "RISC0_DEV_MODE_1"],
                "build_timeout_seconds": 1_200,
                "dev_mode_environment_must_reject": True,
                "expected_dev_mode_reject_report": {
                    "sha256": common.sha256_bytes(dev_mode_reject),
                    "size_bytes": len(dev_mode_reject),
                },
                "expected_mutation_reject_report": {
                    "sha256": common.sha256_bytes(reject_report),
                    "size_bytes": len(reject_report),
                },
                "expected_positive_report": {
                    "sha256": common.sha256_bytes(positive_report),
                    "size_bytes": len(positive_report),
                },
                "max_process_output_bytes": 1_048_576,
                "mutation_artifact_id": ARTIFACTS[1]["id"],
                "normal_positive_must_verify": True,
                "positive_artifact_id": ARTIFACTS[0]["id"],
                "replay_timeout_seconds": 120,
                "supporting_inputs": SUPPORTING_INPUTS,
            },
            "native_replay_verifier": {
                "binary": "prove_spot_value_leaf_v4",
                "build_jobs": 4,
                "build_profile": "release",
                "cargo_frozen": True,
                "cargo_offline": True,
                "complete_build_input_closure_verified": False,
                "cross_path_reproducible_executable": False,
                "expected_executable_transport": "linux_memfd_full_seals_v1",
                "network_isolation_verified": False,
                "package": "zenodex-zrpf-risc0-harness",
                "recorded_executable_identity_match_required": False,
                "recorded_executable_sha256": VERIFIER_BINARY_SHA256,
                "recorded_executable_size_bytes": VERIFIER_BINARY_SIZE_BYTES,
                "risc0_skip_build": True,
                "same_uid_race_resistance_verified": False,
                "sandbox_verified": False,
                "source_commit": VERIFIER_SOURCE_COMMIT,
                "source_to_binary_provenance_scope": "same_host_pinned_source_snapshot_build",
                "source_tree": VERIFIER_SOURCE_TREE,
                "toolchain_lock_path": "config/proof_profiles/risc0_recursive_toolchain_lock.json",
                "toolchain_lock_sha256": "1be127ec1174a52ec246f04fd887d0ab3b89c246401a9cf4489d0e07c10cb2ab",
                "workspace": "zk/zrpf_risc0",
            },
            "non_claims": NON_CLAIMS,
            "program": PROGRAM,
            "proof_generation_source": {
                "commit": PROOF_SOURCE_COMMIT,
                "complete_build_input_closure_verified": False,
                "historical_execution_provenance_verified": False,
                "proof_generation_reported": True,
                "tree": PROOF_SOURCE_TREE,
            },
            "receipt_profile": RECEIPT_PROFILE,
            "schema": MANIFEST_SCHEMA,
            "scope": "source_anchored_retained_receipt_v4_value_leaf_replay",
            "status": "temporary_local_retained_receipt_evidence",
            "version": 1,
        }
    )


def exact_type_and_value(actual: Any, expected: Any) -> bool:
    """Compare recursively without allowing Boolean/integer substitution."""

    if type(actual) is not type(expected):
        return False
    if isinstance(expected, dict):
        return set(actual) == set(expected) and all(
            exact_type_and_value(actual[key], value) for key, value in expected.items()
        )
    if isinstance(expected, list):
        return len(actual) == len(expected) and all(
            exact_type_and_value(left, right)
            for left, right in zip(actual, expected, strict=True)
        )
    return bool(actual == expected)


def sha256_file(path: Path) -> str:
    """Hash one bounded regular file for offline boundary-atlas caching."""

    raw = common.read_relative_regular_file(
        path.parent,
        path.name,
        max_bytes=common.MAX_ARTIFACT_BYTES,
    )
    return hashlib.sha256(raw).hexdigest()
