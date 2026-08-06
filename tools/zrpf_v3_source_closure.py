"""Exact governed-workspace source inventory for frozen ZRPF V3 evidence.

This inventory binds repository files in the governed workspaces. It does not
establish a complete compiler or build-input closure; ambient toolchain,
dependency, build-script, and host inputs retain separate false claim fields.
"""

from __future__ import annotations

import hashlib
import json
import os
import stat
import subprocess
import tomllib
from pathlib import Path, PurePosixPath
from typing import Any

SCHEMA = "zenodex/zrpf_v3_frozen_source_closure/v1"
MAX_SOURCE_BYTES = 16 * 1024 * 1024
GOVERNED_WORKSPACE_ROOTS = (
    "zk/state_proof_risc0",
    "zk/zrpf_protocol",
    "zk/zrpf_risc0",
)

WORKSPACE_AUXILIARY_ROWS: tuple[tuple[str, str], ...] = tuple(
    ("governed_workspace_source", path)
    for path in (
        "zk/state_proof_risc0/Cargo.lock",
        "zk/state_proof_risc0/README.md",
        "zk/state_proof_risc0/cli/Cargo.toml",
        "zk/state_proof_risc0/cli/examples/recursive_artifact_export.rs",
        "zk/state_proof_risc0/cli/examples/recursive_missing_assumption_reject.rs",
        "zk/state_proof_risc0/cli/examples/recursive_summary_leaf_smoke.rs",
        "zk/state_proof_risc0/cli/src/main.rs",
        "zk/state_proof_risc0/cli/src/recursive_wire.rs",
        "zk/state_proof_risc0/cli/src/recursive_wire/application/mod.rs",
        "zk/state_proof_risc0/cli/src/recursive_wire/application/perps.rs",
        "zk/state_proof_risc0/cli/src/recursive_wire/application/spot.rs",
        "zk/state_proof_risc0/cli/src/recursive_wire/application/zusd.rs",
        "zk/state_proof_risc0/cli/src/strict_json.rs",
        "zk/state_proof_risc0/methods/Cargo.toml",
        "zk/state_proof_risc0/methods/aggregate/Cargo.toml",
        "zk/state_proof_risc0/methods/aggregate/src/main.rs",
        "zk/state_proof_risc0/methods/build.rs",
        "zk/state_proof_risc0/methods/guest/Cargo.toml",
        "zk/state_proof_risc0/methods/guest/src/main.rs",
        "zk/state_proof_risc0/methods/perps_np_leaf/Cargo.toml",
        "zk/state_proof_risc0/methods/perps_np_leaf/src/main.rs",
        "zk/state_proof_risc0/methods/spot_leaf/Cargo.toml",
        "zk/state_proof_risc0/methods/spot_leaf/src/main.rs",
        "zk/state_proof_risc0/methods/src/lib.rs",
        "zk/state_proof_risc0/methods/summary_leaf/Cargo.toml",
        "zk/state_proof_risc0/methods/summary_leaf/src/main.rs",
        "zk/state_proof_risc0/methods/zusd_leaf/Cargo.toml",
        "zk/state_proof_risc0/methods/zusd_leaf/src/main.rs",
        "zk/zrpf_protocol/Cargo.lock",
        "zk/zrpf_protocol/README.md",
        "zk/zrpf_protocol/perps_source_finality/Cargo.toml",
        "zk/zrpf_protocol/perps_source_finality/src/codec.rs",
        "zk/zrpf_protocol/perps_source_finality/src/derive.rs",
        "zk/zrpf_protocol/perps_source_finality/src/error.rs",
        "zk/zrpf_protocol/perps_source_finality/src/lib.rs",
        "zk/zrpf_protocol/perps_source_finality/src/model.rs",
        "zk/zrpf_protocol/perps_source_finality/tests/perps_source_finality_v1.rs",
        "zk/zrpf_protocol/zusd_value_flow/Cargo.toml",
        "zk/zrpf_protocol/zusd_value_flow/src/bounded.rs",
        "zk/zrpf_protocol/zusd_value_flow/src/codec.rs",
        "zk/zrpf_protocol/zusd_value_flow/src/context.rs",
        "zk/zrpf_protocol/zusd_value_flow/src/derive.rs",
        "zk/zrpf_protocol/zusd_value_flow/src/error.rs",
        "zk/zrpf_protocol/zusd_value_flow/src/hash.rs",
        "zk/zrpf_protocol/zusd_value_flow/src/lib.rs",
        "zk/zrpf_protocol/zusd_value_flow/src/operation.rs",
        "zk/zrpf_protocol/zusd_value_flow/src/proposal.rs",
        "zk/zrpf_protocol/zusd_value_flow/src/row.rs",
        "zk/zrpf_protocol/zusd_value_flow/tests/zusd_value_flow_v1.rs",
        "zk/zrpf_risc0/README.md",
        "zk/zrpf_risc0/replay_verifier/Cargo.toml",
        "zk/zrpf_risc0/replay_verifier/src/bin/zrpf_firecracker_guest_elf_checker.rs",
        "zk/zrpf_risc0/replay_verifier/src/bin/zrpf_firecracker_guest_init.rs",
        "zk/zrpf_risc0/replay_verifier/src/bundle.rs",
        "zk/zrpf_risc0/replay_verifier/src/error.rs",
        "zk/zrpf_risc0/replay_verifier/src/firecracker_protocol.rs",
        "zk/zrpf_risc0/replay_verifier/src/lib.rs",
        "zk/zrpf_risc0/replay_verifier/src/main.rs",
        "zk/zrpf_risc0/replay_verifier/src/profile.rs",
        "zk/zrpf_risc0/replay_verifier/src/tests.rs",
    )
)

AUXILIARY_RUST_ROWS: tuple[tuple[str, str], ...] = tuple(
    ("assurance_compiler_source", path)
    for path in (
        "zk/zrpf_protocol/protocol/tests/economic_action_v1.rs",
        "zk/zrpf_protocol/protocol/tests/full_blob_da_v1.rs",
        "zk/zrpf_protocol/protocol/tests/global_settlement_abi_v1.rs",
        "zk/zrpf_protocol/protocol/tests/node_v3.rs",
        "zk/zrpf_protocol/protocol/tests/semantic_epoch_v1.rs",
        "zk/zrpf_protocol/protocol/tests/settlement_certificate_v1.rs",
        "zk/zrpf_protocol/protocol/tests/settlement_effect_v2.rs",
        "zk/zrpf_protocol/protocol/tests/sparse_merkle_batch_support.rs",
        "zk/zrpf_protocol/protocol/tests/sparse_merkle_batch_transition_v1.rs",
        "zk/zrpf_protocol/protocol/tests/sparse_merkle_cell_transition_v1.rs",
        "zk/zrpf_protocol/protocol/tests/support/value_aggregate_v5_mirror.rs",
        "zk/zrpf_protocol/protocol/tests/task_manifest_assignment_policy_v1.rs",
        "zk/zrpf_protocol/protocol/tests/task_manifest_compatibility_v1.rs",
        "zk/zrpf_protocol/protocol/tests/task_manifest_hash_v1.rs",
        "zk/zrpf_protocol/protocol/tests/task_manifest_v1.rs",
        "zk/zrpf_protocol/protocol/tests/value_aggregate_v5.rs",
        "zk/zrpf_protocol/protocol/tests/value_aggregate_v5_operational.rs",
        "zk/zrpf_protocol/protocol/tests/value_node_v4.rs",
        "zk/zrpf_protocol/protocol/tests/value_transfer_v2.rs",
        "zk/zrpf_risc0/aggregate_shared/tests/structural_v1.rs",
        "zk/zrpf_risc0/semantic_shared/tests/bind_v1.rs",
        "zk/zrpf_risc0/semantic_shared/tests/codec_v1.rs",
        "zk/zrpf_risc0/semantic_shared/tests/epoch_v1.rs",
        "zk/zrpf_risc0/semantic_shared/tests/recompose_v1.rs",
        "zk/zrpf_risc0/semantic_shared/tests/semantic_v2.rs",
        "zk/zrpf_risc0/semantic_shared/tests/spot_certificate_mutation_v1.rs",
        "zk/zrpf_risc0/semantic_shared/tests/spot_certificate_state_v2.rs",
        "zk/zrpf_risc0/semantic_shared/tests/spot_certificate_v1.rs",
        "zk/zrpf_risc0/semantic_shared/tests/spot_full_blob_da_v1.rs",
        "zk/zrpf_risc0/semantic_shared/tests/spot_guest_input_v2.rs",
        "zk/zrpf_risc0/semantic_shared/tests/spot_guest_receipt_boundary_v2.rs",
        "zk/zrpf_risc0/semantic_shared/tests/spot_guest_source_contract_v2.rs",
        "zk/zrpf_risc0/semantic_shared/tests/spot_replay_data_v1.rs",
        "zk/zrpf_risc0/semantic_shared/tests/spot_replay_data_v2.rs",
        "zk/zrpf_risc0/semantic_shared/tests/spot_settlement_state_v2.rs",
        "zk/zrpf_risc0/semantic_shared/tests/spot_settlement_v1.rs",
        "zk/zrpf_risc0/semantic_shared/tests/support/spot_certificate_fixture.rs",
        "zk/zrpf_risc0/semantic_shared/tests/support/spot_certificate_state_v2_fixture.rs",
        "zk/zrpf_risc0/semantic_shared/tests/support/spot_certificate_state_v2_hashes.rs",
        "zk/zrpf_risc0/semantic_shared/tests/support/spot_certificate_vectors.rs",
        "zk/zrpf_risc0/semantic_shared/tests/support/spot_guest_input_v2_wire.rs",
        "zk/zrpf_risc0/semantic_shared/tests/value_v1.rs",
        "zk/zrpf_risc0/shared/tests/v1_leaf_adapter.rs",
        "zk/zrpf_risc0/value_aggregate_l2_policy/tests/architecture_v5.rs",
        "zk/zrpf_risc0/value_aggregate_l2_policy/tests/identity_v5.rs",
        "zk/zrpf_risc0/value_aggregate_l2_policy/tests/level_two_guest_v5.rs",
        "zk/zrpf_risc0/value_aggregate_root_policy/tests/architecture_v5.rs",
        "zk/zrpf_risc0/value_aggregate_root_policy/tests/identity_v5.rs",
        "zk/zrpf_risc0/value_aggregate_shared/tests/guest_input_v5.rs",
        "zk/zrpf_risc0/value_aggregate_shared/tests/level_one_guest_v5.rs",
        "zk/zrpf_risc0/value_aggregate_shared/tests/level_one_v5.rs",
        "zk/zrpf_risc0/value_aggregate_shared/tests/level_two_v5.rs",
        "zk/zrpf_risc0/value_aggregate_shared/tests/support/mod.rs",
        "zk/zrpf_risc0/value_node_shared/tests/leaf_v4.rs",
    )
)

SOURCE_ROWS: tuple[tuple[str, str], ...] = tuple(
    sorted(
        (
            *AUXILIARY_RUST_ROWS,
            *WORKSPACE_AUXILIARY_ROWS,
            (
                "economic_action_protocol_v1",
                "zk/zrpf_protocol/protocol/src/economic_action_v1/batch.rs",
            ),
            (
                "economic_action_protocol_v1",
                "zk/zrpf_protocol/protocol/src/economic_action_v1/batch_codec.rs",
            ),
            (
                "economic_action_protocol_v1",
                "zk/zrpf_protocol/protocol/src/economic_action_v1/batch_error.rs",
            ),
            (
                "economic_action_protocol_v1",
                "zk/zrpf_protocol/protocol/src/economic_action_v1/batch_hash.rs",
            ),
            (
                "economic_action_protocol_v1",
                "zk/zrpf_protocol/protocol/src/economic_action_v1/codec.rs",
            ),
            (
                "economic_action_protocol_v1",
                "zk/zrpf_protocol/protocol/src/economic_action_v1/mod.rs",
            ),
            (
                "economic_action_protocol_v1",
                "zk/zrpf_protocol/protocol/src/economic_action_v1/record.rs",
            ),
            (
                "data_availability_protocol_v1",
                "zk/zrpf_protocol/protocol/src/full_blob_da_v1/certificate.rs",
            ),
            (
                "data_availability_protocol_v1",
                "zk/zrpf_protocol/protocol/src/full_blob_da_v1/codec.rs",
            ),
            (
                "data_availability_protocol_v1",
                "zk/zrpf_protocol/protocol/src/full_blob_da_v1/error.rs",
            ),
            (
                "data_availability_protocol_v1",
                "zk/zrpf_protocol/protocol/src/full_blob_da_v1/hash.rs",
            ),
            (
                "data_availability_protocol_v1",
                "zk/zrpf_protocol/protocol/src/full_blob_da_v1/mod.rs",
            ),
            (
                "global_settlement_abi_v1",
                "zk/zrpf_protocol/protocol/src/global_settlement_abi_v1/codec.rs",
            ),
            (
                "global_settlement_abi_v1",
                "zk/zrpf_protocol/protocol/src/global_settlement_abi_v1/error.rs",
            ),
            (
                "global_settlement_abi_v1",
                "zk/zrpf_protocol/protocol/src/global_settlement_abi_v1/lane.rs",
            ),
            (
                "global_settlement_abi_v1",
                "zk/zrpf_protocol/protocol/src/global_settlement_abi_v1/mod.rs",
            ),
            (
                "global_settlement_abi_v1",
                "zk/zrpf_protocol/protocol/src/global_settlement_abi_v1/registry.rs",
            ),
            (
                "settlement_certificate_protocol_v1",
                "zk/zrpf_protocol/protocol/src/settlement_certificate_v1/certificate.rs",
            ),
            (
                "settlement_certificate_protocol_v1",
                "zk/zrpf_protocol/protocol/src/settlement_certificate_v1/codec.rs",
            ),
            (
                "settlement_certificate_protocol_v1",
                "zk/zrpf_protocol/protocol/src/settlement_certificate_v1/error.rs",
            ),
            (
                "settlement_certificate_protocol_v1",
                "zk/zrpf_protocol/protocol/src/settlement_certificate_v1/hash.rs",
            ),
            (
                "settlement_certificate_protocol_v1",
                "zk/zrpf_protocol/protocol/src/settlement_certificate_v1/mod.rs",
            ),
            (
                "settlement_effect_protocol_v2",
                "zk/zrpf_protocol/protocol/src/settlement_effect_v2/bounded.rs",
            ),
            (
                "settlement_effect_protocol_v2",
                "zk/zrpf_protocol/protocol/src/settlement_effect_v2/codec.rs",
            ),
            (
                "settlement_effect_protocol_v2",
                "zk/zrpf_protocol/protocol/src/settlement_effect_v2/error.rs",
            ),
            (
                "settlement_effect_protocol_v2",
                "zk/zrpf_protocol/protocol/src/settlement_effect_v2/hash.rs",
            ),
            (
                "settlement_effect_protocol_v2",
                "zk/zrpf_protocol/protocol/src/settlement_effect_v2/mod.rs",
            ),
            (
                "settlement_effect_protocol_v2",
                "zk/zrpf_protocol/protocol/src/settlement_effect_v2/plan.rs",
            ),
            (
                "settlement_effect_protocol_v2",
                "zk/zrpf_protocol/protocol/src/settlement_effect_v2/records.rs",
            ),
            (
                "settlement_effect_protocol_v2",
                "zk/zrpf_protocol/protocol/src/settlement_effect_v2/records/asset.rs",
            ),
            (
                "settlement_effect_protocol_v2",
                "zk/zrpf_protocol/protocol/src/settlement_effect_v2/records/carry_reward.rs",
            ),
            (
                "settlement_effect_protocol_v2",
                "zk/zrpf_protocol/protocol/src/settlement_effect_v2/records/cell.rs",
            ),
            (
                "settlement_effect_protocol_v2",
                "zk/zrpf_protocol/protocol/src/settlement_effect_v2/records/message.rs",
            ),
            (
                "settlement_effect_protocol_v2",
                "zk/zrpf_protocol/protocol/src/settlement_effect_v2/validate.rs",
            ),
            (
                "sparse_state_batch_protocol_v1",
                "zk/zrpf_protocol/protocol/src/sparse_merkle_batch_transition_v1/batch.rs",
            ),
            (
                "sparse_state_batch_protocol_v1",
                "zk/zrpf_protocol/protocol/src/sparse_merkle_batch_transition_v1/bounded.rs",
            ),
            (
                "sparse_state_batch_protocol_v1",
                "zk/zrpf_protocol/protocol/src/sparse_merkle_batch_transition_v1/codec.rs",
            ),
            (
                "sparse_state_batch_protocol_v1",
                "zk/zrpf_protocol/protocol/src/sparse_merkle_batch_transition_v1/entry.rs",
            ),
            (
                "sparse_state_batch_protocol_v1",
                "zk/zrpf_protocol/protocol/src/sparse_merkle_batch_transition_v1/error.rs",
            ),
            (
                "sparse_state_batch_protocol_v1",
                "zk/zrpf_protocol/protocol/src/sparse_merkle_batch_transition_v1/mod.rs",
            ),
            (
                "sparse_state_cell_protocol_v1",
                "zk/zrpf_protocol/protocol/src/sparse_merkle_cell_transition_v1/binding.rs",
            ),
            (
                "sparse_state_cell_protocol_v1",
                "zk/zrpf_protocol/protocol/src/sparse_merkle_cell_transition_v1/codec.rs",
            ),
            (
                "sparse_state_cell_protocol_v1",
                "zk/zrpf_protocol/protocol/src/sparse_merkle_cell_transition_v1/error.rs",
            ),
            (
                "sparse_state_cell_protocol_v1",
                "zk/zrpf_protocol/protocol/src/sparse_merkle_cell_transition_v1/hash.rs",
            ),
            (
                "sparse_state_cell_protocol_v1",
                "zk/zrpf_protocol/protocol/src/sparse_merkle_cell_transition_v1/mod.rs",
            ),
            (
                "sparse_state_cell_protocol_v1",
                "zk/zrpf_protocol/protocol/src/sparse_merkle_cell_transition_v1/path.rs",
            ),
            (
                "sparse_state_cell_protocol_v1",
                "zk/zrpf_protocol/protocol/src/sparse_merkle_cell_transition_v1/witness.rs",
            ),
            (
                "task_manifest_protocol_v1",
                "zk/zrpf_protocol/protocol/src/task_manifest_v1/assignment_policy.rs",
            ),
            (
                "task_manifest_protocol_v1",
                "zk/zrpf_protocol/protocol/src/task_manifest_v1/assignment_policy_codec.rs",
            ),
            ("task_manifest_protocol_v1", "zk/zrpf_protocol/protocol/src/task_manifest_v1/base.rs"),
            (
                "task_manifest_protocol_v1",
                "zk/zrpf_protocol/protocol/src/task_manifest_v1/codec.rs",
            ),
            (
                "task_manifest_protocol_v1",
                "zk/zrpf_protocol/protocol/src/task_manifest_v1/compatibility.rs",
            ),
            ("task_manifest_protocol_v1", "zk/zrpf_protocol/protocol/src/task_manifest_v1/hash.rs"),
            (
                "task_manifest_protocol_v1",
                "zk/zrpf_protocol/protocol/src/task_manifest_v1/manifest.rs",
            ),
            ("task_manifest_protocol_v1", "zk/zrpf_protocol/protocol/src/task_manifest_v1/mod.rs"),
            ("task_manifest_protocol_v1", "zk/zrpf_protocol/protocol/src/task_manifest_v1/task.rs"),
            (
                "value_aggregate_protocol_v5",
                "zk/zrpf_protocol/protocol/src/value_aggregate_v5/child.rs",
            ),
            (
                "value_aggregate_protocol_v5",
                "zk/zrpf_protocol/protocol/src/value_aggregate_v5/codec.rs",
            ),
            (
                "value_aggregate_protocol_v5",
                "zk/zrpf_protocol/protocol/src/value_aggregate_v5/error.rs",
            ),
            (
                "value_aggregate_protocol_v5",
                "zk/zrpf_protocol/protocol/src/value_aggregate_v5/hash.rs",
            ),
            (
                "value_aggregate_protocol_v5",
                "zk/zrpf_protocol/protocol/src/value_aggregate_v5/mod.rs",
            ),
            (
                "value_aggregate_protocol_v5",
                "zk/zrpf_protocol/protocol/src/value_aggregate_v5/operational.rs",
            ),
            (
                "value_aggregate_protocol_v5",
                "zk/zrpf_protocol/protocol/src/value_aggregate_v5/proposal.rs",
            ),
            (
                "value_aggregate_protocol_v5",
                "zk/zrpf_protocol/protocol/src/value_aggregate_v5/proposal_validation.rs",
            ),
            (
                "value_transfer_protocol_v2",
                "zk/zrpf_protocol/protocol/src/value_transfer_v2/codec.rs",
            ),
            (
                "value_transfer_protocol_v2",
                "zk/zrpf_protocol/protocol/src/value_transfer_v2/error.rs",
            ),
            (
                "value_transfer_protocol_v2",
                "zk/zrpf_protocol/protocol/src/value_transfer_v2/hash.rs",
            ),
            (
                "value_transfer_protocol_v2",
                "zk/zrpf_protocol/protocol/src/value_transfer_v2/mod.rs",
            ),
            (
                "value_transfer_protocol_v2",
                "zk/zrpf_protocol/protocol/src/value_transfer_v2/record.rs",
            ),
            (
                "value_transfer_protocol_v2",
                "zk/zrpf_protocol/protocol/src/value_transfer_v2/set.rs",
            ),
            ("proof_harness_v5", "zk/zrpf_risc0/harness/src/bin/prove_value_aggregate_l1_v5.rs"),
            (
                "proof_harness_v5",
                "zk/zrpf_risc0/harness/src/bin/prove_value_aggregate_l1_v5/artifact_io.rs",
            ),
            (
                "proof_harness_v5",
                "zk/zrpf_risc0/harness/src/bin/prove_value_aggregate_l1_v5/cli.rs",
            ),
            (
                "proof_harness_v5",
                "zk/zrpf_risc0/harness/src/bin/prove_value_aggregate_l1_v5/report.rs",
            ),
            (
                "proof_harness_v5",
                "zk/zrpf_risc0/harness/src/bin/prove_value_aggregate_l1_v5/tests.rs",
            ),
            ("proof_harness_v5", "zk/zrpf_risc0/harness/src/bin/prove_value_aggregate_l2_v5.rs"),
            (
                "proof_harness_v5",
                "zk/zrpf_risc0/harness/src/bin/prove_value_aggregate_l2_v5/artifact_io.rs",
            ),
            (
                "proof_harness_v5",
                "zk/zrpf_risc0/harness/src/bin/prove_value_aggregate_l2_v5/cli.rs",
            ),
            (
                "proof_harness_v5",
                "zk/zrpf_risc0/harness/src/bin/prove_value_aggregate_l2_v5/report.rs",
            ),
            (
                "proof_harness_v5",
                "zk/zrpf_risc0/harness/src/bin/prove_value_aggregate_l2_v5/tests.rs",
            ),
            (
                "spot_settlement_guest_v1",
                "zk/zrpf_risc0/methods/ordinary_spot_settlement/src/main.rs",
            ),
            ("value_aggregate_guest_v5", "zk/zrpf_risc0/methods/value_aggregate_l1/src/main.rs"),
            ("value_aggregate_guest_v5", "zk/zrpf_risc0/methods/value_aggregate_l2/src/main.rs"),
            (
                "spot_certificate_mapping_v1",
                "zk/zrpf_risc0/semantic_shared/src/spot_certificate_v1/error.rs",
            ),
            (
                "spot_certificate_mapping_v1",
                "zk/zrpf_risc0/semantic_shared/src/spot_certificate_v1/guest_input_v2/codec.rs",
            ),
            (
                "spot_certificate_mapping_v1",
                "zk/zrpf_risc0/semantic_shared/src/spot_certificate_v1/guest_input_v2/composition.rs",
            ),
            (
                "spot_certificate_mapping_v1",
                "zk/zrpf_risc0/semantic_shared/src/spot_certificate_v1/guest_input_v2/error.rs",
            ),
            (
                "spot_certificate_mapping_v1",
                "zk/zrpf_risc0/semantic_shared/src/spot_certificate_v1/guest_input_v2/mod.rs",
            ),
            (
                "spot_certificate_mapping_v1",
                "zk/zrpf_risc0/semantic_shared/src/spot_certificate_v1/hash.rs",
            ),
            (
                "spot_certificate_mapping_v1",
                "zk/zrpf_risc0/semantic_shared/src/spot_certificate_v1/mod.rs",
            ),
            (
                "spot_certificate_mapping_v1",
                "zk/zrpf_risc0/semantic_shared/src/spot_certificate_v1/replay_data/codec.rs",
            ),
            (
                "spot_certificate_mapping_v1",
                "zk/zrpf_risc0/semantic_shared/src/spot_certificate_v1/replay_data/error.rs",
            ),
            (
                "spot_certificate_mapping_v1",
                "zk/zrpf_risc0/semantic_shared/src/spot_certificate_v1/replay_data/mod.rs",
            ),
            (
                "spot_certificate_mapping_v1",
                "zk/zrpf_risc0/semantic_shared/src/spot_certificate_v1/replay_data_v2/codec.rs",
            ),
            (
                "spot_certificate_mapping_v1",
                "zk/zrpf_risc0/semantic_shared/src/spot_certificate_v1/replay_data_v2/error.rs",
            ),
            (
                "spot_certificate_mapping_v1",
                "zk/zrpf_risc0/semantic_shared/src/spot_certificate_v1/replay_data_v2/mod.rs",
            ),
            (
                "spot_certificate_mapping_v1",
                "zk/zrpf_risc0/semantic_shared/src/spot_certificate_v1/state_v2.rs",
            ),
            (
                "spot_certificate_mapping_v1",
                "zk/zrpf_risc0/semantic_shared/src/spot_certificate_v1/wire_v2.rs",
            ),
            (
                "spot_settlement_mapping_v1",
                "zk/zrpf_risc0/semantic_shared/src/spot_settlement_v1/error.rs",
            ),
            (
                "spot_settlement_mapping_v1",
                "zk/zrpf_risc0/semantic_shared/src/spot_settlement_v1/mod.rs",
            ),
            (
                "spot_settlement_mapping_v1",
                "zk/zrpf_risc0/semantic_shared/src/spot_settlement_v1/state_v2.rs",
            ),
            ("verification_harness_v5", "zk/zrpf_risc0/verifier/src/value_aggregate_v5.rs"),
            ("verification_harness_v5", "zk/zrpf_risc0/verifier/src/value_aggregate_v5/tests.rs"),
            (
                "value_aggregate_guest_v5",
                "zk/zrpf_risc0/methods/ordinary_spot_settlement/Cargo.toml",
            ),
            ("value_aggregate_guest_v5", "zk/zrpf_risc0/methods/value_aggregate_l1/Cargo.toml"),
            ("value_aggregate_guest_v5", "zk/zrpf_risc0/methods/value_aggregate_l2/Cargo.toml"),
            ("value_aggregate_l2_policy_v5", "zk/zrpf_risc0/value_aggregate_l2_policy/Cargo.toml"),
            ("value_aggregate_l2_policy_v5", "zk/zrpf_risc0/value_aggregate_l2_policy/src/lib.rs"),
            (
                "value_aggregate_root_policy_v5",
                "zk/zrpf_risc0/value_aggregate_root_policy/Cargo.toml",
            ),
            (
                "value_aggregate_root_policy_v5",
                "zk/zrpf_risc0/value_aggregate_root_policy/src/lib.rs",
            ),
            ("value_aggregate_mapping_v5", "zk/zrpf_risc0/value_aggregate_shared/Cargo.toml"),
            ("value_aggregate_mapping_v5", "zk/zrpf_risc0/value_aggregate_shared/src/child.rs"),
            ("value_aggregate_mapping_v5", "zk/zrpf_risc0/value_aggregate_shared/src/error.rs"),
            (
                "value_aggregate_mapping_v5",
                "zk/zrpf_risc0/value_aggregate_shared/src/guest_input.rs",
            ),
            ("value_aggregate_mapping_v5", "zk/zrpf_risc0/value_aggregate_shared/src/input.rs"),
            ("value_aggregate_mapping_v5", "zk/zrpf_risc0/value_aggregate_shared/src/level_one.rs"),
            ("value_aggregate_mapping_v5", "zk/zrpf_risc0/value_aggregate_shared/src/level_two.rs"),
            ("value_aggregate_mapping_v5", "zk/zrpf_risc0/value_aggregate_shared/src/lib.rs"),
            ("value_aggregate_mapping_v5", "zk/zrpf_risc0/value_aggregate_shared/src/policy.rs"),
            ("workspace_build", "zk/state_proof_risc0/.cargo/config.toml"),
            ("workspace_build", "zk/state_proof_risc0/Cargo.toml"),
            ("source_journal_dependency", "zk/state_proof_risc0/shared/Cargo.toml"),
            ("source_journal_dependency", "zk/state_proof_risc0/shared/src/lib.rs"),
            ("source_journal_dependency", "zk/state_proof_risc0/shared/src/recursive.rs"),
            ("source_journal_dependency", "zk/state_proof_risc0/shared/src/surfaces.rs"),
            ("protocol_dependency", "zk/zrpf_protocol/Cargo.toml"),
            ("protocol_dependency", "zk/zrpf_protocol/protocol/Cargo.toml"),
            ("protocol_dependency", "zk/zrpf_protocol/protocol/src/lib.rs"),
            ("semantic_protocol", "zk/zrpf_protocol/protocol/src/semantic_epoch_v1/hash.rs"),
            ("semantic_protocol", "zk/zrpf_protocol/protocol/src/semantic_epoch_v1/ids.rs"),
            ("semantic_protocol", "zk/zrpf_protocol/protocol/src/semantic_epoch_v1/leaf.rs"),
            ("semantic_protocol", "zk/zrpf_protocol/protocol/src/semantic_epoch_v1/mod.rs"),
            ("semantic_protocol", "zk/zrpf_protocol/protocol/src/semantic_epoch_v1/proposal.rs"),
            ("semantic_protocol", "zk/zrpf_protocol/protocol/src/semantic_epoch_v1/sets.rs"),
            ("semantic_protocol_v2", "zk/zrpf_protocol/protocol/src/semantic_epoch_v2/hash.rs"),
            ("semantic_protocol_v2", "zk/zrpf_protocol/protocol/src/semantic_epoch_v2/mod.rs"),
            ("semantic_protocol_v2", "zk/zrpf_protocol/protocol/src/semantic_epoch_v2/proposal.rs"),
            ("value_protocol_v4", "zk/zrpf_protocol/protocol/src/value_node_v4/bounded.rs"),
            ("value_protocol_v4", "zk/zrpf_protocol/protocol/src/value_node_v4/error.rs"),
            ("value_protocol_v4", "zk/zrpf_protocol/protocol/src/value_node_v4/journal.rs"),
            ("value_protocol_v4", "zk/zrpf_protocol/protocol/src/value_node_v4/mod.rs"),
            ("value_protocol_v4", "zk/zrpf_protocol/protocol/src/value_node_v4/records.rs"),
            ("value_protocol_v4", "zk/zrpf_protocol/protocol/src/value_node_v4/subtree.rs"),
            (
                "value_protocol_v4",
                "zk/zrpf_protocol/protocol/src/value_node_v4/subtree/codec.rs",
            ),
            (
                "value_protocol_v4",
                "zk/zrpf_protocol/protocol/src/value_node_v4/subtree/hash.rs",
            ),
            (
                "value_protocol_v4",
                "zk/zrpf_protocol/protocol/src/value_node_v4/subtree/merge.rs",
            ),
            (
                "value_protocol_v4",
                "zk/zrpf_protocol/protocol/src/value_node_v4/subtree/validate.rs",
            ),
            ("workspace_build", "zk/zrpf_risc0/.cargo/config.toml"),
            ("workspace_build", "zk/zrpf_risc0/Cargo.lock"),
            ("workspace_build", "zk/zrpf_risc0/Cargo.toml"),
            ("aggregate_mapping", "zk/zrpf_risc0/aggregate_shared/Cargo.toml"),
            ("aggregate_mapping", "zk/zrpf_risc0/aggregate_shared/src/input_v1.rs"),
            ("aggregate_mapping", "zk/zrpf_risc0/aggregate_shared/src/lib.rs"),
            ("aggregate_mapping", "zk/zrpf_risc0/aggregate_shared/src/structural_v1.rs"),
            ("proof_harness", "zk/zrpf_risc0/harness/Cargo.toml"),
            ("proof_harness", "zk/zrpf_risc0/harness/src/bin/prove_semantic_epoch.rs"),
            (
                "proof_harness_v4",
                "zk/zrpf_risc0/harness/src/bin/prove_spot_value_leaf_v4.rs",
            ),
            (
                "proof_harness_v4",
                "zk/zrpf_risc0/harness/src/bin/prove_spot_value_leaf_v4/artifact_io.rs",
            ),
            (
                "proof_harness_v4",
                "zk/zrpf_risc0/harness/src/bin/prove_spot_value_leaf_v4/report.rs",
            ),
            (
                "proof_harness_v4",
                "zk/zrpf_risc0/harness/src/bin/prove_spot_value_leaf_v4/source.rs",
            ),
            (
                "proof_harness_v4",
                "zk/zrpf_risc0/harness/src/bin/prove_spot_value_leaf_v4/tests.rs",
            ),
            ("proof_harness", "zk/zrpf_risc0/harness/src/bin/prove_structural_l1.rs"),
            ("proof_harness", "zk/zrpf_risc0/harness/src/bin/prove_structural_tree.rs"),
            ("verification_harness", "zk/zrpf_risc0/harness/src/bin/verify_semantic_epoch.rs"),
            ("verification_harness", "zk/zrpf_risc0/harness/src/bin/verify_structural_tree.rs"),
            ("proof_harness", "zk/zrpf_risc0/harness/src/main.rs"),
            ("guest_build", "zk/zrpf_risc0/methods/Cargo.toml"),
            ("guest_build", "zk/zrpf_risc0/methods/build.rs"),
            ("guest_build", "zk/zrpf_risc0/methods/src/lib.rs"),
            ("semantic_guest", "zk/zrpf_risc0/methods/semantic_epoch/Cargo.toml"),
            ("semantic_guest", "zk/zrpf_risc0/methods/semantic_epoch/src/main.rs"),
            ("value_guest_v4", "zk/zrpf_risc0/methods/spot_value_leaf_v4/Cargo.toml"),
            ("value_guest_v4", "zk/zrpf_risc0/methods/spot_value_leaf_v4/src/main.rs"),
            ("adapter_guest", "zk/zrpf_risc0/methods/v1_leaf_adapter/Cargo.toml"),
            ("adapter_guest", "zk/zrpf_risc0/methods/v1_leaf_adapter/src/main.rs"),
            ("structural_l1_guest", "zk/zrpf_risc0/methods/structural_aggregate_l1/Cargo.toml"),
            ("structural_l1_guest", "zk/zrpf_risc0/methods/structural_aggregate_l1/src/main.rs"),
            ("structural_l2_guest", "zk/zrpf_risc0/methods/structural_aggregate_l2/Cargo.toml"),
            ("structural_l2_guest", "zk/zrpf_risc0/methods/structural_aggregate_l2/src/main.rs"),
            ("adapter_mapping", "zk/zrpf_risc0/shared/Cargo.toml"),
            ("adapter_mapping", "zk/zrpf_risc0/shared/src/adapter_input_v1.rs"),
            ("adapter_mapping", "zk/zrpf_risc0/shared/src/hashing_v1.rs"),
            ("adapter_mapping", "zk/zrpf_risc0/shared/src/lib.rs"),
            ("adapter_mapping", "zk/zrpf_risc0/shared/src/risc0_binding_v1.rs"),
            ("adapter_mapping", "zk/zrpf_risc0/shared/src/source_binding_v3.rs"),
            ("adapter_mapping", "zk/zrpf_risc0/shared/src/source_policy_v1.rs"),
            ("adapter_mapping", "zk/zrpf_risc0/shared/src/v1_leaf_adapter.rs"),
            ("semantic_mapping", "zk/zrpf_risc0/semantic_shared/Cargo.toml"),
            ("semantic_mapping", "zk/zrpf_risc0/semantic_shared/src/bind_v1.rs"),
            ("semantic_mapping_v2", "zk/zrpf_risc0/semantic_shared/src/bind_v2.rs"),
            ("semantic_mapping", "zk/zrpf_risc0/semantic_shared/src/codec_v1.rs"),
            ("semantic_mapping_v2", "zk/zrpf_risc0/semantic_shared/src/codec_v2.rs"),
            ("semantic_mapping_v2", "zk/zrpf_risc0/semantic_shared/src/disclosure_v1.rs"),
            ("semantic_mapping", "zk/zrpf_risc0/semantic_shared/src/epoch_v1.rs"),
            ("semantic_mapping_v2", "zk/zrpf_risc0/semantic_shared/src/epoch_v2.rs"),
            ("semantic_mapping", "zk/zrpf_risc0/semantic_shared/src/input_v1.rs"),
            ("semantic_mapping", "zk/zrpf_risc0/semantic_shared/src/lib.rs"),
            ("semantic_mapping", "zk/zrpf_risc0/semantic_shared/src/recompose_v1.rs"),
            ("semantic_value_mapping_v4", "zk/zrpf_risc0/semantic_shared/src/value_v1.rs"),
            (
                "semantic_value_mapping_v4",
                "zk/zrpf_risc0/semantic_shared/src/value_v1/compose.rs",
            ),
            (
                "semantic_value_mapping_v4",
                "zk/zrpf_risc0/semantic_shared/src/value_v1/error.rs",
            ),
            (
                "semantic_value_mapping_v4",
                "zk/zrpf_risc0/semantic_shared/src/value_v1/expected.rs",
            ),
            (
                "semantic_value_mapping_v4",
                "zk/zrpf_risc0/semantic_shared/src/value_v1/hash.rs",
            ),
            (
                "semantic_value_mapping_v4",
                "zk/zrpf_risc0/semantic_shared/src/value_v1/validate.rs",
            ),
            (
                "semantic_value_mapping_v4",
                "zk/zrpf_risc0/semantic_shared/src/value_v1/wire_v4.rs",
            ),
            (
                "semantic_value_mapping_v4",
                "zk/zrpf_risc0/semantic_shared/src/value_v1/wire_v4/error.rs",
            ),
            ("value_node_mapping_v4", "zk/zrpf_risc0/value_node_shared/Cargo.toml"),
            ("value_node_mapping_v4", "zk/zrpf_risc0/value_node_shared/src/cursor.rs"),
            ("value_node_mapping_v4", "zk/zrpf_risc0/value_node_shared/src/error.rs"),
            ("value_node_mapping_v4", "zk/zrpf_risc0/value_node_shared/src/leaf.rs"),
            ("value_node_mapping_v4", "zk/zrpf_risc0/value_node_shared/src/leaf_codec.rs"),
            ("value_node_mapping_v4", "zk/zrpf_risc0/value_node_shared/src/lib.rs"),
            ("value_node_mapping_v4", "zk/zrpf_risc0/value_node_shared/src/profile.rs"),
            ("verification_harness", "zk/zrpf_risc0/verifier/Cargo.toml"),
            ("verification_harness", "zk/zrpf_risc0/verifier/src/lib.rs"),
            ("verification_harness", "zk/zrpf_risc0/verifier/src/semantic_epoch_v1.rs"),
            ("verification_harness_v2", "zk/zrpf_risc0/verifier/src/semantic_epoch_v2.rs"),
            ("verification_harness_v4", "zk/zrpf_risc0/verifier/src/spot_value_leaf_v4.rs"),
            (
                "verification_harness_v4",
                "zk/zrpf_risc0/verifier/src/spot_value_leaf_v4/tests.rs",
            ),
        ),
        key=lambda row: row[1],
    )
)


class SourceClosureError(ValueError):
    """Raised when a source tree cannot satisfy the frozen closure contract."""


def build_source_closure(repository_root: Path) -> dict[str, Any]:
    root = _resolved_repository_root(repository_root)
    _reject_target_directories(root)
    _validate_governed_workspace_inventory(root)

    files: list[dict[str, Any]] = []
    closure_hasher = hashlib.sha256()
    for role, relative in SOURCE_ROWS:
        raw = _read_source(root, relative)
        digest = hashlib.sha256(raw).hexdigest()
        row = {
            "path": relative,
            "role": role,
            "sha256": digest,
            "size_bytes": len(raw),
        }
        files.append(row)
        closure_hasher.update(role.encode("utf-8"))
        closure_hasher.update(b"\0")
        closure_hasher.update(relative.encode("utf-8"))
        closure_hasher.update(b"\0")
        closure_hasher.update(digest.encode("ascii"))
        closure_hasher.update(b"\0")
        closure_hasher.update(str(len(raw)).encode("ascii"))
        closure_hasher.update(b"\n")

    commit = _git_output(root, "rev-parse", "HEAD")
    dirty = _git_output(root, "status", "--porcelain", "--untracked-files=all")
    if dirty:
        raise SourceClosureError("source worktree must be clean before snapshot")
    return {
        "definition": "sha256 of sorted role, path, sha256, and size records with NUL field separators and LF record separators",
        "file_count": len(files),
        "files": files,
        "git_commit": commit,
        "schema": SCHEMA,
        "sha256": closure_hasher.hexdigest(),
        "status": "frozen_source_closure",
        "worktree_clean": True,
    }


def check_source_closure(document: Any, repository_root: Path) -> list[str]:
    if not isinstance(document, dict):
        return ["source closure must be an object"]
    try:
        expected = build_source_closure(repository_root)
    except SourceClosureError as exc:
        return [str(exc)]
    return (
        [] if document == expected else ["source closure differs from the current clean worktree"]
    )


def canonical_json_bytes(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")


def write_create_new(path: Path, raw: bytes) -> None:
    try:
        parent = path.parent.resolve(strict=True)
    except OSError as exc:
        raise SourceClosureError("snapshot output parent is unavailable") from exc
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        descriptor = os.open(parent / path.name, flags, 0o644)
    except OSError as exc:
        raise SourceClosureError("create-new snapshot output failed") from exc
    try:
        view = memoryview(raw)
        while view:
            written = os.write(descriptor, view)
            if written <= 0:
                raise SourceClosureError("snapshot output write made no progress")
            view = view[written:]
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
    directory_descriptor = os.open(parent, os.O_RDONLY)
    try:
        os.fsync(directory_descriptor)
    finally:
        os.close(directory_descriptor)


def _resolved_repository_root(path: Path) -> Path:
    try:
        root = path.resolve(strict=True)
    except OSError as exc:
        raise SourceClosureError("repository root is unavailable") from exc
    if path.is_symlink() or not root.is_dir() or not (root / ".git").exists():
        raise SourceClosureError("repository root must be a non-symlink git worktree")
    return root


def _read_source(root: Path, relative: str) -> bytes:
    pure = PurePosixPath(relative)
    if pure.is_absolute() or ".." in pure.parts or str(pure) != relative:
        raise SourceClosureError(f"unsafe source path: {relative}")
    flags = os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW
    directory_flags = flags | os.O_DIRECTORY
    descriptors: list[int] = []
    try:
        descriptor = os.open(root, directory_flags)
        descriptors.append(descriptor)
        for component in pure.parts[:-1]:
            descriptor = os.open(component, directory_flags, dir_fd=descriptor)
            descriptors.append(descriptor)
        file_descriptor = os.open(
            pure.parts[-1],
            flags | os.O_NONBLOCK,
            dir_fd=descriptor,
        )
        descriptors.append(file_descriptor)
        before = os.fstat(file_descriptor)
        if (
            not stat.S_ISREG(before.st_mode)
            or before.st_size <= 0
            or before.st_size > MAX_SOURCE_BYTES
        ):
            raise SourceClosureError(f"source file is not a bounded regular file: {relative}")
        output = bytearray()
        while len(output) < before.st_size:
            chunk = os.read(
                file_descriptor,
                min(1024 * 1024, before.st_size - len(output)),
            )
            if not chunk:
                raise SourceClosureError(f"source file changed while read: {relative}")
            output.extend(chunk)
        if os.read(file_descriptor, 1):
            raise SourceClosureError(f"source file changed while read: {relative}")
        after = os.fstat(file_descriptor)
    except OSError as exc:
        raise SourceClosureError(f"source file unavailable: {relative}") from exc
    finally:
        for opened in reversed(descriptors):
            os.close(opened)
    if _source_identity(before) != _source_identity(after):
        raise SourceClosureError(f"source file changed while read: {relative}")
    return bytes(output)


def _source_identity(metadata: os.stat_result) -> tuple[int, ...]:
    return (
        metadata.st_dev,
        metadata.st_ino,
        metadata.st_mode,
        metadata.st_size,
        metadata.st_mtime_ns,
        metadata.st_ctime_ns,
    )


def _validate_governed_workspace_inventory(root: Path) -> None:
    _validate_cargo_control_inventory(root)
    expected = {path for _, path in SOURCE_ROWS}
    discovered: set[str] = set()
    for relative_root in GOVERNED_WORKSPACE_ROOTS:
        directory = root / relative_root
        if not directory.is_dir() or directory.is_symlink():
            raise SourceClosureError(f"governed workspace unavailable: {relative_root}")
        for path in directory.rglob("*"):
            if path.is_symlink():
                raise SourceClosureError("governed workspace inventory contains a symlink")
            if path.is_dir():
                continue
            if not path.is_file():
                raise SourceClosureError("governed workspace inventory contains a non-regular path")
            discovered.add(path.relative_to(root).as_posix())
    if discovered != expected:
        missing = sorted(expected - discovered)
        extra = sorted(discovered - expected)
        raise SourceClosureError(
            f"governed workspace source inventory mismatch: missing={missing}, extra={extra}"
        )


def _validate_cargo_control_inventory(root: Path) -> None:
    expected = {
        path for _, path in SOURCE_ROWS if path.endswith("/build.rs") or "/.cargo/config" in path
    }
    discovered: set[str] = set()
    manifests = sorted(path for _, path in SOURCE_ROWS if path.endswith("/Cargo.toml"))
    for manifest in manifests:
        manifest_path = PurePosixPath(manifest)
        document = _load_governed_cargo_manifest(root, manifest)
        package = document.get("package")
        if package is not None and not isinstance(package, dict):
            raise SourceClosureError(f"invalid governed Cargo package table: {manifest}")
        if isinstance(package, dict):
            build = package.get("build")
            if build is not False:
                relative_build = "build.rs" if build is None else build
                if not isinstance(relative_build, str) or not relative_build:
                    raise SourceClosureError(f"invalid governed Cargo build path: {manifest}")
                build_path = PurePosixPath(relative_build)
                if build_path.is_absolute() or ".." in build_path.parts:
                    raise SourceClosureError(f"unsafe governed Cargo build path: {manifest}")
                candidate = (manifest_path.parent / build_path).as_posix()
                present = _record_cargo_control(root, candidate, discovered)
                if build is not None and not present:
                    raise SourceClosureError(
                        f"governed Cargo build script unavailable: {candidate}"
                    )
        for directory in _cargo_config_ancestors(manifest_path.parent):
            for name in ("config", "config.toml"):
                _record_cargo_control(
                    root,
                    (directory / ".cargo" / name).as_posix(),
                    discovered,
                )
    if discovered != expected:
        missing = sorted(expected - discovered)
        extra = sorted(discovered - expected)
        raise SourceClosureError(
            f"Cargo compiler control inventory mismatch: missing={missing}, extra={extra}"
        )


def _load_governed_cargo_manifest(root: Path, manifest: str) -> dict[str, Any]:
    try:
        document = tomllib.loads(_read_source(root, manifest).decode("utf-8"))
    except (UnicodeDecodeError, tomllib.TOMLDecodeError) as exc:
        raise SourceClosureError(f"invalid governed Cargo manifest: {manifest}") from exc
    if not isinstance(document, dict):
        raise SourceClosureError(f"invalid governed Cargo manifest: {manifest}")
    return document


def _cargo_config_ancestors(directory: PurePosixPath) -> tuple[PurePosixPath, ...]:
    ancestors: list[PurePosixPath] = []
    current = directory
    while True:
        ancestors.append(current)
        if current == PurePosixPath("."):
            return tuple(ancestors)
        current = current.parent


def _record_cargo_control(root: Path, relative: str, discovered: set[str]) -> bool:
    candidate = root / relative
    if candidate.is_symlink():
        raise SourceClosureError(f"Cargo compiler control is symlinked: {relative}")
    try:
        metadata = candidate.lstat()
    except FileNotFoundError:
        return False
    except OSError as exc:
        raise SourceClosureError(f"Cargo compiler control unavailable: {relative}") from exc
    if not stat.S_ISREG(metadata.st_mode):
        raise SourceClosureError(f"Cargo compiler control is not regular: {relative}")
    _read_source(root, relative)
    discovered.add(relative)
    return True


def _reject_target_directories(root: Path) -> None:
    for relative in (
        "zk/state_proof_risc0",
        "zk/zrpf_protocol",
        "zk/zrpf_risc0",
    ):
        for candidate in (root / relative).rglob("target"):
            if candidate.is_dir():
                raise SourceClosureError("compiler-visible source scope contains target directory")


def _git_output(root: Path, *args: str) -> str:
    try:
        result = subprocess.run(
            ["git", *args],
            cwd=root,
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=30,
        )
    except (OSError, subprocess.SubprocessError) as exc:
        raise SourceClosureError("git source identity command failed") from exc
    return result.stdout.strip()
