"""Closed task and artifact catalog for the ZRPF remote reproof handoff V2."""

from __future__ import annotations

from dataclasses import dataclass

MAX_ARTIFACT_BYTES = 64 * 1024 * 1024
MAX_IDENTITY_DOCUMENT_BYTES = 4 * 1024 * 1024
IDENTITY_RUN_ROOT = "/external/zrpf-remote-reproof-handoff-v2/identity/run"


@dataclass(frozen=True, slots=True)
class ArtifactSpec:
    role: str
    path: str
    kind: str
    producer_stage: str
    maximum_bytes: int = MAX_ARTIFACT_BYTES


@dataclass(frozen=True, slots=True)
class CommandSpec:
    runner: str
    argv: tuple[str, ...]
    stdin_artifact_role: str | None = None
    stdout_artifact_role: str | None = None


@dataclass(frozen=True, slots=True)
class TaskSpec:
    stage_id: str
    depends_on: tuple[str, ...]
    inputs: tuple[str, ...]
    outputs: tuple[str, ...]
    runner: str
    command: tuple[str, ...]
    success_predicates: tuple[str, ...]
    resource_class: str
    command_status: str = "template_available"
    execution_adapter_status: str = "missing"
    pre_commands: tuple[CommandSpec, ...] = ()
    stdin_artifact_role: str | None = None
    stdout_artifact_role: str | None = None


ARTIFACT_SPECS = (
    ArtifactSpec(
        "source_request",
        "inputs/source_request.json",
        "request",
        "external_operator",
        16 * 1024 * 1024,
    ),
    ArtifactSpec(
        "v7_guest_input",
        "inputs/v7_guest_input.bin",
        "guest_input",
        "external_operator",
        16 * 1024 * 1024,
    ),
    ArtifactSpec(
        "identity_plan",
        "identity/plan.json",
        "plan",
        "identity_rebuild",
        MAX_IDENTITY_DOCUMENT_BYTES,
    ),
    ArtifactSpec(
        "identity_observations",
        "identity/run/rebuild-observations.json",
        "observations",
        "identity_rebuild",
        MAX_IDENTITY_DOCUMENT_BYTES,
    ),
    ArtifactSpec(
        "identity_candidate_report",
        "identity/run/rebuild-candidate-report.json",
        "report",
        "identity_rebuild",
        MAX_IDENTITY_DOCUMENT_BYTES,
    ),
    ArtifactSpec("r0vm", "inputs/risc0-home/bin/r0vm", "executable", "external_operator"),
    ArtifactSpec(
        "source_program",
        "identity/run/outputs/01-source-spot/source_spot.bin",
        "risc0_program",
        "identity_rebuild",
    ),
    ArtifactSpec(
        "source_cli",
        "identity/run/outputs/01-source-spot/tau-state-proof-risc0-cli",
        "executable",
        "identity_rebuild",
    ),
    ArtifactSpec(
        "v2_adapter_program",
        "identity/run/outputs/02-v2-adapter/v2_adapter.bin",
        "risc0_program",
        "identity_rebuild",
    ),
    ArtifactSpec(
        "v6_leaf_program",
        "identity/run/outputs/03-v6-leaf/spot_value_leaf_v6.bin",
        "risc0_program",
        "identity_rebuild",
    ),
    ArtifactSpec(
        "v6_l1_program",
        "identity/run/outputs/04-v6-l1/spot_value_aggregate_l1_v6.bin",
        "risc0_program",
        "identity_rebuild",
    ),
    ArtifactSpec(
        "v6_l2_program",
        "identity/run/outputs/05-v6-l2/spot_value_aggregate_l2_v6.bin",
        "risc0_program",
        "identity_rebuild",
    ),
    ArtifactSpec(
        "v6_settlement_program",
        "identity/run/outputs/06-v6-settlement/source_opened_spot_settlement_v6.bin",
        "risc0_program",
        "identity_rebuild",
    ),
    ArtifactSpec(
        "post_pin_governance_result",
        "ancestry/post_pin_governance.json",
        "governance_record",
        "ancestry_materialization",
    ),
    ArtifactSpec(
        "v2_adapter_prover", "worker/bin/prove_v2_leaf_adapter", "executable", "worker_prover_build"
    ),
    ArtifactSpec(
        "v6_leaf_prover", "worker/bin/prove_spot_value_leaf_v6", "executable", "worker_prover_build"
    ),
    ArtifactSpec(
        "v6_l1_prover",
        "worker/bin/prove_spot_value_aggregate_l1_v6",
        "executable",
        "worker_prover_build",
    ),
    ArtifactSpec(
        "v6_l2_prover",
        "worker/bin/prove_spot_value_aggregate_l2_v6",
        "executable",
        "worker_prover_build",
    ),
    ArtifactSpec(
        "v6_settlement_prover",
        "worker/bin/prove_source_opened_spot_settlement_v6",
        "executable",
        "worker_prover_build",
    ),
    ArtifactSpec(
        "v6_host_verifier",
        "worker/bin/source-opened-spot-settlement-verifier-v6",
        "executable",
        "worker_prover_build",
    ),
    ArtifactSpec(
        "mutation_verifier",
        "worker/bin/verify-spot-v7-remote-mutations",
        "executable",
        "worker_prover_build",
    ),
    ArtifactSpec(
        "v7_program",
        "worker/programs/spot_settlement_v7.bin",
        "risc0_program",
        "worker_prover_build",
    ),
    ArtifactSpec(
        "v7_prover", "worker/bin/prove_spot_settlement_v7", "executable", "worker_prover_build"
    ),
    ArtifactSpec(
        "release_runtime_identity",
        "inputs/release_runtime_identity.json",
        "runtime_identity",
        "external_operator",
    ),
    ArtifactSpec(
        "source_proof", "proofs/source_proof.json", "receipt", "source_spot_proof", 16 * 1024 * 1024
    ),
    ArtifactSpec(
        "v2_adapter_receipt",
        "proofs/v2_adapter_receipt.json",
        "receipt",
        "v2_adapter_receipt",
        16 * 1024 * 1024,
    ),
    ArtifactSpec(
        "v2_adapter_report",
        "proofs/v2_adapter_report.json",
        "report",
        "v2_adapter_receipt",
    ),
    ArtifactSpec(
        "v6_leaf_envelope", "proofs/v6_leaf_envelope.bin", "guest_input", "v6_leaf_receipt"
    ),
    ArtifactSpec("v6_leaf_receipt", "proofs/v6_leaf_receipt.json", "receipt", "v6_leaf_receipt"),
    ArtifactSpec("v6_leaf_report", "proofs/v6_leaf_report.json", "report", "v6_leaf_receipt"),
    ArtifactSpec("v6_l1_receipt", "proofs/v6_l1_receipt.json", "receipt", "v6_l1_receipt"),
    ArtifactSpec("v6_l1_report", "proofs/v6_l1_report.json", "report", "v6_l1_receipt"),
    ArtifactSpec("v6_l2_receipt", "proofs/v6_l2_receipt.json", "receipt", "v6_l2_receipt"),
    ArtifactSpec("v6_l2_report", "proofs/v6_l2_report.json", "report", "v6_l2_receipt"),
    ArtifactSpec(
        "v6_settlement_receipt",
        "proofs/v6_settlement_receipt.json",
        "receipt",
        "v6_settlement_receipt",
    ),
    ArtifactSpec(
        "v6_settlement_journal",
        "proofs/v6_settlement_journal.bin",
        "journal",
        "v6_settlement_receipt",
    ),
    ArtifactSpec(
        "v6_settlement_guest_input",
        "proofs/v6_settlement_guest_input.bin",
        "guest_input",
        "v6_settlement_receipt",
    ),
    ArtifactSpec(
        "v6_settlement_replay", "proofs/v6_settlement_replay.bin", "replay", "v6_settlement_receipt"
    ),
    ArtifactSpec(
        "v6_settlement_da_certificate",
        "proofs/v6_settlement_da_certificate.bin",
        "certificate",
        "v6_settlement_receipt",
    ),
    ArtifactSpec(
        "v6_settlement_report",
        "proofs/v6_settlement_report.json",
        "report",
        "v6_settlement_receipt",
    ),
    ArtifactSpec(
        "v6_settlement_seal_mutation",
        "mutations/v6_settlement.json",
        "mutated_receipt",
        "v6_settlement_receipt",
    ),
    ArtifactSpec("v7_receipt", "proofs/v7_receipt.json", "receipt", "v7_receipt"),
    ArtifactSpec(
        "v7_seal_mutation", "proofs/v7_seal_mutation.json", "mutated_receipt", "v7_receipt"
    ),
    ArtifactSpec("v7_journal", "proofs/v7_journal.bin", "journal", "v7_receipt"),
    ArtifactSpec(
        "v7_verifier_output", "proofs/v7_verifier_output.bin", "verifier_output", "v7_receipt"
    ),
    ArtifactSpec("v7_plan_b", "proofs/v7_plan_b.bin", "plan", "v7_receipt"),
    ArtifactSpec("v7_report", "proofs/v7_report.json", "report", "v7_receipt"),
    ArtifactSpec(
        "v6_leaf_seal_mutation",
        "mutations/v6_leaf.json",
        "mutated_receipt",
        "mutation_verification",
        16 * 1024 * 1024,
    ),
    ArtifactSpec(
        "v6_l1_seal_mutation",
        "mutations/v6_l1.json",
        "mutated_receipt",
        "mutation_verification",
        16 * 1024 * 1024,
    ),
    ArtifactSpec(
        "v6_l2_seal_mutation",
        "mutations/v6_l2.json",
        "mutated_receipt",
        "mutation_verification",
        16 * 1024 * 1024,
    ),
    ArtifactSpec(
        "mutation_report",
        "mutations/report.json",
        "report",
        "mutation_verification",
        64 * 1024,
    ),
    ArtifactSpec("release_plan", "release/plan.json", "plan", "release_checks"),
    ArtifactSpec("release_evidence", "release/evidence.json", "report", "release_checks"),
)


TASK_SPECS = (
    TaskSpec(
        "identity_rebuild",
        (),
        ("r0vm",),
        (
            "identity_plan",
            "identity_observations",
            "identity_candidate_report",
            "source_program",
            "source_cli",
            "v2_adapter_program",
            "v6_leaf_program",
            "v6_l1_program",
            "v6_l2_program",
            "v6_settlement_program",
        ),
        "python3",
        (
            "tools/execute_zrpf_source_opened_spot_v6_identity_rebuild.py",
            "--plan",
            "@identity_plan",
            "--risc0-home",
            "@risc0_home",
            "--cargo-registry-dir",
            "@cargo_registry_dir",
            "--docker",
            "@docker",
        ),
        (
            "candidate identity report recomposes from the exact C0 source inventory",
            "all source through V6 program image IDs are nonzero and content-bound",
            "every authority field remains false",
        ),
        "cpu_high_memory",
        pre_commands=(
            CommandSpec(
                "python3",
                (
                    "tools/plan_zrpf_source_opened_spot_v6_identity_rebuild.py",
                    "plan",
                    "--source-commit",
                    "@c0_commit",
                    "--run-root",
                    IDENTITY_RUN_ROOT,
                    "--output",
                    "@identity_plan",
                ),
            ),
        ),
    ),
    TaskSpec(
        "ancestry_materialization",
        ("identity_rebuild",),
        ("identity_candidate_report",),
        ("post_pin_governance_result",),
        "python3",
        ("tools/check_zrpf_v6_v7_post_pin_governance.py",),
        (
            "C1 is the literal direct child of C0",
            "C2 is the literal direct child of C1",
            "G is the literal direct child of C2",
            "no replacement refs or grafts participate",
        ),
        "light",
        execution_adapter_status="implemented",
        stdout_artifact_role="post_pin_governance_result",
    ),
    TaskSpec(
        "worker_prover_build",
        ("ancestry_materialization",),
        ("post_pin_governance_result",),
        (
            "v2_adapter_prover",
            "v6_leaf_prover",
            "v6_l1_prover",
            "v6_l2_prover",
            "v6_settlement_prover",
            "v6_host_verifier",
            "mutation_verifier",
            "v7_program",
            "v7_prover",
        ),
        "cargo",
        (
            "+1.94.1",
            "build",
            "--manifest-path",
            "zk/spot_settlement_v7_risc0/Cargo.toml",
            "--locked",
            "--offline",
            "--release",
            "-p",
            "zenodex-zrpf-risc0-spot-settlement-v7-harness",
            "--bin",
            "prove_spot_settlement_v7",
        ),
        (
            "fresh target begins absent",
            "all worker executables are built at exact G",
            "V7 program image ID is recomputed by the pinned r0vm",
        ),
        "cpu_high_memory",
        pre_commands=(
            CommandSpec(
                "cargo",
                (
                    "+1.94.1",
                    "build",
                    "--manifest-path",
                    "zk/zrpf_risc0/Cargo.toml",
                    "--locked",
                    "--offline",
                    "--release",
                    "-p",
                    "zenodex-zrpf-risc0-harness",
                    "--features",
                    "spot-v6-methods",
                    "--bins",
                ),
            ),
            CommandSpec(
                "cargo",
                (
                    "+1.94.1",
                    "build",
                    "--manifest-path",
                    "zk/zrpf_risc0/Cargo.toml",
                    "--locked",
                    "--offline",
                    "--release",
                    "-p",
                    "zenodex-zrpf-risc0-verifier",
                    "--bins",
                ),
            ),
            CommandSpec(
                "cargo",
                (
                    "+1.94.1",
                    "build",
                    "--manifest-path",
                    "zk/spot_settlement_v7_risc0/Cargo.toml",
                    "--locked",
                    "--offline",
                    "--release",
                    "-p",
                    "zenodex-zrpf-risc0-spot-v7-remote-mutation-verifier",
                    "--bin",
                    "verify-spot-v7-remote-mutations",
                ),
            ),
        ),
    ),
    TaskSpec(
        "source_spot_proof",
        ("worker_prover_build",),
        ("source_request", "source_cli", "source_program", "r0vm"),
        ("source_proof",),
        "@source_cli",
        (),
        (
            "source request and proof share the exact state hash",
            "receipt is Succinct under the current source image ID",
            "canonical source proof bytes persist only after verification",
        ),
        "prover_heavy",
        execution_adapter_status="implemented",
        stdin_artifact_role="source_request",
        stdout_artifact_role="source_proof",
    ),
    TaskSpec(
        "v2_adapter_receipt",
        ("source_spot_proof",),
        ("source_proof", "source_program", "v2_adapter_program", "v2_adapter_prover"),
        ("v2_adapter_receipt", "v2_adapter_report"),
        "@v2_adapter_prover",
        (
            "--source-proof",
            "@source_proof",
            "--receipt-out",
            "@v2_adapter_receipt",
            "--ordinal",
            "0",
        ),
        (
            "source receipt is verified before journal decoding",
            "adapter journal binds the exact source program and proof profile",
            "adapter receipt is Succinct and canonically encoded",
        ),
        "prover_heavy",
        execution_adapter_status="implemented",
        stdout_artifact_role="v2_adapter_report",
    ),
    TaskSpec(
        "v6_leaf_receipt",
        ("v2_adapter_receipt",),
        (
            "source_request",
            "source_proof",
            "v2_adapter_receipt",
            "v6_leaf_program",
            "v6_leaf_prover",
        ),
        ("v6_leaf_envelope", "v6_leaf_receipt", "v6_leaf_report"),
        "@v6_leaf_prover",
        (
            "--receipt-out",
            "@v6_leaf_receipt",
            "--source-envelope-out",
            "@v6_leaf_envelope",
            "--source-request",
            "@source_request",
            "--source-proof",
            "@source_proof",
            "--adapter-receipt",
            "@v2_adapter_receipt",
        ),
        (
            "the exact V2 adapter receipt is verified",
            "the leaf statement is independently recomposed",
            "the V6 leaf receipt verifies under its exact program identity",
        ),
        "prover_heavy",
        execution_adapter_status="implemented",
        stdout_artifact_role="v6_leaf_report",
    ),
    TaskSpec(
        "v6_l1_receipt",
        ("v6_leaf_receipt",),
        ("v6_leaf_receipt", "v6_l1_program", "v6_l1_prover"),
        ("v6_l1_receipt", "v6_l1_report"),
        "@v6_l1_prover",
        ("--receipt-out", "@v6_l1_receipt", "--child", "@v6_leaf_receipt"),
        (
            "the exact V6 leaf child verifies",
            "the L1 journal is independently recomposed",
            "the L1 receipt verifies under its exact program identity",
        ),
        "prover_heavy",
        execution_adapter_status="implemented",
        stdout_artifact_role="v6_l1_report",
    ),
    TaskSpec(
        "v6_l2_receipt",
        ("v6_l1_receipt",),
        ("v6_l1_receipt", "v6_l2_program", "v6_l2_prover"),
        ("v6_l2_receipt", "v6_l2_report"),
        "@v6_l2_prover",
        ("--receipt-out", "@v6_l2_receipt", "--child", "@v6_l1_receipt"),
        (
            "the exact V6 L1 child verifies",
            "the L2 journal is independently recomposed",
            "the L2 receipt verifies under its exact program identity",
        ),
        "prover_heavy",
        execution_adapter_status="implemented",
        stdout_artifact_role="v6_l2_report",
    ),
    TaskSpec(
        "v6_settlement_receipt",
        ("v6_l2_receipt",),
        ("v6_leaf_envelope", "v6_l2_receipt", "v6_settlement_program", "v6_settlement_prover"),
        (
            "v6_settlement_receipt",
            "v6_settlement_journal",
            "v6_settlement_guest_input",
            "v6_settlement_replay",
            "v6_settlement_da_certificate",
            "v6_settlement_report",
            "v6_settlement_seal_mutation",
        ),
        "@v6_settlement_prover",
        (
            "--receipt-out",
            "@v6_settlement_receipt",
            "--journal-out",
            "@v6_settlement_journal",
            "--mutation-out",
            "@v6_settlement_seal_mutation",
            "--guest-input-out",
            "@v6_settlement_guest_input",
            "--replay-out",
            "@v6_settlement_replay",
            "--da-certificate-out",
            "@v6_settlement_da_certificate",
            "--source-envelope",
            "@v6_leaf_envelope",
            "--l2-receipt",
            "@v6_l2_receipt",
        ),
        (
            "the exact V6 L2 child verifies",
            "settlement input and journal are independently recomposed",
            "the settlement receipt verifies under its exact program identity",
        ),
        "prover_heavy",
        execution_adapter_status="implemented",
        stdout_artifact_role="v6_settlement_report",
    ),
    TaskSpec(
        "v7_receipt",
        ("v6_settlement_receipt",),
        ("v6_settlement_receipt", "v7_guest_input", "v7_program", "v7_prover"),
        (
            "v7_receipt",
            "v7_seal_mutation",
            "v7_journal",
            "v7_verifier_output",
            "v7_plan_b",
            "v7_report",
        ),
        "@v7_prover",
        (
            "--v7-receipt-out",
            "@v7_receipt",
            "--v7-receipt-seal-mutation-out",
            "@v7_seal_mutation",
            "--v7-journal-out",
            "@v7_journal",
            "--v7-verifier-output-out",
            "@v7_verifier_output",
            "--v7-plan-b-out",
            "@v7_plan_b",
            "--v6-child-receipt",
            "@v6_settlement_receipt",
            "--v7-guest-input",
            "@v7_guest_input",
        ),
        (
            "the exact V6 settlement child verifies",
            "the V7 journal and Plan B projection agree",
            "the exact V7 seal mutation rejects",
        ),
        "prover_heavy",
        execution_adapter_status="implemented",
        stdout_artifact_role="v7_report",
    ),
    TaskSpec(
        "mutation_verification",
        ("v7_receipt",),
        (
            "v6_leaf_envelope",
            "v6_settlement_guest_input",
            "v7_guest_input",
            "v6_leaf_program",
            "v6_l1_program",
            "v6_l2_program",
            "v6_settlement_program",
            "v7_program",
            "v6_leaf_receipt",
            "v6_l1_receipt",
            "v6_l2_receipt",
            "v6_settlement_receipt",
            "v7_receipt",
            "v7_seal_mutation",
            "v6_settlement_seal_mutation",
            "mutation_verifier",
        ),
        (
            "v6_leaf_seal_mutation",
            "v6_l1_seal_mutation",
            "v6_l2_seal_mutation",
            "mutation_report",
        ),
        "@mutation_verifier",
        (
            "--leaf-source-envelope",
            "@v6_leaf_envelope",
            "--settlement-guest-input",
            "@v6_settlement_guest_input",
            "--v7-guest-input",
            "@v7_guest_input",
            "--leaf-program",
            "@v6_leaf_program",
            "--level-one-program",
            "@v6_l1_program",
            "--level-two-program",
            "@v6_l2_program",
            "--settlement-program",
            "@v6_settlement_program",
            "--v7-program",
            "@v7_program",
            "--leaf-receipt",
            "@v6_leaf_receipt",
            "--level-one-receipt",
            "@v6_l1_receipt",
            "--level-two-receipt",
            "@v6_l2_receipt",
            "--settlement-receipt",
            "@v6_settlement_receipt",
            "--v7-receipt",
            "@v7_receipt",
            "--settlement-mutation",
            "@v6_settlement_seal_mutation",
            "--v7-mutation",
            "@v7_seal_mutation",
            "--leaf-mutation-out",
            "@v6_leaf_seal_mutation",
            "--level-one-mutation-out",
            "@v6_l1_seal_mutation",
            "--level-two-mutation-out",
            "@v6_l2_seal_mutation",
        ),
        (
            "each accepted receipt verifies before mutation",
            "one exact seal mutation per proof stage rejects at the cryptographic verifier",
            "the mutation report binds every positive and negative receipt digest",
        ),
        "prover_light",
        execution_adapter_status="implemented",
        stdout_artifact_role="mutation_report",
    ),
    TaskSpec(
        "release_checks",
        ("mutation_verification",),
        (
            "identity_plan",
            "identity_observations",
            "identity_candidate_report",
            "post_pin_governance_result",
            "mutation_report",
            "v7_report",
            "release_runtime_identity",
        ),
        ("release_plan", "release_evidence"),
        "python3",
        (
            "tools/check_zrpf_spot_v7_release_closure.py",
            "--repository",
            "@repo",
            "--plan",
            "@release_plan",
            "--runtime-identity",
            "@release_runtime_identity",
            "--expected-plan-sha256",
            "@release_plan_sha256",
        ),
        (
            "a future bundle-aware adapter consumes exact returned proof and mutation artifacts",
            "the existing repository release checker remains a non-authoritative template",
            "production release settlement and ledger authority remain false",
        ),
        "light",
        "template_planned",
        pre_commands=(
            CommandSpec(
                "python3",
                (
                    "tools/plan_zrpf_spot_v7_release_closure.py",
                    "--repository",
                    "@repo",
                    "--runtime-identity",
                    "@release_runtime_identity",
                ),
                stdout_artifact_role="release_plan",
            ),
        ),
        stdout_artifact_role="release_evidence",
    ),
)
