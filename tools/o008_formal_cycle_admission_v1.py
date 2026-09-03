#!/usr/bin/env python3
"""Pure admission core for the O-008 formal-cycle evidence packet (schema v3).

This module is the functional core behind ``tools/check_o008_formal_cycle_v1.py``
and ``tools/build_o008_formal_cycle_v1.py``. It performs no I/O: every input is
bytes or an already-decoded value supplied by the imperative shell in
``tools/o008_formal_cycle_shell_v1.py``, and every output is a value.

Contract:

* ``project_packet_v1`` turns one exact source commit S (a ``SubjectSnapshotV1``)
  into the only admissible packet content. The builder writes that projection;
  the checker recomputes it and requires byte equality.
* ``admit_packet_v1`` compares a committed packet against the projection of S and
  against the Git topology of its packet commit P. Every finding is a structured
  ``AdmissionErrorV1`` with a closed code.
* ``evaluate_proof_replay_v1`` grades observations recorded by the shell when the
  recorded proof tools were actually executed. Without observations the status
  is ``NOT_RUN``; a packet author's record never upgrades it.

Authority: NONE. ``CLAIM_CEILING_V1`` is emitted from module constants and no
packet content can raise it.
"""

from __future__ import annotations

import ast
import functools
import hashlib
import json
import re
import tomllib
import unicodedata
from collections.abc import Callable, Mapping, Sequence
from dataclasses import dataclass, field
from typing import Any, Final, NoReturn

import yaml  # type: ignore[import-untyped]

from tools.scan_lean_proof_placeholders_v1 import ScanError, scan_text, strip_lean_noncode

# ---------------------------------------------------------------------------
# Closed constants
# ---------------------------------------------------------------------------

PACKET_SCHEMA_V15: Final = "zenodex/o008-formal-cycle-evidence/v15"
REPORT_SCHEMA_V3: Final = "zenodex/o008-formal-cycle-admission-report/v3"
PACKET_JSON_PATH_V1: Final = "docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json"
PACKET_MD_PATH_V1: Final = "docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.md"
PACKET_WRITE_SET_V1: Final[tuple[tuple[str, str], ...]] = (
    ("M", PACKET_JSON_PATH_V1),
    ("M", PACKET_MD_PATH_V1),
)
MAX_PACKET_BYTES_V1: Final = 1 << 20
MAX_SOURCE_BLOB_BYTES_V1: Final = 8 << 20
GIT_BLOB_MODE_V1: Final = "100644"

CHECKER_PATH_V1: Final = "tools/check_o008_formal_cycle_v1.py"
CORE_PATH_V1: Final = "tools/o008_formal_cycle_admission_v1.py"
SHELL_PATH_V1: Final = "tools/o008_formal_cycle_shell_v1.py"
BUILDER_PATH_V1: Final = "tools/build_o008_formal_cycle_v1.py"
SCANNER_PATH_V1: Final = "tools/scan_lean_proof_placeholders_v1.py"
GATE_TESTS_PATH_V1: Final = "tests/test_check_o008_formal_cycle_v1.py"
PYTHON_REFINEMENT_PATH_V1: Final = "src/core/global_economic_state_effect_refinement_v1.py"
RUST_REFINEMENT_PATH_V1: Final = (
    "zk/global_settlement_abi_v1/src/global_economic_state_effect_refinement.rs"
)
GOLDEN_RENDERER_PATH_V1: Final = "tools/render_global_claimant_backing_guard_v1_golden.py"
GOLDEN_FIXTURE_PATH_V1: Final = "tests/data/global_claimant_backing_guard_v1_golden.json"
GOLDEN_PYTHON_TEST_PATH_V1: Final = "tests/core/test_global_claimant_backing_guard_v1_golden.py"
GOLDEN_RUST_TEST_PATH_V1: Final = "zk/global_settlement_abi_v1/tests/claimant_backing_guard_golden.rs"
CERTIFICATE_PYTHON_PATH_V1: Final = "src/core/global_accounting_allocation_certificate_v1.py"
CERTIFICATE_RUST_PATH_V1: Final = "zk/global_settlement_abi_v1/src/global_accounting_allocation_certificate.rs"
CERTIFICATE_RENDERER_PATH_V1: Final = "tools/render_global_accounting_allocation_certificate_v1_golden.py"
CERTIFICATE_FIXTURE_PATH_V1: Final = "tests/data/global_accounting_allocation_certificate_v1_golden.json"
CERTIFICATE_PYTHON_TEST_PATH_V1: Final = "tests/core/test_global_accounting_allocation_certificate_v1_golden.py"
CERTIFICATE_RUST_TEST_PATH_V1: Final = "zk/global_settlement_abi_v1/tests/global_accounting_allocation_certificate_golden.rs"
CERTIFICATE_LEAN_PATH_V1: Final = "lean-mathlib/Proofs/GlobalAccountingAllocationCertificateV1.lean"
CERTIFICATE_LEAN_GATE_PATH_V1: Final = "tests/formal/test_lean_global_accounting_allocation_certificate_v1.py"
CERTIFICATE_ESSO_MODEL_PATH_V1: Final = "src/kernels/dex/global_accounting_allocation_certificate_v1.yaml"
CERTIFICATE_ESSO_GATE_PATH_V1: Final = "tests/formal/test_esso_global_accounting_allocation_certificate_v1.py"
PRODUCERS_PYTHON_PATH_V1: Final = "src/core/global_accounting_lane_producers_v1.py"
PRODUCERS_RUST_PATH_V1: Final = "zk/global_settlement_abi_v1/src/global_accounting_lane_producers.rs"
PRODUCERS_PYTHON_TEST_PATH_V1: Final = "tests/core/test_global_accounting_lane_producers_v1.py"
PRODUCERS_RUST_TEST_PATH_V1: Final = "zk/global_settlement_abi_v1/tests/global_accounting_lane_producers.rs"
ADMISSION_RUST_PATH_V1: Final = "zk/global_settlement_abi_v1/src/asset_transfer_receipt_admission.rs"
ADMISSION_RUST_TEST_PATH_V1: Final = "zk/global_settlement_abi_v1/tests/lane_module_release_route_binding.rs"
ADMISSION_RUST_WITNESS_PATH_V1: Final = "zk/global_settlement_abi_v1/src/lane_module_receipt_verification.rs"
PROJECTION_PYTHON_PATH_V1: Final = "src/core/global_accounting_allocation_projection_v1.py"
PROJECTION_PYTHON_TEST_PATH_V1: Final = "tests/core/test_global_accounting_allocation_projection_v1.py"
# C9c-2: the mutation ledger executes the declared rows of the packets that carry mechanical
# mutants. Before this gate the rows were executed only by hand, which is the same standing the
# string-only rows had. The expected kill counts are pinned so a row cannot be quietly dropped.
LEDGER_TOOL_PATH_V1: Final = "tools/thv1_mutation_ledger_v1.py"
LEDGER_GATED_PACKETS_V1: Final[tuple[tuple[str, str, int], ...]] = (
    ("ledger_projection_rows", "THV1-20260903-global-accounting-allocation-projection-v5", 29),
    ("ledger_tool_rows", "THV1-20260903-thv1-mutation-ledger-v6", 21),
    ("ledger_checker_rows", "THV1-20260901-o008-formal-cycle-admission-v38", 3),
    ("ledger_admission_rows", "THV1-20260903-o008-asset-transfer-receipt-admission-mechanical-v3", 31),
    ("ledger_ownership_rows", "THV1-20260903-global-settlement-exact-ownership-mechanical-v3", 21),
    ("ledger_certificate_rows", "THV1-20260901-global-accounting-allocation-certificate-v23", 2),
    ("ledger_lineage_rows", "THV1-20260902-test-hygiene-lineage-ordering-v5", 1),
)
PYTHON_TYPES_PATH_V1: Final = "src/core/global_settlement_types_v1.py"
RUST_STATE_PATH_V1: Final = "zk/global_settlement_abi_v1/src/state.rs"
RUST_LIB_PATH_V1: Final = "zk/global_settlement_abi_v1/src/lib.rs"
RUST_MANIFEST_PATH_V1: Final = "zk/global_settlement_abi_v1/Cargo.toml"
RUST_GATE_PATH_V1: Final = "zk/global_settlement_abi_v1/tests/v1_projection_gate.rs"
RUST_BOUNDED_VEC_PATH_V1: Final = "zk/global_settlement_abi_v1/src/bounded_vec.rs"
RUST_LOCKFILE_PATH_V1: Final = "zk/global_settlement_abi_v1/Cargo.lock"
# Cargo reads these from the crate directory upward; none may exist at the subject commit,
# at HEAD, or in the worktree, so no config can redirect sources, wrap rustc, or add flags.
CARGO_CONFIG_FORBIDDEN_PATHS_V1: Final[tuple[str, ...]] = (
    ".cargo/config.toml",
    ".cargo/config",
    "zk/.cargo/config.toml",
    "zk/.cargo/config",
    "zk/global_settlement_abi_v1/.cargo/config.toml",
    "zk/global_settlement_abi_v1/.cargo/config",
)
RUST_CRATE_DIR_V1: Final = "zk/global_settlement_abi_v1"
RUST_CRATE_NAME_V1: Final = "zenodex-global-settlement-abi-v1"
RUST_GATE_TARGET_V1: Final = "v1_projection_gate"
RUST_BOUNDED_VEC_UNIT_FILTER_V1: Final = "bounded_vec::tests::"
RUST_BOUNDED_VEC_UNIT_GATE_EXPECTED_PASSED_V1: Final = 1
PYTHON_GATE_PATH_V1: Final = "tests/test_o008_v1_projection_runtime_gate.py"
ESSO_MODEL_PATH_V1: Final = "src/kernels/dex/global_claimant_custody_certificate_v1.yaml"
ESSO_GATE_PATH_V1: Final = "tests/formal/test_esso_global_claimant_custody_certificate_v1.py"
LEAN_PROOF_PATH_V1: Final = "lean-mathlib/Proofs/GlobalClaimantCustodyRelationV1.lean"
LEAN_ROOT_PATH_V1: Final = "lean-mathlib/Proofs.lean"
LEAN_TOOLCHAIN_PATH_V1: Final = "lean-mathlib/lean-toolchain"
LEAN_GATE_PATH_V1: Final = "tests/formal/test_lean_global_claimant_custody_relation_v1.py"
HYGIENE_EVIDENCE_DIR_V1: Final = "tests/evidence/test_hygiene"
HYGIENE_SCHEMA_V1: Final = "zenodex/test-hygiene-evidence/v1"
BLUEPRINT_PATH_V1: Final = "docs/research/ZENODEX_GLOBAL_FUNCTIONAL_CORE_FORMAL_BLUEPRINT_V1.md"
PRIOR_ESSO_GATE_PATH_V1: Final = "tests/formal/test_esso_global_settlement_core_v1.py"

TRANSFER_REFINEMENT_LEAN_PATH_V1: Final = "lean-mathlib/Proofs/AssetTransferRefinementV1.lean"
TRANSFER_REFINEMENT_CHALLENGE_PATH_V1: Final = "lean-mathlib/Proofs/AssetTransferRefinementV1Challenge.lean"
TRANSFER_REFINEMENT_TOOL_PATH_V1: Final = "tools/check_asset_transfer_refinement_v1.py"
TRANSFER_REFINEMENT_CORPUS_PATH_V1: Final = "tests/data/asset_transfer_refinement_v1.json"
TRANSFER_REFINEMENT_GATE_PATH_V1: Final = "tests/formal/test_lean_asset_transfer_refinement_v1.py"
TRANSFER_REFINEMENT_GATE_EXPECTED_PASSED_V1: Final = 40
PARITY_GATE_PATH_V1: Final = "tests/core/test_global_settlement_abi_v1_resource_bounds.py"
PARITY_GATE_EXPECTED_PASSED_V1: Final = 17
CANDIDATE_CHAIN_SCRIPT_PATH_V1: Final = "tools/formal_core_candidate_chain_v1.sh"
CANDIDATE_BATTERY_SCRIPT_PATH_V1: Final = "tools/formal_core_battery_v1.sh"

SOURCE_PIN_ROLES_V1: Final[tuple[tuple[str, str], ...]] = (
    (PYTHON_REFINEMENT_PATH_V1, "python_visible_necessary_checks"),
    (RUST_REFINEMENT_PATH_V1, "rust_visible_necessary_checks"),
    (GOLDEN_RENDERER_PATH_V1, "claimant_backing_guard_golden_renderer"),
    (GOLDEN_FIXTURE_PATH_V1, "claimant_backing_guard_golden_fixture"),
    (GOLDEN_PYTHON_TEST_PATH_V1, "claimant_backing_guard_golden_python_replay"),
    (GOLDEN_RUST_TEST_PATH_V1, "claimant_backing_guard_golden_rust_replay"),
    (CERTIFICATE_PYTHON_PATH_V1, "allocation_certificate_python_checker"),
    (CERTIFICATE_RUST_PATH_V1, "allocation_certificate_rust_twin"),
    (CERTIFICATE_RENDERER_PATH_V1, "allocation_certificate_golden_renderer"),
    (CERTIFICATE_FIXTURE_PATH_V1, "allocation_certificate_golden_fixture"),
    (CERTIFICATE_PYTHON_TEST_PATH_V1, "allocation_certificate_golden_python_replay"),
    (CERTIFICATE_RUST_TEST_PATH_V1, "allocation_certificate_golden_rust_replay"),
    (CERTIFICATE_LEAN_PATH_V1, "allocation_certificate_bounded_lean_model"),
    (CERTIFICATE_LEAN_GATE_PATH_V1, "allocation_certificate_lean_binding_gate"),
    (CERTIFICATE_ESSO_MODEL_PATH_V1, "allocation_certificate_bounded_esso_model"),
    (CERTIFICATE_ESSO_GATE_PATH_V1, "allocation_certificate_esso_replay_gate"),
    (PRODUCERS_PYTHON_PATH_V1, "registered_empty_lane_producers_python"),
    (PRODUCERS_RUST_PATH_V1, "registered_empty_lane_producers_rust"),
    (PRODUCERS_PYTHON_TEST_PATH_V1, "registered_empty_lane_producers_python_replay"),
    (PRODUCERS_RUST_TEST_PATH_V1, "registered_empty_lane_producers_rust_replay"),
    (PYTHON_TYPES_PATH_V1, "python_v1_wire_schema"),
    (RUST_STATE_PATH_V1, "rust_v1_wire_schema"),
    (RUST_LIB_PATH_V1, "rust_crate_root_module_closure"),
    (RUST_MANIFEST_PATH_V1, "rust_crate_manifest_closure"),
    (RUST_BOUNDED_VEC_PATH_V1, "rust_bounded_vec_deserializer_closure"),
    (RUST_LOCKFILE_PATH_V1, "rust_crate_lockfile"),
    (PYTHON_GATE_PATH_V1, "python_runtime_projection_gate"),
    (RUST_GATE_PATH_V1, "rust_compiled_projection_gate"),
    (ESSO_MODEL_PATH_V1, "bounded_exact_target_model"),
    (ESSO_GATE_PATH_V1, "esso_replay_mutation_and_v1_information_loss_gate"),
    (LEAN_PROOF_PATH_V1, "machine_checked_relation_and_no_recovery_theorems"),
    (LEAN_ROOT_PATH_V1, "lean_library_import_root"),
    (LEAN_TOOLCHAIN_PATH_V1, "lean_toolchain_pin"),
    (LEAN_GATE_PATH_V1, "lean_source_binding_compilation_and_axiom_gate"),
    (SCANNER_PATH_V1, "lean_placeholder_scanner"),
    (CORE_PATH_V1, "admission_core"),
    (SHELL_PATH_V1, "admission_shell"),
    (CHECKER_PATH_V1, "admission_cli"),
    (BUILDER_PATH_V1, "packet_builder_cli"),
    (GATE_TESTS_PATH_V1, "admission_gate_tests"),
    (BLUEPRINT_PATH_V1, "corrected_prior_formal_blueprint"),
    (PRIOR_ESSO_GATE_PATH_V1, "prior_model_semantic_restage_gate"),
    (TRANSFER_REFINEMENT_LEAN_PATH_V1, "transfer_refinement_bounded_lean_model"),
    (TRANSFER_REFINEMENT_CHALLENGE_PATH_V1, "transfer_refinement_lean_challenge"),
    (TRANSFER_REFINEMENT_TOOL_PATH_V1, "transfer_refinement_corpus_oracle"),
    (TRANSFER_REFINEMENT_CORPUS_PATH_V1, "transfer_refinement_bounded_corpus"),
    (TRANSFER_REFINEMENT_GATE_PATH_V1, "transfer_refinement_replay_gate"),
    (PARITY_GATE_PATH_V1, "python_rust_bound_parity_gate"),
    (CANDIDATE_CHAIN_SCRIPT_PATH_V1, "candidate_chain_script"),
    (CANDIDATE_BATTERY_SCRIPT_PATH_V1, "candidate_battery_script"),
    (ADMISSION_RUST_PATH_V1, "admission_rust_twin"),
    (ADMISSION_RUST_TEST_PATH_V1, "admission_rust_replay"),
    (ADMISSION_RUST_WITNESS_PATH_V1, "admission_rust_witness_source"),
    (PROJECTION_PYTHON_PATH_V1, "allocation_projection"),
    (PROJECTION_PYTHON_TEST_PATH_V1, "allocation_projection_replay"),
    (LEDGER_TOOL_PATH_V1, "thv1_mutation_ledger"),
    ("tools/test_hygiene_evidence_v1.py", "thv1_evidence_loader"),
    ("tools/test_hygiene_model_v1.py", "thv1_evidence_model"),
)
SOURCE_PIN_PATHS_V1: Final[tuple[str, ...]] = tuple(path for path, _ in SOURCE_PIN_ROLES_V1)
EXECUTING_TOOL_PATHS_V1: Final[tuple[str, ...]] = (
    CHECKER_PATH_V1,
    CORE_PATH_V1,
    SHELL_PATH_V1,
    SCANNER_PATH_V1,
)
THV1_REQUIRED_PIN_PATHS_V1: Final[tuple[str, ...]] = (
    CHECKER_PATH_V1,
    CORE_PATH_V1,
    SHELL_PATH_V1,
    BUILDER_PATH_V1,
    SCANNER_PATH_V1,
    LEAN_PROOF_PATH_V1,
    LEAN_ROOT_PATH_V1,
    ESSO_MODEL_PATH_V1,
    PYTHON_TYPES_PATH_V1,
    RUST_STATE_PATH_V1,
    RUST_LIB_PATH_V1,
    RUST_MANIFEST_PATH_V1,
    RUST_BOUNDED_VEC_PATH_V1,
    RUST_LOCKFILE_PATH_V1,
    PYTHON_REFINEMENT_PATH_V1,
    RUST_REFINEMENT_PATH_V1,
    GOLDEN_RENDERER_PATH_V1,
    GOLDEN_FIXTURE_PATH_V1,
    GOLDEN_PYTHON_TEST_PATH_V1,
    GOLDEN_RUST_TEST_PATH_V1,
    CERTIFICATE_PYTHON_PATH_V1,
    CERTIFICATE_RUST_PATH_V1,
    CERTIFICATE_RENDERER_PATH_V1,
    CERTIFICATE_FIXTURE_PATH_V1,
    CERTIFICATE_PYTHON_TEST_PATH_V1,
    CERTIFICATE_RUST_TEST_PATH_V1,
    CERTIFICATE_LEAN_PATH_V1,
    CERTIFICATE_LEAN_GATE_PATH_V1,
    CERTIFICATE_ESSO_MODEL_PATH_V1,
    CERTIFICATE_ESSO_GATE_PATH_V1,
    PRODUCERS_PYTHON_PATH_V1,
    PRODUCERS_RUST_PATH_V1,
    PRODUCERS_PYTHON_TEST_PATH_V1,
    PRODUCERS_RUST_TEST_PATH_V1,
    PYTHON_GATE_PATH_V1,
    RUST_GATE_PATH_V1,
    GATE_TESTS_PATH_V1,
    LEAN_GATE_PATH_V1,
    ESSO_GATE_PATH_V1,
    TRANSFER_REFINEMENT_LEAN_PATH_V1,
    TRANSFER_REFINEMENT_CHALLENGE_PATH_V1,
    TRANSFER_REFINEMENT_TOOL_PATH_V1,
    TRANSFER_REFINEMENT_CORPUS_PATH_V1,
    TRANSFER_REFINEMENT_GATE_PATH_V1,
    PARITY_GATE_PATH_V1,
    CANDIDATE_CHAIN_SCRIPT_PATH_V1,
    CANDIDATE_BATTERY_SCRIPT_PATH_V1,
    ADMISSION_RUST_PATH_V1,
    ADMISSION_RUST_TEST_PATH_V1,
    ADMISSION_RUST_WITNESS_PATH_V1,
    PROJECTION_PYTHON_PATH_V1,
    PROJECTION_PYTHON_TEST_PATH_V1,
    LEDGER_TOOL_PATH_V1,
    "tools/test_hygiene_evidence_v1.py",
    "tools/test_hygiene_model_v1.py",
)

PACKET_KEYS_V3: Final[frozenset[str]] = frozenset(
    {
        "schema",
        "created_date",
        "subject_commit",
        "subject_parent",
        "subject_tree",
        "packet_commit_parent",
        "packet_write_set",
        "claim_ceiling",
        "completion_scope",
        "source_pins",
        "esso_evidence",
        "lean_evidence",
        "v1_information_loss",
        "hygiene_selection",
        "lane_source_data",
        "required_sidecar",
        "proof_replay",
        "nonclaims",
    }
)

AUTHORITY_FIELDS_V1: Final[tuple[str, ...]] = (
    "production_authority",
    "settlement_authority",
    "release_authority",
    "verifier_authority",
    "migration_authority",
    "publication_authority",
    "value_movement_authority",
)
CLAIM_CEILING_V1: Final[dict[str, object]] = {
    "formal_cycle_status": "FORMAL_CYCLE_COMPLETE_O008_OPEN",
    "supported_claim": "O008_RELATION_NECESSARY_CHECKS_AND_INFORMATION_LOSS_PROVED",
    "o008_status": "OPEN_EXACT_ALL_12_RECONCILIATION_MISSING",
    "formal_core_complete": False,
    "whole_value_movement_safe": False,
    "value_movement_gates_closed": 0,
    "value_movement_gates_total": 12,
    **{field: "NONE" for field in AUTHORITY_FIELDS_V1},
}

CERTIFICATE_FIXTURE_VECTORS_V1: Final = 29

COMPLETION_SCOPE_V1: Final[tuple[str, ...]] = (
    "Python and Rust reject V1-state-visible same-control-domain claimant underbacking",
    "Python and Rust reject aggregate OPEN-terminal amounts above the same claimant's"
    " visible entitlements",
    "Python and Rust replay one rendered claimant-backing golden vector: states, view bytes,"
    " view roots, closed reject codes with fixed precedence, and byte-identical messages",
    "ESSO proves the bounded exact claimant/control-domain partition inductive with Z3 and CVC5"
    " under five substantive invariants",
    "Lean proves the bounded necessary relation, the exact current-profile relation, exact"
    " deposit/drain preservation, strict weakening of the aggregate and reserve-inclusive"
    " predicates, reserve independence (definitional, disclosed), and V1 terminal"
    " control-domain information loss",
    "the old bounded formal blueprint no longer maps terminal metadata into the owned-atom sum",
    "all twelve lanes were audited for exact reconciliation source data",
    "the smallest wire-compatible sidecar contract and its missing producer/proof obligations"
    " are specified under the control-domain vocabulary",
    "the GlobalAccountingAllocationCertificateV1 checker is implemented in Python and Rust with a"
    " producer registry exhaustive over the twelve lanes and ASSET_TRANSFER registered receipt-backed behind"
    " the witness-slot gate, and both"
    f" replay one rendered golden vector of {CERTIFICATE_FIXTURE_VECTORS_V1} state/certificate pairs"
    " with closed reject codes; the fixture accepts only the registered-empty certificate over an"
    " all-lanes-disabled state, and the witnessed asset-transfer acceptance is exercised in-process with"
    " a real minted witness",
    "the first receipt-backed fragment producer (wave B, ASSET_TRANSFER) is implemented in Python and"
    " Rust as a pure fold of one accepted lane-module transition, binding the fragment to the journal"
    " receipt root with eleven closed reject codes; only the receipt root carries the custody rows and"
    " chain/epoch context, so fragment integrity rests on C9 receipt admission; the certificate"
    " registry registers ASSET_TRANSFER receipt-backed behind the witness-slot gate, so its fragments"
    " enter the certificate only as the sealed witness, and the"
    " controlled-side fold ceiling is unreachable for well-formed inputs whose supply conservation"
    " bounds custody totals",
    "a bounded Lean model of the certificate relation derives the normative partition, same-domain"
    " backing, open-terminal coverage, exact current-profile custody under zero reserves and external"
    " obligations, and that without a receipt-backed producer only the registered-empty certificate is"
    " accepted, with a counterexample that a reserve never covers a missing claimant entitlement",
    "a bounded ESSO model of the certificate relation is inductive under Z3 and CVC5 for eight"
    " invariants (lane partition, row equality, custody aggregate, terminal bound, producer gate, lane"
    " binding, and the derived normative partition and same-domain backing) with eight named mutants,"
    " each caught by its attributed invariant alone and each two-solver counterexample falsifying that"
    " invariant on its post state; the two derived invariants are conclusions and carry no mutant",
    "the EXTERNAL_CUSTODY and PROOF_REWARDS registered-empty fragment producers are pure functions"
    " of the committed lane root that certify the lane is disabled and committed at the root of its"
    " unique empty typed lane state, in Python and Rust, and the certificate checker rejects a"
    " registered-empty lane committed at any other root",
)

EXPECTED_LANES_V1: Final[tuple[str, ...]] = (
    "ASSET_TRANSFER",
    "SPOT_LIQUIDITY",
    "FARM_INCENTIVES",
    "ZDEX_TOKENOMICS",
    "ZUSD_MONETARY",
    "PERPS_MARKET",
    "ORACLE_MARKET",
    "SEALED_AUCTION",
    "STRATEGY_ESCROW",
    "PROOF_REWARDS",
    "EXTERNAL_CUSTODY",
    "GOVERNANCE_MIGRATION",
)
LANE_STATUS_VOCABULARY_V1: Final[tuple[str, ...]] = (
    "PARTIAL",
    "MISSING",
    "NARROW_FRAGMENT_ONLY",
    "EMPTY_ROOT_UNBOUND",
)
LANE_SOURCE_DATA_V1: Final[tuple[tuple[str, str, str], ...]] = (
    ("ASSET_TRANSFER", "PARTIAL", "claimant entitlement and reserve classification"),
    ("SPOT_LIQUIDITY", "PARTIAL", "LP ownership and terminal detail behind opaque roots"),
    ("FARM_INCENTIVES", "MISSING", "V1 projection and receipt producer"),
    (
        "ZDEX_TOKENOMICS",
        "PARTIAL",
        "staking treasury host reward and cover-reserve allocation preimages",
    ),
    ("ZUSD_MONETARY", "MISSING", "matching Python/Rust V1 projection and receipt path"),
    (
        "PERPS_MARKET",
        "NARROW_FRAGMENT_ONLY",
        "full-lane producer beyond margin deposit withdraw and close",
    ),
    ("ORACLE_MARKET", "MISSING", "reporter bond reward and claim accounting projection"),
    ("SEALED_AUCTION", "MISSING", "matching V1 Rust and proof projection"),
    ("STRATEGY_ESCROW", "MISSING", "V1 accounting projection"),
    (
        "PROOF_REWARDS",
        "EMPTY_ROOT_UNBOUND",
        "global lane root to registered empty-state root binding",
    ),
    (
        "EXTERNAL_CUSTODY",
        "EMPTY_ROOT_UNBOUND",
        "global lane root to registered disabled empty-state root binding",
    ),
    ("GOVERNANCE_MIGRATION", "MISSING", "lane-specific accounting projection and receipt"),
)

SIDECAR_TYPE_NAME_V1: Final = "GlobalAccountingAllocationCertificateV1"
SIDECAR_FIELDS_V1: Final[tuple[str, ...]] = (
    "global_state_root",
    "profile_root",
    "writer_epoch",
    "chain_context",
    "ordered_lane_fragments",
    "canonical_allocation_rows",
    "field_ownership_root",
    "terminal_binding_root",
    "allocation_root",
)
SIDECAR_CHECKS_V1: Final[tuple[str, ...]] = (
    "exact_twelve_lane_order",
    "enabled_lane_supported_receipt_backed_producer",
    "receipt_witness_slots_bind_fragment_and_header",
    "disabled_lane_registered_empty_state_root",
    "every_controlled_source_atom_assigned_exactly_once",
    "claimant_entitlement_rows_equal_v1_liabilities",
    "unencumbered_reserve_rows_equal_v1_reserve_partition",
    "external_obligations_bind_asset_amount_destination_and_commitment",
    "terminal_rows_bind_claimant_asset_amount_control_domain_principal_lane_and_state_root",
    "lane_aggregates_equal_global_economic_tables",
    "checked_u128_arithmetic_and_canonical_order",
)
SIDECAR_VERIFIER_AUTHORITY_REQUIRES_V1: Final[tuple[str, ...]] = (
    "all_twelve_lane_fragment_producers",
    "lane_receipt_binding",
    "route_and_epoch_proof_propagation",
    "versioned_journal_admission",
    "commit_port_enforcement",
)
NORMATIVE_PARTITION_V1: Final = (
    "controlled_atoms = claimant_entitlements + named_unencumbered_reserves"
    " + pending_registered_external_obligations"
)
RESERVE_INTERPRETATION_V1: Final = "NAMED_UNENCUMBERED_NO_CLAIMANT"
VOCABULARY_V1: Final[tuple[str, ...]] = (
    "control_domain",
    "controlled_location",
    "controlling_principal",
    "claimant_entitlement",
    "unencumbered_reserve",
    "pending_external_obligation",
)
REQUIRED_SIDECAR_V1: Final[dict[str, object]] = {
    "type_name": SIDECAR_TYPE_NAME_V1,
    "preserves_global_state_v1_wire_bytes": True,
    "vocabulary": list(VOCABULARY_V1),
    "normative_partition": NORMATIVE_PARTITION_V1,
    "reserve_interpretation": RESERVE_INTERPRETATION_V1,
    "required_fields": list(SIDECAR_FIELDS_V1),
    "required_checks": list(SIDECAR_CHECKS_V1),
    "host_only_authority": "EVIDENCE_ONLY",
    "verifier_authority_requires": list(SIDECAR_VERIFIER_AUTHORITY_REQUIRES_V1),
}
# C4a: the sidecar checker exists in Python and Rust; the packet binds its check order, closed
# reject codes, producer registry (no receipt-backed lane), and the shared golden fixture, so the
# implementation claim below is a projection of pinned sources and never a free-text status.
CERTIFICATE_SCHEMA_V1: Final = "zenodex/global-accounting-allocation-certificate/v1"
CERTIFICATE_FIXTURE_SCHEMA_V1: Final = "zenodex/global-accounting-allocation-certificate-v1-golden/v2"
CERTIFICATE_CHECK_ORDER_V1: Final[tuple[str, ...]] = ("header_binding", *SIDECAR_CHECKS_V1, "derived_roots")
LANE_PRODUCER_REJECT_CODES_V1: Final[tuple[str, ...]] = (
    "LANE_NOT_REGISTERED_EMPTY",
    "LANE_ENABLED",
    "REGISTERED_EMPTY_ROOT_DRIFT",
)
RECEIPT_BACKED_PRODUCER_REJECT_CODES_V1: Final[tuple[str, ...]] = (
    "ACCEPTED_INVALID",
    "JOURNAL_LANE_DRIFT",
    "LANE_DISABLED",
    "MODULE_RELEASE_DRIFT",
    "JOURNAL_ROOT_DRIFT",
    "STALE_JOURNAL",
    "TERMINAL_ROOT_NOT_EMPTY",
    "ENTITLEMENT_ROWS_NOT_CANONICAL",
    "CONTROLLED_FOLD_OVERFLOW",
    "ENTITLEMENT_COVERAGE_DRIFT",
    "FRAGMENT_INVALID",
)  # ACCEPTED_INVALID and FRAGMENT_INVALID are defensive in Python (construction validates);
#   both are genuinely reachable in Rust, whose plain structs carry no construction-time checks.

CERTIFICATE_REJECT_CODES_V1: Final[tuple[str, ...]] = (
    "HEADER_BINDING_DRIFT",
    "LANE_ORDER_DRIFT",
    "LANE_STATE_ROOT_DRIFT",
    "PRODUCER_KIND_DRIFT",
    "BLOCKED_LANE_PRODUCER_MISSING",
    "RECEIPT_WITNESS_REQUIRED",
    "RECEIPT_WITNESS_UNEXPECTED",
    "RECEIPT_WITNESS_FRAGMENT_DRIFT",
    "RECEIPT_WITNESS_HEADER_DRIFT",
    "DISABLED_LANE_NOT_EMPTY",
    "REGISTERED_EMPTY_ROOT_DRIFT",
    "BINDING_ROOT_DRIFT",
    "ALLOCATION_TOTAL_OVERFLOW",
    "SOURCE_ATOM_NOT_ASSIGNED_EXACTLY_ONCE",
    "ENTITLEMENT_ROWS_DRIFT",
    "RESERVE_ROWS_DRIFT",
    "EXTERNAL_OBLIGATION_BINDING_DRIFT",
    "TERMINAL_BINDING_DRIFT",
    "LANE_AGGREGATE_DRIFT",
    "DERIVED_ROOT_DRIFT",
)
CERTIFICATE_REJECT_CODE_CLASS_V1: Final = "AllocationCertificateRejectCodeV1"
CERTIFICATE_PRODUCER_KINDS_V1: Final[dict[str, str]] = {
    lane: {
        "ASSET_TRANSFER": "RECEIPT_BACKED",
        "EXTERNAL_CUSTODY": "REGISTERED_EMPTY_DISABLED",
        "PROOF_REWARDS": "REGISTERED_EMPTY_BLOCKED",
    }.get(lane, "NO_PRODUCER")
    for lane in EXPECTED_LANES_V1
}
CERTIFICATE_FIXTURE_ACCEPTED_V1: Final = 3
# C5 (wave A): the unique empty typed lane state roots the registered-empty lanes are bound to;
# every accepted fixture fragment of these lanes must sit at exactly this root.
CERTIFICATE_REGISTERED_EMPTY_ROOTS_V1: Final[dict[str, str]] = {
    "EXTERNAL_CUSTODY": "0x760d222dd2e3dde6b65195d6f9a20b6d855a51743a194d9766481b042ae8d51d",
    "PROOF_REWARDS": "0xd322bac2dd8f9fa0a67c4036b87f41ba7dc9f1d849dada1cc65e5463c67fdf74",
}
CERTIFICATE_FRAGMENT_ROW_FIELDS_V1: Final[tuple[str, ...]] = (
    "controlled_locations", "claimant_entitlements", "unencumbered_reserves", "pending_external_obligations", "terminal_bindings"
)
CERTIFICATE_IMPLEMENTATION_STATUS_V1: Final = "IMPLEMENTED_REGISTERED_EMPTY_ONLY_NOT_MOUNTED"

NONCLAIMS_V1: Final[tuple[str, ...]] = (
    "The completed formal cycle does not complete O-008.",
    "Receipt admission for the ASSET_TRANSFER fragment (C9a) proves the custody rows the"
    " producer folds, not claimant identity: the wave-B coverage fold is keyed on"
    " (asset, control_domain), claimant entitlements are caller-chosen at that layer, and"
    " they are bound only at the certificate layer by ENTITLEMENT_ROWS_DRIFT against the V1"
    " liabilities partition, into which this producer's rows enter through the witness slot since"
    " C9b-2b; whether that partition is authoritative for asset-transfer custody is an"
    " unresolved policy question.",
    "Exact-type gating is audited and mechanically pinned only on the receipt-admission"
    " path; the epoch-certificate verification inputs in global_economic_proof_v1 still"
    " use isinstance and are a named open gap (O-008 EXACT-TYPE-AUDIT-EPOCH-PATH) for a"
    " separate candidate.",
    "The GlobalAccountingAllocationCertificateV1 checker registers exactly one receipt-backed lane"
    " producer (ASSET_TRANSFER, admitted only as the sealed C9 witness) and is not mounted; the"
    " other eleven lanes must be disabled and empty, so it reconciles at most the asset-transfer"
    " lane and no exact all-twelve-lane reconciliation exists.",
    "The allocation certificate is DERIVED from the verified state by the C9c projection, which"
    " refuses with a closed code wherever V1 state does not determine a certificate the checker can"
    " accept. THREE kinds of refusal share that family and the packet does not enumerate them: the"
    " THV1 projection packet carries the current list, and the module's own reject enum is the"
    " contract. CALLER INPUT means the supplied binding roots or witness slots do not match the"
    " enabled receipt-backed lanes. UNDETERMINED means more than one certificate that passes every"
    " row, partition and aggregate check exists (a domainless terminal with two entitlement domains,"
    " two principals controlling a cell, several ways to split a residual across pending obligations)"
    " -- NOT more than one ACCEPTED certificate: under the current registry no accepted certificate"
    " can carry an external, reserve or terminal row at all, so every state reaching one of those"
    " codes is also one no accepted certificate exists for, and the distinction is about what the"
    " STATE determines rather than about what the checker would take (opus2 P40 P1-1, restated in"
    " this artifact after C9c-4 corrected it everywhere except here -- Opus P41 P1)."
    " UNRECONCILABLE means none exists (entitlements exceeding custody,"
    " unassignable controlled atoms, an obligation with no controlled location, an over-claiming"
    " terminal, a claimant with no entitlement, a fold that would overflow, rows with no enabled lane,"
    " more than one enabled lane, an enabled lane whose registry entry has no producer, and a"
    " registered-empty lane committed at a foreign root -- the last two being lane-configuration facts"
    " that no arrangement of rows can repair, refused before the rows are read and, among themselves,"
    " in the checker's order -- though not necessarily before every other code the checker could raise:"
    " the receipt-witness check runs between them (Opus P41 P2-6)). The sealed witness contributes its binding root and its header,"
    " not its rows. The projection has no consumer: no publisher, verifier, or client calls it, so it"
    " refuses nothing at runtime, and it verifies no receipt.",
    "The ESSO model does not refine current Python, Rust, RISC0, Tau, verifier, or publisher"
    " execution.",
    "The Rust receipt-admission twin mirrors the Python check order and reject family but not the"
    " type boundary: Python raises at its snapshot on malformed, non-canonical, or zero-amount inputs,"
    " the twin returns an AbiErrorV1 for malformed inputs and the producer's ENTITLEMENT_ROWS_NOT_CANONICAL"
    " for the rest; only WITNESS_JOURNAL_ROOT_DRIFT is reachable through a minted Rust witness, and the"
    " parity vectors cover well-formed inputs only.",
    "The Lean theorems do not establish cryptographic binding, finite-width runtime parity,"
    " settlement authority, or whole-program value safety.",
    "The ESSO fingerprint is a determinism witness only; the ESSO ir_hash is the model-binding"
    " value and is verified only by proof replay.",
    "A detached host-generated sidecar can be swapped independently of an epoch receipt and"
    " therefore grants evidence-only authority.",
    "The Rust lexical closure pins the crate root module set and five source files; canonical.rs,"
    " release.rs, and the lane modules are compiled unpinned, so the closure binds the V1 record"
    " shapes and their container decode path, not the bound constants or validation helpers"
    " those modules supply.",
    "Recorded proof replay results are packet-author observations; packet admission reports"
    " proof replay as NOT_RUN unless the checker executed the recorded tools.",
    "Without proof replay the author record's python and rust versions and the Lean axioms"
    " probe hash are shape-checked only; fresh replay is what compares them.",
    "The packet binds exactly the test-hygiene packets its hygiene_selection names -- one per"
    " required pin path, the newest whose pin equals the subject blob -- which is currently seven"
    " distinct packets out of the repository's total. A THV1 packet a candidate message names but"
    " the selection does not bind is covered only by the repository-wide sweep"
    " (tools/check_test_hygiene_v1.py), never by this checker (Opus P40 P2-4). The six"
    " ledger-gated packets are named by their replay commands and read by the ledger from the"
    " subject commit, so their bytes are bound by subject_tree rather than by an individual pin,"
    " and two of the six are not in hygiene_selection (opus2 P40 P3-3)."
    " Selected test-hygiene packets are bound by pin only; their evidence families and mutation"
    " tables are validated by tools/check_test_hygiene_v1.py, which this checker does not run.",
    "No production, release, settlement, verifier, migration, publication, or value-moving"
    " authority is granted.",
)
FORBIDDEN_PROMOTION_TOKENS_V1: Final[tuple[str, ...]] = (
    "o-008 is complete",
    "o-008 complete",
    "completes o-008",
    "o-008 closed",
    "o-008 is closed",
    "formal core complete",
    "formal core is complete",
    "formal_core_complete=true",
    "authority granted",
    "authority is granted",
    "release ready",
    "release-ready",
    "production ready",
    "production-ready",
    "value movement safe",
    "value-movement safe",
    "verifier admitted",
    "mounted in production",
)

ESSO_MODEL_ID_V1: Final = "global_claimant_custody_certificate_v1"
ESSO_INVARIANTS_V1: Final[tuple[str, ...]] = (
    "inv_exact_custody_partition_d0",
    "inv_exact_custody_partition_d1",
    "inv_exact_claimant_domain_liabilities",
    "inv_open_terminals_fit_exact_allocations",
    "inv_accept_requires_exact_bound_evidence",
)
ESSO_ACTIONS_V1: Final[tuple[str, ...]] = ("open_claim", "drain_claim", "deposit_reserve")
ESSO_QUERIES_V1: Final[tuple[str, ...]] = (
    "init_implies_inv",
    "inductive_open_claim",
    "inductive_drain_claim",
    "inductive_deposit_reserve",
)
ESSO_NAMED_MUTANTS_V1: Final[tuple[str, ...]] = (
    "accept_without_global_root_binding",
    "cross_domain_custody_substitution",
    "claimant_column_substitution",
    "terminal_domain_erasure",
    "drain_cross_domain_custody_substitution",
    "reserve_masking_open_claim",
)
ESSO_CODE_COMMIT_V1: Final = "7f80c6216be85c827e8d1cc2fa08ee3107a74588"
ESSO_SOLVERS_V1: Final[dict[str, str]] = {"z3": "4.15.4", "cvc5": "1.1.2"}
ESSO_DETERMINISM_TRIALS_V1: Final = 2
ESSO_SOLVER_TIMEOUT_MS_V1: Final = 10000
ESSO_GATE_EXPECTED_PASSED_V1: Final = 20
ESSO_CLAIM_BOUNDARY_V1: Final = (
    "finite one-asset two-control-domain two-claimant model with at most eight atoms per cell"
)
IR_HASH_ROLE_V1: Final = "MODEL_BINDING_REPLAY_VERIFIED"
FINGERPRINT_ROLE_V1: Final = "DETERMINISM_WITNESS_NOT_MODEL_BINDING"

LEAN_NAMESPACE_V1: Final[tuple[str, ...]] = ("Proofs", "GlobalClaimantCustodyRelationV1")
LEAN_TOOLCHAIN_V1: Final = "leanprover/lean4:v4.27.0"
LEAN_IMPORT_LINE_V1: Final = "import Proofs.GlobalClaimantCustodyRelationV1"
ALLOWED_LEAN_AXIOMS_V1: Final[frozenset[str]] = frozenset(
    {"propext", "Quot.sound", "Classical.choice"}
)
LEAN_NO_RECOVERY_THEOREM_V1: Final = "terminalProjection_hasNoUniversalDomainRecovery"
# Theorems whose proofs are `Iff.rfl`/`rfl` and whose docstrings disclose that; reported
# separately so the theorem count never overstates derived content.
LEAN_DEFINITIONAL_THEOREMS_V1: Final[tuple[str, ...]] = (
    "necessaryRelation_independent_of_reserves",
    "exactCurrentProfileCustody_independent_of_reserves",
    "deposit_preserves_reserves",
    "drain_preserves_reserves",
)
LEAN_GATE_EXPECTED_PASSED_V1: Final = 6
LEAN_CLAIM_BOUNDARY_V1: Final = (
    "bounded cardinality relation over natural-number atoms; no canonical bytes, cryptographic"
    " roots, runtime refinement, verifier admission, or authority"
)
# Ordered (kind, name) inventory of the Lean surface at the admitted source commit.
THEOREM_INVENTORY_V1: Final[tuple[tuple[str, str], ...]] = (
    ("theorem", "necessaryRelation_independent_of_reserves"),
    ("theorem", "exactCurrentProfileCustody_independent_of_reserves"),
    ("theorem", "exactAllocation_implies_necessaryRelation"),
    ("theorem", "exactAllocation_noUnclassified_implies_exactCurrentProfileRelation"),
    ("theorem", "necessaryRelation_nonvacuous"),
    ("theorem", "exactCurrentProfileRelation_nonvacuous"),
    ("theorem", "overCollateralised_isBacked_notExact"),
    ("theorem", "noUnclassified_premise_is_necessary"),
    ("theorem", "deposit_preserves_reserves"),
    ("theorem", "deposit_preserves_necessaryRelation"),
    ("theorem", "deposit_preserves_exactCurrentProfileCustody"),
    ("theorem", "deposit_preserves_exactCurrentProfileRelation"),
    ("theorem", "drain_preserves_reserves"),
    ("theorem", "drain_preserves_necessaryRelation"),
    ("theorem", "drain_preserves_exactCurrentProfileCustody"),
    ("theorem", "drain_preserves_exactCurrentProfileRelation"),
    ("theorem", "sameDomainBacked_implies_aggregateBacked"),
    ("theorem", "aggregateOnly_permits_crossDomainBacking"),
    ("theorem", "openTerminalCovered_implies_aggregateCovered"),
    ("theorem", "aggregateClaimants_permit_claimantSwap"),
    ("theorem", "sameDomainBacked_implies_reserveInclusiveBacking"),
    ("theorem", "reserveInclusiveBacking_permits_missingExactCustody"),
    ("theorem", "terminalProjection_domainErasure_witness"),
    ("theorem", "terminalProjection_domainErasure_notInjective"),
    ("theorem", "terminalProjection_hasNoUniversalDomainRecovery"),
)
# Codex C1'' P1 (Lean): every theorem statement and the definitional surface (imports,
# definitions, structures, inductives, and theorem statements with proofs elided) are bound
# to these checker-embedded hashes, so a weakened statement or definition is rejected on a
# fresh projection and not only through a stale packet pin. Changing them is a reviewed edit
# of this source: the same trust anchor as the ESSO and gate expectations above.
LEAN_STATEMENT_SHA256_V1: Final[dict[str, str]] = {
    "necessaryRelation_independent_of_reserves": "e353f66c7d72092eb08df43d0dabd09836c6832f9ea98e0432d78c4e38139523",
    "exactCurrentProfileCustody_independent_of_reserves": "7591bacd2ea767fd05428f9c3276c51740352fc6f4fb8914a21d0b15d3200c52",
    "exactAllocation_implies_necessaryRelation": "b25759f3c2bda2ebdc2c5f313159c000cb5fa2dd4ca8dca8fa9f790615a94f11",
    "exactAllocation_noUnclassified_implies_exactCurrentProfileRelation": "b3eb1c08b6e0b3de461d8df997dd3735d4c8d482bc27ced792b2b71c57cd1867",
    "necessaryRelation_nonvacuous": "130cb012bcd48c3e91598bebaf65cd49ae1e3dc9dcec021d074ffb1dc5039507",
    "exactCurrentProfileRelation_nonvacuous": "ffd61e800278e6e4e911ef712939708490f39a1c7c994943ba0ba7976e277f50",
    "overCollateralised_isBacked_notExact": "e1a77bbea31982f16bef1f804d8cdb7a3f8324e9bcd5a84f7e4e0bb42c8b629d",
    "noUnclassified_premise_is_necessary": "9079528f9f9ed075fe76de725096ffb7ba5c569afba6368d8aa29b2822195ab3",
    "deposit_preserves_reserves": "fb7c093e458851c06f3fd9a40eba22977730263ef9dde44c2a1154d6fe232c2f",
    "deposit_preserves_necessaryRelation": "229ac22c3d6d74b940aa1913e47e5742813e5a36bf1fe5a9f57c05b61bf12985",
    "deposit_preserves_exactCurrentProfileCustody": "7e61c69ce123ee761ce49819186fcef84e80e4936fcf0bbf87ee92860cf0c30f",
    "deposit_preserves_exactCurrentProfileRelation": "c3ebf645d376bfa55d54aeaa9834df3a30173dc5bb73753e60c20cc8fa7d4099",
    "drain_preserves_reserves": "eae866e57966055327bbacc05f30e19d3f504f6412a0130e5f2443af8a6c999b",
    "drain_preserves_necessaryRelation": "e702b06771af864e14e73c29a567a806348f55fd852fefe66b41373c465c062b",
    "drain_preserves_exactCurrentProfileCustody": "4d0d952e2684f101d96c74e6a9c19d28e783ab4a67f968e89b4513e5c6b0c87b",
    "drain_preserves_exactCurrentProfileRelation": "2b7bc6ae5adb703b9c470010daecb464ef367b13891421d6503a1a1aa5e08e21",
    "sameDomainBacked_implies_aggregateBacked": "b3a9be908f486b5347e2778c0d57f0179077056744eb759c55bc3112d0d4a7f2",
    "aggregateOnly_permits_crossDomainBacking": "f6aeb6674338ed0cab9a8cb47fcf3870bb802f401127585a9690ae68fa0c14ee",
    "openTerminalCovered_implies_aggregateCovered": "9de8fadefd79f161eda313f64cde7850e3d3e1dfb38ee55c667172d5504e4d41",
    "aggregateClaimants_permit_claimantSwap": "f55bf9bfc85faff6c03675727156adcb6ade46ec03efe20847f010a676daa749",
    "sameDomainBacked_implies_reserveInclusiveBacking": "03395e46bb66afe7b7762a01ca935c399df94ef74a7c3f5bf45aeaa3c31d480f",
    "reserveInclusiveBacking_permits_missingExactCustody": "1ddaa7ac63765ab070dd1e4f6e96a9f6a957355f956fc30afcc41a2483005d8b",
    "terminalProjection_domainErasure_witness": "f80afe52522e867e7e7d07a4caa0dc3545554b736eb21c9527301e06890bbdda",
    "terminalProjection_domainErasure_notInjective": "d1818fef44d68661b13ff4d2f00449738222e0b2a510e1c2f76c7dbd0ef5a665",
    "terminalProjection_hasNoUniversalDomainRecovery": "80771422f6b46b12f8ec08578e3d56be8ef8226ba3c7f57a49ef4ccb69612241",
}
LEAN_DEFINITION_SURFACE_SHA256_V1: Final = "cd1e010a3f82e1595c4cefa7fc7354bc8d972e77c669ed026d177bb8cf275b11"
LEAN_STATEMENT_BINDING_V1: Final = (
    "theorem statements and the definitional surface are compared against hashes embedded in the"
    " admission core at S (the definition-surface hash carries the binding; the lexical closures are"
    " defence in depth): the file contains no double quote or guillemet and no # character anywhere"
    " in its stripped code, and may use no notation, macro, syntax, instance, attribute, scope, open,"
    " run_cmd, or run_elab command; each elided region is indented, #-free, forbidden-word-free proof"
    " text with no declaration"
)
LEAN_GATE_PIN_ORDER_V1: Final[tuple[str, ...]] = (
    LEAN_PROOF_PATH_V1,
    ESSO_MODEL_PATH_V1,
    PYTHON_TYPES_PATH_V1,
    PYTHON_REFINEMENT_PATH_V1,
    RUST_STATE_PATH_V1,
    RUST_REFINEMENT_PATH_V1,
)


@dataclass(frozen=True, slots=True)
class LeanSubjectV1:
    """One pinned Lean file with its closed theorem inventory, hashes, gate, and replay commands."""

    key: str
    path: str
    gate_path: str
    namespace: tuple[str, ...]
    import_line: str
    inventory: tuple[tuple[str, str], ...]
    statement_sha256: Mapping[str, str]
    definition_surface_sha256: str
    definitional_theorems: tuple[str, ...]
    witness_theorems: tuple[str, ...]
    gate_pin_order: tuple[str, ...]
    gate_expected_passed: int
    direct_check_command: str
    axioms_probe_command: str
    binding_gate_command: str
    probe_token: str
    claim_boundary: str


O008_LEAN_SUBJECT_V1: Final = LeanSubjectV1(
    key="o008_relation",
    path=LEAN_PROOF_PATH_V1,
    gate_path=LEAN_GATE_PATH_V1,
    namespace=LEAN_NAMESPACE_V1,
    import_line=LEAN_IMPORT_LINE_V1,
    inventory=THEOREM_INVENTORY_V1,
    statement_sha256=LEAN_STATEMENT_SHA256_V1,
    definition_surface_sha256=LEAN_DEFINITION_SURFACE_SHA256_V1,
    definitional_theorems=LEAN_DEFINITIONAL_THEOREMS_V1,
    witness_theorems=(),
    gate_pin_order=LEAN_GATE_PIN_ORDER_V1,
    gate_expected_passed=LEAN_GATE_EXPECTED_PASSED_V1,
    direct_check_command="lean_direct_check",
    axioms_probe_command="lean_axioms_probe",
    binding_gate_command="lean_binding_gate",
    probe_token="<PROBE>",
    claim_boundary=LEAN_CLAIM_BOUNDARY_V1,
)
# C4b: the bounded Lean model of the sidecar checker (three lanes, two domains, two claimants).
CERTIFICATE_LEAN_NAMESPACE_V1: Final[tuple[str, ...]] = ("Proofs", "GlobalAccountingAllocationCertificateV1")
CERTIFICATE_THEOREM_INVENTORY_V1: Final[tuple[tuple[str, str], ...]] = (
    ("theorem", "certificate_implies_normativePartition"),
    ("theorem", "certificate_implies_sameDomainBacked"),
    ("theorem", "certificate_implies_terminalCovered"),
    ("theorem", "certificate_noReserve_noExternal_implies_exactCustody"),
    ("theorem", "noReceiptBacked_forces_allDisabled"),
    ("theorem", "noReceiptBacked_implies_zeroTables"),
    ("theorem", "emptyFragment_checks"),
    ("theorem", "registeredEmpty_nonvacuous"),
    ("theorem", "hotFragment_checks"),
    ("theorem", "mixed_nonvacuous"),
    ("theorem", "unassignedAtom_fails_partition"),
    ("theorem", "reserve_cannot_cover_claimant"),
    ("theorem", "enabledWithoutProducer_fails_gate"),
    ("theorem", "terminalOverEntitlement_fails_bound"),
    ("theorem", "unassigned_satisfies_all_but_partition"),
    ("theorem", "lanePartition_premise_is_necessary"),
)
CERTIFICATE_LEAN_STATEMENT_SHA256_V1: Final[dict[str, str]] = {
    "certificate_implies_normativePartition": "5ba5fb86ca4b70adf4cb6a5149e7723edc9a84f46434185f2be17b6f9b09dcf8",
    "certificate_implies_sameDomainBacked": "ded5bf794ae12e43a5977a77b83006015d8689945a49809c378b39f53238c65c",
    "certificate_implies_terminalCovered": "8f106d99dbe0bb09e5826771ecd98c6bbf5da4118cdabdbbbb8f429ab9292f43",
    "certificate_noReserve_noExternal_implies_exactCustody": "ce408ce94cf2073ee3175691606ea7ae551bab31c6314f1a9c4575678b4ecd64",
    "noReceiptBacked_forces_allDisabled": "650c888acaa5c61dd607699242600460a7309ab034eb4194fbaf0e695c86d561",
    "noReceiptBacked_implies_zeroTables": "b39614b10d1ec1a7afbb2dd15d2a132e19d051a48f80103fbaa5883479c32260",
    "emptyFragment_checks": "81d0f8aa350a3c40afe15344903067eab2a19d6979c1a21322018b651024ebd0",
    "registeredEmpty_nonvacuous": "e82db9489c2ed07b76267116cdcb8b20ca0e66f76af25882c75c88d2ea3f930c",
    "hotFragment_checks": "aec77ed1f4e5275ad4b424112282b76808ba192eb33032da6f9be2f9c816384d",
    "mixed_nonvacuous": "eeea239d5994cdec43bf5507f9bdd4fd2f09a243935fac4a41ac909c22156d86",
    "unassignedAtom_fails_partition": "03dfb47aa37799ee3f4ae459395f285bc603e726e099ee2d2e69f9c78a4a27ee",
    "reserve_cannot_cover_claimant": "a8465022ffd914ce1565b370f8fa1783f1fc1519926bc07f5fbe29c1b3fe06e2",
    "enabledWithoutProducer_fails_gate": "68c32b1ace4b90a554a1313a0517249b973f3c877eb7bdc1f9d877354ed40024",
    "terminalOverEntitlement_fails_bound": "7e48af7d2c803fcd261a89ed30a561f575daba000b793feeb81762a8ea9051ac",
    "unassigned_satisfies_all_but_partition": "d4cb243ec4cdb97768481092283272d22139c5935c53eebdc78122ef18a7f5e0",
    "lanePartition_premise_is_necessary": "022af98e186dc3a2ce1cb66e32dd8d35b15d78b17cb2f43d38d8f71b4d1805f5",
}
CERTIFICATE_LEAN_DEFINITION_SURFACE_SHA256_V1: Final = "db6e720f8cca8d62525889c6e529e383a1e2f42297c982b422728d70e0e6594d"
# Decidable evaluations on closed witnesses and refutations; reported apart from the derived theorems.
CERTIFICATE_LEAN_WITNESS_THEOREMS_V1: Final[tuple[str, ...]] = (
    "emptyFragment_checks",
    "registeredEmpty_nonvacuous",
    "hotFragment_checks",
    "mixed_nonvacuous",
    "unassignedAtom_fails_partition",
    "reserve_cannot_cover_claimant",
    "enabledWithoutProducer_fails_gate",
    "terminalOverEntitlement_fails_bound",
    "unassigned_satisfies_all_but_partition",
)
CERTIFICATE_LEAN_GATE_EXPECTED_PASSED_V1: Final = 6
CERTIFICATE_LEAN_GATE_PIN_ORDER_V1: Final[tuple[str, ...]] = (
    CERTIFICATE_LEAN_PATH_V1,
    CERTIFICATE_PYTHON_PATH_V1,
    CERTIFICATE_RUST_PATH_V1,
    CERTIFICATE_FIXTURE_PATH_V1,
)
CERTIFICATE_LEAN_SUBJECT_V1: Final = LeanSubjectV1(
    key="allocation_certificate_model",
    path=CERTIFICATE_LEAN_PATH_V1,
    gate_path=CERTIFICATE_LEAN_GATE_PATH_V1,
    namespace=CERTIFICATE_LEAN_NAMESPACE_V1,
    import_line="import Proofs.GlobalAccountingAllocationCertificateV1",
    inventory=CERTIFICATE_THEOREM_INVENTORY_V1,
    statement_sha256=CERTIFICATE_LEAN_STATEMENT_SHA256_V1,
    definition_surface_sha256=CERTIFICATE_LEAN_DEFINITION_SURFACE_SHA256_V1,
    definitional_theorems=(),
    witness_theorems=CERTIFICATE_LEAN_WITNESS_THEOREMS_V1,
    gate_pin_order=CERTIFICATE_LEAN_GATE_PIN_ORDER_V1,
    gate_expected_passed=CERTIFICATE_LEAN_GATE_EXPECTED_PASSED_V1,
    direct_check_command="lean_certificate_direct_check",
    axioms_probe_command="lean_certificate_axioms_probe",
    binding_gate_command="lean_certificate_binding_gate",
    probe_token="<CERTIFICATE_PROBE>",
    claim_boundary=(
        "bounded three-lane, two-domain, two-claimant model over natural numbers; no finite-width"
        " arithmetic, canonical bytes, roots, runtime refinement, verifier admission, or authority"
    ),
)
LEAN_SUBJECTS_V1: Final[tuple[LeanSubjectV1, ...]] = (O008_LEAN_SUBJECT_V1, CERTIFICATE_LEAN_SUBJECT_V1)


@dataclass(frozen=True, slots=True)
class EssoSubjectV1:
    """One pinned ESSO-IR model with its closed surface, replay gate, and replay commands."""

    key: str
    model_path: str
    gate_path: str
    model_id: str
    invariants: tuple[str, ...]
    actions: tuple[str, ...]
    queries: tuple[str, ...]
    named_mutants: tuple[str, ...]
    gate_expected_passed: int
    validate_command: str
    verify_command: str
    gate_command: str
    evidence_key: str
    claim_boundary: str


O008_ESSO_SUBJECT_V1: Final = EssoSubjectV1(
    key="o008_relation",
    model_path=ESSO_MODEL_PATH_V1,
    gate_path=ESSO_GATE_PATH_V1,
    model_id=ESSO_MODEL_ID_V1,
    invariants=ESSO_INVARIANTS_V1,
    actions=ESSO_ACTIONS_V1,
    queries=ESSO_QUERIES_V1,
    named_mutants=ESSO_NAMED_MUTANTS_V1,
    gate_expected_passed=ESSO_GATE_EXPECTED_PASSED_V1,
    validate_command="esso_validate",
    verify_command="esso_verify_multi",
    gate_command="esso_gate",
    evidence_key="",
    claim_boundary=ESSO_CLAIM_BOUNDARY_V1,
)
# C4c: the bounded ESSO model of the sidecar checker (two lanes, one domain, two claimants).
CERTIFICATE_ESSO_MODEL_ID_V1: Final = "global_accounting_allocation_certificate_v1"
CERTIFICATE_ESSO_INVARIANTS_V1: Final[tuple[str, ...]] = (
    "inv_lane_partition_exact",
    "inv_lane_rows_equal_tables",
    "inv_lane_aggregate_equals_custody",
    "inv_terminal_bound_by_entitlement",
    "inv_producer_gate",
    "inv_accept_requires_lane_binding",
    "inv_normative_partition",
    "inv_same_domain_backed",
)
CERTIFICATE_ESSO_ACTIONS_V1: Final[tuple[str, ...]] = (
    "enable_lane",
    "open_entitlement",
    "deposit_reserve",
    "register_external",
    "open_terminal",
    "drain_terminal",
    "disable_lane",
)
CERTIFICATE_ESSO_QUERIES_V1: Final[tuple[str, ...]] = (
    "init_implies_inv",
    "inductive_enable_lane",
    "inductive_open_entitlement",
    "inductive_deposit_reserve",
    "inductive_register_external",
    "inductive_open_terminal",
    "inductive_drain_terminal",
    "inductive_disable_lane",
)
CERTIFICATE_ESSO_NAMED_MUTANTS_V1: Final[tuple[str, ...]] = (
    "reserve_masks_entitlement",
    "unassigned_atom",
    "enable_without_receipt",
    "terminal_over_entitlement",
    "custody_double_count",
    "disable_with_rows",
    "external_table_not_summed",
    "accept_without_lane_binding",
)
CERTIFICATE_ESSO_GATE_EXPECTED_PASSED_V1: Final = 24
CERTIFICATE_ESSO_SUBJECT_V1: Final = EssoSubjectV1(
    key="allocation_certificate_model",
    model_path=CERTIFICATE_ESSO_MODEL_PATH_V1,
    gate_path=CERTIFICATE_ESSO_GATE_PATH_V1,
    model_id=CERTIFICATE_ESSO_MODEL_ID_V1,
    invariants=CERTIFICATE_ESSO_INVARIANTS_V1,
    actions=CERTIFICATE_ESSO_ACTIONS_V1,
    queries=CERTIFICATE_ESSO_QUERIES_V1,
    named_mutants=CERTIFICATE_ESSO_NAMED_MUTANTS_V1,
    gate_expected_passed=CERTIFICATE_ESSO_GATE_EXPECTED_PASSED_V1,
    validate_command="esso_certificate_validate",
    verify_command="esso_certificate_verify_multi",
    gate_command="esso_certificate_gate",
    evidence_key="certificate_model",
    claim_boundary=(
        "bounded two-lane, one-domain, two-claimant inductive contract of the sidecar checker; no"
        " finite-width arithmetic, canonical bytes, roots, runtime refinement, receipt validity,"
        " mounting, or authority; no lane producer is REGISTERED receipt-backed and none is on an"
        " acceptance path (an implemented, unregistered wave-B producer exists)"
    ),
)
ESSO_SUBJECTS_V1: Final[tuple[EssoSubjectV1, ...]] = (O008_ESSO_SUBJECT_V1, CERTIFICATE_ESSO_SUBJECT_V1)

TERMINAL_CLASS_NAME_V1: Final = "TerminalObligationV1"
OUTBOX_CLASS_NAME_V1: Final = "OutboxStateV1"
TERMINAL_FIELDS_PYTHON_V1: Final[tuple[tuple[str, str], ...]] = (
    ("obligation_id", "str"),
    ("lane_id", "LaneIdV1"),
    ("claimant", "str"),
    ("asset", "str"),
    ("amount_atoms", "int"),
    ("status", "TerminalObligationStatusV1"),
)
TERMINAL_FIELDS_RUST_V1: Final[tuple[tuple[str, str], ...]] = (
    ("obligation_id", "String"),
    ("lane_id", "LaneIdV1"),
    ("claimant", "String"),
    ("asset", "String"),
    ("amount_atoms", "u128"),
    ("status", "TerminalObligationStatusV1"),
)
OUTBOX_FIELDS_PYTHON_V1: Final[tuple[tuple[str, str], ...]] = (
    ("effect_id", "str"),
    ("destination_id", "str"),
    ("payload_hash", "str"),
    ("commit_id", "str"),
    ("status", "OutboxStatusV1"),
)
OUTBOX_FIELDS_RUST_V1: Final[tuple[tuple[str, str], ...]] = (
    ("effect_id", "RootV1"),
    ("destination_id", "String"),
    ("payload_hash", "RootV1"),
    ("commit_id", "RootV1"),
    ("status", "OutboxStatusV1"),
)
TERMINAL_FORBIDDEN_FIELDS_V1: Final[tuple[str, ...]] = (
    "liability_domain",
    "control_domain",
    "custody_domain",
    "custody_principal",
    "controlling_principal",
    "source_principal",
)
OUTBOX_FORBIDDEN_FIELDS_V1: Final[tuple[str, ...]] = ("asset", "amount_atoms")
TERMINAL_ABSENT_FIELDS_V1: Final[tuple[str, ...]] = ("liability_domain", "custody_principal")
STATE_CLASS_NAME_V1: Final = "GlobalEconomicStateV1"
CONTAINER_DESERIALIZERS_V1: Final[dict[str, str]] = {
    "terminal_obligations": "deserialize_terminal_obligations_v1",
    "outbox": "deserialize_outbox_v1",
}
BOUNDED_VEC_MACRO_NAME_V1: Final = "bounded_state_vec_deserializer_v1"
# Whitespace-normalised body of the local macro that produces every container deserialiser.
BOUNDED_VEC_MACRO_BODY_V1: Final = "($function:ident, $row:ty, $maximum:expr, $label:literal) => { fn $function<'de, D>(deserializer: D) -> Result<Vec<$row>, D::Error> where D: Deserializer<'de>, { deserialize_bounded_vec_v1::<D, $row, $maximum>(deserializer, $label) } };"
# Whitespace-normalised library portion of bounded_vec.rs (the cfg(test) module excluded):
# the only decoding path for a container is this visitor, which decodes every element
# through `T: Deserialize` (the record's derive) and nothing else.
BOUNDED_VEC_LIBRARY_TEMPLATE_V1: Final = "use std::{fmt, marker::PhantomData}; use serde::de::{Error, IgnoredAny, SeqAccess, Visitor}; use serde::{Deserialize, Deserializer}; pub(crate) fn deserialize_bounded_vec_v1<'de, D, T, const MAXIMUM: usize>( deserializer: D, label: &'static str, ) -> Result<Vec<T>, D::Error> where D: Deserializer<'de>, T: Deserialize<'de>, { deserializer.deserialize_seq(BoundedVecVisitorV1::<T, MAXIMUM> { label, marker: PhantomData, }) } struct BoundedVecVisitorV1<T, const MAXIMUM: usize> { label: &'static str, marker: PhantomData<T>, } impl<'de, T, const MAXIMUM: usize> Visitor<'de> for BoundedVecVisitorV1<T, MAXIMUM> where T: Deserialize<'de>, { type Value = Vec<T>; fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result { write!(formatter, , self.label) } fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error> where A: SeqAccess<'de>, { if sequence.size_hint().is_some_and(|size| size > MAXIMUM) { return Err(A::Error::custom(format_args!( , self.label ))); } let mut values = Vec::with_capacity(sequence.size_hint().unwrap_or(0).min(MAXIMUM)); while values.len() < MAXIMUM { match sequence.next_element()? { Some(value) => values.push(value), None => return Ok(values), } } if sequence.next_element::<IgnoredAny>()?.is_some() { return Err(A::Error::custom(format_args!( , self.label ))); } Ok(values) } }"
# Closed content of the two compiled/imported projection gates (Rust: exact sha256 of the
# committed bytes; Python: ast.dump of the module)
# plus the named tests and tables, so a gate cannot keep its names and lose its assertions.
# Whole-file pins are exact sha256 of the committed bytes (Opus P10 P1-B2: whitespace
# normalisation let a `//` comment absorb the following code line without moving the hash).
# The scanned constructs are belt-and-braces once each file is a reviewed constant.
RUST_STATE_FILE_SHA256_V1: Final = "44f6874589e72c7fefdcac8b6c220fb311c6dc0f1e53bb3b962e32a6d593b98c"
RUST_GATE_SHA256_V1: Final = "d807778ab2a7169a7e9e2bb8f8b020a53cb3e106dae74ae37dc9106cf587753f"
# Whole-file pin of bounded_vec.rs (exact bytes, cfg(test) module included), so the unit test
# replayed by rust_bounded_vec_unit_gate is the pinned one (Opus C1''' P3-2).
BOUNDED_VEC_FILE_SHA256_V1: Final = "eb4539f793405c0120c7e95424c51daea6c78b7c5b9584b7bfdbbcf63a0b3be6"
PYTHON_GATE_AST_SHA256_V1: Final = "c84dbf97e4bd3021ec46bb6557b5b71d93e1eebe848959b9278926a05fe1fad6"
# The only file the compiled gate may embed: the pinned golden fixture, by its crate-relative path.
RUST_GATE_INCLUDES_V1: Final[tuple[str, ...]] = ("../../../tests/data/global_claimant_backing_guard_v1_golden.json",)
RUST_GATE_TESTS_V1: Final[tuple[str, ...]] = (
    "terminal_record_serialises_fields_in_declared_order",
    "outbox_record_serialises_fields_in_declared_order",
    "terminal_record_rejects_unknown_fields",
    "outbox_record_rejects_unknown_fields",
    "state_container_rejects_unknown_terminal_field_through_the_compiled_type",
    "state_container_rejects_unknown_outbox_field_through_the_compiled_type",
    "records_and_containers_reject_seeded_unknown_keys",
)
PYTHON_GATE_TESTS_V1: Final[tuple[str, ...]] = (
    "test_terminal_record_runtime_fields_and_canonical_keys_are_exact",
    "test_outbox_record_runtime_fields_and_canonical_keys_are_exact",
    "test_terminal_record_rejects_unknown_fields_at_construction",
    "test_outbox_record_rejects_unknown_fields_at_construction",
    "test_records_are_frozen_slots_classes_defined_in_the_pinned_module",
    "test_records_reject_seeded_unknown_kwargs",
    "test_state_containers_hold_exactly_the_record_types",
)
CONTAINER_RECORD_FIELDS_V1: Final[tuple[tuple[str, str], ...]] = (
    ("terminal_obligations", "TerminalObligationV1"),
    ("outbox", "OutboxStateV1"),
)
INFORMATION_LOSS_BINDING_V1: Final[dict[str, str]] = {
    "static": "LEXICAL_CLOSURE_SCAN_OF_PINNED_BYTES",
    "static_closure": (
        "no cfg, include, or path attributes; no item-defining, nested-invoking, foreign, or"
        " later-defined item macros; single depth-zero definition; exact derive plus"
        " deny_unknown_fields attribute block; no field attributes; use statements scanned with"
        " attributes blanked and expanded through brace groups and aliases; the four serde prelude"
        " names bound only as serde::<name>; the bounded-vec deserialiser bound only from"
        " crate::bounded_vec; the state module imports only serde, crate::canonical, crate::release,"
        " and that deserialiser, unaliased, never a container deserialiser or the macro name, and"
        " never a glob; each record container carries only deserialize_with naming a function"
        " produced by exactly one item-position invocation of the local macro, which is defined"
        " exactly once, may be the only fn-producing macro, and is pinned together with the whole"
        " of state.rs and bounded_vec.rs; the crate root declares exactly the pinned"
        " module set with mod state and mod bounded_vec once each, no inline modules, and no use"
        " binding state, bounded_vec, canonical, release, or serde; manifest and lockfile pinned"
        " with default targets, exact versions, and no cargo config at the subject, HEAD, or"
        " worktree; canonical.rs, release.rs, and the lane modules are compiled but unpinned"
    ),
    "compiled": "REPLAY_GATES_python_projection_gate_AND_rust_projection_gate_NOT_RUN_UNLESS_EXECUTED",
}
OUTBOX_ABSENT_FIELDS_V1: Final[tuple[str, ...]] = ("asset", "amount_atoms")
INFORMATION_LOSS_SCOPE_V1: Final = (
    "NO_UNIVERSAL_RECOVERY_THEOREM_IS_SCOPED_TO_THIS_V1_TERMINAL_PROJECTION"
)
INFORMATION_LOSS_FORMAL_RESULT_V1: Final = "NO_UNIVERSAL_RECOVERY_FROM_V1_TERMINAL_PROJECTION"
OPAQUE_BINDINGS_V1: Final[tuple[str, ...]] = (
    "lane_state_root_to_private_accounting_projection",
    "receipt_root_to_allocation_preimage",
)
ACCEPTED_KNOWN_GAPS_V1: Final[tuple[str, ...]] = (
    "same_lane_root_claimant_projection_substitution",
    "domainless_terminal_with_two_distinct_hidden_domain_preimages",
    "exact_type_audit_epoch_path",
)

ADMISSION_SEMANTICS_V1: Final = (
    "AUTHOR_RECORD_IS_OBSERVATION_ONLY_CHECKER_REPORTS_NOT_RUN_UNLESS_IT_EXECUTES"
)
# Codex C1'' P2: the replay shell rebuilds the tool environment from this policy; nothing
# else from the invoking user's environment (host cargo config, RUSTFLAGS, wrappers, rustup
# overrides, PYTHONPATH) reaches a replayed tool.
REPLAY_ENV_POLICY_V1: Final[dict[str, object]] = {
    "fixed": {"LANG": "C.UTF-8", "LC_ALL": "C.UTF-8", "PYTHONDONTWRITEBYTECODE": "1", "PYTHONHASHSEED": "0", "CARGO_INCREMENTAL": "0", "CARGO_BUILD_JOBS": "8"},
    "sanitized": {
        "HOME": "empty directory under the replay temporary directory",
        "TMPDIR": "empty directory under the replay temporary directory",
        "CARGO_HOME": "replay-local directory holding only a link to the host crate registry and no config file",
        "CARGO_TARGET_DIR": "replay-local target directory",
    },
    "derived": {
        "PATH": "directories of the resolved cargo, rustc, lake, and lean executables followed by /usr/bin:/bin",
        "RUSTUP_HOME": "host rustup home when present (toolchain store only)",
        "ELAN_HOME": "host elan home when present (toolchain store only)",
        "PYTHONPATH": "the ESSO checkout, ESSO commands only",
        "PYTHONUSERBASE": "host user site of the ESSO interpreter (solver bindings), ESSO commands only",
        "ZENO_ESSO_PYTHON": "the ESSO interpreter, ESSO commands only",
    },
    "dropped": "every other variable, including RUSTFLAGS, RUSTC_WRAPPER, RUSTC_WORKSPACE_WRAPPER, CARGO_BUILD_RUSTFLAGS, RUSTUP_TOOLCHAIN, and the host cargo config",
    "bound_by": "rust_compiler_version records rustc -vV (release, commit hash, host) and fresh replay compares it",
}
REPLAY_STATUS_NOT_RUN_V1: Final = "NOT_RUN"
REPLAY_STATUS_EXECUTED_PASS_V1: Final = "EXECUTED_PASS"
REPLAY_STATUS_EXECUTED_FAIL_V1: Final = "EXECUTED_FAIL"
REPLAY_STATUS_REFUSED_V1: Final = "REFUSED"
PYTHON_TOKEN_V1: Final = "<PYTHON>"
PYTHON_GATE_EXPECTED_PASSED_V1: Final = 13
RUST_GATE_EXPECTED_PASSED_V1: Final = 7
RUST_REFINEMENT_GATE_EXPECTED_PASSED_V1: Final = 41
RUST_GOLDEN_GATE_EXPECTED_PASSED_V1: Final = 3
RUST_REFINEMENT_GATE_TARGET_V1: Final = "global_economic_state_effect_refinement"
RUST_GOLDEN_GATE_TARGET_V1: Final = "claimant_backing_guard_golden"
CERTIFICATE_RUST_GATE_TARGET_V1: Final = "global_accounting_allocation_certificate_golden"
CERTIFICATE_RUST_GATE_EXPECTED_PASSED_V1: Final = 4
CERTIFICATE_PYTHON_GATE_EXPECTED_PASSED_V1: Final = 44
PRODUCERS_PYTHON_GATE_EXPECTED_PASSED_V1: Final = 30
PRODUCERS_RUST_GATE_TARGET_V1: Final = "global_accounting_lane_producers"
PRODUCERS_RUST_GATE_EXPECTED_PASSED_V1: Final = 7
# C9b-1: the Rust admission twin is exercised inside the route-binding suite (the only place a
# module witness is minted in Rust); the gate filters that suite by the admission prefix.
ADMISSION_RUST_GATE_TARGET_V1: Final = "lane_module_release_route_binding"
ADMISSION_RUST_GATE_FILTER_V1: Final = "receipt_admission_"
ADMISSION_RUST_GATE_EXPECTED_PASSED_V1: Final = 5
# C9c-1: the certificate derived from the state, and the two shapes V1 state leaves undetermined.
PROJECTION_GATE_EXPECTED_PASSED_V1: Final = 87
CERTIFICATE_RUST_UNIT_FILTER_V1: Final = "global_accounting_allocation_certificate::tests::"
CERTIFICATE_RUST_UNIT_GATE_EXPECTED_PASSED_V1: Final = 5
PYTHON_GOLDEN_GATE_EXPECTED_PASSED_V1: Final = 35
_CARGO_VERSION_RE: Final = re.compile(r"^cargo ([0-9]+\.[0-9]+\.[0-9]+)")
_RUSTC_FIELD_RE: Final = re.compile(r"^(release|commit-hash|host): (\S+)$", re.MULTILINE)
_HOST_TRIPLE_RE: Final = re.compile(r"[A-Za-z0-9_.-]+")
EMPTY_SHA256_V1: Final = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
_SEMVER_RE: Final = re.compile(r"[0-9]+\.[0-9]+\.[0-9]+")
_SHA256_HEX_RE_V1: Final = re.compile(r"[0-9a-f]{64}")


def _portable_repo_path_v1(path: str) -> bool:
    """A repository-relative path with no absolute root, drive, traversal or empty segment."""

    if not path or path.startswith("/") or "\\" in path or ":" in path:
        return False
    segments = path.split("/")
    return all(segment not in ("", ".", "..") for segment in segments)

_CARGO_SUMMARY_RE: Final = re.compile(
    r"^test result: (ok|FAILED)\. (\d+) passed; (\d+) failed;", re.MULTILINE
)
ESSO_PYTHON_TOKEN_V1: Final = "<ZENO_ESSO_PYTHON>"
PRIOR_ESSO_GATE_EXPECTED_PASSED_V1: Final = 136

_HEX40_RE: Final = re.compile(r"[0-9a-f]{40}")
_HEX64_RE: Final = re.compile(r"[0-9a-f]{64}")
_DATE_RE: Final = re.compile(r"[0-9]{4}-[0-9]{2}-[0-9]{2}")
_LEAN_DECL_RE: Final = re.compile(
    r"^[ \t]*(?:@\[[^\]]*\][ \t]*)*"
    r"(?P<mods>(?:(?:private|protected|noncomputable|nonrec)[ \t]+)*)"
    r"(?P<kind>theorem|lemma)[ \t]+(?P<name>[A-Za-z_][A-Za-z0-9_'.!?]*)",
    re.MULTILINE,
)
_LEAN_NAMESPACE_RE: Final = re.compile(r"^[ \t]*(namespace|end)[ \t]+(\S+)[ \t]*$", re.MULTILINE)
# Opus C1'''' P1-2: commands that can rebind what a later statement's tokens mean, add instances,
# or open scopes are forbidden anywhere in the pinned proof file (whole words on comment-stripped
# code; the `open` constructor of TerminalStatus survives because only the command form is banned),
# and an elided proof region may contain only indented text without declarations.
_LEAN_FORBIDDEN_WORDS_V1: Final[frozenset[str]] = frozenset({
    "notation", "macro", "macro_rules", "syntax", "elab", "elab_rules", "declare_syntax_cat", "infix", "infixl",
    "infixr", "prefix", "postfix", "export", "initialize", "builtin_initialize", "set_option", "attribute", "local",
    "scoped", "partial", "unsafe", "opaque", "axiom", "mutual", "omit", "include", "variable", "universe", "section",
    "instance", "class", "abbrev", "example", "simproc", "dsimproc", "register_simp_attr",
    "run_cmd", "run_elab",
})
_LEAN_WORD_RE: Final = re.compile(r"(?<![A-Za-z0-9_.'])([A-Za-z_][A-Za-z0-9_]*)")
_LEAN_OPEN_COMMAND_RE: Final = re.compile(r"^[ \t]*open\b", re.MULTILINE)
_LEAN_INDENTED_DECL_RE: Final = re.compile(
    r"^[ \t]+(?:@\[|def|theorem|lemma|structure|inductive|namespace|end|import)\b", re.MULTILINE
)
_LEAN_COLUMN_ZERO_RE: Final = re.compile(r"^(?![ \t\n|])", re.MULTILINE)
_RUST_FIELD_RE: Final = re.compile(r"^([A-Za-z_][A-Za-z0-9_]*)\s*:\s*(.+?)\s*$", re.DOTALL)
_RUST_MACRO_INVOCATION_RE: Final = re.compile(
    r"\b([A-Za-z_][A-Za-z0-9_]*)!\s*(?:[A-Za-z_][A-Za-z0-9_]*\s*)?([\(\[{])"
)
_RUST_ITEM_KEYWORD_RE: Final = re.compile(r"\b(?:struct|enum|union|trait|impl|type|mod|use|extern)\b")
# `use` statements tokenised from stripped code: anchored on statement boundaries, not lines.
# Statement boundaries are matched with a lookbehind so consecutive statements are all seen:
# a consuming boundary would swallow the `;` the next statement needs.
_RUST_USE_RE: Final = re.compile(r"(?:^|(?<=[;{}\]]))\s*(?:pub(?:\([^)]*\))?\s+)?use\s+([^;]+);", re.MULTILINE)
# Opus C1''' P1-1: an attribute on the same line as a `use` must not hide the statement; the
# scan runs on code with every attribute blanked (length-preserving) so offsets still align.
_RUST_ATTRIBUTE_RE: Final = re.compile(r"#!?\[(?:[^\[\]]|\[[^\[\]]*\])*\]")
_RUST_SERDE_NAMES_V1: Final[frozenset[str]] = frozenset({"Serialize", "Deserialize", "Serializer", "Deserializer"})
_RUST_TEST_FN_RE: Final = re.compile(r"#\[test\]\s*fn\s+([A-Za-z_][A-Za-z0-9_]*)")
_RUST_ATTR_PREFIX_RE: Final = re.compile(
    r"((?:#\[[^\]]*\]\s*)+)(?:pub(?:\([^)]*\))?\s+)?$", re.DOTALL
)
_PYTEST_SUMMARY_RE: Final = re.compile(r"(\d+) passed")
_LEAN_VERSION_RE: Final = re.compile(r"Lean \(version ([0-9.]+)")
_PRINT_AXIOMS_RE: Final = re.compile(
    r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
)


# ---------------------------------------------------------------------------
# Errors and value types
# ---------------------------------------------------------------------------


class AdmissionRejectV1(ValueError):
    """A structured fail-closed finding: closed code, pointer, human detail."""

    def __init__(self, code: str, path: str, detail: str) -> None:
        super().__init__(f"{code} at {path}: {detail}")
        self.code = code
        self.path = path
        self.detail = detail


@dataclass(frozen=True, slots=True)
class AdmissionErrorV1:
    code: str
    path: str
    detail: str

    def to_json(self) -> dict[str, str]:
        return {"code": self.code, "path": self.path, "detail": self.detail}


def _reject(code: str, path: str, detail: str) -> NoReturn:
    raise AdmissionRejectV1(code, path, detail)


@dataclass(frozen=True, slots=True)
class SourceBlobV1:
    path: str
    mode: str
    git_blob: str
    sha256: str
    size: int
    data: bytes


@dataclass(frozen=True, slots=True)
class SubjectSnapshotV1:
    subject_commit: str
    subject_parent: str
    subject_tree: str
    blobs: Mapping[str, SourceBlobV1]
    hygiene_packets: Mapping[str, SourceBlobV1] = field(default_factory=dict)
    forbidden_paths_present: tuple[str, ...] = ()


@dataclass(frozen=True, slots=True)
class PacketTopologyV1:
    packet_commit: str
    packet_parents: tuple[str, ...]
    write_set: tuple[tuple[str, str], ...]
    head_commit: str
    packet_in_head_history: bool
    packet_blob_at_p: bytes
    markdown_blob_at_p: bytes
    packet_blob_at_head: bytes | None
    markdown_blob_at_head: bytes | None
    worktree_packet: bytes | None
    worktree_markdown: bytes | None


@dataclass(frozen=True, slots=True)
class CurrentSourceStateV1:
    head_blob_ids: Mapping[str, str | None]
    worktree_sha256: Mapping[str, str | None]
    forbidden_paths_present: tuple[str, ...] = ()


@dataclass(frozen=True, slots=True)
class ExecutingToolsV1:
    sha256_by_path: Mapping[str, str]


@dataclass(frozen=True, slots=True)
class TheoremEntryV1:
    index: int
    kind: str
    name: str
    line: int
    statement_sha256: str

    def to_json(self) -> dict[str, object]:
        return {
            "index": self.index,
            "kind": self.kind,
            "name": self.name,
            "line": self.line,
            "statement_sha256": self.statement_sha256,
        }


@dataclass(frozen=True, slots=True)
class ClassShapeV1:
    line: int
    fields: tuple[tuple[str, str], ...]
    frozen: bool
    canonical_keys: tuple[str, ...]


@dataclass(frozen=True, slots=True)
class StructShapeV1:
    line: int
    fields: tuple[tuple[str, str], ...]
    deny_unknown_fields: bool


@dataclass(frozen=True, slots=True)
class ReplayCommandV1:
    command_id: str
    argv: tuple[str, ...]
    cwd: str
    env_names: tuple[str, ...]
    expectation: str
    timeout_seconds: int

    def to_json(self) -> dict[str, object]:
        return {
            "command_id": self.command_id,
            "argv": list(self.argv),
            "cwd": self.cwd,
            "env_names": list(self.env_names),
            "expectation": self.expectation,
            "timeout_seconds": self.timeout_seconds,
        }


@dataclass(frozen=True, slots=True)
class ReplayObservationV1:
    command_id: str
    exit_code: int
    stdout: bytes
    stderr: bytes
    timed_out: bool
    probe_sha256: str | None = None


@dataclass(frozen=True, slots=True)
class ReplayEvaluationV1:
    status: str
    errors: tuple[AdmissionErrorV1, ...]
    runs: tuple[dict[str, object], ...]
    toolchain: dict[str, object] = field(default_factory=dict)


REPLAY_COMMANDS_V1: Final[tuple[ReplayCommandV1, ...]] = (
    ReplayCommandV1(
        "lean_version",
        ("lake", "env", "lean", "--version"),
        "lean-mathlib",
        (),
        "exit 0; version 4.27.0",
        300,
    ),
    ReplayCommandV1(
        "lean_direct_check",
        ("lake", "env", "lean", "-DwarningAsError=true", "Proofs/GlobalClaimantCustodyRelationV1.lean"),
        "lean-mathlib",
        (),
        "exit 0; empty stdout and stderr",
        900,
    ),
    ReplayCommandV1(
        "lean_axioms_probe",
        ("lake", "env", "lean", "<PROBE>"),
        "lean-mathlib",
        (),
        "exit 0; every theorem depends only on allowed axioms; no sorryAx",
        900,
    ),
    ReplayCommandV1(
        "lean_binding_gate",
        (PYTHON_TOKEN_V1, "-m", "pytest", "-q", "-p", "no:cacheprovider", LEAN_GATE_PATH_V1),
        ".",
        (),
        f"exit 0; {LEAN_GATE_EXPECTED_PASSED_V1} passed",
        1800,
    ),
    ReplayCommandV1(
        "lean_certificate_direct_check",
        ("lake", "env", "lean", "-DwarningAsError=true", "Proofs/GlobalAccountingAllocationCertificateV1.lean"),
        "lean-mathlib",
        (),
        "exit 0; empty stdout and stderr",
        900,
    ),
    ReplayCommandV1(
        "lean_certificate_axioms_probe",
        ("lake", "env", "lean", "<CERTIFICATE_PROBE>"),
        "lean-mathlib",
        (),
        "exit 0; every theorem depends only on allowed axioms; no sorryAx",
        900,
    ),
    ReplayCommandV1(
        "lean_certificate_binding_gate",
        (PYTHON_TOKEN_V1, "-m", "pytest", "-q", "-p", "no:cacheprovider", CERTIFICATE_LEAN_GATE_PATH_V1),
        ".",
        (),
        f"exit 0; {CERTIFICATE_LEAN_GATE_EXPECTED_PASSED_V1} passed",
        1800,
    ),
    ReplayCommandV1(
        "esso_validate",
        (ESSO_PYTHON_TOKEN_V1, "-m", "ESSO", "validate", ESSO_MODEL_PATH_V1),
        ".",
        ("PYTHONPATH",),
        "exit 0; ok; ir_hash equals packet",
        600,
    ),
    ReplayCommandV1(
        "esso_verify_multi",
        (
            ESSO_PYTHON_TOKEN_V1,
            "-m",
            "ESSO",
            "verify-multi",
            ESSO_MODEL_PATH_V1,
            "--solvers",
            "z3,cvc5",
            "--determinism-trials",
            str(ESSO_DETERMINISM_TRIALS_V1),
            "--timeout-ms",
            str(ESSO_SOLVER_TIMEOUT_MS_V1),
        ),
        ".",
        ("PYTHONPATH",),
        "exit 0; VERIFIED; solvers agreed; deterministic fingerprints; code hash and versions",
        600,
    ),
    ReplayCommandV1(
        "esso_gate",
        (PYTHON_TOKEN_V1, "-m", "pytest", "-q", "-p", "no:cacheprovider", ESSO_GATE_PATH_V1),
        ".",
        ("PYTHONPATH", "ZENO_ESSO_PYTHON"),
        f"exit 0; {ESSO_GATE_EXPECTED_PASSED_V1} passed",
        1800,
    ),
    ReplayCommandV1(
        "esso_certificate_validate",
        (ESSO_PYTHON_TOKEN_V1, "-m", "ESSO", "validate", CERTIFICATE_ESSO_MODEL_PATH_V1),
        ".",
        ("PYTHONPATH",),
        "exit 0; ok; ir_hash equals packet",
        600,
    ),
    ReplayCommandV1(
        "esso_certificate_verify_multi",
        (
            ESSO_PYTHON_TOKEN_V1,
            "-m",
            "ESSO",
            "verify-multi",
            CERTIFICATE_ESSO_MODEL_PATH_V1,
            "--solvers",
            "z3,cvc5",
            "--determinism-trials",
            str(ESSO_DETERMINISM_TRIALS_V1),
            "--timeout-ms",
            str(ESSO_SOLVER_TIMEOUT_MS_V1),
        ),
        ".",
        ("PYTHONPATH",),
        "exit 0; VERIFIED; solvers agreed; deterministic fingerprints; code hash and versions",
        600,
    ),
    ReplayCommandV1(
        "esso_certificate_gate",
        (PYTHON_TOKEN_V1, "-m", "pytest", "-q", "-p", "no:cacheprovider", CERTIFICATE_ESSO_GATE_PATH_V1),
        ".",
        ("PYTHONPATH", "ZENO_ESSO_PYTHON"),
        f"exit 0; {CERTIFICATE_ESSO_GATE_EXPECTED_PASSED_V1} passed",
        3600,
    ),
    ReplayCommandV1(
        "prior_restage_gate",
        (PYTHON_TOKEN_V1, "-m", "pytest", "-q", "-p", "no:cacheprovider", PRIOR_ESSO_GATE_PATH_V1),
        ".",
        ("PYTHONPATH", "ZENO_ESSO_PYTHON"),
        f"exit 0; {PRIOR_ESSO_GATE_EXPECTED_PASSED_V1} passed",
        1800,
    ),
    ReplayCommandV1(
        "transfer_refinement_gate",
        (PYTHON_TOKEN_V1, "-m", "pytest", "-q", "-p", "no:cacheprovider", TRANSFER_REFINEMENT_GATE_PATH_V1),
        ".",
        (),
        f"exit 0; {TRANSFER_REFINEMENT_GATE_EXPECTED_PASSED_V1} passed",
        1800,
    ),
    ReplayCommandV1(
        "python_rust_bound_parity_gate",
        (PYTHON_TOKEN_V1, "-m", "pytest", "-q", "-p", "no:cacheprovider", PARITY_GATE_PATH_V1),
        ".",
        (),
        f"exit 0; {PARITY_GATE_EXPECTED_PASSED_V1} passed",
        1800,
    ),
    ReplayCommandV1(
        "python_version",
        (PYTHON_TOKEN_V1, "-c", "import sys; print(sys.version.split()[0])"),
        ".",
        (),
        "exit 0; one semantic version line",
        60,
    ),
    ReplayCommandV1(
        "python_projection_gate",
        (PYTHON_TOKEN_V1, "-m", "pytest", "-q", "-p", "no:cacheprovider", PYTHON_GATE_PATH_V1),
        ".",
        (),
        f"exit 0; {PYTHON_GATE_EXPECTED_PASSED_V1} passed",
        600,
    ),
    ReplayCommandV1(
        "rust_projection_gate",
        ("cargo", "test", "--offline", "--locked", "--test", RUST_GATE_TARGET_V1),
        RUST_CRATE_DIR_V1,
        ("CARGO_TARGET_DIR", "CARGO_INCREMENTAL"),
        f"exit 0; {RUST_GATE_EXPECTED_PASSED_V1} passed",
        1800,
    ),
    ReplayCommandV1(
        "rust_version",
        ("cargo", "--version"),
        RUST_CRATE_DIR_V1,
        (),
        "exit 0; one cargo version line",
        60,
    ),
    ReplayCommandV1(
        "rust_compiler_version",
        ("rustc", "-vV"),
        RUST_CRATE_DIR_V1,
        (),
        "exit 0; rustc -vV block with release, commit-hash, and host lines",
        60,
    ),
    ReplayCommandV1(
        "rust_refinement_gate",
        ("cargo", "test", "--offline", "--locked", "--test", RUST_REFINEMENT_GATE_TARGET_V1),
        RUST_CRATE_DIR_V1,
        ("CARGO_TARGET_DIR", "CARGO_INCREMENTAL"),
        f"exit 0; {RUST_REFINEMENT_GATE_EXPECTED_PASSED_V1} passed",
        1800,
    ),
    ReplayCommandV1(
        "python_golden_gate",
        (PYTHON_TOKEN_V1, "-m", "pytest", "-q", "-p", "no:cacheprovider", GOLDEN_PYTHON_TEST_PATH_V1),
        ".",
        (),
        f"exit 0; {PYTHON_GOLDEN_GATE_EXPECTED_PASSED_V1} passed",
        600,
    ),
    ReplayCommandV1(
        "rust_golden_gate",
        ("cargo", "test", "--offline", "--locked", "--test", RUST_GOLDEN_GATE_TARGET_V1),
        RUST_CRATE_DIR_V1,
        ("CARGO_TARGET_DIR", "CARGO_INCREMENTAL"),
        f"exit 0; {RUST_GOLDEN_GATE_EXPECTED_PASSED_V1} passed",
        1800,
    ),
    ReplayCommandV1(
        "rust_bounded_vec_unit_gate",
        ("cargo", "test", "--offline", "--locked", "--lib", "--", RUST_BOUNDED_VEC_UNIT_FILTER_V1),
        RUST_CRATE_DIR_V1,
        ("CARGO_TARGET_DIR", "CARGO_INCREMENTAL"),
        f"exit 0; {RUST_BOUNDED_VEC_UNIT_GATE_EXPECTED_PASSED_V1} passed",
        1800,
    ),
    ReplayCommandV1(
        "python_certificate_golden_gate",
        (PYTHON_TOKEN_V1, "-m", "pytest", "-q", "-p", "no:cacheprovider", CERTIFICATE_PYTHON_TEST_PATH_V1),
        ".",
        (),
        f"exit 0; {CERTIFICATE_PYTHON_GATE_EXPECTED_PASSED_V1} passed",
        600,
    ),
    ReplayCommandV1(
        "rust_certificate_golden_gate",
        ("cargo", "test", "--offline", "--locked", "--test", CERTIFICATE_RUST_GATE_TARGET_V1),
        RUST_CRATE_DIR_V1,
        ("CARGO_TARGET_DIR", "CARGO_INCREMENTAL"),
        f"exit 0; {CERTIFICATE_RUST_GATE_EXPECTED_PASSED_V1} passed",
        1800,
    ),
    ReplayCommandV1(
        "rust_certificate_unit_gate",
        ("cargo", "test", "--offline", "--locked", "--lib", "--", CERTIFICATE_RUST_UNIT_FILTER_V1),
        RUST_CRATE_DIR_V1,
        ("CARGO_TARGET_DIR", "CARGO_INCREMENTAL"),
        f"exit 0; {CERTIFICATE_RUST_UNIT_GATE_EXPECTED_PASSED_V1} passed",
        1800,
    ),
    ReplayCommandV1(
        "python_producer_gate",
        (PYTHON_TOKEN_V1, "-m", "pytest", "-q", "-p", "no:cacheprovider", PRODUCERS_PYTHON_TEST_PATH_V1),
        ".",
        (),
        f"exit 0; {PRODUCERS_PYTHON_GATE_EXPECTED_PASSED_V1} passed",
        600,
    ),
    ReplayCommandV1(
        "rust_producer_gate",
        ("cargo", "test", "--offline", "--locked", "--test", PRODUCERS_RUST_GATE_TARGET_V1),
        RUST_CRATE_DIR_V1,
        ("CARGO_TARGET_DIR", "CARGO_INCREMENTAL"),
        f"exit 0; {PRODUCERS_RUST_GATE_EXPECTED_PASSED_V1} passed",
        1800,
    ),
    *(
        ReplayCommandV1(
            command_id,
            (PYTHON_TOKEN_V1, LEDGER_TOOL_PATH_V1, "--packet", packet, "--rev", "HEAD", "--python", PYTHON_TOKEN_V1),
            ".",
            (),
            f"exit 0; {expected_killed} killed, 0 survived, 0 errors",
            2400,
        )
        for command_id, packet, expected_killed in LEDGER_GATED_PACKETS_V1
    ),
    ReplayCommandV1(
        "python_allocation_projection_gate",
        (PYTHON_TOKEN_V1, "-m", "pytest", "-q", "-p", "no:cacheprovider", PROJECTION_PYTHON_TEST_PATH_V1),
        ".",
        (),
        f"exit 0; {PROJECTION_GATE_EXPECTED_PASSED_V1} passed",
        600,
    ),
    ReplayCommandV1(
        "rust_admission_gate",
        ("cargo", "test", "--offline", "--locked", "--test", ADMISSION_RUST_GATE_TARGET_V1, ADMISSION_RUST_GATE_FILTER_V1),
        RUST_CRATE_DIR_V1,
        ("CARGO_TARGET_DIR", "CARGO_INCREMENTAL"),
        f"exit 0; {ADMISSION_RUST_GATE_EXPECTED_PASSED_V1} passed",
        1800,
    ),
)
REPLAY_COMMAND_IDS_V1: Final[tuple[str, ...]] = tuple(c.command_id for c in REPLAY_COMMANDS_V1)


# ---------------------------------------------------------------------------
# Hashing and JSON
# ---------------------------------------------------------------------------


def sha256_hex_v1(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob_oid_v1(data: bytes) -> str:
    """Return the Git object id of ``data`` stored as a loose blob."""

    header = f"blob {len(data)}\0".encode("ascii")
    return hashlib.sha1(header + data).hexdigest()  # noqa: S324 - Git object identity


def _reject_float(value: str) -> NoReturn:
    _reject("PACKET_JSON_FLOAT", "$", f"floating-point number forbidden: {value}")


def _reject_constant(value: str) -> NoReturn:
    _reject("PACKET_JSON_FLOAT", "$", f"non-finite number forbidden: {value}")


def _closed_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            _reject("PACKET_JSON_DUPLICATE_KEY", f"$.{key}", "duplicate JSON key")
        result[key] = value
    return result


_ASCII_PRINTABLE_RE: Final = re.compile(r"[\x20-\x7e]*")


def _validate_json_value(value: object, context: str) -> None:
    if type(value) is str:
        if _ASCII_PRINTABLE_RE.fullmatch(value) is None:
            _reject("PACKET_NON_ASCII", context, "string must be printable ASCII")
        return
    if value is None or type(value) in {bool, int}:
        return
    if type(value) is list:
        for index, item in enumerate(value):
            _validate_json_value(item, f"{context}[{index}]")
        return
    if type(value) is dict:
        for key, item in value.items():
            if type(key) is not str:
                _reject("PACKET_JSON_MALFORMED", context, "object key is not a string")
            _validate_json_value(item, f"{context}.{key}")
        return
    _reject("PACKET_JSON_MALFORMED", context, f"unsupported value type {type(value).__name__}")


def canonical_packet_bytes_v1(value: object) -> bytes:
    """Return the one accepted packet encoding: sorted keys, compact, ASCII, newline."""

    _validate_json_value(value, "$")
    text = json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True, allow_nan=False)
    return (text + "\n").encode("ascii")


def decode_json_object_v1(raw: bytes, *, context: str, require_canonical: bool) -> dict[str, Any]:
    if len(raw) > MAX_PACKET_BYTES_V1:
        _reject("PACKET_BYTE_CEILING", context, "JSON input exceeds byte ceiling")
    try:
        value = json.loads(
            raw.decode("utf-8"),
            object_pairs_hook=_closed_object,
            parse_float=_reject_float,
            parse_constant=_reject_constant,
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        _reject("PACKET_JSON_MALFORMED", context, type(exc).__name__)
    if type(value) is not dict:
        _reject("PACKET_NOT_OBJECT", context, "expected a JSON object")
    result: dict[str, Any] = value
    _validate_json_value(result, "$")
    if require_canonical and raw != canonical_packet_bytes_v1(result):
        _reject("PACKET_JSON_NONCANONICAL", context, "noncanonical JSON encoding")
    return result


def decode_packet_v1(raw: bytes) -> dict[str, Any]:
    """Decode the committed packet bytes: schema, then canonical encoding, then key set."""

    packet = decode_json_object_v1(raw, context=PACKET_JSON_PATH_V1, require_canonical=False)
    if packet.get("schema") != PACKET_SCHEMA_V15:
        _reject("PACKET_SCHEMA_DRIFT", "schema", f"expected {PACKET_SCHEMA_V15}")
    if raw != canonical_packet_bytes_v1(packet):
        _reject("PACKET_JSON_NONCANONICAL", PACKET_JSON_PATH_V1, "noncanonical JSON encoding")
    if frozenset(packet) != PACKET_KEYS_V3:
        _reject("PACKET_KEY_SET_DRIFT", "$", "top-level key set differs from the closed set")
    return packet


# ---------------------------------------------------------------------------
# Lean extraction
# ---------------------------------------------------------------------------


def _lean_code(text: str, path: str = LEAN_PROOF_PATH_V1) -> str:
    try:
        code: str = strip_lean_noncode(text)
    except ScanError as exc:
        _reject("LEAN_SOURCE_UNPARSEABLE", path, str(exc))
    return code


def _lean_statement_boundary(code: str, index: int) -> bool:
    """True when a depth-zero statement ends here: ``:=`` or a proof-case line."""

    if code.startswith(":=", index):
        return True
    return code[index] == "\n" and code[index + 1 :].lstrip(" \t").startswith("|")


def _lean_statement_end(code: str, start: int, path: str = LEAN_PROOF_PATH_V1) -> int:
    depth = 0
    for index in range(start, len(code)):
        depth += {"(": 1, "[": 1, "{": 1, "⟨": 1, ")": -1, "]": -1, "}": -1, "⟩": -1}.get(code[index], 0)
        if depth == 0 and _lean_statement_boundary(code, index):
            return index
    _reject("LEAN_STATEMENT_UNPARSEABLE", path, f"no statement end after {start}")


def lean_theorem_inventory_v1(text: str, path: str = LEAN_PROOF_PATH_V1) -> tuple[TheoremEntryV1, ...]:
    """Return every theorem/lemma declaration in file order with a statement hash."""

    code = _lean_code(text, path)
    entries: list[TheoremEntryV1] = []
    for match in _LEAN_DECL_RE.finditer(code):
        if "private" in match.group("mods"):
            _reject("LEAN_PRIVATE_THEOREM_FORBIDDEN", path, match.group("name"))
        end = _lean_statement_end(code, match.end(), path)
        statement = " ".join(code[match.end() : end].split())
        entries.append(
            TheoremEntryV1(
                index=len(entries),
                kind=match.group("kind"),
                name=match.group("name"),
                line=code.count("\n", 0, match.start()) + 1,
                statement_sha256=sha256_hex_v1(statement.encode("utf-8")),
            )
        )
    return tuple(entries)


_LEAN_ITEM_START_RE: Final = re.compile(
    r"^(?:@\[[^\]]*\][ \t]*)*(?:(?:private|protected|noncomputable|nonrec)[ \t]+)*"
    r"(?:theorem|lemma|def|abbrev|structure|inductive|instance|class|axiom|opaque|example|"
    r"namespace|end|open|section|variable|universe|set_option|attribute|deriving|import|#[a-z_]+)\b",
    re.MULTILINE,
)


def lean_literal_closure_v1(text: str, path: str = LEAN_PROOF_PATH_V1) -> None:
    """No string, char, or guillemet literal may exist in a pinned proof file, and no `#` command.

    Opus P10 P1-B1: a double quote inside a char literal opens a phantom string for the
    comment/string stripper, and a quote inside a line comment closes it, hiding arbitrary
    commands from every lexical closure while Lean compiles them. With no `"` anywhere in
    the raw file no string can open, so the stripper's string state is unreachable; `#`
    commands (`#exit`, `#eval`, ...) are refused on the stripped code.
    """

    if '"' in text:
        _reject("LEAN_DOUBLE_QUOTE_FORBIDDEN", path, f"line {text.count(chr(10), 0, text.index(chr(34))) + 1}")
    # Opus P13 P2-3: `«a--»` is one identifier to Lean but opens a line comment for the stripper.
    for guillemet in ("\u00ab", "\u00bb"):
        if guillemet in text:
            _reject("LEAN_GUILLEMET_FORBIDDEN", path, f"line {text.count(chr(10), 0, text.index(guillemet)) + 1}")
    # Opus P15 P1-1: `^`-anchoring let a mid-line `#eval` after proof text in an elided
    # region execute IO during replay. Lean accepts a command wherever a command may begin,
    # so the `#` character is banned anywhere in the stripped code (both pinned files carry
    # zero `#` outside comments; a char literal '#' is also rejected, fail-closed).
    hash_command = re.search(r"#", _lean_code(text, path))
    if hash_command is not None:
        _reject("LEAN_COMMAND_FORBIDDEN", path, f"# command at line {text.count(chr(10), 0, hash_command.start()) + 1}")


def lean_command_closure_v1(text: str, path: str = LEAN_PROOF_PATH_V1) -> None:
    """Reject any command that can change what a pinned statement means or add an instance."""

    code = _lean_code(text, path)
    for match in _LEAN_WORD_RE.finditer(code):
        if match.group(1) in _LEAN_FORBIDDEN_WORDS_V1:
            _reject("LEAN_COMMAND_FORBIDDEN", path, f"{match.group(1)} at line {code.count(chr(10), 0, match.start()) + 1}")
    opened = _LEAN_OPEN_COMMAND_RE.search(code)
    if opened is not None:
        _reject("LEAN_COMMAND_FORBIDDEN", path, f"open command at line {code.count(chr(10), 0, opened.start()) + 1}")


def lean_definition_surface_v1(text: str, path: str = LEAN_PROOF_PATH_V1) -> str:
    """Return the normalised proof file with every theorem proof elided.

    Imports, definitions, structures, inductives, and theorem statements stay. The elided
    region after a statement is the indented text up to the next column-zero line; that line
    must start a recognised item (``LEAN_UNRECOGNISED_ITEM`` otherwise) and the region may
    not contain an indented declaration, so the surface hash binds what the theorems mean
    and leaves only how they are proved to replay (Opus C1'''' P1-2).
    """

    code = _lean_code(text, path)
    kept: list[str] = []
    cursor = 0
    for match in _LEAN_DECL_RE.finditer(code):
        statement_end = _lean_statement_end(code, match.end(), path)
        kept.append(code[cursor:statement_end])
        following = _LEAN_COLUMN_ZERO_RE.search(code, statement_end + 1)
        cursor = following.start() if following else len(code)
        if following is not None and cursor < len(code) and _LEAN_ITEM_START_RE.match(code, cursor) is None:
            _reject("LEAN_UNRECOGNISED_ITEM", path, code[cursor : cursor + 40].split(chr(10))[0])
        indented = _LEAN_INDENTED_DECL_RE.search(code, statement_end, cursor)
        if indented is not None:
            _reject("LEAN_UNRECOGNISED_ITEM", path, f"indented declaration at line {code.count(chr(10), 0, indented.start()) + 1}")
    kept.append(code[cursor:])
    return " ".join("".join(kept).split())


def lean_namespace_check_v1(
    text: str, namespace: tuple[str, ...] = LEAN_NAMESPACE_V1, path: str = LEAN_PROOF_PATH_V1
) -> None:
    code = _lean_code(text, path)
    opened = [m.group(2) for m in _LEAN_NAMESPACE_RE.finditer(code) if m.group(1) == "namespace"]
    closed = [m.group(2) for m in _LEAN_NAMESPACE_RE.finditer(code) if m.group(1) == "end"]
    if tuple(opened) != namespace or tuple(closed) != tuple(reversed(namespace)):
        _reject("LEAN_NAMESPACE_DRIFT", path, f"{opened} / {closed}")


def lean_placeholder_matches_v1(text: str, path: str = LEAN_PROOF_PATH_V1) -> tuple[str, ...]:
    try:
        matches = scan_text(path, text, check_axioms=True)
    except ScanError as exc:
        _reject("LEAN_SOURCE_UNPARSEABLE", path, str(exc))
    return tuple(f"{match.rule}:{match.line}" for match in matches)


def lean_import_root_declares_v1(root_text: str, import_line: str = LEAN_IMPORT_LINE_V1) -> bool:
    code = strip_lean_noncode(root_text)
    return any(line.strip() == import_line for line in code.splitlines())


def lean_toolchain_v1(text: str) -> str:
    lines = [line.strip() for line in text.splitlines() if line.strip()]
    if len(lines) != 1:
        _reject("LEAN_TOOLCHAIN_DRIFT", LEAN_TOOLCHAIN_PATH_V1, "expected one toolchain line")
    return lines[0]


# ---------------------------------------------------------------------------
# Python AST extraction
# ---------------------------------------------------------------------------


def _parse_python(source: bytes, path: str) -> ast.Module:
    try:
        return ast.parse(source.decode("utf-8"))
    except (UnicodeDecodeError, SyntaxError) as exc:
        _reject("PYTHON_SOURCE_UNPARSEABLE", path, type(exc).__name__)


def _binds_name(node: ast.AST, name: str) -> bool:
    if isinstance(node, (ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef)):
        return node.name == name
    if isinstance(node, ast.Name):
        return node.id == name and isinstance(node.ctx, (ast.Store, ast.Del))
    if isinstance(node, ast.alias):
        return (node.asname or node.name.split(".")[0]) == name
    if isinstance(node, ast.Global):
        return name in node.names
    return False


def _top_level_class(module: ast.Module, class_name: str, path: str) -> ast.ClassDef:
    """Return the single module-level class of that name; the name is bound nowhere else."""

    found = [n for n in module.body if isinstance(n, ast.ClassDef) and n.name == class_name]
    if not found:
        _reject("PYTHON_CLASS_MISSING", path, class_name)
    if len(found) > 1:
        _reject("PYTHON_CLASS_AMBIGUOUS", path, class_name)
    node = found[0]
    for other in ast.walk(module):
        if other is not node and _binds_name(other, class_name):
            _reject("PYTHON_CLASS_REBOUND", path, f"{class_name} at line {getattr(other, 'lineno', '?')}")
    if node.bases or node.keywords:
        _reject("PYTHON_CLASS_BASES_FORBIDDEN", path, class_name)
    decorators = [
        d for d in node.decorator_list
        if isinstance(d, ast.Call) and isinstance(d.func, ast.Name) and d.func.id == "dataclass"
    ]
    if len(node.decorator_list) != 1 or len(decorators) != 1:
        _reject("PYTHON_CLASS_DECORATORS_DRIFT", path, class_name)
    if any(not isinstance(k.value, ast.Constant) or k.arg is None for k in decorators[0].keywords):
        _reject("PYTHON_CLASS_DECORATORS_DRIFT", path, f"{class_name} dataclass keywords must be literal")
    return node


def _is_frozen_dataclass(node: ast.ClassDef) -> bool:
    for decorator in node.decorator_list:
        if not isinstance(decorator, ast.Call):
            continue
        func = decorator.func
        name = func.id if isinstance(func, ast.Name) else getattr(func, "attr", "")
        frozen = [k for k in decorator.keywords if k.arg == "frozen"]
        if name == "dataclass" and frozen and getattr(frozen[0].value, "value", None) is True:
            return True
    return False


def _canonical_keys(node: ast.ClassDef, path: str) -> tuple[str, ...]:
    """Keys of the single literal dict returned by ``to_canonical`` (no other statements)."""

    methods = [i for i in node.body if isinstance(i, ast.FunctionDef) and i.name == "to_canonical"]
    if len(methods) != 1:
        _reject("PYTHON_CANONICAL_SHAPE", path, f"{node.name} needs exactly one to_canonical")
    body = [
        stmt for stmt in methods[0].body
        if not (isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Constant) and isinstance(stmt.value.value, str))
    ]
    if len(body) != 1 or not isinstance(body[0], ast.Return) or not isinstance(body[0].value, ast.Dict):
        _reject("PYTHON_CANONICAL_SHAPE", path, f"{node.name}.to_canonical must be one literal dict return")
    keys = body[0].value.keys
    if any(not (isinstance(k, ast.Constant) and isinstance(k.value, str)) for k in keys):
        _reject("PYTHON_CANONICAL_SHAPE", path, f"{node.name}.to_canonical keys must be string literals")
    return tuple(str(k.value) for k in keys if isinstance(k, ast.Constant))


def python_class_shape_v1(source: bytes, class_name: str, path: str) -> ClassShapeV1:
    """Return the ordered annotated fields of a top-level class and its canonical keys."""

    node = _top_level_class(_parse_python(source, path), class_name, path)
    fields = tuple(
        (item.target.id, ast.unparse(item.annotation))
        for item in node.body
        if isinstance(item, ast.AnnAssign) and isinstance(item.target, ast.Name)
    )
    return ClassShapeV1(
        line=node.lineno,
        fields=fields,
        frozen=_is_frozen_dataclass(node),
        canonical_keys=_canonical_keys(node, path),
    )


def python_container_field_annotations_v1(source: bytes, class_name: str, path: str) -> dict[str, str]:
    """Return ``{field: annotation}`` of a module-level class under the same closure as the records."""

    node = _top_level_class(_parse_python(source, path), class_name, path)
    return {
        item.target.id: ast.unparse(item.annotation)
        for item in node.body
        if isinstance(item, ast.AnnAssign) and isinstance(item.target, ast.Name)
    }


_PYTHON_DYNAMIC_CALLS_V1: Final[frozenset[str]] = frozenset(
    {"exec", "eval", "compile", "__import__", "globals", "locals", "vars", "setattr", "delattr"}
)
# Attribute-level rebinding hooks that bypass name binding entirely.
_PYTHON_DYNAMIC_ATTRIBUTES_V1: Final[frozenset[str]] = frozenset(
    {"__setattr__", "__delattr__", "__dict__", "__class__", "__builtins__", "__loader__", "__spec__"}
)
# A gate file may call setattr on an instance under test; module rebinding stays forbidden.
_PYTHON_GATE_DYNAMIC_CALLS_V1: Final[frozenset[str]] = _PYTHON_DYNAMIC_CALLS_V1 - {"setattr", "delattr"}
# Modules that reach interpreter state by construction; the pinned modules never need them.
_PYTHON_FORBIDDEN_MODULES_V1: Final[frozenset[str]] = frozenset({"importlib", "ctypes", "gc", "builtins"})


_PYTHON_MODULE_HOOKS_V1: Final[frozenset[str]] = frozenset({"__getattr__", "__dir__"})


def _scan_hook_definitions_v1(node: ast.AST, path: str, *, under_class: bool) -> None:
    """Reject any def/class binding a module hook name outside a class body (by ancestry)."""

    for child in ast.iter_child_nodes(node):
        if (
            isinstance(child, ast.FunctionDef | ast.AsyncFunctionDef | ast.ClassDef)
            and not under_class
            and child.name in _PYTHON_MODULE_HOOKS_V1
        ):
            _reject("PYTHON_DYNAMIC_BINDING_FORBIDDEN", path, f"{child.name} definition at line {child.lineno}")
        _scan_hook_definitions_v1(child, path, under_class=under_class or isinstance(child, ast.ClassDef))


def _binds_hook_name(node: ast.AST, name: str) -> bool:
    """True when ``node`` binds ``name`` by any form other than a def/class (handled at module level)."""

    if isinstance(node, ast.Name):
        return node.id == name and isinstance(node.ctx, ast.Store | ast.Del)
    if isinstance(node, ast.alias):
        return (node.asname or node.name.split(".")[0]) == name
    if isinstance(node, ast.Global | ast.Nonlocal):
        return name in node.names
    if isinstance(node, ast.ExceptHandler):
        return node.name == name
    if isinstance(node, ast.MatchAs | ast.MatchStar):
        return node.name == name
    if isinstance(node, ast.MatchMapping):
        return node.rest == name
    return False


def _is_self_name(node: ast.expr) -> bool:
    return isinstance(node, ast.Name) and node.id == "self"


def python_dynamic_binding_scan_v1(
    source: bytes, path: str, forbidden: frozenset[str] = _PYTHON_DYNAMIC_CALLS_V1
) -> None:
    """Reject dynamic name binding that an AST scan of definitions cannot see through."""

    module = _parse_python(source, path)
    # Opus P13 P1-1: a module hook can be installed by any binding form anywhere in the module
    # (walrus, `global` inside a called function, except/match captures, imports); the only
    # binding left alone is a method named after the hook inside a class body.
    for node in ast.walk(module):
        for hook in _PYTHON_MODULE_HOOKS_V1:
            if _binds_hook_name(node, hook):
                _reject("PYTHON_DYNAMIC_BINDING_FORBIDDEN", path, f"binding of {hook} at line {getattr(node, 'lineno', 0)}")
    # Opus P15 P1-2: a def/class nested in any module-level compound statement still binds in
    # module scope; only a definition under a ClassDef ancestor binds a class attribute instead.
    _scan_hook_definitions_v1(module, path, under_class=False)
    for node in ast.walk(module):
        if isinstance(node, ast.ImportFrom) and any(alias.name == "*" for alias in node.names):
            # Opus P15 P1-2 second vehicle: `from m import *` can supply any name, including a hook.
            _reject("PYTHON_DYNAMIC_BINDING_FORBIDDEN", path, f"import * at line {node.lineno}")
        if isinstance(node, ast.Import | ast.ImportFrom):
            imported = [alias.name for alias in node.names] if isinstance(node, ast.Import) else [node.module or ""]
            for name in imported:
                if name.split(".")[0] in _PYTHON_FORBIDDEN_MODULES_V1:
                    _reject("PYTHON_DYNAMIC_BINDING_FORBIDDEN", path, f"import {name} at line {node.lineno}")
        # Opus C1''' P2-1: a store or delete through an attribute rebinds whatever object the
        # base names (a module, a class, sys.modules[...]); only `self` attributes may be assigned,
        # and subscript stores may only target a name or a `self` attribute.
        if isinstance(node, ast.Attribute) and isinstance(node.ctx, ast.Store | ast.Del) and not _is_self_name(node.value):
            _reject("PYTHON_DYNAMIC_BINDING_FORBIDDEN", path, f"{ast.unparse(node)} store at line {node.lineno}")
        if isinstance(node, ast.Subscript) and isinstance(node.ctx, ast.Store | ast.Del):
            base = node.value
            while isinstance(base, ast.Subscript):
                base = base.value
            if not (isinstance(base, ast.Name) or (isinstance(base, ast.Attribute) and _is_self_name(base.value))):
                _reject("PYTHON_DYNAMIC_BINDING_FORBIDDEN", path, f"{ast.unparse(node)} store at line {node.lineno}")
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in forbidden:
            _reject("PYTHON_DYNAMIC_BINDING_FORBIDDEN", path, f"{node.func.id}() at line {node.lineno}")
        if isinstance(node, ast.Attribute) and node.attr in _PYTHON_DYNAMIC_ATTRIBUTES_V1:
            _reject("PYTHON_DYNAMIC_BINDING_FORBIDDEN", path, f".{node.attr} at line {node.lineno}")
        if isinstance(node, ast.Subscript) and isinstance(node.ctx, (ast.Store, ast.Del)):
            target = ast.unparse(node.value)
            if target.endswith(".modules") or target in {"globals()", "locals()", "vars()"}:
                _reject("PYTHON_DYNAMIC_BINDING_FORBIDDEN", path, f"{target}[...] at line {node.lineno}")


def _top_level_assignments(module: ast.Module) -> dict[str, ast.expr]:
    values: dict[str, ast.expr] = {}
    for node in module.body:
        if isinstance(node, ast.Assign) and len(node.targets) == 1:
            target = node.targets[0]
            if isinstance(target, ast.Name):
                values[target.id] = node.value
        elif isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name) and node.value:
            values[node.target.id] = node.value
    return values


def _string_elements(node: ast.expr | None) -> tuple[str, ...]:
    if isinstance(node, ast.Call) and node.args:
        node = node.args[0]
    if not isinstance(node, (ast.Tuple, ast.List, ast.Set)):
        return ()
    return tuple(str(e.value) for e in node.elts if isinstance(e, ast.Constant))


def python_string_constants_v1(source: bytes, path: str) -> dict[str, str]:
    module = _parse_python(source, path)
    return {
        name: str(value.value)
        for name, value in _top_level_assignments(module).items()
        if isinstance(value, ast.Constant) and isinstance(value.value, str)
    }


def python_sequence_constant_v1(source: bytes, name: str, path: str) -> tuple[str, ...]:
    """Return the string elements of a top-level tuple/list/set/frozenset constant."""

    return _string_elements(_top_level_assignments(_parse_python(source, path)).get(name))


def python_enum_members_v1(source: bytes, class_name: str, path: str) -> tuple[str, ...]:
    """Return the string values assigned in the body of exactly one top-level class, in order."""

    module = _parse_python(source, path)
    classes = [node for node in module.body if isinstance(node, ast.ClassDef) and node.name == class_name]
    if len(classes) != 1:
        _reject("PYTHON_CLASS_AMBIGUOUS", path, f"{len(classes)} definitions of {class_name}")
    members: list[str] = []
    for node in classes[0].body:
        if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
            if isinstance(node.value, ast.Constant) and isinstance(node.value.value, str):
                members.append(node.value.value)
    return tuple(members)


def python_dict_values_v1(source: bytes, name: str, path: str) -> tuple[str, ...]:
    node = _top_level_assignments(_parse_python(source, path)).get(name)
    if not isinstance(node, ast.Dict):
        return ()
    return tuple(str(v.value) for v in node.values if isinstance(v, ast.Constant))


def pytest_param_ids_v1(source: bytes, path: str) -> tuple[str, ...]:
    ids: list[str] = []
    for node in ast.walk(_parse_python(source, path)):
        if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)):
            continue
        if node.func.attr != "param":
            continue
        for keyword in node.keywords:
            if keyword.arg == "id" and isinstance(keyword.value, ast.Constant):
                ids.append(str(keyword.value.value))
    return tuple(ids)


# ---------------------------------------------------------------------------
# Rust structural extraction
# ---------------------------------------------------------------------------


def _blank(out: list[str], text: str, start: int, end: int) -> int:
    for char in text[start:end]:
        out.append("\n" if char == "\n" else " ")
    return end


def _rust_block_comment_end(text: str, start: int) -> int:
    depth = 0
    index = start
    while index < len(text):
        pair = text[index : index + 2]
        if pair == "/*":
            depth += 1
            index += 2
        elif pair == "*/":
            depth -= 1
            index += 2
            if depth == 0:
                return index
        else:
            index += 1
    _reject("RUST_SOURCE_UNPARSEABLE", RUST_STATE_PATH_V1, "unterminated block comment")


def _rust_string_end(text: str, start: int) -> int:
    index = start + 1
    while index < len(text):
        char = text[index]
        if char == "\\":
            index += 2
            continue
        if char == '"':
            return index + 1
        index += 1
    _reject("RUST_SOURCE_UNPARSEABLE", RUST_STATE_PATH_V1, "unterminated string literal")


def _rust_raw_string_end(text: str, start: int) -> int:
    hashes = 0
    index = start + 1
    while index < len(text) and text[index] == "#":
        hashes += 1
        index += 1
    terminator = '"' + "#" * hashes
    end = text.find(terminator, index + 1)
    if end < 0:
        _reject("RUST_SOURCE_UNPARSEABLE", RUST_STATE_PATH_V1, "unterminated raw string")
    return end + len(terminator)


def _rust_char_literal_end(text: str, start: int) -> int | None:
    """Return the end of a char literal starting at ``start`` or None for a lifetime."""

    if start + 2 < len(text) and text[start + 1] != "\\" and text[start + 2] == "'":
        return start + 3
    if start + 1 < len(text) and text[start + 1] == "\\":
        close = text.find("'", start + 3)
        if 0 <= close <= start + 12:
            return close + 1
    return None


def _rust_literal_start(text: str, index: int) -> tuple[str, int] | None:
    pair = text[index : index + 2]
    if pair == "//":
        return ("line", index)
    if pair == "/*":
        return ("block", index)
    if text[index] == '"' or pair == 'b"':
        return ("string", index + (1 if pair == 'b"' else 0))
    if pair in ('r"', "r#") or text[index : index + 3] in ('br"', "br#"):
        return ("raw", index + (2 if text[index] == "b" else 1))
    if text[index] == "'":
        return ("char", index)
    return None


def _rust_line_comment_end(text: str, start: int) -> int:
    end = text.find("\n", start)
    return len(text) if end < 0 else end


_RUST_LITERAL_ENDS: Final[dict[str, Callable[[str, int], int | None]]] = {
    "line": _rust_line_comment_end,
    "block": _rust_block_comment_end,
    "string": _rust_string_end,
    "raw": _rust_raw_string_end,
    "char": _rust_char_literal_end,
}


def strip_rust_noncode_v1(text: str) -> str:
    """Blank comments, strings, raw strings, and char literals; keep offsets and lines."""

    out: list[str] = []
    index = 0
    while index < len(text):
        literal = _rust_literal_start(text, index)
        end = _RUST_LITERAL_ENDS[literal[0]](text, literal[1]) if literal else None
        if end is None:
            out.append(text[index])
            index += 1
        else:
            index = _blank(out, text, index, end)
    return "".join(out)


def _rust_struct_body(code: str, name: str, path: str) -> tuple[int, int, int]:
    matches = list(re.finditer(r"\bstruct\s+" + re.escape(name) + r"\b", code))
    if not matches:
        _reject("RUST_STRUCT_MISSING", path, name)
    if len(matches) > 1:
        _reject("RUST_STRUCT_AMBIGUOUS", path, name)
    match = matches[0]
    if _brace_depth_at(code, match.start()) != 0:
        _reject("RUST_STRUCT_NOT_TOP_LEVEL", path, name)
    index = match.end()
    while index < len(code) and code[index].isspace():
        index += 1
    if index >= len(code) or code[index] != "{":
        _reject("RUST_STRUCT_SHAPE", path, f"{name} is not a brace struct")
    depth = 0
    for cursor in range(index, len(code)):
        depth += {"{": 1, "}": -1}.get(code[cursor], 0)
        if depth == 0:
            return match.start(), index + 1, cursor
    _reject("RUST_STRUCT_SHAPE", path, f"{name} body is unbalanced")


def _split_depth_zero_commas(body: str) -> list[str]:
    items: list[str] = []
    depth = 0
    current: list[str] = []
    previous = ""
    for char in body:
        if not (char == ">" and previous == "-"):
            depth += {"(": 1, "[": 1, "<": 1, ")": -1, "]": -1, ">": -1}.get(char, 0)
        previous = char
        if char == "," and depth == 0:
            items.append("".join(current))
            current = []
        else:
            current.append(char)
    items.append("".join(current))
    return [item for item in items if item.strip()]


def _strip_rust_field_prefix(item: str, path: str, *, allow_attributes: bool) -> str:
    text = item.strip()
    while text.startswith("#["):
        if not allow_attributes:
            _reject("RUST_FIELD_ATTRIBUTE_FORBIDDEN", path, text[:60])
        end = text.find("]")
        text = text[end + 1 :].lstrip() if end >= 0 else ""
    text = re.sub(r"^pub(?:\([^)]*\))?\s+", "", text)
    return text


def _rust_fields(body: str, path: str, *, allow_attributes: bool) -> tuple[tuple[str, str], ...]:
    fields: list[tuple[str, str]] = []
    for item in _split_depth_zero_commas(body):
        match = _RUST_FIELD_RE.match(_strip_rust_field_prefix(item, path, allow_attributes=allow_attributes))
        if match is None:
            _reject("RUST_FIELD_UNPARSEABLE", path, item.strip()[:60])
        fields.append((match.group(1), " ".join(match.group(2).split())))
    return tuple(fields)


def _brace_depth_at(code: str, position: int) -> int:
    depth = 0
    for char in code[:position]:
        depth += {"{": 1, "}": -1}.get(char, 0)
    return depth


def _balanced_end(code: str, start: int) -> int:
    """Return the index just past the token tree opened at ``start`` (one of ( [ {)."""

    pairs = {"(": ")", "[": "]", "{": "}"}
    stack: list[str] = []
    for cursor in range(start, len(code)):
        char = code[cursor]
        if char in pairs:
            stack.append(pairs[char])
        elif stack and char == stack[-1]:
            stack.pop()
            if not stack:
                return cursor + 1
        elif char in ")]}":
            return cursor + 1
    return len(code)


def _rust_record_attributes(code: str, start: int, name: str, path: str) -> None:
    """The record's attribute block is exactly one serde-derive and deny_unknown_fields."""

    prefix = code[max(0, start - 600) : start]
    attrs = _RUST_ATTR_PREFIX_RE.search(prefix)
    if attrs is None:
        _reject("RUST_STRUCT_ATTRIBUTES_DRIFT", path, f"{name} has no attribute block")
    block = [" ".join(item.split()) for item in re.findall(r"#\[[^\]]*\]", attrs.group(1))]
    derives = [item for item in block if item.startswith("#[derive(")]
    others = [item for item in block if not item.startswith("#[derive(")]
    if "#[serde(deny_unknown_fields)]" not in others:
        _reject("RUST_DENY_UNKNOWN_FIELDS_MISSING", path, name)
    if len(derives) != 1 or others != ["#[serde(deny_unknown_fields)]"]:
        _reject("RUST_STRUCT_ATTRIBUTES_DRIFT", path, f"{name}: {' '.join(block)}")
    derived = {item.strip() for item in derives[0][len("#[derive(") : -2].split(",")}
    if not {"Serialize", "Deserialize"} <= derived:
        _reject("RUST_STRUCT_ATTRIBUTES_DRIFT", path, f"{name} must derive Serialize and Deserialize")


def rust_lexical_closure_v1(
    source: bytes,
    path: str,
    record_names: tuple[str, ...],
    *,
    allow_cfg_test: bool = False,
    defines_bounded_vec: bool = False,
    allow_include_str: tuple[str, ...] = (),
    crate_root: bool = False,
) -> str:
    """Reject the source constructs that let a textual struct scan diverge from the compiled type.

    Without ``cfg``, ``include!``, ``#[path]``, item-defining or nested-invoking local
    macros, foreign item-position macros, and item keywords in item-position token
    trees, a ``pub struct`` at brace depth zero is the single definition Rust compiles
    for that name in this module. Returns the stripped code. ``record_names`` is
    reported in errors only; the closure is name-independent.
    """

    try:
        text = source.decode("utf-8")
    except UnicodeDecodeError as exc:
        _reject("RUST_SOURCE_UNPARSEABLE", path, type(exc).__name__)
    code = strip_rust_noncode_v1(text)
    for cfg in re.finditer(r"#!?\[\s*cfg[^\]]*\]", code):
        if not (allow_cfg_test and " ".join(cfg.group(0).split()) == "#[cfg(test)]"):
            _reject("RUST_CFG_FORBIDDEN", path, "cfg or cfg_attr attribute")
    if re.search(r"\binclude(?:_bytes)?!", code):
        _reject("RUST_INCLUDE_FORBIDDEN", path, "include macro")
    includes = re.findall(r'\binclude_str!\s*\(\s*"([^"]*)"\s*\)', text)
    if len(includes) != len(re.findall(r"\binclude_str!", code)) or any(t not in allow_include_str for t in includes):
        _reject("RUST_INCLUDE_FORBIDDEN", path, "include_str outside the allowed targets")
    if re.search(r"#!?\[\s*path\s*=", code):
        _reject("RUST_PATH_ATTRIBUTE_FORBIDDEN", path, "path attribute")
    if re.search(r"\bextern\s+crate\b", code):
        _reject("RUST_EXTERN_CRATE_FORBIDDEN", path, "extern crate")
    # A macro is local only from its definition onward; item-position invocations must be
    # unqualified names of such macros.
    definitions: dict[str, int] = {}
    for definition in re.finditer(r"\bmacro_rules!\s*([A-Za-z_][A-Za-z0-9_]*)", code):
        # Opus C1'''' P1-1: a later macro_rules of the same name shadows the pinned one.
        if definition.group(1) in definitions:
            _reject("RUST_MACRO_REDEFINED", path, definition.group(1))
        definitions[definition.group(1)] = definition.start()
    for match in _RUST_MACRO_INVOCATION_RE.finditer(code):
        tree = code[match.start(2) : _balanced_end(code, match.start(2))]
        head = code[match.start() : match.start() + 60]
        if match.group(1) == "macro_rules":
            if _RUST_ITEM_KEYWORD_RE.search(tree):
                _reject("RUST_MACRO_DEFINES_ITEM", path, head)
            if _RUST_MACRO_INVOCATION_RE.search(tree):
                _reject("RUST_MACRO_NESTED_INVOCATION", path, head)
            # Only the pinned bounded-vec macro (defined once, body pinned by the container
            # closure) may define a function; any other fn-producing macro is an item factory.
            named = re.search(r"macro_rules!\s*([A-Za-z_][A-Za-z0-9_]*)", code[match.start() : match.start(2)])
            if re.search(r"\bfn\b", tree) and (named is None or named.group(1) != BOUNDED_VEC_MACRO_NAME_V1):
                _reject("RUST_MACRO_DEFINES_ITEM", path, head)
        elif match.group(1) == "include_str" and allow_include_str:
            continue
        elif _brace_depth_at(code, match.start()) == 0:
            qualified = code[max(0, match.start() - 2) : match.start()] == "::"
            defined_before = definitions.get(match.group(1))
            if qualified or defined_before is None or defined_before > match.start():
                _reject("RUST_FOREIGN_ITEM_MACRO", path, head)
            if _RUST_ITEM_KEYWORD_RE.search(tree):
                _reject("RUST_MACRO_DEFINES_ITEM", path, head)
    use_code = _strip_rust_attributes_v1(code)
    for use in _RUST_USE_RE.finditer(use_code):
        target = " ".join(use.group(1).split())
        is_pub = "pub" in use_code[max(0, use.start()) : use.start(1)]
        for full_path, bound_name in _expand_use_paths(target, path):
            leaf = full_path.rsplit("::", 1)[-1]
            if leaf == "*":
                if not (crate_root and is_pub and re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*::\*", full_path)):
                    _reject("RUST_GLOB_IMPORT_FORBIDDEN", path, full_path[:60])
                continue
            if bound_name in _RUST_SERDE_NAMES_V1 or leaf in _RUST_SERDE_NAMES_V1:
                if full_path != f"serde::{leaf}" or bound_name != leaf:
                    _reject("RUST_SERDE_IMPORT_DRIFT", path, full_path[:60])
            if not defines_bounded_vec and (bound_name == "deserialize_bounded_vec_v1" or leaf == "deserialize_bounded_vec_v1"):
                if full_path != "crate::bounded_vec::deserialize_bounded_vec_v1" or bound_name != leaf:
                    _reject("RUST_BOUNDED_VEC_IMPORT_DRIFT", path, full_path[:60])
    return code


_RUST_USE_PATH: Final = r"(?:[A-Za-z_][A-Za-z0-9_]*(?:::[A-Za-z_][A-Za-z0-9_]*)*(?:::\*)?|\*|self)"


def _strip_rust_attributes_v1(code: str) -> str:
    """Blank every attribute (length-preserving) so no attribute prefix hides a statement."""

    return _RUST_ATTRIBUTE_RE.sub(lambda match: " " * len(match.group(0)), code)


def _split_use_items(body: str) -> list[str]:
    items: list[str] = []
    depth = 0
    current: list[str] = []
    for char in body:
        depth += {"{": 1, "}": -1}.get(char, 0)
        if char == "," and depth == 0:
            items.append("".join(current))
            current = []
        else:
            current.append(char)
    items.append("".join(current))
    return [item for item in items if item.strip()]


def _expand_use_paths(target: str, path: str) -> list[tuple[str, str]]:
    """Expand a `use` tree (brace groups, `as` aliases, globs) into (full path, bound name) pairs."""

    def expand(text: str, prefix: str) -> list[tuple[str, str]]:
        text = text.strip()
        brace = text.find("{")
        if brace >= 0:
            if text.find("}") < 0 or _balanced_end(text, brace) != len(text):
                _reject("RUST_USE_UNPARSEABLE", path, text[:60])
            head = (prefix + text[:brace]).strip()
            pairs: list[tuple[str, str]] = []
            for item in _split_use_items(text[brace + 1 : -1]):
                pairs.extend(expand(item, head))
            return pairs
        alias = re.fullmatch(r"(" + _RUST_USE_PATH + r")\s+as\s+([A-Za-z_][A-Za-z0-9_]*)", text)
        if alias:
            full = prefix + alias.group(1)
            return [(full, alias.group(2))]
        if re.fullmatch(_RUST_USE_PATH, text) is None:
            _reject("RUST_USE_UNPARSEABLE", path, text[:60])
        full = prefix.rstrip(":") if text == "self" else prefix + text
        return [(full, full.rsplit("::", 1)[-1])]

    return expand(target, "")


def rust_struct_shape_v1(source: bytes, struct_name: str, path: str) -> StructShapeV1:
    """Return the ordered fields of a top-level brace struct and whether serde denies unknown fields.

    The record structs carry exactly ``#[derive(...)]`` (with Serialize and
    Deserialize) and ``#[serde(deny_unknown_fields)]`` and no field attributes, so no
    serde renaming, flattening, defaulting, or custom (de)serialisation can widen the
    wire schema behind the scanned field list.
    """

    try:
        text = source.decode("utf-8")
    except UnicodeDecodeError as exc:
        _reject("RUST_SOURCE_UNPARSEABLE", path, type(exc).__name__)
    code = strip_rust_noncode_v1(text)
    start, body_start, body_end = _rust_struct_body(code, struct_name, path)
    _rust_record_attributes(code, start, struct_name, path)
    return StructShapeV1(
        line=code.count("\n", 0, start) + 1,
        fields=_rust_fields(code[body_start:body_end], path, allow_attributes=False),
        deny_unknown_fields=True,
    )


def _rust_fields_with_attributes(body: str, path: str) -> dict[str, tuple[str, str]]:
    """Return ``{field: (attribute block, type)}`` for a struct whose fields may carry attributes."""

    fields: dict[str, tuple[str, str]] = {}
    for item in _split_depth_zero_commas(body):
        text = item.strip()
        attributes: list[str] = []
        while text.startswith("#["):
            end = text.find("]")
            attributes.append(" ".join(text[: end + 1].split()) if end >= 0 else text)
            text = text[end + 1 :].lstrip() if end >= 0 else ""
        text = re.sub(r"^pub(?:\([^)]*\))?\s+", "", text)
        match = _RUST_FIELD_RE.match(text)
        if match is None:
            _reject("RUST_FIELD_UNPARSEABLE", path, item.strip()[:60])
        fields[match.group(1)] = (" ".join(attributes), " ".join(match.group(2).split()))
    return fields


def rust_container_field_types_v1(source: bytes, struct_name: str, path: str) -> dict[str, str]:
    """Return ``{field: type}`` of a top-level struct whose fields may carry attributes."""

    code = strip_rust_noncode_v1(source.decode("utf-8", errors="strict"))
    _, body_start, body_end = _rust_struct_body(code, struct_name, path)
    return {name: kind for name, (_, kind) in _rust_fields_with_attributes(code[body_start:body_end], path).items()}


def _normalized(text: str) -> str:
    return " ".join(text.split())


def rust_container_deserializer_closure_v1(source: bytes, path: str) -> None:
    """Bind the two record containers' deserialisers to the local bounded-vec macro.

    The only attribute a record container may carry is
    ``#[serde(deserialize_with = "<fn>")]`` naming the closed deserialiser for that
    container; that function must be produced by exactly one item-position
    invocation of the local ``bounded_state_vec_deserializer_v1!`` macro with the
    record type, must not be defined as a plain ``fn`` anywhere, and the macro body
    must equal the pinned template, so the only decoding path for a record is
    serde's derive on the record type (``deny_unknown_fields``) through
    ``Vec<T>``'s bounded sequence visitor.
    """

    code = strip_rust_noncode_v1(source.decode("utf-8", errors="strict"))
    _, body_start, body_end = _rust_struct_body(code, STATE_CLASS_NAME_V1, path)
    fields = _rust_fields_with_attributes(code[body_start:body_end], path)
    macro = re.search(r"\bmacro_rules!\s*" + BOUNDED_VEC_MACRO_NAME_V1 + r"\s*\{", code)
    if macro is None:
        _reject("RUST_BOUNDED_VEC_MACRO_MISSING", path, BOUNDED_VEC_MACRO_NAME_V1)
    body = code[macro.end() : _balanced_end(code, macro.end() - 1) - 1]
    if _normalized(body) != BOUNDED_VEC_MACRO_BODY_V1:
        _reject("RUST_BOUNDED_VEC_MACRO_DRIFT", path, _normalized(body)[:80])
    for container, record in CONTAINER_RECORD_FIELDS_V1:
        function = CONTAINER_DESERIALIZERS_V1[container]
        attributes, _ = fields.get(container, ("", ""))
        # String literals are blanked in stripped code, so the literal reads as whitespace here.
        if re.fullmatch(r"#\[serde\(deserialize_with =\s*\)\]", attributes) is None:
            _reject("RUST_CONTAINER_ATTRIBUTE_DRIFT", path, f"{container}: {attributes[:60]}")
        # Strings are blanked in stripped code; bind the name through the raw source.
        raw = source.decode("utf-8", errors="strict")
        expected_attribute = f'#[serde(deserialize_with = "{function}")]\n    pub {container}:'
        if raw.count(expected_attribute) != 1:
            _reject("RUST_CONTAINER_ATTRIBUTE_DRIFT", path, f"{container}: deserialize_with must name {function}")
        pattern = r"\b" + BOUNDED_VEC_MACRO_NAME_V1 + r"!\(\s*" + function + r"\s*,\s*" + record + r"\s*,\s*MAX_GLOBAL_[A-Z_]+_V1\s*,"
        invocations = list(re.finditer(pattern, code))
        # Codex C1'' P1 (Rust): a block-local invocation (`const _: () = { ... };`) defines
        # nothing at module scope; only an item-position (brace depth zero) invocation binds
        # the name the container attribute selects.
        item_position = [m for m in invocations if _brace_depth_at(code, m.start()) == 0]
        if len(invocations) != 1 or len(item_position) != 1 or re.search(r"\bfn\s+" + function + r"\b", code):
            _reject("RUST_CONTAINER_DESERIALIZER_DRIFT", path, f"{function}: {len(item_position)} item-position macro invocations")


def rust_bounded_vec_closure_v1(source: bytes, path: str) -> None:
    """The bounded-vec deserialiser file is closed and carries the pinned decoding fragments."""

    code = rust_lexical_closure_v1(
        source, path, (TERMINAL_CLASS_NAME_V1, OUTBOX_CLASS_NAME_V1), allow_cfg_test=True, defines_bounded_vec=True
    )
    # The `#[cfg(test)] mod tests { ... }` block never compiles into the library; drop it.
    library = code
    test_module = re.search(r"#\[cfg\(test\)\]\s*mod\s+tests\s*\{", code)
    if test_module is not None:
        library = code[: test_module.start()] + code[_balanced_end(code, test_module.end() - 1) :]
    if _normalized(library) != BOUNDED_VEC_LIBRARY_TEMPLATE_V1:
        _reject("RUST_BOUNDED_VEC_DRIFT", path, "library portion differs from the pinned template")
    if sha256_hex_v1(source) != BOUNDED_VEC_FILE_SHA256_V1:
        _reject("RUST_BOUNDED_VEC_DRIFT", path, "whole file differs from the pinned bytes (test module included)")


# Codex C1'' P1 (Rust): the compiled module graph is closed. Every `mod` the crate root
# declares is listed here; a new module (for example one hosting a widening deserialiser)
# is a reviewed edit of this table, and inline modules are rejected outright.
RUST_CRATE_MODULES_V1: Final[tuple[str, ...]] = (
    "asset_lane_coordinator",
    "asset_lane_projection",
    "asset_transfer",
    "asset_transfer_lane_module",
    "asset_transfer_policy_registry",
    "asset_transfer_receipt_admission",
    "asset_transfer_types",
    "bounded_vec",
    "canonical",
    "current_profile_lane_gate",
    "economic_command_authentication",
    "economic_command_authorization_registry",
    "economic_command_signature_verifier_deployment",
    "economic_command_signature_verifier_registry",
    "economic_effect_occurrence",
    "economic_epoch_receipt_verification",
    "economic_initial_state",
    "economic_initial_state_atom_coverage",
    "economic_initial_state_outbox_continuity",
    "economic_initial_state_replay_continuity",
    "economic_initial_state_terminal_continuity",
    "effects",
    "epoch_effect_composition",
    "external_custody_disabled_lane",
    "global_accounting_allocation_certificate",
    "global_accounting_lane_producers",
    "global_economic_replay_refinement",
    "global_economic_state_delta",
    "global_economic_state_effect_refinement",
    "global_oracle_occurrence_authority",
    "global_oracle_price_occurrence",
    "lane_capability_registry",
    "lane_composition_receipt_verification",
    "lane_module_receipt_verification",
    "lane_module_release_route_binding",
    "managed_asset_lifecycle",
    "managed_asset_lifecycle_lane_module",
    "managed_asset_lifecycle_types",
    "managed_asset_policy_registry",
    "migration",
    "perps_margin",
    "perps_margin_lane_coordinator",
    "perps_margin_lane_module",
    "perps_margin_types",
    "perps_market_policy",
    "proof",
    "proof_rewards_policy_blocked_lane",
    "receipt_backed_asset_lane_composition",
    "receipt_backed_perps_margin_lane_composition",
    "release",
    "route_composition_receipt_verification",
    "route_global_state_projection",
    "state",
    "zdex_atomic_buyback",
    "zdex_atomic_buyback_lane_ports",
    "zdex_atomic_buyback_quote_port_v2",
    "zdex_atomic_buyback_state",
    "zdex_buyback_price_authority",
    "zdex_buyback_price_safety",
    "zdex_buyback_shadow_composer_v2",
    "zdex_buyback_spend",
    "zdex_current_authority",
    "zdex_fee_allocation",
    "zdex_fee_allocation_profile_binding",
    "zdex_fee_allocation_receipt_verification",
    "zdex_fee_allocation_types",
    "zdex_hyperdeflation",
    "zdex_hyperdeflation_decode",
    "zdex_hyperdeflation_results",
    "zdex_hyperdeflation_route_refinement",
    "zdex_hyperdeflation_types",
    "zdex_hyperdeflation_validation",
    "zdex_purchase_burn_effects",
    "zdex_purchase_burn_receipt_verification",
    "zdex_purchase_burn_route",
    "zdex_purchase_burn_types",
    "zdex_spot_buyback_transition",
    "zdex_spot_buyback_transition_v2",
    "zdex_tokenomics_buyback_transition",
    "zdex_tokenomics_buyback_transition_v2",
    "zdex_tokenomics_fee_lane_coordinator",
    "zdex_tokenomics_fee_lane_receipt_verification",
    "zdex_tokenomics_fee_lane_types",
    "zdex_tokenomics_lane_coordinator",
    "zdex_tokenomics_lane_receipt_common",
    "zdex_tokenomics_lane_receipt_verification",
    "zdex_tokenomics_lane_types",
)
_RUST_MOD_DECL_RE: Final = re.compile(r"^[ \t]*(?:pub(?:\([^)]*\))?[ \t]+)?mod[ \t]+([A-Za-z_][A-Za-z0-9_]*)[ \t]*;", re.MULTILINE)
# The state module may import only these roots (plus the exact bounded-vec deserialiser),
# never through an alias, and never a name reserved for the local macro-produced items.
RUST_STATE_IMPORT_ROOTS_V1: Final[tuple[str, ...]] = ("serde::", "crate::canonical::", "crate::release::")
RUST_CRATE_PINNED_MODULES_V1: Final[tuple[str, ...]] = ("state", "bounded_vec")
RUST_CRATE_RESERVED_NAMES_V1: Final[frozenset[str]] = frozenset({"state", "bounded_vec", "canonical", "release", "serde"})
RUST_BOUNDED_VEC_IMPORT_V1: Final = "crate::bounded_vec::deserialize_bounded_vec_v1"


def rust_state_import_closure_v1(source: bytes, path: str) -> None:
    """Every name the state module imports comes from a closed set of paths, unaliased.

    Codex C1'' P1 (Rust): the container deserialisers must be produced by the local macro,
    so no ``use`` may bind their names or the macro name from anywhere, and the module may
    import only serde, the exact bounded-vec deserialiser, and the crate's canonical and
    release items.
    """

    code = _strip_rust_attributes_v1(strip_rust_noncode_v1(source.decode("utf-8", errors="strict")))
    reserved = (BOUNDED_VEC_MACRO_NAME_V1, *CONTAINER_DESERIALIZERS_V1.values())
    for use in _RUST_USE_RE.finditer(code):
        for full_path, bound_name in _expand_use_paths(" ".join(use.group(1).split()), path):
            leaf = full_path.rsplit("::", 1)[-1]
            if leaf == "*" or bound_name != leaf:
                _reject("RUST_STATE_IMPORT_DRIFT", path, f"{bound_name} <- {full_path[:50]}")
            if bound_name in reserved:
                _reject("RUST_STATE_IMPORT_DRIFT", path, f"{bound_name} imported from {full_path[:50]}")
            if full_path != RUST_BOUNDED_VEC_IMPORT_V1 and not full_path.startswith(RUST_STATE_IMPORT_ROOTS_V1):
                _reject("RUST_STATE_IMPORT_DRIFT", path, full_path[:60])


def rust_crate_root_closure_v1(source: bytes, path: str) -> None:
    """The crate root declares ``mod state;`` unconditionally and exactly the pinned module set."""

    code = rust_lexical_closure_v1(source, path, (TERMINAL_CLASS_NAME_V1, OUTBOX_CLASS_NAME_V1), crate_root=True)
    # Opus C1''' P1-2: `mod state;` and `mod bounded_vec;` each appear exactly once as file modules.
    for module in RUST_CRATE_PINNED_MODULES_V1:
        declarations = re.findall(r"^\s*(?:pub(?:\([^)]*\))?\s+)?mod\s+" + module + r"\s*;", code, re.MULTILINE)
        if len(declarations) != 1:
            _reject("RUST_STATE_MODULE_DECLARATION_DRIFT", path, f"{len(declarations)} declarations of mod {module}")
        if re.search(r"\bmod\s+" + module + r"\s*\{", code):
            _reject("RUST_STATE_MODULE_DECLARATION_DRIFT", path, f"inline mod {module}")
    # No crate-root `use` may bind a name the state module resolves through the crate root.
    for use in _RUST_USE_RE.finditer(_strip_rust_attributes_v1(code)):
        for full_path, bound_name in _expand_use_paths(" ".join(use.group(1).split()), path):
            if bound_name in RUST_CRATE_RESERVED_NAMES_V1:
                _reject("RUST_CRATE_ROOT_REBINDING", path, f"{bound_name} <- {full_path[:50]}")
    declared = tuple(sorted(_RUST_MOD_DECL_RE.findall(code)))
    if declared != RUST_CRATE_MODULES_V1:
        difference = ",".join(sorted(set(declared) ^ set(RUST_CRATE_MODULES_V1))) or f"count {len(declared)}"
        _reject("RUST_CRATE_MODULE_SET_DRIFT", path, difference[:80])
    if re.search(r"\bmod\s+[A-Za-z_][A-Za-z0-9_]*\s*\{", code):
        _reject("RUST_CRATE_MODULE_SET_DRIFT", path, "inline module")


def rust_manifest_closure_v1(source: bytes, path: str) -> None:
    """Cargo.toml keeps the default lib and test target layout and the registry serde crates."""

    try:
        manifest = tomllib.loads(source.decode("utf-8"))
    except (UnicodeDecodeError, tomllib.TOMLDecodeError) as exc:
        _reject("CARGO_MANIFEST_UNPARSEABLE", path, type(exc).__name__)
    package = manifest.get("package")
    if not isinstance(package, dict) or package.get("name") != RUST_CRATE_NAME_V1:
        _reject("CARGO_PACKAGE_NAME_DRIFT", path, str(package.get("name") if isinstance(package, dict) else None))
    lib = manifest.get("lib")
    if isinstance(lib, dict) and ("path" in lib or "name" in lib):
        _reject("CARGO_LIB_TARGET_OVERRIDE", path, ",".join(sorted(lib)))
    for key in ("test", "bench", "example", "bin", "patch", "replace", "build", "workspace", "features", "profile"):
        if key in manifest:
            _reject("CARGO_TARGET_OVERRIDE_FORBIDDEN", path, key)
    for key in ("autobins", "autoexamples", "autotests", "autobenches", "build", "links", "workspace"):
        if key in package:
            _reject("CARGO_TARGET_OVERRIDE_FORBIDDEN", path, f"package.{key}")
    if "build" in package:
        _reject("CARGO_TARGET_OVERRIDE_FORBIDDEN", path, "package.build")
    for table in ("dependencies", "dev-dependencies", "build-dependencies"):
        rows = manifest.get(table)
        if not isinstance(rows, dict):
            continue
        for crate, spec in rows.items():
            if isinstance(spec, dict) and any(k in spec for k in ("path", "git", "registry", "package")):
                _reject("CARGO_DEPENDENCY_SOURCE_OVERRIDE", path, f"{table}.{crate}")
            version = spec.get("version") if isinstance(spec, dict) else spec
            if not isinstance(version, str) or not version.startswith("="):
                _reject("CARGO_DEPENDENCY_VERSION_NOT_EXACT", path, f"{table}.{crate}")


# ---------------------------------------------------------------------------
# ESSO extraction
# ---------------------------------------------------------------------------


def esso_model_surface_v1(blob: bytes, path: str = ESSO_MODEL_PATH_V1) -> tuple[str, tuple[str, ...], tuple[str, ...]]:
    """Return (model_id, ordered invariant ids, ordered action ids) from the ESSO-IR yaml."""

    try:
        data = yaml.safe_load(blob.decode("utf-8"))
    except (UnicodeDecodeError, yaml.YAMLError) as exc:
        _reject("ESSO_MODEL_UNPARSEABLE", path, type(exc).__name__)
    if not isinstance(data, dict) or not isinstance(data.get("meta"), dict):
        _reject("ESSO_MODEL_UNPARSEABLE", path, "meta object required")
    model_id = data["meta"].get("model_id")
    invariants = data.get("invariants")
    actions = data.get("actions")
    if not isinstance(model_id, str) or not isinstance(invariants, list) or not isinstance(actions, list):
        _reject("ESSO_MODEL_UNPARSEABLE", path, "model_id, invariants, actions required")
    return (
        model_id,
        tuple(str(row.get("id")) for row in invariants if isinstance(row, dict)),
        tuple(str(row.get("id")) for row in actions if isinstance(row, dict)),
    )


# ---------------------------------------------------------------------------
# Projection of the admitted source commit
# ---------------------------------------------------------------------------


def _blob(snapshot: SubjectSnapshotV1, path: str) -> SourceBlobV1:
    blob = snapshot.blobs.get(path)
    if blob is None:
        _reject("SOURCE_PIN_MISSING_IN_SUBJECT", path, "pinned path absent from subject commit")
    return blob


def _project_source_pins(snapshot: SubjectSnapshotV1) -> list[dict[str, object]]:
    pins: list[dict[str, object]] = []
    for path, role in SOURCE_PIN_ROLES_V1:
        blob = _blob(snapshot, path)
        pins.append(
            {
                "path": path,
                "role": role,
                "mode": blob.mode,
                "git_blob": blob.git_blob,
                "sha256": blob.sha256,
                "size": blob.size,
            }
        )
    return pins


def _project_esso_subject(snapshot: SubjectSnapshotV1, subject: EssoSubjectV1) -> dict[str, object]:
    model = _blob(snapshot, subject.model_path)
    gate = _blob(snapshot, subject.gate_path)
    model_id, invariants, actions = esso_model_surface_v1(model.data, subject.model_path)
    if model_id != subject.model_id:
        _reject("ESSO_MODEL_ID_DRIFT", subject.model_path, model_id)
    if invariants != subject.invariants:
        _reject("ESSO_INVARIANTS_DRIFT", subject.model_path, ",".join(invariants))
    if actions != subject.actions:
        _reject("ESSO_ACTIONS_DRIFT", subject.model_path, ",".join(actions))
    constants = python_string_constants_v1(gate.data, subject.gate_path)
    if model.sha256 not in constants.values():
        _reject("ESSO_GATE_SOURCE_PIN_DRIFT", subject.gate_path, "gate does not pin the model sha256")
    gate_invariants = python_sequence_constant_v1(gate.data, "EXPECTED_INVARIANTS", subject.gate_path)
    if frozenset(gate_invariants) != frozenset(subject.invariants):
        _reject("ESSO_GATE_INVARIANTS_DRIFT", subject.gate_path, ",".join(gate_invariants))
    mutants = pytest_param_ids_v1(gate.data, subject.gate_path)
    if tuple(m for m in mutants if m in subject.named_mutants) != subject.named_mutants:
        _reject("ESSO_GATE_MUTANTS_DRIFT", subject.gate_path, ",".join(mutants))
    ir_hash = constants.get("RECORDED_IR_HASH", "")
    if not ir_hash.startswith("sha256:") or _HEX64_RE.fullmatch(ir_hash[7:]) is None:
        _reject("ESSO_IR_HASH_DRIFT", subject.gate_path, "RECORDED_IR_HASH malformed")
    if constants.get("RECORDED_ESSO_CODE_HASH") != ESSO_CODE_COMMIT_V1:
        _reject("ESSO_CODE_COMMIT_DRIFT", subject.gate_path, "RECORDED_ESSO_CODE_HASH drift")
    return {
        "model_id": model_id,
        "model_path": subject.model_path,
        "model_source_sha256": model.sha256,
        "actions": list(actions),
        "invariants": list(invariants),
        "queries": list(subject.queries),
        "named_mutants": list(subject.named_mutants),
        "esso_code_commit": ESSO_CODE_COMMIT_V1,
        "ir_hash": ir_hash,
        "ir_hash_role": IR_HASH_ROLE_V1,
        "fingerprint": constants.get("RECORDED_FINGERPRINT", ""),
        "fingerprint_role": FINGERPRINT_ROLE_V1,
        "solvers": dict(ESSO_SOLVERS_V1),
        "determinism_trials": ESSO_DETERMINISM_TRIALS_V1,
        "solver_timeout_ms": ESSO_SOLVER_TIMEOUT_MS_V1,
        "gate_expected_passed": subject.gate_expected_passed,
        "replay_only": {"validate": subject.validate_command, "verify_multi": subject.verify_command, "gate": subject.gate_command},
        "claim_boundary": subject.claim_boundary,
    }


def _project_esso(snapshot: SubjectSnapshotV1) -> dict[str, object]:
    relation = _project_esso_subject(snapshot, O008_ESSO_SUBJECT_V1)
    return {**relation, "certificate_model": _project_esso_subject(snapshot, CERTIFICATE_ESSO_SUBJECT_V1)}


def _check_lean_gate(
    snapshot: SubjectSnapshotV1, names: tuple[str, ...], subject: LeanSubjectV1 = O008_LEAN_SUBJECT_V1
) -> None:
    gate = _blob(snapshot, subject.gate_path)
    if python_sequence_constant_v1(gate.data, "THEOREMS", subject.gate_path) != names:
        _reject("LEAN_GATE_THEOREMS_DRIFT", subject.gate_path, "THEOREMS differs from inventory")
    expected_pins = tuple(_blob(snapshot, path).sha256 for path in subject.gate_pin_order)
    if python_dict_values_v1(gate.data, "PINNED_SOURCES", subject.gate_path) != expected_pins:
        _reject("LEAN_GATE_PIN_DRIFT", subject.gate_path, "PINNED_SOURCES differ from subject")
    axioms = python_sequence_constant_v1(gate.data, "ALLOWED_STANDARD_AXIOMS", subject.gate_path)
    if frozenset(axioms) != ALLOWED_LEAN_AXIOMS_V1:
        _reject("LEAN_GATE_AXIOMS_DRIFT", subject.gate_path, ",".join(axioms))


def _project_lean_subject(snapshot: SubjectSnapshotV1, subject: LeanSubjectV1) -> dict[str, object]:
    """Project one pinned Lean subject: inventory, statement and surface hashes, command closure."""

    proof = _blob(snapshot, subject.path).data.decode("utf-8")
    lean_literal_closure_v1(proof, subject.path)
    placeholders = lean_placeholder_matches_v1(proof, subject.path)
    if placeholders:
        _reject("LEAN_PLACEHOLDER_PRESENT", subject.path, ",".join(placeholders))
    lean_namespace_check_v1(proof, subject.namespace, subject.path)
    lean_command_closure_v1(proof, subject.path)
    inventory = lean_theorem_inventory_v1(proof, subject.path)
    pairs = tuple((entry.kind, entry.name) for entry in inventory)
    if pairs != subject.inventory:
        _reject("LEAN_THEOREM_INVENTORY_DRIFT", subject.path, _first_difference(pairs, subject.inventory))
    for entry in inventory:
        if subject.statement_sha256.get(entry.name) != entry.statement_sha256:
            _reject("LEAN_STATEMENT_DRIFT", subject.path, entry.name)
    surface_sha256 = sha256_hex_v1(lean_definition_surface_v1(proof, subject.path).encode("utf-8"))
    if surface_sha256 != subject.definition_surface_sha256:
        _reject("LEAN_DEFINITION_SURFACE_DRIFT", subject.path, surface_sha256[:16])
    if not lean_import_root_declares_v1(_blob(snapshot, LEAN_ROOT_PATH_V1).data.decode("utf-8"), subject.import_line):
        _reject("LEAN_IMPORT_ROOT_MISSING", LEAN_ROOT_PATH_V1, subject.import_line)
    return {
        "path": subject.path,
        "namespace": ".".join(subject.namespace),
        "import_root_declares_module": True,
        "theorems": [entry.to_json() for entry in inventory],
        "statement_binding": LEAN_STATEMENT_BINDING_V1,
        "definition_surface_sha256": surface_sha256,
        "theorem_count": len(inventory),
        "definitional_theorems": list(subject.definitional_theorems),
        "witness_theorems": list(subject.witness_theorems),
        "substantive_theorem_count": len(inventory) - len(subject.definitional_theorems) - len(subject.witness_theorems),
        "placeholder_scan": {"match_count": 0, "axiom_check": True},
        "allowed_axioms": sorted(ALLOWED_LEAN_AXIOMS_V1),
        "replay_only": {
            "direct_warning_as_error_check": subject.direct_check_command,
            "print_axioms_probe": subject.axioms_probe_command,
            "binding_gate": subject.binding_gate_command,
            "binding_gate_expected_passed": subject.gate_expected_passed,
        },
        "claim_boundary": subject.claim_boundary,
    }


def _project_lean(snapshot: SubjectSnapshotV1) -> dict[str, object]:
    toolchain = lean_toolchain_v1(_blob(snapshot, LEAN_TOOLCHAIN_PATH_V1).data.decode("utf-8"))
    if toolchain != LEAN_TOOLCHAIN_V1:
        _reject("LEAN_TOOLCHAIN_DRIFT", LEAN_TOOLCHAIN_PATH_V1, toolchain)
    relation = _project_lean_subject(snapshot, O008_LEAN_SUBJECT_V1)
    return {
        "toolchain": toolchain,
        **relation,
        "no_recovery_theorem": LEAN_NO_RECOVERY_THEOREM_V1,
        "certificate_model": _project_lean_subject(snapshot, CERTIFICATE_LEAN_SUBJECT_V1),
    }


def _first_difference(pairs: tuple[tuple[str, str], ...], inventory: tuple[tuple[str, str], ...] = THEOREM_INVENTORY_V1) -> str:
    for index, (actual, expected) in enumerate(zip(pairs, inventory, strict=False)):
        if actual != expected:
            return f"index {index}: {actual} != {expected}"
    return f"count {len(pairs)} != {len(inventory)}"


def _check_python_record(shape: ClassShapeV1, fields: tuple[tuple[str, str], ...],
                         forbidden: tuple[str, ...], label: str) -> None:
    names = tuple(name for name, _ in shape.fields)
    present = [name for name in forbidden if name in names]
    if present:
        _reject(f"{label}_FORBIDDEN_FIELD_PRESENT", PYTHON_TYPES_PATH_V1, ",".join(present))
    if shape.fields != fields:
        _reject(f"PYTHON_{label}_FIELD_ORDER_DRIFT", PYTHON_TYPES_PATH_V1, str(shape.fields))
    if shape.canonical_keys != names:
        _reject(f"PYTHON_{label}_CANONICAL_KEYS_DRIFT", PYTHON_TYPES_PATH_V1, str(shape.canonical_keys))
    if not shape.frozen:
        _reject(f"PYTHON_{label}_NOT_FROZEN", PYTHON_TYPES_PATH_V1, "frozen dataclass required")


def _check_rust_record(shape: StructShapeV1, fields: tuple[tuple[str, str], ...],
                       forbidden: tuple[str, ...], label: str) -> None:
    names = tuple(name for name, _ in shape.fields)
    present = [name for name in forbidden if name in names]
    if present:
        _reject(f"{label}_FORBIDDEN_FIELD_PRESENT", RUST_STATE_PATH_V1, ",".join(present))
    if shape.fields != fields:
        _reject(f"RUST_{label}_FIELD_ORDER_DRIFT", RUST_STATE_PATH_V1, str(shape.fields))
    if not shape.deny_unknown_fields:
        _reject("RUST_DENY_UNKNOWN_FIELDS_MISSING", RUST_STATE_PATH_V1, label)


def _record_projection(python: ClassShapeV1, rust: StructShapeV1, absent: tuple[str, ...],
                       class_name: str) -> dict[str, object]:
    if tuple(n for n, _ in python.fields) != tuple(n for n, _ in rust.fields):
        _reject(f"{class_name}_CROSS_LANGUAGE_FIELD_DRIFT", RUST_STATE_PATH_V1, "field names differ")
    return {
        "python": {
            "module": PYTHON_TYPES_PATH_V1,
            "class": class_name,
            "line": python.line,
            "fields": [list(field) for field in python.fields],
            "canonical_keys": list(python.canonical_keys),
            "frozen": True,
        },
        "rust": {
            "module": RUST_STATE_PATH_V1,
            "struct": class_name,
            "line": rust.line,
            "fields": [list(field) for field in rust.fields],
            "deny_unknown_fields": True,
        },
        "absent_fields": list(absent),
    }


def _rust_str_array(raw: str, name: str, path: str) -> tuple[str, ...]:
    match = re.search(r"const " + name + r": \[&str; (\d+)\] = \[([^\]]*)\];", raw)
    if match is None:
        _reject("RUST_GATE_CONTENT_DRIFT", path, f"{name} array missing")
    items = tuple(re.findall(r'"([^"]*)"', match.group(2)))
    if len(items) != int(match.group(1)):
        _reject("RUST_GATE_CONTENT_DRIFT", path, f"{name} length")
    return items


def _check_projection_gates(snapshot: SubjectSnapshotV1) -> dict[str, object]:
    """Pin the content of the compiled and imported projection gates, not only their bytes."""

    rust_raw = _blob(snapshot, RUST_GATE_PATH_V1).data.decode("utf-8", errors="strict")
    rust_code = rust_lexical_closure_v1(
        _blob(snapshot, RUST_GATE_PATH_V1).data, RUST_GATE_PATH_V1, (), allow_include_str=RUST_GATE_INCLUDES_V1
    )
    if _blob(snapshot, RUST_GATE_PATH_V1).sha256 != RUST_GATE_SHA256_V1:
        _reject("RUST_GATE_CONTENT_DRIFT", RUST_GATE_PATH_V1, "bytes differ from the pinned gate")
    rust_tests = tuple(_RUST_TEST_FN_RE.findall(rust_code))
    if rust_tests != RUST_GATE_TESTS_V1:
        _reject("RUST_GATE_CONTENT_DRIFT", RUST_GATE_PATH_V1, ",".join(rust_tests)[:80])
    terminal_names = tuple(name for name, _ in TERMINAL_FIELDS_RUST_V1)
    outbox_names = tuple(name for name, _ in OUTBOX_FIELDS_RUST_V1)
    expected_arrays = (
        ("TERMINAL_FIELDS", terminal_names),
        ("OUTBOX_FIELDS", outbox_names),
        ("TERMINAL_FORBIDDEN", TERMINAL_FORBIDDEN_FIELDS_V1),
        ("OUTBOX_FORBIDDEN", OUTBOX_FORBIDDEN_FIELDS_V1),
    )
    for name, expected in expected_arrays:
        if _rust_str_array(rust_raw, name, RUST_GATE_PATH_V1) != expected:
            _reject("RUST_GATE_CONTENT_DRIFT", RUST_GATE_PATH_V1, name)
    python_source = _blob(snapshot, PYTHON_GATE_PATH_V1).data
    module = _parse_python(python_source, PYTHON_GATE_PATH_V1)
    if sha256_hex_v1(ast.dump(module, include_attributes=False).encode("utf-8")) != PYTHON_GATE_AST_SHA256_V1:
        _reject("PYTHON_GATE_CONTENT_DRIFT", PYTHON_GATE_PATH_V1, "module AST differs from the pinned gate")
    python_tests = tuple(n.name for n in module.body if isinstance(n, ast.FunctionDef) and n.name.startswith("test_"))
    if python_tests != PYTHON_GATE_TESTS_V1:
        _reject("PYTHON_GATE_CONTENT_DRIFT", PYTHON_GATE_PATH_V1, ",".join(python_tests)[:80])
    python_dynamic_binding_scan_v1(python_source, PYTHON_GATE_PATH_V1, _PYTHON_GATE_DYNAMIC_CALLS_V1)
    if python_sequence_constant_v1(python_source, "TERMINAL_FIELDS", PYTHON_GATE_PATH_V1) != terminal_names:
        _reject("PYTHON_GATE_CONTENT_DRIFT", PYTHON_GATE_PATH_V1, "TERMINAL_FIELDS")
    if python_sequence_constant_v1(python_source, "OUTBOX_FIELDS", PYTHON_GATE_PATH_V1) != outbox_names:
        _reject("PYTHON_GATE_CONTENT_DRIFT", PYTHON_GATE_PATH_V1, "OUTBOX_FIELDS")
    if python_sequence_constant_v1(python_source, "TERMINAL_UNKNOWN_FIELDS", PYTHON_GATE_PATH_V1) != TERMINAL_FORBIDDEN_FIELDS_V1:
        _reject("PYTHON_GATE_CONTENT_DRIFT", PYTHON_GATE_PATH_V1, "TERMINAL_UNKNOWN_FIELDS")
    if python_sequence_constant_v1(python_source, "OUTBOX_UNKNOWN_FIELDS", PYTHON_GATE_PATH_V1) != OUTBOX_FORBIDDEN_FIELDS_V1:
        _reject("PYTHON_GATE_CONTENT_DRIFT", PYTHON_GATE_PATH_V1, "OUTBOX_UNKNOWN_FIELDS")
    return {
        "rust": {"path": RUST_GATE_PATH_V1, "tests": list(rust_tests), "expected_passed": RUST_GATE_EXPECTED_PASSED_V1},
        "python": {"path": PYTHON_GATE_PATH_V1, "tests": list(python_tests), "expected_passed": PYTHON_GATE_EXPECTED_PASSED_V1},
        "seeded_unknown_keys": "both gates generate unknown keys from a printed seed and require rejection of every one",
    }


def _check_container_bindings(python_source: bytes, rust_source: bytes) -> None:
    """The V1 state containers hold exactly the scanned record types."""

    python_fields = python_container_field_annotations_v1(python_source, STATE_CLASS_NAME_V1, PYTHON_TYPES_PATH_V1)
    python_dynamic_binding_scan_v1(python_source, PYTHON_TYPES_PATH_V1)
    rust_fields = rust_container_field_types_v1(rust_source, STATE_CLASS_NAME_V1, RUST_STATE_PATH_V1)
    rust_container_deserializer_closure_v1(rust_source, RUST_STATE_PATH_V1)
    for container, record in CONTAINER_RECORD_FIELDS_V1:
        if python_fields.get(container) != f"tuple[{record}, ...]":
            _reject("PYTHON_STATE_FIELD_TYPE_DRIFT", PYTHON_TYPES_PATH_V1, f"{container}: {python_fields.get(container)}")
        if rust_fields.get(container) != f"Vec<{record}>":
            _reject("RUST_STATE_FIELD_TYPE_DRIFT", RUST_STATE_PATH_V1, f"{container}: {rust_fields.get(container)}")


def certificate_fixture_surface_v1(fixture: object) -> dict[str, object]:
    """Validate the decoded golden fixture against the closed certificate surface and summarise it.

    Total over decoded JSON: every nested shape is type-checked before use, so a hostile
    fixture yields ``CERTIFICATE_FIXTURE_DRIFT`` rather than an untyped exception.
    """

    path = CERTIFICATE_FIXTURE_PATH_V1
    if not isinstance(fixture, dict):
        _reject("CERTIFICATE_FIXTURE_DRIFT", path, "object required")
    if fixture.get("fixture_schema") != CERTIFICATE_FIXTURE_SCHEMA_V1 or fixture.get("certificate_schema") != CERTIFICATE_SCHEMA_V1:
        _reject("CERTIFICATE_FIXTURE_DRIFT", path, "schema")
    if fixture.get("authority") != "NONE":
        _reject("CERTIFICATE_FIXTURE_DRIFT", path, "authority")
    messages = fixture.get("reject_messages")
    if not isinstance(messages, dict) or tuple(sorted(messages)) != tuple(sorted(CERTIFICATE_REJECT_CODES_V1)):
        _reject("CERTIFICATE_FIXTURE_DRIFT", path, "reject_messages")
    order = fixture.get("check_order")
    if not isinstance(order, list) or tuple(order) != CERTIFICATE_CHECK_ORDER_V1:
        _reject("CERTIFICATE_FIXTURE_DRIFT", path, "check_order")
    registry = fixture.get("producer_registry")
    if not isinstance(registry, dict) or not all(isinstance(entry, dict) for entry in registry.values()):
        _reject("CERTIFICATE_PRODUCER_DRIFT", path, "registry shape")
    kinds = {str(lane): entry.get("producer_kind") for lane, entry in registry.items()}
    if kinds != CERTIFICATE_PRODUCER_KINDS_V1:
        drifted = sorted(f"{lane}:{kind}" for lane, kind in kinds.items() if CERTIFICATE_PRODUCER_KINDS_V1.get(lane) != kind)
        _reject("CERTIFICATE_PRODUCER_DRIFT", path, drifted[0] if drifted else "registry")
    vectors = fixture.get("vectors")
    if not isinstance(vectors, dict) or len(vectors) != CERTIFICATE_FIXTURE_VECTORS_V1:
        _reject("CERTIFICATE_FIXTURE_DRIFT", path, "vectors")
    accepted: list[str] = []
    for name, vector in sorted(vectors.items()):
        if not isinstance(vector, dict) or not isinstance(vector.get("expected_outcome"), dict):
            _reject("CERTIFICATE_FIXTURE_DRIFT", path, f"vector {name} shape")
        outcome = vector["expected_outcome"]
        if outcome.get("status") != "ACCEPT":
            continue
        certificate = vector.get("certificate")
        fragments = certificate.get("ordered_lane_fragments") if isinstance(certificate, dict) else None
        if not isinstance(fragments, list) or not all(isinstance(fragment, dict) for fragment in fragments):
            _reject("CERTIFICATE_FIXTURE_DRIFT", path, f"accepted vector {name} certificate shape")
        for fragment in fragments:
            if fragment.get("enabled") is not False or any(fragment.get(field) for field in CERTIFICATE_FRAGMENT_ROW_FIELDS_V1):
                _reject("CERTIFICATE_FIXTURE_DRIFT", path, f"accepted vector {name} is not registered-empty")
            registered_root = CERTIFICATE_REGISTERED_EMPTY_ROOTS_V1.get(str(fragment.get("lane_id")))
            if registered_root is not None and fragment.get("lane_state_root") != registered_root:
                _reject("CERTIFICATE_FIXTURE_DRIFT", path, f"accepted vector {name} lane {fragment.get('lane_id')} is not at its registered-empty root")
        accepted.append(str(name))
    if len(accepted) != CERTIFICATE_FIXTURE_ACCEPTED_V1:
        _reject("CERTIFICATE_FIXTURE_DRIFT", path, f"{len(accepted)} accepted vectors")
    return {
        "fixture": path,
        "vectors": len(vectors),
        "accepted_vectors": accepted,
        "accepted_vectors_are_registered_empty_over_disabled_lanes": True,
        "python_replay": CERTIFICATE_PYTHON_TEST_PATH_V1,
        "rust_replay": CERTIFICATE_RUST_TEST_PATH_V1,
    }


def _project_certificate(snapshot: SubjectSnapshotV1) -> dict[str, object]:
    """Bind the implemented sidecar checker: check order, closed reject codes, registry, golden fixture."""

    python_source = _blob(snapshot, CERTIFICATE_PYTHON_PATH_V1).data
    order = python_sequence_constant_v1(python_source, "CHECK_ORDER_V1", CERTIFICATE_PYTHON_PATH_V1)
    if order != CERTIFICATE_CHECK_ORDER_V1:
        _reject("CERTIFICATE_CHECK_ORDER_DRIFT", CERTIFICATE_PYTHON_PATH_V1, ",".join(order)[:80])
    codes = python_enum_members_v1(python_source, CERTIFICATE_REJECT_CODE_CLASS_V1, CERTIFICATE_PYTHON_PATH_V1)
    if codes != CERTIFICATE_REJECT_CODES_V1:
        _reject("CERTIFICATE_REJECT_CODES_DRIFT", CERTIFICATE_PYTHON_PATH_V1, ",".join(codes)[:80])
    producers_source = _blob(snapshot, PRODUCERS_PYTHON_PATH_V1).data
    for enum_name, expected_codes in (
        ("LaneProducerRejectCodeV1", LANE_PRODUCER_REJECT_CODES_V1),
        ("ReceiptBackedProducerRejectCodeV1", RECEIPT_BACKED_PRODUCER_REJECT_CODES_V1),
    ):
        members = python_enum_members_v1(producers_source, enum_name, PRODUCERS_PYTHON_PATH_V1)
        if members != expected_codes:
            _reject("PRODUCER_REJECT_CODES_DRIFT", PRODUCERS_PYTHON_PATH_V1, f"{enum_name}: {','.join(members)[:60]}")
    python_dynamic_binding_scan_v1(python_source, CERTIFICATE_PYTHON_PATH_V1)
    _blob(snapshot, CERTIFICATE_RUST_PATH_V1)
    _blob(snapshot, CERTIFICATE_RENDERER_PATH_V1)
    try:
        fixture = json.loads(_blob(snapshot, CERTIFICATE_FIXTURE_PATH_V1).data.decode("utf-8"))
    except (UnicodeDecodeError, ValueError) as exc:
        _reject("CERTIFICATE_FIXTURE_UNPARSEABLE", CERTIFICATE_FIXTURE_PATH_V1, type(exc).__name__)
    return {
        "status": CERTIFICATE_IMPLEMENTATION_STATUS_V1,
        "python": CERTIFICATE_PYTHON_PATH_V1,
        "rust": CERTIFICATE_RUST_PATH_V1,
        "check_order": list(order),
        "reject_codes": list(codes),
        "producer_registry": dict(CERTIFICATE_PRODUCER_KINDS_V1),
        "receipt_backed_producers": 1,
        "receipt_backed_producer_implementations": {
            "asset_transfer": {
                "python": PRODUCERS_PYTHON_PATH_V1,
                "rust": PRODUCERS_RUST_PATH_V1,
                "binding": "produce_asset_transfer_fragment_v1 folds one accepted asset-transfer transition into a fragment whose binding_root is the journal receipt root, refusing lane, disabled-lane, release, post-root, carry-forward (prior lane, prior release, pre root), terminal-root, non-canonical-entitlement, fold-ceiling, and coverage drift with eleven closed codes (accepted-validation, lane, disabled-lane, release, post-root, carry-forward incl. prior kind and enabled flag, terminal-root, non-canonical-or-over-ceiling entitlements, fold-ceiling, coverage, and defensive fragment-validation); only the receipt root carries custody rows and chain/epoch context (the committed lane root carries none of it), so fragment integrity rests on C9 receipt admission; until then the certificate registry keeps ASSET_TRANSFER at NO_PRODUCER, no acceptance path uses this producer, and the registry count above stays 0",
            }
        },
        "golden": certificate_fixture_surface_v1(fixture),
        "registered_empty_producers": {
            "python": PRODUCERS_PYTHON_PATH_V1,
            "rust": PRODUCERS_RUST_PATH_V1,
            "lanes": dict(CERTIFICATE_REGISTERED_EMPTY_ROOTS_V1),
            "binding": "a registered-empty lane is accepted only when its committed lane root is the root of its unique empty typed lane state (REGISTERED_EMPTY_ROOT_DRIFT otherwise); the producer is a pure function of that committed root",
        },
        "lean_model": CERTIFICATE_LEAN_PATH_V1,
        "esso_model": CERTIFICATE_ESSO_MODEL_PATH_V1,
        "mounted": False,
    }


def _project_information_loss(snapshot: SubjectSnapshotV1) -> dict[str, object]:
    python_source = _blob(snapshot, PYTHON_TYPES_PATH_V1).data
    rust_source = _blob(snapshot, RUST_STATE_PATH_V1).data
    rust_lexical_closure_v1(rust_source, RUST_STATE_PATH_V1, (TERMINAL_CLASS_NAME_V1, OUTBOX_CLASS_NAME_V1))
    rust_state_import_closure_v1(rust_source, RUST_STATE_PATH_V1)
    rust_crate_root_closure_v1(_blob(snapshot, RUST_LIB_PATH_V1).data, RUST_LIB_PATH_V1)
    rust_manifest_closure_v1(_blob(snapshot, RUST_MANIFEST_PATH_V1).data, RUST_MANIFEST_PATH_V1)
    rust_bounded_vec_closure_v1(_blob(snapshot, RUST_BOUNDED_VEC_PATH_V1).data, RUST_BOUNDED_VEC_PATH_V1)
    _blob(snapshot, RUST_LOCKFILE_PATH_V1)
    if snapshot.forbidden_paths_present:
        _reject("CARGO_CONFIG_PRESENT", snapshot.forbidden_paths_present[0], "cargo config present at the subject commit")
    _check_container_bindings(python_source, rust_source)
    gates = _check_projection_gates(snapshot)
    terminal_py = python_class_shape_v1(python_source, TERMINAL_CLASS_NAME_V1, PYTHON_TYPES_PATH_V1)
    terminal_rs = rust_struct_shape_v1(rust_source, TERMINAL_CLASS_NAME_V1, RUST_STATE_PATH_V1)
    outbox_py = python_class_shape_v1(python_source, OUTBOX_CLASS_NAME_V1, PYTHON_TYPES_PATH_V1)
    outbox_rs = rust_struct_shape_v1(rust_source, OUTBOX_CLASS_NAME_V1, RUST_STATE_PATH_V1)
    _check_python_record(terminal_py, TERMINAL_FIELDS_PYTHON_V1, TERMINAL_FORBIDDEN_FIELDS_V1, "TERMINAL")
    _check_rust_record(terminal_rs, TERMINAL_FIELDS_RUST_V1, TERMINAL_FORBIDDEN_FIELDS_V1, "TERMINAL")
    _check_python_record(outbox_py, OUTBOX_FIELDS_PYTHON_V1, OUTBOX_FORBIDDEN_FIELDS_V1, "OUTBOX")
    _check_rust_record(outbox_rs, OUTBOX_FIELDS_RUST_V1, OUTBOX_FORBIDDEN_FIELDS_V1, "OUTBOX")
    if sha256_hex_v1(rust_source) != RUST_STATE_FILE_SHA256_V1:
        _reject("RUST_STATE_FILE_DRIFT", RUST_STATE_PATH_V1, "whole file differs from the pinned bytes")
    return {
        "terminal_projection": _record_projection(
            terminal_py, terminal_rs, TERMINAL_ABSENT_FIELDS_V1, TERMINAL_CLASS_NAME_V1
        ),
        "external_outbox": _record_projection(
            outbox_py, outbox_rs, OUTBOX_ABSENT_FIELDS_V1, OUTBOX_CLASS_NAME_V1
        ),
        "scope": INFORMATION_LOSS_SCOPE_V1,
        "binding": dict(INFORMATION_LOSS_BINDING_V1),
        "projection_gates": gates,
        "opaque_bindings": list(OPAQUE_BINDINGS_V1),
        "accepted_known_gaps": list(ACCEPTED_KNOWN_GAPS_V1),
        "formal_result": INFORMATION_LOSS_FORMAL_RESULT_V1,
        "mounted_exploit_claim": False,
    }


def _hygiene_pins(blob: SourceBlobV1) -> dict[str, str]:
    """Return ``{pinned path: sha256}`` of one test-hygiene packet after shape checks."""

    packet = decode_json_object_v1(blob.data, context=blob.path, require_canonical=False)
    stem = blob.path.rsplit("/", 1)[-1].removesuffix(".json")
    if packet.get("schema") != HYGIENE_SCHEMA_V1 or packet.get("evidence_id") != stem:
        _reject("THV1_SHAPE", blob.path, "schema and evidence_id must match the file")
    pins: dict[str, str] = {}
    for key in ("source_pins", "test_pins"):
        rows = packet.get(key)
        if not isinstance(rows, list) or not all(isinstance(row, dict) for row in rows):
            _reject("THV1_SHAPE", blob.path, f"{key} must be a list of objects")
        for row in rows:
            pins[str(row.get("path"))] = str(row.get("sha256"))
    return pins


_HYGIENE_LINEAGE_RE: Final = re.compile(r"^(.*?)(?:-v([0-9]+))?(\.json)?$")
_HYGIENE_DATE_PREFIX_RE: Final = re.compile(r"^THV1-[0-9]{8}-")


def hygiene_lineage_key_v1(path: str) -> tuple[str, int, str]:
    """Order key for hygiene packets: lineage name, then the numeric ``-vN`` suffix, then the path."""

    match = _HYGIENE_LINEAGE_RE.fullmatch(path)
    if match is None:
        return (path, -1, path)
    version = -1 if match.group(2) is None else int(match.group(2))
    return (match.group(1), version, path)


def _require_hygiene_lineage_versions_monotone_v1(paths: list[str]) -> None:
    """Refuse a hygiene lineage whose versions regress across date prefixes (Opus P32 F-2);
    identical rule to tools.test_hygiene_evidence_v1.require_lineage_versions_monotone_with_dates_v1."""

    by_lineage: dict[str, list[tuple[str, int, str]]] = {}
    for path in paths:
        lineage_with_date, version, _ = hygiene_lineage_key_v1(path)
        stem = lineage_with_date.rsplit("/", 1)[-1]
        date = stem[:14] if _HYGIENE_DATE_PREFIX_RE.match(stem) else ""
        by_lineage.setdefault(_HYGIENE_DATE_PREFIX_RE.sub("", stem), []).append((date, version, path))
    for lineage, rows in by_lineage.items():
        for date_a, version_a, path_a in rows:
            for date_b, version_b, path_b in rows:
                if date_a < date_b and version_a >= version_b:
                    _reject("THV1_LINEAGE_VERSION_REGRESSES_ACROSS_DATES", path_a, f"{lineage}: before {path_b.rsplit('/', 1)[-1]}")


def _select_hygiene_packets(snapshot: SubjectSnapshotV1) -> list[dict[str, object]]:
    """Select, per required path, the newest hygiene packet whose pin equals the subject blob.

    Packets are ordered by lineage version (the trailing ``-vN`` compared numerically, so
    ``v10`` outranks ``v9``), newest first: stale packets are skipped, a path with no matching
    packet is drift, and a selected packet that pins the O-008 packet itself is circular. The
    repository hygiene gate orders packets by the same lineage key
    (tools.test_hygiene_evidence_v1.hygiene_lineage_key_v1, pinned equal to this one by a
    parity test), requires every pin of the packet it selects to be current (mirrored here over the
    subject-visible pins as ``THV1_SELECTED_PACKET_STALE``), and additionally requires the
    selected packet to satisfy the contract rules for the changed path (evidence families, risk
    class), which this checker does not model; a version cut under an older date prefix is refused
    by both gates (``THV1_LINEAGE_VERSION_REGRESSES_ACROSS_DATES`` here) instead of reordered, so
    recency across lineages stays date-first (Opus P32 F-2); before the ordering alignment it
    iterated lexicographically, so a stale ``v9`` outranked ``v27`` for any path whose bytes
    it still matched, and it bound a partly stale packet as evidence.
    """

    _require_hygiene_lineage_versions_monotone_v1([blob.path for blob in snapshot.hygiene_packets.values()])
    ordered = sorted(snapshot.hygiene_packets.values(), key=lambda blob: hygiene_lineage_key_v1(blob.path), reverse=True)
    pins_by_packet = {blob.path: _hygiene_pins(blob) for blob in ordered}
    selection: list[dict[str, object]] = []
    for path in THV1_REQUIRED_PIN_PATHS_V1:
        expected = _blob(snapshot, path).sha256
        chosen = next((blob for blob in ordered if pins_by_packet[blob.path].get(path) == expected), None)
        if chosen is None:
            _reject("THV1_PIN_DRIFT", HYGIENE_EVIDENCE_DIR_V1, path)
        pins = pins_by_packet[chosen.path]
        circular = [item for item in (PACKET_JSON_PATH_V1, PACKET_MD_PATH_V1) if item in pins]
        if circular:
            _reject("THV1_PINS_PACKET_CIRCULAR", chosen.path, ",".join(circular))
        selection.append(
            {
                "path": path,
                "packet_path": chosen.path,
                "packet_git_blob": chosen.git_blob,
                "packet_sha256": chosen.sha256,
                "pin_sha256": expected,
            }
        )
    # Fable P31 NEW-26: the repository gate requires EVERY pin of the packet it selects to be
    # current; mirror it here over the pins the subject snapshot can see (after per-path
    # selection, so a changed required path still reports its own THV1_PIN_DRIFT first). Pins
    # on paths outside the subject snapshot are not verifiable in this pure core; the
    # repository gate, which the chain runs against the parent and the campaign base, covers them.
    for packet_path in sorted({str(row["packet_path"]) for row in selection}):
        for pinned_path, pinned_sha in sorted(pins_by_packet[packet_path].items()):
            current = snapshot.blobs.get(pinned_path)
            if current is not None and current.sha256 != pinned_sha:
                _reject("THV1_SELECTED_PACKET_STALE", packet_path, pinned_path)
    return selection


AUTHOR_RUN_KEYS_V1: Final[frozenset[str]] = frozenset({"command_id", "exit_code", "comparable"})
AUTHOR_TOOLCHAIN_KEYS_V1: Final[frozenset[str]] = frozenset({"esso_code_hash", "lean", "python", "rust", "rustc", "solvers"})
RUSTC_TOOLCHAIN_KEYS_V1: Final[frozenset[str]] = frozenset({"rustc_release", "rustc_commit_hash", "rustc_host"})
LEAN_VERSION_V1: Final = LEAN_TOOLCHAIN_V1.rsplit("v", 1)[1]
# Closed comparable schema per replay command: key -> ("hex64" | "semver" | "verdict" | "solvers" | exact value).
COMPARABLE_SCHEMA_V1: Final[dict[str, dict[str, object]]] = {
    "lean_version": {"lean_version": LEAN_VERSION_V1},
    "lean_direct_check": {"stdout_sha256": EMPTY_SHA256_V1},
    "lean_axioms_probe": {"probe_sha256": "hex64", "theorems_probed": len(THEOREM_INVENTORY_V1)},
    "lean_binding_gate": {"passed": LEAN_GATE_EXPECTED_PASSED_V1},
    "lean_certificate_direct_check": {"stdout_sha256": EMPTY_SHA256_V1},
    "lean_certificate_axioms_probe": {"probe_sha256": "hex64", "theorems_probed": len(CERTIFICATE_THEOREM_INVENTORY_V1)},
    "lean_certificate_binding_gate": {"passed": CERTIFICATE_LEAN_GATE_EXPECTED_PASSED_V1},
    "esso_validate": {"ir_hash": "esso_ir_hash"},
    "esso_verify_multi": {
        "verdict": "VERIFIED",
        "fingerprint": "esso_fingerprint",
        "solvers": "solvers",
        "esso_code_hash": ESSO_CODE_COMMIT_V1,
    },
    "esso_gate": {"passed": ESSO_GATE_EXPECTED_PASSED_V1},
    "esso_certificate_validate": {"ir_hash": "esso_certificate_ir_hash"},
    "esso_certificate_verify_multi": {
        "verdict": "VERIFIED",
        "fingerprint": "esso_certificate_fingerprint",
        "solvers": "solvers",
        "esso_code_hash": ESSO_CODE_COMMIT_V1,
    },
    "esso_certificate_gate": {"passed": CERTIFICATE_ESSO_GATE_EXPECTED_PASSED_V1},
    "prior_restage_gate": {"passed": PRIOR_ESSO_GATE_EXPECTED_PASSED_V1},
    "transfer_refinement_gate": {"passed": TRANSFER_REFINEMENT_GATE_EXPECTED_PASSED_V1},
    "python_rust_bound_parity_gate": {"passed": PARITY_GATE_EXPECTED_PASSED_V1},
    "python_version": {"python_version": "semver"},
    "python_projection_gate": {"passed": PYTHON_GATE_EXPECTED_PASSED_V1},
    "rust_projection_gate": {"passed": RUST_GATE_EXPECTED_PASSED_V1},
    "rust_version": {"cargo_version": "semver"},
    "rust_compiler_version": {"rustc_release": "semver", "rustc_commit_hash": "hex40", "rustc_host": "host_triple"},
    "rust_refinement_gate": {"passed": RUST_REFINEMENT_GATE_EXPECTED_PASSED_V1},
    "python_golden_gate": {"passed": PYTHON_GOLDEN_GATE_EXPECTED_PASSED_V1},
    "rust_golden_gate": {"passed": RUST_GOLDEN_GATE_EXPECTED_PASSED_V1},
    "rust_bounded_vec_unit_gate": {"passed": RUST_BOUNDED_VEC_UNIT_GATE_EXPECTED_PASSED_V1},
    "python_certificate_golden_gate": {"passed": CERTIFICATE_PYTHON_GATE_EXPECTED_PASSED_V1},
    "rust_certificate_golden_gate": {"passed": CERTIFICATE_RUST_GATE_EXPECTED_PASSED_V1},
    "rust_certificate_unit_gate": {"passed": CERTIFICATE_RUST_UNIT_GATE_EXPECTED_PASSED_V1},
    "python_producer_gate": {"passed": PRODUCERS_PYTHON_GATE_EXPECTED_PASSED_V1},
    "rust_producer_gate": {"passed": PRODUCERS_RUST_GATE_EXPECTED_PASSED_V1},
    "rust_admission_gate": {"passed": ADMISSION_RUST_GATE_EXPECTED_PASSED_V1},
    "python_allocation_projection_gate": {"passed": PROJECTION_GATE_EXPECTED_PASSED_V1},
    **{
        command_id: {"killed": expected, "mechanical": expected, "survived": 0, "errors": 0}
        for command_id, _packet, expected in LEDGER_GATED_PACKETS_V1
    },
}


def _comparable_value_ok(rule: object, value: object, esso: Mapping[str, Any]) -> bool:
    if rule == "hex64":
        return isinstance(value, str) and _HEX64_RE.fullmatch(value) is not None
    if rule == "semver":
        return isinstance(value, str) and _SEMVER_RE.fullmatch(value) is not None
    if rule == "hex40":
        return isinstance(value, str) and _HEX40_RE.fullmatch(value) is not None
    if rule == "host_triple":
        return isinstance(value, str) and _HOST_TRIPLE_RE.fullmatch(value) is not None
    if rule == "solvers":
        return value == dict(ESSO_SOLVERS_V1)
    if rule == "esso_ir_hash":
        return value == esso.get("ir_hash")
    if rule == "esso_fingerprint":
        return value == esso.get("fingerprint")
    certificate = esso.get("certificate_model")
    if rule == "esso_certificate_ir_hash":
        return isinstance(certificate, dict) and value == certificate.get("ir_hash")
    if rule == "esso_certificate_fingerprint":
        return isinstance(certificate, dict) and value == certificate.get("fingerprint")
    return type(value) is type(rule) and value == rule


def _validate_replay_run(run: object, index: int, esso: Mapping[str, Any]) -> dict[str, object]:
    where = f"proof_replay.author_record.runs[{index}]"
    if not isinstance(run, dict) or set(run) != AUTHOR_RUN_KEYS_V1:
        _reject("REPLAY_RECORD_SHAPE", where, "exactly command_id, exit_code, comparable")
    command_id = run.get("command_id")
    if command_id not in COMPARABLE_SCHEMA_V1:
        _reject("REPLAY_RECORD_SHAPE", where, str(command_id))
    exit_code = run.get("exit_code")
    if type(exit_code) is not int or exit_code != 0:
        _reject("REPLAY_RECORD_EXIT_NONZERO", where, str(exit_code))
    schema = COMPARABLE_SCHEMA_V1[str(command_id)]
    comparable = run.get("comparable")
    if not isinstance(comparable, dict) or set(comparable) != set(schema):
        _reject("REPLAY_RECORD_COMPARABLE_SHAPE", where, str(sorted(comparable) if isinstance(comparable, dict) else comparable))
    for key, rule in schema.items():
        if not _comparable_value_ok(rule, comparable[key], esso):
            _reject("REPLAY_RECORD_COMPARABLE_DRIFT", f"{where}.{key}", str(comparable[key])[:80])
    return {"command_id": command_id, "exit_code": exit_code, "comparable": dict(comparable)}


def _validate_toolchain(record: Mapping[str, Any]) -> dict[str, object]:
    toolchain = record.get("toolchain")
    where = "proof_replay.author_record.toolchain"
    if not isinstance(toolchain, dict) or set(toolchain) != AUTHOR_TOOLCHAIN_KEYS_V1:
        _reject("REPLAY_RECORD_SHAPE", where, "exactly esso_code_hash, lean, python, rust, rustc, solvers")
    expected = {"esso_code_hash": ESSO_CODE_COMMIT_V1, "lean": LEAN_VERSION_V1, "solvers": dict(ESSO_SOLVERS_V1)}
    for key, value in expected.items():
        if toolchain.get(key) != value:
            _reject("REPLAY_RECORD_TOOLCHAIN_DRIFT", f"{where}.{key}", str(toolchain.get(key))[:80])
    versions: dict[str, str] = {}
    for key in ("python", "rust"):
        reported = toolchain.get(key)
        if not isinstance(reported, str) or _SEMVER_RE.fullmatch(reported) is None:
            _reject("REPLAY_RECORD_TOOLCHAIN_DRIFT", f"{where}.{key}", str(reported)[:80])
        versions[key] = reported
    rustc = toolchain.get("rustc")
    if not isinstance(rustc, dict) or set(rustc) != RUSTC_TOOLCHAIN_KEYS_V1:
        _reject("REPLAY_RECORD_TOOLCHAIN_DRIFT", f"{where}.rustc", "exactly rustc_release, rustc_commit_hash, rustc_host")
    rustc_rules = COMPARABLE_SCHEMA_V1["rust_compiler_version"]
    for key, rule in rustc_rules.items():
        if not _comparable_value_ok(rule, rustc[key], {}):
            _reject("REPLAY_RECORD_TOOLCHAIN_DRIFT", f"{where}.rustc.{key}", str(rustc[key])[:80])
    return {
        "esso_code_hash": ESSO_CODE_COMMIT_V1,
        "lean": LEAN_VERSION_V1,
        "python": versions["python"],
        "rust": versions["rust"],
        "rustc": {key: str(rustc[key]) for key in sorted(RUSTC_TOOLCHAIN_KEYS_V1)},
        "solvers": dict(ESSO_SOLVERS_V1),
    }


def validate_author_replay_record_v1(record: object, esso: Mapping[str, Any]) -> dict[str, object]:
    """Validate a packet author's proof-replay observation record against the closed schema.

    Every comparable is typed and, where the packet already carries the value
    (ESSO ir_hash, fingerprint, solver and code versions, Lean version, gate counts,
    empty direct-check output), must equal it; the toolchain block is closed and
    exact. Only ``python`` and the two probe hashes are free, and fresh replay
    compares them.
    """

    if not isinstance(record, dict) or "status" not in record:
        _reject("REPLAY_RECORD_SHAPE", "proof_replay.author_record", "object with status required")
    status = record["status"]
    if status == REPLAY_STATUS_NOT_RUN_V1:
        if set(record) != {"status"}:
            _reject("REPLAY_RECORD_SHAPE", "proof_replay.author_record", "NOT_RUN carries no runs")
        return {"status": REPLAY_STATUS_NOT_RUN_V1}
    if status != "EXECUTED":
        _reject("REPLAY_RECORD_STATUS_INVALID", "proof_replay.author_record.status", str(status))
    runs = record.get("runs")
    if set(record) != {"status", "runs", "toolchain"} or not isinstance(runs, list):
        _reject("REPLAY_RECORD_SHAPE", "proof_replay.author_record", "EXECUTED needs runs and toolchain")
    validated = [_validate_replay_run(run, index, esso) for index, run in enumerate(runs)]
    if tuple(str(run["command_id"]) for run in validated) != REPLAY_COMMAND_IDS_V1:
        _reject("REPLAY_RECORD_SHAPE", "proof_replay.author_record.runs", "one run per command in order")
    toolchain = _validate_toolchain(record)
    bindings: tuple[tuple[str, str, str | None], ...] = (
        ("python", "python_version", "python_version"),
        ("rust", "rust_version", "cargo_version"),
        ("rustc", "rust_compiler_version", None),
    )
    for key, command_id, field_name in bindings:
        comparable = next(run["comparable"] for run in validated if run["command_id"] == command_id)
        observed: object = None
        if isinstance(comparable, dict):
            observed = comparable if field_name is None else comparable.get(field_name)
        if observed != toolchain[key]:
            _reject("REPLAY_RECORD_TOOLCHAIN_DRIFT", f"proof_replay.author_record.toolchain.{key}", f"differs from {command_id} run")
    return {"status": "EXECUTED", "runs": validated, "toolchain": toolchain}


def project_packet_v1(
    snapshot: SubjectSnapshotV1,
    *,
    created_date: str,
    author_replay_record: object,
) -> dict[str, Any]:
    """Return the only admissible packet content for the subject snapshot."""

    if _DATE_RE.fullmatch(created_date) is None:
        _reject("CREATED_DATE_INVALID", "created_date", created_date)
    for name, value in (("subject_commit", snapshot.subject_commit),
                        ("subject_parent", snapshot.subject_parent),
                        ("subject_tree", snapshot.subject_tree)):
        if _HEX40_RE.fullmatch(value) is None:
            _reject("SUBJECT_COMMIT_INVALID", name, value)
    # Source pins first: a missing pinned path is reported before any content-level finding.
    source_pins = _project_source_pins(snapshot)
    esso_evidence = _project_esso(snapshot)
    projection = {
        "schema": PACKET_SCHEMA_V15,
        "created_date": created_date,
        "subject_commit": snapshot.subject_commit,
        "subject_parent": snapshot.subject_parent,
        "subject_tree": snapshot.subject_tree,
        "packet_commit_parent": snapshot.subject_commit,
        "packet_write_set": [{"status": s, "path": p} for s, p in PACKET_WRITE_SET_V1],
        "claim_ceiling": dict(CLAIM_CEILING_V1),
        "completion_scope": list(COMPLETION_SCOPE_V1),
        "source_pins": source_pins,
        "esso_evidence": esso_evidence,
        "lean_evidence": _project_lean(snapshot),
        "v1_information_loss": _project_information_loss(snapshot),
        "lane_source_data": [
            {"lane_id": lane, "status": status, "missing": missing}
            for lane, status, missing in LANE_SOURCE_DATA_V1
        ],
        "required_sidecar": {**json.loads(json.dumps(REQUIRED_SIDECAR_V1)), "implementation": _project_certificate(snapshot)},
        "proof_replay": {
            "commands": [command.to_json() for command in REPLAY_COMMANDS_V1],
            "environment_policy": json.loads(json.dumps(REPLAY_ENV_POLICY_V1)),
            "author_record": validate_author_replay_record_v1(author_replay_record, esso_evidence),
            "admission_semantics": ADMISSION_SEMANTICS_V1,
        },
        "nonclaims": list(NONCLAIMS_V1),
    }
    # Pin-consistency checks run last so a structural finding in a source is
    # reported before the derived pin drift it also causes.
    _check_lean_gate(snapshot, tuple(name for _, name in THEOREM_INVENTORY_V1))
    _check_lean_gate(snapshot, tuple(name for _, name in CERTIFICATE_THEOREM_INVENTORY_V1), CERTIFICATE_LEAN_SUBJECT_V1)
    projection["hygiene_selection"] = _select_hygiene_packets(snapshot)
    return projection


# ---------------------------------------------------------------------------
# Admission checks
# ---------------------------------------------------------------------------


def _section(packet: Mapping[str, Any], key: str) -> Mapping[str, Any]:
    value = packet.get(key)
    if not isinstance(value, dict):
        _reject("PACKET_SECTION_SHAPE", key, "object required")
    return value


def check_claim_ceiling_v1(packet: Mapping[str, Any]) -> None:
    ceiling = _section(packet, "claim_ceiling")
    codes = {
        "formal_core_complete": "FORMAL_CORE_PROMOTION",
        "whole_value_movement_safe": "VALUE_MOVEMENT_PROMOTION",
        "value_movement_gates_closed": "VALUE_MOVEMENT_PROMOTION",
        "value_movement_gates_total": "VALUE_MOVEMENT_PROMOTION",
    }
    for key, expected in CLAIM_CEILING_V1.items():
        actual = ceiling.get(key)
        if type(actual) is type(expected) and actual == expected:
            continue
        default = "AUTHORITY_PROMOTION" if key in AUTHORITY_FIELDS_V1 else "CLAIM_STATUS_DRIFT"
        _reject(codes.get(key, default), f"claim_ceiling.{key}", str(actual))
    if set(ceiling) != set(CLAIM_CEILING_V1):
        _reject("CLAIM_STATUS_DRIFT", "claim_ceiling", "unexpected keys")


def check_subject_binding_v1(packet: Mapping[str, Any], snapshot: SubjectSnapshotV1) -> None:
    if packet.get("subject_commit") != snapshot.subject_commit:
        _reject("SUBJECT_COMMIT_DRIFT", "subject_commit", str(packet.get("subject_commit")))
    if packet.get("subject_parent") != snapshot.subject_parent:
        _reject("SUBJECT_PARENT_DRIFT", "subject_parent", str(packet.get("subject_parent")))
    if packet.get("subject_tree") != snapshot.subject_tree:
        _reject("SUBJECT_TREE_DRIFT", "subject_tree", str(packet.get("subject_tree")))
    if packet.get("packet_commit_parent") != snapshot.subject_commit:
        _reject("PACKET_PARENT_DECLARATION_DRIFT", "packet_commit_parent", "must equal subject_commit")


def check_packet_topology_v1(packet: Mapping[str, Any], topology: PacketTopologyV1) -> None:
    if topology.packet_parents != (str(packet.get("subject_commit")),):
        _reject("PACKET_PARENT_NOT_SUBJECT", topology.packet_commit, str(topology.packet_parents))
    declared = tuple(
        (str(row.get("status")), str(row.get("path")))
        for row in packet.get("packet_write_set", ())
        if isinstance(row, dict)
    )
    if declared != PACKET_WRITE_SET_V1:
        _reject("PACKET_WRITE_SET_DECLARATION_DRIFT", "packet_write_set", str(declared))
    if tuple(sorted(topology.write_set)) != tuple(sorted(PACKET_WRITE_SET_V1)):
        _reject("PACKET_ENVELOPE_DRIFT", topology.packet_commit, str(topology.write_set))
    if not topology.packet_in_head_history:
        _reject("PACKET_NOT_IN_HEAD_HISTORY", topology.packet_commit, topology.head_commit)


def _pin_rows(packet: Mapping[str, Any]) -> list[Mapping[str, Any]]:
    rows = packet.get("source_pins")
    if not isinstance(rows, list) or not all(isinstance(row, dict) for row in rows):
        _reject("SOURCE_PIN_SHAPE", "source_pins", "list of objects required")
    for index, row in enumerate(rows):
        if set(row) != {"path", "role", "mode", "git_blob", "sha256", "size"}:
            _reject("SOURCE_PIN_SHAPE", f"source_pins[{index}]", "closed row keys required")
    return rows


def _check_pin_row(index: int, row: Mapping[str, Any], snapshot: SubjectSnapshotV1) -> None:
    pointer = f"source_pins[{index}]"
    path, role = SOURCE_PIN_ROLES_V1[index]
    if row["path"] != path:
        _reject("SOURCE_PIN_SET_DRIFT", pointer, f"{row['path']} != {path}")
    if row["role"] != role:
        _reject("SOURCE_PIN_ROLE_DRIFT", pointer, str(row["role"]))
    blob = _blob(snapshot, path)
    if row["mode"] != blob.mode or blob.mode != GIT_BLOB_MODE_V1:
        _reject("SOURCE_PIN_MODE_DRIFT", pointer, str(row["mode"]))
    if row["git_blob"] != blob.git_blob:
        _reject("SOURCE_PIN_BLOB_DRIFT", pointer, str(row["git_blob"]))
    if row["sha256"] != blob.sha256:
        _reject("SOURCE_PIN_SHA256_DRIFT", pointer, str(row["sha256"]))
    if row["size"] != blob.size:
        _reject("SOURCE_PIN_SIZE_DRIFT", pointer, str(row["size"]))


def check_source_pins_v1(packet: Mapping[str, Any], snapshot: SubjectSnapshotV1) -> None:
    rows = _pin_rows(packet)
    for index, row in enumerate(rows):
        if index >= len(SOURCE_PIN_ROLES_V1):
            _reject("SOURCE_PIN_SET_DRIFT", f"source_pins[{index}]", "extra pin")
        _safe_repo_path(str(row["path"]), f"source_pins[{index}].path")
        _check_pin_row(index, row, snapshot)
    if len(rows) != len(SOURCE_PIN_ROLES_V1):
        _reject("SOURCE_PIN_SET_DRIFT", "source_pins", f"{len(rows)} != {len(SOURCE_PIN_ROLES_V1)}")


def _safe_repo_path(path: str, pointer: str) -> None:
    parts = path.split("/")
    if not path or path.startswith("/") or "\\" in path or "." in parts or ".." in parts:
        _reject("SOURCE_PIN_PATH_UNSAFE", pointer, path)


def check_executing_tools_v1(snapshot: SubjectSnapshotV1, executing: ExecutingToolsV1) -> None:
    labels = {
        CHECKER_PATH_V1: "EXECUTING_CHECKER_DRIFT",
        CORE_PATH_V1: "EXECUTING_CORE_DRIFT",
        SHELL_PATH_V1: "EXECUTING_SHELL_DRIFT",
        SCANNER_PATH_V1: "EXECUTING_SCANNER_DRIFT",
    }
    for path in EXECUTING_TOOL_PATHS_V1:
        if executing.sha256_by_path.get(path) != _blob(snapshot, path).sha256:
            _reject(labels[path], path, "executing tool differs from the subject blob")


def check_lane_map_v1(packet: Mapping[str, Any]) -> None:
    rows = packet.get("lane_source_data")
    if not isinstance(rows, list) or not all(isinstance(row, dict) for row in rows):
        _reject("LANE_ROW_SHAPE", "lane_source_data", "list of objects required")
    for index, row in enumerate(rows):
        if set(row) != {"lane_id", "status", "missing"}:
            _reject("LANE_ROW_SHAPE", f"lane_source_data[{index}]", "closed row keys required")
        if row["status"] not in LANE_STATUS_VOCABULARY_V1:
            _reject("LANE_STATUS_NOT_IN_VOCABULARY", f"lane_source_data[{index}].status", str(row["status"]))
    actual = tuple((r["lane_id"], r["status"], r["missing"]) for r in rows)
    if actual != LANE_SOURCE_DATA_V1:
        _reject("LANE_MAP_DRIFT", "lane_source_data", "differs from the closed twelve-lane map")


SIDECAR_IMPLEMENTATION_KEYS_V1: Final[frozenset[str]] = frozenset(
    {
        "status",
        "python",
        "rust",
        "check_order",
        "reject_codes",
        "producer_registry",
        "receipt_backed_producers",
        "receipt_backed_producer_implementations",
        "golden",
        "registered_empty_producers",
        "lean_model",
        "esso_model",
        "mounted",
    }
)


def check_sidecar_v1(packet: Mapping[str, Any]) -> None:
    sidecar = _section(packet, "required_sidecar")
    expected = json.loads(json.dumps(REQUIRED_SIDECAR_V1))
    for key, value in expected.items():
        if sidecar.get(key) != value:
            _reject("SIDECAR_DRIFT", f"required_sidecar.{key}", str(sidecar.get(key))[:80])
    if set(sidecar) != set(expected) | {"implementation"}:
        _reject("SIDECAR_DRIFT", "required_sidecar", "unexpected keys")
    implementation = sidecar.get("implementation")
    if not isinstance(implementation, dict) or set(implementation) != SIDECAR_IMPLEMENTATION_KEYS_V1:
        _reject("SIDECAR_DRIFT", "required_sidecar.implementation", "closed implementation keys required")
    fixed: dict[str, object] = {
        "status": CERTIFICATE_IMPLEMENTATION_STATUS_V1,
        "python": CERTIFICATE_PYTHON_PATH_V1,
        "rust": CERTIFICATE_RUST_PATH_V1,
        "check_order": list(CERTIFICATE_CHECK_ORDER_V1),
        "reject_codes": list(CERTIFICATE_REJECT_CODES_V1),
        "producer_registry": dict(CERTIFICATE_PRODUCER_KINDS_V1),
        "receipt_backed_producers": 1,
        "receipt_backed_producer_implementations": {
            "asset_transfer": {
                "python": PRODUCERS_PYTHON_PATH_V1,
                "rust": PRODUCERS_RUST_PATH_V1,
                "binding": "produce_asset_transfer_fragment_v1 folds one accepted asset-transfer transition into a fragment whose binding_root is the journal receipt root, refusing lane, disabled-lane, release, post-root, carry-forward (prior lane, prior release, pre root), terminal-root, non-canonical-entitlement, fold-ceiling, and coverage drift with eleven closed codes (accepted-validation, lane, disabled-lane, release, post-root, carry-forward incl. prior kind and enabled flag, terminal-root, non-canonical-or-over-ceiling entitlements, fold-ceiling, coverage, and defensive fragment-validation); only the receipt root carries custody rows and chain/epoch context (the committed lane root carries none of it), so fragment integrity rests on C9 receipt admission; until then the certificate registry keeps ASSET_TRANSFER at NO_PRODUCER, no acceptance path uses this producer, and the registry count above stays 0",
            }
        },
        "lean_model": CERTIFICATE_LEAN_PATH_V1,
        "esso_model": CERTIFICATE_ESSO_MODEL_PATH_V1,
        "mounted": False,
    }
    for key, value in fixed.items():
        if implementation.get(key) != value or type(implementation.get(key)) is not type(value):
            _reject("SIDECAR_DRIFT", f"required_sidecar.implementation.{key}", str(implementation.get(key))[:80])
    golden = implementation.get("golden")
    if not isinstance(golden, dict) or golden.get("vectors") != CERTIFICATE_FIXTURE_VECTORS_V1 or golden.get("fixture") != CERTIFICATE_FIXTURE_PATH_V1:
        _reject("SIDECAR_DRIFT", "required_sidecar.implementation.golden", str(golden)[:80])
    producers = implementation.get("registered_empty_producers")
    if not isinstance(producers, dict) or producers.get("lanes") != dict(CERTIFICATE_REGISTERED_EMPTY_ROOTS_V1):
        _reject("SIDECAR_DRIFT", "required_sidecar.implementation.registered_empty_producers", str(producers)[:80])


def _string_scalars(value: object, pointer: str) -> list[tuple[str, str]]:
    if isinstance(value, str):
        return [(pointer, value)]
    if isinstance(value, list):
        return [p for i, v in enumerate(value) for p in _string_scalars(v, f"{pointer}[{i}]")]
    if isinstance(value, dict):
        return [p for k, v in value.items() for p in _string_scalars(v, f"{pointer}.{k}")]
    return []


def check_nonclaims_v1(packet: Mapping[str, Any]) -> None:
    nonclaims = packet.get("nonclaims")
    if not isinstance(nonclaims, list) or tuple(nonclaims) != NONCLAIMS_V1:
        _reject("NONCLAIM_DRIFT", "nonclaims", "differs from the closed ordered nonclaim list")
    scalars = [
        (pointer, text)
        for key, value in packet.items()
        if key != "nonclaims"
        for pointer, text in _string_scalars(value, key)
    ]
    for pointer, text in scalars:
        folded = " ".join(unicodedata.normalize("NFKC", text).split()).lower()
        hits = [token for token in FORBIDDEN_PROMOTION_TOKENS_V1 if token in folded]
        if hits:
            _reject("PROMOTION_TOKEN_PRESENT", pointer, hits[0])


def check_replay_declaration_v1(packet: Mapping[str, Any]) -> None:
    replay = _section(packet, "proof_replay")
    commands = replay.get("commands")
    if commands != [command.to_json() for command in REPLAY_COMMANDS_V1]:
        _reject("REPLAY_COMMANDS_DRIFT", "proof_replay.commands", "differs from the closed command list")
    if replay.get("admission_semantics") != ADMISSION_SEMANTICS_V1:
        _reject("REPLAY_SEMANTICS_DRIFT", "proof_replay.admission_semantics", "drift")
    validate_author_replay_record_v1(replay.get("author_record"), _section(packet, "esso_evidence"))


def check_projection_v1(packet: Mapping[str, Any], expected: Mapping[str, Any]) -> None:
    if canonical_packet_bytes_v1(dict(packet)) != canonical_packet_bytes_v1(dict(expected)):
        for key in sorted(PACKET_KEYS_V3):
            if packet.get(key) != expected.get(key):
                _reject("PACKET_PROJECTION_DRIFT", key, "differs from the projection of the subject")
        _reject("PACKET_PROJECTION_DRIFT", "$", "differs from the projection of the subject")


def check_markdown_projection_v1(packet: Mapping[str, Any], topology: PacketTopologyV1) -> None:
    if topology.markdown_blob_at_p != render_markdown_v1(packet).encode("utf-8"):
        _reject("MARKDOWN_PROJECTION_DRIFT", PACKET_MD_PATH_V1, "committed markdown is not the rendering")


def check_current_applicability_v1(
    snapshot: SubjectSnapshotV1, topology: PacketTopologyV1, current: CurrentSourceStateV1
) -> tuple[str, ...]:
    """Return the drifted paths; raise for packet drift at HEAD or in the worktree."""

    if topology.packet_blob_at_head != topology.packet_blob_at_p:
        _reject("CURRENT_PACKET_DRIFT", PACKET_JSON_PATH_V1, "HEAD packet differs from P")
    if topology.markdown_blob_at_head != topology.markdown_blob_at_p:
        _reject("CURRENT_PACKET_DRIFT", PACKET_MD_PATH_V1, "HEAD markdown differs from P")
    if topology.worktree_packet != topology.packet_blob_at_p:
        _reject("WORKTREE_PACKET_DRIFT", PACKET_JSON_PATH_V1, "worktree packet differs from P")
    if topology.worktree_markdown != topology.markdown_blob_at_p:
        _reject("WORKTREE_PACKET_DRIFT", PACKET_MD_PATH_V1, "worktree markdown differs from P")
    drift: list[str] = []
    pinned: dict[str, SourceBlobV1] = {path: _blob(snapshot, path) for path in SOURCE_PIN_PATHS_V1}
    for row in _select_hygiene_packets(snapshot):
        packet_path = str(row["packet_path"])
        pinned.setdefault(packet_path, snapshot.hygiene_packets[packet_path])
    for path, blob in pinned.items():
        if current.head_blob_ids.get(path) != blob.git_blob:
            drift.append(path)
        elif current.worktree_sha256.get(path) != blob.sha256:
            drift.append(path)
    drift.extend(path for path in current.forbidden_paths_present if path not in drift)
    return tuple(drift)


def applicability_paths_v1(packet: Mapping[str, Any]) -> tuple[str, ...]:
    """Paths whose HEAD and worktree state decide applicability: source pins plus selected packets."""

    paths = list(SOURCE_PIN_PATHS_V1)
    selection = packet.get("hygiene_selection")
    for row in selection if isinstance(selection, list) else ():
        packet_path = row.get("packet_path") if isinstance(row, dict) else None
        if isinstance(packet_path, str) and packet_path not in paths and ".." not in packet_path:
            paths.append(packet_path)
    return tuple(paths)


def _run_check(errors: list[AdmissionErrorV1], check: Callable[[], object]) -> object | None:
    try:
        return check()
    except AdmissionRejectV1 as exc:
        errors.append(AdmissionErrorV1(exc.code, exc.path, exc.detail))
        return None


@dataclass(frozen=True, slots=True)
class AdmissionOutcomeV1:
    errors: tuple[AdmissionErrorV1, ...]
    current_source_drift: tuple[str, ...]

    @property
    def packet_admitted(self) -> bool:
        return not self.errors

    @property
    def current_applicable(self) -> bool:
        return self.packet_admitted and not self.current_source_drift


@dataclass(frozen=True, slots=True)
class AdmissionContextV1:
    """Every shell observation the admission decision depends on."""

    snapshot: SubjectSnapshotV1
    topology: PacketTopologyV1
    current: CurrentSourceStateV1
    executing: ExecutingToolsV1


def admit_packet_v1(packet: Mapping[str, Any], context: AdmissionContextV1) -> AdmissionOutcomeV1:
    """Run every admission section in fixed order; collect one finding per section."""

    snapshot, topology = context.snapshot, context.topology
    errors: list[AdmissionErrorV1] = []
    _run_check(errors, lambda: check_claim_ceiling_v1(packet))
    _run_check(errors, lambda: check_subject_binding_v1(packet, snapshot))
    _run_check(errors, lambda: check_packet_topology_v1(packet, topology))
    _run_check(errors, lambda: check_source_pins_v1(packet, snapshot))
    _run_check(errors, lambda: check_executing_tools_v1(snapshot, context.executing))
    _run_check(errors, lambda: check_lane_map_v1(packet))
    _run_check(errors, lambda: check_sidecar_v1(packet))
    _run_check(errors, lambda: check_replay_declaration_v1(packet))
    _run_check(errors, lambda: check_nonclaims_v1(packet))
    expected = _run_check(errors, lambda: _expected_projection(packet, snapshot))
    if isinstance(expected, dict):
        _run_check(errors, lambda: check_projection_v1(packet, expected))
    _run_check(errors, lambda: check_markdown_projection_v1(packet, topology))
    drift = _run_check(
        errors, lambda: check_current_applicability_v1(snapshot, topology, context.current)
    )
    current_drift = tuple(drift) if isinstance(drift, tuple) else ()
    return AdmissionOutcomeV1(errors=tuple(errors), current_source_drift=current_drift)


def _expected_projection(packet: Mapping[str, Any], snapshot: SubjectSnapshotV1) -> dict[str, Any]:
    replay = packet.get("proof_replay")
    record = replay.get("author_record") if isinstance(replay, dict) else None
    return project_packet_v1(
        snapshot,
        created_date=str(packet.get("created_date", "")),
        author_replay_record=record,
    )


# ---------------------------------------------------------------------------
# Proof replay evaluation
# ---------------------------------------------------------------------------


def parse_pytest_summary_v1(stdout: bytes) -> int | None:
    lines = [line for line in stdout.decode("utf-8", "replace").splitlines() if line.strip()]
    if not lines:
        return None
    last = lines[-1]
    if "failed" in last or "error" in last:
        return None
    match = _PYTEST_SUMMARY_RE.search(last)
    return int(match.group(1)) if match else None


def parse_esso_json_v1(stdout: bytes, stderr: bytes) -> dict[str, Any] | None:
    raw = stdout if stdout.strip() else stderr
    try:
        value = json.loads(raw.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError):
        return None
    return value if isinstance(value, dict) else None


def parse_lean_version_v1(stdout: bytes) -> str | None:
    match = _LEAN_VERSION_RE.search(stdout.decode("utf-8", "replace"))
    return match.group(1) if match else None


def parse_print_axioms_v1(stdout: bytes) -> dict[str, frozenset[str]]:
    result: dict[str, frozenset[str]] = {}
    for match in _PRINT_AXIOMS_RE.finditer(stdout.decode("utf-8", "replace")):
        axioms = match.group(2) or ""
        result[match.group(1)] = frozenset(a.strip() for a in axioms.split(",") if a.strip())
    return result


def _grade_lean(obs: ReplayObservationV1, packet: Mapping[str, Any]) -> dict[str, object]:
    if obs.command_id == "lean_version":
        version = parse_lean_version_v1(obs.stdout)
        if version != LEAN_TOOLCHAIN_V1.rsplit("v", 1)[1]:
            _reject("REPLAY_LEAN_VERSION_DRIFT", obs.command_id, str(version))
        return {"lean_version": version}
    if obs.command_id in {subject.direct_check_command for subject in LEAN_SUBJECTS_V1}:
        if obs.stdout.strip() or obs.stderr.strip():
            _reject("REPLAY_LEAN_OUTPUT_NONEMPTY", obs.command_id, "direct check produced output")
        return {"stdout_sha256": sha256_hex_v1(obs.stdout)}
    subject = next((s for s in LEAN_SUBJECTS_V1 if s.axioms_probe_command == obs.command_id), None)
    if subject is None:
        _reject("REPLAY_RECORD_SHAPE", obs.command_id, "unknown lean command")
    axioms = parse_print_axioms_v1(obs.stdout)
    namespace = ".".join(subject.namespace)
    for _, name in subject.inventory:
        found = axioms.get(f"{namespace}.{name}")
        if found is None or not found <= ALLOWED_LEAN_AXIOMS_V1 or "sorryAx" in obs.stdout.decode():
            _reject("REPLAY_AXIOM_DRIFT", obs.command_id, name)
    return {"probe_sha256": obs.probe_sha256, "theorems_probed": len(axioms)}


def parse_cargo_test_summary_v1(stdout: bytes) -> int | None:
    """Return the passed count of exactly one all-green cargo test summary line, else None."""

    found = _CARGO_SUMMARY_RE.findall(stdout.decode("utf-8", errors="replace"))
    if len(found) != 1 or found[0][0] != "ok" or found[0][2] != "0":
        return None
    return int(found[0][1])


def parse_python_version_v1(stdout: bytes) -> str | None:
    text = stdout.decode("utf-8", errors="replace").strip()
    return text if _SEMVER_RE.fullmatch(text) else None


def _grade_cargo(obs: ReplayObservationV1, expected: int) -> dict[str, object]:
    passed = parse_cargo_test_summary_v1(obs.stdout)
    if passed is None:
        _reject("REPLAY_CARGO_SUMMARY_UNPARSEABLE", obs.command_id, "no single all-green summary")
    if passed != expected:
        _reject("REPLAY_PASSED_COUNT_DRIFT", obs.command_id, f"{passed} != {expected}")
    return {"passed": passed}


def parse_cargo_version_v1(stdout: bytes) -> str | None:
    match = _CARGO_VERSION_RE.match(stdout.decode("utf-8", errors="replace").strip())
    return match.group(1) if match else None


def _grade_rust_version(obs: ReplayObservationV1) -> dict[str, object]:
    version = parse_cargo_version_v1(obs.stdout)
    if version is None:
        _reject("REPLAY_RUST_VERSION_UNPARSEABLE", obs.command_id, obs.stdout[:40].decode("utf-8", "replace"))
    return {"cargo_version": version}


def parse_rustc_vv_v1(stdout: bytes) -> dict[str, str] | None:
    """Return the release, commit hash, and host triple from ``rustc -vV`` output."""

    fields = dict(_RUSTC_FIELD_RE.findall(stdout.decode("utf-8", errors="replace")))
    release, commit, host = fields.get("release"), fields.get("commit-hash"), fields.get("host")
    if release is None or commit is None or host is None:
        return None
    if _SEMVER_RE.fullmatch(release) is None or _HEX40_RE.fullmatch(commit) is None or _HOST_TRIPLE_RE.fullmatch(host) is None:
        return None
    return {"rustc_release": release, "rustc_commit_hash": commit, "rustc_host": host}


def _grade_rustc_version(obs: ReplayObservationV1) -> dict[str, object]:
    parsed = parse_rustc_vv_v1(obs.stdout)
    if parsed is None:
        _reject("REPLAY_RUSTC_VERSION_UNPARSEABLE", obs.command_id, obs.stdout[:60].decode("utf-8", "replace"))
    return dict(parsed)


def _grade_python_version(obs: ReplayObservationV1) -> dict[str, object]:
    version = parse_python_version_v1(obs.stdout)
    if version is None:
        _reject("REPLAY_PYTHON_VERSION_UNPARSEABLE", obs.command_id, obs.stdout[:40].decode("utf-8", "replace"))
    return {"python_version": version}


def _grade_ledger(obs: ReplayObservationV1, expected_killed: int) -> dict[str, object]:
    """Every mechanical row of the packet killed, none survived, none errored.

    Both P40 reviews attacked this grader and both got through, in three ways it now
    refuses: a digest field that is not a digest (any non-empty string passed), one
    mutation reported N times to reach the expected count, and a mutated path that is not
    a portable repository-relative path.

    What it does NOT check, and cannot from here: that the mutated path is one the THV1
    packet pins. That binding is the packet validator's ("mutant path is not a pinned
    source path"), enforced by tools/check_test_hygiene_v1.py, which this checker does not
    run -- nonclaim 14. A first version of this guard required the path to be pinned by the
    FORMAL-CYCLE packet instead, which is a different set: it refused a real row that
    mutates a tool only the THV1 packet pins. Nor can it check that a row's English
    description describes the mutation that ran; that is semantic.
    """

    try:
        report = json.loads(obs.stdout.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError):
        _reject("REPLAY_LEDGER_REPORT_UNPARSEABLE", obs.command_id, "stdout is not one JSON object")
    if not isinstance(report, dict):
        _reject("REPLAY_LEDGER_REPORT_UNPARSEABLE", obs.command_id, "stdout is not one JSON object")
    killed = report.get("killed")
    survived = report.get("survived")
    errors = report.get("errors")
    mechanical = report.get("mechanical")
    for name, value in (("killed", killed), ("survived", survived), ("errors", errors), ("mechanical", mechanical)):
        if type(value) is not int:
            _reject("REPLAY_LEDGER_REPORT_UNPARSEABLE", obs.command_id, f"{name} is not an integer")
    if survived or errors:
        _reject("REPLAY_LEDGER_ROW_NOT_KILLED", obs.command_id, f"survived {survived} errors {errors}")
    if killed != expected_killed or mechanical != expected_killed:
        _reject(
            "REPLAY_LEDGER_KILLED_COUNT_DRIFT",
            obs.command_id,
            f"killed {killed} mechanical {mechanical} != {expected_killed}",
        )
    rows = report.get("rows")
    if not isinstance(rows, list):
        _reject("REPLAY_LEDGER_REPORT_UNPARSEABLE", obs.command_id, "rows is not a list")
    # Opus P39 P3: the totals alone said nothing about what ran. Every mechanical row must
    # name the mutation that produced its verdict, so a KILLED row can be tied to the row
    # declaring it rather than to some other edit of the same file.
    described = 0
    seen: set[tuple[str, str, str]] = set()
    for row in rows:
        if not isinstance(row, dict) or row.get("verdict") != "KILLED":
            continue
        mutation = row.get("mutation")
        if not isinstance(mutation, dict) or not all(
            type(mutation.get(field)) is str and mutation.get(field)
            for field in ("path", "needle_sha256", "replacement_sha256")
        ):
            _reject("REPLAY_LEDGER_ROW_WITHOUT_MUTATION", obs.command_id, str(row.get("description"))[:60])
        if mutation["needle_sha256"] == mutation["replacement_sha256"]:
            _reject("REPLAY_LEDGER_ROW_WITHOUT_MUTATION", obs.command_id, "needle equals replacement")
        for digest_field in ("needle_sha256", "replacement_sha256"):
            if _SHA256_HEX_RE_V1.fullmatch(mutation[digest_field]) is None:
                _reject(
                    "REPLAY_LEDGER_ROW_WITHOUT_MUTATION", obs.command_id, f"{digest_field} is not a sha256"
                )
        if not _portable_repo_path_v1(mutation["path"]):
            _reject("REPLAY_LEDGER_ROW_PATH_UNPORTABLE", obs.command_id, mutation["path"][:60])
        identity = (mutation["path"], mutation["needle_sha256"], mutation["replacement_sha256"])
        if identity in seen:
            _reject("REPLAY_LEDGER_ROW_NOT_DISTINCT", obs.command_id, mutation["path"][:60])
        seen.add(identity)
        described += 1
    if described != killed:
        _reject("REPLAY_LEDGER_ROW_WITHOUT_MUTATION", obs.command_id, f"{described} described of {killed} killed")
    return {"killed": killed, "mechanical": mechanical, "survived": survived, "errors": errors}


def _grade_pytest(obs: ReplayObservationV1, expected: int) -> dict[str, object]:
    passed = parse_pytest_summary_v1(obs.stdout)
    if passed is None:
        _reject("REPLAY_PYTEST_SUMMARY_UNPARSEABLE", obs.command_id, "no passed summary")
    if passed != expected:
        _reject("REPLAY_PASSED_COUNT_DRIFT", obs.command_id, f"{passed} != {expected}")
    return {"passed": passed}


def _esso_subject_for(command_id: str) -> EssoSubjectV1:
    for subject in ESSO_SUBJECTS_V1:
        if command_id in (subject.validate_command, subject.verify_command):
            return subject
    _reject("REPLAY_RECORD_SHAPE", command_id, "unknown esso command")


def _grade_esso(obs: ReplayObservationV1, evidence: Mapping[str, Any]) -> dict[str, object]:
    subject = _esso_subject_for(obs.command_id)
    nested = evidence.get(subject.evidence_key) if subject.evidence_key else evidence
    esso: Mapping[str, Any] = nested if isinstance(nested, Mapping) else {}
    payload = parse_esso_json_v1(obs.stdout, obs.stderr)
    if payload is None:
        _reject("REPLAY_ESSO_OUTPUT_UNPARSEABLE", obs.command_id, "no JSON payload")
    if obs.command_id == subject.validate_command:
        if payload.get("ir_hash") != esso.get("ir_hash"):
            _reject("REPLAY_ESSO_IR_HASH_DRIFT", obs.command_id, str(payload.get("ir_hash")))
        return {"ir_hash": payload.get("ir_hash")}
    report_raw = payload.get("report")
    report: dict[str, Any] = report_raw if isinstance(report_raw, dict) else {}
    versions_raw = report.get("tool_versions")
    versions: dict[str, Any] = versions_raw if isinstance(versions_raw, dict) else {}
    fingerprints = payload.get("fingerprints")
    if not (payload.get("ok") is True and payload.get("determinism") is True):
        _reject("REPLAY_ESSO_VERDICT", obs.command_id, "ok/determinism false")
    verified = report.get("verdict") == "VERIFIED" and report.get("solvers_agreed") is True
    if not verified or report.get("failed_queries") != 0 or report.get("inconclusive_queries") != 0:
        _reject("REPLAY_ESSO_VERDICT", obs.command_id, str(report.get("verdict")))
    expected_queries = len(subject.queries)
    queries_raw = payload.get("queries")
    query_ids = set(queries_raw) if isinstance(queries_raw, dict) else set()
    if report.get("total_queries") != expected_queries or report.get("passed_queries") != expected_queries:
        _reject("REPLAY_ESSO_QUERY_COUNT_DRIFT", obs.command_id, f"{report.get('total_queries')}/{report.get('passed_queries')}")
    if query_ids != set(subject.queries):
        _reject("REPLAY_ESSO_QUERY_SET_DRIFT", obs.command_id, ",".join(sorted(query_ids)))
    if versions.get("esso_code_hash") != esso.get("esso_code_commit"):
        _reject("REPLAY_ESSO_CODE_COMMIT_DRIFT", obs.command_id, str(versions.get("esso_code_hash")))
    solvers = _solver_versions(versions.get("solvers"), esso.get("solvers"))
    if solvers is None:
        _reject("REPLAY_SOLVER_VERSION_DRIFT", obs.command_id, str(versions.get("solvers")))
    if not isinstance(fingerprints, list) or len(set(fingerprints)) != 1:
        _reject("REPLAY_FINGERPRINT_NONDETERMINISTIC", obs.command_id, str(fingerprints))
    if fingerprints[0] != esso.get("fingerprint"):
        _reject("REPLAY_FINGERPRINT_DRIFT", obs.command_id, str(fingerprints[0]))
    return {
        "verdict": "VERIFIED",
        "fingerprint": fingerprints[0],
        "solvers": solvers,
        "esso_code_hash": versions.get("esso_code_hash"),
    }


def _solver_versions(reported: object, expected: object) -> dict[str, str] | None:
    """Return the expected solver versions when each appears in the reported banner."""

    if not isinstance(reported, dict) or not isinstance(expected, dict):
        return None
    if set(reported) != set(expected):
        return None
    for solver, version in expected.items():
        banner = str(reported.get(solver, ""))
        if str(version) not in banner.split():
            return None
    return {str(solver): str(version) for solver, version in expected.items()}


def _grade_observation(obs: ReplayObservationV1, packet: Mapping[str, Any]) -> dict[str, object]:
    if obs.timed_out or obs.exit_code != 0:
        _reject("REPLAY_EXIT_CODE", obs.command_id, f"exit {obs.exit_code} timed_out={obs.timed_out}")
    esso = _section(packet, "esso_evidence")
    if obs.command_id.startswith("lean_") and not obs.command_id.endswith("binding_gate"):
        return _grade_lean(obs, packet)
    for subject in LEAN_SUBJECTS_V1:
        if obs.command_id == subject.binding_gate_command:
            return _grade_pytest(obs, subject.gate_expected_passed)
    if obs.command_id == "esso_gate":
        return _grade_pytest(obs, ESSO_GATE_EXPECTED_PASSED_V1)
    if obs.command_id == "esso_certificate_gate":
        return _grade_pytest(obs, CERTIFICATE_ESSO_GATE_EXPECTED_PASSED_V1)
    if obs.command_id == "prior_restage_gate":
        return _grade_pytest(obs, PRIOR_ESSO_GATE_EXPECTED_PASSED_V1)
    if obs.command_id == "transfer_refinement_gate":
        return _grade_pytest(obs, TRANSFER_REFINEMENT_GATE_EXPECTED_PASSED_V1)
    if obs.command_id == "python_rust_bound_parity_gate":
        return _grade_pytest(obs, PARITY_GATE_EXPECTED_PASSED_V1)
    if obs.command_id == "python_version":
        return _grade_python_version(obs)
    if obs.command_id == "python_projection_gate":
        return _grade_pytest(obs, PYTHON_GATE_EXPECTED_PASSED_V1)
    if obs.command_id == "rust_projection_gate":
        return _grade_cargo(obs, RUST_GATE_EXPECTED_PASSED_V1)
    if obs.command_id == "rust_version":
        return _grade_rust_version(obs)
    if obs.command_id == "rust_compiler_version":
        return _grade_rustc_version(obs)
    if obs.command_id == "rust_refinement_gate":
        return _grade_cargo(obs, RUST_REFINEMENT_GATE_EXPECTED_PASSED_V1)
    if obs.command_id == "rust_golden_gate":
        return _grade_cargo(obs, RUST_GOLDEN_GATE_EXPECTED_PASSED_V1)
    if obs.command_id == "rust_bounded_vec_unit_gate":
        return _grade_cargo(obs, RUST_BOUNDED_VEC_UNIT_GATE_EXPECTED_PASSED_V1)
    if obs.command_id == "python_certificate_golden_gate":
        return _grade_pytest(obs, CERTIFICATE_PYTHON_GATE_EXPECTED_PASSED_V1)
    if obs.command_id == "rust_certificate_golden_gate":
        return _grade_cargo(obs, CERTIFICATE_RUST_GATE_EXPECTED_PASSED_V1)
    if obs.command_id == "rust_certificate_unit_gate":
        return _grade_cargo(obs, CERTIFICATE_RUST_UNIT_GATE_EXPECTED_PASSED_V1)
    if obs.command_id == "python_producer_gate":
        return _grade_pytest(obs, PRODUCERS_PYTHON_GATE_EXPECTED_PASSED_V1)
    if obs.command_id == "rust_producer_gate":
        return _grade_cargo(obs, PRODUCERS_RUST_GATE_EXPECTED_PASSED_V1)
    if obs.command_id == "rust_admission_gate":
        return _grade_cargo(obs, ADMISSION_RUST_GATE_EXPECTED_PASSED_V1)
    if obs.command_id == "python_allocation_projection_gate":
        return _grade_pytest(obs, PROJECTION_GATE_EXPECTED_PASSED_V1)
    for command_id, _packet, expected_killed in LEDGER_GATED_PACKETS_V1:
        if obs.command_id == command_id:
            return _grade_ledger(obs, expected_killed)
    if obs.command_id == "python_golden_gate":
        return _grade_pytest(obs, PYTHON_GOLDEN_GATE_EXPECTED_PASSED_V1)
    return _grade_esso(obs, esso)


def replay_expected_sha_by_path_v1(packet: dict[str, object]) -> dict[str, str]:
    """The packet's expected worktree sha for every applicability path: source pins plus selected hygiene packets."""

    expected: dict[str, str] = {}
    rows = packet.get("source_pins")
    if isinstance(rows, list):
        for row in rows:
            if isinstance(row, dict):
                expected[str(row.get("path"))] = str(row.get("sha256"))
    selection = packet.get("hygiene_selection")
    if isinstance(selection, list):
        for row in selection:
            if isinstance(row, dict):
                expected[str(row.get("packet_path"))] = str(row.get("packet_sha256"))
    return expected


def replay_worktree_mutation_errors_v1(
    packet: dict[str, object], current_sha_by_path: dict[str, str | None]
) -> tuple[AdmissionErrorV1, ...]:
    """Errors for every applicability path whose worktree bytes changed during replay.

    Opus P15 P1-1 escalation: replay command #2 can execute IO, so the worktree must be
    re-verified against the packet's own pins (source pins plus selected hygiene packets)
    after the last command; a missing path or an applicability path the packet carries no
    pin for is a mutation, fail-closed.
    """

    expected = replay_expected_sha_by_path_v1(packet)
    errors: list[AdmissionErrorV1] = []
    for path in applicability_paths_v1(packet):
        pinned = expected.get(path)
        if pinned is None or current_sha_by_path.get(path) != pinned:
            errors.append(AdmissionErrorV1("REPLAY_WORKTREE_MUTATED", path, "worktree changed during replay"))
    return tuple(errors)


def evaluate_proof_replay_v1(
    packet: Mapping[str, Any], observations: Sequence[ReplayObservationV1]
) -> ReplayEvaluationV1:
    """Grade executed replay observations; no observations means NOT_RUN."""

    if not observations:
        return ReplayEvaluationV1(REPLAY_STATUS_NOT_RUN_V1, (), ())
    errors: list[AdmissionErrorV1] = []
    runs: list[dict[str, object]] = []
    observed = {obs.command_id: obs for obs in observations}
    for command in REPLAY_COMMANDS_V1:
        obs = observed.get(command.command_id)
        if obs is None:
            errors.append(AdmissionErrorV1("REPLAY_COMMAND_MISSING", command.command_id, "not executed"))
            continue
        comparable = _run_check(errors, functools.partial(_grade_observation, obs, packet))
        runs.append(
            {
                "command_id": command.command_id,
                "exit_code": obs.exit_code,
                "stdout_sha256": sha256_hex_v1(obs.stdout),
                "stderr_sha256": sha256_hex_v1(obs.stderr),
                "comparable": comparable if isinstance(comparable, dict) else {},
            }
        )
    status = REPLAY_STATUS_EXECUTED_FAIL_V1 if errors else REPLAY_STATUS_EXECUTED_PASS_V1
    return ReplayEvaluationV1(status, tuple(errors), tuple(runs), observed_toolchain_v1(runs))


def observed_toolchain_v1(runs: Sequence[Mapping[str, object]]) -> dict[str, object]:
    """Derive the toolchain record from fresh replay comparables (never from the builder process)."""

    comparable: dict[str, Mapping[str, object]] = {}
    for run in runs:
        value = run.get("comparable")
        if isinstance(value, dict):
            comparable[str(run.get("command_id"))] = value
    esso = comparable.get("esso_verify_multi", {})
    return {
        "esso_code_hash": esso.get("esso_code_hash"),
        "lean": comparable.get("lean_version", {}).get("lean_version"),
        "python": comparable.get("python_version", {}).get("python_version"),
        "rust": comparable.get("rust_version", {}).get("cargo_version"),
        "rustc": dict(comparable.get("rust_compiler_version", {})) or None,
        "solvers": esso.get("solvers"),
    }


def compare_author_record_v1(
    packet: Mapping[str, Any], evaluation: ReplayEvaluationV1
) -> tuple[AdmissionErrorV1, ...]:
    """Compare an EXECUTED author record against a fresh evaluation's comparable values."""

    record = _section(packet, "proof_replay").get("author_record")
    if not isinstance(record, dict) or record.get("status") != "EXECUTED":
        return ()
    recorded = {str(run.get("command_id")): run for run in record.get("runs", ())}
    errors: list[AdmissionErrorV1] = []
    for run in evaluation.runs:
        previous = recorded.get(str(run["command_id"]), {})
        if previous.get("comparable") != run["comparable"]:
            errors.append(
                AdmissionErrorV1("REPLAY_AUTHOR_RECORD_DRIFT", str(run["command_id"]), "comparable drift")
            )
    if evaluation.status == REPLAY_STATUS_EXECUTED_PASS_V1 and record.get("toolchain") != evaluation.toolchain:
        errors.append(AdmissionErrorV1("REPLAY_AUTHOR_TOOLCHAIN_DRIFT", "proof_replay.author_record.toolchain", "toolchain drift"))
    return tuple(errors)


# ---------------------------------------------------------------------------
# Rendering
# ---------------------------------------------------------------------------


def _md_table(headers: Sequence[str], rows: Sequence[Sequence[object]]) -> list[str]:
    lines = ["| " + " | ".join(headers) + " |", "| " + " | ".join("---" for _ in headers) + " |"]
    for row in rows:
        lines.append("| " + " | ".join(str(cell) for cell in row) + " |")
    return lines


def render_markdown_v1(packet: Mapping[str, Any]) -> str:
    """Render the deterministic human companion of the packet."""

    ceiling = _section(packet, "claim_ceiling")
    esso = _section(packet, "esso_evidence")
    lean = _section(packet, "lean_evidence")
    replay = _section(packet, "proof_replay")
    lines: list[str] = [
        "# ZenoDEX O-008 Formal Cycle V2",
        "",
        "Generated by `tools/build_o008_formal_cycle_v1.py` from the exact source commit below.",
        "Edit the sources and rebuild; do not edit this file by hand.",
        "",
        f"Subject commit: `{packet.get('subject_commit')}`",
        f"Subject parent: `{packet.get('subject_parent')}`",
        f"Subject tree: `{packet.get('subject_tree')}`",
        f"Created: `{packet.get('created_date')}`",
        "",
        "## Claim ceiling",
        "",
    ]
    lines += [f"- `{key}`: `{value}`" for key, value in sorted(ceiling.items())]
    lines += ["", "## Source pins (Git blobs at the subject commit)", ""]
    lines += _md_table(
        ("path", "role", "git_blob", "sha256"),
        [(p["path"], p["role"], p["git_blob"], p["sha256"]) for p in packet.get("source_pins", ())],
    )
    lines += ["", "## Hygiene selection (newest packet pinning each required path at the subject commit)", ""]
    lines += _md_table(
        ("path", "packet", "packet_git_blob", "pin_sha256"),
        [(r["path"], r["packet_path"], r["packet_git_blob"], r["pin_sha256"]) for r in packet.get("hygiene_selection", ())],
    )
    binding = _section(packet, "v1_information_loss").get("binding", {})
    lines += ["", "## V1 projection binding", ""]
    lines += [f"- `{key}`: `{value}`" for key, value in sorted(binding.items())] if isinstance(binding, dict) else []
    lines += ["", "## Lean evidence", "", f"- toolchain: `{lean.get('toolchain')}`",
              f"- theorem count: `{lean.get('theorem_count')}`", ""]
    lines += _md_table(
        ("index", "kind", "name", "line", "statement_sha256"),
        [(t["index"], t["kind"], t["name"], t["line"], t["statement_sha256"]) for t in lean.get("theorems", ())],
    )
    lines += ["", "## ESSO evidence", "", f"- model: `{esso.get('model_id')}`",
              f"- ir_hash ({esso.get('ir_hash_role')}): `{esso.get('ir_hash')}`",
              f"- fingerprint ({esso.get('fingerprint_role')}): `{esso.get('fingerprint')}`",
              f"- invariants: {', '.join(f'`{i}`' for i in esso.get('invariants', ()))}",
              f"- named mutants: {', '.join(f'`{m}`' for m in esso.get('named_mutants', ()))}",
              "", "## Lane source data", ""]
    lines += _md_table(
        ("lane", "status", "missing"),
        [(r["lane_id"], r["status"], r["missing"]) for r in packet.get("lane_source_data", ())],
    )
    command_ids = ", ".join(f"`{c.get('command_id')}`" for c in replay.get("commands", ()))
    lines += ["", "## Proof replay", "",
              f"- commands: {command_ids}",
              f"- author record status: `{replay.get('author_record', {}).get('status')}`",
              f"- admission semantics: `{replay.get('admission_semantics')}`", "",
              "## Nonclaims", ""]
    lines += [f"- {item}" for item in packet.get("nonclaims", ())]
    return "\n".join(lines) + "\n"


@dataclass(frozen=True, slots=True)
class ReportInputsV1:
    """Everything the report renderer needs; absent values mean the stage was not reached."""

    packet_commit: str | None
    subject_commit: str | None
    head_commit: str | None
    outcome: AdmissionOutcomeV1 | None
    replay: ReplayEvaluationV1
    executing: Mapping[str, str]
    extra_errors: tuple[AdmissionErrorV1, ...] = ()
    infra_error: AdmissionErrorV1 | None = None


def render_report_v1(inputs: ReportInputsV1) -> dict[str, Any]:
    """Assemble the machine-readable report; the claim ceiling comes from constants."""

    outcome, replay = inputs.outcome, inputs.replay
    errors = list(outcome.errors if outcome else ()) + list(inputs.extra_errors) + list(replay.errors)
    if inputs.infra_error is not None:
        errors.append(inputs.infra_error)
    admitted = outcome is not None and outcome.packet_admitted and inputs.infra_error is None
    applicable = admitted and outcome is not None and outcome.current_applicable
    ok = applicable and replay.status in {REPLAY_STATUS_NOT_RUN_V1, REPLAY_STATUS_EXECUTED_PASS_V1}
    ok = ok and not inputs.extra_errors
    exit_code = 2 if inputs.infra_error is not None else (0 if ok else 1)
    return {
        "schema": REPORT_SCHEMA_V3,
        "ok": ok,
        "exit_code": exit_code,
        "packet_path": PACKET_JSON_PATH_V1,
        "packet_commit": inputs.packet_commit,
        "subject_commit": inputs.subject_commit,
        "head_commit": inputs.head_commit,
        "packet_admitted": admitted,
        "current_applicable": applicable,
        "current_source_drift": list(outcome.current_source_drift) if outcome else [],
        "proof_replay": {"status": replay.status, "runs": list(replay.runs)},
        "claim_ceiling": dict(CLAIM_CEILING_V1),
        "executing_tools": dict(inputs.executing),
        "errors": [error.to_json() for error in errors],
    }


def exit_code_for_report_v1(report: Mapping[str, Any]) -> int:
    value = report.get("exit_code")
    return value if isinstance(value, int) and value in {0, 1, 2} else 2


__all__ = [
    "AdmissionContextV1",
    "AdmissionErrorV1",
    "AdmissionOutcomeV1",
    "AdmissionRejectV1",
    "admit_packet_v1",
    "canonical_packet_bytes_v1",
    "CERTIFICATE_CHECK_ORDER_V1",
    "CERTIFICATE_ESSO_SUBJECT_V1",
    "certificate_fixture_surface_v1",
    "CERTIFICATE_LEAN_SUBJECT_V1",
    "CERTIFICATE_PRODUCER_KINDS_V1",
    "CERTIFICATE_REJECT_CODES_V1",
    "ClassShapeV1",
    "compare_author_record_v1",
    "CurrentSourceStateV1",
    "decode_json_object_v1",
    "decode_packet_v1",
    "esso_model_surface_v1",
    "ESSO_SUBJECTS_V1",
    "EssoSubjectV1",
    "evaluate_proof_replay_v1",
    "ExecutingToolsV1",
    "exit_code_for_report_v1",
    "git_blob_oid_v1",
    "hygiene_lineage_key_v1",
    "lean_command_closure_v1",
    "LEAN_DEFINITION_SURFACE_SHA256_V1",
    "lean_definition_surface_v1",
    "lean_literal_closure_v1",
    "LEAN_STATEMENT_SHA256_V1",
    "LEAN_SUBJECTS_V1",
    "lean_theorem_inventory_v1",
    "LeanSubjectV1",
    "O008_ESSO_SUBJECT_V1",
    "O008_LEAN_SUBJECT_V1",
    "PacketTopologyV1",
    "parse_rustc_vv_v1",
    "project_packet_v1",
    "python_class_shape_v1",
    "python_enum_members_v1",
    "render_markdown_v1",
    "render_report_v1",
    "REPLAY_ENV_POLICY_V1",
    "ReplayCommandV1",
    "ReplayEvaluationV1",
    "ReplayObservationV1",
    "ReportInputsV1",
    "RUST_CRATE_MODULES_V1",
    "rust_state_import_closure_v1",
    "rust_struct_shape_v1",
    "sha256_hex_v1",
    "SourceBlobV1",
    "strip_rust_noncode_v1",
    "StructShapeV1",
    "SubjectSnapshotV1",
    "TheoremEntryV1",
    "validate_author_replay_record_v1",
]
