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

PACKET_SCHEMA_V3: Final = "zenodex/o008-formal-cycle-evidence/v3"
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

SOURCE_PIN_ROLES_V1: Final[tuple[tuple[str, str], ...]] = (
    (PYTHON_REFINEMENT_PATH_V1, "python_visible_necessary_checks"),
    (RUST_REFINEMENT_PATH_V1, "rust_visible_necessary_checks"),
    (GOLDEN_RENDERER_PATH_V1, "claimant_backing_guard_golden_renderer"),
    (GOLDEN_FIXTURE_PATH_V1, "claimant_backing_guard_golden_fixture"),
    (GOLDEN_PYTHON_TEST_PATH_V1, "claimant_backing_guard_golden_python_replay"),
    (GOLDEN_RUST_TEST_PATH_V1, "claimant_backing_guard_golden_rust_replay"),
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
    PYTHON_GATE_PATH_V1,
    RUST_GATE_PATH_V1,
    GATE_TESTS_PATH_V1,
    LEAN_GATE_PATH_V1,
    ESSO_GATE_PATH_V1,
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

NONCLAIMS_V1: Final[tuple[str, ...]] = (
    "The completed formal cycle does not complete O-008.",
    "The exact all-twelve-lane claimant entitlement and reserve reconciliation certificate is"
    " not implemented or mounted.",
    "The ESSO model does not refine current Python, Rust, RISC0, Tau, verifier, or publisher"
    " execution.",
    "The Lean theorems do not establish cryptographic binding, finite-width runtime parity,"
    " settlement authority, or whole-program value safety.",
    "The ESSO fingerprint is a determinism witness only; the ESSO ir_hash is the model-binding"
    " value and is verified only by proof replay.",
    "A detached host-generated sidecar can be swapped independently of an epoch receipt and"
    " therefore grants evidence-only authority.",
    "Recorded proof replay results are packet-author observations; packet admission reports"
    " proof replay as NOT_RUN unless the checker executed the recorded tools.",
    "Without proof replay the author record's python and rust versions and the Lean axioms"
    " probe hash are shape-checked only; fresh replay is what compares them.",
    "Selected test-hygiene packets are bound by pin only; their evidence families and mutation"
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
ESSO_ACTIONS_V1: Final[tuple[str, ...]] = ("open_claim", "drain_claim")
ESSO_QUERIES_V1: Final[tuple[str, ...]] = (
    "init_implies_inv",
    "inductive_open_claim",
    "inductive_drain_claim",
)
ESSO_NAMED_MUTANTS_V1: Final[tuple[str, ...]] = (
    "accept_without_global_root_binding",
    "cross_domain_custody_substitution",
    "claimant_column_substitution",
    "terminal_domain_erasure",
    "drain_cross_domain_custody_substitution",
)
ESSO_CODE_COMMIT_V1: Final = "7f80c6216be85c827e8d1cc2fa08ee3107a74588"
ESSO_SOLVERS_V1: Final[dict[str, str]] = {"z3": "4.15.4", "cvc5": "1.1.2"}
ESSO_DETERMINISM_TRIALS_V1: Final = 2
ESSO_SOLVER_TIMEOUT_MS_V1: Final = 10000
ESSO_GATE_EXPECTED_PASSED_V1: Final = 18
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
LEAN_GATE_PIN_ORDER_V1: Final[tuple[str, ...]] = (
    LEAN_PROOF_PATH_V1,
    ESSO_MODEL_PATH_V1,
    PYTHON_TYPES_PATH_V1,
    PYTHON_REFINEMENT_PATH_V1,
    RUST_STATE_PATH_V1,
    RUST_REFINEMENT_PATH_V1,
)

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
# Whitespace-normalised fragments of bounded_vec.rs that fix the decoding path: the visitor
# decodes every element through `T: Deserialize` (the record's derive) and nothing else.
BOUNDED_VEC_REQUIRED_FRAGMENTS_V1: Final[tuple[str, ...]] = (
    "pub(crate) fn deserialize_bounded_vec_v1<'de, D, T, const MAXIMUM: usize>( deserializer: D, label: &'static str, ) -> Result<Vec<T>, D::Error> where D: Deserializer<'de>, T: Deserialize<'de>, { deserializer.deserialize_seq(BoundedVecVisitorV1::<T, MAXIMUM> { label, marker: PhantomData, }) }",
    "impl<'de, T, const MAXIMUM: usize> Visitor<'de> for BoundedVecVisitorV1<T, MAXIMUM> where T: Deserialize<'de>, { type Value = Vec<T>;",
    'match sequence.next_element()? { Some(value) => values.push(value), None => return Ok(values), }',
)
# Closed content of the two compiled/imported projection gates.
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
        "no cfg, include, or path attributes; no item-defining or record-naming macro token"
        " trees; single depth-zero definition; exact derive plus deny_unknown_fields attribute"
        " block; no field attributes; serde imported only from serde; crate root declares mod"
        " state once; manifest keeps default targets and registry dependencies"
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
)

ADMISSION_SEMANTICS_V1: Final = (
    "AUTHOR_RECORD_IS_OBSERVATION_ONLY_CHECKER_REPORTS_NOT_RUN_UNLESS_IT_EXECUTES"
)
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
PYTHON_GOLDEN_GATE_EXPECTED_PASSED_V1: Final = 35
_CARGO_VERSION_RE: Final = re.compile(r"^cargo ([0-9]+\.[0-9]+\.[0-9]+)")
EMPTY_SHA256_V1: Final = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
_SEMVER_RE: Final = re.compile(r"[0-9]+\.[0-9]+\.[0-9]+")
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
_LEAN_NAMESPACE_RE: Final = re.compile(r"^(namespace|end)[ \t]+(\S+)[ \t]*$", re.MULTILINE)
_RUST_FIELD_RE: Final = re.compile(r"^([A-Za-z_][A-Za-z0-9_]*)\s*:\s*(.+?)\s*$", re.DOTALL)
_RUST_MACRO_INVOCATION_RE: Final = re.compile(
    r"\b([A-Za-z_][A-Za-z0-9_]*)!\s*(?:[A-Za-z_][A-Za-z0-9_]*\s*)?([\(\[{])"
)
_RUST_ITEM_KEYWORD_RE: Final = re.compile(r"\b(?:struct|enum|union|trait|impl|type|mod|use|extern)\b")
# `use` statements tokenised from stripped code: anchored on statement boundaries, not lines.
_RUST_USE_RE: Final = re.compile(r"(?:^|[;{}])\s*(?:pub(?:\([^)]*\))?\s+)?use\s+([^;{}]+);")
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
        "prior_restage_gate",
        (PYTHON_TOKEN_V1, "-m", "pytest", "-q", "-p", "no:cacheprovider", PRIOR_ESSO_GATE_PATH_V1),
        ".",
        ("PYTHONPATH", "ZENO_ESSO_PYTHON"),
        f"exit 0; {PRIOR_ESSO_GATE_EXPECTED_PASSED_V1} passed",
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
    if packet.get("schema") != PACKET_SCHEMA_V3:
        _reject("PACKET_SCHEMA_DRIFT", "schema", f"expected {PACKET_SCHEMA_V3}")
    if raw != canonical_packet_bytes_v1(packet):
        _reject("PACKET_JSON_NONCANONICAL", PACKET_JSON_PATH_V1, "noncanonical JSON encoding")
    if frozenset(packet) != PACKET_KEYS_V3:
        _reject("PACKET_KEY_SET_DRIFT", "$", "top-level key set differs from the closed set")
    return packet


# ---------------------------------------------------------------------------
# Lean extraction
# ---------------------------------------------------------------------------


def _lean_code(text: str) -> str:
    try:
        code: str = strip_lean_noncode(text)
    except ScanError as exc:
        _reject("LEAN_SOURCE_UNPARSEABLE", LEAN_PROOF_PATH_V1, str(exc))
    return code


def _lean_statement_boundary(code: str, index: int) -> bool:
    """True when a depth-zero statement ends here: ``:=`` or a proof-case line."""

    if code.startswith(":=", index):
        return True
    return code[index] == "\n" and code[index + 1 :].lstrip(" \t").startswith("|")


def _lean_statement_end(code: str, start: int) -> int:
    depth = 0
    for index in range(start, len(code)):
        depth += {"(": 1, "[": 1, "{": 1, "⟨": 1, ")": -1, "]": -1, "}": -1, "⟩": -1}.get(code[index], 0)
        if depth == 0 and _lean_statement_boundary(code, index):
            return index
    _reject("LEAN_STATEMENT_UNPARSEABLE", LEAN_PROOF_PATH_V1, f"no statement end after {start}")


def lean_theorem_inventory_v1(text: str) -> tuple[TheoremEntryV1, ...]:
    """Return every theorem/lemma declaration in file order with a statement hash."""

    code = _lean_code(text)
    entries: list[TheoremEntryV1] = []
    for match in _LEAN_DECL_RE.finditer(code):
        if "private" in match.group("mods"):
            _reject("LEAN_PRIVATE_THEOREM_FORBIDDEN", LEAN_PROOF_PATH_V1, match.group("name"))
        end = _lean_statement_end(code, match.end())
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


def lean_namespace_check_v1(text: str) -> None:
    code = _lean_code(text)
    opened = [m.group(2) for m in _LEAN_NAMESPACE_RE.finditer(code) if m.group(1) == "namespace"]
    closed = [m.group(2) for m in _LEAN_NAMESPACE_RE.finditer(code) if m.group(1) == "end"]
    if tuple(opened) != LEAN_NAMESPACE_V1 or tuple(closed) != tuple(reversed(LEAN_NAMESPACE_V1)):
        _reject("LEAN_NAMESPACE_DRIFT", LEAN_PROOF_PATH_V1, f"{opened} / {closed}")


def lean_placeholder_matches_v1(text: str) -> tuple[str, ...]:
    try:
        matches = scan_text(LEAN_PROOF_PATH_V1, text, check_axioms=True)
    except ScanError as exc:
        _reject("LEAN_SOURCE_UNPARSEABLE", LEAN_PROOF_PATH_V1, str(exc))
    return tuple(f"{match.rule}:{match.line}" for match in matches)


def lean_import_root_declares_v1(root_text: str) -> bool:
    code = strip_lean_noncode(root_text)
    return any(line.strip() == LEAN_IMPORT_LINE_V1 for line in code.splitlines())


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
# A gate file may call setattr on an instance under test; module rebinding stays forbidden.
_PYTHON_GATE_DYNAMIC_CALLS_V1: Final[frozenset[str]] = _PYTHON_DYNAMIC_CALLS_V1 - {"setattr", "delattr"}


def python_dynamic_binding_scan_v1(
    source: bytes, path: str, forbidden: frozenset[str] = _PYTHON_DYNAMIC_CALLS_V1
) -> None:
    """Reject dynamic name binding that an AST scan of definitions cannot see through."""

    for node in ast.walk(_parse_python(source, path)):
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in forbidden:
            _reject("PYTHON_DYNAMIC_BINDING_FORBIDDEN", path, f"{node.func.id}() at line {node.lineno}")
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
    definitions = {m.group(1): m.start() for m in re.finditer(r"\bmacro_rules!\s*([A-Za-z_][A-Za-z0-9_]*)", code)}
    for match in _RUST_MACRO_INVOCATION_RE.finditer(code):
        tree = code[match.start(2) : _balanced_end(code, match.start(2))]
        head = code[match.start() : match.start() + 60]
        if match.group(1) == "macro_rules":
            if _RUST_ITEM_KEYWORD_RE.search(tree):
                _reject("RUST_MACRO_DEFINES_ITEM", path, head)
            if _RUST_MACRO_INVOCATION_RE.search(tree):
                _reject("RUST_MACRO_NESTED_INVOCATION", path, head)
        elif match.group(1) == "include_str" and allow_include_str:
            continue
        elif _brace_depth_at(code, match.start()) == 0:
            qualified = code[max(0, match.start() - 2) : match.start()] == "::"
            defined_before = definitions.get(match.group(1))
            if qualified or defined_before is None or defined_before > match.start():
                _reject("RUST_FOREIGN_ITEM_MACRO", path, head)
            if _RUST_ITEM_KEYWORD_RE.search(tree):
                _reject("RUST_MACRO_DEFINES_ITEM", path, head)
    for use in _RUST_USE_RE.finditer(code):
        target = " ".join(use.group(1).split())
        if re.search(r"\b(?:Serialize|Deserialize|Serializer|Deserializer)\b", target) and not target.startswith("serde::"):
            _reject("RUST_SERDE_IMPORT_DRIFT", path, target[:60])
        if (
            not defines_bounded_vec
            and "deserialize_bounded_vec_v1" in target
            and target != "crate::bounded_vec::deserialize_bounded_vec_v1"
        ):
            _reject("RUST_BOUNDED_VEC_IMPORT_DRIFT", path, target[:60])
    return code


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
        invocations = re.findall(
            r"\b" + BOUNDED_VEC_MACRO_NAME_V1 + r"!\(\s*" + function + r"\s*,\s*" + record + r"\s*,\s*MAX_GLOBAL_[A-Z_]+_V1\s*,",
            code,
        )
        if len(invocations) != 1 or re.search(r"\bfn\s+" + function + r"\b", code):
            _reject("RUST_CONTAINER_DESERIALIZER_DRIFT", path, f"{function}: {len(invocations)} macro invocations")


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
    normalized = _normalized(library)
    for fragment in BOUNDED_VEC_REQUIRED_FRAGMENTS_V1:
        if fragment not in normalized:
            _reject("RUST_BOUNDED_VEC_DRIFT", path, fragment[:60])
    manual_deserialize = re.search(r"\bimpl\b[^{]*\bDeserialize\b[^{]*\bfor\b", library)
    if len(re.findall(r"\bimpl\b", library)) != 1 or manual_deserialize is not None:
        _reject("RUST_BOUNDED_VEC_DRIFT", path, "exactly one impl block and no Deserialize impl")


def rust_crate_root_closure_v1(source: bytes, path: str) -> None:
    """The crate root declares ``mod state;`` unconditionally and nothing redirects modules."""

    code = rust_lexical_closure_v1(source, path, (TERMINAL_CLASS_NAME_V1, OUTBOX_CLASS_NAME_V1))
    declarations = re.findall(r"^\s*(?:pub(?:\([^)]*\))?\s+)?mod\s+state\s*;", code, re.MULTILINE)
    if len(declarations) != 1:
        _reject("RUST_STATE_MODULE_DECLARATION_DRIFT", path, f"{len(declarations)} declarations of mod state")
    if re.search(r"\bmod\s+state\s*\{", code):
        _reject("RUST_STATE_MODULE_DECLARATION_DRIFT", path, "inline mod state")


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


def esso_model_surface_v1(blob: bytes) -> tuple[str, tuple[str, ...], tuple[str, ...]]:
    """Return (model_id, ordered invariant ids, ordered action ids) from the ESSO-IR yaml."""

    try:
        data = yaml.safe_load(blob.decode("utf-8"))
    except (UnicodeDecodeError, yaml.YAMLError) as exc:
        _reject("ESSO_MODEL_UNPARSEABLE", ESSO_MODEL_PATH_V1, type(exc).__name__)
    if not isinstance(data, dict) or not isinstance(data.get("meta"), dict):
        _reject("ESSO_MODEL_UNPARSEABLE", ESSO_MODEL_PATH_V1, "meta object required")
    model_id = data["meta"].get("model_id")
    invariants = data.get("invariants")
    actions = data.get("actions")
    if not isinstance(model_id, str) or not isinstance(invariants, list) or not isinstance(actions, list):
        _reject("ESSO_MODEL_UNPARSEABLE", ESSO_MODEL_PATH_V1, "model_id, invariants, actions required")
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


def _project_esso(snapshot: SubjectSnapshotV1) -> dict[str, object]:
    model = _blob(snapshot, ESSO_MODEL_PATH_V1)
    gate = _blob(snapshot, ESSO_GATE_PATH_V1)
    model_id, invariants, actions = esso_model_surface_v1(model.data)
    if model_id != ESSO_MODEL_ID_V1:
        _reject("ESSO_MODEL_ID_DRIFT", ESSO_MODEL_PATH_V1, model_id)
    if invariants != ESSO_INVARIANTS_V1:
        _reject("ESSO_INVARIANTS_DRIFT", ESSO_MODEL_PATH_V1, ",".join(invariants))
    if actions != ESSO_ACTIONS_V1:
        _reject("ESSO_ACTIONS_DRIFT", ESSO_MODEL_PATH_V1, ",".join(actions))
    constants = python_string_constants_v1(gate.data, ESSO_GATE_PATH_V1)
    if model.sha256 not in constants.values():
        _reject("ESSO_GATE_SOURCE_PIN_DRIFT", ESSO_GATE_PATH_V1, "gate does not pin the model sha256")
    gate_invariants = python_sequence_constant_v1(gate.data, "EXPECTED_INVARIANTS", ESSO_GATE_PATH_V1)
    if frozenset(gate_invariants) != frozenset(ESSO_INVARIANTS_V1):
        _reject("ESSO_GATE_INVARIANTS_DRIFT", ESSO_GATE_PATH_V1, ",".join(gate_invariants))
    mutants = pytest_param_ids_v1(gate.data, ESSO_GATE_PATH_V1)
    if tuple(m for m in mutants if m in ESSO_NAMED_MUTANTS_V1) != ESSO_NAMED_MUTANTS_V1:
        _reject("ESSO_GATE_MUTANTS_DRIFT", ESSO_GATE_PATH_V1, ",".join(mutants))
    ir_hash = constants.get("RECORDED_IR_HASH", "")
    if not ir_hash.startswith("sha256:") or _HEX64_RE.fullmatch(ir_hash[7:]) is None:
        _reject("ESSO_IR_HASH_DRIFT", ESSO_GATE_PATH_V1, "RECORDED_IR_HASH malformed")
    if constants.get("RECORDED_ESSO_CODE_HASH") != ESSO_CODE_COMMIT_V1:
        _reject("ESSO_CODE_COMMIT_DRIFT", ESSO_GATE_PATH_V1, "RECORDED_ESSO_CODE_HASH drift")
    return {
        "model_id": model_id,
        "model_source_sha256": model.sha256,
        "actions": list(actions),
        "invariants": list(invariants),
        "queries": list(ESSO_QUERIES_V1),
        "named_mutants": list(ESSO_NAMED_MUTANTS_V1),
        "esso_code_commit": ESSO_CODE_COMMIT_V1,
        "ir_hash": ir_hash,
        "ir_hash_role": IR_HASH_ROLE_V1,
        "fingerprint": constants.get("RECORDED_FINGERPRINT", ""),
        "fingerprint_role": FINGERPRINT_ROLE_V1,
        "solvers": dict(ESSO_SOLVERS_V1),
        "determinism_trials": ESSO_DETERMINISM_TRIALS_V1,
        "solver_timeout_ms": ESSO_SOLVER_TIMEOUT_MS_V1,
        "gate_expected_passed": ESSO_GATE_EXPECTED_PASSED_V1,
        "claim_boundary": ESSO_CLAIM_BOUNDARY_V1,
    }


def _check_lean_gate(snapshot: SubjectSnapshotV1, names: tuple[str, ...]) -> None:
    gate = _blob(snapshot, LEAN_GATE_PATH_V1)
    if python_sequence_constant_v1(gate.data, "THEOREMS", LEAN_GATE_PATH_V1) != names:
        _reject("LEAN_GATE_THEOREMS_DRIFT", LEAN_GATE_PATH_V1, "THEOREMS differs from inventory")
    expected_pins = tuple(_blob(snapshot, path).sha256 for path in LEAN_GATE_PIN_ORDER_V1)
    if python_dict_values_v1(gate.data, "PINNED_SOURCES", LEAN_GATE_PATH_V1) != expected_pins:
        _reject("LEAN_GATE_PIN_DRIFT", LEAN_GATE_PATH_V1, "PINNED_SOURCES differ from subject")
    axioms = python_sequence_constant_v1(gate.data, "ALLOWED_STANDARD_AXIOMS", LEAN_GATE_PATH_V1)
    if frozenset(axioms) != ALLOWED_LEAN_AXIOMS_V1:
        _reject("LEAN_GATE_AXIOMS_DRIFT", LEAN_GATE_PATH_V1, ",".join(axioms))


def _project_lean(snapshot: SubjectSnapshotV1) -> dict[str, object]:
    proof = _blob(snapshot, LEAN_PROOF_PATH_V1).data.decode("utf-8")
    placeholders = lean_placeholder_matches_v1(proof)
    if placeholders:
        _reject("LEAN_PLACEHOLDER_PRESENT", LEAN_PROOF_PATH_V1, ",".join(placeholders))
    lean_namespace_check_v1(proof)
    inventory = lean_theorem_inventory_v1(proof)
    pairs = tuple((entry.kind, entry.name) for entry in inventory)
    if pairs != THEOREM_INVENTORY_V1:
        _reject("LEAN_THEOREM_INVENTORY_DRIFT", LEAN_PROOF_PATH_V1, _first_difference(pairs))
    toolchain = lean_toolchain_v1(_blob(snapshot, LEAN_TOOLCHAIN_PATH_V1).data.decode("utf-8"))
    if toolchain != LEAN_TOOLCHAIN_V1:
        _reject("LEAN_TOOLCHAIN_DRIFT", LEAN_TOOLCHAIN_PATH_V1, toolchain)
    if not lean_import_root_declares_v1(_blob(snapshot, LEAN_ROOT_PATH_V1).data.decode("utf-8")):
        _reject("LEAN_IMPORT_ROOT_MISSING", LEAN_ROOT_PATH_V1, LEAN_IMPORT_LINE_V1)
    return {
        "toolchain": toolchain,
        "namespace": ".".join(LEAN_NAMESPACE_V1),
        "import_root_declares_module": True,
        "theorems": [entry.to_json() for entry in inventory],
        "theorem_count": len(inventory),
        "definitional_theorems": list(LEAN_DEFINITIONAL_THEOREMS_V1),
        "substantive_theorem_count": len(inventory) - len(LEAN_DEFINITIONAL_THEOREMS_V1),
        "placeholder_scan": {"match_count": 0, "axiom_check": True},
        "allowed_axioms": sorted(ALLOWED_LEAN_AXIOMS_V1),
        "no_recovery_theorem": LEAN_NO_RECOVERY_THEOREM_V1,
        "replay_only": {
            "direct_warning_as_error_check": "lean_direct_check",
            "print_axioms_probe": "lean_axioms_probe",
            "binding_gate_expected_passed": LEAN_GATE_EXPECTED_PASSED_V1,
        },
        "claim_boundary": LEAN_CLAIM_BOUNDARY_V1,
    }


def _first_difference(pairs: tuple[tuple[str, str], ...]) -> str:
    for index, (actual, expected) in enumerate(zip(pairs, THEOREM_INVENTORY_V1, strict=False)):
        if actual != expected:
            return f"index {index}: {actual} != {expected}"
    return f"count {len(pairs)} != {len(THEOREM_INVENTORY_V1)}"


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


def _project_information_loss(snapshot: SubjectSnapshotV1) -> dict[str, object]:
    python_source = _blob(snapshot, PYTHON_TYPES_PATH_V1).data
    rust_source = _blob(snapshot, RUST_STATE_PATH_V1).data
    rust_lexical_closure_v1(rust_source, RUST_STATE_PATH_V1, (TERMINAL_CLASS_NAME_V1, OUTBOX_CLASS_NAME_V1))
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


def _select_hygiene_packets(snapshot: SubjectSnapshotV1) -> list[dict[str, object]]:
    """Select, per required path, the newest hygiene packet whose pin equals the subject blob.

    Packets are ordered by evidence id (newest last), mirroring the repository
    hygiene gate: stale packets are skipped, a path with no matching packet is drift,
    and a selected packet that pins the O-008 packet itself is circular.
    """

    ordered = sorted(snapshot.hygiene_packets.values(), key=lambda blob: blob.path, reverse=True)
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
    return selection


AUTHOR_RUN_KEYS_V1: Final[frozenset[str]] = frozenset({"command_id", "exit_code", "comparable"})
AUTHOR_TOOLCHAIN_KEYS_V1: Final[frozenset[str]] = frozenset({"esso_code_hash", "lean", "python", "rust", "solvers"})
LEAN_VERSION_V1: Final = LEAN_TOOLCHAIN_V1.rsplit("v", 1)[1]
# Closed comparable schema per replay command: key -> ("hex64" | "semver" | "verdict" | "solvers" | exact value).
COMPARABLE_SCHEMA_V1: Final[dict[str, dict[str, object]]] = {
    "lean_version": {"lean_version": LEAN_VERSION_V1},
    "lean_direct_check": {"stdout_sha256": EMPTY_SHA256_V1},
    "lean_axioms_probe": {"probe_sha256": "hex64", "theorems_probed": len(THEOREM_INVENTORY_V1)},
    "lean_binding_gate": {"passed": LEAN_GATE_EXPECTED_PASSED_V1},
    "esso_validate": {"ir_hash": "esso_ir_hash"},
    "esso_verify_multi": {
        "verdict": "VERIFIED",
        "fingerprint": "esso_fingerprint",
        "solvers": "solvers",
        "esso_code_hash": ESSO_CODE_COMMIT_V1,
    },
    "esso_gate": {"passed": ESSO_GATE_EXPECTED_PASSED_V1},
    "prior_restage_gate": {"passed": PRIOR_ESSO_GATE_EXPECTED_PASSED_V1},
    "python_version": {"python_version": "semver"},
    "python_projection_gate": {"passed": PYTHON_GATE_EXPECTED_PASSED_V1},
    "rust_projection_gate": {"passed": RUST_GATE_EXPECTED_PASSED_V1},
    "rust_version": {"cargo_version": "semver"},
    "rust_refinement_gate": {"passed": RUST_REFINEMENT_GATE_EXPECTED_PASSED_V1},
    "python_golden_gate": {"passed": PYTHON_GOLDEN_GATE_EXPECTED_PASSED_V1},
    "rust_golden_gate": {"passed": RUST_GOLDEN_GATE_EXPECTED_PASSED_V1},
}


def _comparable_value_ok(rule: object, value: object, esso: Mapping[str, Any]) -> bool:
    if rule == "hex64":
        return isinstance(value, str) and _HEX64_RE.fullmatch(value) is not None
    if rule == "semver":
        return isinstance(value, str) and _SEMVER_RE.fullmatch(value) is not None
    if rule == "solvers":
        return value == dict(ESSO_SOLVERS_V1)
    if rule == "esso_ir_hash":
        return value == esso.get("ir_hash")
    if rule == "esso_fingerprint":
        return value == esso.get("fingerprint")
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
        _reject("REPLAY_RECORD_SHAPE", where, "exactly esso_code_hash, lean, python, rust, solvers")
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
    return {
        "esso_code_hash": ESSO_CODE_COMMIT_V1,
        "lean": LEAN_VERSION_V1,
        "python": versions["python"],
        "rust": versions["rust"],
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
    for key, command_id, field_name in (("python", "python_version", "python_version"), ("rust", "rust_version", "cargo_version")):
        run = next(run["comparable"] for run in validated if run["command_id"] == command_id)
        if not isinstance(run, dict) or run.get(field_name) != toolchain[key]:
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
    esso_evidence = _project_esso(snapshot)
    projection = {
        "schema": PACKET_SCHEMA_V3,
        "created_date": created_date,
        "subject_commit": snapshot.subject_commit,
        "subject_parent": snapshot.subject_parent,
        "subject_tree": snapshot.subject_tree,
        "packet_commit_parent": snapshot.subject_commit,
        "packet_write_set": [{"status": s, "path": p} for s, p in PACKET_WRITE_SET_V1],
        "claim_ceiling": dict(CLAIM_CEILING_V1),
        "completion_scope": list(COMPLETION_SCOPE_V1),
        "source_pins": _project_source_pins(snapshot),
        "esso_evidence": esso_evidence,
        "lean_evidence": _project_lean(snapshot),
        "v1_information_loss": _project_information_loss(snapshot),
        "lane_source_data": [
            {"lane_id": lane, "status": status, "missing": missing}
            for lane, status, missing in LANE_SOURCE_DATA_V1
        ],
        "required_sidecar": json.loads(json.dumps(REQUIRED_SIDECAR_V1)),
        "proof_replay": {
            "commands": [command.to_json() for command in REPLAY_COMMANDS_V1],
            "author_record": validate_author_replay_record_v1(author_replay_record, esso_evidence),
            "admission_semantics": ADMISSION_SEMANTICS_V1,
        },
        "nonclaims": list(NONCLAIMS_V1),
    }
    # Pin-consistency checks run last so a structural finding in a source is
    # reported before the derived pin drift it also causes.
    _check_lean_gate(snapshot, tuple(name for _, name in THEOREM_INVENTORY_V1))
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


def check_sidecar_v1(packet: Mapping[str, Any]) -> None:
    sidecar = _section(packet, "required_sidecar")
    expected = json.loads(json.dumps(REQUIRED_SIDECAR_V1))
    for key, value in expected.items():
        if sidecar.get(key) != value:
            _reject("SIDECAR_DRIFT", f"required_sidecar.{key}", str(sidecar.get(key))[:80])
    if set(sidecar) != set(expected):
        _reject("SIDECAR_DRIFT", "required_sidecar", "unexpected keys")


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
    if obs.command_id == "lean_direct_check":
        if obs.stdout.strip() or obs.stderr.strip():
            _reject("REPLAY_LEAN_OUTPUT_NONEMPTY", obs.command_id, "direct check produced output")
        return {"stdout_sha256": sha256_hex_v1(obs.stdout)}
    axioms = parse_print_axioms_v1(obs.stdout)
    namespace = ".".join(LEAN_NAMESPACE_V1)
    for _, name in THEOREM_INVENTORY_V1:
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


def _grade_python_version(obs: ReplayObservationV1) -> dict[str, object]:
    version = parse_python_version_v1(obs.stdout)
    if version is None:
        _reject("REPLAY_PYTHON_VERSION_UNPARSEABLE", obs.command_id, obs.stdout[:40].decode("utf-8", "replace"))
    return {"python_version": version}


def _grade_pytest(obs: ReplayObservationV1, expected: int) -> dict[str, object]:
    passed = parse_pytest_summary_v1(obs.stdout)
    if passed is None:
        _reject("REPLAY_PYTEST_SUMMARY_UNPARSEABLE", obs.command_id, "no passed summary")
    if passed != expected:
        _reject("REPLAY_PASSED_COUNT_DRIFT", obs.command_id, f"{passed} != {expected}")
    return {"passed": passed}


def _grade_esso(obs: ReplayObservationV1, esso: Mapping[str, Any]) -> dict[str, object]:
    payload = parse_esso_json_v1(obs.stdout, obs.stderr)
    if payload is None:
        _reject("REPLAY_ESSO_OUTPUT_UNPARSEABLE", obs.command_id, "no JSON payload")
    if obs.command_id == "esso_validate":
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
    expected_queries = len(ESSO_QUERIES_V1)
    queries_raw = payload.get("queries")
    query_ids = set(queries_raw) if isinstance(queries_raw, dict) else set()
    if report.get("total_queries") != expected_queries or report.get("passed_queries") != expected_queries:
        _reject("REPLAY_ESSO_QUERY_COUNT_DRIFT", obs.command_id, f"{report.get('total_queries')}/{report.get('passed_queries')}")
    if query_ids != set(ESSO_QUERIES_V1):
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
    if obs.command_id.startswith("lean_") and obs.command_id != "lean_binding_gate":
        return _grade_lean(obs, packet)
    if obs.command_id == "lean_binding_gate":
        return _grade_pytest(obs, LEAN_GATE_EXPECTED_PASSED_V1)
    if obs.command_id == "esso_gate":
        return _grade_pytest(obs, ESSO_GATE_EXPECTED_PASSED_V1)
    if obs.command_id == "prior_restage_gate":
        return _grade_pytest(obs, PRIOR_ESSO_GATE_EXPECTED_PASSED_V1)
    if obs.command_id == "python_version":
        return _grade_python_version(obs)
    if obs.command_id == "python_projection_gate":
        return _grade_pytest(obs, PYTHON_GATE_EXPECTED_PASSED_V1)
    if obs.command_id == "rust_projection_gate":
        return _grade_cargo(obs, RUST_GATE_EXPECTED_PASSED_V1)
    if obs.command_id == "rust_version":
        return _grade_rust_version(obs)
    if obs.command_id == "rust_refinement_gate":
        return _grade_cargo(obs, RUST_REFINEMENT_GATE_EXPECTED_PASSED_V1)
    if obs.command_id == "rust_golden_gate":
        return _grade_cargo(obs, RUST_GOLDEN_GATE_EXPECTED_PASSED_V1)
    if obs.command_id == "python_golden_gate":
        return _grade_pytest(obs, PYTHON_GOLDEN_GATE_EXPECTED_PASSED_V1)
    return _grade_esso(obs, esso)


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
    "ReportInputsV1",
    "ClassShapeV1",
    "CurrentSourceStateV1",
    "ExecutingToolsV1",
    "PacketTopologyV1",
    "ReplayCommandV1",
    "ReplayEvaluationV1",
    "ReplayObservationV1",
    "SourceBlobV1",
    "StructShapeV1",
    "SubjectSnapshotV1",
    "TheoremEntryV1",
    "admit_packet_v1",
    "canonical_packet_bytes_v1",
    "compare_author_record_v1",
    "decode_json_object_v1",
    "decode_packet_v1",
    "esso_model_surface_v1",
    "evaluate_proof_replay_v1",
    "exit_code_for_report_v1",
    "git_blob_oid_v1",
    "lean_theorem_inventory_v1",
    "project_packet_v1",
    "python_class_shape_v1",
    "render_markdown_v1",
    "render_report_v1",
    "rust_struct_shape_v1",
    "sha256_hex_v1",
    "strip_rust_noncode_v1",
    "validate_author_replay_record_v1",
]
