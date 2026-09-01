#!/usr/bin/env python3
"""Pure admission core for the O-008 formal-cycle evidence packet (schema v2).

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
from collections.abc import Callable, Mapping, Sequence
from dataclasses import dataclass
from typing import Any, Final, NoReturn

import yaml  # type: ignore[import-untyped]

from tools.scan_lean_proof_placeholders_v1 import ScanError, scan_text, strip_lean_noncode

# ---------------------------------------------------------------------------
# Closed constants
# ---------------------------------------------------------------------------

PACKET_SCHEMA_V2: Final = "zenodex/o008-formal-cycle-evidence/v2"
REPORT_SCHEMA_V2: Final = "zenodex/o008-formal-cycle-admission-report/v2"
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
PYTHON_TYPES_PATH_V1: Final = "src/core/global_settlement_types_v1.py"
RUST_STATE_PATH_V1: Final = "zk/global_settlement_abi_v1/src/state.rs"
ESSO_MODEL_PATH_V1: Final = "src/kernels/dex/global_claimant_custody_certificate_v1.yaml"
ESSO_GATE_PATH_V1: Final = "tests/formal/test_esso_global_claimant_custody_certificate_v1.py"
LEAN_PROOF_PATH_V1: Final = "lean-mathlib/Proofs/GlobalClaimantCustodyRelationV1.lean"
LEAN_ROOT_PATH_V1: Final = "lean-mathlib/Proofs.lean"
LEAN_TOOLCHAIN_PATH_V1: Final = "lean-mathlib/lean-toolchain"
LEAN_GATE_PATH_V1: Final = "tests/formal/test_lean_global_claimant_custody_relation_v1.py"
THV1_PATH_V1: Final = (
    "tests/evidence/test_hygiene/THV1-20260901-o008-formal-cycle-admission-v2.json"
)
BLUEPRINT_PATH_V1: Final = "docs/research/ZENODEX_GLOBAL_FUNCTIONAL_CORE_FORMAL_BLUEPRINT_V1.md"
PRIOR_ESSO_GATE_PATH_V1: Final = "tests/formal/test_esso_global_settlement_core_v1.py"
PRIOR_THV1_PATH_V1: Final = (
    "tests/evidence/test_hygiene/"
    "THV1-20260901-global-settlement-formal-core-semantic-restage-v1.json"
)

SOURCE_PIN_ROLES_V1: Final[tuple[tuple[str, str], ...]] = (
    (PYTHON_REFINEMENT_PATH_V1, "python_visible_necessary_checks"),
    (RUST_REFINEMENT_PATH_V1, "rust_visible_necessary_checks"),
    (PYTHON_TYPES_PATH_V1, "python_v1_wire_schema"),
    (RUST_STATE_PATH_V1, "rust_v1_wire_schema"),
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
    (THV1_PATH_V1, "test_hygiene_evidence_packet"),
    (BLUEPRINT_PATH_V1, "corrected_prior_formal_blueprint"),
    (PRIOR_ESSO_GATE_PATH_V1, "prior_model_semantic_restage_gate"),
    (PRIOR_THV1_PATH_V1, "append_only_semantic_correction_packet"),
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
    PYTHON_REFINEMENT_PATH_V1,
    RUST_REFINEMENT_PATH_V1,
)

PACKET_KEYS_V2: Final[frozenset[str]] = frozenset(
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
    "ESSO proves the bounded exact claimant/control-domain partition inductive with Z3 and CVC5"
    " under five substantive invariants",
    "Lean proves the bounded necessary relation, the exact current-profile relation, exact"
    " deposit/drain preservation, strict weakening of the aggregate and reserve-inclusive"
    " predicates, reserve independence, and V1 terminal control-domain information loss",
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


def _validate_json_value(value: object, context: str) -> None:
    if value is None or type(value) in {bool, int, str}:
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
    if packet.get("schema") != PACKET_SCHEMA_V2:
        _reject("PACKET_SCHEMA_DRIFT", "schema", f"expected {PACKET_SCHEMA_V2}")
    if raw != canonical_packet_bytes_v1(packet):
        _reject("PACKET_JSON_NONCANONICAL", PACKET_JSON_PATH_V1, "noncanonical JSON encoding")
    if frozenset(packet) != PACKET_KEYS_V2:
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


def _top_level_class(module: ast.Module, class_name: str, path: str) -> ast.ClassDef:
    found = [n for n in module.body if isinstance(n, ast.ClassDef) and n.name == class_name]
    if not found:
        _reject("PYTHON_CLASS_MISSING", path, class_name)
    if len(found) > 1:
        _reject("PYTHON_CLASS_AMBIGUOUS", path, class_name)
    return found[0]


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


def _canonical_keys(node: ast.ClassDef) -> tuple[str, ...]:
    for item in node.body:
        if isinstance(item, ast.FunctionDef) and item.name == "to_canonical":
            for statement in ast.walk(item):
                if isinstance(statement, ast.Return) and isinstance(statement.value, ast.Dict):
                    keys = statement.value.keys
                    return tuple(str(getattr(k, "value", "")) for k in keys)
    return ()


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
        canonical_keys=_canonical_keys(node),
    )


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
    for char in body:
        depth += {"(": 1, "[": 1, "<": 1, ")": -1, "]": -1, ">": -1}.get(char, 0)
        if char == "," and depth == 0:
            items.append("".join(current))
            current = []
        else:
            current.append(char)
    items.append("".join(current))
    return [item for item in items if item.strip()]


def _strip_rust_field_prefix(item: str) -> str:
    text = item.strip()
    while text.startswith("#["):
        end = text.find("]")
        text = text[end + 1 :].lstrip() if end >= 0 else ""
    text = re.sub(r"^pub(?:\([^)]*\))?\s+", "", text)
    return text


def _rust_fields(body: str, path: str) -> tuple[tuple[str, str], ...]:
    fields: list[tuple[str, str]] = []
    for item in _split_depth_zero_commas(body):
        match = _RUST_FIELD_RE.match(_strip_rust_field_prefix(item))
        if match is None:
            _reject("RUST_FIELD_UNPARSEABLE", path, item.strip()[:60])
        fields.append((match.group(1), " ".join(match.group(2).split())))
    return tuple(fields)


def rust_struct_shape_v1(source: bytes, struct_name: str, path: str) -> StructShapeV1:
    """Return the ordered fields of a brace struct and whether serde denies unknown fields."""

    try:
        text = source.decode("utf-8")
    except UnicodeDecodeError as exc:
        _reject("RUST_SOURCE_UNPARSEABLE", path, type(exc).__name__)
    code = strip_rust_noncode_v1(text)
    start, body_start, body_end = _rust_struct_body(code, struct_name, path)
    prefix = code[max(0, start - 600) : start]
    attrs = _RUST_ATTR_PREFIX_RE.search(prefix)
    attr_text = " ".join(attrs.group(1).split()) if attrs else ""
    return StructShapeV1(
        line=code.count("\n", 0, start) + 1,
        fields=_rust_fields(code[body_start:body_end], path),
        deny_unknown_fields="#[serde(deny_unknown_fields)]" in attr_text,
    )


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


def _project_information_loss(snapshot: SubjectSnapshotV1) -> dict[str, object]:
    python_source = _blob(snapshot, PYTHON_TYPES_PATH_V1).data
    rust_source = _blob(snapshot, RUST_STATE_PATH_V1).data
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
        "opaque_bindings": list(OPAQUE_BINDINGS_V1),
        "accepted_known_gaps": list(ACCEPTED_KNOWN_GAPS_V1),
        "formal_result": INFORMATION_LOSS_FORMAL_RESULT_V1,
        "mounted_exploit_claim": False,
    }


def _check_thv1_packet(snapshot: SubjectSnapshotV1) -> None:
    raw = _blob(snapshot, THV1_PATH_V1).data
    packet = decode_json_object_v1(raw, context=THV1_PATH_V1, require_canonical=False)
    pins = packet.get("source_pins")
    if not isinstance(pins, list) or not all(isinstance(pin, dict) for pin in pins):
        _reject("THV1_SHAPE", THV1_PATH_V1, "source_pins must be a list of objects")
    by_path = {str(pin.get("path")): str(pin.get("sha256")) for pin in pins}
    circular = [path for path in (PACKET_JSON_PATH_V1, PACKET_MD_PATH_V1) if path in by_path]
    if circular:
        _reject("THV1_PINS_PACKET_CIRCULAR", THV1_PATH_V1, ",".join(circular))
    for path in THV1_REQUIRED_PIN_PATHS_V1:
        if by_path.get(path) != _blob(snapshot, path).sha256:
            _reject("THV1_PIN_DRIFT", THV1_PATH_V1, path)


AUTHOR_RUN_KEYS_V1: Final[frozenset[str]] = frozenset({"command_id", "exit_code", "comparable"})


def _validate_replay_run(run: object, index: int) -> dict[str, object]:
    if not isinstance(run, dict) or set(run) != AUTHOR_RUN_KEYS_V1:
        _reject(
            "REPLAY_RECORD_SHAPE",
            f"proof_replay.author_record.runs[{index}]",
            "exactly command_id, exit_code, comparable",
        )
    command_id = run.get("command_id")
    if command_id not in REPLAY_COMMAND_IDS_V1:
        _reject("REPLAY_RECORD_SHAPE", f"proof_replay.author_record.runs[{index}]", str(command_id))
    exit_code = run.get("exit_code")
    if type(exit_code) is not int or exit_code != 0:
        _reject("REPLAY_RECORD_EXIT_NONZERO", f"proof_replay.author_record.runs[{index}]", str(exit_code))
    for key, value in run.items():
        if isinstance(value, str) and value.startswith("/"):
            _reject("REPLAY_RECORD_MACHINE_PATH", f"proof_replay.author_record.runs[{index}].{key}", value)
    return dict(run)


def validate_author_replay_record_v1(record: object) -> dict[str, object]:
    """Validate a packet author's proof-replay observation record."""

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
    validated = [_validate_replay_run(run, index) for index, run in enumerate(runs)]
    if tuple(str(run["command_id"]) for run in validated) != REPLAY_COMMAND_IDS_V1:
        _reject("REPLAY_RECORD_SHAPE", "proof_replay.author_record.runs", "one run per command in order")
    return {"status": "EXECUTED", "runs": validated, "toolchain": record["toolchain"]}


def project_packet_v1(
    snapshot: SubjectSnapshotV1,
    *,
    created_date: str,
    author_replay_record: object,
) -> dict[str, Any]:
    """Return the only admissible packet content for the subject snapshot."""

    if _DATE_RE.fullmatch(created_date) is None:
        _reject("CREATED_DATE_INVALID", "created_date", created_date)
    for field, value in (("subject_commit", snapshot.subject_commit),
                         ("subject_parent", snapshot.subject_parent),
                         ("subject_tree", snapshot.subject_tree)):
        if _HEX40_RE.fullmatch(value) is None:
            _reject("SUBJECT_COMMIT_INVALID", field, value)
    projection = {
        "schema": PACKET_SCHEMA_V2,
        "created_date": created_date,
        "subject_commit": snapshot.subject_commit,
        "subject_parent": snapshot.subject_parent,
        "subject_tree": snapshot.subject_tree,
        "packet_commit_parent": snapshot.subject_commit,
        "packet_write_set": [{"status": s, "path": p} for s, p in PACKET_WRITE_SET_V1],
        "claim_ceiling": dict(CLAIM_CEILING_V1),
        "completion_scope": list(COMPLETION_SCOPE_V1),
        "source_pins": _project_source_pins(snapshot),
        "esso_evidence": _project_esso(snapshot),
        "lean_evidence": _project_lean(snapshot),
        "v1_information_loss": _project_information_loss(snapshot),
        "lane_source_data": [
            {"lane_id": lane, "status": status, "missing": missing}
            for lane, status, missing in LANE_SOURCE_DATA_V1
        ],
        "required_sidecar": json.loads(json.dumps(REQUIRED_SIDECAR_V1)),
        "proof_replay": {
            "commands": [command.to_json() for command in REPLAY_COMMANDS_V1],
            "author_record": validate_author_replay_record_v1(author_replay_record),
            "admission_semantics": ADMISSION_SEMANTICS_V1,
        },
        "nonclaims": list(NONCLAIMS_V1),
    }
    # Pin-consistency checks run last so a structural finding in a source is
    # reported before the derived pin drift it also causes.
    _check_lean_gate(snapshot, tuple(name for _, name in THEOREM_INVENTORY_V1))
    _check_thv1_packet(snapshot)
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
        folded = " ".join(text.split()).lower()
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
    validate_author_replay_record_v1(replay.get("author_record"))


def check_projection_v1(packet: Mapping[str, Any], expected: Mapping[str, Any]) -> None:
    if canonical_packet_bytes_v1(dict(packet)) != canonical_packet_bytes_v1(dict(expected)):
        for key in sorted(PACKET_KEYS_V2):
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
    for path in SOURCE_PIN_PATHS_V1:
        blob = _blob(snapshot, path)
        if current.head_blob_ids.get(path) != blob.git_blob:
            drift.append(path)
        elif current.worktree_sha256.get(path) != blob.sha256:
            drift.append(path)
    return tuple(drift)


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
    if versions.get("esso_code_hash") != esso.get("esso_code_commit"):
        _reject("REPLAY_ESSO_CODE_COMMIT_DRIFT", obs.command_id, str(versions.get("esso_code_hash")))
    solvers = _solver_versions(versions.get("solvers"), esso.get("solvers"))
    if solvers is None:
        _reject("REPLAY_SOLVER_VERSION_DRIFT", obs.command_id, str(versions.get("solvers")))
    if not isinstance(fingerprints, list) or len(set(fingerprints)) != 1:
        _reject("REPLAY_FINGERPRINT_NONDETERMINISTIC", obs.command_id, str(fingerprints))
    if fingerprints[0] != esso.get("fingerprint"):
        _reject("REPLAY_FINGERPRINT_DRIFT", obs.command_id, str(fingerprints[0]))
    return {"verdict": "VERIFIED", "fingerprint": fingerprints[0], "solvers": solvers}


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
    return ReplayEvaluationV1(status, tuple(errors), tuple(runs))


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
    lines += ["", "## Proof replay", "",
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
        "schema": REPORT_SCHEMA_V2,
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
