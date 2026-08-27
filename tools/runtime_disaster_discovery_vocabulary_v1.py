#!/usr/bin/env python3
"""Closed vocabulary, limits, and the pinned source universe (WholeEconomyDisasterCoverageV1).

Every enumeration here is closed by construction.  The nine lifecycle phases
and twelve invariant families are the grid axes; they are vocabulary, not
applicability claims.  Nothing here grants authority.
"""

from __future__ import annotations

from enum import Enum
from typing import Final

REGISTRY_SCHEMA_V1: Final = "zenodex/whole-economy-disaster-coverage-registry/v1"
PACKET_SCHEMA_V1: Final = "zenodex/whole-economy-disaster-discovery-packet/v1"
RECEIPT_CHECK_SCHEMA_V1: Final = "zenodex/whole-economy-disaster-receipt-check/v1"
OBLIGATION_ID_PREFIX_V1: Final = "WEDC1-"
CLAIM_CEILING_V1: Final = "RESEARCH_ONLY_NO_AUTHORITY"
REGISTRY_STATUS_V1: Final = "RESEARCH_ONLY_DENOMINATOR_INCOMPLETE"
REGISTRY_PATH_V1: Final = "tools/runtime_disaster_discovery_registry_v1.json"
IMPLEMENTATION_BASE_COMMIT_V1: Final = "c52c71d01a3edf3e298a840d41345abdc2d6d26d"
IMPLEMENTATION_BASE_TREE_V1: Final = "7978c0df78428e806e5f19281df537fe1cfc7451"
# Hard V1 denominator minima.  A registry may raise these, never lower them.
V1_FLOOR_CAPABILITIES: Final = 103
V1_FLOOR_ROUTES: Final = 4
V1_FLOOR_EXCLUSIONS: Final = 4
V1_FLOOR_APPLICABILITY_CELLS: Final = 11_988
HISTORICAL_STRICT_RELEASE_CLOSURE_V1: Final = "0_OF_967_MANIFEST_DERIVED_MINIMUM_EVIDENCE_CELLS"
HISTORICAL_MINIMUM_RELEASE_EVIDENCE_CELLS_V1: Final = 967
EXPECTED_M6_CAPABILITY_MANIFEST_ROOT_V1: Final = (
    "0x21efc162df198e40a0aa942fcb69b7a5f5cc0f93907b11a3c6b25359e4a464bb"
)
M6_MANIFEST_HASH_DOMAIN_V1: Final = "m6-capability-manifest-v1"
COVERAGE_RATIO_WITHHELD_V1: Final = "WITHHELD"

MAX_SOURCE_BYTES_V1: Final = 4 * 1024 * 1024
MAX_REGISTRY_BYTES_V1: Final = 2 * 1024 * 1024
MAX_PACKET_BYTES_V1: Final = 16 * 1024 * 1024
MAX_RUNNER_ARGV_V1: Final = 8
MAX_RUNNER_TIMEOUT_S_V1: Final = 3600
MAX_RUNNER_OUTPUT_BYTES_V1: Final = 1024 * 1024
MAX_GIT_OUTPUT_BYTES_V1: Final = 1024 * 1024
MAX_PRIORITY_SCORE_V1: Final = 100

LEGACY_BRIDGE_SCHEMAS_V1: Final = frozenset(
    {
        "zenodex/stateful-scenario-candidate/v1",
        "zenodex/stateful-scenario-candidate-check/v1",
        "zenodex/stateful-shapeforge-promotion-bridge/v1",
        "zenodex/stateful-disaster-reachability-ratchet/v1",
        "zenodex/stateful-scenario-run-receipt/v1",
        "zenodex/stateful-disaster-proof-obligation-packet/v1",
        "zenodex/stateful-disaster-proof-obligation-closure-receipt/v1",
        "zenodex/stateful-minimal-witness-language-audit/v1",
        "zenodex/stateful-cross-surface-witness-exploration/v1",
        "zenodex/stateful-disaster-search-expansion-plan/v1",
        "zenodex/stateful-disaster-search-expansion-receipt/v1",
    }
)
VM_GATE_IDS_V1: Final = tuple(f"VM-{index:02d}" for index in range(1, 13))
ALLOWED_RUNNER_FLAGS_V1: Final = frozenset({"-q", "--json", "--check"})
RUNNER_PROGRAM_V1: Final = "python3"
M6_LANE_ORDER_V1: Final = (
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


class TargetKindV1(str, Enum):
    CAPABILITY = "CAPABILITY"
    CROSS_LANE_ROUTE = "CROSS_LANE_ROUTE"
    EXPLICIT_EXCLUSION = "EXPLICIT_EXCLUSION"


class LifecyclePhaseV1(str, Enum):
    """Nine closed value-lifecycle phases of the applicability grid."""

    ADMISSION = "ADMISSION"
    ACTIVATION = "ACTIVATION"
    ACCRUAL = "ACCRUAL"
    TRANSFER = "TRANSFER"
    CLAIM = "CLAIM"
    PUBLICATION = "PUBLICATION"
    LIQUIDATION_RECOVERY = "LIQUIDATION_RECOVERY"
    TERMINAL_CLOSE = "TERMINAL_CLOSE"
    MIGRATION_RETIREMENT = "MIGRATION_RETIREMENT"


class InvariantFamilyV1(str, Enum):
    """Twelve closed invariant families; eight are the aggregate families."""

    VALUE_CONSERVATION = "VALUE_CONSERVATION"
    AUTHORIZATION_AUTHORITY = "AUTHORIZATION_AUTHORITY"
    REPLAY_OCCURRENCE_UNIQUENESS = "REPLAY_OCCURRENCE_UNIQUENESS"
    CANONICAL_ENCODING_BINDING = "CANONICAL_ENCODING_BINDING"
    ORDERED_EPOCHS = "ORDERED_EPOCHS"
    PROFILE_RELEASE_COEXISTENCE = "PROFILE_RELEASE_COEXISTENCE"
    MIGRATION_WRITER_RETIREMENT = "MIGRATION_WRITER_RETIREMENT"
    ATOMIC_PUBLICATION = "ATOMIC_PUBLICATION"
    OUTBOX_FINALITY = "OUTBOX_FINALITY"
    RECOVERY_ADMIN = "RECOVERY_ADMIN"
    SIDE_COVERT_CHANNELS = "SIDE_COVERT_CHANNELS"
    RESOURCE_CEILINGS = "RESOURCE_CEILINGS"


AGGREGATE_FAMILIES_V1: Final = (
    InvariantFamilyV1.ORDERED_EPOCHS,
    InvariantFamilyV1.PROFILE_RELEASE_COEXISTENCE,
    InvariantFamilyV1.MIGRATION_WRITER_RETIREMENT,
    InvariantFamilyV1.ATOMIC_PUBLICATION,
    InvariantFamilyV1.OUTBOX_FINALITY,
    InvariantFamilyV1.RECOVERY_ADMIN,
    InvariantFamilyV1.SIDE_COVERT_CHANNELS,
    InvariantFamilyV1.RESOURCE_CEILINGS,
)


class ApplicabilityV1(str, Enum):
    REQUIRED = "REQUIRED"
    BLOCKED_SEMANTICS = "BLOCKED_SEMANTICS"
    APPLICABILITY_UNKNOWN = "APPLICABILITY_UNKNOWN"
    NOT_APPLICABLE_PROVED = "NOT_APPLICABLE_PROVED"


class EvidenceStatusV1(str, Enum):
    UNSPECIFIED_SEMANTICS = "UNSPECIFIED_SEMANTICS"
    UNKNOWN_REACHABILITY = "UNKNOWN_REACHABILITY"
    SEARCH_PENDING = "SEARCH_PENDING"
    EXTERNAL_PREMISE = "EXTERNAL_PREMISE"
    STALE_EVIDENCE = "STALE_EVIDENCE"
    INCONCLUSIVE = "INCONCLUSIVE"
    NOT_WITNESSED_IN_TESTS = "NOT_WITNESSED_IN_TESTS"
    MODEL_PROVED_UNREACHABLE = "MODEL_PROVED_UNREACHABLE"
    UNREACHABLE_BY_CONSTRUCTION = "UNREACHABLE_BY_CONSTRUCTION"
    RUNTIME_REFINEMENT_CLOSED = "RUNTIME_REFINEMENT_CLOSED"
    DISABLED_PROVED_NO_WRITER = "DISABLED_PROVED_NO_WRITER"
    WITNESSED_REACHABLE = "WITNESSED_REACHABLE"


STATUS_RANK_V1: Final = {status: rank for rank, status in enumerate(EvidenceStatusV1)}
CLOSURE_STATUSES_V1: Final = frozenset(
    {
        EvidenceStatusV1.MODEL_PROVED_UNREACHABLE,
        EvidenceStatusV1.UNREACHABLE_BY_CONSTRUCTION,
        EvidenceStatusV1.RUNTIME_REFINEMENT_CLOSED,
        EvidenceStatusV1.DISABLED_PROVED_NO_WRITER,
    }
)
BOUNDED_STATUSES_V1: Final = CLOSURE_STATUSES_V1 | {EvidenceStatusV1.NOT_WITNESSED_IN_TESTS}


class DenominatorStateV1(str, Enum):
    DENOMINATOR_INCOMPLETE = "DENOMINATOR_INCOMPLETE"
    DENOMINATOR_CLOSED_EXACT = "DENOMINATOR_CLOSED_EXACT"


class RegistrySectionStateV1(str, Enum):
    INCOMPLETE = "INCOMPLETE"
    COMPLETE = "COMPLETE"


class SourceRoleV1(str, Enum):
    SEMANTIC_SOURCE = "SEMANTIC_SOURCE"
    PROFILE_RELEASE = "PROFILE_RELEASE"
    TOOLCHAIN = "TOOLCHAIN"
    CHECKER_SOURCE = "CHECKER_SOURCE"


class PathKindV1(str, Enum):
    REGULAR = "REGULAR"
    SYMLINK = "SYMLINK"
    DIRECTORY = "DIRECTORY"
    FIFO = "FIFO"
    DEVICE = "DEVICE"
    SOCKET = "SOCKET"
    MISSING = "MISSING"
    OVERSIZE = "OVERSIZE"
    OTHER = "OTHER"


class HeadBindingV1(str, Enum):
    HEAD_BLOB_MATCH = "HEAD_BLOB_MATCH"
    NOT_IN_HEAD = "NOT_IN_HEAD"
    HEAD_BLOB_MISMATCH = "HEAD_BLOB_MISMATCH"
    PROBE_UNAVAILABLE = "PROBE_UNAVAILABLE"


class ExecutionPremiseV1(str, Enum):
    CLEAN_WORKTREE_HEAD_BOUND = "CLEAN_WORKTREE_HEAD_BOUND"
    EXTERNAL_PREMISE_MUTABLE_WORKTREE = "EXTERNAL_PREMISE_MUTABLE_WORKTREE"


class OracleKindV1(str, Enum):
    EXIT_CODE_ONLY = "EXIT_CODE_ONLY"
    TEST_RUNNER = "TEST_RUNNER"
    DETERMINISTIC_CHECKER = "DETERMINISTIC_CHECKER"
    FORMAL_PROVER = "FORMAL_PROVER"


class OracleVerdictV1(str, Enum):
    PASS = "PASS"
    FAIL = "FAIL"
    INCONCLUSIVE = "INCONCLUSIVE"


class WitnessKindV1(str, Enum):
    NONE = "NONE"
    BAD_TRACE_WITNESS = "BAD_TRACE_WITNESS"
    REPLAY_TRANSCRIPT = "REPLAY_TRANSCRIPT"


class CertificateKindV1(str, Enum):
    MODEL_PROOF = "MODEL_PROOF"
    CONSTRUCTION_PROOF = "CONSTRUCTION_PROOF"
    REFINEMENT_PROOF = "REFINEMENT_PROOF"
    NO_WRITER_PROOF = "NO_WRITER_PROOF"


class NoEffectSurfaceV1(str, Enum):
    STATE = "STATE"
    HISTORY = "HISTORY"
    RECEIPT = "RECEIPT"
    OUTBOX = "OUTBOX"


class NoEffectOutcomeV1(str, Enum):
    UNCHANGED = "UNCHANGED"
    CHANGED = "CHANGED"
    UNOBSERVED = "UNOBSERVED"


class InventoryUniverseV1(str, Enum):
    DANGEROUS_SURFACE = "DANGEROUS_SURFACE"
    WRITER_ENTRYPOINT = "WRITER_ENTRYPOINT"
    WRITER_COVERAGE_ROW = "WRITER_COVERAGE_ROW"
    POKAYOKE_SCENARIO = "POKAYOKE_SCENARIO"
    BRIDGE_EXPANSION_AXIS = "BRIDGE_EXPANSION_AXIS"
    SHAPEFORGE_CROSS_SLICE_INVARIANT = "SHAPEFORGE_CROSS_SLICE_INVARIANT"
    SHAPEFORGE_SCENARIO_TRANSFORM = "SHAPEFORGE_SCENARIO_TRANSFORM"
    AGGREGATE_FAMILY = "AGGREGATE_FAMILY"


UNSPECIFIED_V1: Final = "UNSPECIFIED"
CLOSURE_MODES_V1: Final = (
    UNSPECIFIED_V1,
    "BOUNDED_TEST_SEARCH",
    "MODEL_PROOF",
    "CONSTRUCTION_PROOF",
    "RUNTIME_REFINEMENT",
    "DISABLED_NO_WRITER",
)
ATTACK_FAMILIES_V1: Final = (
    UNSPECIFIED_V1,
    "ADVERSARY_MALLORY",
    "SEQUENCER_REORDERING",
    "PROOF_AGGREGATOR",
    "ORACLE_REPORTER",
    "GOVERNANCE_OPERATOR",
    "COLLUDING_COALITION",
    "ENVIRONMENT_FAULT",
)

# Closed source universe.  The registry must pin exactly these paths.
PLAN_PATH_V1: Final = "docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V2.json"
M6_MANIFEST_PATH_V1: Final = "docs/research/ZENODEX_M6_CAPABILITY_MANIFEST_V1.json"
SHAPEFORGE_SEED_PATH_V1: Final = "docs/zenodex/shapeforge_promoted/zenodex_world_model.seed.json"
DANGEROUS_SURFACES_PATH_V1: Final = "tools/acceptance_tcb_dangerous_surfaces.json"
WRITER_INVENTORY_PATH_V1: Final = "tools/m6_writer_inventory_manifest_v1.json"
POKAYOKE_MATRIX_PATH_V1: Final = "tools/adversarial_hardening_pokayoke_matrix.json"
STATEFUL_BRIDGE_PATH_V1: Final = "tools/stateful_scenario_bridge.py"
PROFILE_RELEASE_PATH_V1: Final = "config/proof_profiles/zeno_ledger_profiles.json"
CHECKER_SOURCE_PATHS_V1: Final = (
    "tools/check_runtime_disaster_discovery_receipt.py",
    "tools/run_runtime_disaster_discovery.py",
    "tools/runtime_disaster_discovery.py",
    "tools/runtime_disaster_discovery_evidence_v1.py",
    "tools/runtime_disaster_discovery_inventory_v1.py",
    "tools/runtime_disaster_discovery_packet_v1.py",
    "tools/runtime_disaster_discovery_ports_v1.py",
    "tools/runtime_disaster_discovery_primitives_v1.py",
    "tools/runtime_disaster_discovery_registry_v1.py",
    "tools/runtime_disaster_discovery_sources_v1.py",
    "tools/runtime_disaster_discovery_subject_v1.py",
    "tools/runtime_disaster_discovery_vocabulary_v1.py",
)
TOOLCHAIN_PATHS_V1: Final = (
    "lean-mathlib/lean-toolchain",
    "pyproject.toml",
    "requirements-agents.lock.txt",
    "requirements-core.lock.txt",
    "requirements-dev.lock.txt",
)
REQUIRED_SOURCE_PINS_V1: Final = tuple(
    sorted(
        (
            (PLAN_PATH_V1, SourceRoleV1.SEMANTIC_SOURCE),
            (M6_MANIFEST_PATH_V1, SourceRoleV1.SEMANTIC_SOURCE),
            (SHAPEFORGE_SEED_PATH_V1, SourceRoleV1.SEMANTIC_SOURCE),
            (DANGEROUS_SURFACES_PATH_V1, SourceRoleV1.SEMANTIC_SOURCE),
            (WRITER_INVENTORY_PATH_V1, SourceRoleV1.SEMANTIC_SOURCE),
            (POKAYOKE_MATRIX_PATH_V1, SourceRoleV1.SEMANTIC_SOURCE),
            (STATEFUL_BRIDGE_PATH_V1, SourceRoleV1.SEMANTIC_SOURCE),
            (PROFILE_RELEASE_PATH_V1, SourceRoleV1.PROFILE_RELEASE),
            *((path, SourceRoleV1.TOOLCHAIN) for path in TOOLCHAIN_PATHS_V1),
            *((path, SourceRoleV1.CHECKER_SOURCE) for path in CHECKER_SOURCE_PATHS_V1),
        )
    )
)
REQUIRED_SOURCE_PATHS_V1: Final = tuple(path for path, _role in REQUIRED_SOURCE_PINS_V1)
