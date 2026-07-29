"""Closed policy constants for the FCIS M5-P4B5A ATDD checker."""

from __future__ import annotations

B1B2_PROMOTION_GATE = (
    "new committed ATDD contract revision + "
    "exact B1B-1 implementation approval identity + "
    "exact B1B-2 design approval identity + "
    "explicit user implementation authority"
)

INTEGRATION_ACCEPTANCE_ID = "ATDD-B1B1-009"

CASE_LIFECYCLE = {
    "precondition": frozenset({"ATDD-B1B1-001"}),
    "implementation": frozenset(
        {
            "ATDD-B1B1-002",
            "ATDD-B1B1-003",
            "ATDD-B1B1-004",
            "ATDD-B1B1-005",
            "ATDD-B1B1-006",
            "ATDD-B1B1-007",
            "ATDD-B1B1-008",
            "ATDD-B1B1-011",
        }
    ),
    "phase_gate": frozenset(
        {
            "ATDD-B1B1-009",
            "ATDD-B1B1-010",
            "ATDD-B1B1-012",
        }
    ),
    "design_obligation": frozenset(
        {f"ATDD-B1B2-{index:03d}" for index in range(1, 9)}
    ),
    "red_required": frozenset(
        {
            "ATDD-B1B1-002",
            "ATDD-B1B1-008",
            "ATDD-B1B1-011",
        }
    ),
    "mutation_kill_required": frozenset(
        {
            "ATDD-B1B1-003",
            "ATDD-B1B1-004",
            "ATDD-B1B1-005",
            "ATDD-B1B1-006",
            "ATDD-B1B1-007",
        }
    ),
    "live_evidence": frozenset(
        {
            "ATDD-B1B1-001",
            "ATDD-B1B1-009",
        }
    ),
}

B1B2_DESIGN_GATE = {
    "approval_verdict": "APPROVE_B1B2_SOURCE_BOUND_MIGRATION_DESIGN_UNMOUNTED",
    "design_document_path": (
        "docs/research/"
        "FCIS_M5_P4B5A_B1B2_PINNED_MIGRATION_REFERENCE_DESIGN_20260729.md"
    ),
    "design_manifest_path": (
        "docs/research/prompts/"
        "fcis_m5_p4b5a_b1b2_pinned_migration_review_v1/SOURCE_MANIFEST.sha256"
    ),
    "design_packet": {
        "builder_command": (
            "python3 -m "
            "tools.build_fcis_b1b2_pinned_migration_review_packet --check"
        ),
        "builder_path": (
            "tools/build_fcis_b1b2_pinned_migration_review_packet.py"
        ),
        "inventory_rule": (
            "all committed paths changed from the exact independently approved "
            "B1B-1 packet commit through the design target, plus immutable "
            "authority and exact B1B-1 approval sources"
        ),
        "manifest_self_hash": "excluded",
        "packet_relation": (
            "documentation-only packet commit exactly one child of design target"
        ),
    },
    "implementation_requires": [
        "new committed ATDD contract revision",
        "exact B1B-1 implementation approval identity",
        "exact B1B-2 design approval identity",
        "explicit user implementation authority",
    ],
    "review_prompt_path": (
        "docs/research/prompts/fcis_m5_p4b5a_atdd_subagents_v1/"
        "B1B2_REVIEW_PROMPT.md"
    ),
    "status": "planned_review_only",
}

FORBIDDEN_CHANGED_PATH_PATTERNS = (
    "src/core/fcis_fee_distribution_configuration_content_validation.py",
    "src/core/fcis_b1b_*migration*candidate*.py",
    "src/core/fcis_b1b_*publication*.py",
    "src/core/fcis_b1b_*state_bound*.py",
    "src/state/*fcis*b1b*",
    "integration/*fcis*b1b*",
)

PATH_OWNERS = (
    {
        "acceptance_ids": ["ATDD-B1B1-009"],
        "pattern": "docs/research/FCIS_M5_P4B5A_ATDD_EXECUTION_CONTRACT_20260729.md",
    },
    {
        "acceptance_ids": ["ATDD-B1B1-009"],
        "pattern": (
            "docs/research/prompts/fcis_m5_p4b5a_atdd_subagents_v1/*"
        ),
    },
    {
        "acceptance_ids": ["ATDD-B1B1-009"],
        "pattern": "tools/check_fcis_m5_p4b5a_atdd_contract.py",
    },
    {
        "acceptance_ids": ["ATDD-B1B1-009"],
        "pattern": "tools/fcis_m5_p4b5a_atdd_policy.py",
    },
    {
        "acceptance_ids": ["ATDD-B1B1-009"],
        "pattern": "tools/fcis_m5_p4b5a_atdd_validation.py",
    },
    {
        "acceptance_ids": ["ATDD-B1B1-009"],
        "pattern": "tests/tools/test_check_fcis_m5_p4b5a_atdd_contract.py",
    },
    {
        "acceptance_ids": [
            "ATDD-B1B1-003",
            "ATDD-B1B1-004",
            "ATDD-B1B1-005",
            "ATDD-B1B1-007",
        ],
        "pattern": "src/core/fcis_b1b_authority_values.py",
    },
    {
        "acceptance_ids": [
            "ATDD-B1B1-003",
            "ATDD-B1B1-005",
        ],
        "pattern": "src/core/fcis_b1b_authority_schema.py",
    },
    {
        "acceptance_ids": [
            "ATDD-B1B1-003",
            "ATDD-B1B1-005",
            "ATDD-B1B1-006",
        ],
        "pattern": "src/core/fcis_b1b_authority_codec.py",
    },
    {
        "acceptance_ids": [
            "ATDD-B1B1-003",
            "ATDD-B1B1-004",
            "ATDD-B1B1-005",
            "ATDD-B1B1-007",
        ],
        "pattern": "src/core/fcis_b1b_authority_admission.py",
    },
    {
        "acceptance_ids": [
            "ATDD-B1B1-003",
            "ATDD-B1B1-004",
            "ATDD-B1B1-005",
            "ATDD-B1B1-006",
            "ATDD-B1B1-007",
        ],
        "pattern": "tests/core/test_fcis_b1b_authority_*.py",
    },
    {
        "acceptance_ids": [
            "ATDD-B1B1-003",
            "ATDD-B1B1-005",
            "ATDD-B1B1-007",
        ],
        "pattern": "tests/core/test_fcis_b1b1_carriers.py",
    },
    {
        "acceptance_ids": ["ATDD-B1B1-006"],
        "pattern": "tests/fixtures/fcis_b1b_authority_v2_golden.json",
    },
    {
        "acceptance_ids": ["ATDD-B1B1-006"],
        "pattern": "tools/build_fcis_b1b_authority_v2_golden.py",
    },
    {
        "acceptance_ids": [
            "ATDD-B1B1-008",
            "ATDD-B1B1-010",
            "ATDD-B1B1-011",
        ],
        "pattern": "tools/check_fcis_b1b_revision34_contract.py",
    },
    {
        "acceptance_ids": ["ATDD-B1B1-008", "ATDD-B1B1-011"],
        "pattern": "tests/tools/test_check_fcis_b1b_revision34_contract.py",
    },
    {
        "acceptance_ids": ["ATDD-B1B1-008"],
        "pattern": "tools/fcis_b1b_revision34_adversarial_model.py",
    },
    {
        "acceptance_ids": ["ATDD-B1B1-006"],
        "pattern": (
            "rust-runtime/crates/zenodex-runtime-core/src/fcis_b1b_authority.rs"
        ),
    },
    {
        "acceptance_ids": ["ATDD-B1B1-006"],
        "pattern": "rust-runtime/crates/zenodex-runtime-core/src/lib.rs",
    },
    {
        "acceptance_ids": [
            "ATDD-B1B1-001",
            "ATDD-B1B1-002",
            "ATDD-B1B1-006",
            "ATDD-B1B1-008",
            "ATDD-B1B1-012",
        ],
        "pattern": ".github/workflows/fcis-b1b-revision34.yml",
    },
    {
        "acceptance_ids": ["ATDD-B1B1-012"],
        "pattern": "docs/research/FCIS_M5_P4B5A_B1B1_IMPLEMENTATION_REPORT_*.md",
    },
    {
        "acceptance_ids": ["ATDD-B1B1-012"],
        "pattern": (
            "docs/research/prompts/"
            "fcis_m5_p4b5a_b1b1_implementation_review_v1/*"
        ),
    },
    {
        "acceptance_ids": ["ATDD-B1B1-012"],
        "pattern": "tools/build_fcis_b1b1_implementation_review_packet.py",
    },
    {
        "acceptance_ids": ["ATDD-B1B1-012"],
        "pattern": "tests/tools/test_build_fcis_b1b1_implementation_review_packet.py",
    },
)


def lifecycle_as_json() -> dict[str, list[str]]:
    """Return deterministic JSON-ready lifecycle sets."""

    all_ids = set().union(
        CASE_LIFECYCLE["precondition"],
        CASE_LIFECYCLE["implementation"],
        CASE_LIFECYCLE["phase_gate"],
        CASE_LIFECYCLE["design_obligation"],
    )
    planned = all_ids - CASE_LIFECYCLE["live_evidence"]
    result = {
        key: sorted(value)
        for key, value in CASE_LIFECYCLE.items()
    }
    result["planned_evidence"] = sorted(planned)
    return result


def path_ownership_as_json() -> dict[str, object]:
    """Return deterministic JSON-ready path ownership."""

    return {
        "forbidden_patterns": list(FORBIDDEN_CHANGED_PATH_PATTERNS),
        "owners": [dict(row) for row in PATH_OWNERS],
    }
