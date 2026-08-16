"""Declarative source contract for the exact-subject G1 entrypoint audit."""

from __future__ import annotations

WRITER_MANIFEST_PATH = "tools/m6_writer_inventory_manifest_v1.json"

PINNED_PATHS = (
    "src/core/m6_safe_mount_v1.py",
    "src/core/m6_safe_mount_transition_v1.py",
    "src/core/m6_safe_mount_types_v1.py",
    "src/core/m6_zrpf_v1.py",
    "src/integration/m6_authority_verifier_v1.py",
    "src/integration/m6_commit_port_v1.py",
    "src/integration/m6_durable_store_v1.py",
    "src/integration/m6_outbox_delivery_journal_v1.py",
    "src/integration/m6_outbox_delivery_v1.py",
    WRITER_MANIFEST_PATH,
)

SURFACE_SPECS: tuple[dict[str, str | None], ...] = (
    {
        "id": "m6_public_candidate_facade",
        "path": "src/core/m6_safe_mount_v1.py",
        "class": None,
        "symbol": "run_m6_transition_v1",
        "kind": "reexport",
        "authority": "candidate_only",
        "status": "RESEARCH_ONLY_CANDIDATE_NO_PUBLICATION",
    },
    {
        "id": "m6_core_transition",
        "path": "src/core/m6_safe_mount_transition_v1.py",
        "class": None,
        "symbol": "run_m6_transition_v1",
        "kind": "definition",
        "authority": "candidate_only",
        "status": "RESEARCH_ONLY_CANDIDATE_NO_PUBLICATION",
    },
    {
        "id": "m6_finality_verifier_port",
        "path": "src/integration/m6_commit_port_v1.py",
        "class": "M6FinalityVerifierV1",
        "symbol": "verify_finality",
        "kind": "definition",
        "authority": "unimplemented_external_verifier_port",
        "status": "PORT_ONLY_NO_IMPLEMENTATION",
    },
    {
        "id": "m6_reference_commit_direct",
        "path": "src/integration/m6_commit_port_v1.py",
        "class": "M6CommitPortV1",
        "symbol": "publish",
        "kind": "definition",
        "authority": "reference_test_commit_shell",
        "status": "M6_RESEARCH_ONLY",
    },
    {
        "id": "m6_reference_commit_zrpf",
        "path": "src/integration/m6_commit_port_v1.py",
        "class": "M6CommitPortV1",
        "symbol": "publish_zrpf",
        "kind": "definition",
        "authority": "reference_test_commit_shell",
        "status": "M6_RESEARCH_ONLY",
    },
    {
        "id": "m6_reference_commit_direct_batch",
        "path": "src/integration/m6_commit_port_v1.py",
        "class": "M6CommitPortV1",
        "symbol": "publish_direct_batch",
        "kind": "definition",
        "authority": "reference_test_commit_shell",
        "status": "M6_RESEARCH_ONLY",
    },
    {
        "id": "m6_research_durable_direct",
        "path": "src/integration/m6_durable_store_v1.py",
        "class": "M6DurableLedgerStoreV1",
        "symbol": "publish",
        "kind": "definition",
        "authority": "research_filesystem_adapter",
        "status": "M6_RESEARCH_ONLY",
    },
    {
        "id": "m6_research_durable_zrpf",
        "path": "src/integration/m6_durable_store_v1.py",
        "class": "M6DurableLedgerStoreV1",
        "symbol": "publish_zrpf",
        "kind": "definition",
        "authority": "research_filesystem_adapter",
        "status": "M6_RESEARCH_ONLY",
    },
    {
        "id": "m6_research_durable_direct_batch",
        "path": "src/integration/m6_durable_store_v1.py",
        "class": "M6DurableLedgerStoreV1",
        "symbol": "publish_direct_batch",
        "kind": "definition",
        "authority": "research_filesystem_adapter",
        "status": "M6_RESEARCH_ONLY",
    },
    {
        "id": "m6_outbox_journal_reserve",
        "path": "src/integration/m6_outbox_delivery_journal_v1.py",
        "class": "M6OutboxDeliveryJournalV1",
        "symbol": "reserve",
        "kind": "definition",
        "authority": "external_effect_journal_only",
        "status": "M6_RESEARCH_ONLY_NO_STATE_WRITER",
    },
    {
        "id": "m6_outbox_journal_mark_delivered",
        "path": "src/integration/m6_outbox_delivery_journal_v1.py",
        "class": "M6OutboxDeliveryJournalV1",
        "symbol": "mark_delivered",
        "kind": "definition",
        "authority": "external_effect_journal_only",
        "status": "M6_RESEARCH_ONLY_NO_STATE_WRITER",
    },
    {
        "id": "m6_outbox_delivery",
        "path": "src/integration/m6_outbox_delivery_v1.py",
        "class": "M6OutboxDeliveryPortV1",
        "symbol": "deliver",
        "kind": "definition",
        "authority": "external_effect_transport_only",
        "status": "M6_RESEARCH_ONLY_NO_STATE_WRITER",
    },
)

SOURCE_MARKERS: dict[str, tuple[str, ...]] = {
    "src/integration/m6_commit_port_v1.py": (
        "Single in-memory M6 commit port used by the reference and test shell.",
        "without pretending to",
        "The reference repository does not implement",
    ),
    "src/integration/m6_durable_store_v1.py": (
        "Research-only durable shell for the M6 typed commit bundle.",
        "It intentionally has no validator networking",
        "external effect delivery",
    ),
    "src/integration/m6_outbox_delivery_v1.py": (
        "Research-only Tau outbox delivery shell for the M6 durable ledger.",
        "never changes M6",
        "never creates acknowledgment authority",
    ),
}
