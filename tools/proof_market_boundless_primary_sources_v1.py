"""Pinned primary-source review used by the research-only proof-market packet."""

from __future__ import annotations

from typing import Any


def primary_source_review() -> dict[str, Any]:
    """Return a fresh, exact record of the reviewed Boundless materials."""
    return {
        "checked_on": "2026-08-17",
        "scope": "official Boundless documentation, releases, repository, and published audit PDFs",
        "sources": [
            {
                "id": "BOUNDLESS_PROOF_LIFECYCLE",
                "url": "https://docs.boundless.network/developers/proof-lifecycle",
            },
            {
                "id": "BOUNDLESS_AUCTION_GUIDE",
                "url": "https://docs.boundless.network/developers/tutorials/auction",
            },
            {
                "id": "BOUNDLESS_RELEASE_V2_0_2",
                "url": "https://github.com/boundless-xyz/boundless/releases/tag/v2.0.2",
            },
            {
                "id": "BOUNDLESS_HOMEPAGE",
                "url": "https://boundless.network/",
            },
            {
                "id": "VERIDISE_CORE_2025_04",
                "url": "https://github.com/boundless-xyz/boundless-security/blob/main/audits/2025_04_Veridise%20%28Boundless%20Core%29.pdf",
                "observed_pdf_sha256": "00b40d09c3b1b53529adfb6d840a7e8ecee411e4c621fa1ceb44e8adec1fbdcf",
            },
            {
                "id": "HEXENS_CORE_2025_07",
                "url": "https://github.com/boundless-xyz/boundless-security/blob/main/audits/2025_07_Hexens%20%28Boundless%20Core%29.pdf",
                "observed_pdf_sha256": "46c5905fe8ea1d2e37a2845beda8b71c102c26afaa7c5e7b2b7a134653f9f644",
            },
            {
                "id": "HEXENS_POVW_2025_08",
                "url": "https://github.com/boundless-xyz/boundless-security/blob/main/audits/2025_08_Hexens%20%28PoVW%29.pdf",
                "observed_pdf_sha256": "1b657031cc086391c9a60998ddc8c62b4ccf766fac290b98d0280cddbcc58a86",
            },
            {
                "id": "OPENZEPPELIN_POVW_2025_09",
                "url": "https://github.com/boundless-xyz/boundless-security/blob/main/audits/2025_09_OZ%20%28POVW%29.pdf",
                "observed_pdf_sha256": "d67305db81c81e56bca1be7ca53a84d5b09b5c6e88416b794b3295b643a18613",
            },
        ],
        "documented_findings": [
            {
                "id": "REQUEST_ID_NOT_BOUND_TO_REQUEST_DIGEST",
                "source": "VERIDISE_CORE_2025_04",
                "source_severity": "CRITICAL",
                "source_status": "FIXED_IN_REVIEWED_VERSION",
                "zenoproof_closure": "bind request ID, request digest, claim, verifier profile, and payment account in one canonical occurrence",
            },
            {
                "id": "COMMUTATIVE_BATCH_ROOT_PERMITTED_FULFILLMENT_REORDERING",
                "source": "VERIDISE_CORE_2025_04",
                "source_severity": "HIGH",
                "source_status": "FIXED_IN_REVIEWED_VERSION",
                "zenoproof_closure": "commit the exact ordered leaf manifest with tagged leaf and internal-node domains",
            },
            {
                "id": "CALLBACK_BEFORE_PAYMENT_ENABLED_REENTRANCY",
                "source": "VERIDISE_CORE_2025_04",
                "source_severity": "HIGH",
                "source_status": "FIXED_IN_REVIEWED_VERSION",
                "zenoproof_closure": "commit payment and an idempotent outbox row before external callback delivery",
            },
            {
                "id": "CLIENT_AND_PROVER_SIGNATURES_LACKED_DOMAIN_SEPARATION",
                "source": "VERIDISE_CORE_2025_04",
                "source_severity": "MEDIUM",
                "source_status": "FIXED_IN_REVIEWED_VERSION",
                "zenoproof_closure": "use distinct typed signing domains for buyer authorization, prover lock, verification, and publication",
            },
            {
                "id": "DUPLICATE_CALLBACK_ON_RESUBMITTED_REQUEST_ID",
                "source": "HEXENS_CORE_2025_07",
                "source_severity": "MEDIUM",
                "source_status": "ACKNOWLEDGED_IN_REVIEWED_VERSION",
                "zenoproof_closure": "derive one effect key from promotion subject, request occurrence, and effect index; redelivery remains idempotent",
            },
            {
                "id": "UNLOCKED_OR_POST_LOCK_PROOF_COULD_FINALIZE_WITHOUT_PAYMENT",
                "source": "HEXENS_CORE_2025_07",
                "source_severity": "LOW",
                "source_status": "ACKNOWLEDGED_IN_REVIEWED_VERSION",
                "zenoproof_closure": "reserve maximum buyer liability before lock and reject-no-commit if the exact payment bundle is unavailable",
            },
            {
                "id": "REWARD_CAP_SPLIT_ACROSS_WORK_LOGS",
                "source": "OPENZEPPELIN_POVW_2025_09",
                "source_severity": "MEDIUM",
                "source_status": "RESOLVED_IN_REVIEWED_VERSION",
                "zenoproof_closure": "aggregate reward caps by beneficial recipient and epoch across every work-log identity",
            },
            {
                "id": "EPHEMERAL_UNSUBMITTED_WORK_RECEIPTS",
                "source": "BOUNDLESS_RELEASE_V2_0_2",
                "source_severity": "RELEASE_DEFECT",
                "source_status": "FIXED_FOR_POST_UPGRADE_RECEIPTS",
                "zenoproof_closure": "durably journal and fsync a content-addressed work receipt before acknowledging claimable work",
            },
            {
                "id": "REQUESTOR_PRIORITY_LEVELS_AFFECT_BROKER_RANKING",
                "source": "BOUNDLESS_RELEASE_V2_0_2",
                "source_severity": "DESIGN_SURFACE",
                "source_status": "DOCUMENTED_CURRENT_FEATURE",
                "zenoproof_closure": "cap paid reservations and preserve a nonzero permissionless capacity floor; priority never changes verifier or settlement semantics",
            },
            {
                "id": "ABSOLUTE_LOCK_DEADLINE_AND_FIXED_SLASH_SPLIT",
                "source": "BOUNDLESS_AUCTION_GUIDE",
                "source_severity": "DESIGN_TRADEOFF",
                "source_status": "DOCUMENTED_CURRENT_MECHANISM",
                "zenoproof_closure": "check the locker's effective remaining window and route slashing by named loss priority before residual burn",
            },
        ],
        "inferences": [
            {
                "id": "WORKLOAD_DIVERSIFICATION_MAY_IMPROVE_CAPACITY_UTILIZATION",
                "basis": "The current homepage says Boundless began with proofs and now markets distributed GPU AI compute.",
                "claim_ceiling": "strategic inference rather than evidence that the proof market failed",
                "zenoproof_response": "retain a general verifier-profile market while keeping all non-ZRPF workloads outside settlement authority",
            }
        ],
    }
