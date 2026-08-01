"""Minimal immutable decoded bundle claim for FCIS M5.

The bundle nests one committable decision. Successor state, patch, effects,
replay update, receipt, and their roots are reached through that one lineage
rather than copied into independently swappable fields.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import final

from ..state.fcis_committed_state_values import FCISCommittedStateV1
from .fcis_decision_values import (
    AcceptanceReceiptClaimV1,
    AcceptClaimV1,
    CommittedFailureClaimV1,
    CommittedFailureReceiptClaimV1,
)
from .fcis_outbox_values import OutboxPlanV1
from .fcis_transition_values import CommitPlanV1

FCIS_COMMIT_BUNDLE_SCHEMA_ID_V1 = "zenodex/fcis/commit-bundle/v1"


@final
@dataclass(frozen=True, slots=True)
class CommitBundleSourceV1:
    expected_pre_root: object
    decision: object
    receipt_root: object
    outbox_plan: object
    authority_normal_form_root: object = None


def _is_digest_v1(value: object) -> bool:
    return (
        type(value) is str
        and len(value) == 66
        and value.startswith("0x")
        and all(character in "0123456789abcdef" for character in value[2:])
    )


@final
@dataclass(frozen=True, slots=True)
class CommitBundleClaimV1:
    """Decoded CAS-payload claim with no publication authority."""

    expected_pre_root: str
    decision: AcceptClaimV1 | CommittedFailureClaimV1
    receipt_root: str
    outbox_plan: OutboxPlanV1
    authority_normal_form_root: str | None = None

    def __post_init__(self) -> None:
        if not _is_digest_v1(self.expected_pre_root):
            raise TypeError("bundle expected_pre_root must be a canonical digest")
        if type(self.decision) not in (AcceptClaimV1, CommittedFailureClaimV1):
            raise TypeError("bundle decision must be an exact committable decision")
        if not _is_digest_v1(self.receipt_root):
            raise TypeError("bundle receipt_root must be a canonical digest")
        if type(self.outbox_plan) is not OutboxPlanV1:
            raise TypeError("bundle outbox_plan must be exact")
        if self.expected_pre_root != self.receipt.binding.pre_state_root:
            raise ValueError("bundle expected root must equal the receipt pre-root")
        receipt_anf_root = self.receipt.binding.authority_normal_form_root
        if self.authority_normal_form_root != receipt_anf_root:
            raise ValueError("bundle ANF root must equal the decision receipt ANF root")
        if self.outbox_plan.authority_normal_form_root != self.authority_normal_form_root:
            raise ValueError("bundle ANF root must equal the outbox ANF root")

    @property
    def next_state(self) -> FCISCommittedStateV1:
        return self.decision.next_state

    @property
    def commit_plan(self) -> CommitPlanV1:
        return self.decision.commit_plan

    @property
    def receipt(self) -> AcceptanceReceiptClaimV1 | CommittedFailureReceiptClaimV1:
        return self.decision.receipt

    @property
    def next_state_root(self) -> str:
        return self.receipt.binding.next_state_root

    @property
    def execution_context_hash(self) -> str:
        return self.receipt.binding.execution_context_hash

    @property
    def command_or_batch_root(self) -> str:
        return self.receipt.binding.command_or_batch_root


__all__ = (
    "CommitBundleSourceV1",
    "CommitBundleClaimV1",
    "FCIS_COMMIT_BUNDLE_SCHEMA_ID_V1",
)
