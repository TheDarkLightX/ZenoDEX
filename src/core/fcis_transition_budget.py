"""First-class deterministic resource budget for one FCIS transition."""

from __future__ import annotations

from dataclasses import dataclass
from typing import final

from ..state.snapshot_combinators import (
    MAX_ADMISSION_DEPTH_V1,
    MAX_ADMISSION_NODES_V1,
    MAX_CANONICAL_BYTES_V1,
    MAX_COLLECTION_ITEMS_V1,
    MAX_SORTABLE_KEY_INTEGER_BITS_V1,
)

FCIS_TRANSITION_BUDGET_SCHEMA_ID_V1 = "zenodex/fcis/transition-budget/v1"
MAX_FCIS_INTENTS_V1 = 256
MAX_FCIS_OUTBOX_RECORDS_V1 = 4_096
MAX_FCIS_CANDIDATES_V1 = 256


@final
@dataclass(frozen=True, slots=True)
class TransitionBudgetSourceV1:
    """Exact source carrier interpreted by the closed admission algebra."""

    max_canonical_input_bytes: object
    max_depth: object
    max_nodes: object
    max_intents: object
    max_state_reads: object
    max_context_reads: object
    max_patch_writes: object
    max_effects: object
    max_outbox_records: object
    max_candidates: object
    max_witness_bytes: object
    max_receipt_bytes: object
    max_integer_bits: object


@final
@dataclass(frozen=True, slots=True)
class TransitionBudgetV1:
    """Version-pinned upper bounds that make transition cost deterministic."""

    max_canonical_input_bytes: int
    max_depth: int
    max_nodes: int
    max_intents: int
    max_state_reads: int
    max_context_reads: int
    max_patch_writes: int
    max_effects: int
    max_outbox_records: int
    max_candidates: int
    max_witness_bytes: int
    max_receipt_bytes: int
    max_integer_bits: int

    def __post_init__(self) -> None:
        bounded = (
            (
                "max_canonical_input_bytes",
                self.max_canonical_input_bytes,
                MAX_CANONICAL_BYTES_V1,
            ),
            ("max_depth", self.max_depth, MAX_ADMISSION_DEPTH_V1),
            ("max_nodes", self.max_nodes, MAX_ADMISSION_NODES_V1),
            ("max_intents", self.max_intents, MAX_FCIS_INTENTS_V1),
            ("max_state_reads", self.max_state_reads, MAX_COLLECTION_ITEMS_V1),
            ("max_context_reads", self.max_context_reads, MAX_COLLECTION_ITEMS_V1),
            ("max_patch_writes", self.max_patch_writes, MAX_COLLECTION_ITEMS_V1),
            ("max_effects", self.max_effects, MAX_COLLECTION_ITEMS_V1),
            (
                "max_outbox_records",
                self.max_outbox_records,
                MAX_FCIS_OUTBOX_RECORDS_V1,
            ),
            ("max_candidates", self.max_candidates, MAX_FCIS_CANDIDATES_V1),
            ("max_witness_bytes", self.max_witness_bytes, MAX_CANONICAL_BYTES_V1),
            ("max_receipt_bytes", self.max_receipt_bytes, MAX_CANONICAL_BYTES_V1),
            (
                "max_integer_bits",
                self.max_integer_bits,
                MAX_SORTABLE_KEY_INTEGER_BITS_V1,
            ),
        )
        for field_name, value, policy_maximum in bounded:
            if type(value) is not int:
                raise TypeError(f"{field_name} must be an exact int")
            if not 0 < value <= policy_maximum:
                raise ValueError(f"{field_name} is outside the FCIS policy")
        if self.max_intents > self.max_nodes:
            raise ValueError("max_intents cannot exceed max_nodes")
        if self.max_patch_writes > self.max_nodes:
            raise ValueError("max_patch_writes cannot exceed max_nodes")


__all__ = (
    "FCIS_TRANSITION_BUDGET_SCHEMA_ID_V1",
    "MAX_FCIS_CANDIDATES_V1",
    "MAX_FCIS_INTENTS_V1",
    "MAX_FCIS_OUTBOX_RECORDS_V1",
    "TransitionBudgetSourceV1",
    "TransitionBudgetV1",
)
