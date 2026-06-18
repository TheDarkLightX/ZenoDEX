"""Aequitas-style batch ordering with externally verified VRF tie-breaks.

This module is a small ordering primitive for mechanism-design review. It does
not verify VRF cryptography. It consumes receipts that a verifier has already
accepted and uses their output hashes only for ordering members inside an
Aequitas SCC batch.

Contract:
- SCC batch dependencies are ordered by topological condensation order.
- Members inside one SCC are ordered by `(vrf_output_hash, subject_id)`.
- The seed id must match every receipt, so a caller cannot mix outputs from a
  different randomness epoch.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Iterable, Mapping

_HEX64_RE = re.compile(r"[0-9a-f]{64}")


@dataclass(frozen=True)
class ExternallyVerifiedVrfReceipt:
    """VRF output receipt accepted by an external cryptographic verifier."""

    subject_id: str
    seed_id: str
    output_hash: str
    proof_hash: str


@dataclass(frozen=True)
class AequitasSccBatch:
    """One SCC in an Aequitas condensation DAG."""

    batch_id: str
    member_ids: tuple[str, ...]
    predecessor_batch_ids: tuple[str, ...] = ()


@dataclass(frozen=True)
class AequitasVrfOrdering:
    """Deterministic fair-order result."""

    batch_order: tuple[str, ...]
    member_order_by_batch: tuple[tuple[str, tuple[str, ...]], ...]
    flattened_member_order: tuple[str, ...]


@dataclass
class _TopologicalSortState:
    remaining_predecessors: dict[str, set[str]]
    ready: list[str]
    ordered_ids: list[str]


def _require_str(value: object, *, name: str) -> str:
    if not isinstance(value, str) or value == "":
        raise ValueError(f"{name} must be a non-empty string")
    return value


def _require_hex64(value: object, *, name: str) -> str:
    text = _require_str(value, name=name)
    if _HEX64_RE.fullmatch(text) is None:
        raise ValueError(f"{name} must be a lowercase 32-byte hex string")
    return text


def _require_unique_str_tuple(values: Iterable[object], *, name: str) -> tuple[str, ...]:
    out = tuple(_require_str(value, name=name) for value in values)
    if len(set(out)) != len(out):
        raise ValueError(f"{name} must not contain duplicates")
    return out


def _validate_receipt(
    receipt: ExternallyVerifiedVrfReceipt,
    *,
    expected_seed_id: str,
    expected_subject_id: str,
) -> ExternallyVerifiedVrfReceipt:
    subject_id = _require_str(receipt.subject_id, name="receipt.subject_id")
    if subject_id != expected_subject_id:
        raise ValueError("receipt subject_id mismatch")
    seed_id = _require_str(receipt.seed_id, name="receipt.seed_id")
    if seed_id != expected_seed_id:
        raise ValueError("receipt seed_id mismatch")
    return ExternallyVerifiedVrfReceipt(
        subject_id=subject_id,
        seed_id=seed_id,
        output_hash=_require_hex64(receipt.output_hash, name="receipt.output_hash"),
        proof_hash=_require_hex64(receipt.proof_hash, name="receipt.proof_hash"),
    )


def order_members_by_verified_vrf(
    member_ids: Iterable[object],
    *,
    receipts_by_subject_id: Mapping[str, ExternallyVerifiedVrfReceipt],
    expected_seed_id: str,
) -> tuple[str, ...]:
    """Order members by externally verified VRF output for one SCC batch."""
    seed_id = _require_str(expected_seed_id, name="expected_seed_id")
    members = _require_unique_str_tuple(member_ids, name="member_ids")
    if set(receipts_by_subject_id) != set(members):
        raise ValueError("receipts must match member_ids exactly")

    validated = tuple(
        _validate_receipt(
            receipts_by_subject_id[member_id],
            expected_seed_id=seed_id,
            expected_subject_id=member_id,
        )
        for member_id in members
    )
    return tuple(
        receipt.subject_id
        for receipt in sorted(
            validated,
            key=lambda receipt: (bytes.fromhex(receipt.output_hash), receipt.subject_id),
        )
    )


def _normalize_scc_batch(batch: AequitasSccBatch) -> AequitasSccBatch:
    return AequitasSccBatch(
        batch_id=_require_str(batch.batch_id, name="batch_id"),
        member_ids=_require_unique_str_tuple(batch.member_ids, name="member_ids"),
        predecessor_batch_ids=_require_unique_str_tuple(
            batch.predecessor_batch_ids,
            name="predecessor_batch_ids",
        ),
    )


def _index_batches_by_id(batches: tuple[AequitasSccBatch, ...]) -> dict[str, AequitasSccBatch]:
    by_id = {batch.batch_id: batch for batch in batches}
    if len(by_id) != len(batches):
        raise ValueError("batch_id values must be unique")
    return by_id


def _validate_scc_batch_graph(
    batches: tuple[AequitasSccBatch, ...],
    by_id: Mapping[str, AequitasSccBatch],
) -> None:
    seen_members: set[str] = set()
    for batch in batches:
        overlap = seen_members.intersection(batch.member_ids)
        if overlap:
            raise ValueError("member_ids must be globally unique across batches")
        seen_members.update(batch.member_ids)
        unknown = set(batch.predecessor_batch_ids).difference(by_id)
        if unknown:
            raise ValueError("predecessor_batch_ids must refer to known batches")
        if batch.batch_id in batch.predecessor_batch_ids:
            raise ValueError("batch cannot depend on itself")


def _children_by_predecessor(
    batches: tuple[AequitasSccBatch, ...],
    by_id: Mapping[str, AequitasSccBatch],
) -> dict[str, list[str]]:
    children: dict[str, list[str]] = {batch_id: [] for batch_id in by_id}
    for batch in batches:
        for predecessor in batch.predecessor_batch_ids:
            children[predecessor].append(batch.batch_id)
    return children


def _release_ready_children(
    *,
    batch_id: str,
    children: Mapping[str, list[str]],
    state: _TopologicalSortState,
) -> None:
    for child in sorted(children[batch_id]):
        state.remaining_predecessors[child].discard(batch_id)
        if (
            not state.remaining_predecessors[child]
            and child not in state.ordered_ids
            and child not in state.ready
        ):
            state.ready.append(child)
    state.ready.sort()


def _topological_batch_ids(
    batches: tuple[AequitasSccBatch, ...],
    by_id: Mapping[str, AequitasSccBatch],
    children: Mapping[str, list[str]],
) -> tuple[str, ...]:
    remaining_predecessors = {
        batch.batch_id: set(batch.predecessor_batch_ids)
        for batch in batches
    }
    state = _TopologicalSortState(
        remaining_predecessors=remaining_predecessors,
        ready=sorted(batch_id for batch_id, preds in remaining_predecessors.items() if not preds),
        ordered_ids=[],
    )
    while state.ready:
        batch_id = state.ready.pop(0)
        state.ordered_ids.append(batch_id)
        _release_ready_children(
            batch_id=batch_id,
            children=children,
            state=state,
        )
    if len(state.ordered_ids) != len(by_id):
        raise ValueError("batch dependency graph must be acyclic")
    return tuple(state.ordered_ids)


def order_aequitas_scc_batches(batches: Iterable[AequitasSccBatch]) -> tuple[AequitasSccBatch, ...]:
    """Topologically order Aequitas condensation batches."""
    normalized = tuple(_normalize_scc_batch(batch) for batch in batches)
    by_id = _index_batches_by_id(normalized)
    _validate_scc_batch_graph(normalized, by_id)
    children = _children_by_predecessor(normalized, by_id)
    ordered_ids = _topological_batch_ids(normalized, by_id, children)
    return tuple(by_id[batch_id] for batch_id in ordered_ids)


def order_aequitas_batches_with_vrf_tiebreak(
    batches: Iterable[AequitasSccBatch],
    *,
    receipts_by_subject_id: Mapping[str, ExternallyVerifiedVrfReceipt],
    expected_seed_id: str,
) -> AequitasVrfOrdering:
    """Order SCC batches, then order members inside each SCC by verified VRF output."""
    ordered_batches = order_aequitas_scc_batches(batches)
    member_order_entries: list[tuple[str, tuple[str, ...]]] = []
    flattened: list[str] = []
    for batch in ordered_batches:
        member_order = order_members_by_verified_vrf(
            batch.member_ids,
            receipts_by_subject_id={
                member_id: receipts_by_subject_id[member_id]
                for member_id in batch.member_ids
            },
            expected_seed_id=expected_seed_id,
        )
        member_order_entries.append((batch.batch_id, member_order))
        flattened.extend(member_order)
    return AequitasVrfOrdering(
        batch_order=tuple(batch.batch_id for batch in ordered_batches),
        member_order_by_batch=tuple(member_order_entries),
        flattened_member_order=tuple(flattened),
    )
