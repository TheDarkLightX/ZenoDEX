from __future__ import annotations

from dataclasses import dataclass
from typing import Literal, NewType

AxisId = NewType("AxisId", str)
CrosswalkEntryId = NewType("CrosswalkEntryId", str)
ClosurePacketId = NewType("ClosurePacketId", str)
PublicSourceId = NewType("PublicSourceId", str)

CoveragePosture = Literal[
    "seed_only",
    "covered_axis_family",
    "backlog_axis_family",
    "out_of_scope",
]


@dataclass(frozen=True)
class PublicSourceRef:
    source_id: PublicSourceId
    name: str
    url: str
    role: str


@dataclass(frozen=True)
class CrosswalkEntry:
    entry_id: CrosswalkEntryId
    source_families: tuple[str, ...]
    mapped_axis_ids: tuple[AxisId, ...]
    coverage_posture: CoveragePosture
    what_if: str


@dataclass(frozen=True)
class BadTracePredicate:
    name: str
    state_scope: tuple[str, ...]
    conditions: tuple[str, ...]


@dataclass(frozen=True)
class ClosurePacket:
    packet_id: ClosurePacketId
    crosswalk_entry_id: CrosswalkEntryId
    bad_trace_predicate: BadTracePredicate
    closure_obligations: tuple[str, ...]
