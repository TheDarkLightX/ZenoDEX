from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping, Sequence

from src.core.amm_dispatch import swap_exact_out_for_pool
from src.core.split_routing_dispatch import (
    ExactOutRouteCanonicalKey,
    SplitLegExactOutQuote,
    SplitManyPoolsExactOutQuote,
    SplitTwoPoolsQuote,
    best_split_many_pools_exact_out_for_pools,
    best_split_two_pools_exact_out_for_pools,
)
from src.kernels.python.exact_out_many_pool_bounded_oracle_v1 import (
    bounded_exact_out_many_pool_runtime_domain as _kernel_bounded_exact_out_many_pool_runtime_domain,
)
from src.kernels.python.exact_out_many_pool_bounded_oracle_v1 import (
    enumerate_exact_out_many_pool_candidates as _kernel_enumerate_exact_out_many_pool_candidates,
)
from src.kernels.python.exact_out_many_pool_bounded_oracle_v1 import (
    feasible_exact_out_pools as _kernel_feasible_exact_out_pools,
)
from src.kernels.python.exact_out_many_pool_bounded_oracle_v1 import (
    pool_reserves_for_exact_out as _kernel_pool_reserves_for_exact_out,
)
from src.kernels.python.exact_out_many_pool_bounded_oracle_v1 import (
    select_many_pool_audit_candidates as _kernel_select_many_pool_audit_candidates,
)
from src.kernels.python.exact_out_many_pool_canonical_domain_v1 import (
    build_exact_out_many_pool_selected_domain as _kernel_build_exact_out_many_pool_selected_domain,
)
from src.kernels.python.exact_out_many_pool_canonical_domain_v1 import (
    rank_exact_out_feasible_pools as _kernel_rank_exact_out_feasible_pools,
)
from src.kernels.python.exact_out_many_pool_certified_winner_packet_v1_adapter import (
    check_exact_out_many_pool_certified_winner_packet_gate,
)
from src.kernels.python.exact_out_many_pool_prefilter_contraction_audit_v1 import (
    audit_exact_out_many_pool_selected_subset_contraction as _kernel_audit_exact_out_many_pool_selected_subset_contraction,
)
from src.kernels.python.exact_out_many_pool_projection_cover_audit_v1 import (
    ExactOutManyPoolProjectionCoverAudit as _KernelExactOutManyPoolProjectionCoverAudit,
)
from src.kernels.python.exact_out_many_pool_projection_cover_audit_v1 import (
    audit_exact_out_many_pool_selected_domain_projection_cover as _kernel_audit_exact_out_many_pool_selected_domain_projection_cover,
)
from src.kernels.python.exact_out_many_pool_repaired_prefilter_v1 import (
    build_many_pool_repaired_prefilter_selection as _kernel_build_many_pool_repaired_prefilter_selection,
)
from src.kernels.python.exact_out_route_canonical_selector_v1 import (
    select_exact_out_route_canonical_winner as _kernel_select_exact_out_route_canonical_winner,
)
from src.state.pools import PoolState, PoolStatus

from .tau_witness import ARGMIN_STREAM_CERTIFICATE_V1, build_argmin_stream_certificate_v1_step

EXACT_OUT_ROUTE_CERTIFICATE_SCHEMA = "zenodex/exact-out-route-certificate/v1"
EXACT_OUT_MANY_POOL_PREFILTER_CONTRACT_SCHEMA = "zenodex/exact-out-many-pool-prefilter-contract/v1"
EXACT_OUT_MANY_POOL_REPAIRED_PREFILTER_CONTRACT_SCHEMA = "zenodex/exact-out-many-pool-repaired-prefilter-contract/v1"
EXACT_OUT_MANY_POOL_REPAIRED_SELECTED_DOMAIN_ORACLE_CONTRACT_SCHEMA = (
    "zenodex/exact-out-many-pool-repaired-selected-domain-oracle-contract/v1"
)
EXACT_OUT_MANY_POOL_REPAIRED_ADVISORY_QUOTE_PACKET_SCHEMA = "zenodex/exact-out-many-pool-repaired-advisory-quote-packet/v1"
EXACT_OUT_MANY_POOL_REPAIRED_FULL_DOMAIN_CERTIFIED_PACKET_SCHEMA = (
    "zenodex/exact-out-many-pool-repaired-full-domain-certified-packet/v1"
)
EXACT_OUT_MANY_POOL_REPAIRED_KEY_COVER_PACKET_SCHEMA = (
    "zenodex/exact-out-many-pool-repaired-key-cover-packet/v1"
)
EXACT_OUT_MANY_POOL_REPAIRED_KEY_COVER_INTERPRETATION_PACKET_SCHEMA = (
    "zenodex/exact-out-many-pool-repaired-key-cover-interpretation-packet/v1"
)
EXACT_OUT_MANY_POOL_BOUNDED_WORKAROUND_PACKET_SCHEMA = "zenodex/exact-out-many-pool-bounded-workaround-packet/v1"
EXACT_OUT_MANY_POOL_BOUNDED_ADVISORY_QUOTE_PACKET_SCHEMA = "zenodex/exact-out-many-pool-bounded-advisory-quote-packet/v1"
EXACT_OUT_MANY_POOL_CERTIFIED_ADVISORY_PACKET_SCHEMA = "zenodex/exact-out-many-pool-certified-advisory-packet/v1"
EXACT_OUT_MANY_POOL_REPAIRED_REPLACEMENT_SHADOW_PACKET_SCHEMA = (
    "zenodex/exact-out-many-pool-repaired-replacement-shadow-packet/v1"
)
EXACT_OUT_MANY_POOL_CANDIDATE_DOMAIN_CONTRACT_SCHEMA = "zenodex/exact-out-many-pool-candidate-domain-contract/v1"
EXACT_OUT_MANY_POOL_ORACLE_CONTRACT_SCHEMA = "zenodex/exact-out-many-pool-oracle-contract/v1"
EXACT_OUT_MANY_POOL_GUARDED_QUOTE_PACKET_SCHEMA = "zenodex/exact-out-many-pool-guarded-quote-packet/v1"
EXACT_OUT_MANY_POOL_CERTIFIED_WINNER_PACKET_SCHEMA = "zenodex/exact-out-many-pool-certified-winner-packet/v1"
EXACT_OUT_MANY_POOL_AUDITED_BOUNDS_CONTRACT_SCHEMA = "zenodex/exact-out-many-pool-audited-bounds-contract/v1"
EXACT_OUT_MANY_POOL_ADAPTIVE_LIVENESS_PACKET_SCHEMA = "zenodex/exact-out-many-pool-adaptive-liveness-packet/v1"
EXACT_OUT_MANY_POOL_GUARD_MISMATCH_ERROR = "many_pool_runtime_not_canonical_on_bounded_audit_domain"
EXACT_OUT_MANY_POOL_PROJECTION_COVER_ERROR = "many_pool_projection_cover_not_verified"
EXACT_OUT_MANY_POOL_REPAIRED_ADVISORY_UNAVAILABLE_ERROR = "many_pool_repaired_prefilter_contract_not_ok"
EXACT_OUT_MANY_POOL_REPAIRED_SELECTED_DOMAIN_UNAVAILABLE_ERROR = "many_pool_repaired_selected_domain_contract_not_ok"
EXACT_OUT_MANY_POOL_REPAIRED_FULL_DOMAIN_CERTIFIED_ERROR = "many_pool_repaired_advisory_not_full_domain_canonical"
EXACT_OUT_MANY_POOL_REPAIRED_KEY_COVER_ERROR = "many_pool_repaired_selected_domain_not_key_cover_complete"
EXACT_OUT_MANY_POOL_REPAIRED_KEY_COVER_INTERPRETATION_ERROR = (
    "many_pool_repaired_key_cover_witness_interpretation_inconsistent"
)
EXACT_OUT_MANY_POOL_RUNTIME_QUOTE_INCONSISTENCY_ERROR = "many_pool_runtime_quote_inconsistency_between_selected_and_repaired_packets"
EXACT_OUT_MANY_POOL_ADAPTIVE_FAILURE_AUDITED_BOUNDS_CONTRACT_NOT_OK = "audited_bounds_contract_not_ok"
EXACT_OUT_MANY_POOL_ADAPTIVE_FAILURE_DEFAULT_PACKET_NOT_OK = "default_packet_not_ok"
EXACT_OUT_MANY_POOL_ADAPTIVE_FAILURE_REPAIRED_FULL_DOMAIN_PACKET_NOT_OK = "repaired_full_domain_packet_not_ok"
EXACT_OUT_MANY_POOL_ADAPTIVE_FAILURE_REPLAYABLE_QUOTE_MISSING = "replayable_quote_missing"


def _require_payload_int(payload: Mapping[str, Any], field_name: str) -> int:
    value = payload[field_name]
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{field_name} must be an int")
    return int(value)


def _require_payload_int_path(payload: Mapping[str, Any], *field_path: str) -> int:
    if not field_path:
        raise ValueError("field_path must be non-empty")
    current: object = payload
    for field_name in field_path[:-1]:
        if not isinstance(current, Mapping):
            raise TypeError(".".join(field_path[:-1]) + " must be a dict")
        current = current[field_name]
    if not isinstance(current, Mapping):
        raise TypeError(".".join(field_path[:-1]) + " must be a dict")
    return _require_payload_int(current, field_path[-1])


def _require_amount_out_total_int(amount_out_total: object) -> int:
    if not isinstance(amount_out_total, int) or isinstance(amount_out_total, bool):
        raise ValueError("amount_out_total must be an int")
    return int(amount_out_total)


def _require_control_int(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValueError(f"{name} must be an int")
    return int(value)


def _require_optional_control_int(value: object | None, *, name: str) -> int | None:
    if value is None:
        return None
    return _require_control_int(value, name=name)


def _require_control_fields(fields: tuple[tuple[str, object], ...]) -> None:
    for name, value in fields:
        _require_control_int(value, name=name)


def _require_runtime_control_values(
    *,
    max_legs: object,
    max_candidate_pools: object,
    max_candidates: object,
    max_iters: object,
    window: object,
    brute_force_max: object,
    max_full_domain_pools: object,
    max_enumerated_candidates: object,
) -> tuple[int, int, int, int, int, int, int, int]:
    return (
        _require_control_int(max_legs, name="max_legs"),
        _require_control_int(max_candidate_pools, name="max_candidate_pools"),
        _require_control_int(max_candidates, name="max_candidates"),
        _require_control_int(max_iters, name="max_iters"),
        _require_control_int(window, name="window"),
        _require_control_int(brute_force_max, name="brute_force_max"),
        _require_control_int(max_full_domain_pools, name="max_full_domain_pools"),
        _require_control_int(max_enumerated_candidates, name="max_enumerated_candidates"),
    )


@dataclass(frozen=True)
class ExactOutRouteCandidateCertificate:
    candidate_index: int
    quote: SplitManyPoolsExactOutQuote
    route_key: ExactOutRouteCanonicalKey
    route_key_rank_u64: int

    def __post_init__(self) -> None:
        if not isinstance(self.candidate_index, int) or isinstance(self.candidate_index, bool):
            raise TypeError("candidate_index must be an int")
        if self.candidate_index < 0 or self.candidate_index > 0xFFFFFFFF:
            raise ValueError(f"candidate_index out of range: {self.candidate_index}")
        if not isinstance(self.quote, SplitManyPoolsExactOutQuote):
            raise TypeError("quote must be a SplitManyPoolsExactOutQuote")
        if not isinstance(self.route_key, ExactOutRouteCanonicalKey):
            raise TypeError("route_key must be an ExactOutRouteCanonicalKey")
        if not isinstance(self.route_key_rank_u64, int) or isinstance(self.route_key_rank_u64, bool):
            raise TypeError("route_key_rank_u64 must be an int")
        if self.route_key_rank_u64 < 0 or self.route_key_rank_u64 > 0xFFFFFFFFFFFFFFFF:
            raise ValueError(f"route_key_rank_u64 out of range: {self.route_key_rank_u64}")

    def to_dict(self) -> dict[str, Any]:
        return {
            "candidate_index": int(self.candidate_index),
            "route_key_rank_u64": int(self.route_key_rank_u64),
            "route_key": {
                "amount_in_total": int(self.route_key.amount_in_total),
                "leg_count": int(self.route_key.leg_count),
                "legs_lex": [[pool_id, int(amount_out)] for pool_id, amount_out in self.route_key.legs_lex],
            },
            "quote": _quote_to_dict(self.quote),
        }


@dataclass(frozen=True)
class ExactOutRouteCanonicalCertificate:
    winner_index: int
    winner_route_key_rank_u64: int
    winner_quote: SplitManyPoolsExactOutQuote
    candidates: tuple[ExactOutRouteCandidateCertificate, ...]
    argmin_steps: tuple[dict[str, int], ...]
    tau_spec_id: str = ARGMIN_STREAM_CERTIFICATE_V1.spec_id

    def __post_init__(self) -> None:
        if not isinstance(self.winner_index, int) or isinstance(self.winner_index, bool):
            raise TypeError("winner_index must be an int")
        if self.winner_index < 0 or self.winner_index > 0xFFFFFFFF:
            raise ValueError(f"winner_index out of range: {self.winner_index}")
        if not isinstance(self.winner_route_key_rank_u64, int) or isinstance(self.winner_route_key_rank_u64, bool):
            raise TypeError("winner_route_key_rank_u64 must be an int")
        if self.winner_route_key_rank_u64 < 0 or self.winner_route_key_rank_u64 > 0xFFFFFFFFFFFFFFFF:
            raise ValueError(f"winner_route_key_rank_u64 out of range: {self.winner_route_key_rank_u64}")
        if not isinstance(self.winner_quote, SplitManyPoolsExactOutQuote):
            raise TypeError("winner_quote must be a SplitManyPoolsExactOutQuote")
        if not self.candidates:
            raise ValueError("candidates must be non-empty")
        if not self.argmin_steps:
            raise ValueError("argmin_steps must be non-empty")

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": EXACT_OUT_ROUTE_CERTIFICATE_SCHEMA,
            "tau_spec_id": self.tau_spec_id,
            "winner_index": int(self.winner_index),
            "winner_route_key_rank_u64": int(self.winner_route_key_rank_u64),
            "winner_quote": _quote_to_dict(self.winner_quote),
            "candidates": [candidate.to_dict() for candidate in self.candidates],
            "argmin_steps": [dict(step) for step in self.argmin_steps],
        }


@dataclass(frozen=True)
class ExactOutTwoPoolCanonicalityAudit:
    runtime_matches_canonical: bool
    runtime_quote: SplitManyPoolsExactOutQuote
    canonical_winner_quote: SplitManyPoolsExactOutQuote
    candidate_count: int
    certificate: ExactOutRouteCanonicalCertificate

    def to_dict(self) -> dict[str, Any]:
        return {
            "runtime_matches_canonical": bool(self.runtime_matches_canonical),
            "runtime_quote": _quote_to_dict(self.runtime_quote),
            "canonical_winner_quote": _quote_to_dict(self.canonical_winner_quote),
            "candidate_count": int(self.candidate_count),
            "certificate": self.certificate.to_dict(),
        }


@dataclass(frozen=True)
class ExactOutManyPoolCanonicalityAudit:
    runtime_matches_canonical: bool
    runtime_quote: SplitManyPoolsExactOutQuote
    canonical_winner_quote: SplitManyPoolsExactOutQuote
    candidate_count: int
    audit_pool_ids: tuple[str, ...]
    max_legs: int
    certificate: ExactOutRouteCanonicalCertificate
    projection_cover_audit: "ExactOutManyPoolProjectionCoverAudit | None" = None

    def _selected_domain_summary(self) -> dict[str, Any]:
        runtime_projected_path = _quote_to_projected_path_payload(self.runtime_quote)
        canonical_winner_projected_path = _quote_to_projected_path_payload(self.canonical_winner_quote)
        return {
            "runtime_projected_path": runtime_projected_path,
            "canonical_winner_projected_path": canonical_winner_projected_path,
            "runtime_matches_canonical_projected_path": bool(
                runtime_projected_path == canonical_winner_projected_path
            ),
            "projection_cover_available": bool(self.projection_cover_audit is not None),
            "projection_cover_holds": (
                None if self.projection_cover_audit is None else bool(self.projection_cover_audit.projection_cover_holds)
            ),
        }

    def to_dict(self) -> dict[str, Any]:
        return {
            "runtime_matches_canonical": bool(self.runtime_matches_canonical),
            "runtime_quote": _quote_to_dict(self.runtime_quote),
            "canonical_winner_quote": _quote_to_dict(self.canonical_winner_quote),
            "candidate_count": int(self.candidate_count),
            "audit_pool_ids": [str(pool_id) for pool_id in self.audit_pool_ids],
            "max_legs": int(self.max_legs),
            "certificate": self.certificate.to_dict(),
            "projection_cover_audit": None if self.projection_cover_audit is None else self.projection_cover_audit.to_dict(),
            **self._selected_domain_summary(),
        }


@dataclass(frozen=True)
class ExactOutManyPoolProjectionCoverAudit:
    selected_pool_ids: tuple[str, ...]
    emitted_candidate_count: int
    emitted_projected_path_count: int
    reachable_projected_path_count: int
    canonical_quote_projected_path: tuple[tuple[str, int, int], ...]
    canonical_quote_covered: bool
    sound_holds: bool
    complete_holds: bool
    projection_cover_holds: bool
    extra_emitted_path: tuple[tuple[str, int, int], ...] | None
    missing_reachable_path: tuple[tuple[str, int, int], ...] | None

    def to_dict(self) -> dict[str, Any]:
        return {
            "selected_pool_ids": [str(pool_id) for pool_id in self.selected_pool_ids],
            "emitted_candidate_count": int(self.emitted_candidate_count),
            "emitted_projected_path_count": int(self.emitted_projected_path_count),
            "reachable_projected_path_count": int(self.reachable_projected_path_count),
            "canonical_quote_projected_path": [
                [str(pool_id), int(amount_out), int(amount_in)]
                for pool_id, amount_out, amount_in in self.canonical_quote_projected_path
            ],
            "canonical_quote_covered": bool(self.canonical_quote_covered),
            "sound_holds": bool(self.sound_holds),
            "complete_holds": bool(self.complete_holds),
            "projection_cover_holds": bool(self.projection_cover_holds),
            "extra_emitted_path": None
            if self.extra_emitted_path is None
            else [[str(pool_id), int(amount_out), int(amount_in)] for pool_id, amount_out, amount_in in self.extra_emitted_path],
            "missing_reachable_path": None
            if self.missing_reachable_path is None
            else [[str(pool_id), int(amount_out), int(amount_in)] for pool_id, amount_out, amount_in in self.missing_reachable_path],
        }


@dataclass(frozen=True)
class ExactOutManyPoolCandidateDomainContract:
    asset_in: str
    asset_out: str
    amount_out_total: int
    max_legs: int
    max_candidate_pools: int
    max_enumerated_candidates: int
    audit_pool_ids: tuple[str, ...]
    pool_snapshots: tuple[dict[str, Any], ...]
    candidates: tuple[SplitManyPoolsExactOutQuote, ...]
    candidate_count: int
    audit_pool_ids_sorted_unique: bool
    audit_pool_ids_within_budget: bool
    candidate_domain_nonempty: bool
    all_candidates_complete: bool
    all_candidates_leg_bounded: bool
    all_candidates_leg_pool_ids_sorted_unique: bool
    all_candidates_within_audit_pool_ids: bool
    candidate_count_within_budget: bool
    contract_ok: bool
    schema: str = EXACT_OUT_MANY_POOL_CANDIDATE_DOMAIN_CONTRACT_SCHEMA

    def __post_init__(self) -> None:
        if not self.asset_in or not self.asset_out or self.asset_in == self.asset_out:
            raise ValueError("asset_in and asset_out must be non-empty and distinct")
        int_fields = (
            ("amount_out_total", self.amount_out_total, 1),
            ("max_legs", self.max_legs, 1),
            ("max_candidate_pools", self.max_candidate_pools, 1),
            ("max_enumerated_candidates", self.max_enumerated_candidates, 1),
            ("candidate_count", self.candidate_count, 0),
        )
        for field_name, value, min_value in int_fields:
            if not isinstance(value, int) or isinstance(value, bool) or value < int(min_value):
                raise ValueError(f"{field_name} must be an int >= {min_value}")
        if not all(isinstance(pool_id, str) and pool_id for pool_id in self.audit_pool_ids):
            raise ValueError("audit_pool_ids must be non-empty strings")
        if not all(isinstance(snapshot, dict) for snapshot in self.pool_snapshots):
            raise TypeError("pool_snapshots must be dict payloads")
        if not all(isinstance(candidate, SplitManyPoolsExactOutQuote) for candidate in self.candidates):
            raise TypeError("candidates must contain SplitManyPoolsExactOutQuote values")
        if self.schema != EXACT_OUT_MANY_POOL_CANDIDATE_DOMAIN_CONTRACT_SCHEMA:
            raise ValueError("unsupported candidate domain contract schema")

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "asset_in": str(self.asset_in),
            "asset_out": str(self.asset_out),
            "amount_out_total": int(self.amount_out_total),
            "max_legs": int(self.max_legs),
            "max_candidate_pools": int(self.max_candidate_pools),
            "max_enumerated_candidates": int(self.max_enumerated_candidates),
            "audit_pool_ids": [str(pool_id) for pool_id in self.audit_pool_ids],
            "pool_snapshots": [dict(snapshot) for snapshot in self.pool_snapshots],
            "candidates": [_quote_to_dict(candidate) for candidate in self.candidates],
            "candidate_count": int(self.candidate_count),
            "audit_pool_ids_sorted_unique": bool(self.audit_pool_ids_sorted_unique),
            "audit_pool_ids_within_budget": bool(self.audit_pool_ids_within_budget),
            "candidate_domain_nonempty": bool(self.candidate_domain_nonempty),
            "all_candidates_complete": bool(self.all_candidates_complete),
            "all_candidates_leg_bounded": bool(self.all_candidates_leg_bounded),
            "all_candidates_leg_pool_ids_sorted_unique": bool(self.all_candidates_leg_pool_ids_sorted_unique),
            "all_candidates_within_audit_pool_ids": bool(self.all_candidates_within_audit_pool_ids),
            "candidate_count_within_budget": bool(self.candidate_count_within_budget),
            "contract_ok": bool(self.contract_ok),
        }


@dataclass(frozen=True)
class ExactOutManyPoolPrefilterRow:
    pool_id: str
    cap_out: int
    probe_amount_out: int
    probe_amount_in: int
    scaled_unit_cost_u64: int

    def __post_init__(self) -> None:
        if not self.pool_id:
            raise ValueError("pool_id must be non-empty")
        int_fields = (
            ("cap_out", self.cap_out, 1),
            ("probe_amount_out", self.probe_amount_out, 1),
            ("probe_amount_in", self.probe_amount_in, 1),
            ("scaled_unit_cost_u64", self.scaled_unit_cost_u64, 0),
        )
        for field_name, value, min_value in int_fields:
            if not isinstance(value, int) or isinstance(value, bool) or value < int(min_value):
                raise ValueError(f"{field_name} must be an int >= {min_value}")
        if int(self.probe_amount_out) > int(self.cap_out):
            raise ValueError("probe_amount_out must not exceed cap_out")

    def to_dict(self) -> dict[str, Any]:
        return {
            "pool_id": str(self.pool_id),
            "cap_out": int(self.cap_out),
            "probe_amount_out": int(self.probe_amount_out),
            "probe_amount_in": int(self.probe_amount_in),
            "scaled_unit_cost_u64": int(self.scaled_unit_cost_u64),
        }


@dataclass(frozen=True)
class ExactOutManyPoolPrefilterContract:
    asset_in: str
    asset_out: str
    amount_out_total: int
    max_legs: int
    max_candidate_pools: int
    pool_snapshots: tuple[dict[str, Any], ...]
    feasible_rows: tuple[ExactOutManyPoolPrefilterRow, ...]
    selected_pool_ids: tuple[str, ...]
    feasible_rows_sorted_unique: bool
    selected_pool_ids_sorted_unique: bool
    selected_pool_ids_within_budget: bool
    selected_pool_ids_subset_of_feasible: bool
    selected_is_prefix_of_feasible_ranking: bool
    full_capacity_guard_feasible: bool
    selected_capacity_guard_feasible: bool
    contract_ok: bool
    schema: str = EXACT_OUT_MANY_POOL_PREFILTER_CONTRACT_SCHEMA

    def __post_init__(self) -> None:
        if not self.asset_in or not self.asset_out or self.asset_in == self.asset_out:
            raise ValueError("asset_in and asset_out must be non-empty and distinct")
        int_fields = (
            ("amount_out_total", self.amount_out_total, 1),
            ("max_legs", self.max_legs, 1),
            ("max_candidate_pools", self.max_candidate_pools, 1),
        )
        for field_name, value, min_value in int_fields:
            if not isinstance(value, int) or isinstance(value, bool) or value < int(min_value):
                raise ValueError(f"{field_name} must be an int >= {min_value}")
        if not all(isinstance(snapshot, dict) for snapshot in self.pool_snapshots):
            raise TypeError("pool_snapshots must be dict payloads")
        if not all(isinstance(row, ExactOutManyPoolPrefilterRow) for row in self.feasible_rows):
            raise TypeError("feasible_rows must contain ExactOutManyPoolPrefilterRow values")
        if not all(isinstance(pool_id, str) and pool_id for pool_id in self.selected_pool_ids):
            raise ValueError("selected_pool_ids must be non-empty strings")
        if self.schema != EXACT_OUT_MANY_POOL_PREFILTER_CONTRACT_SCHEMA:
            raise ValueError("unsupported prefilter contract schema")

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "asset_in": str(self.asset_in),
            "asset_out": str(self.asset_out),
            "amount_out_total": int(self.amount_out_total),
            "max_legs": int(self.max_legs),
            "max_candidate_pools": int(self.max_candidate_pools),
            "pool_snapshots": [dict(snapshot) for snapshot in self.pool_snapshots],
            "feasible_rows": [row.to_dict() for row in self.feasible_rows],
            "selected_pool_ids": [str(pool_id) for pool_id in self.selected_pool_ids],
            "feasible_rows_sorted_unique": bool(self.feasible_rows_sorted_unique),
            "selected_pool_ids_sorted_unique": bool(self.selected_pool_ids_sorted_unique),
            "selected_pool_ids_within_budget": bool(self.selected_pool_ids_within_budget),
            "selected_pool_ids_subset_of_feasible": bool(self.selected_pool_ids_subset_of_feasible),
            "selected_is_prefix_of_feasible_ranking": bool(self.selected_is_prefix_of_feasible_ranking),
            "full_capacity_guard_feasible": bool(self.full_capacity_guard_feasible),
            "selected_capacity_guard_feasible": bool(self.selected_capacity_guard_feasible),
            "contract_ok": bool(self.contract_ok),
        }


@dataclass(frozen=True)
class ExactOutManyPoolRepairedPrefilterContract:
    asset_in: str
    asset_out: str
    amount_out_total: int
    max_legs: int
    max_candidate_pools: int
    max_full_domain_pools: int
    max_enumerated_candidates: int
    pool_snapshots: tuple[dict[str, Any], ...]
    feasible_pool_ids: tuple[str, ...]
    current_selected_pool_ids: tuple[str, ...]
    repaired_selected_pool_ids: tuple[str, ...]
    strategy: str
    searched_subset_count: int
    current_selected_matches_full_canonical: bool
    repaired_selected_pool_ids_sorted_unique: bool
    repaired_selected_pool_ids_within_budget: bool
    repaired_selected_pool_ids_subset_of_feasible: bool
    repaired_selected_domain_matches_full_canonical: bool
    repaired_contraction_holds: bool
    contract_ok: bool
    schema: str = EXACT_OUT_MANY_POOL_REPAIRED_PREFILTER_CONTRACT_SCHEMA

    def __post_init__(self) -> None:
        if not self.asset_in or not self.asset_out or self.asset_in == self.asset_out:
            raise ValueError("asset_in and asset_out must be non-empty and distinct")
        int_fields = (
            ("amount_out_total", self.amount_out_total, 1),
            ("max_legs", self.max_legs, 1),
            ("max_candidate_pools", self.max_candidate_pools, 1),
            ("max_full_domain_pools", self.max_full_domain_pools, 1),
            ("max_enumerated_candidates", self.max_enumerated_candidates, 1),
            ("searched_subset_count", self.searched_subset_count, 0),
        )
        for field_name, value, min_value in int_fields:
            if not isinstance(value, int) or isinstance(value, bool) or value < int(min_value):
                raise ValueError(f"{field_name} must be an int >= {min_value}")
        if not all(isinstance(snapshot, dict) for snapshot in self.pool_snapshots):
            raise TypeError("pool_snapshots must be dict payloads")
        for field_name, pool_ids in (
            ("feasible_pool_ids", self.feasible_pool_ids),
            ("current_selected_pool_ids", self.current_selected_pool_ids),
            ("repaired_selected_pool_ids", self.repaired_selected_pool_ids),
        ):
            if not all(isinstance(pool_id, str) and pool_id for pool_id in pool_ids):
                raise ValueError(f"{field_name} must be non-empty strings")
        if not isinstance(self.strategy, str) or not self.strategy:
            raise ValueError("strategy must be a non-empty string")
        bool_fields = (
            self.current_selected_matches_full_canonical,
            self.repaired_selected_pool_ids_sorted_unique,
            self.repaired_selected_pool_ids_within_budget,
            self.repaired_selected_pool_ids_subset_of_feasible,
            self.repaired_selected_domain_matches_full_canonical,
            self.repaired_contraction_holds,
            self.contract_ok,
        )
        if not all(isinstance(value, bool) for value in bool_fields):
            raise TypeError("repaired prefilter contract flags must be bools")
        if self.schema != EXACT_OUT_MANY_POOL_REPAIRED_PREFILTER_CONTRACT_SCHEMA:
            raise ValueError("unsupported repaired prefilter contract schema")

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "asset_in": str(self.asset_in),
            "asset_out": str(self.asset_out),
            "amount_out_total": int(self.amount_out_total),
            "max_legs": int(self.max_legs),
            "max_candidate_pools": int(self.max_candidate_pools),
            "max_full_domain_pools": int(self.max_full_domain_pools),
            "max_enumerated_candidates": int(self.max_enumerated_candidates),
            "pool_snapshots": [dict(snapshot) for snapshot in self.pool_snapshots],
            "feasible_pool_ids": [str(pool_id) for pool_id in self.feasible_pool_ids],
            "current_selected_pool_ids": [str(pool_id) for pool_id in self.current_selected_pool_ids],
            "repaired_selected_pool_ids": [str(pool_id) for pool_id in self.repaired_selected_pool_ids],
            "strategy": str(self.strategy),
            "searched_subset_count": int(self.searched_subset_count),
            "current_selected_matches_full_canonical": bool(self.current_selected_matches_full_canonical),
            "repaired_selected_pool_ids_sorted_unique": bool(self.repaired_selected_pool_ids_sorted_unique),
            "repaired_selected_pool_ids_within_budget": bool(self.repaired_selected_pool_ids_within_budget),
            "repaired_selected_pool_ids_subset_of_feasible": bool(self.repaired_selected_pool_ids_subset_of_feasible),
            "repaired_selected_domain_matches_full_canonical": bool(self.repaired_selected_domain_matches_full_canonical),
            "repaired_contraction_holds": bool(self.repaired_contraction_holds),
            "contract_ok": bool(self.contract_ok),
        }


@dataclass(frozen=True)
class ExactOutManyPoolRepairedSelectedDomainOracleContract:
    asset_in: str
    asset_out: str
    amount_out_total: int
    max_legs: int
    max_candidate_pools: int
    max_candidates: int
    max_iters: int
    window: int
    brute_force_max: int
    max_full_domain_pools: int
    max_enumerated_candidates: int
    pool_snapshots: tuple[dict[str, Any], ...]
    repaired_contract: ExactOutManyPoolRepairedPrefilterContract
    audit: ExactOutManyPoolCanonicalityAudit
    audit_pool_ids_match_repaired_selected_pool_ids: bool
    contract_ok: bool
    schema: str = EXACT_OUT_MANY_POOL_REPAIRED_SELECTED_DOMAIN_ORACLE_CONTRACT_SCHEMA

    def __post_init__(self) -> None:
        if not self.asset_in or not self.asset_out or self.asset_in == self.asset_out:
            raise ValueError("asset_in and asset_out must be non-empty and distinct")
        for field_name, value, min_value in (
            ("amount_out_total", self.amount_out_total, 1),
            ("max_legs", self.max_legs, 1),
            ("max_candidate_pools", self.max_candidate_pools, 1),
            ("max_candidates", self.max_candidates, 1),
            ("max_iters", self.max_iters, 1),
            ("window", self.window, 0),
            ("brute_force_max", self.brute_force_max, 0),
            ("max_full_domain_pools", self.max_full_domain_pools, 1),
            ("max_enumerated_candidates", self.max_enumerated_candidates, 1),
        ):
            if not isinstance(value, int) or isinstance(value, bool) or int(value) < int(min_value):
                raise ValueError(f"{field_name} must be an int >= {min_value}")
        if not all(isinstance(snapshot, dict) for snapshot in self.pool_snapshots):
            raise TypeError("pool_snapshots must be dict payloads")
        if not isinstance(self.repaired_contract, ExactOutManyPoolRepairedPrefilterContract):
            raise TypeError("repaired_contract must be an ExactOutManyPoolRepairedPrefilterContract")
        if not isinstance(self.audit, ExactOutManyPoolCanonicalityAudit):
            raise TypeError("audit must be an ExactOutManyPoolCanonicalityAudit")
        if not isinstance(self.audit_pool_ids_match_repaired_selected_pool_ids, bool):
            raise TypeError("audit_pool_ids_match_repaired_selected_pool_ids must be a bool")
        if not isinstance(self.contract_ok, bool):
            raise TypeError("contract_ok must be a bool")
        if self.schema != EXACT_OUT_MANY_POOL_REPAIRED_SELECTED_DOMAIN_ORACLE_CONTRACT_SCHEMA:
            raise ValueError("unsupported repaired selected-domain oracle contract schema")

    def _repaired_selected_domain_summary(self) -> dict[str, Any]:
        audit_payload = self.audit.to_dict()
        return {
            "repaired_selected_pool_ids": [str(pool_id) for pool_id in self.repaired_contract.repaired_selected_pool_ids],
            "repaired_selected_domain_matches_full_canonical": bool(
                self.repaired_contract.repaired_selected_domain_matches_full_canonical
            ),
            "audit_pool_ids_match_repaired_selected_pool_ids": bool(self.audit_pool_ids_match_repaired_selected_pool_ids),
            "repaired_selected_domain_runtime_quote": audit_payload["runtime_quote"],
            "repaired_selected_domain_runtime_projected_path": audit_payload["runtime_projected_path"],
            "repaired_selected_domain_canonical_quote": audit_payload["canonical_winner_quote"],
            "repaired_selected_domain_canonical_projected_path": audit_payload["canonical_winner_projected_path"],
            "repaired_selected_domain_runtime_matches_canonical": bool(audit_payload["runtime_matches_canonical"]),
            "repaired_selected_domain_runtime_matches_canonical_projected_path": bool(
                audit_payload["runtime_matches_canonical_projected_path"]
            ),
            "repaired_projection_cover_available": bool(audit_payload["projection_cover_available"]),
            "repaired_projection_cover_holds": audit_payload["projection_cover_holds"],
            "replacement_quote_matches_full_canonical": bool(
                self.repaired_contract.repaired_selected_domain_matches_full_canonical
                and self.audit.runtime_matches_canonical
            ),
        }

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "asset_in": str(self.asset_in),
            "asset_out": str(self.asset_out),
            "amount_out_total": int(self.amount_out_total),
            "max_legs": int(self.max_legs),
            "max_candidate_pools": int(self.max_candidate_pools),
            "max_candidates": int(self.max_candidates),
            "max_iters": int(self.max_iters),
            "window": int(self.window),
            "brute_force_max": int(self.brute_force_max),
            "max_full_domain_pools": int(self.max_full_domain_pools),
            "max_enumerated_candidates": int(self.max_enumerated_candidates),
            "pool_snapshots": [dict(snapshot) for snapshot in self.pool_snapshots],
            "repaired_contract": self.repaired_contract.to_dict(),
            "audit": self.audit.to_dict(),
            "contract_ok": bool(self.contract_ok),
            **self._repaired_selected_domain_summary(),
        }


@dataclass(frozen=True)
class ExactOutManyPoolOracleContract:
    asset_in: str
    asset_out: str
    amount_out_total: int
    max_legs: int
    max_candidate_pools: int
    max_candidates: int
    max_iters: int
    window: int
    brute_force_max: int
    max_full_domain_pools: int
    max_enumerated_candidates: int
    pool_snapshots: tuple[dict[str, Any], ...]
    audit: ExactOutManyPoolCanonicalityAudit

    @property
    def contract_ok(self) -> bool:
        projection_cover = self.audit.projection_cover_audit
        if projection_cover is None:
            return False
        runtime_projected_path = _quote_to_projected_path_payload(self.audit.runtime_quote)
        canonical_projected_path = _quote_to_projected_path_payload(self.audit.canonical_winner_quote)
        return bool(
            self.audit.runtime_matches_canonical
            and runtime_projected_path == canonical_projected_path
            and projection_cover.projection_cover_holds
        )

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": EXACT_OUT_MANY_POOL_ORACLE_CONTRACT_SCHEMA,
            "asset_in": str(self.asset_in),
            "asset_out": str(self.asset_out),
            "amount_out_total": int(self.amount_out_total),
            "max_legs": int(self.max_legs),
            "max_candidate_pools": int(self.max_candidate_pools),
            "max_candidates": int(self.max_candidates),
            "max_iters": int(self.max_iters),
            "window": int(self.window),
            "brute_force_max": int(self.brute_force_max),
            "max_full_domain_pools": int(self.max_full_domain_pools),
            "max_enumerated_candidates": int(self.max_enumerated_candidates),
            "pool_snapshots": [dict(snapshot) for snapshot in self.pool_snapshots],
            "audit": self.audit.to_dict(),
            "contract_ok": bool(self.contract_ok),
        }


@dataclass(frozen=True)
class ExactOutManyPoolGuardedQuotePacket:
    guard_ok: bool
    quote: SplitManyPoolsExactOutQuote | None
    error: str | None
    contract: ExactOutManyPoolOracleContract
    schema: str = EXACT_OUT_MANY_POOL_GUARDED_QUOTE_PACKET_SCHEMA

    def __post_init__(self) -> None:
        if not isinstance(self.guard_ok, bool):
            raise TypeError("guard_ok must be a bool")
        if self.quote is not None and not isinstance(self.quote, SplitManyPoolsExactOutQuote):
            raise TypeError("quote must be a SplitManyPoolsExactOutQuote or None")
        if self.error is not None and (not isinstance(self.error, str) or not self.error):
            raise ValueError("error must be a non-empty string or None")
        if not isinstance(self.contract, ExactOutManyPoolOracleContract):
            raise TypeError("contract must be an ExactOutManyPoolOracleContract")
        if self.schema != EXACT_OUT_MANY_POOL_GUARDED_QUOTE_PACKET_SCHEMA:
            raise ValueError("unsupported guarded quote packet schema")

    def _selected_domain_summary(self) -> dict[str, Any]:
        projection_cover = self.contract.audit.projection_cover_audit
        runtime_quote = _quote_to_dict(self.contract.audit.runtime_quote)
        runtime_projected_path = _quote_to_projected_path_payload(self.contract.audit.runtime_quote)
        quote_payload = None if self.quote is None else _quote_to_dict(self.quote)
        quote_projected_path = None if self.quote is None else _quote_to_projected_path_payload(self.quote)
        canonical_projected_path = (
            None
            if projection_cover is None
            else [
                [str(pool_id), int(amount_out), int(amount_in)]
                for pool_id, amount_out, amount_in in projection_cover.canonical_quote_projected_path
            ]
        )
        return {
            "selected_domain_runtime_quote": runtime_quote,
            "selected_domain_runtime_projected_path": runtime_projected_path,
            "selected_domain_projection_cover_available": bool(projection_cover is not None),
            "selected_domain_projection_cover_holds": (
                None if projection_cover is None else bool(projection_cover.projection_cover_holds)
            ),
            "selected_domain_canonical_projected_path": canonical_projected_path,
            "selected_runtime_matches_selected_canonical_projected_path": (
                None if canonical_projected_path is None else bool(runtime_projected_path == canonical_projected_path)
            ),
            "guarded_quote": quote_payload,
            "guarded_quote_projected_path": quote_projected_path,
            "guarded_quote_matches_runtime_quote": (
                None if quote_payload is None else bool(quote_payload == runtime_quote)
            ),
            "guarded_quote_matches_canonical_projected_path": (
                None
                if quote_projected_path is None or canonical_projected_path is None
                else bool(quote_projected_path == canonical_projected_path)
            ),
        }

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "guard_ok": bool(self.guard_ok),
            "quote": None if self.quote is None else _quote_to_dict(self.quote),
            "error": self.error,
            "contract": self.contract.to_dict(),
            **self._selected_domain_summary(),
        }


@dataclass(frozen=True)
class ExactOutManyPoolRepairedAdvisoryQuotePacket:
    packet_ok: bool
    advisory_quote: SplitManyPoolsExactOutQuote | None
    runtime_quote: SplitManyPoolsExactOutQuote
    runtime_matches_advisory: bool
    error: str | None
    max_candidates: int
    max_iters: int
    window: int
    brute_force_max: int
    repaired_contract: ExactOutManyPoolRepairedPrefilterContract
    projection_cover_audit: "ExactOutManyPoolProjectionCoverAudit | None" = None
    schema: str = EXACT_OUT_MANY_POOL_REPAIRED_ADVISORY_QUOTE_PACKET_SCHEMA

    def __post_init__(self) -> None:
        if not isinstance(self.packet_ok, bool):
            raise TypeError("packet_ok must be a bool")
        if self.advisory_quote is not None and not isinstance(self.advisory_quote, SplitManyPoolsExactOutQuote):
            raise TypeError("advisory_quote must be a SplitManyPoolsExactOutQuote or None")
        if not isinstance(self.runtime_quote, SplitManyPoolsExactOutQuote):
            raise TypeError("runtime_quote must be a SplitManyPoolsExactOutQuote")
        if not isinstance(self.runtime_matches_advisory, bool):
            raise TypeError("runtime_matches_advisory must be a bool")
        if self.error is not None and (not isinstance(self.error, str) or not self.error):
            raise ValueError("error must be a non-empty string or None")
        for field_name, value, min_value in (
            ("max_candidates", self.max_candidates, 1),
            ("max_iters", self.max_iters, 1),
            ("window", self.window, 0),
            ("brute_force_max", self.brute_force_max, 0),
        ):
            if not isinstance(value, int) or isinstance(value, bool) or int(value) < int(min_value):
                raise ValueError(f"{field_name} must be an int >= {min_value}")
        if not isinstance(self.repaired_contract, ExactOutManyPoolRepairedPrefilterContract):
            raise TypeError("repaired_contract must be an ExactOutManyPoolRepairedPrefilterContract")
        if self.projection_cover_audit is not None and not isinstance(self.projection_cover_audit, ExactOutManyPoolProjectionCoverAudit):
            raise TypeError("projection_cover_audit must be an ExactOutManyPoolProjectionCoverAudit or None")
        if self.schema != EXACT_OUT_MANY_POOL_REPAIRED_ADVISORY_QUOTE_PACKET_SCHEMA:
            raise ValueError("unsupported repaired advisory quote packet schema")

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "packet_ok": bool(self.packet_ok),
            "advisory_quote": None if self.advisory_quote is None else _quote_to_dict(self.advisory_quote),
            "runtime_quote": _quote_to_dict(self.runtime_quote),
            "runtime_matches_advisory": bool(self.runtime_matches_advisory),
            "error": self.error,
            "max_candidates": int(self.max_candidates),
            "max_iters": int(self.max_iters),
            "window": int(self.window),
            "brute_force_max": int(self.brute_force_max),
            "repaired_contract": self.repaired_contract.to_dict(),
            "projection_cover_audit": None if self.projection_cover_audit is None else self.projection_cover_audit.to_dict(),
        }


@dataclass(frozen=True)
class ExactOutManyPoolRepairedFullDomainCertifiedPacket:
    packet_ok: bool
    repaired_quote: SplitManyPoolsExactOutQuote | None
    repaired_matches_full_canonical: bool
    error: str | None
    full_domain_feasible_pool_ids: tuple[str, ...]
    full_domain_candidate_count: int
    full_domain_canonical_quote: SplitManyPoolsExactOutQuote
    repaired_packet: ExactOutManyPoolRepairedAdvisoryQuotePacket
    full_domain_certificate: ExactOutRouteCanonicalCertificate
    schema: str = EXACT_OUT_MANY_POOL_REPAIRED_FULL_DOMAIN_CERTIFIED_PACKET_SCHEMA

    def __post_init__(self) -> None:
        if not isinstance(self.packet_ok, bool):
            raise TypeError("packet_ok must be a bool")
        if self.repaired_quote is not None and not isinstance(self.repaired_quote, SplitManyPoolsExactOutQuote):
            raise TypeError("repaired_quote must be a SplitManyPoolsExactOutQuote or None")
        if not isinstance(self.repaired_matches_full_canonical, bool):
            raise TypeError("repaired_matches_full_canonical must be a bool")
        if self.error is not None and (not isinstance(self.error, str) or not self.error):
            raise ValueError("error must be a non-empty string or None")
        if not all(isinstance(pool_id, str) and pool_id for pool_id in self.full_domain_feasible_pool_ids):
            raise ValueError("full_domain_feasible_pool_ids must be non-empty strings")
        if not isinstance(self.full_domain_candidate_count, int) or isinstance(self.full_domain_candidate_count, bool):
            raise TypeError("full_domain_candidate_count must be an int")
        if self.full_domain_candidate_count <= 0:
            raise ValueError("full_domain_candidate_count must be positive")
        if not isinstance(self.full_domain_canonical_quote, SplitManyPoolsExactOutQuote):
            raise TypeError("full_domain_canonical_quote must be a SplitManyPoolsExactOutQuote")
        if not isinstance(self.repaired_packet, ExactOutManyPoolRepairedAdvisoryQuotePacket):
            raise TypeError("repaired_packet must be an ExactOutManyPoolRepairedAdvisoryQuotePacket")
        if not isinstance(self.full_domain_certificate, ExactOutRouteCanonicalCertificate):
            raise TypeError("full_domain_certificate must be an ExactOutRouteCanonicalCertificate")
        if self.schema != EXACT_OUT_MANY_POOL_REPAIRED_FULL_DOMAIN_CERTIFIED_PACKET_SCHEMA:
            raise ValueError("unsupported repaired full-domain certified packet schema")
        if self.full_domain_certificate.winner_quote != self.full_domain_canonical_quote:
            raise ValueError("full_domain_certificate winner_quote must equal full_domain_canonical_quote")
        if self.packet_ok:
            if not self.repaired_packet.packet_ok:
                raise ValueError("packet_ok requires repaired_packet.packet_ok")
            if self.repaired_quote is None:
                raise ValueError("packet_ok requires repaired_quote")
            if not self.repaired_matches_full_canonical:
                raise ValueError("packet_ok requires repaired_matches_full_canonical")
            if self.error is not None:
                raise ValueError("packet_ok packet must not carry error")
        else:
            if self.error is None:
                raise ValueError("failed packet must carry an error")

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "packet_ok": bool(self.packet_ok),
            "repaired_quote": None if self.repaired_quote is None else _quote_to_dict(self.repaired_quote),
            "repaired_matches_full_canonical": bool(self.repaired_matches_full_canonical),
            "error": self.error,
            "full_domain_feasible_pool_ids": [str(pool_id) for pool_id in self.full_domain_feasible_pool_ids],
            "full_domain_candidate_count": int(self.full_domain_candidate_count),
            "full_domain_canonical_quote": _quote_to_dict(self.full_domain_canonical_quote),
            "repaired_packet": self.repaired_packet.to_dict(),
            "full_domain_certificate": self.full_domain_certificate.to_dict(),
        }


@dataclass(frozen=True)
class ExactOutManyPoolKeyCoverDominationWitness:
    full_candidate_index: int
    selected_candidate_index: int
    full_route_key_rank_u64: int
    selected_route_key_rank_u64: int
    full_route_key: ExactOutRouteCanonicalKey
    selected_route_key: ExactOutRouteCanonicalKey

    def __post_init__(self) -> None:
        for field_name, value, max_value in (
            ("full_candidate_index", self.full_candidate_index, 0xFFFFFFFF),
            ("selected_candidate_index", self.selected_candidate_index, 0xFFFFFFFF),
            ("full_route_key_rank_u64", self.full_route_key_rank_u64, 0xFFFFFFFFFFFFFFFF),
            ("selected_route_key_rank_u64", self.selected_route_key_rank_u64, 0xFFFFFFFFFFFFFFFF),
        ):
            if not isinstance(value, int) or isinstance(value, bool):
                raise TypeError(f"{field_name} must be an int")
            if int(value) < 0 or int(value) > int(max_value):
                raise ValueError(f"{field_name} out of range")
        if not isinstance(self.full_route_key, ExactOutRouteCanonicalKey):
            raise TypeError("full_route_key must be an ExactOutRouteCanonicalKey")
        if not isinstance(self.selected_route_key, ExactOutRouteCanonicalKey):
            raise TypeError("selected_route_key must be an ExactOutRouteCanonicalKey")
        if self.selected_route_key > self.full_route_key:
            raise ValueError("selected_route_key must dominate full_route_key")

    def to_dict(self) -> dict[str, Any]:
        return {
            "full_candidate_index": int(self.full_candidate_index),
            "selected_candidate_index": int(self.selected_candidate_index),
            "full_route_key_rank_u64": int(self.full_route_key_rank_u64),
            "selected_route_key_rank_u64": int(self.selected_route_key_rank_u64),
            "full_route_key": _route_key_to_dict(self.full_route_key),
            "selected_route_key": _route_key_to_dict(self.selected_route_key),
        }


@dataclass(frozen=True)
class ExactOutManyPoolRepairedKeyCoverPacket:
    packet_ok: bool
    error: str | None
    selected_keys_subset_full_keys: bool
    key_cover_holds: bool
    selected_domain_canonical_matches_full_domain_canonical: bool
    selected_candidate_count: int
    full_candidate_count: int
    domination_witnesses: tuple[ExactOutManyPoolKeyCoverDominationWitness, ...]
    selected_domain_contract: ExactOutManyPoolRepairedSelectedDomainOracleContract
    repaired_full_domain_packet: ExactOutManyPoolRepairedFullDomainCertifiedPacket
    schema: str = EXACT_OUT_MANY_POOL_REPAIRED_KEY_COVER_PACKET_SCHEMA

    def __post_init__(self) -> None:
        if not isinstance(self.packet_ok, bool):
            raise TypeError("packet_ok must be a bool")
        if self.error is not None and (not isinstance(self.error, str) or not self.error):
            raise ValueError("error must be a non-empty string or None")
        for field_name, flag_value in (
            ("selected_keys_subset_full_keys", self.selected_keys_subset_full_keys),
            ("key_cover_holds", self.key_cover_holds),
            ("selected_domain_canonical_matches_full_domain_canonical", self.selected_domain_canonical_matches_full_domain_canonical),
        ):
            if not isinstance(flag_value, bool):
                raise TypeError(f"{field_name} must be a bool")
        for field_name, count_value in (
            ("selected_candidate_count", self.selected_candidate_count),
            ("full_candidate_count", self.full_candidate_count),
        ):
            if not isinstance(count_value, int) or isinstance(count_value, bool):
                raise TypeError(f"{field_name} must be an int")
            if int(count_value) <= 0:
                raise ValueError(f"{field_name} must be positive")
        if not all(isinstance(witness, ExactOutManyPoolKeyCoverDominationWitness) for witness in self.domination_witnesses):
            raise TypeError("domination_witnesses must be ExactOutManyPoolKeyCoverDominationWitness values")
        if not isinstance(self.selected_domain_contract, ExactOutManyPoolRepairedSelectedDomainOracleContract):
            raise TypeError("selected_domain_contract must be an ExactOutManyPoolRepairedSelectedDomainOracleContract")
        if not isinstance(self.repaired_full_domain_packet, ExactOutManyPoolRepairedFullDomainCertifiedPacket):
            raise TypeError("repaired_full_domain_packet must be an ExactOutManyPoolRepairedFullDomainCertifiedPacket")
        if self.schema != EXACT_OUT_MANY_POOL_REPAIRED_KEY_COVER_PACKET_SCHEMA:
            raise ValueError("unsupported repaired key-cover packet schema")
        if len(self.domination_witnesses) > int(self.full_candidate_count):
            raise ValueError("domination_witnesses cannot exceed full_candidate_count")
        if self.packet_ok:
            if not self.selected_domain_contract.contract_ok:
                raise ValueError("packet_ok requires selected_domain_contract.contract_ok")
            if not self.repaired_full_domain_packet.packet_ok:
                raise ValueError("packet_ok requires repaired_full_domain_packet.packet_ok")
            if not self.selected_keys_subset_full_keys:
                raise ValueError("packet_ok requires selected_keys_subset_full_keys")
            if not self.key_cover_holds:
                raise ValueError("packet_ok requires key_cover_holds")
            if not self.selected_domain_canonical_matches_full_domain_canonical:
                raise ValueError("packet_ok requires selected_domain_canonical_matches_full_domain_canonical")
            if self.error is not None:
                raise ValueError("packet_ok packet must not carry error")
        else:
            if self.error is None:
                raise ValueError("failed packet must carry an error")

    def _candidate_key_set_summary(self) -> dict[str, Any]:
        selected_candidates = self.selected_domain_contract.audit.certificate.candidates
        full_candidates = self.repaired_full_domain_packet.full_domain_certificate.candidates
        return {
            "selected_candidate_keys": [_candidate_key_payload(candidate) for candidate in selected_candidates],
            "full_candidate_keys": [_candidate_key_payload(candidate) for candidate in full_candidates],
        }

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "packet_ok": bool(self.packet_ok),
            "error": self.error,
            "selected_keys_subset_full_keys": bool(self.selected_keys_subset_full_keys),
            "key_cover_holds": bool(self.key_cover_holds),
            "selected_domain_canonical_matches_full_domain_canonical": bool(
                self.selected_domain_canonical_matches_full_domain_canonical
            ),
            "selected_candidate_count": int(self.selected_candidate_count),
            "full_candidate_count": int(self.full_candidate_count),
            "domination_witnesses": [witness.to_dict() for witness in self.domination_witnesses],
            "selected_domain_contract": self.selected_domain_contract.to_dict(),
            "repaired_full_domain_packet": self.repaired_full_domain_packet.to_dict(),
            **self._candidate_key_set_summary(),
        }


@dataclass(frozen=True)
class ExactOutManyPoolRepairedKeyCoverInterpretationPacket:
    packet_ok: bool
    error: str | None
    selected_winner_index_in_range: bool
    selected_winner_matches_certificate: bool
    selected_winner_key_minimal: bool
    domination_witness_indices_in_range: bool
    domination_witnesses_cover_full_candidates: bool
    domination_witness_keys_match_candidates: bool
    domination_witnesses_dominate: bool
    key_cover_packet: ExactOutManyPoolRepairedKeyCoverPacket
    schema: str = EXACT_OUT_MANY_POOL_REPAIRED_KEY_COVER_INTERPRETATION_PACKET_SCHEMA

    def __post_init__(self) -> None:
        if not isinstance(self.packet_ok, bool):
            raise TypeError("packet_ok must be a bool")
        if self.error is not None and (not isinstance(self.error, str) or not self.error):
            raise ValueError("error must be a non-empty string or None")
        for field_name, value in (
            ("selected_winner_index_in_range", self.selected_winner_index_in_range),
            ("selected_winner_matches_certificate", self.selected_winner_matches_certificate),
            ("selected_winner_key_minimal", self.selected_winner_key_minimal),
            ("domination_witness_indices_in_range", self.domination_witness_indices_in_range),
            ("domination_witnesses_cover_full_candidates", self.domination_witnesses_cover_full_candidates),
            ("domination_witness_keys_match_candidates", self.domination_witness_keys_match_candidates),
            ("domination_witnesses_dominate", self.domination_witnesses_dominate),
        ):
            if not isinstance(value, bool):
                raise TypeError(f"{field_name} must be a bool")
        if not isinstance(self.key_cover_packet, ExactOutManyPoolRepairedKeyCoverPacket):
            raise TypeError("key_cover_packet must be an ExactOutManyPoolRepairedKeyCoverPacket")
        if self.schema != EXACT_OUT_MANY_POOL_REPAIRED_KEY_COVER_INTERPRETATION_PACKET_SCHEMA:
            raise ValueError("unsupported repaired key-cover interpretation packet schema")
        if self.packet_ok:
            if not self.key_cover_packet.packet_ok:
                raise ValueError("packet_ok requires key_cover_packet.packet_ok")
            if not self.selected_winner_index_in_range:
                raise ValueError("packet_ok requires selected_winner_index_in_range")
            if not self.selected_winner_matches_certificate:
                raise ValueError("packet_ok requires selected_winner_matches_certificate")
            if not self.selected_winner_key_minimal:
                raise ValueError("packet_ok requires selected_winner_key_minimal")
            if not self.domination_witness_indices_in_range:
                raise ValueError("packet_ok requires domination_witness_indices_in_range")
            if not self.domination_witnesses_cover_full_candidates:
                raise ValueError("packet_ok requires domination_witnesses_cover_full_candidates")
            if not self.domination_witness_keys_match_candidates:
                raise ValueError("packet_ok requires domination_witness_keys_match_candidates")
            if not self.domination_witnesses_dominate:
                raise ValueError("packet_ok requires domination_witnesses_dominate")
            if self.error is not None:
                raise ValueError("packet_ok packet must not carry error")
        else:
            if self.error is None:
                raise ValueError("failed packet must carry an error")

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "packet_ok": bool(self.packet_ok),
            "error": self.error,
            "selected_winner_index_in_range": bool(self.selected_winner_index_in_range),
            "selected_winner_matches_certificate": bool(self.selected_winner_matches_certificate),
            "selected_winner_key_minimal": bool(self.selected_winner_key_minimal),
            "domination_witness_indices_in_range": bool(self.domination_witness_indices_in_range),
            "domination_witnesses_cover_full_candidates": bool(self.domination_witnesses_cover_full_candidates),
            "domination_witness_keys_match_candidates": bool(self.domination_witness_keys_match_candidates),
            "domination_witnesses_dominate": bool(self.domination_witnesses_dominate),
            "key_cover_packet": self.key_cover_packet.to_dict(),
        }


@dataclass(frozen=True)
class ExactOutManyPoolBoundedWorkaroundPacket:
    oracle_contract: ExactOutManyPoolOracleContract
    repaired_packet: ExactOutManyPoolRepairedAdvisoryQuotePacket
    repaired_full_domain_packet: ExactOutManyPoolRepairedFullDomainCertifiedPacket
    runtime_quotes_agree: bool
    runtime_matches_repaired_advisory: bool
    packet_ok: bool
    schema: str = EXACT_OUT_MANY_POOL_BOUNDED_WORKAROUND_PACKET_SCHEMA

    def __post_init__(self) -> None:
        if not isinstance(self.oracle_contract, ExactOutManyPoolOracleContract):
            raise TypeError("oracle_contract must be an ExactOutManyPoolOracleContract")
        if not isinstance(self.repaired_packet, ExactOutManyPoolRepairedAdvisoryQuotePacket):
            raise TypeError("repaired_packet must be an ExactOutManyPoolRepairedAdvisoryQuotePacket")
        if not isinstance(self.repaired_full_domain_packet, ExactOutManyPoolRepairedFullDomainCertifiedPacket):
            raise TypeError("repaired_full_domain_packet must be an ExactOutManyPoolRepairedFullDomainCertifiedPacket")
        if not isinstance(self.runtime_quotes_agree, bool):
            raise TypeError("runtime_quotes_agree must be a bool")
        if not isinstance(self.runtime_matches_repaired_advisory, bool):
            raise TypeError("runtime_matches_repaired_advisory must be a bool")
        if not isinstance(self.packet_ok, bool):
            raise TypeError("packet_ok must be a bool")
        if self.schema != EXACT_OUT_MANY_POOL_BOUNDED_WORKAROUND_PACKET_SCHEMA:
            raise ValueError("unsupported bounded workaround packet schema")

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "oracle_contract": self.oracle_contract.to_dict(),
            "repaired_packet": self.repaired_packet.to_dict(),
            "repaired_full_domain_packet": self.repaired_full_domain_packet.to_dict(),
            "runtime_quotes_agree": bool(self.runtime_quotes_agree),
            "runtime_matches_repaired_advisory": bool(self.runtime_matches_repaired_advisory),
            "packet_ok": bool(self.packet_ok),
        }


@dataclass(frozen=True)
class ExactOutManyPoolBoundedAdvisoryQuotePacket:
    packet_ok: bool
    advisory_quote: SplitManyPoolsExactOutQuote | None
    quote_source: str | None
    repaired_advisory_available: bool
    quote_matches_runtime: bool
    quote_matches_repaired_advisory: bool
    error: str | None
    workaround_packet: ExactOutManyPoolBoundedWorkaroundPacket
    schema: str = EXACT_OUT_MANY_POOL_BOUNDED_ADVISORY_QUOTE_PACKET_SCHEMA

    def __post_init__(self) -> None:
        if not isinstance(self.packet_ok, bool):
            raise TypeError("packet_ok must be a bool")
        if self.advisory_quote is not None and not isinstance(self.advisory_quote, SplitManyPoolsExactOutQuote):
            raise TypeError("advisory_quote must be a SplitManyPoolsExactOutQuote or None")
        if self.quote_source is not None and self.quote_source not in (
            "selected_domain_runtime",
            "repaired_bounded_advisory",
        ):
            raise ValueError("unsupported quote_source")
        if not isinstance(self.repaired_advisory_available, bool):
            raise TypeError("repaired_advisory_available must be a bool")
        if not isinstance(self.quote_matches_runtime, bool):
            raise TypeError("quote_matches_runtime must be a bool")
        if not isinstance(self.quote_matches_repaired_advisory, bool):
            raise TypeError("quote_matches_repaired_advisory must be a bool")
        if self.error is not None and (not isinstance(self.error, str) or not self.error):
            raise ValueError("error must be a non-empty string or None")
        if not isinstance(self.workaround_packet, ExactOutManyPoolBoundedWorkaroundPacket):
            raise TypeError("workaround_packet must be an ExactOutManyPoolBoundedWorkaroundPacket")
        if self.schema != EXACT_OUT_MANY_POOL_BOUNDED_ADVISORY_QUOTE_PACKET_SCHEMA:
            raise ValueError("unsupported bounded advisory quote packet schema")
        if self.packet_ok:
            if self.advisory_quote is None:
                raise ValueError("packet_ok requires advisory_quote")
            if self.quote_source is None:
                raise ValueError("packet_ok requires quote_source")
            if self.error is not None:
                raise ValueError("packet_ok packet must not carry error")
        else:
            if self.advisory_quote is not None or self.quote_source is not None:
                raise ValueError("failed packet must not carry advisory quote or source")
            if self.error is None:
                raise ValueError("failed packet must carry an error")

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "packet_ok": bool(self.packet_ok),
            "advisory_quote": None if self.advisory_quote is None else _quote_to_dict(self.advisory_quote),
            "quote_source": self.quote_source,
            "repaired_advisory_available": bool(self.repaired_advisory_available),
            "quote_matches_runtime": bool(self.quote_matches_runtime),
            "quote_matches_repaired_advisory": bool(self.quote_matches_repaired_advisory),
            "error": self.error,
            "workaround_packet": self.workaround_packet.to_dict(),
        }


@dataclass(frozen=True)
class ExactOutManyPoolCertifiedWinnerPacket:
    domain_contract: ExactOutManyPoolCandidateDomainContract
    guarded_packet: ExactOutManyPoolGuardedQuotePacket
    packet_ok: bool
    schema: str = EXACT_OUT_MANY_POOL_CERTIFIED_WINNER_PACKET_SCHEMA

    def __post_init__(self) -> None:
        if not isinstance(self.domain_contract, ExactOutManyPoolCandidateDomainContract):
            raise TypeError("domain_contract must be an ExactOutManyPoolCandidateDomainContract")
        if not isinstance(self.guarded_packet, ExactOutManyPoolGuardedQuotePacket):
            raise TypeError("guarded_packet must be an ExactOutManyPoolGuardedQuotePacket")
        if not isinstance(self.packet_ok, bool):
            raise TypeError("packet_ok must be a bool")
        if self.schema != EXACT_OUT_MANY_POOL_CERTIFIED_WINNER_PACKET_SCHEMA:
            raise ValueError("unsupported certified winner packet schema")

    def _selected_domain_summary(self) -> dict[str, Any]:
        guarded_payload = self.guarded_packet.to_dict()
        return {
            "selected_domain_runtime_quote": guarded_payload["selected_domain_runtime_quote"],
            "selected_domain_runtime_projected_path": guarded_payload["selected_domain_runtime_projected_path"],
            "selected_domain_projection_cover_available": guarded_payload["selected_domain_projection_cover_available"],
            "selected_domain_projection_cover_holds": guarded_payload["selected_domain_projection_cover_holds"],
            "selected_domain_canonical_projected_path": guarded_payload["selected_domain_canonical_projected_path"],
            "selected_runtime_matches_selected_canonical_projected_path": guarded_payload[
                "selected_runtime_matches_selected_canonical_projected_path"
            ],
            "certified_quote": guarded_payload["guarded_quote"],
            "certified_quote_projected_path": guarded_payload["guarded_quote_projected_path"],
            "certified_quote_matches_runtime_quote": guarded_payload["guarded_quote_matches_runtime_quote"],
            "certified_quote_matches_canonical_projected_path": guarded_payload[
                "guarded_quote_matches_canonical_projected_path"
            ],
        }

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "domain_contract": self.domain_contract.to_dict(),
            "guarded_packet": self.guarded_packet.to_dict(),
            "packet_ok": bool(self.packet_ok),
            **self._selected_domain_summary(),
        }


def _projection_cover_canonical_path_payload(
    projection_cover: ExactOutManyPoolProjectionCoverAudit | None,
) -> list[list[object]] | None:
    if projection_cover is None:
        return None
    return [
        [str(pool_id), int(amount_out), int(amount_in)]
        for pool_id, amount_out, amount_in in projection_cover.canonical_quote_projected_path
    ]


def _projection_cover_holds_payload(projection_cover: ExactOutManyPoolProjectionCoverAudit | None) -> bool | None:
    return None if projection_cover is None else bool(projection_cover.projection_cover_holds)


_PayloadItems = tuple[tuple[str, Any], ...]


def _repaired_full_domain_summary_items(
    *,
    repaired_full_domain_payload: Mapping[str, Any],
    effective_quote: dict[str, Any] | None,
) -> _PayloadItems:
    return (
        ("repaired_full_domain_packet_ok", bool(repaired_full_domain_payload["packet_ok"])),
        (
            "repaired_quote_matches_full_domain_canonical",
            bool(repaired_full_domain_payload["repaired_matches_full_canonical"]),
        ),
        ("repaired_full_domain_feasible_pool_ids", repaired_full_domain_payload["full_domain_feasible_pool_ids"]),
        ("repaired_full_domain_candidate_count", repaired_full_domain_payload["full_domain_candidate_count"]),
        ("repaired_full_domain_canonical_quote", repaired_full_domain_payload["full_domain_canonical_quote"]),
        (
            "effective_quote_matches_full_domain_canonical",
            None
            if effective_quote is None
            else bool(effective_quote == repaired_full_domain_payload["full_domain_canonical_quote"]),
        ),
    )


def _repaired_key_cover_summary_items(
    *,
    key_cover_packet: ExactOutManyPoolRepairedKeyCoverPacket,
    interpretation_packet: ExactOutManyPoolRepairedKeyCoverInterpretationPacket,
) -> _PayloadItems:
    return (
        ("repaired_key_cover_packet_ok", bool(key_cover_packet.packet_ok)),
        ("repaired_selected_keys_subset_full_keys", bool(key_cover_packet.selected_keys_subset_full_keys)),
        ("repaired_key_cover_holds", bool(key_cover_packet.key_cover_holds)),
        (
            "repaired_selected_domain_canonical_matches_full_domain_canonical",
            bool(key_cover_packet.selected_domain_canonical_matches_full_domain_canonical),
        ),
        ("repaired_key_cover_witness_count", len(key_cover_packet.domination_witnesses)),
        ("repaired_key_cover_interpretation_packet_ok", bool(interpretation_packet.packet_ok)),
        (
            "repaired_key_cover_selected_winner_index_in_range",
            bool(interpretation_packet.selected_winner_index_in_range),
        ),
        (
            "repaired_key_cover_selected_winner_matches_certificate",
            bool(interpretation_packet.selected_winner_matches_certificate),
        ),
        ("repaired_key_cover_selected_winner_key_minimal", bool(interpretation_packet.selected_winner_key_minimal)),
        (
            "repaired_key_cover_witness_indices_in_range",
            bool(interpretation_packet.domination_witness_indices_in_range),
        ),
        (
            "repaired_key_cover_witness_coverage_complete",
            bool(interpretation_packet.domination_witnesses_cover_full_candidates),
        ),
        (
            "repaired_key_cover_witness_keys_match_candidates",
            bool(interpretation_packet.domination_witness_keys_match_candidates),
        ),
        ("repaired_key_cover_witness_domination_holds", bool(interpretation_packet.domination_witnesses_dominate)),
    )


def _effective_projection_cover_summary_items(
    *,
    quote_source: str | None,
    selected_projection_cover_holds: bool | None,
    selected_canonical_projected_path: list[list[object]] | None,
    selected_runtime_projected_path: list[list[object]],
    repaired_projection_cover_holds: bool | None,
    repaired_canonical_projected_path: list[list[object]] | None,
    advisory_projected_path: list[list[object]] | None,
) -> _PayloadItems:
    side: str | None
    cover_holds: bool | None
    canonical_projected_path: list[list[object]] | None
    quote_projected_path: list[list[object]] | None
    if quote_source == "selected_domain_runtime":
        side = "selected_domain"
        cover_holds = selected_projection_cover_holds
        canonical_projected_path = selected_canonical_projected_path
        quote_projected_path = selected_runtime_projected_path
    elif quote_source == "repaired_bounded_advisory":
        side = "repaired"
        cover_holds = repaired_projection_cover_holds
        canonical_projected_path = repaired_canonical_projected_path
        quote_projected_path = advisory_projected_path
    else:
        side = None
        cover_holds = None
        canonical_projected_path = None
        quote_projected_path = None
    return (
        ("effective_projection_cover_side", side),
        ("effective_projection_cover_holds", cover_holds),
        ("effective_canonical_projected_path", canonical_projected_path),
        ("effective_quote_projected_path", quote_projected_path),
        (
            "effective_quote_matches_canonical_projected_path",
            None
            if quote_projected_path is None or canonical_projected_path is None
            else bool(quote_projected_path == canonical_projected_path),
        ),
    )


@dataclass(frozen=True)
class ExactOutManyPoolCertifiedAdvisoryPacket:
    certified_packet: ExactOutManyPoolCertifiedWinnerPacket
    advisory_packet: ExactOutManyPoolBoundedAdvisoryQuotePacket
    repaired_key_cover_packet: ExactOutManyPoolRepairedKeyCoverPacket
    repaired_key_cover_interpretation_packet: ExactOutManyPoolRepairedKeyCoverInterpretationPacket
    selected_runtime_quotes_agree: bool
    packet_ok: bool
    schema: str = EXACT_OUT_MANY_POOL_CERTIFIED_ADVISORY_PACKET_SCHEMA

    def __post_init__(self) -> None:
        if not isinstance(self.certified_packet, ExactOutManyPoolCertifiedWinnerPacket):
            raise TypeError("certified_packet must be an ExactOutManyPoolCertifiedWinnerPacket")
        if not isinstance(self.advisory_packet, ExactOutManyPoolBoundedAdvisoryQuotePacket):
            raise TypeError("advisory_packet must be an ExactOutManyPoolBoundedAdvisoryQuotePacket")
        if not isinstance(self.repaired_key_cover_packet, ExactOutManyPoolRepairedKeyCoverPacket):
            raise TypeError("repaired_key_cover_packet must be an ExactOutManyPoolRepairedKeyCoverPacket")
        if not isinstance(
            self.repaired_key_cover_interpretation_packet,
            ExactOutManyPoolRepairedKeyCoverInterpretationPacket,
        ):
            raise TypeError(
                "repaired_key_cover_interpretation_packet must be an "
                "ExactOutManyPoolRepairedKeyCoverInterpretationPacket"
            )
        if not isinstance(self.selected_runtime_quotes_agree, bool):
            raise TypeError("selected_runtime_quotes_agree must be a bool")
        if not isinstance(self.packet_ok, bool):
            raise TypeError("packet_ok must be a bool")
        if self.schema != EXACT_OUT_MANY_POOL_CERTIFIED_ADVISORY_PACKET_SCHEMA:
            raise ValueError("unsupported certified advisory packet schema")

    def _projection_cover_summary(self) -> dict[str, Any]:
        selected_projection_cover = self.advisory_packet.workaround_packet.oracle_contract.audit.projection_cover_audit
        repaired_projection_cover = self.advisory_packet.workaround_packet.repaired_packet.projection_cover_audit
        repaired_full_domain_payload = self.advisory_packet.workaround_packet.repaired_full_domain_packet.to_dict()
        effective_quote = None if self.advisory_packet.advisory_quote is None else _quote_to_dict(self.advisory_packet.advisory_quote)
        selected_runtime_quote = _quote_to_dict(self.advisory_packet.workaround_packet.oracle_contract.audit.runtime_quote)
        selected_runtime_projected_path = _quote_to_projected_path_payload(
            self.advisory_packet.workaround_packet.oracle_contract.audit.runtime_quote
        )
        advisory_projected_path = (
            None
            if self.advisory_packet.advisory_quote is None
            else _quote_to_projected_path_payload(self.advisory_packet.advisory_quote)
        )
        selected_canonical_projected_path = _projection_cover_canonical_path_payload(selected_projection_cover)
        repaired_canonical_projected_path = _projection_cover_canonical_path_payload(repaired_projection_cover)
        selected_projection_cover_holds = _projection_cover_holds_payload(selected_projection_cover)
        repaired_projection_cover_holds = _projection_cover_holds_payload(repaired_projection_cover)
        return {
            "effective_quote_source": self.advisory_packet.quote_source,
            "effective_quote": effective_quote,
            "selected_domain_runtime_quote": selected_runtime_quote,
            "effective_quote_matches_selected_runtime_quote": bool(self.advisory_packet.quote_matches_runtime),
            "effective_quote_matches_repaired_advisory_quote": bool(self.advisory_packet.quote_matches_repaired_advisory),
            **dict(_repaired_full_domain_summary_items(
                repaired_full_domain_payload=repaired_full_domain_payload,
                effective_quote=effective_quote,
            )),
            **dict(_repaired_key_cover_summary_items(
                key_cover_packet=self.repaired_key_cover_packet,
                interpretation_packet=self.repaired_key_cover_interpretation_packet,
            )),
            "selected_domain_runtime_projected_path": selected_runtime_projected_path,
            "advisory_projected_path": advisory_projected_path,
            "selected_domain_projection_cover_available": bool(selected_projection_cover is not None),
            "selected_domain_projection_cover_holds": selected_projection_cover_holds,
            "selected_domain_canonical_projected_path": selected_canonical_projected_path,
            "selected_runtime_matches_selected_canonical_projected_path": (
                None
                if selected_canonical_projected_path is None
                else bool(selected_runtime_projected_path == selected_canonical_projected_path)
            ),
            "repaired_projection_cover_available": bool(repaired_projection_cover is not None),
            "repaired_projection_cover_holds": repaired_projection_cover_holds,
            "repaired_canonical_projected_path": repaired_canonical_projected_path,
            "advisory_matches_repaired_canonical_projected_path": (
                None
                if advisory_projected_path is None or repaired_canonical_projected_path is None
                else bool(advisory_projected_path == repaired_canonical_projected_path)
            ),
            **dict(_effective_projection_cover_summary_items(
                quote_source=self.advisory_packet.quote_source,
                selected_projection_cover_holds=selected_projection_cover_holds,
                selected_canonical_projected_path=selected_canonical_projected_path,
                selected_runtime_projected_path=selected_runtime_projected_path,
                repaired_projection_cover_holds=repaired_projection_cover_holds,
                repaired_canonical_projected_path=repaired_canonical_projected_path,
                advisory_projected_path=advisory_projected_path,
            )),
        }

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "certified_packet": self.certified_packet.to_dict(),
            "advisory_packet": self.advisory_packet.to_dict(),
            "repaired_key_cover_packet": self.repaired_key_cover_packet.to_dict(),
            "repaired_key_cover_interpretation_packet": self.repaired_key_cover_interpretation_packet.to_dict(),
            "selected_runtime_quotes_agree": bool(self.selected_runtime_quotes_agree),
            "packet_ok": bool(self.packet_ok),
            **self._projection_cover_summary(),
        }


@dataclass(frozen=True)
class ExactOutManyPoolAuditedBoundsContract:
    asset_in: str
    asset_out: str
    amount_out_total: int
    max_legs: int
    max_candidate_pools: int
    max_candidates: int
    max_iters: int
    window: int
    brute_force_max: int
    max_full_domain_pools: int
    max_enumerated_candidates: int
    pool_snapshots: tuple[dict[str, Any], ...]
    certified_advisory_packet: ExactOutManyPoolCertifiedAdvisoryPacket
    selected_domain_budget_respected: bool
    repaired_selection_budget_respected: bool
    full_domain_pool_budget_respected: bool
    full_domain_candidate_budget_respected: bool
    budget_parameters_bound: bool
    failure_path_explicit: bool
    success_path_replayable: bool
    contract_ok: bool
    schema: str = EXACT_OUT_MANY_POOL_AUDITED_BOUNDS_CONTRACT_SCHEMA

    def __post_init__(self) -> None:
        if not self.asset_in or not self.asset_out or self.asset_in == self.asset_out:
            raise ValueError("asset_in and asset_out must be non-empty and distinct")
        for field_name, value, min_value in (
            ("amount_out_total", self.amount_out_total, 1),
            ("max_legs", self.max_legs, 1),
            ("max_candidate_pools", self.max_candidate_pools, 1),
            ("max_candidates", self.max_candidates, 1),
            ("max_iters", self.max_iters, 1),
            ("window", self.window, 0),
            ("brute_force_max", self.brute_force_max, 0),
            ("max_full_domain_pools", self.max_full_domain_pools, 1),
            ("max_enumerated_candidates", self.max_enumerated_candidates, 1),
        ):
            if not isinstance(value, int) or isinstance(value, bool) or int(value) < int(min_value):
                raise ValueError(f"{field_name} must be an int >= {min_value}")
        if not all(isinstance(snapshot, dict) for snapshot in self.pool_snapshots):
            raise TypeError("pool_snapshots must be dict payloads")
        if not isinstance(self.certified_advisory_packet, ExactOutManyPoolCertifiedAdvisoryPacket):
            raise TypeError("certified_advisory_packet must be an ExactOutManyPoolCertifiedAdvisoryPacket")
        bool_fields = (
            self.selected_domain_budget_respected,
            self.repaired_selection_budget_respected,
            self.full_domain_pool_budget_respected,
            self.full_domain_candidate_budget_respected,
            self.budget_parameters_bound,
            self.failure_path_explicit,
            self.success_path_replayable,
            self.contract_ok,
        )
        if not all(isinstance(value, bool) for value in bool_fields):
            raise TypeError("audited bounds contract flags must be bools")
        if self.schema != EXACT_OUT_MANY_POOL_AUDITED_BOUNDS_CONTRACT_SCHEMA:
            raise ValueError("unsupported audited bounds contract schema")

    def _bounds_summary(self) -> dict[str, Any]:
        domain_contract = self.certified_advisory_packet.certified_packet.domain_contract
        repaired_contract = self.certified_advisory_packet.advisory_packet.workaround_packet.repaired_packet.repaired_contract
        repaired_full_domain_packet = self.certified_advisory_packet.advisory_packet.workaround_packet.repaired_full_domain_packet
        return {
            "selected_domain_audit_pool_count": len(domain_contract.audit_pool_ids),
            "selected_domain_candidate_count": int(domain_contract.candidate_count),
            "repaired_selected_pool_count": len(repaired_contract.repaired_selected_pool_ids),
            "repaired_subset_search_count": int(repaired_contract.searched_subset_count),
            "full_domain_feasible_pool_count": len(repaired_full_domain_packet.full_domain_feasible_pool_ids),
            "full_domain_candidate_count": int(repaired_full_domain_packet.full_domain_candidate_count),
            "certified_packet_ok": bool(self.certified_advisory_packet.certified_packet.packet_ok),
            "advisory_packet_ok": bool(self.certified_advisory_packet.advisory_packet.packet_ok),
            "selected_runtime_quotes_agree": bool(self.certified_advisory_packet.selected_runtime_quotes_agree),
        }

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "asset_in": str(self.asset_in),
            "asset_out": str(self.asset_out),
            "amount_out_total": int(self.amount_out_total),
            "max_legs": int(self.max_legs),
            "max_candidate_pools": int(self.max_candidate_pools),
            "max_candidates": int(self.max_candidates),
            "max_iters": int(self.max_iters),
            "window": int(self.window),
            "brute_force_max": int(self.brute_force_max),
            "max_full_domain_pools": int(self.max_full_domain_pools),
            "max_enumerated_candidates": int(self.max_enumerated_candidates),
            "pool_snapshots": [dict(snapshot) for snapshot in self.pool_snapshots],
            "certified_advisory_packet": self.certified_advisory_packet.to_dict(),
            "selected_domain_budget_respected": bool(self.selected_domain_budget_respected),
            "repaired_selection_budget_respected": bool(self.repaired_selection_budget_respected),
            "full_domain_pool_budget_respected": bool(self.full_domain_pool_budget_respected),
            "full_domain_candidate_budget_respected": bool(self.full_domain_candidate_budget_respected),
            "budget_parameters_bound": bool(self.budget_parameters_bound),
            "failure_path_explicit": bool(self.failure_path_explicit),
            "success_path_replayable": bool(self.success_path_replayable),
            "contract_ok": bool(self.contract_ok),
            **self._bounds_summary(),
        }


@dataclass(frozen=True)
class ExactOutManyPoolAdaptiveLivenessPacket:
    audited_bounds_contract: ExactOutManyPoolAuditedBoundsContract
    repaired_full_domain_packet: ExactOutManyPoolRepairedFullDomainCertifiedPacket
    cheap_path_attempted: bool
    cheap_path_success: bool
    fallback_required: bool
    fallback_attempted: bool
    fallback_available: bool
    fallback_success: bool
    returned_success: bool
    explicit_failure: bool
    failure_reason_present: bool
    no_spurious_failure: bool
    effective_quote_source: str | None
    effective_quote: SplitManyPoolsExactOutQuote | None
    failure_reason: str | None
    nested_error: str | None
    packet_ok: bool
    liveness_ok: bool
    schema: str = EXACT_OUT_MANY_POOL_ADAPTIVE_LIVENESS_PACKET_SCHEMA

    def __post_init__(self) -> None:
        self._validate_packet_types()
        self._validate_bool_fields()
        self._validate_optional_fields()
        self._validate_nested_binding()
        self._validate_liveness_flags()
        self._validate_success_or_failure_payload()
        self._validate_liveness_ok_formula()

    def _validate_packet_types(self) -> None:
        if not isinstance(self.audited_bounds_contract, ExactOutManyPoolAuditedBoundsContract):
            raise TypeError("audited_bounds_contract must be an ExactOutManyPoolAuditedBoundsContract")
        if not isinstance(self.repaired_full_domain_packet, ExactOutManyPoolRepairedFullDomainCertifiedPacket):
            raise TypeError("repaired_full_domain_packet must be an ExactOutManyPoolRepairedFullDomainCertifiedPacket")

    def _validate_bool_fields(self) -> None:
        for field_name, value in (
            ("cheap_path_attempted", self.cheap_path_attempted),
            ("cheap_path_success", self.cheap_path_success),
            ("fallback_required", self.fallback_required),
            ("fallback_attempted", self.fallback_attempted),
            ("fallback_available", self.fallback_available),
            ("fallback_success", self.fallback_success),
            ("returned_success", self.returned_success),
            ("explicit_failure", self.explicit_failure),
            ("failure_reason_present", self.failure_reason_present),
            ("no_spurious_failure", self.no_spurious_failure),
            ("packet_ok", self.packet_ok),
            ("liveness_ok", self.liveness_ok),
        ):
            if not isinstance(value, bool):
                raise TypeError(f"{field_name} must be a bool")

    def _validate_optional_fields(self) -> None:
        if self.effective_quote_source is not None and self.effective_quote_source not in (
            "default_certified_advisory",
            "repaired_full_domain",
        ):
            raise ValueError("unsupported effective_quote_source")
        if self.effective_quote is not None and not isinstance(self.effective_quote, SplitManyPoolsExactOutQuote):
            raise TypeError("effective_quote must be a SplitManyPoolsExactOutQuote or None")
        if self.failure_reason is not None and self.failure_reason not in (
            EXACT_OUT_MANY_POOL_ADAPTIVE_FAILURE_AUDITED_BOUNDS_CONTRACT_NOT_OK,
            EXACT_OUT_MANY_POOL_ADAPTIVE_FAILURE_DEFAULT_PACKET_NOT_OK,
            EXACT_OUT_MANY_POOL_ADAPTIVE_FAILURE_REPAIRED_FULL_DOMAIN_PACKET_NOT_OK,
            EXACT_OUT_MANY_POOL_ADAPTIVE_FAILURE_REPLAYABLE_QUOTE_MISSING,
        ):
            raise ValueError("unsupported failure_reason")
        if self.nested_error is not None and (not isinstance(self.nested_error, str) or not self.nested_error):
            raise ValueError("nested_error must be a non-empty string or None")
        if self.schema != EXACT_OUT_MANY_POOL_ADAPTIVE_LIVENESS_PACKET_SCHEMA:
            raise ValueError("unsupported adaptive liveness packet schema")

    def _validate_nested_binding(self) -> None:
        if (
            self.repaired_full_domain_packet
            != self.audited_bounds_contract.certified_advisory_packet.advisory_packet.workaround_packet.repaired_full_domain_packet
        ):
            raise ValueError("repaired_full_domain_packet must match the nested audited-bounds repaired full-domain packet")

    def _validate_liveness_flags(self) -> None:
        if not self.cheap_path_attempted:
            raise ValueError("cheap_path_attempted must always be true")
        if self.fallback_required != (not self.cheap_path_success):
            raise ValueError("fallback_required must equal not cheap_path_success")
        if self.fallback_attempted != self.fallback_required:
            raise ValueError("fallback_attempted must equal fallback_required")
        if self.fallback_success != (self.fallback_attempted and self.fallback_available):
            raise ValueError("fallback_success must equal fallback_attempted and fallback_available")
        if self.returned_success != (self.cheap_path_success or self.fallback_success):
            raise ValueError("returned_success must equal cheap_path_success or fallback_success")
        if self.explicit_failure != (not self.returned_success):
            raise ValueError("explicit_failure must equal not returned_success")
        if self.failure_reason_present != (self.failure_reason is not None):
            raise ValueError("failure_reason_present must track failure_reason presence")
        if self.no_spurious_failure != ((not self.explicit_failure) or (not self.fallback_available)):
            raise ValueError("no_spurious_failure formula mismatch")

    def _validate_success_or_failure_payload(self) -> None:
        if self.returned_success:
            self._validate_success_payload()
        else:
            self._validate_failure_payload()

    def _validate_success_payload(self) -> None:
        if self.effective_quote_source is None:
            raise ValueError("returned_success requires effective_quote_source")
        if self.effective_quote is None:
            raise ValueError("returned_success requires effective_quote")
        if self.failure_reason is not None:
            raise ValueError("returned_success must not carry failure_reason")
        if self.effective_quote_source == "default_certified_advisory":
            self._validate_default_advisory_success_quote()
        elif self.effective_quote_source == "repaired_full_domain":
            self._validate_repaired_full_domain_success_quote()

    def _validate_default_advisory_success_quote(self) -> None:
        if not self.cheap_path_success:
            raise ValueError("default_certified_advisory source requires cheap_path_success")
        if self.effective_quote != self.audited_bounds_contract.certified_advisory_packet.advisory_packet.advisory_quote:
            raise ValueError("effective_quote must match audited-bounds certified advisory quote")

    def _validate_repaired_full_domain_success_quote(self) -> None:
        if not self.fallback_success:
            raise ValueError("repaired_full_domain source requires fallback_success")
        if self.effective_quote != self.repaired_full_domain_packet.repaired_quote:
            raise ValueError("effective_quote must match repaired_full_domain_packet.repaired_quote")

    def _validate_failure_payload(self) -> None:
        if self.effective_quote_source is not None or self.effective_quote is not None:
            raise ValueError("explicit failure packets must not carry an effective quote")
        if self.failure_reason is None:
            raise ValueError("explicit failure packets must carry a failure_reason")

    def _validate_liveness_ok_formula(self) -> None:
        if self.liveness_ok != (
            self.packet_ok and self.audited_bounds_contract.contract_ok and self.no_spurious_failure
        ):
            raise ValueError("liveness_ok formula mismatch")

    def _summary(self) -> dict[str, Any]:
        default_payload = self.audited_bounds_contract.certified_advisory_packet.to_dict()
        repaired_payload = self.repaired_full_domain_packet.to_dict()
        return {
            "audited_bounds_contract_ok": bool(self.audited_bounds_contract.contract_ok),
            "default_packet_ok": bool(self.audited_bounds_contract.certified_advisory_packet.packet_ok),
            "default_effective_quote_source": default_payload["effective_quote_source"],
            "default_effective_quote": default_payload["effective_quote"],
            "default_effective_quote_matches_full_domain_canonical": default_payload[
                "effective_quote_matches_full_domain_canonical"
            ],
            "repaired_full_domain_packet_ok": bool(self.repaired_full_domain_packet.packet_ok),
            "repaired_full_domain_quote": repaired_payload["repaired_quote"],
            "repaired_quote_matches_full_domain_canonical": bool(
                repaired_payload["repaired_matches_full_canonical"]
            ),
            "repaired_full_domain_canonical_quote": repaired_payload["full_domain_canonical_quote"],
            "effective_quote_matches_full_domain_canonical": (
                None
                if self.effective_quote is None
                else bool(self.effective_quote == self.repaired_full_domain_packet.full_domain_canonical_quote)
            ),
        }

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "audited_bounds_contract": self.audited_bounds_contract.to_dict(),
            "repaired_full_domain_packet": self.repaired_full_domain_packet.to_dict(),
            "cheap_path_attempted": bool(self.cheap_path_attempted),
            "cheap_path_success": bool(self.cheap_path_success),
            "fallback_required": bool(self.fallback_required),
            "fallback_attempted": bool(self.fallback_attempted),
            "fallback_available": bool(self.fallback_available),
            "fallback_success": bool(self.fallback_success),
            "returned_success": bool(self.returned_success),
            "explicit_failure": bool(self.explicit_failure),
            "failure_reason_present": bool(self.failure_reason_present),
            "no_spurious_failure": bool(self.no_spurious_failure),
            "effective_quote_source": self.effective_quote_source,
            "effective_quote": None if self.effective_quote is None else _quote_to_dict(self.effective_quote),
            "failure_reason": self.failure_reason,
            "nested_error": self.nested_error,
            "packet_ok": bool(self.packet_ok),
            "liveness_ok": bool(self.liveness_ok),
            **self._summary(),
        }


@dataclass(frozen=True)
class ExactOutManyPoolRepairedReplacementShadowPacket:
    default_packet: ExactOutManyPoolCertifiedAdvisoryPacket
    replacement_contract: ExactOutManyPoolRepairedSelectedDomainOracleContract
    replacement_available: bool
    effective_quote_matches_replacement_quote: bool
    replacement_quote_matches_selected_runtime_quote: bool
    packet_ok: bool
    schema: str = EXACT_OUT_MANY_POOL_REPAIRED_REPLACEMENT_SHADOW_PACKET_SCHEMA

    def __post_init__(self) -> None:
        if not isinstance(self.default_packet, ExactOutManyPoolCertifiedAdvisoryPacket):
            raise TypeError("default_packet must be an ExactOutManyPoolCertifiedAdvisoryPacket")
        if not isinstance(self.replacement_contract, ExactOutManyPoolRepairedSelectedDomainOracleContract):
            raise TypeError("replacement_contract must be an ExactOutManyPoolRepairedSelectedDomainOracleContract")
        for field_name, value in (
            ("replacement_available", self.replacement_available),
            ("effective_quote_matches_replacement_quote", self.effective_quote_matches_replacement_quote),
            ("replacement_quote_matches_selected_runtime_quote", self.replacement_quote_matches_selected_runtime_quote),
            ("packet_ok", self.packet_ok),
        ):
            if not isinstance(value, bool):
                raise TypeError(f"{field_name} must be a bool")
        if self.schema != EXACT_OUT_MANY_POOL_REPAIRED_REPLACEMENT_SHADOW_PACKET_SCHEMA:
            raise ValueError("unsupported repaired replacement shadow packet schema")

    def _shadow_summary(self) -> dict[str, Any]:
        default_payload = self.default_packet.to_dict()
        replacement_payload = self.replacement_contract.to_dict()
        replacement_quote = (
            replacement_payload["repaired_selected_domain_runtime_quote"]
            if self.replacement_available
            else None
        )
        replacement_projected_path = (
            replacement_payload["repaired_selected_domain_runtime_projected_path"]
            if self.replacement_available
            else None
        )
        return {
            "default_quote_policy": "certified_advisory_v1",
            "default_effective_quote": default_payload["effective_quote"],
            "default_effective_quote_source": default_payload["effective_quote_source"],
            "default_effective_quote_projected_path": default_payload["effective_quote_projected_path"],
            "replacement_available": bool(self.replacement_available),
            "replacement_quote": replacement_quote,
            "replacement_quote_projected_path": replacement_projected_path,
            "replacement_quote_matches_full_canonical": replacement_payload["replacement_quote_matches_full_canonical"],
            "replacement_quote_matches_selected_runtime_quote": bool(self.replacement_quote_matches_selected_runtime_quote),
            "effective_quote_matches_replacement_quote": bool(self.effective_quote_matches_replacement_quote),
        }

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "default_packet": self.default_packet.to_dict(),
            "replacement_contract": self.replacement_contract.to_dict(),
            "packet_ok": bool(self.packet_ok),
            **self._shadow_summary(),
        }


def build_exact_out_route_canonical_certificate(
    quotes: Sequence[SplitManyPoolsExactOutQuote],
    *,
    binding_ok: int = 1,
) -> ExactOutRouteCanonicalCertificate:
    selection = _kernel_select_exact_out_route_canonical_winner(quotes)

    candidates = tuple(
        ExactOutRouteCandidateCertificate(
            candidate_index=int(candidate.candidate_index),
            quote=candidate.quote,
            route_key=candidate.route_key,
            route_key_rank_u64=int(candidate.route_key_rank_u64),
        )
        for candidate in selection.candidates
    )
    winner = selection.winner
    steps = tuple(
        build_argmin_stream_certificate_v1_step(
            winner_key=int(winner.route_key_rank_u64),
            winner_index=int(winner.candidate_index),
            cand_key=int(candidate.route_key_rank_u64),
            cand_index=int(candidate.candidate_index),
            binding_ok=int(binding_ok),
        )
        for candidate in candidates
    )
    return ExactOutRouteCanonicalCertificate(
        winner_index=int(winner.candidate_index),
        winner_route_key_rank_u64=int(winner.route_key_rank_u64),
        winner_quote=winner.quote,
        candidates=candidates,
        argmin_steps=steps,
    )


def split_two_pools_exact_out_quote_to_many(quote: SplitTwoPoolsQuote) -> SplitManyPoolsExactOutQuote:
    legs: list[SplitLegExactOutQuote] = []
    if int(quote.amount_out_0) > 0:
        legs.append(
            SplitLegExactOutQuote(
                pool_id=quote.pool0_id,
                amount_out=int(quote.amount_out_0),
                amount_in=int(quote.amount_in_0),
            )
        )
    if int(quote.amount_out_1) > 0:
        legs.append(
            SplitLegExactOutQuote(
                pool_id=quote.pool1_id,
                amount_out=int(quote.amount_out_1),
                amount_in=int(quote.amount_in_1),
            )
        )
    return SplitManyPoolsExactOutQuote(
        amount_out_total=int(quote.amount_out_total),
        amount_in_total=int(quote.amount_in_total),
        legs=tuple(legs),
    )


def _pool_reserves_for_exact_out(pool: PoolState, *, asset_in: str, asset_out: str) -> tuple[int, int] | None:
    return _kernel_pool_reserves_for_exact_out(pool, asset_in=asset_in, asset_out=asset_out)


def _feasible_exact_out_pools(
    pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
) -> list[tuple[PoolState, int, int]]:
    return _kernel_feasible_exact_out_pools(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
    )


def _select_many_pool_audit_candidates(
    pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int,
    max_candidate_pools: int,
) -> tuple[PoolState, ...]:
    max_legs_i = _require_control_int(max_legs, name="max_legs")
    max_candidate_pools_i = _require_control_int(max_candidate_pools, name="max_candidate_pools")
    return _kernel_select_many_pool_audit_candidates(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=max_legs_i,
        max_candidate_pools=max_candidate_pools_i,
    )


@dataclass(frozen=True)
class _TwoPoolExactOutParams:
    asset_in: str
    asset_out: str
    amount_out_total: int


@dataclass(frozen=True)
class _TwoPoolExactOutDomain:
    pool0: PoolState
    pool1: PoolState
    reserves0: tuple[int, int]
    reserves1: tuple[int, int]
    amount_out_total: int
    split_lo: int
    split_hi: int


def _two_pool_exact_out_domain(
    pool0: PoolState,
    pool1: PoolState,
    *,
    params: _TwoPoolExactOutParams,
) -> _TwoPoolExactOutDomain:
    if int(params.amount_out_total) <= 0:
        raise ValueError("amount_out_total must be positive")
    p0, p1 = (pool0, pool1) if pool0.pool_id <= pool1.pool_id else (pool1, pool0)
    reserves0 = _pool_reserves_for_exact_out(p0, asset_in=params.asset_in, asset_out=params.asset_out)
    reserves1 = _pool_reserves_for_exact_out(p1, asset_in=params.asset_in, asset_out=params.asset_out)
    if reserves0 is None or reserves1 is None:
        raise ValueError("pools do not support this direction (or are inactive)")
    max0 = max(0, int(reserves0[1]) - 1)
    max1 = max(0, int(reserves1[1]) - 1)
    split_lo = max(0, int(params.amount_out_total) - max1)
    split_hi = min(int(params.amount_out_total), max0)
    if split_lo > split_hi:
        raise ValueError("no feasible split for desired amount_out_total")
    return _TwoPoolExactOutDomain(
        pool0=p0,
        pool1=p1,
        reserves0=(int(reserves0[0]), int(reserves0[1])),
        reserves1=(int(reserves1[0]), int(reserves1[1])),
        amount_out_total=int(params.amount_out_total),
        split_lo=int(split_lo),
        split_hi=int(split_hi),
    )


def _exact_out_amount_in_for_split_leg(
    pool: PoolState,
    *,
    reserves: tuple[int, int],
    amount_out: int,
) -> int:
    if int(amount_out) <= 0:
        return 0
    amount_in, _ = swap_exact_out_for_pool(
        pool,
        reserve_in=int(reserves[0]),
        reserve_out=int(reserves[1]),
        amount_out=int(amount_out),
    )
    return int(amount_in)


def _two_pool_candidate_for_split(
    domain: _TwoPoolExactOutDomain,
    *,
    amount_out_pool0: int,
) -> SplitManyPoolsExactOutQuote:
    q0 = int(amount_out_pool0)
    q1 = int(domain.amount_out_total) - q0
    in0 = _exact_out_amount_in_for_split_leg(domain.pool0, reserves=domain.reserves0, amount_out=q0)
    in1 = _exact_out_amount_in_for_split_leg(domain.pool1, reserves=domain.reserves1, amount_out=q1)
    legs: list[SplitLegExactOutQuote] = []
    if q0 > 0:
        legs.append(SplitLegExactOutQuote(pool_id=domain.pool0.pool_id, amount_out=q0, amount_in=int(in0)))
    if q1 > 0:
        legs.append(SplitLegExactOutQuote(pool_id=domain.pool1.pool_id, amount_out=q1, amount_in=int(in1)))
    return SplitManyPoolsExactOutQuote(
        amount_out_total=int(domain.amount_out_total),
        amount_in_total=int(in0 + in1),
        legs=tuple(legs),
    )


def enumerate_exact_out_two_pool_candidates(
    pool0: PoolState,
    pool1: PoolState,
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
) -> tuple[SplitManyPoolsExactOutQuote, ...]:
    amount_out_total_i = _require_amount_out_total_int(amount_out_total)
    params = _TwoPoolExactOutParams(
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=amount_out_total_i,
    )
    domain = _two_pool_exact_out_domain(pool0, pool1, params=params)
    quotes: list[SplitManyPoolsExactOutQuote] = []
    for q0 in range(domain.split_lo, domain.split_hi + 1):
        try:
            quote = _two_pool_candidate_for_split(domain, amount_out_pool0=q0)
        except ValueError:
            continue
        quotes.append(quote)
    if not quotes:
        raise ValueError("no feasible exact-out candidates")
    return tuple(quotes)


def enumerate_exact_out_many_pool_candidates(
    pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int = 3,
    max_candidate_pools: int = 5,
    max_enumerated_candidates: int = 20_000,
) -> tuple[SplitManyPoolsExactOutQuote, ...]:
    amount_out_total_i = _require_amount_out_total_int(amount_out_total)
    max_legs_i = _require_control_int(max_legs, name="max_legs")
    max_candidate_pools_i = _require_control_int(max_candidate_pools, name="max_candidate_pools")
    max_enumerated_candidates_i = _require_control_int(
        max_enumerated_candidates,
        name="max_enumerated_candidates",
    )
    return _kernel_enumerate_exact_out_many_pool_candidates(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=amount_out_total_i,
        max_legs=max_legs_i,
        max_candidate_pools=max_candidate_pools_i,
        max_enumerated_candidates=max_enumerated_candidates_i,
    )


def _quote_is_complete_exact_out_candidate(
    quote: SplitManyPoolsExactOutQuote,
    *,
    amount_out_total: int,
) -> bool:
    if int(quote.amount_out_total) != int(amount_out_total):
        return False
    if int(quote.amount_in_total) <= 0:
        return False
    if not quote.legs:
        return False
    leg_amount_out_sum = 0
    leg_amount_in_sum = 0
    for leg in quote.legs:
        if int(leg.amount_out) <= 0 or int(leg.amount_in) <= 0:
            return False
        leg_amount_out_sum += int(leg.amount_out)
        leg_amount_in_sum += int(leg.amount_in)
    return int(leg_amount_out_sum) == int(amount_out_total) and int(leg_amount_in_sum) == int(quote.amount_in_total)


def _quote_leg_pool_ids_sorted_unique(quote: SplitManyPoolsExactOutQuote) -> bool:
    pool_ids = tuple(leg.pool_id for leg in quote.legs)
    return pool_ids == tuple(sorted(pool_ids)) and len(set(pool_ids)) == len(pool_ids)


def _audit_pool_ids_sorted_unique(audit_pool_ids: Sequence[str]) -> bool:
    ids = tuple(str(pool_id) for pool_id in audit_pool_ids)
    return ids == tuple(sorted(ids)) and len(set(ids)) == len(ids)


def _prefilter_rows_rank_sorted_unique(rows: Sequence[ExactOutManyPoolPrefilterRow]) -> bool:
    pool_ids = tuple(row.pool_id for row in rows)
    if len(set(pool_ids)) != len(pool_ids):
        return False
    ranked = tuple(
        sorted(
            rows,
            key=lambda row: (int(row.scaled_unit_cost_u64), int(row.probe_amount_in), row.pool_id),
        )
    )
    return tuple(rows) == ranked


def _top_capacity_sum(caps_by_pool_id: dict[str, int], *, max_legs: int) -> int:
    max_legs_i = _require_control_int(max_legs, name="max_legs")
    if max_legs_i <= 0:
        return 0
    caps = sorted((int(cap) for cap in caps_by_pool_id.values() if int(cap) > 0), reverse=True)
    return int(sum(caps[:max_legs_i]))


@dataclass(frozen=True)
class _PrefilterContractParams:
    asset_in: str
    asset_out: str
    amount_out_total: int
    max_legs: int
    max_candidate_pools: int

    def __post_init__(self) -> None:
        _require_control_fields(
            (
                ("amount_out_total", self.amount_out_total),
                ("max_legs", self.max_legs),
                ("max_candidate_pools", self.max_candidate_pools),
            )
        )


@dataclass(frozen=True)
class _PrefilterContractChecks:
    feasible_rows_sorted_unique: bool
    selected_pool_ids_sorted_unique: bool
    selected_pool_ids_within_budget: bool
    selected_pool_ids_subset_of_feasible: bool
    selected_is_prefix_of_feasible_ranking: bool
    full_capacity_guard_feasible: bool
    selected_capacity_guard_feasible: bool

    @property
    def contract_ok(self) -> bool:
        return (
            self.feasible_rows_sorted_unique
            and self.selected_pool_ids_sorted_unique
            and self.selected_pool_ids_within_budget
            and self.selected_pool_ids_subset_of_feasible
            and self.selected_is_prefix_of_feasible_ranking
            and self.full_capacity_guard_feasible
            and self.selected_capacity_guard_feasible
        )


@dataclass(frozen=True)
class _PrefilterContractEvidence:
    feasible_rows: tuple[ExactOutManyPoolPrefilterRow, ...]
    selected_pool_ids: tuple[str, ...]
    checks: _PrefilterContractChecks

    @property
    def contract_ok(self) -> bool:
        return bool(self.feasible_rows and self.checks.contract_ok)


def _validate_prefilter_contract_inputs(params: _PrefilterContractParams) -> None:
    if not params.asset_in or not params.asset_out or params.asset_in == params.asset_out:
        raise ValueError("asset_in and asset_out must be non-empty and distinct")
    if int(params.amount_out_total) <= 0:
        raise ValueError("amount_out_total must be positive")
    if int(params.max_legs) <= 0:
        raise ValueError("max_legs must be positive")
    if int(params.max_candidate_pools) <= 0:
        raise ValueError("max_candidate_pools must be positive")


def _prefilter_feasible_rows(
    pools: Sequence[PoolState],
    *,
    params: _PrefilterContractParams,
) -> tuple[ExactOutManyPoolPrefilterRow, ...]:
    ranked_rows_raw = _kernel_rank_exact_out_feasible_pools(
        pools,
        asset_in=params.asset_in,
        asset_out=params.asset_out,
        amount_out_total=int(params.amount_out_total),
    )
    return tuple(
        ExactOutManyPoolPrefilterRow(
            pool_id=row.pool_id,
            cap_out=int(row.cap_out),
            probe_amount_out=int(row.probe_amount_out),
            probe_amount_in=int(row.probe_amount_in),
            scaled_unit_cost_u64=int(row.scaled_unit_cost_u64),
        )
        for row in ranked_rows_raw
    )


def _prefilter_selected_pool_ids(
    pools: Sequence[PoolState],
    *,
    params: _PrefilterContractParams,
) -> tuple[str, ...]:
    return tuple(
        pool.pool_id
        for pool in _select_many_pool_audit_candidates(
            pools,
            asset_in=params.asset_in,
            asset_out=params.asset_out,
            amount_out_total=int(params.amount_out_total),
            max_legs=int(params.max_legs),
            max_candidate_pools=int(params.max_candidate_pools),
        )
    )


def _prefilter_contract_checks(
    feasible_rows: Sequence[ExactOutManyPoolPrefilterRow],
    selected_pool_ids: Sequence[str],
    *,
    params: _PrefilterContractParams,
) -> _PrefilterContractChecks:
    feasible_pool_ids = tuple(row.pool_id for row in feasible_rows)
    feasible_pool_id_set = set(feasible_pool_ids)
    selected_pool_id_set = set(selected_pool_ids)
    return _PrefilterContractChecks(
        feasible_rows_sorted_unique=_prefilter_rows_rank_sorted_unique(feasible_rows),
        selected_pool_ids_sorted_unique=_audit_pool_ids_sorted_unique(selected_pool_ids),
        selected_pool_ids_within_budget=len(selected_pool_ids) <= int(params.max_candidate_pools),
        selected_pool_ids_subset_of_feasible=all(pool_id in feasible_pool_id_set for pool_id in selected_pool_ids),
        selected_is_prefix_of_feasible_ranking=tuple(selected_pool_ids)
        == tuple(sorted(feasible_pool_ids[: len(selected_pool_ids)])),
        full_capacity_guard_feasible=_top_capacity_sum(
            {row.pool_id: int(row.cap_out) for row in feasible_rows},
            max_legs=int(params.max_legs),
        )
        >= int(params.amount_out_total),
        selected_capacity_guard_feasible=_top_capacity_sum(
            {row.pool_id: int(row.cap_out) for row in feasible_rows if row.pool_id in selected_pool_id_set},
            max_legs=int(params.max_legs),
        )
        >= int(params.amount_out_total),
    )


def _build_prefilter_contract_evidence(
    pools: Sequence[PoolState],
    *,
    params: _PrefilterContractParams,
) -> _PrefilterContractEvidence:
    feasible_rows = _prefilter_feasible_rows(pools, params=params)
    selected_pool_ids = _prefilter_selected_pool_ids(pools, params=params)
    checks = _prefilter_contract_checks(feasible_rows, selected_pool_ids, params=params)
    return _PrefilterContractEvidence(feasible_rows=feasible_rows, selected_pool_ids=selected_pool_ids, checks=checks)


def _prefilter_contract_from_evidence(
    pools: Sequence[PoolState],
    *,
    params: _PrefilterContractParams,
    evidence: _PrefilterContractEvidence,
) -> ExactOutManyPoolPrefilterContract:
    checks = evidence.checks
    return ExactOutManyPoolPrefilterContract(
        asset_in=str(params.asset_in),
        asset_out=str(params.asset_out),
        amount_out_total=int(params.amount_out_total),
        max_legs=int(params.max_legs),
        max_candidate_pools=int(params.max_candidate_pools),
        pool_snapshots=tuple(_pool_to_dict(pool) for pool in pools),
        feasible_rows=evidence.feasible_rows,
        selected_pool_ids=evidence.selected_pool_ids,
        feasible_rows_sorted_unique=bool(checks.feasible_rows_sorted_unique),
        selected_pool_ids_sorted_unique=bool(checks.selected_pool_ids_sorted_unique),
        selected_pool_ids_within_budget=bool(checks.selected_pool_ids_within_budget),
        selected_pool_ids_subset_of_feasible=bool(checks.selected_pool_ids_subset_of_feasible),
        selected_is_prefix_of_feasible_ranking=bool(checks.selected_is_prefix_of_feasible_ranking),
        full_capacity_guard_feasible=bool(checks.full_capacity_guard_feasible),
        selected_capacity_guard_feasible=bool(checks.selected_capacity_guard_feasible),
        contract_ok=bool(evidence.contract_ok),
    )


def build_exact_out_many_pool_prefilter_contract(
    pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int = 3,
    max_candidate_pools: int = 5,
) -> ExactOutManyPoolPrefilterContract:
    amount_out_total_i = _require_amount_out_total_int(amount_out_total)
    params = _PrefilterContractParams(
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=amount_out_total_i,
        max_legs=max_legs,
        max_candidate_pools=max_candidate_pools,
    )
    _validate_prefilter_contract_inputs(params)
    evidence = _build_prefilter_contract_evidence(pools, params=params)
    return _prefilter_contract_from_evidence(pools, params=params, evidence=evidence)


@dataclass(frozen=True)
class _RepairedPrefilterSelectionChecks:
    sorted_unique: bool
    within_budget: bool
    subset_of_feasible: bool
    matches_full_canonical: bool
    contraction_holds: bool

    @property
    def contract_ok(self) -> bool:
        return (
            self.sorted_unique
            and self.within_budget
            and self.subset_of_feasible
            and self.matches_full_canonical
            and self.contraction_holds
        )


@dataclass(frozen=True)
class _RepairedPrefilterContractParams:
    asset_in: str
    asset_out: str
    amount_out_total: int
    max_legs: int
    max_candidate_pools: int
    max_full_domain_pools: int
    max_enumerated_candidates: int

    def __post_init__(self) -> None:
        _require_control_fields(
            (
                ("amount_out_total", self.amount_out_total),
                ("max_legs", self.max_legs),
                ("max_candidate_pools", self.max_candidate_pools),
                ("max_full_domain_pools", self.max_full_domain_pools),
                ("max_enumerated_candidates", self.max_enumerated_candidates),
            )
        )


@dataclass(frozen=True)
class _RepairedPrefilterEvidence:
    search_result: Any
    selection: Any
    checks: _RepairedPrefilterSelectionChecks


def _validate_repaired_prefilter_contract_inputs(params: _RepairedPrefilterContractParams) -> None:
    if not params.asset_in or not params.asset_out or params.asset_in == params.asset_out:
        raise ValueError("asset_in and asset_out must be non-empty and distinct")
    int_fields = (
        ("amount_out_total", params.amount_out_total, 1),
        ("max_legs", params.max_legs, 1),
        ("max_candidate_pools", params.max_candidate_pools, 1),
        ("max_full_domain_pools", params.max_full_domain_pools, 1),
        ("max_enumerated_candidates", params.max_enumerated_candidates, 1),
    )
    for field_name, value, min_value in int_fields:
        if not isinstance(value, int) or isinstance(value, bool) or int(value) < int(min_value):
            raise ValueError(f"{field_name} must be an int >= {min_value}")


def _search_exact_out_many_pool_prefilter_subset(
    pools: Sequence[PoolState],
    *,
    params: _RepairedPrefilterContractParams,
) -> Any:
    from src.kernels.python.exact_out_many_pool_prefilter_subset_search_v1 import (  # pylint: disable=import-outside-toplevel
        search_exact_out_many_pool_prefilter_subset,
    )

    return search_exact_out_many_pool_prefilter_subset(
        pools,
        asset_in=params.asset_in,
        asset_out=params.asset_out,
        amount_out_total=int(params.amount_out_total),
        max_legs=int(params.max_legs),
        max_candidate_pools=int(params.max_candidate_pools),
        max_full_domain_pools=int(params.max_full_domain_pools),
        max_enumerated_candidates=int(params.max_enumerated_candidates),
    )


def _build_repaired_prefilter_selection(
    pools: Sequence[PoolState],
    *,
    params: _RepairedPrefilterContractParams,
) -> Any:
    return _kernel_build_many_pool_repaired_prefilter_selection(
        pools,
        asset_in=params.asset_in,
        asset_out=params.asset_out,
        amount_out_total=int(params.amount_out_total),
        max_legs=int(params.max_legs),
        max_candidate_pools=int(params.max_candidate_pools),
        max_full_domain_pools=int(params.max_full_domain_pools),
        max_enumerated_candidates=int(params.max_enumerated_candidates),
    )


def _repaired_prefilter_matches_full_canonical(search_result: Any, selection: Any) -> bool:
    expected_pool_ids = (
        search_result.best_cover_subset_ids
        if search_result.best_cover_subset_ids is not None
        else search_result.current_selected_pool_ids
    )
    expected_matches_full = (
        search_result.best_cover_canonical_quote == search_result.full_domain_canonical_quote
        if search_result.best_cover_subset_ids is not None
        else search_result.current_selected_canonical_quote == search_result.full_domain_canonical_quote
    )
    return tuple(selection.selected_pool_ids) == tuple(expected_pool_ids) and bool(expected_matches_full)


def _repaired_prefilter_selected_pools(
    pools: Sequence[PoolState],
    *,
    selected_pool_ids: Sequence[str],
) -> tuple[PoolState, ...]:
    pool_by_id = {pool.pool_id: pool for pool in pools}
    return tuple(pool_by_id[pool_id] for pool_id in selected_pool_ids)


def _repaired_prefilter_contraction_holds(
    pools: Sequence[PoolState],
    selected_pools: Sequence[PoolState],
    *,
    params: _RepairedPrefilterContractParams,
) -> bool:
    audit = _kernel_audit_exact_out_many_pool_selected_subset_contraction(
        pools,
        selected_pools,
        asset_in=params.asset_in,
        asset_out=params.asset_out,
        amount_out_total=int(params.amount_out_total),
        max_legs=int(params.max_legs),
        max_full_domain_pools=int(params.max_full_domain_pools),
        max_enumerated_candidates=int(params.max_enumerated_candidates),
    )
    return bool(audit.contraction_holds)


def _repaired_prefilter_selection_checks(
    pools: Sequence[PoolState],
    search_result: Any,
    selection: Any,
    *,
    params: _RepairedPrefilterContractParams,
) -> _RepairedPrefilterSelectionChecks:
    selected_pool_ids = tuple(selection.selected_pool_ids)
    feasible_pool_id_set = set(search_result.feasible_pool_ids)
    selected_pools = _repaired_prefilter_selected_pools(pools, selected_pool_ids=selected_pool_ids)
    return _RepairedPrefilterSelectionChecks(
        sorted_unique=_audit_pool_ids_sorted_unique(selected_pool_ids),
        within_budget=len(selected_pool_ids) <= int(params.max_candidate_pools),
        subset_of_feasible=all(pool_id in feasible_pool_id_set for pool_id in selected_pool_ids),
        matches_full_canonical=_repaired_prefilter_matches_full_canonical(search_result, selection),
        contraction_holds=_repaired_prefilter_contraction_holds(
            pools,
            selected_pools,
            params=params,
        ),
    )


def _build_repaired_prefilter_evidence(
    pools: Sequence[PoolState],
    *,
    params: _RepairedPrefilterContractParams,
) -> _RepairedPrefilterEvidence:
    search_result = _search_exact_out_many_pool_prefilter_subset(pools, params=params)
    selection = _build_repaired_prefilter_selection(pools, params=params)
    checks = _repaired_prefilter_selection_checks(
        pools,
        search_result,
        selection,
        params=params,
    )
    return _RepairedPrefilterEvidence(search_result=search_result, selection=selection, checks=checks)


def _repaired_prefilter_contract_from_evidence(
    pools: Sequence[PoolState],
    *,
    params: _RepairedPrefilterContractParams,
    evidence: _RepairedPrefilterEvidence,
) -> ExactOutManyPoolRepairedPrefilterContract:
    search_result = evidence.search_result
    selection = evidence.selection
    checks = evidence.checks
    return ExactOutManyPoolRepairedPrefilterContract(
        asset_in=str(params.asset_in),
        asset_out=str(params.asset_out),
        amount_out_total=int(params.amount_out_total),
        max_legs=int(params.max_legs),
        max_candidate_pools=int(params.max_candidate_pools),
        max_full_domain_pools=int(params.max_full_domain_pools),
        max_enumerated_candidates=int(params.max_enumerated_candidates),
        pool_snapshots=tuple(_pool_to_dict(pool) for pool in pools),
        feasible_pool_ids=tuple(search_result.feasible_pool_ids),
        current_selected_pool_ids=tuple(selection.current_selected_pool_ids),
        repaired_selected_pool_ids=tuple(selection.selected_pool_ids),
        strategy=str(selection.strategy),
        searched_subset_count=int(selection.searched_subset_count),
        current_selected_matches_full_canonical=bool(selection.current_selected_matches_full_canonical),
        repaired_selected_pool_ids_sorted_unique=bool(checks.sorted_unique),
        repaired_selected_pool_ids_within_budget=bool(checks.within_budget),
        repaired_selected_pool_ids_subset_of_feasible=bool(checks.subset_of_feasible),
        repaired_selected_domain_matches_full_canonical=bool(checks.matches_full_canonical),
        repaired_contraction_holds=bool(checks.contraction_holds),
        contract_ok=bool(checks.contract_ok),
    )


def build_exact_out_many_pool_repaired_prefilter_contract(
    pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int = 3,
    max_candidate_pools: int = 5,
    max_full_domain_pools: int = 8,
    max_enumerated_candidates: int = 20_000,
) -> ExactOutManyPoolRepairedPrefilterContract:
    params = _RepairedPrefilterContractParams(
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=amount_out_total,
        max_legs=max_legs,
        max_candidate_pools=max_candidate_pools,
        max_full_domain_pools=max_full_domain_pools,
        max_enumerated_candidates=max_enumerated_candidates,
    )
    _validate_repaired_prefilter_contract_inputs(params)
    evidence = _build_repaired_prefilter_evidence(pools, params=params)
    return _repaired_prefilter_contract_from_evidence(pools, params=params, evidence=evidence)


def _repaired_selected_pools_from_contract(
    pools: Sequence[PoolState],
    *,
    repaired_contract: ExactOutManyPoolRepairedPrefilterContract,
) -> tuple[PoolState, ...]:
    pools_by_id = {pool.pool_id: pool for pool in pools}
    return tuple(pools_by_id[pool_id] for pool_id in repaired_contract.repaired_selected_pool_ids)


def _candidate_quote_to_core_quote(quote: Any) -> SplitManyPoolsExactOutQuote:
    amount_out_total = int(quote.amount_out_total)
    amount_in_total = int(quote.amount_in_total)
    legs = tuple(
        SplitLegExactOutQuote(
            pool_id=str(leg.pool_id),
            amount_out=int(leg.amount_out),
            amount_in=int(leg.amount_in),
        )
        for leg in quote.legs
    )
    return SplitManyPoolsExactOutQuote(
        amount_out_total=amount_out_total,
        amount_in_total=amount_in_total,
        legs=legs,
    )


def _build_exact_out_many_pool_full_domain_certificate(
    pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int,
    max_full_domain_pools: int,
    max_enumerated_candidates: int,
) -> tuple[tuple[str, ...], tuple[SplitManyPoolsExactOutQuote, ...], ExactOutRouteCanonicalCertificate]:
    max_legs_i = _require_control_int(max_legs, name="max_legs")
    max_full_domain_pools_i = _require_control_int(max_full_domain_pools, name="max_full_domain_pools")
    max_enumerated_candidates_i = _require_control_int(
        max_enumerated_candidates,
        name="max_enumerated_candidates",
    )
    feasible_rows = _feasible_exact_out_pools(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
    )
    feasible_pools = tuple(pool for pool, _cap, _amount_in in feasible_rows)
    if not feasible_pools:
        raise ValueError("no feasible pools for repaired full-domain certification")
    if len(feasible_pools) > max_full_domain_pools_i:
        raise ValueError("repaired full-domain certification exceeded max_full_domain_pools")
    full_domain = _kernel_build_exact_out_many_pool_selected_domain(
        feasible_pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=max_legs_i,
        max_enumerated_candidates=max_enumerated_candidates_i,
    )
    full_candidates = tuple(_candidate_quote_to_core_quote(candidate) for candidate in full_domain.candidates)
    return (
        tuple(str(pool_id) for pool_id in full_domain.selected_pool_ids),
        full_candidates,
        build_exact_out_route_canonical_certificate(full_candidates),
    )


def _build_exact_out_many_pool_key_cover_witnesses(
    *,
    selected_candidates: Sequence[ExactOutRouteCandidateCertificate],
    full_candidates: Sequence[ExactOutRouteCandidateCertificate],
) -> tuple[tuple[ExactOutManyPoolKeyCoverDominationWitness, ...], bool, bool]:
    full_route_keys = {candidate.route_key for candidate in full_candidates}
    selected_keys_subset_full_keys = all(candidate.route_key in full_route_keys for candidate in selected_candidates)

    witnesses: list[ExactOutManyPoolKeyCoverDominationWitness] = []
    key_cover_holds = True
    for full_candidate in full_candidates:
        dominators = [
            selected_candidate
            for selected_candidate in selected_candidates
            if selected_candidate.route_key <= full_candidate.route_key
        ]
        if not dominators:
            key_cover_holds = False
            continue
        selected_candidate = min(dominators, key=lambda candidate: (candidate.route_key, candidate.candidate_index))
        witnesses.append(
            ExactOutManyPoolKeyCoverDominationWitness(
                full_candidate_index=int(full_candidate.candidate_index),
                selected_candidate_index=int(selected_candidate.candidate_index),
                full_route_key_rank_u64=int(full_candidate.route_key_rank_u64),
                selected_route_key_rank_u64=int(selected_candidate.route_key_rank_u64),
                full_route_key=full_candidate.route_key,
                selected_route_key=selected_candidate.route_key,
            )
        )
    return tuple(witnesses), bool(selected_keys_subset_full_keys), bool(key_cover_holds)


def _selected_domain_minimum_witness_summary(
    contract: ExactOutManyPoolRepairedSelectedDomainOracleContract,
) -> tuple[bool, bool, bool]:
    certificate = contract.audit.certificate
    candidates = certificate.candidates
    winner_index_in_range = 0 <= int(certificate.winner_index) < len(candidates)
    if not winner_index_in_range:
        return False, False, False
    winner_candidate = candidates[int(certificate.winner_index)]
    winner_matches_certificate = bool(
        winner_candidate.quote == certificate.winner_quote
        and int(winner_candidate.route_key_rank_u64) == int(certificate.winner_route_key_rank_u64)
    )
    winner_key_minimal = bool(
        all(winner_candidate.route_key <= candidate.route_key for candidate in candidates)
    )
    return bool(winner_index_in_range), bool(winner_matches_certificate), bool(winner_key_minimal)


def _key_cover_witness_interpretation_summary(
    packet: ExactOutManyPoolRepairedKeyCoverPacket,
) -> tuple[bool, bool, bool, bool]:
    selected_candidates = packet.selected_domain_contract.audit.certificate.candidates
    full_candidates = packet.repaired_full_domain_packet.full_domain_certificate.candidates
    selected_candidate_count = len(selected_candidates)
    full_candidate_count = len(full_candidates)
    witnesses = packet.domination_witnesses

    witness_indices_in_range = True
    witness_keys_match_candidates = True
    witness_domination_holds = True
    covered_full_candidate_indices: set[int] = set()

    for witness in witnesses:
        full_index = int(witness.full_candidate_index)
        selected_index = int(witness.selected_candidate_index)
        if not (0 <= full_index < full_candidate_count and 0 <= selected_index < selected_candidate_count):
            witness_indices_in_range = False
            witness_keys_match_candidates = False
            witness_domination_holds = False
            continue
        covered_full_candidate_indices.add(full_index)
        full_candidate = full_candidates[full_index]
        selected_candidate = selected_candidates[selected_index]
        if (
            witness.full_route_key != full_candidate.route_key
            or int(witness.full_route_key_rank_u64) != int(full_candidate.route_key_rank_u64)
            or witness.selected_route_key != selected_candidate.route_key
            or int(witness.selected_route_key_rank_u64) != int(selected_candidate.route_key_rank_u64)
        ):
            witness_keys_match_candidates = False
        if witness.selected_route_key > witness.full_route_key:
            witness_domination_holds = False

    witness_coverage_complete = bool(
        witness_indices_in_range
        and len(witnesses) == full_candidate_count
        and covered_full_candidate_indices == set(range(full_candidate_count))
    )
    return (
        bool(witness_indices_in_range),
        bool(witness_coverage_complete),
        bool(witness_keys_match_candidates),
        bool(witness_domination_holds),
    )


def _build_exact_out_many_pool_repaired_key_cover_packet_from_components(
    *,
    selected_domain_contract: ExactOutManyPoolRepairedSelectedDomainOracleContract,
    repaired_full_domain_packet: ExactOutManyPoolRepairedFullDomainCertifiedPacket,
) -> ExactOutManyPoolRepairedKeyCoverPacket:
    selected_candidates = selected_domain_contract.audit.certificate.candidates
    full_candidates = repaired_full_domain_packet.full_domain_certificate.candidates
    domination_witnesses, selected_keys_subset_full_keys, key_cover_holds = _build_exact_out_many_pool_key_cover_witnesses(
        selected_candidates=selected_candidates,
        full_candidates=full_candidates,
    )
    selected_domain_canonical_matches_full_domain_canonical = bool(
        selected_domain_contract.audit.canonical_winner_quote == repaired_full_domain_packet.full_domain_canonical_quote
    )
    packet_ok = bool(
        selected_domain_contract.contract_ok
        and repaired_full_domain_packet.packet_ok
        and selected_keys_subset_full_keys
        and key_cover_holds
        and selected_domain_canonical_matches_full_domain_canonical
    )
    if packet_ok:
        error = None
    elif not selected_domain_contract.contract_ok:
        error = EXACT_OUT_MANY_POOL_REPAIRED_SELECTED_DOMAIN_UNAVAILABLE_ERROR
    elif not repaired_full_domain_packet.packet_ok:
        error = str(repaired_full_domain_packet.error or EXACT_OUT_MANY_POOL_REPAIRED_FULL_DOMAIN_CERTIFIED_ERROR)
    elif not selected_keys_subset_full_keys or not key_cover_holds:
        error = EXACT_OUT_MANY_POOL_REPAIRED_KEY_COVER_ERROR
    else:
        error = EXACT_OUT_MANY_POOL_REPAIRED_FULL_DOMAIN_CERTIFIED_ERROR
    return ExactOutManyPoolRepairedKeyCoverPacket(
        packet_ok=bool(packet_ok),
        error=error,
        selected_keys_subset_full_keys=bool(selected_keys_subset_full_keys),
        key_cover_holds=bool(key_cover_holds),
        selected_domain_canonical_matches_full_domain_canonical=bool(
            selected_domain_canonical_matches_full_domain_canonical
        ),
        selected_candidate_count=len(selected_candidates),
        full_candidate_count=len(full_candidates),
        domination_witnesses=domination_witnesses,
        selected_domain_contract=selected_domain_contract,
        repaired_full_domain_packet=repaired_full_domain_packet,
    )


def build_exact_out_many_pool_repaired_key_cover_packet(
    pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int = 3,
    max_candidate_pools: int = 5,
    max_candidates: int = 12,
    max_iters: int = 4096,
    window: int = 64,
    brute_force_max: int = 512,
    max_full_domain_pools: int = 8,
    max_enumerated_candidates: int = 20_000,
) -> ExactOutManyPoolRepairedKeyCoverPacket:
    amount_out_total_i = _require_amount_out_total_int(amount_out_total)
    (
        max_legs_i,
        max_candidate_pools_i,
        max_candidates_i,
        max_iters_i,
        window_i,
        brute_force_max_i,
        max_full_domain_pools_i,
        max_enumerated_candidates_i,
    ) = _require_runtime_control_values(
        max_legs=max_legs,
        max_candidate_pools=max_candidate_pools,
        max_candidates=max_candidates,
        max_iters=max_iters,
        window=window,
        brute_force_max=brute_force_max,
        max_full_domain_pools=max_full_domain_pools,
        max_enumerated_candidates=max_enumerated_candidates,
    )
    selected_domain_contract = build_exact_out_many_pool_repaired_selected_domain_oracle_contract(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=amount_out_total_i,
        max_legs=max_legs_i,
        max_candidate_pools=max_candidate_pools_i,
        max_candidates=max_candidates_i,
        max_iters=max_iters_i,
        window=window_i,
        brute_force_max=brute_force_max_i,
        max_full_domain_pools=max_full_domain_pools_i,
        max_enumerated_candidates=max_enumerated_candidates_i,
    )
    repaired_full_domain_packet = build_exact_out_many_pool_repaired_full_domain_certified_packet(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=amount_out_total_i,
        max_legs=max_legs_i,
        max_candidate_pools=max_candidate_pools_i,
        max_candidates=max_candidates_i,
        max_iters=max_iters_i,
        window=window_i,
        brute_force_max=brute_force_max_i,
        max_full_domain_pools=max_full_domain_pools_i,
        max_enumerated_candidates=max_enumerated_candidates_i,
    )
    return _build_exact_out_many_pool_repaired_key_cover_packet_from_components(
        selected_domain_contract=selected_domain_contract,
        repaired_full_domain_packet=repaired_full_domain_packet,
    )


def _build_exact_out_many_pool_repaired_key_cover_interpretation_packet_from_key_cover_packet(
    key_cover_packet: ExactOutManyPoolRepairedKeyCoverPacket,
) -> ExactOutManyPoolRepairedKeyCoverInterpretationPacket:
    (
        selected_winner_index_in_range,
        selected_winner_matches_certificate,
        selected_winner_key_minimal,
    ) = _selected_domain_minimum_witness_summary(key_cover_packet.selected_domain_contract)
    (
        domination_witness_indices_in_range,
        domination_witnesses_cover_full_candidates,
        domination_witness_keys_match_candidates,
        domination_witnesses_dominate,
    ) = _key_cover_witness_interpretation_summary(key_cover_packet)
    packet_ok = bool(
        key_cover_packet.packet_ok
        and selected_winner_index_in_range
        and selected_winner_matches_certificate
        and selected_winner_key_minimal
        and domination_witness_indices_in_range
        and domination_witnesses_cover_full_candidates
        and domination_witness_keys_match_candidates
        and domination_witnesses_dominate
    )
    if packet_ok:
        error = None
    elif not key_cover_packet.packet_ok:
        error = str(key_cover_packet.error or EXACT_OUT_MANY_POOL_REPAIRED_KEY_COVER_ERROR)
    else:
        error = EXACT_OUT_MANY_POOL_REPAIRED_KEY_COVER_INTERPRETATION_ERROR
    return ExactOutManyPoolRepairedKeyCoverInterpretationPacket(
        packet_ok=bool(packet_ok),
        error=error,
        selected_winner_index_in_range=bool(selected_winner_index_in_range),
        selected_winner_matches_certificate=bool(selected_winner_matches_certificate),
        selected_winner_key_minimal=bool(selected_winner_key_minimal),
        domination_witness_indices_in_range=bool(domination_witness_indices_in_range),
        domination_witnesses_cover_full_candidates=bool(domination_witnesses_cover_full_candidates),
        domination_witness_keys_match_candidates=bool(domination_witness_keys_match_candidates),
        domination_witnesses_dominate=bool(domination_witnesses_dominate),
        key_cover_packet=key_cover_packet,
    )


def build_exact_out_many_pool_repaired_key_cover_interpretation_packet(
    pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int = 3,
    max_candidate_pools: int = 5,
    max_candidates: int = 12,
    max_iters: int = 4096,
    window: int = 64,
    brute_force_max: int = 512,
    max_full_domain_pools: int = 8,
    max_enumerated_candidates: int = 20_000,
) -> ExactOutManyPoolRepairedKeyCoverInterpretationPacket:
    amount_out_total_i = _require_amount_out_total_int(amount_out_total)
    (
        max_legs_i,
        max_candidate_pools_i,
        max_candidates_i,
        max_iters_i,
        window_i,
        brute_force_max_i,
        max_full_domain_pools_i,
        max_enumerated_candidates_i,
    ) = _require_runtime_control_values(
        max_legs=max_legs,
        max_candidate_pools=max_candidate_pools,
        max_candidates=max_candidates,
        max_iters=max_iters,
        window=window,
        brute_force_max=brute_force_max,
        max_full_domain_pools=max_full_domain_pools,
        max_enumerated_candidates=max_enumerated_candidates,
    )
    key_cover_packet = build_exact_out_many_pool_repaired_key_cover_packet(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=amount_out_total_i,
        max_legs=max_legs_i,
        max_candidate_pools=max_candidate_pools_i,
        max_candidates=max_candidates_i,
        max_iters=max_iters_i,
        window=window_i,
        brute_force_max=brute_force_max_i,
        max_full_domain_pools=max_full_domain_pools_i,
        max_enumerated_candidates=max_enumerated_candidates_i,
    )
    return _build_exact_out_many_pool_repaired_key_cover_interpretation_packet_from_key_cover_packet(
        key_cover_packet
    )


@dataclass(frozen=True)
class _CandidateDomainParams:
    asset_in: str
    asset_out: str
    amount_out_total: int
    max_legs: int
    max_candidate_pools: int
    max_enumerated_candidates: int

    def __post_init__(self) -> None:
        _require_control_fields(
            (
                ("amount_out_total", self.amount_out_total),
                ("max_legs", self.max_legs),
                ("max_candidate_pools", self.max_candidate_pools),
                ("max_enumerated_candidates", self.max_enumerated_candidates),
            )
        )


@dataclass(frozen=True)
class _CandidateDomainChecks:
    audit_pool_ids_sorted_unique: bool
    audit_pool_ids_within_budget: bool
    candidate_domain_nonempty: bool
    all_candidates_complete: bool
    all_candidates_leg_bounded: bool
    all_candidates_leg_pool_ids_sorted_unique: bool
    all_candidates_within_audit_pool_ids: bool
    candidate_count_within_budget: bool

    @property
    def contract_ok(self) -> bool:
        return (
            self.candidate_domain_nonempty
            and self.audit_pool_ids_sorted_unique
            and self.audit_pool_ids_within_budget
            and self.all_candidates_complete
            and self.all_candidates_leg_bounded
            and self.all_candidates_leg_pool_ids_sorted_unique
            and self.all_candidates_within_audit_pool_ids
            and self.candidate_count_within_budget
        )


@dataclass(frozen=True)
class _CandidateDomainEvidence:
    candidates: tuple[SplitManyPoolsExactOutQuote, ...]
    audit_pool_ids: tuple[str, ...]
    checks: _CandidateDomainChecks


def _validate_candidate_domain_assets(params: _CandidateDomainParams) -> None:
    if not params.asset_in or not params.asset_out or params.asset_in == params.asset_out:
        raise ValueError("asset_in and asset_out must be non-empty and distinct")


def _candidate_domain_candidates(
    pools: Sequence[PoolState],
    *,
    params: _CandidateDomainParams,
) -> tuple[SplitManyPoolsExactOutQuote, ...]:
    return tuple(
        enumerate_exact_out_many_pool_candidates(
            pools,
            asset_in=params.asset_in,
            asset_out=params.asset_out,
            amount_out_total=int(params.amount_out_total),
            max_legs=int(params.max_legs),
            max_candidate_pools=int(params.max_candidate_pools),
            max_enumerated_candidates=int(params.max_enumerated_candidates),
        )
    )


def _candidate_domain_audit_pool_ids(candidates: Sequence[SplitManyPoolsExactOutQuote]) -> tuple[str, ...]:
    return tuple(
        sorted(
            {
                leg.pool_id
                for candidate in candidates
                for leg in candidate.legs
            }
        )
    )


def _candidate_domain_checks(
    candidates: Sequence[SplitManyPoolsExactOutQuote],
    audit_pool_ids: Sequence[str],
    *,
    params: _CandidateDomainParams,
) -> _CandidateDomainChecks:
    audit_pool_id_set = set(audit_pool_ids)
    return _CandidateDomainChecks(
        audit_pool_ids_sorted_unique=_audit_pool_ids_sorted_unique(audit_pool_ids),
        audit_pool_ids_within_budget=len(audit_pool_ids) <= int(params.max_candidate_pools),
        candidate_domain_nonempty=bool(candidates),
        all_candidates_complete=all(
            _quote_is_complete_exact_out_candidate(candidate, amount_out_total=int(params.amount_out_total))
            for candidate in candidates
        ),
        all_candidates_leg_bounded=all(1 <= len(candidate.legs) <= int(params.max_legs) for candidate in candidates),
        all_candidates_leg_pool_ids_sorted_unique=all(
            _quote_leg_pool_ids_sorted_unique(candidate) for candidate in candidates
        ),
        all_candidates_within_audit_pool_ids=all(
            all(leg.pool_id in audit_pool_id_set for leg in candidate.legs) for candidate in candidates
        ),
        candidate_count_within_budget=len(candidates) <= int(params.max_enumerated_candidates),
    )


def _build_candidate_domain_evidence(
    pools: Sequence[PoolState],
    *,
    params: _CandidateDomainParams,
) -> _CandidateDomainEvidence:
    candidates = _candidate_domain_candidates(pools, params=params)
    audit_pool_ids = _candidate_domain_audit_pool_ids(candidates)
    checks = _candidate_domain_checks(candidates, audit_pool_ids, params=params)
    return _CandidateDomainEvidence(candidates=candidates, audit_pool_ids=audit_pool_ids, checks=checks)


def _candidate_domain_contract_from_evidence(
    pools: Sequence[PoolState],
    *,
    params: _CandidateDomainParams,
    evidence: _CandidateDomainEvidence,
) -> ExactOutManyPoolCandidateDomainContract:
    checks = evidence.checks
    return ExactOutManyPoolCandidateDomainContract(
        asset_in=str(params.asset_in),
        asset_out=str(params.asset_out),
        amount_out_total=int(params.amount_out_total),
        max_legs=int(params.max_legs),
        max_candidate_pools=int(params.max_candidate_pools),
        max_enumerated_candidates=int(params.max_enumerated_candidates),
        audit_pool_ids=evidence.audit_pool_ids,
        pool_snapshots=tuple(_pool_to_dict(pool) for pool in pools),
        candidates=evidence.candidates,
        candidate_count=len(evidence.candidates),
        audit_pool_ids_sorted_unique=bool(checks.audit_pool_ids_sorted_unique),
        audit_pool_ids_within_budget=bool(checks.audit_pool_ids_within_budget),
        candidate_domain_nonempty=bool(checks.candidate_domain_nonempty),
        all_candidates_complete=bool(checks.all_candidates_complete),
        all_candidates_leg_bounded=bool(checks.all_candidates_leg_bounded),
        all_candidates_leg_pool_ids_sorted_unique=bool(checks.all_candidates_leg_pool_ids_sorted_unique),
        all_candidates_within_audit_pool_ids=bool(checks.all_candidates_within_audit_pool_ids),
        candidate_count_within_budget=bool(checks.candidate_count_within_budget),
        contract_ok=bool(checks.contract_ok),
    )


def build_exact_out_many_pool_candidate_domain_contract(
    pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int = 3,
    max_candidate_pools: int = 5,
    max_enumerated_candidates: int = 20_000,
) -> ExactOutManyPoolCandidateDomainContract:
    amount_out_total_i = _require_amount_out_total_int(amount_out_total)
    params = _CandidateDomainParams(
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=amount_out_total_i,
        max_legs=max_legs,
        max_candidate_pools=max_candidate_pools,
        max_enumerated_candidates=max_enumerated_candidates,
    )
    _validate_candidate_domain_assets(params)
    evidence = _build_candidate_domain_evidence(pools, params=params)
    return _candidate_domain_contract_from_evidence(pools, params=params, evidence=evidence)


def verify_exact_out_many_pool_prefilter_contract_payload(payload: object) -> tuple[bool, str | None]:
    if not isinstance(payload, dict):
        return False, "prefilter contract payload must be a dict"
    if payload.get("schema") != EXACT_OUT_MANY_POOL_PREFILTER_CONTRACT_SCHEMA:
        return False, "unsupported prefilter contract schema"
    try:
        pools_payload = payload["pool_snapshots"]
        if not isinstance(pools_payload, list) or not pools_payload:
            return False, "pool_snapshots must be a non-empty list"
        pools = tuple(_pool_from_dict(pool_payload) for pool_payload in pools_payload)
        expected = build_exact_out_many_pool_prefilter_contract(
            pools,
            asset_in=str(payload["asset_in"]),
            asset_out=str(payload["asset_out"]),
            amount_out_total=_require_payload_int(payload, "amount_out_total"),
            max_legs=_require_payload_int(payload, "max_legs"),
            max_candidate_pools=_require_payload_int(payload, "max_candidate_pools"),
        )
    except (KeyError, TypeError, ValueError) as exc:
        return False, str(exc)
    if payload != expected.to_dict():
        return False, "prefilter contract payload mismatch"
    return True, None


def verify_exact_out_many_pool_repaired_prefilter_contract_payload(payload: object) -> tuple[bool, str | None]:
    if not isinstance(payload, dict):
        return False, "repaired prefilter contract payload must be a dict"
    if payload.get("schema") != EXACT_OUT_MANY_POOL_REPAIRED_PREFILTER_CONTRACT_SCHEMA:
        return False, "unsupported repaired prefilter contract schema"
    try:
        pools_payload = payload["pool_snapshots"]
        if not isinstance(pools_payload, list) or not pools_payload:
            return False, "pool_snapshots must be a non-empty list"
        pools = tuple(_pool_from_dict(pool_payload) for pool_payload in pools_payload)
        expected = build_exact_out_many_pool_repaired_prefilter_contract(
            pools,
            asset_in=str(payload["asset_in"]),
            asset_out=str(payload["asset_out"]),
            amount_out_total=_require_payload_int(payload, "amount_out_total"),
            max_legs=_require_payload_int(payload, "max_legs"),
            max_candidate_pools=_require_payload_int(payload, "max_candidate_pools"),
            max_full_domain_pools=_require_payload_int(payload, "max_full_domain_pools"),
            max_enumerated_candidates=_require_payload_int(payload, "max_enumerated_candidates"),
        )
    except (KeyError, TypeError, ValueError) as exc:
        return False, str(exc)
    if payload != expected.to_dict():
        return False, "repaired prefilter contract payload mismatch"
    return True, None


def audit_exact_out_two_pool_runtime_canonicality(
    pool0: PoolState,
    pool1: PoolState,
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    brute_force_max: int | None = None,
) -> ExactOutTwoPoolCanonicalityAudit:
    amount_out_total_i = _require_amount_out_total_int(amount_out_total)
    brute_force_max_i = _require_optional_control_int(brute_force_max, name="brute_force_max")
    candidates = enumerate_exact_out_two_pool_candidates(
        pool0,
        pool1,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=amount_out_total_i,
    )
    certificate = build_exact_out_route_canonical_certificate(candidates)
    runtime_quote = best_split_two_pools_exact_out_for_pools(
        pool0,
        pool1,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=amount_out_total_i,
        brute_force_max=(max(0, brute_force_max_i) if brute_force_max_i is not None else max(1, amount_out_total_i)),
    )
    runtime_many = split_two_pools_exact_out_quote_to_many(runtime_quote)
    return ExactOutTwoPoolCanonicalityAudit(
        runtime_matches_canonical=runtime_many == certificate.winner_quote,
        runtime_quote=runtime_many,
        canonical_winner_quote=certificate.winner_quote,
        candidate_count=len(candidates),
        certificate=certificate,
    )


@dataclass(frozen=True)
class _ManyPoolCanonicalityParams:
    asset_in: str
    asset_out: str
    amount_out_total: int
    max_legs: int
    max_candidate_pools: int
    max_candidates: int
    max_iters: int
    window: int
    brute_force_max: int
    max_full_domain_pools: int
    max_enumerated_candidates: int

    def __post_init__(self) -> None:
        _require_control_fields(
            (
                ("amount_out_total", self.amount_out_total),
                ("max_legs", self.max_legs),
                ("max_candidate_pools", self.max_candidate_pools),
                ("max_candidates", self.max_candidates),
                ("max_iters", self.max_iters),
                ("window", self.window),
                ("brute_force_max", self.brute_force_max),
                ("max_full_domain_pools", self.max_full_domain_pools),
                ("max_enumerated_candidates", self.max_enumerated_candidates),
            )
        )


def _bounded_exact_out_many_pool_runtime_domain(
    pools: Sequence[PoolState],
    *,
    params: _ManyPoolCanonicalityParams,
) -> Any:
    return _kernel_bounded_exact_out_many_pool_runtime_domain(
        pools,
        asset_in=params.asset_in,
        asset_out=params.asset_out,
        amount_out_total=int(params.amount_out_total),
        max_legs=int(params.max_legs),
        max_candidate_pools=int(params.max_candidate_pools),
        max_candidates=int(params.max_candidates),
        max_iters=int(params.max_iters),
        window=int(params.window),
        brute_force_max=int(params.brute_force_max),
        max_full_domain_pools=int(params.max_full_domain_pools),
        max_enumerated_candidates=int(params.max_enumerated_candidates),
    )


def _selected_pools_for_audit_pool_ids(
    pools: Sequence[PoolState],
    *,
    audit_pool_ids: Sequence[str],
) -> tuple[PoolState, ...]:
    pools_by_id = {pool.pool_id: pool for pool in pools}
    return tuple(
        pools_by_id[pool_id]
        for pool_id in audit_pool_ids
        if pool_id in pools_by_id
    )


def _many_pool_projection_cover_audit(
    selected_pools: Sequence[PoolState],
    *,
    audit_pool_ids: Sequence[str],
    params: _ManyPoolCanonicalityParams,
) -> ExactOutManyPoolProjectionCoverAudit | None:
    if len(selected_pools) != len(audit_pool_ids):
        return None
    try:
        kernel_audit = _kernel_audit_exact_out_many_pool_selected_domain_projection_cover(
            selected_pools,
            asset_in=params.asset_in,
            asset_out=params.asset_out,
            amount_out_total=int(params.amount_out_total),
            max_legs=int(params.max_legs),
            max_selected_pools=max(len(selected_pools), 1),
            max_enumerated_candidates=int(params.max_enumerated_candidates),
        )
    except ValueError:
        return None
    return _projection_cover_audit_from_kernel(kernel_audit)


def _many_pool_canonicality_audit_from_bounded_domain(
    pools: Sequence[PoolState],
    bounded: Any,
    *,
    params: _ManyPoolCanonicalityParams,
) -> ExactOutManyPoolCanonicalityAudit:
    audit_pool_ids = tuple(bounded.audit_pool_ids)
    selected_pools = _selected_pools_for_audit_pool_ids(pools, audit_pool_ids=audit_pool_ids)
    projection_cover_audit = _many_pool_projection_cover_audit(
        selected_pools,
        audit_pool_ids=audit_pool_ids,
        params=params,
    )
    return ExactOutManyPoolCanonicalityAudit(
        runtime_matches_canonical=bounded.runtime_quote == bounded.canonical_quote,
        runtime_quote=bounded.runtime_quote,
        canonical_winner_quote=bounded.canonical_quote,
        candidate_count=len(bounded.candidates),
        audit_pool_ids=audit_pool_ids,
        max_legs=int(params.max_legs),
        certificate=build_exact_out_route_canonical_certificate(bounded.candidates),
        projection_cover_audit=projection_cover_audit,
    )


def audit_exact_out_many_pool_runtime_canonicality(
    pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int = 3,
    max_candidate_pools: int = 5,
    max_candidates: int = 12,
    max_iters: int = 4096,
    window: int = 64,
    brute_force_max: int = 512,
    max_full_domain_pools: int = 8,
    max_enumerated_candidates: int = 20_000,
) -> ExactOutManyPoolCanonicalityAudit:
    amount_out_total_i = _require_amount_out_total_int(amount_out_total)
    params = _ManyPoolCanonicalityParams(
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=amount_out_total_i,
        max_legs=max_legs,
        max_candidate_pools=max_candidate_pools,
        max_candidates=max_candidates,
        max_iters=max_iters,
        window=window,
        brute_force_max=brute_force_max,
        max_full_domain_pools=max_full_domain_pools,
        max_enumerated_candidates=max_enumerated_candidates,
    )
    bounded = _bounded_exact_out_many_pool_runtime_domain(pools, params=params)
    return _many_pool_canonicality_audit_from_bounded_domain(pools, bounded, params=params)


def build_exact_out_many_pool_oracle_contract(
    pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int = 3,
    max_candidate_pools: int = 5,
    max_candidates: int = 12,
    max_iters: int = 4096,
    window: int = 64,
    brute_force_max: int = 512,
    max_full_domain_pools: int = 8,
    max_enumerated_candidates: int = 20_000,
) -> ExactOutManyPoolOracleContract:
    amount_out_total_i = _require_amount_out_total_int(amount_out_total)
    (
        max_legs_i,
        max_candidate_pools_i,
        max_candidates_i,
        max_iters_i,
        window_i,
        brute_force_max_i,
        max_full_domain_pools_i,
        max_enumerated_candidates_i,
    ) = _require_runtime_control_values(
        max_legs=max_legs,
        max_candidate_pools=max_candidate_pools,
        max_candidates=max_candidates,
        max_iters=max_iters,
        window=window,
        brute_force_max=brute_force_max,
        max_full_domain_pools=max_full_domain_pools,
        max_enumerated_candidates=max_enumerated_candidates,
    )
    if not asset_in or not asset_out or asset_in == asset_out:
        raise ValueError("asset_in and asset_out must be non-empty and distinct")
    audit = audit_exact_out_many_pool_runtime_canonicality(
        pools,
        asset_in=str(asset_in),
        asset_out=str(asset_out),
        amount_out_total=amount_out_total_i,
        max_legs=max_legs_i,
        max_candidate_pools=max_candidate_pools_i,
        max_candidates=max_candidates_i,
        max_iters=max_iters_i,
        window=window_i,
        brute_force_max=brute_force_max_i,
        max_full_domain_pools=max_full_domain_pools_i,
        max_enumerated_candidates=max_enumerated_candidates_i,
    )
    return ExactOutManyPoolOracleContract(
        asset_in=str(asset_in),
        asset_out=str(asset_out),
        amount_out_total=amount_out_total_i,
        max_legs=max_legs_i,
        max_candidate_pools=max_candidate_pools_i,
        max_candidates=max_candidates_i,
        max_iters=max_iters_i,
        window=window_i,
        brute_force_max=brute_force_max_i,
        max_full_domain_pools=max_full_domain_pools_i,
        max_enumerated_candidates=max_enumerated_candidates_i,
        pool_snapshots=tuple(_pool_to_dict(pool) for pool in pools),
        audit=audit,
    )


@dataclass(frozen=True)
class _RepairedSelectedDomainOracleEvidence:
    repaired_contract: ExactOutManyPoolRepairedPrefilterContract
    audit: ExactOutManyPoolCanonicalityAudit
    audit_pool_ids_match_repaired_selected_pool_ids: bool

    @property
    def contract_ok(self) -> bool:
        return bool(
            self.repaired_contract.contract_ok
            and self.audit_pool_ids_match_repaired_selected_pool_ids
            and self.audit.runtime_matches_canonical
        )


def _audit_repaired_selected_domain(
    selected_pools: Sequence[PoolState],
    *,
    params: _ExactOutManyPoolRuntimeParams,
) -> ExactOutManyPoolCanonicalityAudit:
    return audit_exact_out_many_pool_runtime_canonicality(
        selected_pools,
        asset_in=str(params.asset_in),
        asset_out=str(params.asset_out),
        amount_out_total=int(params.amount_out_total),
        max_legs=int(params.max_legs),
        max_candidate_pools=max(len(selected_pools), 1),
        max_candidates=int(params.max_candidates),
        max_iters=int(params.max_iters),
        window=int(params.window),
        brute_force_max=int(params.brute_force_max),
        max_full_domain_pools=max(len(selected_pools), int(params.max_full_domain_pools)),
        max_enumerated_candidates=int(params.max_enumerated_candidates),
    )


def _audit_repaired_selected_domain_fallback(
    pools: Sequence[PoolState],
    *,
    params: _ExactOutManyPoolRuntimeParams,
) -> ExactOutManyPoolCanonicalityAudit:
    return audit_exact_out_many_pool_runtime_canonicality(
        tuple(pools),
        asset_in=str(params.asset_in),
        asset_out=str(params.asset_out),
        amount_out_total=int(params.amount_out_total),
        max_legs=int(params.max_legs),
        max_candidate_pools=int(params.max_candidate_pools),
        max_candidates=int(params.max_candidates),
        max_iters=int(params.max_iters),
        window=int(params.window),
        brute_force_max=int(params.brute_force_max),
        max_full_domain_pools=int(params.max_full_domain_pools),
        max_enumerated_candidates=int(params.max_enumerated_candidates),
    )


def _repaired_selected_domain_oracle_audit(
    pools: Sequence[PoolState],
    repaired_contract: ExactOutManyPoolRepairedPrefilterContract,
    *,
    params: _ExactOutManyPoolRuntimeParams,
) -> ExactOutManyPoolCanonicalityAudit:
    if not repaired_contract.contract_ok:
        return _audit_repaired_selected_domain_fallback(pools, params=params)
    selected_pools = _repaired_selected_pools_from_contract(
        pools,
        repaired_contract=repaired_contract,
    )
    return _audit_repaired_selected_domain(selected_pools, params=params)


def _build_repaired_selected_domain_oracle_evidence(
    pools: Sequence[PoolState],
    *,
    params: _ExactOutManyPoolRuntimeParams,
) -> _RepairedSelectedDomainOracleEvidence:
    repaired_contract = _repaired_prefilter_contract_for_runtime_params(pools, params=params)
    audit = _repaired_selected_domain_oracle_audit(pools, repaired_contract, params=params)
    audit_pool_ids_match = bool(tuple(audit.audit_pool_ids) == tuple(repaired_contract.repaired_selected_pool_ids))
    return _RepairedSelectedDomainOracleEvidence(
        repaired_contract=repaired_contract,
        audit=audit,
        audit_pool_ids_match_repaired_selected_pool_ids=audit_pool_ids_match,
    )


def _repaired_selected_domain_oracle_contract_from_evidence(
    pools: Sequence[PoolState],
    *,
    params: _ExactOutManyPoolRuntimeParams,
    evidence: _RepairedSelectedDomainOracleEvidence,
) -> ExactOutManyPoolRepairedSelectedDomainOracleContract:
    return ExactOutManyPoolRepairedSelectedDomainOracleContract(
        asset_in=str(params.asset_in),
        asset_out=str(params.asset_out),
        amount_out_total=int(params.amount_out_total),
        max_legs=int(params.max_legs),
        max_candidate_pools=int(params.max_candidate_pools),
        max_candidates=int(params.max_candidates),
        max_iters=int(params.max_iters),
        window=int(params.window),
        brute_force_max=int(params.brute_force_max),
        max_full_domain_pools=int(params.max_full_domain_pools),
        max_enumerated_candidates=int(params.max_enumerated_candidates),
        pool_snapshots=tuple(_pool_to_dict(pool) for pool in pools),
        repaired_contract=evidence.repaired_contract,
        audit=evidence.audit,
        audit_pool_ids_match_repaired_selected_pool_ids=bool(
            evidence.audit_pool_ids_match_repaired_selected_pool_ids
        ),
        contract_ok=bool(evidence.contract_ok),
    )


def build_exact_out_many_pool_repaired_selected_domain_oracle_contract(
    pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int = 3,
    max_candidate_pools: int = 5,
    max_candidates: int = 12,
    max_iters: int = 4096,
    window: int = 64,
    brute_force_max: int = 512,
    max_full_domain_pools: int = 8,
    max_enumerated_candidates: int = 20_000,
) -> ExactOutManyPoolRepairedSelectedDomainOracleContract:
    amount_out_total_i = _require_amount_out_total_int(amount_out_total)
    params = _ExactOutManyPoolRuntimeParams(
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=amount_out_total_i,
        max_legs=max_legs,
        max_candidate_pools=max_candidate_pools,
        max_candidates=max_candidates,
        max_iters=max_iters,
        window=window,
        brute_force_max=brute_force_max,
        max_full_domain_pools=max_full_domain_pools,
        max_enumerated_candidates=max_enumerated_candidates,
    )
    evidence = _build_repaired_selected_domain_oracle_evidence(pools, params=params)
    return _repaired_selected_domain_oracle_contract_from_evidence(pools, params=params, evidence=evidence)


def quote_exact_out_many_pool_repaired_selected_domain(
    pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int = 3,
    max_candidate_pools: int = 5,
    max_candidates: int = 12,
    max_iters: int = 4096,
    window: int = 64,
    brute_force_max: int = 512,
    max_full_domain_pools: int = 8,
    max_enumerated_candidates: int = 20_000,
) -> tuple[
    SplitManyPoolsExactOutQuote | None,
    str | None,
    ExactOutManyPoolRepairedSelectedDomainOracleContract,
]:
    amount_out_total_i = _require_amount_out_total_int(amount_out_total)
    (
        max_legs_i,
        max_candidate_pools_i,
        max_candidates_i,
        max_iters_i,
        window_i,
        brute_force_max_i,
        max_full_domain_pools_i,
        max_enumerated_candidates_i,
    ) = _require_runtime_control_values(
        max_legs=max_legs,
        max_candidate_pools=max_candidate_pools,
        max_candidates=max_candidates,
        max_iters=max_iters,
        window=window,
        brute_force_max=brute_force_max,
        max_full_domain_pools=max_full_domain_pools,
        max_enumerated_candidates=max_enumerated_candidates,
    )
    contract = build_exact_out_many_pool_repaired_selected_domain_oracle_contract(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=amount_out_total_i,
        max_legs=max_legs_i,
        max_candidate_pools=max_candidate_pools_i,
        max_candidates=max_candidates_i,
        max_iters=max_iters_i,
        window=window_i,
        brute_force_max=brute_force_max_i,
        max_full_domain_pools=max_full_domain_pools_i,
        max_enumerated_candidates=max_enumerated_candidates_i,
    )
    if contract.contract_ok:
        return contract.audit.runtime_quote, None, contract
    return None, EXACT_OUT_MANY_POOL_REPAIRED_SELECTED_DOMAIN_UNAVAILABLE_ERROR, contract


@dataclass(frozen=True)
class _ExactOutManyPoolRuntimeParams:
    asset_in: str
    asset_out: str
    amount_out_total: int
    max_legs: int
    max_candidate_pools: int
    max_candidates: int
    max_iters: int
    window: int
    brute_force_max: int
    max_full_domain_pools: int
    max_enumerated_candidates: int

    def __post_init__(self) -> None:
        _require_control_fields(
            (
                ("amount_out_total", self.amount_out_total),
                ("max_legs", self.max_legs),
                ("max_candidate_pools", self.max_candidate_pools),
                ("max_candidates", self.max_candidates),
                ("max_iters", self.max_iters),
                ("window", self.window),
                ("brute_force_max", self.brute_force_max),
                ("max_full_domain_pools", self.max_full_domain_pools),
                ("max_enumerated_candidates", self.max_enumerated_candidates),
            )
        )


@dataclass(frozen=True)
class _RepairedAdvisorySuccessPayload:
    advisory_quote: SplitManyPoolsExactOutQuote
    runtime_quote: SplitManyPoolsExactOutQuote
    repaired_contract: ExactOutManyPoolRepairedPrefilterContract
    projection_cover_audit: ExactOutManyPoolProjectionCoverAudit | None


def _repaired_prefilter_contract_for_runtime_params(
    pools: Sequence[PoolState],
    *,
    params: _ExactOutManyPoolRuntimeParams,
) -> ExactOutManyPoolRepairedPrefilterContract:
    return build_exact_out_many_pool_repaired_prefilter_contract(
        pools,
        asset_in=params.asset_in,
        asset_out=params.asset_out,
        amount_out_total=int(params.amount_out_total),
        max_legs=int(params.max_legs),
        max_candidate_pools=int(params.max_candidate_pools),
        max_full_domain_pools=int(params.max_full_domain_pools),
        max_enumerated_candidates=int(params.max_enumerated_candidates),
    )


def _repaired_advisory_runtime_quote(
    pools: Sequence[PoolState],
    *,
    params: _ExactOutManyPoolRuntimeParams,
) -> SplitManyPoolsExactOutQuote:
    return best_split_many_pools_exact_out_for_pools(
        pools,
        asset_in=params.asset_in,
        asset_out=params.asset_out,
        amount_out_total=int(params.amount_out_total),
        max_legs=int(params.max_legs),
        max_candidates=int(params.max_candidates),
        max_iters=int(params.max_iters),
        window=int(params.window),
        brute_force_max=int(params.brute_force_max),
    )


def _repaired_advisory_unavailable_packet(
    runtime_quote: SplitManyPoolsExactOutQuote,
    repaired_contract: ExactOutManyPoolRepairedPrefilterContract,
    *,
    params: _ExactOutManyPoolRuntimeParams,
) -> ExactOutManyPoolRepairedAdvisoryQuotePacket:
    return ExactOutManyPoolRepairedAdvisoryQuotePacket(
        packet_ok=False,
        advisory_quote=None,
        runtime_quote=runtime_quote,
        runtime_matches_advisory=False,
        error=EXACT_OUT_MANY_POOL_REPAIRED_ADVISORY_UNAVAILABLE_ERROR,
        max_candidates=int(params.max_candidates),
        max_iters=int(params.max_iters),
        window=int(params.window),
        brute_force_max=int(params.brute_force_max),
        repaired_contract=repaired_contract,
        projection_cover_audit=None,
    )


def _repaired_advisory_selected_domain(
    selected_pools: Sequence[PoolState],
    *,
    params: _ExactOutManyPoolRuntimeParams,
) -> Any:
    return _kernel_build_exact_out_many_pool_selected_domain(
        selected_pools,
        asset_in=params.asset_in,
        asset_out=params.asset_out,
        amount_out_total=int(params.amount_out_total),
        max_legs=int(params.max_legs),
        max_enumerated_candidates=int(params.max_enumerated_candidates),
    )


def _repaired_advisory_projection_cover_audit(
    selected_pools: Sequence[PoolState],
    *,
    params: _ExactOutManyPoolRuntimeParams,
) -> ExactOutManyPoolProjectionCoverAudit | None:
    try:
        kernel_audit = _kernel_audit_exact_out_many_pool_selected_domain_projection_cover(
            selected_pools,
            asset_in=params.asset_in,
            asset_out=params.asset_out,
            amount_out_total=int(params.amount_out_total),
            max_legs=int(params.max_legs),
            max_selected_pools=max(len(selected_pools), 1),
            max_enumerated_candidates=int(params.max_enumerated_candidates),
        )
        return _projection_cover_audit_from_kernel(kernel_audit)
    except ValueError:
        return None


def _repaired_advisory_success_packet(
    *,
    payload: _RepairedAdvisorySuccessPayload,
    params: _ExactOutManyPoolRuntimeParams,
) -> ExactOutManyPoolRepairedAdvisoryQuotePacket:
    return ExactOutManyPoolRepairedAdvisoryQuotePacket(
        packet_ok=True,
        advisory_quote=payload.advisory_quote,
        runtime_quote=payload.runtime_quote,
        runtime_matches_advisory=bool(payload.runtime_quote == payload.advisory_quote),
        error=None,
        max_candidates=int(params.max_candidates),
        max_iters=int(params.max_iters),
        window=int(params.window),
        brute_force_max=int(params.brute_force_max),
        repaired_contract=payload.repaired_contract,
        projection_cover_audit=payload.projection_cover_audit,
    )


def build_exact_out_many_pool_repaired_advisory_quote_packet(
    pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int = 3,
    max_candidate_pools: int = 5,
    max_candidates: int = 12,
    max_iters: int = 4096,
    window: int = 64,
    brute_force_max: int = 512,
    max_full_domain_pools: int = 8,
    max_enumerated_candidates: int = 20_000,
) -> ExactOutManyPoolRepairedAdvisoryQuotePacket:
    amount_out_total_i = _require_amount_out_total_int(amount_out_total)
    params = _ExactOutManyPoolRuntimeParams(
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=amount_out_total_i,
        max_legs=max_legs,
        max_candidate_pools=max_candidate_pools,
        max_candidates=max_candidates,
        max_iters=max_iters,
        window=window,
        brute_force_max=brute_force_max,
        max_full_domain_pools=max_full_domain_pools,
        max_enumerated_candidates=max_enumerated_candidates,
    )
    repaired_contract = _repaired_prefilter_contract_for_runtime_params(pools, params=params)
    runtime_quote = _repaired_advisory_runtime_quote(pools, params=params)
    if not repaired_contract.contract_ok:
        return _repaired_advisory_unavailable_packet(runtime_quote, repaired_contract, params=params)

    repaired_selected_pools = _repaired_selected_pools_from_contract(
        pools,
        repaired_contract=repaired_contract,
    )
    repaired_selected_domain = _repaired_advisory_selected_domain(repaired_selected_pools, params=params)
    projection_cover_audit = _repaired_advisory_projection_cover_audit(repaired_selected_pools, params=params)
    advisory_quote = _candidate_quote_to_core_quote(repaired_selected_domain.canonical_quote)
    return _repaired_advisory_success_packet(
        payload=_RepairedAdvisorySuccessPayload(
            advisory_quote=advisory_quote,
            runtime_quote=runtime_quote,
            repaired_contract=repaired_contract,
            projection_cover_audit=projection_cover_audit,
        ),
        params=params,
    )


def quote_exact_out_many_pool_repaired_advisory(
    pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int = 3,
    max_candidate_pools: int = 5,
    max_candidates: int = 12,
    max_iters: int = 4096,
    window: int = 64,
    brute_force_max: int = 512,
    max_full_domain_pools: int = 8,
    max_enumerated_candidates: int = 20_000,
) -> tuple[SplitManyPoolsExactOutQuote | None, str | None, ExactOutManyPoolRepairedAdvisoryQuotePacket]:
    amount_out_total_i = _require_amount_out_total_int(amount_out_total)
    (
        max_legs_i,
        max_candidate_pools_i,
        max_candidates_i,
        max_iters_i,
        window_i,
        brute_force_max_i,
        max_full_domain_pools_i,
        max_enumerated_candidates_i,
    ) = _require_runtime_control_values(
        max_legs=max_legs,
        max_candidate_pools=max_candidate_pools,
        max_candidates=max_candidates,
        max_iters=max_iters,
        window=window,
        brute_force_max=brute_force_max,
        max_full_domain_pools=max_full_domain_pools,
        max_enumerated_candidates=max_enumerated_candidates,
    )
    packet = build_exact_out_many_pool_repaired_advisory_quote_packet(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=amount_out_total_i,
        max_legs=max_legs_i,
        max_candidate_pools=max_candidate_pools_i,
        max_candidates=max_candidates_i,
        max_iters=max_iters_i,
        window=window_i,
        brute_force_max=brute_force_max_i,
        max_full_domain_pools=max_full_domain_pools_i,
        max_enumerated_candidates=max_enumerated_candidates_i,
    )
    if packet.packet_ok:
        return packet.advisory_quote, None, packet
    return None, str(packet.error or EXACT_OUT_MANY_POOL_REPAIRED_ADVISORY_UNAVAILABLE_ERROR), packet


def _build_exact_out_many_pool_repaired_full_domain_certified_packet_from_repaired_packet(
    repaired_packet: ExactOutManyPoolRepairedAdvisoryQuotePacket,
    pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int,
    max_full_domain_pools: int,
    max_enumerated_candidates: int,
) -> ExactOutManyPoolRepairedFullDomainCertifiedPacket:
    max_legs_i = _require_control_int(max_legs, name="max_legs")
    max_full_domain_pools_i = _require_control_int(max_full_domain_pools, name="max_full_domain_pools")
    max_enumerated_candidates_i = _require_control_int(
        max_enumerated_candidates,
        name="max_enumerated_candidates",
    )
    feasible_pool_ids, full_candidates, full_domain_certificate = _build_exact_out_many_pool_full_domain_certificate(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=max_legs_i,
        max_full_domain_pools=max_full_domain_pools_i,
        max_enumerated_candidates=max_enumerated_candidates_i,
    )
    repaired_quote = repaired_packet.advisory_quote
    repaired_matches_full_canonical = bool(
        repaired_quote is not None and repaired_quote == full_domain_certificate.winner_quote
    )
    packet_ok = bool(repaired_packet.packet_ok and repaired_matches_full_canonical)
    error: str | None
    if packet_ok:
        error = None
    elif not repaired_packet.packet_ok:
        error = str(repaired_packet.error or EXACT_OUT_MANY_POOL_REPAIRED_ADVISORY_UNAVAILABLE_ERROR)
    else:
        error = EXACT_OUT_MANY_POOL_REPAIRED_FULL_DOMAIN_CERTIFIED_ERROR
    return ExactOutManyPoolRepairedFullDomainCertifiedPacket(
        packet_ok=bool(packet_ok),
        repaired_quote=repaired_quote,
        repaired_matches_full_canonical=bool(repaired_matches_full_canonical),
        error=error,
        full_domain_feasible_pool_ids=tuple(feasible_pool_ids),
        full_domain_candidate_count=len(full_candidates),
        full_domain_canonical_quote=full_domain_certificate.winner_quote,
        repaired_packet=repaired_packet,
        full_domain_certificate=full_domain_certificate,
    )


def build_exact_out_many_pool_repaired_full_domain_certified_packet(
    pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int = 3,
    max_candidate_pools: int = 5,
    max_candidates: int = 12,
    max_iters: int = 4096,
    window: int = 64,
    brute_force_max: int = 512,
    max_full_domain_pools: int = 8,
    max_enumerated_candidates: int = 20_000,
) -> ExactOutManyPoolRepairedFullDomainCertifiedPacket:
    amount_out_total_i = _require_amount_out_total_int(amount_out_total)
    (
        max_legs_i,
        max_candidate_pools_i,
        max_candidates_i,
        max_iters_i,
        window_i,
        brute_force_max_i,
        max_full_domain_pools_i,
        max_enumerated_candidates_i,
    ) = _require_runtime_control_values(
        max_legs=max_legs,
        max_candidate_pools=max_candidate_pools,
        max_candidates=max_candidates,
        max_iters=max_iters,
        window=window,
        brute_force_max=brute_force_max,
        max_full_domain_pools=max_full_domain_pools,
        max_enumerated_candidates=max_enumerated_candidates,
    )
    repaired_packet = build_exact_out_many_pool_repaired_advisory_quote_packet(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=amount_out_total_i,
        max_legs=max_legs_i,
        max_candidate_pools=max_candidate_pools_i,
        max_candidates=max_candidates_i,
        max_iters=max_iters_i,
        window=window_i,
        brute_force_max=brute_force_max_i,
        max_full_domain_pools=max_full_domain_pools_i,
        max_enumerated_candidates=max_enumerated_candidates_i,
    )
    return _build_exact_out_many_pool_repaired_full_domain_certified_packet_from_repaired_packet(
        repaired_packet,
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=amount_out_total_i,
        max_legs=max_legs_i,
        max_full_domain_pools=max_full_domain_pools_i,
        max_enumerated_candidates=max_enumerated_candidates_i,
    )


def quote_exact_out_many_pool_repaired_full_domain_certified(
    pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int = 3,
    max_candidate_pools: int = 5,
    max_candidates: int = 12,
    max_iters: int = 4096,
    window: int = 64,
    brute_force_max: int = 512,
    max_full_domain_pools: int = 8,
    max_enumerated_candidates: int = 20_000,
) -> tuple[SplitManyPoolsExactOutQuote | None, str | None, ExactOutManyPoolRepairedFullDomainCertifiedPacket]:
    amount_out_total_i = _require_amount_out_total_int(amount_out_total)
    (
        max_legs_i,
        max_candidate_pools_i,
        max_candidates_i,
        max_iters_i,
        window_i,
        brute_force_max_i,
        max_full_domain_pools_i,
        max_enumerated_candidates_i,
    ) = _require_runtime_control_values(
        max_legs=max_legs,
        max_candidate_pools=max_candidate_pools,
        max_candidates=max_candidates,
        max_iters=max_iters,
        window=window,
        brute_force_max=brute_force_max,
        max_full_domain_pools=max_full_domain_pools,
        max_enumerated_candidates=max_enumerated_candidates,
    )
    packet = build_exact_out_many_pool_repaired_full_domain_certified_packet(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=amount_out_total_i,
        max_legs=max_legs_i,
        max_candidate_pools=max_candidate_pools_i,
        max_candidates=max_candidates_i,
        max_iters=max_iters_i,
        window=window_i,
        brute_force_max=brute_force_max_i,
        max_full_domain_pools=max_full_domain_pools_i,
        max_enumerated_candidates=max_enumerated_candidates_i,
    )
    if packet.packet_ok:
        return packet.repaired_quote, None, packet
    return None, str(packet.error or EXACT_OUT_MANY_POOL_REPAIRED_FULL_DOMAIN_CERTIFIED_ERROR), packet


@dataclass(frozen=True)
class _BoundedWorkaroundComponents:
    oracle_contract: ExactOutManyPoolOracleContract
    repaired_packet: ExactOutManyPoolRepairedAdvisoryQuotePacket
    repaired_full_domain_packet: ExactOutManyPoolRepairedFullDomainCertifiedPacket

    @property
    def runtime_quotes_agree(self) -> bool:
        return bool(
            self.oracle_contract.audit.runtime_quote
            == self.repaired_full_domain_packet.repaired_packet.runtime_quote
        )

    @property
    def runtime_matches_repaired_advisory(self) -> bool:
        return bool(
            self.runtime_quotes_agree
            and self.repaired_full_domain_packet.repaired_quote is not None
            and self.oracle_contract.audit.runtime_quote == self.repaired_full_domain_packet.repaired_quote
        )

    @property
    def packet_ok(self) -> bool:
        return bool(
            self.oracle_contract.audit.runtime_matches_canonical
            and self.repaired_full_domain_packet.packet_ok
            and self.runtime_quotes_agree
        )


def _oracle_contract_for_runtime_params(
    pools: Sequence[PoolState],
    *,
    params: _ExactOutManyPoolRuntimeParams,
) -> ExactOutManyPoolOracleContract:
    return build_exact_out_many_pool_oracle_contract(
        pools,
        asset_in=params.asset_in,
        asset_out=params.asset_out,
        amount_out_total=int(params.amount_out_total),
        max_legs=int(params.max_legs),
        max_candidate_pools=int(params.max_candidate_pools),
        max_candidates=int(params.max_candidates),
        max_iters=int(params.max_iters),
        window=int(params.window),
        brute_force_max=int(params.brute_force_max),
        max_full_domain_pools=int(params.max_full_domain_pools),
        max_enumerated_candidates=int(params.max_enumerated_candidates),
    )


def _repaired_advisory_packet_for_runtime_params(
    pools: Sequence[PoolState],
    *,
    params: _ExactOutManyPoolRuntimeParams,
) -> ExactOutManyPoolRepairedAdvisoryQuotePacket:
    return build_exact_out_many_pool_repaired_advisory_quote_packet(
        pools,
        asset_in=params.asset_in,
        asset_out=params.asset_out,
        amount_out_total=int(params.amount_out_total),
        max_legs=int(params.max_legs),
        max_candidate_pools=int(params.max_candidate_pools),
        max_candidates=int(params.max_candidates),
        max_iters=int(params.max_iters),
        window=int(params.window),
        brute_force_max=int(params.brute_force_max),
        max_full_domain_pools=int(params.max_full_domain_pools),
        max_enumerated_candidates=int(params.max_enumerated_candidates),
    )


def _repaired_full_domain_packet_for_runtime_params(
    repaired_packet: ExactOutManyPoolRepairedAdvisoryQuotePacket,
    pools: Sequence[PoolState],
    *,
    params: _ExactOutManyPoolRuntimeParams,
) -> ExactOutManyPoolRepairedFullDomainCertifiedPacket:
    return _build_exact_out_many_pool_repaired_full_domain_certified_packet_from_repaired_packet(
        repaired_packet,
        pools,
        asset_in=params.asset_in,
        asset_out=params.asset_out,
        amount_out_total=int(params.amount_out_total),
        max_legs=int(params.max_legs),
        max_full_domain_pools=int(params.max_full_domain_pools),
        max_enumerated_candidates=int(params.max_enumerated_candidates),
    )


def _build_bounded_workaround_components(
    pools: Sequence[PoolState],
    *,
    params: _ExactOutManyPoolRuntimeParams,
) -> _BoundedWorkaroundComponents:
    oracle_contract = _oracle_contract_for_runtime_params(pools, params=params)
    repaired_packet = _repaired_advisory_packet_for_runtime_params(pools, params=params)
    repaired_full_domain_packet = _repaired_full_domain_packet_for_runtime_params(
        repaired_packet,
        pools,
        params=params,
    )
    return _BoundedWorkaroundComponents(
        oracle_contract=oracle_contract,
        repaired_packet=repaired_packet,
        repaired_full_domain_packet=repaired_full_domain_packet,
    )


def _bounded_workaround_packet_from_components(
    components: _BoundedWorkaroundComponents,
) -> ExactOutManyPoolBoundedWorkaroundPacket:
    return ExactOutManyPoolBoundedWorkaroundPacket(
        oracle_contract=components.oracle_contract,
        repaired_packet=components.repaired_packet,
        repaired_full_domain_packet=components.repaired_full_domain_packet,
        runtime_quotes_agree=bool(components.runtime_quotes_agree),
        runtime_matches_repaired_advisory=bool(components.runtime_matches_repaired_advisory),
        packet_ok=bool(components.packet_ok),
    )


def build_exact_out_many_pool_bounded_workaround_packet(
    pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int = 3,
    max_candidate_pools: int = 5,
    max_candidates: int = 12,
    max_iters: int = 4096,
    window: int = 64,
    brute_force_max: int = 512,
    max_full_domain_pools: int = 8,
    max_enumerated_candidates: int = 20_000,
) -> ExactOutManyPoolBoundedWorkaroundPacket:
    amount_out_total_i = _require_amount_out_total_int(amount_out_total)
    params = _ExactOutManyPoolRuntimeParams(
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=amount_out_total_i,
        max_legs=max_legs,
        max_candidate_pools=max_candidate_pools,
        max_candidates=max_candidates,
        max_iters=max_iters,
        window=window,
        brute_force_max=brute_force_max,
        max_full_domain_pools=max_full_domain_pools,
        max_enumerated_candidates=max_enumerated_candidates,
    )
    components = _build_bounded_workaround_components(pools, params=params)
    return _bounded_workaround_packet_from_components(components)


def _bounded_advisory_failure_packet(
    workaround_packet: ExactOutManyPoolBoundedWorkaroundPacket,
    *,
    error: str,
) -> ExactOutManyPoolBoundedAdvisoryQuotePacket:
    return ExactOutManyPoolBoundedAdvisoryQuotePacket(
        packet_ok=False,
        advisory_quote=None,
        quote_source=None,
        repaired_advisory_available=bool(workaround_packet.repaired_full_domain_packet.packet_ok),
        quote_matches_runtime=False,
        quote_matches_repaired_advisory=False,
        error=error,
        workaround_packet=workaround_packet,
    )


@dataclass(frozen=True)
class _BoundedAdvisorySuccessDecision:
    advisory_quote: SplitManyPoolsExactOutQuote
    quote_source: str
    repaired_advisory_available: bool
    quote_matches_runtime: bool
    quote_matches_repaired_advisory: bool


def _bounded_advisory_success_decision(
    workaround_packet: ExactOutManyPoolBoundedWorkaroundPacket,
) -> _BoundedAdvisorySuccessDecision:
    runtime_quote = workaround_packet.oracle_contract.audit.runtime_quote
    repaired_full_domain_packet = workaround_packet.repaired_full_domain_packet
    repaired_quote = repaired_full_domain_packet.repaired_quote
    repaired_available = bool(repaired_full_domain_packet.packet_ok and repaired_quote is not None)
    use_repaired = bool(repaired_available and not workaround_packet.runtime_matches_repaired_advisory)
    advisory_quote = repaired_quote if use_repaired else runtime_quote
    quote_source = "repaired_bounded_advisory" if use_repaired else "selected_domain_runtime"
    return _BoundedAdvisorySuccessDecision(
        advisory_quote=advisory_quote,
        quote_source=quote_source,
        repaired_advisory_available=bool(repaired_available),
        quote_matches_runtime=bool(advisory_quote == runtime_quote),
        quote_matches_repaired_advisory=bool(repaired_quote is not None and advisory_quote == repaired_quote),
    )


def _bounded_advisory_success_packet(
    workaround_packet: ExactOutManyPoolBoundedWorkaroundPacket,
) -> ExactOutManyPoolBoundedAdvisoryQuotePacket:
    decision = _bounded_advisory_success_decision(workaround_packet)
    return ExactOutManyPoolBoundedAdvisoryQuotePacket(
        packet_ok=True,
        advisory_quote=decision.advisory_quote,
        quote_source=decision.quote_source,
        repaired_advisory_available=bool(decision.repaired_advisory_available),
        quote_matches_runtime=bool(decision.quote_matches_runtime),
        quote_matches_repaired_advisory=bool(decision.quote_matches_repaired_advisory),
        error=None,
        workaround_packet=workaround_packet,
    )


def build_exact_out_many_pool_bounded_advisory_quote_packet(
    pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int = 3,
    max_candidate_pools: int = 5,
    max_candidates: int = 12,
    max_iters: int = 4096,
    window: int = 64,
    brute_force_max: int = 512,
    max_full_domain_pools: int = 8,
    max_enumerated_candidates: int = 20_000,
) -> ExactOutManyPoolBoundedAdvisoryQuotePacket:
    amount_out_total_i = _require_amount_out_total_int(amount_out_total)
    params = _ExactOutManyPoolRuntimeParams(
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=amount_out_total_i,
        max_legs=max_legs,
        max_candidate_pools=max_candidate_pools,
        max_candidates=max_candidates,
        max_iters=max_iters,
        window=window,
        brute_force_max=brute_force_max,
        max_full_domain_pools=max_full_domain_pools,
        max_enumerated_candidates=max_enumerated_candidates,
    )
    components = _build_bounded_workaround_components(pools, params=params)
    workaround_packet = _bounded_workaround_packet_from_components(components)
    if not workaround_packet.oracle_contract.audit.runtime_matches_canonical:
        return _bounded_advisory_failure_packet(
            workaround_packet,
            error=EXACT_OUT_MANY_POOL_GUARD_MISMATCH_ERROR,
        )
    if not workaround_packet.runtime_quotes_agree:
        return _bounded_advisory_failure_packet(
            workaround_packet,
            error=EXACT_OUT_MANY_POOL_RUNTIME_QUOTE_INCONSISTENCY_ERROR,
        )
    return _bounded_advisory_success_packet(workaround_packet)


def quote_exact_out_many_pool_bounded_advisory(
    pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int = 3,
    max_candidate_pools: int = 5,
    max_candidates: int = 12,
    max_iters: int = 4096,
    window: int = 64,
    brute_force_max: int = 512,
    max_full_domain_pools: int = 8,
    max_enumerated_candidates: int = 20_000,
) -> tuple[SplitManyPoolsExactOutQuote | None, str | None, ExactOutManyPoolBoundedAdvisoryQuotePacket]:
    amount_out_total_i = _require_amount_out_total_int(amount_out_total)
    (
        max_legs_i,
        max_candidate_pools_i,
        max_candidates_i,
        max_iters_i,
        window_i,
        brute_force_max_i,
        max_full_domain_pools_i,
        max_enumerated_candidates_i,
    ) = _require_runtime_control_values(
        max_legs=max_legs,
        max_candidate_pools=max_candidate_pools,
        max_candidates=max_candidates,
        max_iters=max_iters,
        window=window,
        brute_force_max=brute_force_max,
        max_full_domain_pools=max_full_domain_pools,
        max_enumerated_candidates=max_enumerated_candidates,
    )
    packet = build_exact_out_many_pool_bounded_advisory_quote_packet(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=amount_out_total_i,
        max_legs=max_legs_i,
        max_candidate_pools=max_candidate_pools_i,
        max_candidates=max_candidates_i,
        max_iters=max_iters_i,
        window=window_i,
        brute_force_max=brute_force_max_i,
        max_full_domain_pools=max_full_domain_pools_i,
        max_enumerated_candidates=max_enumerated_candidates_i,
    )
    if packet.packet_ok:
        return packet.advisory_quote, None, packet
    return None, str(packet.error or EXACT_OUT_MANY_POOL_GUARD_MISMATCH_ERROR), packet


def quote_exact_out_many_pool_default(
    pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int = 3,
    max_candidate_pools: int = 5,
    max_candidates: int = 12,
    max_iters: int = 4096,
    window: int = 64,
    brute_force_max: int = 512,
    max_full_domain_pools: int = 8,
    max_enumerated_candidates: int = 20_000,
) -> tuple[SplitManyPoolsExactOutQuote | None, str | None, ExactOutManyPoolCertifiedAdvisoryPacket]:
    amount_out_total_i = _require_amount_out_total_int(amount_out_total)
    (
        max_legs_i,
        max_candidate_pools_i,
        max_candidates_i,
        max_iters_i,
        window_i,
        brute_force_max_i,
        max_full_domain_pools_i,
        max_enumerated_candidates_i,
    ) = _require_runtime_control_values(
        max_legs=max_legs,
        max_candidate_pools=max_candidate_pools,
        max_candidates=max_candidates,
        max_iters=max_iters,
        window=window,
        brute_force_max=brute_force_max,
        max_full_domain_pools=max_full_domain_pools,
        max_enumerated_candidates=max_enumerated_candidates,
    )
    return quote_exact_out_many_pool_certified_advisory(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=amount_out_total_i,
        max_legs=max_legs_i,
        max_candidate_pools=max_candidate_pools_i,
        max_candidates=max_candidates_i,
        max_iters=max_iters_i,
        window=window_i,
        brute_force_max=brute_force_max_i,
        max_full_domain_pools=max_full_domain_pools_i,
        max_enumerated_candidates=max_enumerated_candidates_i,
    )


def build_exact_out_many_pool_default_packet(
    pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int = 3,
    max_candidate_pools: int = 5,
    max_candidates: int = 12,
    max_iters: int = 4096,
    window: int = 64,
    brute_force_max: int = 512,
    max_full_domain_pools: int = 8,
    max_enumerated_candidates: int = 20_000,
) -> ExactOutManyPoolCertifiedAdvisoryPacket:
    amount_out_total_i = _require_amount_out_total_int(amount_out_total)
    (
        max_legs_i,
        max_candidate_pools_i,
        max_candidates_i,
        max_iters_i,
        window_i,
        brute_force_max_i,
        max_full_domain_pools_i,
        max_enumerated_candidates_i,
    ) = _require_runtime_control_values(
        max_legs=max_legs,
        max_candidate_pools=max_candidate_pools,
        max_candidates=max_candidates,
        max_iters=max_iters,
        window=window,
        brute_force_max=brute_force_max,
        max_full_domain_pools=max_full_domain_pools,
        max_enumerated_candidates=max_enumerated_candidates,
    )
    return build_exact_out_many_pool_certified_advisory_packet(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=amount_out_total_i,
        max_legs=max_legs_i,
        max_candidate_pools=max_candidate_pools_i,
        max_candidates=max_candidates_i,
        max_iters=max_iters_i,
        window=window_i,
        brute_force_max=brute_force_max_i,
        max_full_domain_pools=max_full_domain_pools_i,
        max_enumerated_candidates=max_enumerated_candidates_i,
    )


@dataclass(frozen=True)
class _AuditedBoundsBuildParams:
    asset_in: str
    asset_out: str
    amount_out_total: int
    max_legs: int
    max_candidate_pools: int
    max_candidates: int
    max_iters: int
    window: int
    brute_force_max: int
    max_full_domain_pools: int
    max_enumerated_candidates: int

    def __post_init__(self) -> None:
        _require_control_fields(
            (
                ("amount_out_total", self.amount_out_total),
                ("max_legs", self.max_legs),
                ("max_candidate_pools", self.max_candidate_pools),
                ("max_candidates", self.max_candidates),
                ("max_iters", self.max_iters),
                ("window", self.window),
                ("brute_force_max", self.brute_force_max),
                ("max_full_domain_pools", self.max_full_domain_pools),
                ("max_enumerated_candidates", self.max_enumerated_candidates),
            )
        )

    @property
    def domain_bounds(self) -> tuple[int, int, int]:
        return (
            int(self.max_legs),
            int(self.max_candidate_pools),
            int(self.max_enumerated_candidates),
        )

    @property
    def runtime_bounds(self) -> tuple[int, int, int, int, int, int, int, int]:
        return (
            int(self.max_legs),
            int(self.max_candidate_pools),
            int(self.max_candidates),
            int(self.max_iters),
            int(self.window),
            int(self.brute_force_max),
            int(self.max_full_domain_pools),
            int(self.max_enumerated_candidates),
        )

    @property
    def repaired_packet_bounds(self) -> tuple[int, int, int, int]:
        return (
            int(self.max_candidates),
            int(self.max_iters),
            int(self.window),
            int(self.brute_force_max),
        )

    @property
    def repaired_contract_bounds(self) -> tuple[int, int, int, int]:
        return (
            int(self.max_legs),
            int(self.max_candidate_pools),
            int(self.max_full_domain_pools),
            int(self.max_enumerated_candidates),
        )


@dataclass(frozen=True)
class _AuditedBoundsFlags:
    selected_domain_budget_respected: bool
    repaired_selection_budget_respected: bool
    full_domain_pool_budget_respected: bool
    full_domain_candidate_budget_respected: bool
    budget_parameters_bound: bool
    failure_path_explicit: bool
    success_path_replayable: bool

    @property
    def contract_ok(self) -> bool:
        return (
            self.selected_domain_budget_respected
            and self.repaired_selection_budget_respected
            and self.full_domain_pool_budget_respected
            and self.full_domain_candidate_budget_respected
            and self.budget_parameters_bound
            and self.failure_path_explicit
            and self.success_path_replayable
        )


def _domain_contract_budget_tuple(domain_contract: Any) -> tuple[int, int, int]:
    return (
        int(domain_contract.max_legs),
        int(domain_contract.max_candidate_pools),
        int(domain_contract.max_enumerated_candidates),
    )


def _runtime_contract_budget_tuple(runtime_contract: Any) -> tuple[int, int, int, int, int, int, int, int]:
    return (
        int(runtime_contract.max_legs),
        int(runtime_contract.max_candidate_pools),
        int(runtime_contract.max_candidates),
        int(runtime_contract.max_iters),
        int(runtime_contract.window),
        int(runtime_contract.brute_force_max),
        int(runtime_contract.max_full_domain_pools),
        int(runtime_contract.max_enumerated_candidates),
    )


def _repaired_packet_budget_tuple(repaired_packet: Any) -> tuple[int, int, int, int]:
    return (
        int(repaired_packet.max_candidates),
        int(repaired_packet.max_iters),
        int(repaired_packet.window),
        int(repaired_packet.brute_force_max),
    )


def _repaired_contract_budget_tuple(repaired_contract: Any) -> tuple[int, int, int, int]:
    return (
        int(repaired_contract.max_legs),
        int(repaired_contract.max_candidate_pools),
        int(repaired_contract.max_full_domain_pools),
        int(repaired_contract.max_enumerated_candidates),
    )


def _exact_out_many_pool_budget_parameters_bound(
    packet: ExactOutManyPoolCertifiedAdvisoryPacket,
    *,
    params: _AuditedBoundsBuildParams,
) -> bool:
    domain_contract = packet.certified_packet.domain_contract
    guarded_contract = packet.certified_packet.guarded_packet.contract
    selected_domain_contract = packet.repaired_key_cover_packet.selected_domain_contract
    advisory_packet = packet.advisory_packet
    oracle_contract = advisory_packet.workaround_packet.oracle_contract
    repaired_packet = advisory_packet.workaround_packet.repaired_packet
    repaired_contract = repaired_packet.repaired_contract
    return (
        _domain_contract_budget_tuple(domain_contract) == params.domain_bounds
        and _runtime_contract_budget_tuple(guarded_contract) == params.runtime_bounds
        and _runtime_contract_budget_tuple(selected_domain_contract) == params.runtime_bounds
        and _runtime_contract_budget_tuple(oracle_contract) == params.runtime_bounds
        and _repaired_packet_budget_tuple(repaired_packet) == params.repaired_packet_bounds
        and _repaired_contract_budget_tuple(repaired_contract) == params.repaired_contract_bounds
    )


def _build_certified_advisory_packet_for_audited_bounds(
    pools: Sequence[PoolState],
    *,
    params: _AuditedBoundsBuildParams,
) -> ExactOutManyPoolCertifiedAdvisoryPacket:
    return build_exact_out_many_pool_certified_advisory_packet(
        pools,
        asset_in=params.asset_in,
        asset_out=params.asset_out,
        amount_out_total=int(params.amount_out_total),
        max_legs=int(params.max_legs),
        max_candidate_pools=int(params.max_candidate_pools),
        max_candidates=int(params.max_candidates),
        max_iters=int(params.max_iters),
        window=int(params.window),
        brute_force_max=int(params.brute_force_max),
        max_full_domain_pools=int(params.max_full_domain_pools),
        max_enumerated_candidates=int(params.max_enumerated_candidates),
    )


def _audited_bounds_failure_path_explicit(packet: ExactOutManyPoolCertifiedAdvisoryPacket) -> bool:
    return bool(
        packet.packet_ok
        or not packet.certified_packet.packet_ok
        or (not packet.advisory_packet.packet_ok and packet.advisory_packet.error is not None)
        or not packet.selected_runtime_quotes_agree
    )


def _audited_bounds_success_path_replayable(packet: ExactOutManyPoolCertifiedAdvisoryPacket) -> bool:
    return bool(
        not packet.packet_ok
        or (
            packet.advisory_packet.advisory_quote is not None
            and packet.advisory_packet.quote_source is not None
            and packet.advisory_packet.error is None
        )
    )


def _audited_bounds_flags(
    packet: ExactOutManyPoolCertifiedAdvisoryPacket,
    *,
    params: _AuditedBoundsBuildParams,
) -> _AuditedBoundsFlags:
    domain_contract = packet.certified_packet.domain_contract
    repaired_packet = packet.advisory_packet.workaround_packet.repaired_packet
    repaired_contract = repaired_packet.repaired_contract
    full_domain_packet = packet.advisory_packet.workaround_packet.repaired_full_domain_packet
    return _AuditedBoundsFlags(
        selected_domain_budget_respected=bool(
            domain_contract.audit_pool_ids_within_budget
            and domain_contract.candidate_count_within_budget
        ),
        repaired_selection_budget_respected=bool(repaired_contract.repaired_selected_pool_ids_within_budget),
        full_domain_pool_budget_respected=bool(
            len(full_domain_packet.full_domain_feasible_pool_ids) <= int(params.max_full_domain_pools)
        ),
        full_domain_candidate_budget_respected=bool(
            int(full_domain_packet.full_domain_candidate_count) <= int(params.max_enumerated_candidates)
        ),
        budget_parameters_bound=_exact_out_many_pool_budget_parameters_bound(packet, params=params),
        failure_path_explicit=_audited_bounds_failure_path_explicit(packet),
        success_path_replayable=_audited_bounds_success_path_replayable(packet),
    )


def _audited_bounds_contract_from_flags(
    pools: Sequence[PoolState],
    packet: ExactOutManyPoolCertifiedAdvisoryPacket,
    *,
    params: _AuditedBoundsBuildParams,
    flags: _AuditedBoundsFlags,
) -> ExactOutManyPoolAuditedBoundsContract:
    return ExactOutManyPoolAuditedBoundsContract(
        asset_in=str(params.asset_in),
        asset_out=str(params.asset_out),
        amount_out_total=int(params.amount_out_total),
        max_legs=int(params.max_legs),
        max_candidate_pools=int(params.max_candidate_pools),
        max_candidates=int(params.max_candidates),
        max_iters=int(params.max_iters),
        window=int(params.window),
        brute_force_max=int(params.brute_force_max),
        max_full_domain_pools=int(params.max_full_domain_pools),
        max_enumerated_candidates=int(params.max_enumerated_candidates),
        pool_snapshots=tuple(_pool_to_dict(pool) for pool in pools),
        certified_advisory_packet=packet,
        selected_domain_budget_respected=bool(flags.selected_domain_budget_respected),
        repaired_selection_budget_respected=bool(flags.repaired_selection_budget_respected),
        full_domain_pool_budget_respected=bool(flags.full_domain_pool_budget_respected),
        full_domain_candidate_budget_respected=bool(flags.full_domain_candidate_budget_respected),
        budget_parameters_bound=bool(flags.budget_parameters_bound),
        failure_path_explicit=bool(flags.failure_path_explicit),
        success_path_replayable=bool(flags.success_path_replayable),
        contract_ok=bool(flags.contract_ok),
    )


def build_exact_out_many_pool_audited_bounds_contract(
    pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int = 3,
    max_candidate_pools: int = 5,
    max_candidates: int = 12,
    max_iters: int = 4096,
    window: int = 64,
    brute_force_max: int = 512,
    max_full_domain_pools: int = 8,
    max_enumerated_candidates: int = 20_000,
) -> ExactOutManyPoolAuditedBoundsContract:
    amount_out_total_i = _require_amount_out_total_int(amount_out_total)
    params = _AuditedBoundsBuildParams(
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=amount_out_total_i,
        max_legs=max_legs,
        max_candidate_pools=max_candidate_pools,
        max_candidates=max_candidates,
        max_iters=max_iters,
        window=window,
        brute_force_max=brute_force_max,
        max_full_domain_pools=max_full_domain_pools,
        max_enumerated_candidates=max_enumerated_candidates,
    )
    packet = _build_certified_advisory_packet_for_audited_bounds(pools, params=params)
    flags = _audited_bounds_flags(packet, params=params)
    return _audited_bounds_contract_from_flags(pools, packet, params=params, flags=flags)


def _exact_out_many_pool_certified_advisory_packet_error(
    packet: ExactOutManyPoolCertifiedAdvisoryPacket,
) -> str | None:
    if packet.packet_ok:
        return None
    if not packet.certified_packet.packet_ok:
        return EXACT_OUT_MANY_POOL_GUARD_MISMATCH_ERROR
    if not packet.advisory_packet.packet_ok:
        return str(packet.advisory_packet.error or EXACT_OUT_MANY_POOL_GUARD_MISMATCH_ERROR)
    if not packet.selected_runtime_quotes_agree:
        return EXACT_OUT_MANY_POOL_RUNTIME_QUOTE_INCONSISTENCY_ERROR
    return EXACT_OUT_MANY_POOL_GUARD_MISMATCH_ERROR


@dataclass(frozen=True)
class _AdaptiveLivenessPathStatus:
    repaired_full_domain_packet: ExactOutManyPoolRepairedFullDomainCertifiedPacket
    cheap_path_attempted: bool
    cheap_path_success: bool
    fallback_required: bool
    fallback_attempted: bool
    fallback_available: bool
    fallback_success: bool
    returned_success: bool
    explicit_failure: bool


@dataclass(frozen=True)
class _AdaptiveLivenessEffectiveResult:
    effective_quote_source: str | None
    effective_quote: SplitManyPoolsExactOutQuote | None
    failure_reason: str | None
    nested_error: str | None


def _adaptive_liveness_path_status(
    default_packet: ExactOutManyPoolCertifiedAdvisoryPacket,
) -> _AdaptiveLivenessPathStatus:
    repaired_full_domain_packet = default_packet.advisory_packet.workaround_packet.repaired_full_domain_packet
    cheap_path_success = bool(default_packet.packet_ok and default_packet.advisory_packet.advisory_quote is not None)
    fallback_required = not cheap_path_success
    fallback_available = bool(
        repaired_full_domain_packet.packet_ok and repaired_full_domain_packet.repaired_quote is not None
    )
    fallback_success = bool(fallback_required and fallback_available)
    returned_success = bool(cheap_path_success or fallback_success)
    return _AdaptiveLivenessPathStatus(
        repaired_full_domain_packet=repaired_full_domain_packet,
        cheap_path_attempted=True,
        cheap_path_success=cheap_path_success,
        fallback_required=fallback_required,
        fallback_attempted=fallback_required,
        fallback_available=fallback_available,
        fallback_success=fallback_success,
        returned_success=returned_success,
        explicit_failure=not returned_success,
    )


def _adaptive_liveness_failure_reason(
    *,
    audited_bounds_contract: ExactOutManyPoolAuditedBoundsContract,
    default_packet: ExactOutManyPoolCertifiedAdvisoryPacket,
    repaired_full_domain_packet: ExactOutManyPoolRepairedFullDomainCertifiedPacket,
) -> str:
    if not audited_bounds_contract.contract_ok:
        return EXACT_OUT_MANY_POOL_ADAPTIVE_FAILURE_AUDITED_BOUNDS_CONTRACT_NOT_OK
    if not default_packet.packet_ok:
        return EXACT_OUT_MANY_POOL_ADAPTIVE_FAILURE_DEFAULT_PACKET_NOT_OK
    if not repaired_full_domain_packet.packet_ok:
        return EXACT_OUT_MANY_POOL_ADAPTIVE_FAILURE_REPAIRED_FULL_DOMAIN_PACKET_NOT_OK
    return EXACT_OUT_MANY_POOL_ADAPTIVE_FAILURE_REPLAYABLE_QUOTE_MISSING


def _adaptive_liveness_effective_result(
    *,
    audited_bounds_contract: ExactOutManyPoolAuditedBoundsContract,
    status: _AdaptiveLivenessPathStatus,
) -> _AdaptiveLivenessEffectiveResult:
    default_packet = audited_bounds_contract.certified_advisory_packet
    if status.cheap_path_success:
        return _AdaptiveLivenessEffectiveResult(
            effective_quote_source="default_certified_advisory",
            effective_quote=default_packet.advisory_packet.advisory_quote,
            failure_reason=None,
            nested_error=None,
        )
    if status.fallback_success:
        return _AdaptiveLivenessEffectiveResult(
            effective_quote_source="repaired_full_domain",
            effective_quote=status.repaired_full_domain_packet.repaired_quote,
            failure_reason=None,
            nested_error=None,
        )

    default_error = _exact_out_many_pool_certified_advisory_packet_error(default_packet)
    fallback_error = None if status.fallback_available else status.repaired_full_domain_packet.error
    failure_reason = _adaptive_liveness_failure_reason(
        audited_bounds_contract=audited_bounds_contract,
        default_packet=default_packet,
        repaired_full_domain_packet=status.repaired_full_domain_packet,
    )
    return _AdaptiveLivenessEffectiveResult(
        effective_quote_source=None,
        effective_quote=None,
        failure_reason=failure_reason,
        nested_error=str(fallback_error or default_error or failure_reason),
    )


def _adaptive_liveness_packet_ok(
    *,
    audited_bounds_contract: ExactOutManyPoolAuditedBoundsContract,
    status: _AdaptiveLivenessPathStatus,
    result: _AdaptiveLivenessEffectiveResult,
) -> bool:
    return bool(
        status.repaired_full_domain_packet
        == audited_bounds_contract.certified_advisory_packet.advisory_packet.workaround_packet.repaired_full_domain_packet
        and status.cheap_path_attempted
        and status.fallback_required == (not status.cheap_path_success)
        and status.fallback_attempted == status.fallback_required
        and status.fallback_success == (status.fallback_attempted and status.fallback_available)
        and status.returned_success == (status.cheap_path_success or status.fallback_success)
        and status.explicit_failure == (not status.returned_success)
        and (result.failure_reason is not None) == status.explicit_failure
        and (
            (
                status.returned_success
                and result.effective_quote_source is not None
                and result.effective_quote is not None
                and result.failure_reason is None
            )
            or (
                status.explicit_failure
                and result.effective_quote_source is None
                and result.effective_quote is None
                and result.failure_reason is not None
            )
        )
    )


def _adaptive_liveness_packet_from_audited_bounds(
    audited_bounds_contract: ExactOutManyPoolAuditedBoundsContract,
) -> ExactOutManyPoolAdaptiveLivenessPacket:
    status = _adaptive_liveness_path_status(audited_bounds_contract.certified_advisory_packet)
    result = _adaptive_liveness_effective_result(
        audited_bounds_contract=audited_bounds_contract,
        status=status,
    )
    no_spurious_failure = bool((not status.explicit_failure) or (not status.fallback_available))
    packet_ok = _adaptive_liveness_packet_ok(
        audited_bounds_contract=audited_bounds_contract,
        status=status,
        result=result,
    )
    liveness_ok = bool(packet_ok and audited_bounds_contract.contract_ok and no_spurious_failure)
    return ExactOutManyPoolAdaptiveLivenessPacket(
        audited_bounds_contract=audited_bounds_contract,
        repaired_full_domain_packet=status.repaired_full_domain_packet,
        cheap_path_attempted=status.cheap_path_attempted,
        cheap_path_success=status.cheap_path_success,
        fallback_required=status.fallback_required,
        fallback_attempted=status.fallback_attempted,
        fallback_available=status.fallback_available,
        fallback_success=status.fallback_success,
        returned_success=status.returned_success,
        explicit_failure=status.explicit_failure,
        failure_reason_present=result.failure_reason is not None,
        no_spurious_failure=no_spurious_failure,
        effective_quote_source=result.effective_quote_source,
        effective_quote=result.effective_quote,
        failure_reason=result.failure_reason,
        nested_error=result.nested_error,
        packet_ok=packet_ok,
        liveness_ok=liveness_ok,
    )


def build_exact_out_many_pool_adaptive_liveness_packet(
    pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int = 3,
    max_candidate_pools: int = 5,
    max_candidates: int = 12,
    max_iters: int = 4096,
    window: int = 64,
    brute_force_max: int = 512,
    max_full_domain_pools: int = 8,
    max_enumerated_candidates: int = 20_000,
) -> ExactOutManyPoolAdaptiveLivenessPacket:
    amount_out_total_i = _require_amount_out_total_int(amount_out_total)
    (
        max_legs_i,
        max_candidate_pools_i,
        max_candidates_i,
        max_iters_i,
        window_i,
        brute_force_max_i,
        max_full_domain_pools_i,
        max_enumerated_candidates_i,
    ) = _require_runtime_control_values(
        max_legs=max_legs,
        max_candidate_pools=max_candidate_pools,
        max_candidates=max_candidates,
        max_iters=max_iters,
        window=window,
        brute_force_max=brute_force_max,
        max_full_domain_pools=max_full_domain_pools,
        max_enumerated_candidates=max_enumerated_candidates,
    )
    audited_bounds_contract = build_exact_out_many_pool_audited_bounds_contract(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=amount_out_total_i,
        max_legs=max_legs_i,
        max_candidate_pools=max_candidate_pools_i,
        max_candidates=max_candidates_i,
        max_iters=max_iters_i,
        window=window_i,
        brute_force_max=brute_force_max_i,
        max_full_domain_pools=max_full_domain_pools_i,
        max_enumerated_candidates=max_enumerated_candidates_i,
    )
    return _adaptive_liveness_packet_from_audited_bounds(audited_bounds_contract)


def quote_exact_out_many_pool_adaptive(
    pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int = 3,
    max_candidate_pools: int = 5,
    max_candidates: int = 12,
    max_iters: int = 4096,
    window: int = 64,
    brute_force_max: int = 512,
    max_full_domain_pools: int = 8,
    max_enumerated_candidates: int = 20_000,
) -> tuple[SplitManyPoolsExactOutQuote | None, str | None, ExactOutManyPoolAdaptiveLivenessPacket]:
    amount_out_total_i = _require_amount_out_total_int(amount_out_total)
    (
        max_legs_i,
        max_candidate_pools_i,
        max_candidates_i,
        max_iters_i,
        window_i,
        brute_force_max_i,
        max_full_domain_pools_i,
        max_enumerated_candidates_i,
    ) = _require_runtime_control_values(
        max_legs=max_legs,
        max_candidate_pools=max_candidate_pools,
        max_candidates=max_candidates,
        max_iters=max_iters,
        window=window,
        brute_force_max=brute_force_max,
        max_full_domain_pools=max_full_domain_pools,
        max_enumerated_candidates=max_enumerated_candidates,
    )
    packet = build_exact_out_many_pool_adaptive_liveness_packet(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=amount_out_total_i,
        max_legs=max_legs_i,
        max_candidate_pools=max_candidate_pools_i,
        max_candidates=max_candidates_i,
        max_iters=max_iters_i,
        window=window_i,
        brute_force_max=brute_force_max_i,
        max_full_domain_pools=max_full_domain_pools_i,
        max_enumerated_candidates=max_enumerated_candidates_i,
    )
    if packet.returned_success:
        return packet.effective_quote, None, packet
    return None, str(packet.failure_reason or packet.nested_error or EXACT_OUT_MANY_POOL_ADAPTIVE_FAILURE_REPLAYABLE_QUOTE_MISSING), packet


def verify_exact_out_many_pool_default_packet_payload(payload: object) -> tuple[bool, str | None]:
    return verify_exact_out_many_pool_certified_advisory_packet_payload(payload)


def verify_exact_out_many_pool_audited_bounds_contract_payload(payload: object) -> tuple[bool, str | None]:
    if not isinstance(payload, dict):
        return False, "audited bounds contract payload must be a dict"
    if payload.get("schema") != EXACT_OUT_MANY_POOL_AUDITED_BOUNDS_CONTRACT_SCHEMA:
        return False, "unsupported audited bounds contract schema"
    try:
        pools_payload = payload["pool_snapshots"]
        if not isinstance(pools_payload, list) or not pools_payload:
            return False, "pool_snapshots must be a non-empty list"
        pools = tuple(_pool_from_dict(pool_payload) for pool_payload in pools_payload)
        expected = build_exact_out_many_pool_audited_bounds_contract(
            pools,
            asset_in=str(payload["asset_in"]),
            asset_out=str(payload["asset_out"]),
            amount_out_total=_require_payload_int(payload, "amount_out_total"),
            max_legs=_require_payload_int(payload, "max_legs"),
            max_candidate_pools=_require_payload_int(payload, "max_candidate_pools"),
            max_candidates=_require_payload_int(payload, "max_candidates"),
            max_iters=_require_payload_int(payload, "max_iters"),
            window=_require_payload_int(payload, "window"),
            brute_force_max=_require_payload_int(payload, "brute_force_max"),
            max_full_domain_pools=_require_payload_int(payload, "max_full_domain_pools"),
            max_enumerated_candidates=_require_payload_int(payload, "max_enumerated_candidates"),
        )
    except (KeyError, TypeError, ValueError) as exc:
        return False, str(exc)
    if payload != expected.to_dict():
        return False, "audited bounds contract payload mismatch"
    return True, None


def verify_exact_out_many_pool_adaptive_liveness_packet_payload(payload: object) -> tuple[bool, str | None]:
    if not isinstance(payload, dict):
        return False, "adaptive liveness packet payload must be a dict"
    if payload.get("schema") != EXACT_OUT_MANY_POOL_ADAPTIVE_LIVENESS_PACKET_SCHEMA:
        return False, "unsupported adaptive liveness packet schema"
    try:
        contract_payload = payload["audited_bounds_contract"]
        if not isinstance(contract_payload, dict):
            return False, "audited_bounds_contract must be a dict"
        pools_payload = contract_payload["pool_snapshots"]
        if not isinstance(pools_payload, list) or not pools_payload:
            return False, "pool_snapshots must be a non-empty list"
        pools = tuple(_pool_from_dict(pool_payload) for pool_payload in pools_payload)
        expected = build_exact_out_many_pool_adaptive_liveness_packet(
            pools,
            asset_in=str(contract_payload["asset_in"]),
            asset_out=str(contract_payload["asset_out"]),
            amount_out_total=_require_payload_int(contract_payload, "amount_out_total"),
            max_legs=_require_payload_int(contract_payload, "max_legs"),
            max_candidate_pools=_require_payload_int(contract_payload, "max_candidate_pools"),
            max_candidates=_require_payload_int(contract_payload, "max_candidates"),
            max_iters=_require_payload_int(contract_payload, "max_iters"),
            window=_require_payload_int(contract_payload, "window"),
            brute_force_max=_require_payload_int(contract_payload, "brute_force_max"),
            max_full_domain_pools=_require_payload_int(contract_payload, "max_full_domain_pools"),
            max_enumerated_candidates=_require_payload_int(contract_payload, "max_enumerated_candidates"),
        )
    except (KeyError, TypeError, ValueError) as exc:
        return False, str(exc)
    if payload != expected.to_dict():
        return False, "adaptive liveness packet payload mismatch"
    return True, None


def verify_exact_out_many_pool_candidate_domain_contract_payload(payload: object) -> tuple[bool, str | None]:
    if not isinstance(payload, dict):
        return False, "candidate domain contract payload must be a dict"
    if payload.get("schema") != EXACT_OUT_MANY_POOL_CANDIDATE_DOMAIN_CONTRACT_SCHEMA:
        return False, "unsupported candidate domain contract schema"
    try:
        pools_payload = payload["pool_snapshots"]
        if not isinstance(pools_payload, list) or not pools_payload:
            return False, "pool_snapshots must be a non-empty list"
        pools = tuple(_pool_from_dict(pool_payload) for pool_payload in pools_payload)
        expected = build_exact_out_many_pool_candidate_domain_contract(
            pools,
            asset_in=str(payload["asset_in"]),
            asset_out=str(payload["asset_out"]),
            amount_out_total=_require_payload_int(payload, "amount_out_total"),
            max_legs=_require_payload_int(payload, "max_legs"),
            max_candidate_pools=_require_payload_int(payload, "max_candidate_pools"),
            max_enumerated_candidates=_require_payload_int(payload, "max_enumerated_candidates"),
        )
    except (KeyError, TypeError, ValueError) as exc:
        return False, str(exc)
    if payload != expected.to_dict():
        return False, "candidate domain contract payload mismatch"
    return True, None


def guard_exact_out_many_pool_runtime_canonicality(
    pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int = 3,
    max_candidate_pools: int = 5,
    max_candidates: int = 12,
    max_iters: int = 4096,
    window: int = 64,
    brute_force_max: int = 512,
    max_full_domain_pools: int = 8,
    max_enumerated_candidates: int = 20_000,
) -> tuple[bool, str | None, ExactOutManyPoolOracleContract]:
    amount_out_total_i = _require_amount_out_total_int(amount_out_total)
    (
        max_legs_i,
        max_candidate_pools_i,
        max_candidates_i,
        max_iters_i,
        window_i,
        brute_force_max_i,
        max_full_domain_pools_i,
        max_enumerated_candidates_i,
    ) = _require_runtime_control_values(
        max_legs=max_legs,
        max_candidate_pools=max_candidate_pools,
        max_candidates=max_candidates,
        max_iters=max_iters,
        window=window,
        brute_force_max=brute_force_max,
        max_full_domain_pools=max_full_domain_pools,
        max_enumerated_candidates=max_enumerated_candidates,
    )
    contract = build_exact_out_many_pool_oracle_contract(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=amount_out_total_i,
        max_legs=max_legs_i,
        max_candidate_pools=max_candidate_pools_i,
        max_candidates=max_candidates_i,
        max_iters=max_iters_i,
        window=window_i,
        brute_force_max=brute_force_max_i,
        max_full_domain_pools=max_full_domain_pools_i,
        max_enumerated_candidates=max_enumerated_candidates_i,
    )
    if contract.contract_ok:
        return True, None, contract
    if contract.audit.runtime_matches_canonical:
        return False, EXACT_OUT_MANY_POOL_PROJECTION_COVER_ERROR, contract
    return False, EXACT_OUT_MANY_POOL_GUARD_MISMATCH_ERROR, contract


def quote_exact_out_many_pool_guarded(
    pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int = 3,
    max_candidate_pools: int = 5,
    max_candidates: int = 12,
    max_iters: int = 4096,
    window: int = 64,
    brute_force_max: int = 512,
    max_full_domain_pools: int = 8,
    max_enumerated_candidates: int = 20_000,
) -> tuple[SplitManyPoolsExactOutQuote | None, str | None, ExactOutManyPoolOracleContract]:
    amount_out_total_i = _require_amount_out_total_int(amount_out_total)
    (
        max_legs_i,
        max_candidate_pools_i,
        max_candidates_i,
        max_iters_i,
        window_i,
        brute_force_max_i,
        max_full_domain_pools_i,
        max_enumerated_candidates_i,
    ) = _require_runtime_control_values(
        max_legs=max_legs,
        max_candidate_pools=max_candidate_pools,
        max_candidates=max_candidates,
        max_iters=max_iters,
        window=window,
        brute_force_max=brute_force_max,
        max_full_domain_pools=max_full_domain_pools,
        max_enumerated_candidates=max_enumerated_candidates,
    )
    ok, err, contract = guard_exact_out_many_pool_runtime_canonicality(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=amount_out_total_i,
        max_legs=max_legs_i,
        max_candidate_pools=max_candidate_pools_i,
        max_candidates=max_candidates_i,
        max_iters=max_iters_i,
        window=window_i,
        brute_force_max=brute_force_max_i,
        max_full_domain_pools=max_full_domain_pools_i,
        max_enumerated_candidates=max_enumerated_candidates_i,
    )
    if ok:
        return contract.audit.runtime_quote, None, contract
    return None, str(err or EXACT_OUT_MANY_POOL_GUARD_MISMATCH_ERROR), contract


def build_exact_out_many_pool_guarded_quote_packet(
    pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int = 3,
    max_candidate_pools: int = 5,
    max_candidates: int = 12,
    max_iters: int = 4096,
    window: int = 64,
    brute_force_max: int = 512,
    max_full_domain_pools: int = 8,
    max_enumerated_candidates: int = 20_000,
) -> ExactOutManyPoolGuardedQuotePacket:
    amount_out_total_i = _require_amount_out_total_int(amount_out_total)
    (
        max_legs_i,
        max_candidate_pools_i,
        max_candidates_i,
        max_iters_i,
        window_i,
        brute_force_max_i,
        max_full_domain_pools_i,
        max_enumerated_candidates_i,
    ) = _require_runtime_control_values(
        max_legs=max_legs,
        max_candidate_pools=max_candidate_pools,
        max_candidates=max_candidates,
        max_iters=max_iters,
        window=window,
        brute_force_max=brute_force_max,
        max_full_domain_pools=max_full_domain_pools,
        max_enumerated_candidates=max_enumerated_candidates,
    )
    quote, err, contract = quote_exact_out_many_pool_guarded(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=amount_out_total_i,
        max_legs=max_legs_i,
        max_candidate_pools=max_candidate_pools_i,
        max_candidates=max_candidates_i,
        max_iters=max_iters_i,
        window=window_i,
        brute_force_max=brute_force_max_i,
        max_full_domain_pools=max_full_domain_pools_i,
        max_enumerated_candidates=max_enumerated_candidates_i,
    )
    if quote is None:
        return ExactOutManyPoolGuardedQuotePacket(
            guard_ok=False,
            quote=None,
            error=str(err or EXACT_OUT_MANY_POOL_GUARD_MISMATCH_ERROR),
            contract=contract,
        )
    return ExactOutManyPoolGuardedQuotePacket(
        guard_ok=True,
        quote=quote,
        error=None,
        contract=contract,
    )


def build_exact_out_many_pool_certified_winner_packet(
    pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int = 3,
    max_candidate_pools: int = 5,
    max_candidates: int = 12,
    max_iters: int = 4096,
    window: int = 64,
    brute_force_max: int = 512,
    max_full_domain_pools: int = 8,
    max_enumerated_candidates: int = 20_000,
) -> ExactOutManyPoolCertifiedWinnerPacket:
    amount_out_total_i = _require_amount_out_total_int(amount_out_total)
    (
        max_legs_i,
        max_candidate_pools_i,
        max_candidates_i,
        max_iters_i,
        window_i,
        brute_force_max_i,
        max_full_domain_pools_i,
        max_enumerated_candidates_i,
    ) = _require_runtime_control_values(
        max_legs=max_legs,
        max_candidate_pools=max_candidate_pools,
        max_candidates=max_candidates,
        max_iters=max_iters,
        window=window,
        brute_force_max=brute_force_max,
        max_full_domain_pools=max_full_domain_pools,
        max_enumerated_candidates=max_enumerated_candidates,
    )
    domain_contract = build_exact_out_many_pool_candidate_domain_contract(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=amount_out_total_i,
        max_legs=max_legs_i,
        max_candidate_pools=max_candidate_pools_i,
        max_enumerated_candidates=max_enumerated_candidates_i,
    )
    guarded_packet = build_exact_out_many_pool_guarded_quote_packet(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=amount_out_total_i,
        max_legs=max_legs_i,
        max_candidate_pools=max_candidate_pools_i,
        max_candidates=max_candidates_i,
        max_iters=max_iters_i,
        window=window_i,
        brute_force_max=brute_force_max_i,
        max_full_domain_pools=max_full_domain_pools_i,
        max_enumerated_candidates=max_enumerated_candidates_i,
    )
    gate = check_exact_out_many_pool_certified_winner_packet_gate(
        domain_contract_ok=bool(domain_contract.contract_ok),
        guard_ok=bool(guarded_packet.guard_ok),
    )
    return ExactOutManyPoolCertifiedWinnerPacket(
        domain_contract=domain_contract,
        guarded_packet=guarded_packet,
        packet_ok=bool(gate.ok),
    )


@dataclass(frozen=True)
class _CertifiedAdvisoryComponents:
    certified_packet: ExactOutManyPoolCertifiedWinnerPacket
    advisory_packet: ExactOutManyPoolBoundedAdvisoryQuotePacket
    repaired_key_cover_packet: ExactOutManyPoolRepairedKeyCoverPacket
    repaired_key_cover_interpretation_packet: ExactOutManyPoolRepairedKeyCoverInterpretationPacket

    @property
    def selected_runtime_quotes_agree(self) -> bool:
        return bool(
            self.certified_packet.guarded_packet.contract.audit.runtime_quote
            == self.advisory_packet.workaround_packet.oracle_contract.audit.runtime_quote
        )

    @property
    def packet_ok(self) -> bool:
        return bool(
            self.certified_packet.packet_ok
            and self.advisory_packet.packet_ok
            and self.selected_runtime_quotes_agree
        )


def _certified_winner_packet_for_runtime_params(
    pools: Sequence[PoolState],
    *,
    params: _ExactOutManyPoolRuntimeParams,
) -> ExactOutManyPoolCertifiedWinnerPacket:
    return build_exact_out_many_pool_certified_winner_packet(
        pools,
        asset_in=params.asset_in,
        asset_out=params.asset_out,
        amount_out_total=int(params.amount_out_total),
        max_legs=int(params.max_legs),
        max_candidate_pools=int(params.max_candidate_pools),
        max_candidates=int(params.max_candidates),
        max_iters=int(params.max_iters),
        window=int(params.window),
        brute_force_max=int(params.brute_force_max),
        max_full_domain_pools=int(params.max_full_domain_pools),
        max_enumerated_candidates=int(params.max_enumerated_candidates),
    )


def _bounded_advisory_packet_for_runtime_params(
    pools: Sequence[PoolState],
    *,
    params: _ExactOutManyPoolRuntimeParams,
) -> ExactOutManyPoolBoundedAdvisoryQuotePacket:
    return build_exact_out_many_pool_bounded_advisory_quote_packet(
        pools,
        asset_in=params.asset_in,
        asset_out=params.asset_out,
        amount_out_total=int(params.amount_out_total),
        max_legs=int(params.max_legs),
        max_candidate_pools=int(params.max_candidate_pools),
        max_candidates=int(params.max_candidates),
        max_iters=int(params.max_iters),
        window=int(params.window),
        brute_force_max=int(params.brute_force_max),
        max_full_domain_pools=int(params.max_full_domain_pools),
        max_enumerated_candidates=int(params.max_enumerated_candidates),
    )


def _selected_domain_contract_for_runtime_params(
    pools: Sequence[PoolState],
    *,
    params: _ExactOutManyPoolRuntimeParams,
) -> ExactOutManyPoolRepairedSelectedDomainOracleContract:
    return build_exact_out_many_pool_repaired_selected_domain_oracle_contract(
        pools,
        asset_in=params.asset_in,
        asset_out=params.asset_out,
        amount_out_total=int(params.amount_out_total),
        max_legs=int(params.max_legs),
        max_candidate_pools=int(params.max_candidate_pools),
        max_candidates=int(params.max_candidates),
        max_iters=int(params.max_iters),
        window=int(params.window),
        brute_force_max=int(params.brute_force_max),
        max_full_domain_pools=int(params.max_full_domain_pools),
        max_enumerated_candidates=int(params.max_enumerated_candidates),
    )


def _build_certified_advisory_components(
    pools: Sequence[PoolState],
    *,
    params: _ExactOutManyPoolRuntimeParams,
) -> _CertifiedAdvisoryComponents:
    certified_packet = _certified_winner_packet_for_runtime_params(pools, params=params)
    advisory_packet = _bounded_advisory_packet_for_runtime_params(pools, params=params)
    selected_domain_contract = _selected_domain_contract_for_runtime_params(pools, params=params)
    repaired_key_cover_packet = _build_exact_out_many_pool_repaired_key_cover_packet_from_components(
        selected_domain_contract=selected_domain_contract,
        repaired_full_domain_packet=advisory_packet.workaround_packet.repaired_full_domain_packet,
    )
    interpretation_packet = _build_exact_out_many_pool_repaired_key_cover_interpretation_packet_from_key_cover_packet(
        repaired_key_cover_packet
    )
    return _CertifiedAdvisoryComponents(
        certified_packet=certified_packet,
        advisory_packet=advisory_packet,
        repaired_key_cover_packet=repaired_key_cover_packet,
        repaired_key_cover_interpretation_packet=interpretation_packet,
    )


def _certified_advisory_packet_from_components(
    components: _CertifiedAdvisoryComponents,
) -> ExactOutManyPoolCertifiedAdvisoryPacket:
    return ExactOutManyPoolCertifiedAdvisoryPacket(
        certified_packet=components.certified_packet,
        advisory_packet=components.advisory_packet,
        repaired_key_cover_packet=components.repaired_key_cover_packet,
        repaired_key_cover_interpretation_packet=components.repaired_key_cover_interpretation_packet,
        selected_runtime_quotes_agree=bool(components.selected_runtime_quotes_agree),
        packet_ok=bool(components.packet_ok),
    )


def build_exact_out_many_pool_certified_advisory_packet(
    pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int = 3,
    max_candidate_pools: int = 5,
    max_candidates: int = 12,
    max_iters: int = 4096,
    window: int = 64,
    brute_force_max: int = 512,
    max_full_domain_pools: int = 8,
    max_enumerated_candidates: int = 20_000,
) -> ExactOutManyPoolCertifiedAdvisoryPacket:
    amount_out_total_i = _require_amount_out_total_int(amount_out_total)
    params = _ExactOutManyPoolRuntimeParams(
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=amount_out_total_i,
        max_legs=max_legs,
        max_candidate_pools=max_candidate_pools,
        max_candidates=max_candidates,
        max_iters=max_iters,
        window=window,
        brute_force_max=brute_force_max,
        max_full_domain_pools=max_full_domain_pools,
        max_enumerated_candidates=max_enumerated_candidates,
    )
    components = _build_certified_advisory_components(pools, params=params)
    return _certified_advisory_packet_from_components(components)


def quote_exact_out_many_pool_certified_advisory(
    pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int = 3,
    max_candidate_pools: int = 5,
    max_candidates: int = 12,
    max_iters: int = 4096,
    window: int = 64,
    brute_force_max: int = 512,
    max_full_domain_pools: int = 8,
    max_enumerated_candidates: int = 20_000,
) -> tuple[SplitManyPoolsExactOutQuote | None, str | None, ExactOutManyPoolCertifiedAdvisoryPacket]:
    amount_out_total_i = _require_amount_out_total_int(amount_out_total)
    (
        max_legs_i,
        max_candidate_pools_i,
        max_candidates_i,
        max_iters_i,
        window_i,
        brute_force_max_i,
        max_full_domain_pools_i,
        max_enumerated_candidates_i,
    ) = _require_runtime_control_values(
        max_legs=max_legs,
        max_candidate_pools=max_candidate_pools,
        max_candidates=max_candidates,
        max_iters=max_iters,
        window=window,
        brute_force_max=brute_force_max,
        max_full_domain_pools=max_full_domain_pools,
        max_enumerated_candidates=max_enumerated_candidates,
    )
    packet = build_exact_out_many_pool_certified_advisory_packet(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=amount_out_total_i,
        max_legs=max_legs_i,
        max_candidate_pools=max_candidate_pools_i,
        max_candidates=max_candidates_i,
        max_iters=max_iters_i,
        window=window_i,
        brute_force_max=brute_force_max_i,
        max_full_domain_pools=max_full_domain_pools_i,
        max_enumerated_candidates=max_enumerated_candidates_i,
    )
    if packet.packet_ok:
        return packet.advisory_packet.advisory_quote, None, packet
    if not packet.certified_packet.packet_ok:
        return None, EXACT_OUT_MANY_POOL_GUARD_MISMATCH_ERROR, packet
    if not packet.advisory_packet.packet_ok:
        return None, str(packet.advisory_packet.error or EXACT_OUT_MANY_POOL_GUARD_MISMATCH_ERROR), packet
    if not packet.selected_runtime_quotes_agree:
        return None, EXACT_OUT_MANY_POOL_RUNTIME_QUOTE_INCONSISTENCY_ERROR, packet
    return None, EXACT_OUT_MANY_POOL_GUARD_MISMATCH_ERROR, packet


def build_exact_out_many_pool_repaired_replacement_shadow_packet(
    pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int = 3,
    max_candidate_pools: int = 5,
    max_candidates: int = 12,
    max_iters: int = 4096,
    window: int = 64,
    brute_force_max: int = 512,
    max_full_domain_pools: int = 8,
    max_enumerated_candidates: int = 20_000,
) -> ExactOutManyPoolRepairedReplacementShadowPacket:
    amount_out_total_i = _require_amount_out_total_int(amount_out_total)
    (
        max_legs_i,
        max_candidate_pools_i,
        max_candidates_i,
        max_iters_i,
        window_i,
        brute_force_max_i,
        max_full_domain_pools_i,
        max_enumerated_candidates_i,
    ) = _require_runtime_control_values(
        max_legs=max_legs,
        max_candidate_pools=max_candidate_pools,
        max_candidates=max_candidates,
        max_iters=max_iters,
        window=window,
        brute_force_max=brute_force_max,
        max_full_domain_pools=max_full_domain_pools,
        max_enumerated_candidates=max_enumerated_candidates,
    )
    default_packet = build_exact_out_many_pool_default_packet(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=amount_out_total_i,
        max_legs=max_legs_i,
        max_candidate_pools=max_candidate_pools_i,
        max_candidates=max_candidates_i,
        max_iters=max_iters_i,
        window=window_i,
        brute_force_max=brute_force_max_i,
        max_full_domain_pools=max_full_domain_pools_i,
        max_enumerated_candidates=max_enumerated_candidates_i,
    )
    replacement_contract = default_packet.repaired_key_cover_packet.selected_domain_contract
    replacement_available = bool(replacement_contract.contract_ok)
    effective_quote_matches_replacement_quote = bool(
        replacement_available
        and default_packet.packet_ok
        and default_packet.advisory_packet.advisory_quote == replacement_contract.audit.runtime_quote
    )
    replacement_quote_matches_selected_runtime_quote = bool(
        replacement_available
        and replacement_contract.audit.runtime_quote
        == default_packet.certified_packet.guarded_packet.contract.audit.runtime_quote
    )
    packet_ok = bool(default_packet.packet_ok and replacement_available)
    return ExactOutManyPoolRepairedReplacementShadowPacket(
        default_packet=default_packet,
        replacement_contract=replacement_contract,
        replacement_available=bool(replacement_available),
        effective_quote_matches_replacement_quote=bool(effective_quote_matches_replacement_quote),
        replacement_quote_matches_selected_runtime_quote=bool(replacement_quote_matches_selected_runtime_quote),
        packet_ok=bool(packet_ok),
    )


def verify_exact_out_route_canonical_certificate(
    quotes: Sequence[SplitManyPoolsExactOutQuote],
    *,
    certificate: object,
    expected_binding_ok: int = 1,
) -> tuple[bool, str | None]:
    if not isinstance(certificate, ExactOutRouteCanonicalCertificate):
        return False, "certificate must be an ExactOutRouteCanonicalCertificate"
    if certificate.tau_spec_id != ARGMIN_STREAM_CERTIFICATE_V1.spec_id:
        return False, "unsupported tau spec id"
    expected = build_exact_out_route_canonical_certificate(quotes, binding_ok=expected_binding_ok)
    if certificate.winner_index != expected.winner_index:
        return False, "winner_index mismatch"
    if certificate.winner_route_key_rank_u64 != expected.winner_route_key_rank_u64:
        return False, "winner_route_key_rank_u64 mismatch"
    if certificate.winner_quote != expected.winner_quote:
        return False, "winner_quote mismatch"
    if certificate.candidates != expected.candidates:
        return False, "candidate list mismatch"
    if certificate.argmin_steps != expected.argmin_steps:
        return False, "argmin steps mismatch"
    return True, None


def verify_exact_out_many_pool_certified_winner_packet_payload(payload: object) -> tuple[bool, str | None]:
    if not isinstance(payload, dict):
        return False, "certified winner packet payload must be a dict"
    if payload.get("schema") != EXACT_OUT_MANY_POOL_CERTIFIED_WINNER_PACKET_SCHEMA:
        return False, "unsupported certified winner packet schema"
    try:
        domain_payload = payload["domain_contract"]
        if not isinstance(domain_payload, dict):
            return False, "domain_contract must be a dict"
        pools_payload = domain_payload["pool_snapshots"]
        if not isinstance(pools_payload, list) or not pools_payload:
            return False, "pool_snapshots must be a non-empty list"
        pools = tuple(_pool_from_dict(pool_payload) for pool_payload in pools_payload)
        expected = build_exact_out_many_pool_certified_winner_packet(
            pools,
            asset_in=str(domain_payload["asset_in"]),
            asset_out=str(domain_payload["asset_out"]),
            amount_out_total=_require_payload_int(domain_payload, "amount_out_total"),
            max_legs=_require_payload_int(domain_payload, "max_legs"),
            max_candidate_pools=_require_payload_int(domain_payload, "max_candidate_pools"),
            max_candidates=_require_payload_int_path(payload, "guarded_packet", "contract", "max_candidates"),
            max_iters=_require_payload_int_path(payload, "guarded_packet", "contract", "max_iters"),
            window=_require_payload_int_path(payload, "guarded_packet", "contract", "window"),
            brute_force_max=_require_payload_int_path(payload, "guarded_packet", "contract", "brute_force_max"),
            max_full_domain_pools=_require_payload_int_path(payload, "guarded_packet", "contract", "max_full_domain_pools"),
            max_enumerated_candidates=_require_payload_int(domain_payload, "max_enumerated_candidates"),
        )
    except (KeyError, TypeError, ValueError) as exc:
        return False, str(exc)
    if payload != expected.to_dict():
        return False, "certified winner packet payload mismatch"
    return True, None


def verify_exact_out_many_pool_certified_advisory_packet_payload(payload: object) -> tuple[bool, str | None]:
    if not isinstance(payload, dict):
        return False, "certified advisory packet payload must be a dict"
    if payload.get("schema") != EXACT_OUT_MANY_POOL_CERTIFIED_ADVISORY_PACKET_SCHEMA:
        return False, "unsupported certified advisory packet schema"
    try:
        certified_payload = payload["certified_packet"]
        advisory_payload = payload["advisory_packet"]
        if not isinstance(certified_payload, dict):
            return False, "certified_packet must be a dict"
        if not isinstance(advisory_payload, dict):
            return False, "advisory_packet must be a dict"
        domain_payload = certified_payload["domain_contract"]
        workaround_payload = advisory_payload["workaround_packet"]
        if not isinstance(domain_payload, dict):
            return False, "domain_contract must be a dict"
        if not isinstance(workaround_payload, dict):
            return False, "workaround_packet must be a dict"
        pools_payload = domain_payload["pool_snapshots"]
        if not isinstance(pools_payload, list) or not pools_payload:
            return False, "pool_snapshots must be a non-empty list"
        pools = tuple(_pool_from_dict(pool_payload) for pool_payload in pools_payload)
        expected = build_exact_out_many_pool_certified_advisory_packet(
            pools,
            asset_in=str(domain_payload["asset_in"]),
            asset_out=str(domain_payload["asset_out"]),
            amount_out_total=_require_payload_int(domain_payload, "amount_out_total"),
            max_legs=_require_payload_int(domain_payload, "max_legs"),
            max_candidate_pools=_require_payload_int(domain_payload, "max_candidate_pools"),
            max_candidates=_require_payload_int_path(certified_payload, "guarded_packet", "contract", "max_candidates"),
            max_iters=_require_payload_int_path(certified_payload, "guarded_packet", "contract", "max_iters"),
            window=_require_payload_int_path(certified_payload, "guarded_packet", "contract", "window"),
            brute_force_max=_require_payload_int_path(certified_payload, "guarded_packet", "contract", "brute_force_max"),
            max_full_domain_pools=_require_payload_int_path(
                workaround_payload,
                "repaired_packet",
                "repaired_contract",
                "max_full_domain_pools",
            ),
            max_enumerated_candidates=_require_payload_int(domain_payload, "max_enumerated_candidates"),
        )
    except (KeyError, TypeError, ValueError) as exc:
        return False, str(exc)
    if payload != expected.to_dict():
        return False, "certified advisory packet payload mismatch"
    return True, None


def verify_exact_out_route_canonical_certificate_payload(
    payload: object,
    *,
    expected_binding_ok: int = 1,
) -> tuple[bool, str | None]:
    try:
        quotes = extract_exact_out_route_certificate_quotes(payload)
    except (TypeError, ValueError) as exc:
        return False, str(exc)
    expected = build_exact_out_route_canonical_certificate(quotes, binding_ok=expected_binding_ok)
    if not isinstance(payload, dict):
        return False, "certificate payload must be a dict"
    if payload != expected.to_dict():
        return False, "certificate payload mismatch"
    return True, None


def verify_exact_out_many_pool_repaired_replacement_shadow_packet_payload(payload: object) -> tuple[bool, str | None]:
    if not isinstance(payload, dict):
        return False, "repaired replacement shadow packet payload must be a dict"
    if payload.get("schema") != EXACT_OUT_MANY_POOL_REPAIRED_REPLACEMENT_SHADOW_PACKET_SCHEMA:
        return False, "unsupported repaired replacement shadow packet schema"
    try:
        replacement_payload = payload["replacement_contract"]
        if not isinstance(replacement_payload, dict):
            return False, "replacement_contract must be a dict"
        pools_payload = replacement_payload["pool_snapshots"]
        if not isinstance(pools_payload, list) or not pools_payload:
            return False, "pool_snapshots must be a non-empty list"
        pools = tuple(_pool_from_dict(pool_payload) for pool_payload in pools_payload)
        expected = build_exact_out_many_pool_repaired_replacement_shadow_packet(
            pools,
            asset_in=str(replacement_payload["asset_in"]),
            asset_out=str(replacement_payload["asset_out"]),
            amount_out_total=_require_payload_int(replacement_payload, "amount_out_total"),
            max_legs=_require_payload_int(replacement_payload, "max_legs"),
            max_candidate_pools=_require_payload_int(replacement_payload, "max_candidate_pools"),
            max_candidates=_require_payload_int(replacement_payload, "max_candidates"),
            max_iters=_require_payload_int(replacement_payload, "max_iters"),
            window=_require_payload_int(replacement_payload, "window"),
            brute_force_max=_require_payload_int(replacement_payload, "brute_force_max"),
            max_full_domain_pools=_require_payload_int(replacement_payload, "max_full_domain_pools"),
            max_enumerated_candidates=_require_payload_int(replacement_payload, "max_enumerated_candidates"),
        )
    except (KeyError, TypeError, ValueError) as exc:
        return False, str(exc)
    if payload != expected.to_dict():
        return False, "repaired replacement shadow packet payload mismatch"
    return True, None


def verify_exact_out_many_pool_repaired_selected_domain_oracle_contract_payload(payload: object) -> tuple[bool, str | None]:
    if not isinstance(payload, dict):
        return False, "repaired selected-domain oracle contract payload must be a dict"
    if payload.get("schema") != EXACT_OUT_MANY_POOL_REPAIRED_SELECTED_DOMAIN_ORACLE_CONTRACT_SCHEMA:
        return False, "unsupported repaired selected-domain oracle contract schema"
    try:
        pools_payload = payload["pool_snapshots"]
        if not isinstance(pools_payload, list) or not pools_payload:
            return False, "pool_snapshots must be a non-empty list"
        pools = tuple(_pool_from_dict(pool_payload) for pool_payload in pools_payload)
        expected = build_exact_out_many_pool_repaired_selected_domain_oracle_contract(
            pools,
            asset_in=str(payload["asset_in"]),
            asset_out=str(payload["asset_out"]),
            amount_out_total=_require_payload_int(payload, "amount_out_total"),
            max_legs=_require_payload_int(payload, "max_legs"),
            max_candidate_pools=_require_payload_int(payload, "max_candidate_pools"),
            max_candidates=_require_payload_int(payload, "max_candidates"),
            max_iters=_require_payload_int(payload, "max_iters"),
            window=_require_payload_int(payload, "window"),
            brute_force_max=_require_payload_int(payload, "brute_force_max"),
            max_full_domain_pools=_require_payload_int(payload, "max_full_domain_pools"),
            max_enumerated_candidates=_require_payload_int(payload, "max_enumerated_candidates"),
        )
    except (KeyError, TypeError, ValueError) as exc:
        return False, str(exc)
    if payload != expected.to_dict():
        return False, "repaired selected-domain oracle contract payload mismatch"
    return True, None


def verify_exact_out_many_pool_oracle_contract_payload(payload: object) -> tuple[bool, str | None]:
    if not isinstance(payload, dict):
        return False, "oracle contract payload must be a dict"
    if payload.get("schema") != EXACT_OUT_MANY_POOL_ORACLE_CONTRACT_SCHEMA:
        return False, "unsupported oracle contract schema"
    try:
        pools_payload = payload["pool_snapshots"]
        if not isinstance(pools_payload, list) or not pools_payload:
            return False, "pool_snapshots must be a non-empty list"
        pools = tuple(_pool_from_dict(pool_payload) for pool_payload in pools_payload)
        expected = build_exact_out_many_pool_oracle_contract(
            pools,
            asset_in=str(payload["asset_in"]),
            asset_out=str(payload["asset_out"]),
            amount_out_total=_require_payload_int(payload, "amount_out_total"),
            max_legs=_require_payload_int(payload, "max_legs"),
            max_candidate_pools=_require_payload_int(payload, "max_candidate_pools"),
            max_candidates=_require_payload_int(payload, "max_candidates"),
            max_iters=_require_payload_int(payload, "max_iters"),
            window=_require_payload_int(payload, "window"),
            brute_force_max=_require_payload_int(payload, "brute_force_max"),
            max_enumerated_candidates=_require_payload_int(payload, "max_enumerated_candidates"),
        )
    except (KeyError, TypeError, ValueError) as exc:
        return False, str(exc)
    if payload != expected.to_dict():
        return False, "oracle contract payload mismatch"
    return True, None


def verify_exact_out_many_pool_guarded_quote_packet_payload(payload: object) -> tuple[bool, str | None]:
    if not isinstance(payload, dict):
        return False, "guarded quote packet payload must be a dict"
    if payload.get("schema") != EXACT_OUT_MANY_POOL_GUARDED_QUOTE_PACKET_SCHEMA:
        return False, "unsupported guarded quote packet schema"
    contract_payload = payload.get("contract")
    if not isinstance(contract_payload, dict):
        return False, "contract must be a dict"
    ok, err = verify_exact_out_many_pool_oracle_contract_payload(contract_payload)
    if not ok:
        return False, err
    try:
        pools_payload = contract_payload["pool_snapshots"]
        if not isinstance(pools_payload, list) or not pools_payload:
            return False, "pool_snapshots must be a non-empty list"
        pools = tuple(_pool_from_dict(pool_payload) for pool_payload in pools_payload)
        expected = build_exact_out_many_pool_guarded_quote_packet(
            pools,
            asset_in=str(contract_payload["asset_in"]),
            asset_out=str(contract_payload["asset_out"]),
            amount_out_total=_require_payload_int(contract_payload, "amount_out_total"),
            max_legs=_require_payload_int(contract_payload, "max_legs"),
            max_candidate_pools=_require_payload_int(contract_payload, "max_candidate_pools"),
            max_candidates=_require_payload_int(contract_payload, "max_candidates"),
            max_iters=_require_payload_int(contract_payload, "max_iters"),
            window=_require_payload_int(contract_payload, "window"),
            brute_force_max=_require_payload_int(contract_payload, "brute_force_max"),
            max_enumerated_candidates=_require_payload_int(contract_payload, "max_enumerated_candidates"),
        )
    except (KeyError, TypeError, ValueError) as exc:
        return False, str(exc)
    if payload != expected.to_dict():
        return False, "guarded quote packet payload mismatch"
    return True, None


def verify_exact_out_many_pool_repaired_advisory_quote_packet_payload(payload: object) -> tuple[bool, str | None]:
    if not isinstance(payload, dict):
        return False, "repaired advisory quote packet payload must be a dict"
    if payload.get("schema") != EXACT_OUT_MANY_POOL_REPAIRED_ADVISORY_QUOTE_PACKET_SCHEMA:
        return False, "unsupported repaired advisory quote packet schema"
    contract_payload = payload.get("repaired_contract")
    if not isinstance(contract_payload, dict):
        return False, "repaired_contract must be a dict"
    ok, err = verify_exact_out_many_pool_repaired_prefilter_contract_payload(contract_payload)
    if not ok:
        return False, err
    try:
        pools_payload = contract_payload["pool_snapshots"]
        if not isinstance(pools_payload, list) or not pools_payload:
            return False, "pool_snapshots must be a non-empty list"
        pools = tuple(_pool_from_dict(pool_payload) for pool_payload in pools_payload)
        expected = build_exact_out_many_pool_repaired_advisory_quote_packet(
            pools,
            asset_in=str(contract_payload["asset_in"]),
            asset_out=str(contract_payload["asset_out"]),
            amount_out_total=_require_payload_int(contract_payload, "amount_out_total"),
            max_legs=_require_payload_int(contract_payload, "max_legs"),
            max_candidate_pools=_require_payload_int(contract_payload, "max_candidate_pools"),
            max_candidates=_require_payload_int(payload, "max_candidates"),
            max_iters=_require_payload_int(payload, "max_iters"),
            window=_require_payload_int(payload, "window"),
            brute_force_max=_require_payload_int(payload, "brute_force_max"),
            max_full_domain_pools=_require_payload_int(contract_payload, "max_full_domain_pools"),
            max_enumerated_candidates=_require_payload_int(contract_payload, "max_enumerated_candidates"),
        )
    except (KeyError, TypeError, ValueError) as exc:
        return False, str(exc)
    if payload != expected.to_dict():
        return False, "repaired advisory quote packet payload mismatch"
    return True, None


def verify_exact_out_many_pool_repaired_full_domain_certified_packet_payload(
    payload: object,
) -> tuple[bool, str | None]:
    if not isinstance(payload, dict):
        return False, "repaired full-domain certified packet payload must be a dict"
    if payload.get("schema") != EXACT_OUT_MANY_POOL_REPAIRED_FULL_DOMAIN_CERTIFIED_PACKET_SCHEMA:
        return False, "unsupported repaired full-domain certified packet schema"
    repaired_payload = payload.get("repaired_packet")
    if not isinstance(repaired_payload, dict):
        return False, "repaired_packet must be a dict"
    ok, err = verify_exact_out_many_pool_repaired_advisory_quote_packet_payload(repaired_payload)
    if not ok:
        return False, err
    contract_payload = repaired_payload.get("repaired_contract")
    if not isinstance(contract_payload, dict):
        return False, "repaired_contract must be a dict"
    try:
        pools_payload = contract_payload["pool_snapshots"]
        if not isinstance(pools_payload, list) or not pools_payload:
            return False, "pool_snapshots must be a non-empty list"
        pools = tuple(_pool_from_dict(pool_payload) for pool_payload in pools_payload)
        expected = build_exact_out_many_pool_repaired_full_domain_certified_packet(
            pools,
            asset_in=str(contract_payload["asset_in"]),
            asset_out=str(contract_payload["asset_out"]),
            amount_out_total=_require_payload_int(contract_payload, "amount_out_total"),
            max_legs=_require_payload_int(contract_payload, "max_legs"),
            max_candidate_pools=_require_payload_int(contract_payload, "max_candidate_pools"),
            max_candidates=_require_payload_int(repaired_payload, "max_candidates"),
            max_iters=_require_payload_int(repaired_payload, "max_iters"),
            window=_require_payload_int(repaired_payload, "window"),
            brute_force_max=_require_payload_int(repaired_payload, "brute_force_max"),
            max_full_domain_pools=_require_payload_int(contract_payload, "max_full_domain_pools"),
            max_enumerated_candidates=_require_payload_int(contract_payload, "max_enumerated_candidates"),
        )
    except (KeyError, TypeError, ValueError) as exc:
        return False, str(exc)
    if payload != expected.to_dict():
        return False, "repaired full-domain certified packet payload mismatch"
    return True, None


def verify_exact_out_many_pool_repaired_key_cover_packet_payload(
    payload: object,
) -> tuple[bool, str | None]:
    if not isinstance(payload, dict):
        return False, "repaired key-cover packet payload must be a dict"
    if payload.get("schema") != EXACT_OUT_MANY_POOL_REPAIRED_KEY_COVER_PACKET_SCHEMA:
        return False, "unsupported repaired key-cover packet schema"
    selected_domain_payload = payload.get("selected_domain_contract")
    if not isinstance(selected_domain_payload, dict):
        return False, "selected_domain_contract must be a dict"
    ok, err = verify_exact_out_many_pool_repaired_selected_domain_oracle_contract_payload(selected_domain_payload)
    if not ok:
        return False, err
    try:
        pools_payload = selected_domain_payload["pool_snapshots"]
        if not isinstance(pools_payload, list) or not pools_payload:
            return False, "pool_snapshots must be a non-empty list"
        pools = tuple(_pool_from_dict(pool_payload) for pool_payload in pools_payload)
        expected = build_exact_out_many_pool_repaired_key_cover_packet(
            pools,
            asset_in=str(selected_domain_payload["asset_in"]),
            asset_out=str(selected_domain_payload["asset_out"]),
            amount_out_total=_require_payload_int(selected_domain_payload, "amount_out_total"),
            max_legs=_require_payload_int(selected_domain_payload, "max_legs"),
            max_candidate_pools=_require_payload_int(selected_domain_payload, "max_candidate_pools"),
            max_candidates=_require_payload_int(selected_domain_payload, "max_candidates"),
            max_iters=_require_payload_int(selected_domain_payload, "max_iters"),
            window=_require_payload_int(selected_domain_payload, "window"),
            brute_force_max=_require_payload_int(selected_domain_payload, "brute_force_max"),
            max_full_domain_pools=_require_payload_int(selected_domain_payload, "max_full_domain_pools"),
            max_enumerated_candidates=_require_payload_int(selected_domain_payload, "max_enumerated_candidates"),
        )
    except (KeyError, TypeError, ValueError) as exc:
        return False, str(exc)
    if payload != expected.to_dict():
        return False, "repaired key-cover packet payload mismatch"
    return True, None


def verify_exact_out_many_pool_repaired_key_cover_interpretation_packet_payload(
    payload: object,
) -> tuple[bool, str | None]:
    if not isinstance(payload, dict):
        return False, "repaired key-cover interpretation packet payload must be a dict"
    if payload.get("schema") != EXACT_OUT_MANY_POOL_REPAIRED_KEY_COVER_INTERPRETATION_PACKET_SCHEMA:
        return False, "unsupported repaired key-cover interpretation packet schema"
    key_cover_payload = payload.get("key_cover_packet")
    if not isinstance(key_cover_payload, dict):
        return False, "key_cover_packet must be a dict"
    ok, err = verify_exact_out_many_pool_repaired_key_cover_packet_payload(key_cover_payload)
    if not ok:
        return False, err
    selected_domain_payload = key_cover_payload.get("selected_domain_contract")
    if not isinstance(selected_domain_payload, dict):
        return False, "selected_domain_contract must be a dict"
    try:
        pools_payload = selected_domain_payload["pool_snapshots"]
        if not isinstance(pools_payload, list) or not pools_payload:
            return False, "pool_snapshots must be a non-empty list"
        pools = tuple(_pool_from_dict(pool_payload) for pool_payload in pools_payload)
        expected = build_exact_out_many_pool_repaired_key_cover_interpretation_packet(
            pools,
            asset_in=str(selected_domain_payload["asset_in"]),
            asset_out=str(selected_domain_payload["asset_out"]),
            amount_out_total=_require_payload_int(selected_domain_payload, "amount_out_total"),
            max_legs=_require_payload_int(selected_domain_payload, "max_legs"),
            max_candidate_pools=_require_payload_int(selected_domain_payload, "max_candidate_pools"),
            max_candidates=_require_payload_int(selected_domain_payload, "max_candidates"),
            max_iters=_require_payload_int(selected_domain_payload, "max_iters"),
            window=_require_payload_int(selected_domain_payload, "window"),
            brute_force_max=_require_payload_int(selected_domain_payload, "brute_force_max"),
            max_full_domain_pools=_require_payload_int(selected_domain_payload, "max_full_domain_pools"),
            max_enumerated_candidates=_require_payload_int(selected_domain_payload, "max_enumerated_candidates"),
        )
    except (KeyError, TypeError, ValueError) as exc:
        return False, str(exc)
    if payload != expected.to_dict():
        return False, "repaired key-cover interpretation packet payload mismatch"
    return True, None


def verify_exact_out_many_pool_bounded_workaround_packet_payload(payload: object) -> tuple[bool, str | None]:
    if not isinstance(payload, dict):
        return False, "bounded workaround packet payload must be a dict"
    if payload.get("schema") != EXACT_OUT_MANY_POOL_BOUNDED_WORKAROUND_PACKET_SCHEMA:
        return False, "unsupported bounded workaround packet schema"
    try:
        oracle_payload = payload["oracle_contract"]
        repaired_payload = payload["repaired_packet"]
        if not isinstance(oracle_payload, dict):
            return False, "oracle_contract must be a dict"
        if not isinstance(repaired_payload, dict):
            return False, "repaired_packet must be a dict"
        repaired_full_domain_payload = payload["repaired_full_domain_packet"]
        if not isinstance(repaired_full_domain_payload, dict):
            return False, "repaired_full_domain_packet must be a dict"
        pools_payload = oracle_payload["pool_snapshots"]
        if not isinstance(pools_payload, list) or not pools_payload:
            return False, "pool_snapshots must be a non-empty list"
        pools = tuple(_pool_from_dict(pool_payload) for pool_payload in pools_payload)
        expected = build_exact_out_many_pool_bounded_workaround_packet(
            pools,
            asset_in=str(oracle_payload["asset_in"]),
            asset_out=str(oracle_payload["asset_out"]),
            amount_out_total=_require_payload_int(oracle_payload, "amount_out_total"),
            max_legs=_require_payload_int(oracle_payload, "max_legs"),
            max_candidate_pools=_require_payload_int(oracle_payload, "max_candidate_pools"),
            max_candidates=_require_payload_int(oracle_payload, "max_candidates"),
            max_iters=_require_payload_int(oracle_payload, "max_iters"),
            window=_require_payload_int(oracle_payload, "window"),
            brute_force_max=_require_payload_int(oracle_payload, "brute_force_max"),
            max_full_domain_pools=_require_payload_int_path(repaired_payload, "repaired_contract", "max_full_domain_pools"),
            max_enumerated_candidates=_require_payload_int(oracle_payload, "max_enumerated_candidates"),
        )
    except (KeyError, TypeError, ValueError) as exc:
        return False, str(exc)
    if payload != expected.to_dict():
        return False, "bounded workaround packet payload mismatch"
    return True, None


def verify_exact_out_many_pool_bounded_advisory_quote_packet_payload(payload: object) -> tuple[bool, str | None]:
    if not isinstance(payload, dict):
        return False, "bounded advisory quote packet payload must be a dict"
    if payload.get("schema") != EXACT_OUT_MANY_POOL_BOUNDED_ADVISORY_QUOTE_PACKET_SCHEMA:
        return False, "unsupported bounded advisory quote packet schema"
    try:
        workaround_payload = payload["workaround_packet"]
        if not isinstance(workaround_payload, dict):
            return False, "workaround_packet must be a dict"
        oracle_payload = workaround_payload["oracle_contract"]
        repaired_payload = workaround_payload["repaired_packet"]
        repaired_full_domain_payload = workaround_payload["repaired_full_domain_packet"]
        if not isinstance(oracle_payload, dict):
            return False, "oracle_contract must be a dict"
        if not isinstance(repaired_payload, dict):
            return False, "repaired_packet must be a dict"
        if not isinstance(repaired_full_domain_payload, dict):
            return False, "repaired_full_domain_packet must be a dict"
        pools_payload = oracle_payload["pool_snapshots"]
        if not isinstance(pools_payload, list) or not pools_payload:
            return False, "pool_snapshots must be a non-empty list"
        pools = tuple(_pool_from_dict(pool_payload) for pool_payload in pools_payload)
        expected = build_exact_out_many_pool_bounded_advisory_quote_packet(
            pools,
            asset_in=str(oracle_payload["asset_in"]),
            asset_out=str(oracle_payload["asset_out"]),
            amount_out_total=_require_payload_int(oracle_payload, "amount_out_total"),
            max_legs=_require_payload_int(oracle_payload, "max_legs"),
            max_candidate_pools=_require_payload_int(oracle_payload, "max_candidate_pools"),
            max_candidates=_require_payload_int(oracle_payload, "max_candidates"),
            max_iters=_require_payload_int(oracle_payload, "max_iters"),
            window=_require_payload_int(oracle_payload, "window"),
            brute_force_max=_require_payload_int(oracle_payload, "brute_force_max"),
            max_full_domain_pools=_require_payload_int_path(repaired_payload, "repaired_contract", "max_full_domain_pools"),
            max_enumerated_candidates=_require_payload_int(oracle_payload, "max_enumerated_candidates"),
        )
    except (KeyError, TypeError, ValueError) as exc:
        return False, str(exc)
    if payload != expected.to_dict():
        return False, "bounded advisory quote packet payload mismatch"
    return True, None


def _projection_cover_audit_from_kernel(
    audit: _KernelExactOutManyPoolProjectionCoverAudit,
) -> ExactOutManyPoolProjectionCoverAudit:
    return ExactOutManyPoolProjectionCoverAudit(
        selected_pool_ids=tuple(str(pool_id) for pool_id in audit.selected_pool_ids),
        emitted_candidate_count=int(audit.emitted_candidate_count),
        emitted_projected_path_count=int(audit.emitted_projected_path_count),
        reachable_projected_path_count=int(audit.reachable_projected_path_count),
        canonical_quote_projected_path=tuple(
            (str(pool_id), int(amount_out), int(amount_in))
            for pool_id, amount_out, amount_in in audit.canonical_quote_projected_path
        ),
        canonical_quote_covered=bool(audit.canonical_quote_covered),
        sound_holds=bool(audit.sound_holds),
        complete_holds=bool(audit.complete_holds),
        projection_cover_holds=bool(audit.projection_cover_holds),
        extra_emitted_path=None
        if audit.extra_emitted_path is None
        else tuple(
            (str(pool_id), int(amount_out), int(amount_in))
            for pool_id, amount_out, amount_in in audit.extra_emitted_path
        ),
        missing_reachable_path=None
        if audit.missing_reachable_path is None
        else tuple(
            (str(pool_id), int(amount_out), int(amount_in))
            for pool_id, amount_out, amount_in in audit.missing_reachable_path
        ),
    )


def _quote_to_dict(quote: SplitManyPoolsExactOutQuote) -> dict[str, Any]:
    return {
        "amount_out_total": int(quote.amount_out_total),
        "amount_in_total": int(quote.amount_in_total),
        "legs": [_leg_to_dict(leg) for leg in quote.legs],
    }


def _quote_to_projected_path_payload(
    quote: SplitManyPoolsExactOutQuote,
) -> list[list[Any]]:
    return [
        [str(leg.pool_id), int(leg.amount_out), int(leg.amount_in)]
        for leg in quote.legs
    ]


def _route_key_to_dict(route_key: ExactOutRouteCanonicalKey) -> dict[str, Any]:
    return {
        "amount_in_total": int(route_key.amount_in_total),
        "leg_count": int(route_key.leg_count),
        "legs_lex": [[str(pool_id), int(amount_out)] for pool_id, amount_out in route_key.legs_lex],
    }


def _candidate_key_payload(candidate: ExactOutRouteCandidateCertificate) -> dict[str, Any]:
    return {
        "candidate_index": int(candidate.candidate_index),
        "route_key_rank_u64": int(candidate.route_key_rank_u64),
        "route_key": _route_key_to_dict(candidate.route_key),
    }


def _pool_to_dict(pool: PoolState) -> dict[str, Any]:
    return {
        "pool_id": str(pool.pool_id),
        "asset0": str(pool.asset0),
        "asset1": str(pool.asset1),
        "reserve0": int(pool.reserve0),
        "reserve1": int(pool.reserve1),
        "fee_bps": int(pool.fee_bps),
        "lp_supply": int(pool.lp_supply),
        "status": str(pool.status.value),
        "created_at": int(pool.created_at),
        "curve_tag": str(pool.curve_tag),
        "curve_params": str(pool.curve_params),
    }


def _pool_from_dict(payload: object) -> PoolState:
    if not isinstance(payload, dict):
        raise TypeError("pool snapshot payload must be a dict")
    status_raw = payload.get("status")
    if not isinstance(status_raw, str) or status_raw not in PoolStatus.__members__:
        raise ValueError("pool snapshot status must be a valid PoolStatus string")
    return PoolState(
        pool_id=str(payload["pool_id"]),
        asset0=str(payload["asset0"]),
        asset1=str(payload["asset1"]),
        reserve0=_require_payload_int(payload, "reserve0"),
        reserve1=_require_payload_int(payload, "reserve1"),
        fee_bps=_require_payload_int(payload, "fee_bps"),
        lp_supply=_require_payload_int(payload, "lp_supply"),
        status=PoolStatus[status_raw],
        created_at=_require_payload_int(payload, "created_at"),
        curve_tag=str(payload["curve_tag"]),
        curve_params=str(payload["curve_params"]),
    )


def extract_exact_out_route_certificate_quotes(payload: object) -> tuple[SplitManyPoolsExactOutQuote, ...]:
    if not isinstance(payload, dict):
        raise TypeError("certificate payload must be a dict")
    candidates = payload.get("candidates")
    if not isinstance(candidates, list) or not candidates:
        raise ValueError("certificate payload must include non-empty candidates")
    return tuple(_quote_from_candidate_dict(candidate) for candidate in candidates)


def _leg_to_dict(leg: SplitLegExactOutQuote) -> dict[str, Any]:
    return {
        "pool_id": leg.pool_id,
        "amount_out": int(leg.amount_out),
        "amount_in": int(leg.amount_in),
    }


def _quote_from_candidate_dict(candidate: object) -> SplitManyPoolsExactOutQuote:
    if not isinstance(candidate, dict):
        raise TypeError("certificate candidate must be a dict")
    return _quote_from_dict(candidate.get("quote"))


def _quote_from_dict(payload: object) -> SplitManyPoolsExactOutQuote:
    if not isinstance(payload, dict):
        raise TypeError("split quote payload must be a dict")
    amount_out_total = payload.get("amount_out_total")
    amount_in_total = payload.get("amount_in_total")
    legs = payload.get("legs")
    if not isinstance(amount_out_total, int) or isinstance(amount_out_total, bool) or amount_out_total <= 0:
        raise ValueError("split quote amount_out_total must be a positive int")
    if not isinstance(amount_in_total, int) or isinstance(amount_in_total, bool) or amount_in_total <= 0:
        raise ValueError("split quote amount_in_total must be a positive int")
    if not isinstance(legs, list) or not legs:
        raise ValueError("split quote legs must be a non-empty list")
    return SplitManyPoolsExactOutQuote(
        amount_out_total=int(amount_out_total),
        amount_in_total=int(amount_in_total),
        legs=tuple(_leg_from_dict(leg) for leg in legs),
    )


def _leg_from_dict(payload: object) -> SplitLegExactOutQuote:
    if not isinstance(payload, dict):
        raise TypeError("split leg payload must be a dict")
    pool_id = payload.get("pool_id")
    amount_out = payload.get("amount_out")
    amount_in = payload.get("amount_in")
    if not isinstance(pool_id, str) or not pool_id:
        raise ValueError("split leg pool_id must be a non-empty string")
    if not isinstance(amount_out, int) or isinstance(amount_out, bool) or amount_out <= 0:
        raise ValueError("split leg amount_out must be a positive int")
    if not isinstance(amount_in, int) or isinstance(amount_in, bool) or amount_in <= 0:
        raise ValueError("split leg amount_in must be a positive int")
    return SplitLegExactOutQuote(
        pool_id=pool_id,
        amount_out=int(amount_out),
        amount_in=int(amount_in),
    )
