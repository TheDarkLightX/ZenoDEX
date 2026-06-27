from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Sequence

from src.core.split_routing_dispatch import (
    ExactOutRouteCanonicalKey,
    SplitLegExactOutQuote,
    SplitManyPoolsExactOutQuote,
    SplitTwoPoolsQuote,
    best_split_many_pools_exact_out_for_pools,
    best_split_two_pools_exact_out_for_pools,
)
from src.core.amm_dispatch import swap_exact_out_for_pool
from src.state.pools import PoolState, PoolStatus
from src.kernels.python.exact_out_many_pool_certified_winner_packet_v1_adapter import (
    check_exact_out_many_pool_certified_winner_packet_gate,
)
from src.kernels.python.exact_out_many_pool_bounded_oracle_v1 import (
    bounded_exact_out_many_pool_runtime_domain as _kernel_bounded_exact_out_many_pool_runtime_domain,
    enumerate_exact_out_many_pool_candidates as _kernel_enumerate_exact_out_many_pool_candidates,
    feasible_exact_out_pools as _kernel_feasible_exact_out_pools,
    pool_reserves_for_exact_out as _kernel_pool_reserves_for_exact_out,
    select_many_pool_audit_candidates as _kernel_select_many_pool_audit_candidates,
)
from src.kernels.python.exact_out_many_pool_canonical_domain_v1 import (
    build_exact_out_many_pool_selected_domain as _kernel_build_exact_out_many_pool_selected_domain,
    rank_exact_out_feasible_pools as _kernel_rank_exact_out_feasible_pools,
)
from src.kernels.python.exact_out_many_pool_prefilter_contraction_audit_v1 import (
    audit_exact_out_many_pool_selected_subset_contraction as _kernel_audit_exact_out_many_pool_selected_subset_contraction,
)
from src.kernels.python.exact_out_many_pool_projection_cover_audit_v1 import (
    ExactOutManyPoolCpmmProjectionCoverAudit as _KernelExactOutManyPoolCpmmProjectionCoverAudit,
    audit_exact_out_many_pool_selected_domain_projection_cover as _kernel_audit_exact_out_many_pool_selected_domain_projection_cover,
)
from src.kernels.python.exact_out_many_pool_repaired_prefilter_v1 import (
    build_many_pool_repaired_prefilter_selection as _kernel_build_many_pool_repaired_prefilter_selection,
)
from src.kernels.python.exact_out_route_canonical_selector_v1 import (
    select_exact_out_route_canonical_winner as _kernel_select_exact_out_route_canonical_winner,
)

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
        for field_name, value in (
            ("selected_keys_subset_full_keys", self.selected_keys_subset_full_keys),
            ("key_cover_holds", self.key_cover_holds),
            ("selected_domain_canonical_matches_full_domain_canonical", self.selected_domain_canonical_matches_full_domain_canonical),
        ):
            if not isinstance(value, bool):
                raise TypeError(f"{field_name} must be a bool")
        for field_name, value in (
            ("selected_candidate_count", self.selected_candidate_count),
            ("full_candidate_count", self.full_candidate_count),
        ):
            if not isinstance(value, int) or isinstance(value, bool):
                raise TypeError(f"{field_name} must be an int")
            if int(value) <= 0:
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
        selected_canonical_projected_path = (
            None
            if selected_projection_cover is None
            else [
                [str(pool_id), int(amount_out), int(amount_in)]
                for pool_id, amount_out, amount_in in selected_projection_cover.canonical_quote_projected_path
            ]
        )
        repaired_canonical_projected_path = (
            None
            if repaired_projection_cover is None
            else [
                [str(pool_id), int(amount_out), int(amount_in)]
                for pool_id, amount_out, amount_in in repaired_projection_cover.canonical_quote_projected_path
            ]
        )
        selected_projection_cover_holds = (
            None if selected_projection_cover is None else bool(selected_projection_cover.projection_cover_holds)
        )
        repaired_projection_cover_holds = (
            None if repaired_projection_cover is None else bool(repaired_projection_cover.projection_cover_holds)
        )
        if self.advisory_packet.quote_source == "selected_domain_runtime":
            effective_projection_cover_side = "selected_domain"
            effective_projection_cover_holds = selected_projection_cover_holds
            effective_canonical_projected_path = selected_canonical_projected_path
            effective_quote_projected_path = selected_runtime_projected_path
        elif self.advisory_packet.quote_source == "repaired_bounded_advisory":
            effective_projection_cover_side = "repaired"
            effective_projection_cover_holds = repaired_projection_cover_holds
            effective_canonical_projected_path = repaired_canonical_projected_path
            effective_quote_projected_path = advisory_projected_path
        else:
            effective_projection_cover_side = None
            effective_projection_cover_holds = None
            effective_canonical_projected_path = None
            effective_quote_projected_path = None
        return {
            "effective_quote_source": self.advisory_packet.quote_source,
            "effective_quote": effective_quote,
            "selected_domain_runtime_quote": selected_runtime_quote,
            "effective_quote_matches_selected_runtime_quote": bool(self.advisory_packet.quote_matches_runtime),
            "effective_quote_matches_repaired_advisory_quote": bool(self.advisory_packet.quote_matches_repaired_advisory),
            "repaired_full_domain_packet_ok": bool(repaired_full_domain_payload["packet_ok"]),
            "repaired_quote_matches_full_domain_canonical": bool(
                repaired_full_domain_payload["repaired_matches_full_canonical"]
            ),
            "repaired_full_domain_feasible_pool_ids": repaired_full_domain_payload["full_domain_feasible_pool_ids"],
            "repaired_full_domain_candidate_count": repaired_full_domain_payload["full_domain_candidate_count"],
            "repaired_full_domain_canonical_quote": repaired_full_domain_payload["full_domain_canonical_quote"],
            "effective_quote_matches_full_domain_canonical": (
                None
                if effective_quote is None
                else bool(effective_quote == repaired_full_domain_payload["full_domain_canonical_quote"])
            ),
            "repaired_key_cover_packet_ok": bool(self.repaired_key_cover_packet.packet_ok),
            "repaired_selected_keys_subset_full_keys": bool(self.repaired_key_cover_packet.selected_keys_subset_full_keys),
            "repaired_key_cover_holds": bool(self.repaired_key_cover_packet.key_cover_holds),
            "repaired_selected_domain_canonical_matches_full_domain_canonical": bool(
                self.repaired_key_cover_packet.selected_domain_canonical_matches_full_domain_canonical
            ),
            "repaired_key_cover_witness_count": len(self.repaired_key_cover_packet.domination_witnesses),
            "repaired_key_cover_interpretation_packet_ok": bool(self.repaired_key_cover_interpretation_packet.packet_ok),
            "repaired_key_cover_selected_winner_index_in_range": bool(
                self.repaired_key_cover_interpretation_packet.selected_winner_index_in_range
            ),
            "repaired_key_cover_selected_winner_matches_certificate": bool(
                self.repaired_key_cover_interpretation_packet.selected_winner_matches_certificate
            ),
            "repaired_key_cover_selected_winner_key_minimal": bool(
                self.repaired_key_cover_interpretation_packet.selected_winner_key_minimal
            ),
            "repaired_key_cover_witness_indices_in_range": bool(
                self.repaired_key_cover_interpretation_packet.domination_witness_indices_in_range
            ),
            "repaired_key_cover_witness_coverage_complete": bool(
                self.repaired_key_cover_interpretation_packet.domination_witnesses_cover_full_candidates
            ),
            "repaired_key_cover_witness_keys_match_candidates": bool(
                self.repaired_key_cover_interpretation_packet.domination_witness_keys_match_candidates
            ),
            "repaired_key_cover_witness_domination_holds": bool(
                self.repaired_key_cover_interpretation_packet.domination_witnesses_dominate
            ),
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
            "effective_projection_cover_side": effective_projection_cover_side,
            "effective_projection_cover_holds": effective_projection_cover_holds,
            "effective_canonical_projected_path": effective_canonical_projected_path,
            "effective_quote_projected_path": effective_quote_projected_path,
            "effective_quote_matches_canonical_projected_path": (
                None
                if effective_quote_projected_path is None or effective_canonical_projected_path is None
                else bool(effective_quote_projected_path == effective_canonical_projected_path)
            ),
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
        if not isinstance(self.audited_bounds_contract, ExactOutManyPoolAuditedBoundsContract):
            raise TypeError("audited_bounds_contract must be an ExactOutManyPoolAuditedBoundsContract")
        if not isinstance(self.repaired_full_domain_packet, ExactOutManyPoolRepairedFullDomainCertifiedPacket):
            raise TypeError("repaired_full_domain_packet must be an ExactOutManyPoolRepairedFullDomainCertifiedPacket")
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
        if (
            self.repaired_full_domain_packet
            != self.audited_bounds_contract.certified_advisory_packet.advisory_packet.workaround_packet.repaired_full_domain_packet
        ):
            raise ValueError("repaired_full_domain_packet must match the nested audited-bounds repaired full-domain packet")
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
        if self.returned_success:
            if self.effective_quote_source is None:
                raise ValueError("returned_success requires effective_quote_source")
            if self.effective_quote is None:
                raise ValueError("returned_success requires effective_quote")
            if self.failure_reason is not None:
                raise ValueError("returned_success must not carry failure_reason")
            if self.effective_quote_source == "default_certified_advisory":
                if not self.cheap_path_success:
                    raise ValueError("default_certified_advisory source requires cheap_path_success")
                if self.effective_quote != self.audited_bounds_contract.certified_advisory_packet.advisory_packet.advisory_quote:
                    raise ValueError("effective_quote must match audited-bounds certified advisory quote")
            elif self.effective_quote_source == "repaired_full_domain":
                if not self.fallback_success:
                    raise ValueError("repaired_full_domain source requires fallback_success")
                if self.effective_quote != self.repaired_full_domain_packet.repaired_quote:
                    raise ValueError("effective_quote must match repaired_full_domain_packet.repaired_quote")
        else:
            if self.effective_quote_source is not None or self.effective_quote is not None:
                raise ValueError("explicit failure packets must not carry an effective quote")
            if self.failure_reason is None:
                raise ValueError("explicit failure packets must carry a failure_reason")
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
    return _kernel_select_many_pool_audit_candidates(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_candidate_pools=int(max_candidate_pools),
    )


def enumerate_exact_out_two_pool_candidates(
    pool0: PoolState,
    pool1: PoolState,
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
) -> tuple[SplitManyPoolsExactOutQuote, ...]:
    if int(amount_out_total) <= 0:
        raise ValueError("amount_out_total must be positive")
    p0, p1 = (pool0, pool1) if pool0.pool_id <= pool1.pool_id else (pool1, pool0)
    r0 = _pool_reserves_for_exact_out(p0, asset_in=asset_in, asset_out=asset_out)
    r1 = _pool_reserves_for_exact_out(p1, asset_in=asset_in, asset_out=asset_out)
    if r0 is None or r1 is None:
        raise ValueError("pools do not support this direction (or are inactive)")
    _rin0, rout0 = r0
    _rin1, rout1 = r1
    max0 = max(0, int(rout0) - 1)
    max1 = max(0, int(rout1) - 1)
    lo = max(0, int(amount_out_total) - max1)
    hi = min(int(amount_out_total), max0)
    if lo > hi:
        raise ValueError("no feasible split for desired amount_out_total")

    quotes: list[SplitManyPoolsExactOutQuote] = []
    for q0 in range(int(lo), int(hi) + 1):
        q1 = int(amount_out_total) - int(q0)
        try:
            in0, _ = (
                swap_exact_out_for_pool(
                    p0,
                    reserve_in=int(r0[0]),
                    reserve_out=int(r0[1]),
                    amount_out=int(q0),
                )
                if q0 > 0
                else (0, (int(r0[0]), int(r0[1])))
            )
            in1, _ = (
                swap_exact_out_for_pool(
                    p1,
                    reserve_in=int(r1[0]),
                    reserve_out=int(r1[1]),
                    amount_out=int(q1),
                )
                if q1 > 0
                else (0, (int(r1[0]), int(r1[1])))
            )
        except ValueError:
            continue

        legs: list[SplitLegExactOutQuote] = []
        if q0 > 0:
            legs.append(SplitLegExactOutQuote(pool_id=p0.pool_id, amount_out=int(q0), amount_in=int(in0)))
        if q1 > 0:
            legs.append(SplitLegExactOutQuote(pool_id=p1.pool_id, amount_out=int(q1), amount_in=int(in1)))
        quotes.append(
            SplitManyPoolsExactOutQuote(
                amount_out_total=int(amount_out_total),
                amount_in_total=int(in0 + in1),
                legs=tuple(legs),
            )
        )
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
    return _kernel_enumerate_exact_out_many_pool_candidates(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_candidate_pools=int(max_candidate_pools),
        max_enumerated_candidates=int(max_enumerated_candidates),
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
    if int(max_legs) <= 0:
        return 0
    caps = sorted((int(cap) for cap in caps_by_pool_id.values() if int(cap) > 0), reverse=True)
    return int(sum(caps[: int(max_legs)]))


def build_exact_out_many_pool_prefilter_contract(
    pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int = 3,
    max_candidate_pools: int = 5,
) -> ExactOutManyPoolPrefilterContract:
    if not asset_in or not asset_out or asset_in == asset_out:
        raise ValueError("asset_in and asset_out must be non-empty and distinct")
    if int(amount_out_total) <= 0:
        raise ValueError("amount_out_total must be positive")
    if int(max_legs) <= 0:
        raise ValueError("max_legs must be positive")
    if int(max_candidate_pools) <= 0:
        raise ValueError("max_candidate_pools must be positive")

    ranked_rows_raw = _kernel_rank_exact_out_feasible_pools(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
    )
    feasible_rows = tuple(
        ExactOutManyPoolPrefilterRow(
            pool_id=row.pool_id,
            cap_out=int(row.cap_out),
            probe_amount_out=int(row.probe_amount_out),
            probe_amount_in=int(row.probe_amount_in),
            scaled_unit_cost_u64=int(row.scaled_unit_cost_u64),
        )
        for row in ranked_rows_raw
    )
    selected_pool_ids = tuple(
        pool.pool_id
        for pool in _select_many_pool_audit_candidates(
            pools,
            asset_in=asset_in,
            asset_out=asset_out,
            amount_out_total=int(amount_out_total),
            max_legs=int(max_legs),
            max_candidate_pools=int(max_candidate_pools),
        )
    )

    feasible_pool_ids = tuple(row.pool_id for row in feasible_rows)
    feasible_rows_sorted_unique = _prefilter_rows_rank_sorted_unique(feasible_rows)
    selected_pool_ids_sorted_unique = _audit_pool_ids_sorted_unique(selected_pool_ids)
    selected_pool_ids_within_budget = len(selected_pool_ids) <= int(max_candidate_pools)
    selected_pool_ids_subset_of_feasible = all(pool_id in set(feasible_pool_ids) for pool_id in selected_pool_ids)
    selected_is_prefix_of_feasible_ranking = selected_pool_ids == tuple(
        sorted(feasible_pool_ids[: len(selected_pool_ids)])
    )
    full_capacity_guard_feasible = _top_capacity_sum(
        {row.pool_id: int(row.cap_out) for row in feasible_rows},
        max_legs=int(max_legs),
    ) >= int(amount_out_total)
    selected_capacity_guard_feasible = _top_capacity_sum(
        {row.pool_id: int(row.cap_out) for row in feasible_rows if row.pool_id in set(selected_pool_ids)},
        max_legs=int(max_legs),
    ) >= int(amount_out_total)
    contract_ok = (
        bool(feasible_rows)
        and feasible_rows_sorted_unique
        and selected_pool_ids_sorted_unique
        and selected_pool_ids_within_budget
        and selected_pool_ids_subset_of_feasible
        and selected_is_prefix_of_feasible_ranking
        and full_capacity_guard_feasible
        and selected_capacity_guard_feasible
    )
    return ExactOutManyPoolPrefilterContract(
        asset_in=str(asset_in),
        asset_out=str(asset_out),
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_candidate_pools=int(max_candidate_pools),
        pool_snapshots=tuple(_pool_to_dict(pool) for pool in pools),
        feasible_rows=feasible_rows,
        selected_pool_ids=selected_pool_ids,
        feasible_rows_sorted_unique=bool(feasible_rows_sorted_unique),
        selected_pool_ids_sorted_unique=bool(selected_pool_ids_sorted_unique),
        selected_pool_ids_within_budget=bool(selected_pool_ids_within_budget),
        selected_pool_ids_subset_of_feasible=bool(selected_pool_ids_subset_of_feasible),
        selected_is_prefix_of_feasible_ranking=bool(selected_is_prefix_of_feasible_ranking),
        full_capacity_guard_feasible=bool(full_capacity_guard_feasible),
        selected_capacity_guard_feasible=bool(selected_capacity_guard_feasible),
        contract_ok=bool(contract_ok),
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
    if not asset_in or not asset_out or asset_in == asset_out:
        raise ValueError("asset_in and asset_out must be non-empty and distinct")
    int_fields = (
        ("amount_out_total", amount_out_total, 1),
        ("max_legs", max_legs, 1),
        ("max_candidate_pools", max_candidate_pools, 1),
        ("max_full_domain_pools", max_full_domain_pools, 1),
        ("max_enumerated_candidates", max_enumerated_candidates, 1),
    )
    for field_name, value, min_value in int_fields:
        if not isinstance(value, int) or isinstance(value, bool) or int(value) < int(min_value):
            raise ValueError(f"{field_name} must be an int >= {min_value}")

    from src.kernels.python.exact_out_many_pool_prefilter_subset_search_v1 import (  # pylint: disable=import-outside-toplevel
        search_exact_out_many_pool_prefilter_subset,
    )

    search_result = search_exact_out_many_pool_prefilter_subset(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_candidate_pools=int(max_candidate_pools),
        max_full_domain_pools=int(max_full_domain_pools),
        max_enumerated_candidates=int(max_enumerated_candidates),
    )
    selection = _kernel_build_many_pool_repaired_prefilter_selection(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_candidate_pools=int(max_candidate_pools),
        max_full_domain_pools=int(max_full_domain_pools),
        max_enumerated_candidates=int(max_enumerated_candidates),
    )

    feasible_pool_id_set = set(search_result.feasible_pool_ids)
    repaired_selected_pool_ids_sorted_unique = _audit_pool_ids_sorted_unique(selection.selected_pool_ids)
    repaired_selected_pool_ids_within_budget = len(selection.selected_pool_ids) <= int(max_candidate_pools)
    repaired_selected_pool_ids_subset_of_feasible = all(
        pool_id in feasible_pool_id_set for pool_id in selection.selected_pool_ids
    )
    expected_repaired_selected_pool_ids = (
        search_result.best_cover_subset_ids
        if search_result.best_cover_subset_ids is not None
        else search_result.current_selected_pool_ids
    )
    expected_repaired_matches_full = (
        search_result.best_cover_canonical_quote == search_result.full_domain_canonical_quote
        if search_result.best_cover_subset_ids is not None
        else search_result.current_selected_canonical_quote == search_result.full_domain_canonical_quote
    )
    repaired_selected_domain_matches_full_canonical = (
        tuple(selection.selected_pool_ids) == tuple(expected_repaired_selected_pool_ids)
        and bool(expected_repaired_matches_full)
    )

    pool_by_id = {pool.pool_id: pool for pool in pools}
    repaired_selected_pools = tuple(pool_by_id[pool_id] for pool_id in selection.selected_pool_ids)
    repaired_contraction_audit = _kernel_audit_exact_out_many_pool_selected_subset_contraction(
        pools,
        repaired_selected_pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_full_domain_pools=int(max_full_domain_pools),
        max_enumerated_candidates=int(max_enumerated_candidates),
    )
    repaired_contraction_holds = bool(repaired_contraction_audit.contraction_holds)
    contract_ok = (
        repaired_selected_pool_ids_sorted_unique
        and repaired_selected_pool_ids_within_budget
        and repaired_selected_pool_ids_subset_of_feasible
        and repaired_selected_domain_matches_full_canonical
        and repaired_contraction_holds
    )
    return ExactOutManyPoolRepairedPrefilterContract(
        asset_in=str(asset_in),
        asset_out=str(asset_out),
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_candidate_pools=int(max_candidate_pools),
        max_full_domain_pools=int(max_full_domain_pools),
        max_enumerated_candidates=int(max_enumerated_candidates),
        pool_snapshots=tuple(_pool_to_dict(pool) for pool in pools),
        feasible_pool_ids=tuple(search_result.feasible_pool_ids),
        current_selected_pool_ids=tuple(selection.current_selected_pool_ids),
        repaired_selected_pool_ids=tuple(selection.selected_pool_ids),
        strategy=str(selection.strategy),
        searched_subset_count=int(selection.searched_subset_count),
        current_selected_matches_full_canonical=bool(selection.current_selected_matches_full_canonical),
        repaired_selected_pool_ids_sorted_unique=bool(repaired_selected_pool_ids_sorted_unique),
        repaired_selected_pool_ids_within_budget=bool(repaired_selected_pool_ids_within_budget),
        repaired_selected_pool_ids_subset_of_feasible=bool(repaired_selected_pool_ids_subset_of_feasible),
        repaired_selected_domain_matches_full_canonical=bool(repaired_selected_domain_matches_full_canonical),
        repaired_contraction_holds=bool(repaired_contraction_holds),
        contract_ok=bool(contract_ok),
    )


def _repaired_selected_pools_from_contract(
    pools: Sequence[PoolState],
    *,
    repaired_contract: ExactOutManyPoolRepairedPrefilterContract,
) -> tuple[PoolState, ...]:
    pools_by_id = {pool.pool_id: pool for pool in pools}
    return tuple(pools_by_id[pool_id] for pool_id in repaired_contract.repaired_selected_pool_ids)


def _candidate_quote_to_core_quote(quote: object) -> SplitManyPoolsExactOutQuote:
    amount_out_total = int(getattr(quote, "amount_out_total"))
    amount_in_total = int(getattr(quote, "amount_in_total"))
    legs = tuple(
        SplitLegExactOutQuote(
            pool_id=str(getattr(leg, "pool_id")),
            amount_out=int(getattr(leg, "amount_out")),
            amount_in=int(getattr(leg, "amount_in")),
        )
        for leg in getattr(quote, "legs")
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
    feasible_rows = _feasible_exact_out_pools(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
    )
    feasible_pools = tuple(pool for pool, _cap, _amount_in in feasible_rows)
    if not feasible_pools:
        raise ValueError("no feasible pools for repaired full-domain certification")
    if len(feasible_pools) > int(max_full_domain_pools):
        raise ValueError("repaired full-domain certification exceeded max_full_domain_pools")
    full_domain = _kernel_build_exact_out_many_pool_selected_domain(
        feasible_pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_enumerated_candidates=int(max_enumerated_candidates),
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
    selected_domain_contract = build_exact_out_many_pool_repaired_selected_domain_oracle_contract(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_candidate_pools=int(max_candidate_pools),
        max_candidates=int(max_candidates),
        max_iters=int(max_iters),
        window=int(window),
        brute_force_max=int(brute_force_max),
        max_full_domain_pools=int(max_full_domain_pools),
        max_enumerated_candidates=int(max_enumerated_candidates),
    )
    repaired_full_domain_packet = build_exact_out_many_pool_repaired_full_domain_certified_packet(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_candidate_pools=int(max_candidate_pools),
        max_candidates=int(max_candidates),
        max_iters=int(max_iters),
        window=int(window),
        brute_force_max=int(brute_force_max),
        max_full_domain_pools=int(max_full_domain_pools),
        max_enumerated_candidates=int(max_enumerated_candidates),
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
    key_cover_packet = build_exact_out_many_pool_repaired_key_cover_packet(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_candidate_pools=int(max_candidate_pools),
        max_candidates=int(max_candidates),
        max_iters=int(max_iters),
        window=int(window),
        brute_force_max=int(brute_force_max),
        max_full_domain_pools=int(max_full_domain_pools),
        max_enumerated_candidates=int(max_enumerated_candidates),
    )
    return _build_exact_out_many_pool_repaired_key_cover_interpretation_packet_from_key_cover_packet(
        key_cover_packet
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
    if not asset_in or not asset_out or asset_in == asset_out:
        raise ValueError("asset_in and asset_out must be non-empty and distinct")
    candidates = enumerate_exact_out_many_pool_candidates(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_candidate_pools=int(max_candidate_pools),
        max_enumerated_candidates=int(max_enumerated_candidates),
    )
    audit_pool_ids = tuple(
        sorted(
            {
                leg.pool_id
                for candidate in candidates
                for leg in candidate.legs
            }
        )
    )
    audit_pool_id_set = set(audit_pool_ids)
    candidate_domain_nonempty = bool(candidates)
    audit_pool_ids_sorted_unique = _audit_pool_ids_sorted_unique(audit_pool_ids)
    audit_pool_ids_within_budget = len(audit_pool_ids) <= int(max_candidate_pools)
    all_candidates_complete = all(
        _quote_is_complete_exact_out_candidate(candidate, amount_out_total=int(amount_out_total)) for candidate in candidates
    )
    all_candidates_leg_bounded = all(1 <= len(candidate.legs) <= int(max_legs) for candidate in candidates)
    all_candidates_leg_pool_ids_sorted_unique = all(_quote_leg_pool_ids_sorted_unique(candidate) for candidate in candidates)
    all_candidates_within_audit_pool_ids = all(
        all(leg.pool_id in audit_pool_id_set for leg in candidate.legs) for candidate in candidates
    )
    candidate_count_within_budget = len(candidates) <= int(max_enumerated_candidates)
    contract_ok = (
        candidate_domain_nonempty
        and audit_pool_ids_sorted_unique
        and audit_pool_ids_within_budget
        and all_candidates_complete
        and all_candidates_leg_bounded
        and all_candidates_leg_pool_ids_sorted_unique
        and all_candidates_within_audit_pool_ids
        and candidate_count_within_budget
    )
    return ExactOutManyPoolCandidateDomainContract(
        asset_in=str(asset_in),
        asset_out=str(asset_out),
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_candidate_pools=int(max_candidate_pools),
        max_enumerated_candidates=int(max_enumerated_candidates),
        audit_pool_ids=audit_pool_ids,
        pool_snapshots=tuple(_pool_to_dict(pool) for pool in pools),
        candidates=tuple(candidates),
        candidate_count=len(candidates),
        audit_pool_ids_sorted_unique=bool(audit_pool_ids_sorted_unique),
        audit_pool_ids_within_budget=bool(audit_pool_ids_within_budget),
        candidate_domain_nonempty=bool(candidate_domain_nonempty),
        all_candidates_complete=bool(all_candidates_complete),
        all_candidates_leg_bounded=bool(all_candidates_leg_bounded),
        all_candidates_leg_pool_ids_sorted_unique=bool(all_candidates_leg_pool_ids_sorted_unique),
        all_candidates_within_audit_pool_ids=bool(all_candidates_within_audit_pool_ids),
        candidate_count_within_budget=bool(candidate_count_within_budget),
        contract_ok=bool(contract_ok),
    )


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
            amount_out_total=int(payload["amount_out_total"]),
            max_legs=int(payload["max_legs"]),
            max_candidate_pools=int(payload["max_candidate_pools"]),
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
            amount_out_total=int(payload["amount_out_total"]),
            max_legs=int(payload["max_legs"]),
            max_candidate_pools=int(payload["max_candidate_pools"]),
            max_full_domain_pools=int(payload["max_full_domain_pools"]),
            max_enumerated_candidates=int(payload["max_enumerated_candidates"]),
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
    candidates = enumerate_exact_out_two_pool_candidates(
        pool0,
        pool1,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
    )
    certificate = build_exact_out_route_canonical_certificate(candidates)
    runtime_quote = best_split_two_pools_exact_out_for_pools(
        pool0,
        pool1,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        brute_force_max=(max(0, int(brute_force_max)) if brute_force_max is not None else max(1, int(amount_out_total))),
    )
    runtime_many = split_two_pools_exact_out_quote_to_many(runtime_quote)
    return ExactOutTwoPoolCanonicalityAudit(
        runtime_matches_canonical=runtime_many == certificate.winner_quote,
        runtime_quote=runtime_many,
        canonical_winner_quote=certificate.winner_quote,
        candidate_count=len(candidates),
        certificate=certificate,
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
    bounded = _kernel_bounded_exact_out_many_pool_runtime_domain(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_candidate_pools=int(max_candidate_pools),
        max_candidates=int(max_candidates),
        max_iters=int(max_iters),
        window=int(window),
        brute_force_max=int(brute_force_max),
        max_full_domain_pools=int(max_full_domain_pools),
        max_enumerated_candidates=int(max_enumerated_candidates),
    )
    candidates = bounded.candidates
    certificate = build_exact_out_route_canonical_certificate(candidates)
    runtime_quote = bounded.runtime_quote
    canonical_quote = bounded.canonical_quote
    audit_pool_ids = bounded.audit_pool_ids
    pools_by_id = {pool.pool_id: pool for pool in pools}
    selected_pools = tuple(
        pools_by_id[pool_id]
        for pool_id in audit_pool_ids
        if pool_id in pools_by_id
    )
    projection_cover_audit: ExactOutManyPoolProjectionCoverAudit | None = None
    if len(selected_pools) == len(audit_pool_ids):
        try:
            kernel_projection_audit = _kernel_audit_exact_out_many_pool_selected_domain_projection_cover(
                selected_pools,
                asset_in=asset_in,
                asset_out=asset_out,
                amount_out_total=int(amount_out_total),
                max_legs=int(max_legs),
                max_selected_pools=max(len(selected_pools), 1),
                max_enumerated_candidates=int(max_enumerated_candidates),
            )
        except ValueError:
            kernel_projection_audit = None
        if kernel_projection_audit is not None:
            projection_cover_audit = _projection_cover_audit_from_kernel(kernel_projection_audit)
    return ExactOutManyPoolCanonicalityAudit(
        runtime_matches_canonical=runtime_quote == canonical_quote,
        runtime_quote=runtime_quote,
        canonical_winner_quote=canonical_quote,
        candidate_count=len(candidates),
        audit_pool_ids=audit_pool_ids,
        max_legs=int(max_legs),
        certificate=certificate,
        projection_cover_audit=projection_cover_audit,
    )


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
    if not asset_in or not asset_out or asset_in == asset_out:
        raise ValueError("asset_in and asset_out must be non-empty and distinct")
    audit = audit_exact_out_many_pool_runtime_canonicality(
        pools,
        asset_in=str(asset_in),
        asset_out=str(asset_out),
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_candidate_pools=int(max_candidate_pools),
        max_candidates=int(max_candidates),
        max_iters=int(max_iters),
        window=int(window),
        brute_force_max=int(brute_force_max),
        max_full_domain_pools=int(max_full_domain_pools),
        max_enumerated_candidates=int(max_enumerated_candidates),
    )
    return ExactOutManyPoolOracleContract(
        asset_in=str(asset_in),
        asset_out=str(asset_out),
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_candidate_pools=int(max_candidate_pools),
        max_candidates=int(max_candidates),
        max_iters=int(max_iters),
        window=int(window),
        brute_force_max=int(brute_force_max),
        max_full_domain_pools=int(max_full_domain_pools),
        max_enumerated_candidates=int(max_enumerated_candidates),
        pool_snapshots=tuple(_pool_to_dict(pool) for pool in pools),
        audit=audit,
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
    repaired_contract = build_exact_out_many_pool_repaired_prefilter_contract(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_candidate_pools=int(max_candidate_pools),
        max_full_domain_pools=int(max_full_domain_pools),
        max_enumerated_candidates=int(max_enumerated_candidates),
    )
    if repaired_contract.contract_ok:
        repaired_selected_pools = _repaired_selected_pools_from_contract(
            pools,
            repaired_contract=repaired_contract,
        )
        audit = audit_exact_out_many_pool_runtime_canonicality(
            repaired_selected_pools,
            asset_in=str(asset_in),
            asset_out=str(asset_out),
            amount_out_total=int(amount_out_total),
            max_legs=int(max_legs),
            max_candidate_pools=max(len(repaired_selected_pools), 1),
            max_candidates=int(max_candidates),
            max_iters=int(max_iters),
            window=int(window),
            brute_force_max=int(brute_force_max),
            max_full_domain_pools=max(len(repaired_selected_pools), int(max_full_domain_pools)),
            max_enumerated_candidates=int(max_enumerated_candidates),
        )
    else:
        audit = audit_exact_out_many_pool_runtime_canonicality(
            tuple(pools),
            asset_in=str(asset_in),
            asset_out=str(asset_out),
            amount_out_total=int(amount_out_total),
            max_legs=int(max_legs),
            max_candidate_pools=int(max_candidate_pools),
            max_candidates=int(max_candidates),
            max_iters=int(max_iters),
            window=int(window),
            brute_force_max=int(brute_force_max),
            max_full_domain_pools=int(max_full_domain_pools),
            max_enumerated_candidates=int(max_enumerated_candidates),
        )
    audit_pool_ids_match_repaired_selected_pool_ids = bool(
        tuple(audit.audit_pool_ids) == tuple(repaired_contract.repaired_selected_pool_ids)
    )
    contract_ok = bool(
        repaired_contract.contract_ok
        and audit_pool_ids_match_repaired_selected_pool_ids
        and audit.runtime_matches_canonical
    )
    return ExactOutManyPoolRepairedSelectedDomainOracleContract(
        asset_in=str(asset_in),
        asset_out=str(asset_out),
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_candidate_pools=int(max_candidate_pools),
        max_candidates=int(max_candidates),
        max_iters=int(max_iters),
        window=int(window),
        brute_force_max=int(brute_force_max),
        max_full_domain_pools=int(max_full_domain_pools),
        max_enumerated_candidates=int(max_enumerated_candidates),
        pool_snapshots=tuple(_pool_to_dict(pool) for pool in pools),
        repaired_contract=repaired_contract,
        audit=audit,
        audit_pool_ids_match_repaired_selected_pool_ids=bool(audit_pool_ids_match_repaired_selected_pool_ids),
        contract_ok=bool(contract_ok),
    )


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
    contract = build_exact_out_many_pool_repaired_selected_domain_oracle_contract(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_candidate_pools=int(max_candidate_pools),
        max_candidates=int(max_candidates),
        max_iters=int(max_iters),
        window=int(window),
        brute_force_max=int(brute_force_max),
        max_full_domain_pools=int(max_full_domain_pools),
        max_enumerated_candidates=int(max_enumerated_candidates),
    )
    if contract.contract_ok:
        return contract.audit.runtime_quote, None, contract
    return None, EXACT_OUT_MANY_POOL_REPAIRED_SELECTED_DOMAIN_UNAVAILABLE_ERROR, contract


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
    repaired_contract = build_exact_out_many_pool_repaired_prefilter_contract(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_candidate_pools=int(max_candidate_pools),
        max_full_domain_pools=int(max_full_domain_pools),
        max_enumerated_candidates=int(max_enumerated_candidates),
    )
    runtime_quote = best_split_many_pools_exact_out_for_pools(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_candidates=int(max_candidates),
        max_iters=int(max_iters),
        window=int(window),
        brute_force_max=int(brute_force_max),
    )
    if not repaired_contract.contract_ok:
        return ExactOutManyPoolRepairedAdvisoryQuotePacket(
            packet_ok=False,
            advisory_quote=None,
            runtime_quote=runtime_quote,
            runtime_matches_advisory=False,
            error=EXACT_OUT_MANY_POOL_REPAIRED_ADVISORY_UNAVAILABLE_ERROR,
            max_candidates=int(max_candidates),
            max_iters=int(max_iters),
            window=int(window),
            brute_force_max=int(brute_force_max),
            repaired_contract=repaired_contract,
            projection_cover_audit=None,
        )

    repaired_selected_pools = _repaired_selected_pools_from_contract(
        pools,
        repaired_contract=repaired_contract,
    )
    repaired_selected_domain = _kernel_build_exact_out_many_pool_selected_domain(
        repaired_selected_pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_enumerated_candidates=int(max_enumerated_candidates),
    )
    projection_cover_audit: ExactOutManyPoolProjectionCoverAudit | None = None
    try:
        kernel_projection_audit = _kernel_audit_exact_out_many_pool_selected_domain_projection_cover(
            repaired_selected_pools,
            asset_in=asset_in,
            asset_out=asset_out,
            amount_out_total=int(amount_out_total),
            max_legs=int(max_legs),
            max_selected_pools=max(len(repaired_selected_pools), 1),
            max_enumerated_candidates=int(max_enumerated_candidates),
        )
        projection_cover_audit = _projection_cover_audit_from_kernel(kernel_projection_audit)
    except Exception:
        projection_cover_audit = None
    advisory_quote = _candidate_quote_to_core_quote(repaired_selected_domain.canonical_quote)
    runtime_matches_advisory = runtime_quote == advisory_quote
    return ExactOutManyPoolRepairedAdvisoryQuotePacket(
        packet_ok=True,
        advisory_quote=advisory_quote,
        runtime_quote=runtime_quote,
        runtime_matches_advisory=bool(runtime_matches_advisory),
        error=None,
        max_candidates=int(max_candidates),
        max_iters=int(max_iters),
        window=int(window),
        brute_force_max=int(brute_force_max),
        repaired_contract=repaired_contract,
        projection_cover_audit=projection_cover_audit,
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
    packet = build_exact_out_many_pool_repaired_advisory_quote_packet(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_candidate_pools=int(max_candidate_pools),
        max_candidates=int(max_candidates),
        max_iters=int(max_iters),
        window=int(window),
        brute_force_max=int(brute_force_max),
        max_full_domain_pools=int(max_full_domain_pools),
        max_enumerated_candidates=int(max_enumerated_candidates),
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
    feasible_pool_ids, full_candidates, full_domain_certificate = _build_exact_out_many_pool_full_domain_certificate(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_full_domain_pools=int(max_full_domain_pools),
        max_enumerated_candidates=int(max_enumerated_candidates),
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
    repaired_packet = build_exact_out_many_pool_repaired_advisory_quote_packet(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_candidate_pools=int(max_candidate_pools),
        max_candidates=int(max_candidates),
        max_iters=int(max_iters),
        window=int(window),
        brute_force_max=int(brute_force_max),
        max_full_domain_pools=int(max_full_domain_pools),
        max_enumerated_candidates=int(max_enumerated_candidates),
    )
    return _build_exact_out_many_pool_repaired_full_domain_certified_packet_from_repaired_packet(
        repaired_packet,
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_full_domain_pools=int(max_full_domain_pools),
        max_enumerated_candidates=int(max_enumerated_candidates),
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
    packet = build_exact_out_many_pool_repaired_full_domain_certified_packet(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_candidate_pools=int(max_candidate_pools),
        max_candidates=int(max_candidates),
        max_iters=int(max_iters),
        window=int(window),
        brute_force_max=int(brute_force_max),
        max_full_domain_pools=int(max_full_domain_pools),
        max_enumerated_candidates=int(max_enumerated_candidates),
    )
    if packet.packet_ok:
        return packet.repaired_quote, None, packet
    return None, str(packet.error or EXACT_OUT_MANY_POOL_REPAIRED_FULL_DOMAIN_CERTIFIED_ERROR), packet


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
    oracle_contract = build_exact_out_many_pool_oracle_contract(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_candidate_pools=int(max_candidate_pools),
        max_candidates=int(max_candidates),
        max_iters=int(max_iters),
        window=int(window),
        brute_force_max=int(brute_force_max),
        max_full_domain_pools=int(max_full_domain_pools),
        max_enumerated_candidates=int(max_enumerated_candidates),
    )
    repaired_packet = build_exact_out_many_pool_repaired_advisory_quote_packet(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_candidate_pools=int(max_candidate_pools),
        max_candidates=int(max_candidates),
        max_iters=int(max_iters),
        window=int(window),
        brute_force_max=int(brute_force_max),
        max_full_domain_pools=int(max_full_domain_pools),
        max_enumerated_candidates=int(max_enumerated_candidates),
    )
    repaired_full_domain_packet = _build_exact_out_many_pool_repaired_full_domain_certified_packet_from_repaired_packet(
        repaired_packet,
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_full_domain_pools=int(max_full_domain_pools),
        max_enumerated_candidates=int(max_enumerated_candidates),
    )
    runtime_quotes_agree = oracle_contract.audit.runtime_quote == repaired_full_domain_packet.repaired_packet.runtime_quote
    runtime_matches_repaired_advisory = bool(
        runtime_quotes_agree
        and repaired_full_domain_packet.repaired_quote is not None
        and oracle_contract.audit.runtime_quote == repaired_full_domain_packet.repaired_quote
    )
    packet_ok = bool(
        oracle_contract.audit.runtime_matches_canonical
        and repaired_full_domain_packet.packet_ok
        and runtime_quotes_agree
    )
    return ExactOutManyPoolBoundedWorkaroundPacket(
        oracle_contract=oracle_contract,
        repaired_packet=repaired_packet,
        repaired_full_domain_packet=repaired_full_domain_packet,
        runtime_quotes_agree=bool(runtime_quotes_agree),
        runtime_matches_repaired_advisory=bool(runtime_matches_repaired_advisory),
        packet_ok=bool(packet_ok),
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
    workaround_packet = build_exact_out_many_pool_bounded_workaround_packet(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_candidate_pools=int(max_candidate_pools),
        max_candidates=int(max_candidates),
        max_iters=int(max_iters),
        window=int(window),
        brute_force_max=int(brute_force_max),
        max_full_domain_pools=int(max_full_domain_pools),
        max_enumerated_candidates=int(max_enumerated_candidates),
    )
    if not workaround_packet.oracle_contract.audit.runtime_matches_canonical:
        return ExactOutManyPoolBoundedAdvisoryQuotePacket(
            packet_ok=False,
            advisory_quote=None,
            quote_source=None,
            repaired_advisory_available=bool(workaround_packet.repaired_full_domain_packet.packet_ok),
            quote_matches_runtime=False,
            quote_matches_repaired_advisory=False,
            error=EXACT_OUT_MANY_POOL_GUARD_MISMATCH_ERROR,
            workaround_packet=workaround_packet,
        )
    if not workaround_packet.runtime_quotes_agree:
        return ExactOutManyPoolBoundedAdvisoryQuotePacket(
            packet_ok=False,
            advisory_quote=None,
            quote_source=None,
            repaired_advisory_available=bool(workaround_packet.repaired_full_domain_packet.packet_ok),
            quote_matches_runtime=False,
            quote_matches_repaired_advisory=False,
            error=EXACT_OUT_MANY_POOL_RUNTIME_QUOTE_INCONSISTENCY_ERROR,
            workaround_packet=workaround_packet,
        )

    runtime_quote = workaround_packet.oracle_contract.audit.runtime_quote
    repaired_full_domain_packet = workaround_packet.repaired_full_domain_packet
    repaired_advisory_available = bool(
        repaired_full_domain_packet.packet_ok and repaired_full_domain_packet.repaired_quote is not None
    )
    use_repaired_advisory = bool(
        repaired_advisory_available and not workaround_packet.runtime_matches_repaired_advisory
    )
    advisory_quote = repaired_full_domain_packet.repaired_quote if use_repaired_advisory else runtime_quote
    quote_source = "repaired_bounded_advisory" if use_repaired_advisory else "selected_domain_runtime"
    return ExactOutManyPoolBoundedAdvisoryQuotePacket(
        packet_ok=True,
        advisory_quote=advisory_quote,
        quote_source=quote_source,
        repaired_advisory_available=bool(repaired_advisory_available),
        quote_matches_runtime=bool(advisory_quote == runtime_quote),
        quote_matches_repaired_advisory=bool(
            repaired_full_domain_packet.repaired_quote is not None and advisory_quote == repaired_full_domain_packet.repaired_quote
        ),
        error=None,
        workaround_packet=workaround_packet,
    )


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
    packet = build_exact_out_many_pool_bounded_advisory_quote_packet(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_candidate_pools=int(max_candidate_pools),
        max_candidates=int(max_candidates),
        max_iters=int(max_iters),
        window=int(window),
        brute_force_max=int(brute_force_max),
        max_full_domain_pools=int(max_full_domain_pools),
        max_enumerated_candidates=int(max_enumerated_candidates),
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
    return quote_exact_out_many_pool_certified_advisory(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_candidate_pools=int(max_candidate_pools),
        max_candidates=int(max_candidates),
        max_iters=int(max_iters),
        window=int(window),
        brute_force_max=int(brute_force_max),
        max_full_domain_pools=int(max_full_domain_pools),
        max_enumerated_candidates=int(max_enumerated_candidates),
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
    return build_exact_out_many_pool_certified_advisory_packet(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_candidate_pools=int(max_candidate_pools),
        max_candidates=int(max_candidates),
        max_iters=int(max_iters),
        window=int(window),
        brute_force_max=int(brute_force_max),
        max_full_domain_pools=int(max_full_domain_pools),
        max_enumerated_candidates=int(max_enumerated_candidates),
    )


def _exact_out_many_pool_budget_parameters_bound(
    packet: ExactOutManyPoolCertifiedAdvisoryPacket,
    *,
    max_legs: int,
    max_candidate_pools: int,
    max_candidates: int,
    max_iters: int,
    window: int,
    brute_force_max: int,
    max_full_domain_pools: int,
    max_enumerated_candidates: int,
) -> bool:
    domain_contract = packet.certified_packet.domain_contract
    guarded_contract = packet.certified_packet.guarded_packet.contract
    selected_domain_contract = packet.repaired_key_cover_packet.selected_domain_contract
    advisory_packet = packet.advisory_packet
    oracle_contract = advisory_packet.workaround_packet.oracle_contract
    repaired_packet = advisory_packet.workaround_packet.repaired_packet
    repaired_contract = repaired_packet.repaired_contract
    expected_domain_bounds = (
        int(max_legs),
        int(max_candidate_pools),
        int(max_enumerated_candidates),
    )
    expected_runtime_bounds = (
        int(max_legs),
        int(max_candidate_pools),
        int(max_candidates),
        int(max_iters),
        int(window),
        int(brute_force_max),
        int(max_full_domain_pools),
        int(max_enumerated_candidates),
    )
    return (
        (int(domain_contract.max_legs), int(domain_contract.max_candidate_pools), int(domain_contract.max_enumerated_candidates))
        == expected_domain_bounds
        and (
            int(guarded_contract.max_legs),
            int(guarded_contract.max_candidate_pools),
            int(guarded_contract.max_candidates),
            int(guarded_contract.max_iters),
            int(guarded_contract.window),
            int(guarded_contract.brute_force_max),
            int(guarded_contract.max_full_domain_pools),
            int(guarded_contract.max_enumerated_candidates),
        )
        == expected_runtime_bounds
        and (
            int(selected_domain_contract.max_legs),
            int(selected_domain_contract.max_candidate_pools),
            int(selected_domain_contract.max_candidates),
            int(selected_domain_contract.max_iters),
            int(selected_domain_contract.window),
            int(selected_domain_contract.brute_force_max),
            int(selected_domain_contract.max_full_domain_pools),
            int(selected_domain_contract.max_enumerated_candidates),
        )
        == expected_runtime_bounds
        and (
            int(oracle_contract.max_legs),
            int(oracle_contract.max_candidate_pools),
            int(oracle_contract.max_candidates),
            int(oracle_contract.max_iters),
            int(oracle_contract.window),
            int(oracle_contract.brute_force_max),
            int(oracle_contract.max_full_domain_pools),
            int(oracle_contract.max_enumerated_candidates),
        )
        == expected_runtime_bounds
        and (
            int(repaired_packet.max_candidates),
            int(repaired_packet.max_iters),
            int(repaired_packet.window),
            int(repaired_packet.brute_force_max),
        )
        == (
            int(max_candidates),
            int(max_iters),
            int(window),
            int(brute_force_max),
        )
        and (
            int(repaired_contract.max_legs),
            int(repaired_contract.max_candidate_pools),
            int(repaired_contract.max_full_domain_pools),
            int(repaired_contract.max_enumerated_candidates),
        )
        == (
            int(max_legs),
            int(max_candidate_pools),
            int(max_full_domain_pools),
            int(max_enumerated_candidates),
        )
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
    certified_advisory_packet = build_exact_out_many_pool_certified_advisory_packet(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_candidate_pools=int(max_candidate_pools),
        max_candidates=int(max_candidates),
        max_iters=int(max_iters),
        window=int(window),
        brute_force_max=int(brute_force_max),
        max_full_domain_pools=int(max_full_domain_pools),
        max_enumerated_candidates=int(max_enumerated_candidates),
    )
    domain_contract = certified_advisory_packet.certified_packet.domain_contract
    repaired_contract = certified_advisory_packet.advisory_packet.workaround_packet.repaired_packet.repaired_contract
    repaired_full_domain_packet = certified_advisory_packet.advisory_packet.workaround_packet.repaired_full_domain_packet
    selected_domain_budget_respected = bool(
        domain_contract.audit_pool_ids_within_budget
        and domain_contract.candidate_count_within_budget
    )
    repaired_selection_budget_respected = bool(
        repaired_contract.repaired_selected_pool_ids_within_budget
    )
    full_domain_pool_budget_respected = bool(
        len(repaired_full_domain_packet.full_domain_feasible_pool_ids) <= int(max_full_domain_pools)
    )
    full_domain_candidate_budget_respected = bool(
        int(repaired_full_domain_packet.full_domain_candidate_count) <= int(max_enumerated_candidates)
    )
    budget_parameters_bound = _exact_out_many_pool_budget_parameters_bound(
        certified_advisory_packet,
        max_legs=int(max_legs),
        max_candidate_pools=int(max_candidate_pools),
        max_candidates=int(max_candidates),
        max_iters=int(max_iters),
        window=int(window),
        brute_force_max=int(brute_force_max),
        max_full_domain_pools=int(max_full_domain_pools),
        max_enumerated_candidates=int(max_enumerated_candidates),
    )
    failure_path_explicit = bool(
        certified_advisory_packet.packet_ok
        or not certified_advisory_packet.certified_packet.packet_ok
        or (
            not certified_advisory_packet.advisory_packet.packet_ok
            and certified_advisory_packet.advisory_packet.error is not None
        )
        or not certified_advisory_packet.selected_runtime_quotes_agree
    )
    success_path_replayable = bool(
        not certified_advisory_packet.packet_ok
        or (
            certified_advisory_packet.advisory_packet.advisory_quote is not None
            and certified_advisory_packet.advisory_packet.quote_source is not None
            and certified_advisory_packet.advisory_packet.error is None
        )
    )
    contract_ok = bool(
        selected_domain_budget_respected
        and repaired_selection_budget_respected
        and full_domain_pool_budget_respected
        and full_domain_candidate_budget_respected
        and budget_parameters_bound
        and failure_path_explicit
        and success_path_replayable
    )
    return ExactOutManyPoolAuditedBoundsContract(
        asset_in=str(asset_in),
        asset_out=str(asset_out),
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_candidate_pools=int(max_candidate_pools),
        max_candidates=int(max_candidates),
        max_iters=int(max_iters),
        window=int(window),
        brute_force_max=int(brute_force_max),
        max_full_domain_pools=int(max_full_domain_pools),
        max_enumerated_candidates=int(max_enumerated_candidates),
        pool_snapshots=tuple(_pool_to_dict(pool) for pool in pools),
        certified_advisory_packet=certified_advisory_packet,
        selected_domain_budget_respected=bool(selected_domain_budget_respected),
        repaired_selection_budget_respected=bool(repaired_selection_budget_respected),
        full_domain_pool_budget_respected=bool(full_domain_pool_budget_respected),
        full_domain_candidate_budget_respected=bool(full_domain_candidate_budget_respected),
        budget_parameters_bound=bool(budget_parameters_bound),
        failure_path_explicit=bool(failure_path_explicit),
        success_path_replayable=bool(success_path_replayable),
        contract_ok=bool(contract_ok),
    )


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
    audited_bounds_contract = build_exact_out_many_pool_audited_bounds_contract(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_candidate_pools=int(max_candidate_pools),
        max_candidates=int(max_candidates),
        max_iters=int(max_iters),
        window=int(window),
        brute_force_max=int(brute_force_max),
        max_full_domain_pools=int(max_full_domain_pools),
        max_enumerated_candidates=int(max_enumerated_candidates),
    )
    default_packet = audited_bounds_contract.certified_advisory_packet
    repaired_full_domain_packet = default_packet.advisory_packet.workaround_packet.repaired_full_domain_packet

    cheap_path_attempted = True
    cheap_path_success = bool(default_packet.packet_ok and default_packet.advisory_packet.advisory_quote is not None)
    fallback_required = not cheap_path_success
    fallback_attempted = fallback_required
    fallback_available = bool(
        repaired_full_domain_packet.packet_ok and repaired_full_domain_packet.repaired_quote is not None
    )
    fallback_success = bool(fallback_attempted and fallback_available)
    returned_success = bool(cheap_path_success or fallback_success)
    explicit_failure = not returned_success

    if cheap_path_success:
        effective_quote_source = "default_certified_advisory"
        effective_quote = default_packet.advisory_packet.advisory_quote
        failure_reason = None
        nested_error = None
    elif fallback_success:
        effective_quote_source = "repaired_full_domain"
        effective_quote = repaired_full_domain_packet.repaired_quote
        failure_reason = None
        nested_error = None
    else:
        effective_quote_source = None
        effective_quote = None
        default_error = _exact_out_many_pool_certified_advisory_packet_error(default_packet)
        fallback_error = None if fallback_available else repaired_full_domain_packet.error
        if not audited_bounds_contract.contract_ok:
            failure_reason = EXACT_OUT_MANY_POOL_ADAPTIVE_FAILURE_AUDITED_BOUNDS_CONTRACT_NOT_OK
        elif not default_packet.packet_ok:
            failure_reason = EXACT_OUT_MANY_POOL_ADAPTIVE_FAILURE_DEFAULT_PACKET_NOT_OK
        elif not repaired_full_domain_packet.packet_ok:
            failure_reason = EXACT_OUT_MANY_POOL_ADAPTIVE_FAILURE_REPAIRED_FULL_DOMAIN_PACKET_NOT_OK
        else:
            failure_reason = EXACT_OUT_MANY_POOL_ADAPTIVE_FAILURE_REPLAYABLE_QUOTE_MISSING
        nested_error = str(fallback_error or default_error or failure_reason)

    failure_reason_present = bool(failure_reason is not None)
    no_spurious_failure = bool((not explicit_failure) or (not fallback_available))
    packet_ok = bool(
        repaired_full_domain_packet
        == default_packet.advisory_packet.workaround_packet.repaired_full_domain_packet
        and cheap_path_attempted
        and fallback_required == (not cheap_path_success)
        and fallback_attempted == fallback_required
        and fallback_success == (fallback_attempted and fallback_available)
        and returned_success == (cheap_path_success or fallback_success)
        and explicit_failure == (not returned_success)
        and failure_reason_present == (failure_reason is not None)
        and no_spurious_failure == ((not explicit_failure) or (not fallback_available))
        and (
            (
                returned_success
                and effective_quote_source is not None
                and effective_quote is not None
                and failure_reason is None
            )
            or (
                explicit_failure
                and effective_quote_source is None
                and effective_quote is None
                and failure_reason is not None
            )
        )
    )
    liveness_ok = bool(packet_ok and audited_bounds_contract.contract_ok and no_spurious_failure)
    return ExactOutManyPoolAdaptiveLivenessPacket(
        audited_bounds_contract=audited_bounds_contract,
        repaired_full_domain_packet=repaired_full_domain_packet,
        cheap_path_attempted=bool(cheap_path_attempted),
        cheap_path_success=bool(cheap_path_success),
        fallback_required=bool(fallback_required),
        fallback_attempted=bool(fallback_attempted),
        fallback_available=bool(fallback_available),
        fallback_success=bool(fallback_success),
        returned_success=bool(returned_success),
        explicit_failure=bool(explicit_failure),
        failure_reason_present=bool(failure_reason_present),
        no_spurious_failure=bool(no_spurious_failure),
        effective_quote_source=effective_quote_source,
        effective_quote=effective_quote,
        failure_reason=failure_reason,
        nested_error=nested_error,
        packet_ok=bool(packet_ok),
        liveness_ok=bool(liveness_ok),
    )


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
    packet = build_exact_out_many_pool_adaptive_liveness_packet(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_candidate_pools=int(max_candidate_pools),
        max_candidates=int(max_candidates),
        max_iters=int(max_iters),
        window=int(window),
        brute_force_max=int(brute_force_max),
        max_full_domain_pools=int(max_full_domain_pools),
        max_enumerated_candidates=int(max_enumerated_candidates),
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
            amount_out_total=int(payload["amount_out_total"]),
            max_legs=int(payload["max_legs"]),
            max_candidate_pools=int(payload["max_candidate_pools"]),
            max_candidates=int(payload["max_candidates"]),
            max_iters=int(payload["max_iters"]),
            window=int(payload["window"]),
            brute_force_max=int(payload["brute_force_max"]),
            max_full_domain_pools=int(payload["max_full_domain_pools"]),
            max_enumerated_candidates=int(payload["max_enumerated_candidates"]),
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
            amount_out_total=int(contract_payload["amount_out_total"]),
            max_legs=int(contract_payload["max_legs"]),
            max_candidate_pools=int(contract_payload["max_candidate_pools"]),
            max_candidates=int(contract_payload["max_candidates"]),
            max_iters=int(contract_payload["max_iters"]),
            window=int(contract_payload["window"]),
            brute_force_max=int(contract_payload["brute_force_max"]),
            max_full_domain_pools=int(contract_payload["max_full_domain_pools"]),
            max_enumerated_candidates=int(contract_payload["max_enumerated_candidates"]),
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
            amount_out_total=int(payload["amount_out_total"]),
            max_legs=int(payload["max_legs"]),
            max_candidate_pools=int(payload["max_candidate_pools"]),
            max_enumerated_candidates=int(payload["max_enumerated_candidates"]),
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
    contract = build_exact_out_many_pool_oracle_contract(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_candidate_pools=int(max_candidate_pools),
        max_candidates=int(max_candidates),
        max_iters=int(max_iters),
        window=int(window),
        brute_force_max=int(brute_force_max),
        max_full_domain_pools=int(max_full_domain_pools),
        max_enumerated_candidates=int(max_enumerated_candidates),
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
    ok, err, contract = guard_exact_out_many_pool_runtime_canonicality(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_candidate_pools=int(max_candidate_pools),
        max_candidates=int(max_candidates),
        max_iters=int(max_iters),
        window=int(window),
        brute_force_max=int(brute_force_max),
        max_full_domain_pools=int(max_full_domain_pools),
        max_enumerated_candidates=int(max_enumerated_candidates),
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
    quote, err, contract = quote_exact_out_many_pool_guarded(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_candidate_pools=int(max_candidate_pools),
        max_candidates=int(max_candidates),
        max_iters=int(max_iters),
        window=int(window),
        brute_force_max=int(brute_force_max),
        max_full_domain_pools=int(max_full_domain_pools),
        max_enumerated_candidates=int(max_enumerated_candidates),
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
    domain_contract = build_exact_out_many_pool_candidate_domain_contract(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_candidate_pools=int(max_candidate_pools),
        max_enumerated_candidates=int(max_enumerated_candidates),
    )
    guarded_packet = build_exact_out_many_pool_guarded_quote_packet(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_candidate_pools=int(max_candidate_pools),
        max_candidates=int(max_candidates),
        max_iters=int(max_iters),
        window=int(window),
        brute_force_max=int(brute_force_max),
        max_full_domain_pools=int(max_full_domain_pools),
        max_enumerated_candidates=int(max_enumerated_candidates),
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
    certified_packet = build_exact_out_many_pool_certified_winner_packet(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_candidate_pools=int(max_candidate_pools),
        max_candidates=int(max_candidates),
        max_iters=int(max_iters),
        window=int(window),
        brute_force_max=int(brute_force_max),
        max_full_domain_pools=int(max_full_domain_pools),
        max_enumerated_candidates=int(max_enumerated_candidates),
    )
    advisory_packet = build_exact_out_many_pool_bounded_advisory_quote_packet(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_candidate_pools=int(max_candidate_pools),
        max_candidates=int(max_candidates),
        max_iters=int(max_iters),
        window=int(window),
        brute_force_max=int(brute_force_max),
        max_full_domain_pools=int(max_full_domain_pools),
        max_enumerated_candidates=int(max_enumerated_candidates),
    )
    selected_domain_contract = build_exact_out_many_pool_repaired_selected_domain_oracle_contract(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_candidate_pools=int(max_candidate_pools),
        max_candidates=int(max_candidates),
        max_iters=int(max_iters),
        window=int(window),
        brute_force_max=int(brute_force_max),
        max_full_domain_pools=int(max_full_domain_pools),
        max_enumerated_candidates=int(max_enumerated_candidates),
    )
    repaired_key_cover_packet = _build_exact_out_many_pool_repaired_key_cover_packet_from_components(
        selected_domain_contract=selected_domain_contract,
        repaired_full_domain_packet=advisory_packet.workaround_packet.repaired_full_domain_packet,
    )
    repaired_key_cover_interpretation_packet = (
        _build_exact_out_many_pool_repaired_key_cover_interpretation_packet_from_key_cover_packet(
            repaired_key_cover_packet
        )
    )
    selected_runtime_quotes_agree = (
        certified_packet.guarded_packet.contract.audit.runtime_quote
        == advisory_packet.workaround_packet.oracle_contract.audit.runtime_quote
    )
    packet_ok = bool(
        certified_packet.packet_ok
        and advisory_packet.packet_ok
        and selected_runtime_quotes_agree
    )
    return ExactOutManyPoolCertifiedAdvisoryPacket(
        certified_packet=certified_packet,
        advisory_packet=advisory_packet,
        repaired_key_cover_packet=repaired_key_cover_packet,
        repaired_key_cover_interpretation_packet=repaired_key_cover_interpretation_packet,
        selected_runtime_quotes_agree=bool(selected_runtime_quotes_agree),
        packet_ok=bool(packet_ok),
    )


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
    packet = build_exact_out_many_pool_certified_advisory_packet(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_candidate_pools=int(max_candidate_pools),
        max_candidates=int(max_candidates),
        max_iters=int(max_iters),
        window=int(window),
        brute_force_max=int(brute_force_max),
        max_full_domain_pools=int(max_full_domain_pools),
        max_enumerated_candidates=int(max_enumerated_candidates),
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
    default_packet = build_exact_out_many_pool_default_packet(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_candidate_pools=int(max_candidate_pools),
        max_candidates=int(max_candidates),
        max_iters=int(max_iters),
        window=int(window),
        brute_force_max=int(brute_force_max),
        max_full_domain_pools=int(max_full_domain_pools),
        max_enumerated_candidates=int(max_enumerated_candidates),
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
    certificate: ExactOutRouteCanonicalCertificate,
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
            amount_out_total=int(domain_payload["amount_out_total"]),
            max_legs=int(domain_payload["max_legs"]),
            max_candidate_pools=int(domain_payload["max_candidate_pools"]),
            max_candidates=int(payload["guarded_packet"]["contract"]["max_candidates"]),
            max_iters=int(payload["guarded_packet"]["contract"]["max_iters"]),
            window=int(payload["guarded_packet"]["contract"]["window"]),
            brute_force_max=int(payload["guarded_packet"]["contract"]["brute_force_max"]),
            max_full_domain_pools=int(payload["guarded_packet"]["contract"]["max_full_domain_pools"]),
            max_enumerated_candidates=int(domain_payload["max_enumerated_candidates"]),
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
            amount_out_total=int(domain_payload["amount_out_total"]),
            max_legs=int(domain_payload["max_legs"]),
            max_candidate_pools=int(domain_payload["max_candidate_pools"]),
            max_candidates=int(certified_payload["guarded_packet"]["contract"]["max_candidates"]),
            max_iters=int(certified_payload["guarded_packet"]["contract"]["max_iters"]),
            window=int(certified_payload["guarded_packet"]["contract"]["window"]),
            brute_force_max=int(certified_payload["guarded_packet"]["contract"]["brute_force_max"]),
            max_full_domain_pools=int(
                workaround_payload["repaired_packet"]["repaired_contract"]["max_full_domain_pools"]
            ),
            max_enumerated_candidates=int(domain_payload["max_enumerated_candidates"]),
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
            amount_out_total=int(replacement_payload["amount_out_total"]),
            max_legs=int(replacement_payload["max_legs"]),
            max_candidate_pools=int(replacement_payload["max_candidate_pools"]),
            max_candidates=int(replacement_payload["max_candidates"]),
            max_iters=int(replacement_payload["max_iters"]),
            window=int(replacement_payload["window"]),
            brute_force_max=int(replacement_payload["brute_force_max"]),
            max_full_domain_pools=int(replacement_payload["max_full_domain_pools"]),
            max_enumerated_candidates=int(replacement_payload["max_enumerated_candidates"]),
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
            amount_out_total=int(payload["amount_out_total"]),
            max_legs=int(payload["max_legs"]),
            max_candidate_pools=int(payload["max_candidate_pools"]),
            max_candidates=int(payload["max_candidates"]),
            max_iters=int(payload["max_iters"]),
            window=int(payload["window"]),
            brute_force_max=int(payload["brute_force_max"]),
            max_full_domain_pools=int(payload["max_full_domain_pools"]),
            max_enumerated_candidates=int(payload["max_enumerated_candidates"]),
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
            amount_out_total=int(payload["amount_out_total"]),
            max_legs=int(payload["max_legs"]),
            max_candidate_pools=int(payload["max_candidate_pools"]),
            max_candidates=int(payload["max_candidates"]),
            max_iters=int(payload["max_iters"]),
            window=int(payload["window"]),
            brute_force_max=int(payload["brute_force_max"]),
            max_enumerated_candidates=int(payload["max_enumerated_candidates"]),
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
            amount_out_total=int(contract_payload["amount_out_total"]),
            max_legs=int(contract_payload["max_legs"]),
            max_candidate_pools=int(contract_payload["max_candidate_pools"]),
            max_candidates=int(contract_payload["max_candidates"]),
            max_iters=int(contract_payload["max_iters"]),
            window=int(contract_payload["window"]),
            brute_force_max=int(contract_payload["brute_force_max"]),
            max_enumerated_candidates=int(contract_payload["max_enumerated_candidates"]),
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
            amount_out_total=int(contract_payload["amount_out_total"]),
            max_legs=int(contract_payload["max_legs"]),
            max_candidate_pools=int(contract_payload["max_candidate_pools"]),
            max_candidates=int(payload["max_candidates"]),
            max_iters=int(payload["max_iters"]),
            window=int(payload["window"]),
            brute_force_max=int(payload["brute_force_max"]),
            max_full_domain_pools=int(contract_payload["max_full_domain_pools"]),
            max_enumerated_candidates=int(contract_payload["max_enumerated_candidates"]),
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
            amount_out_total=int(contract_payload["amount_out_total"]),
            max_legs=int(contract_payload["max_legs"]),
            max_candidate_pools=int(contract_payload["max_candidate_pools"]),
            max_candidates=int(repaired_payload["max_candidates"]),
            max_iters=int(repaired_payload["max_iters"]),
            window=int(repaired_payload["window"]),
            brute_force_max=int(repaired_payload["brute_force_max"]),
            max_full_domain_pools=int(contract_payload["max_full_domain_pools"]),
            max_enumerated_candidates=int(contract_payload["max_enumerated_candidates"]),
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
            amount_out_total=int(selected_domain_payload["amount_out_total"]),
            max_legs=int(selected_domain_payload["max_legs"]),
            max_candidate_pools=int(selected_domain_payload["max_candidate_pools"]),
            max_candidates=int(selected_domain_payload["max_candidates"]),
            max_iters=int(selected_domain_payload["max_iters"]),
            window=int(selected_domain_payload["window"]),
            brute_force_max=int(selected_domain_payload["brute_force_max"]),
            max_full_domain_pools=int(selected_domain_payload["max_full_domain_pools"]),
            max_enumerated_candidates=int(selected_domain_payload["max_enumerated_candidates"]),
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
            amount_out_total=int(selected_domain_payload["amount_out_total"]),
            max_legs=int(selected_domain_payload["max_legs"]),
            max_candidate_pools=int(selected_domain_payload["max_candidate_pools"]),
            max_candidates=int(selected_domain_payload["max_candidates"]),
            max_iters=int(selected_domain_payload["max_iters"]),
            window=int(selected_domain_payload["window"]),
            brute_force_max=int(selected_domain_payload["brute_force_max"]),
            max_full_domain_pools=int(selected_domain_payload["max_full_domain_pools"]),
            max_enumerated_candidates=int(selected_domain_payload["max_enumerated_candidates"]),
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
            amount_out_total=int(oracle_payload["amount_out_total"]),
            max_legs=int(oracle_payload["max_legs"]),
            max_candidate_pools=int(oracle_payload["max_candidate_pools"]),
            max_candidates=int(oracle_payload["max_candidates"]),
            max_iters=int(oracle_payload["max_iters"]),
            window=int(oracle_payload["window"]),
            brute_force_max=int(oracle_payload["brute_force_max"]),
            max_full_domain_pools=int(repaired_payload["repaired_contract"]["max_full_domain_pools"]),
            max_enumerated_candidates=int(oracle_payload["max_enumerated_candidates"]),
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
            amount_out_total=int(oracle_payload["amount_out_total"]),
            max_legs=int(oracle_payload["max_legs"]),
            max_candidate_pools=int(oracle_payload["max_candidate_pools"]),
            max_candidates=int(oracle_payload["max_candidates"]),
            max_iters=int(oracle_payload["max_iters"]),
            window=int(oracle_payload["window"]),
            brute_force_max=int(oracle_payload["brute_force_max"]),
            max_full_domain_pools=int(repaired_payload["repaired_contract"]["max_full_domain_pools"]),
            max_enumerated_candidates=int(oracle_payload["max_enumerated_candidates"]),
        )
    except (KeyError, TypeError, ValueError) as exc:
        return False, str(exc)
    if payload != expected.to_dict():
        return False, "bounded advisory quote packet payload mismatch"
    return True, None


def _projection_cover_audit_from_kernel(
    audit: _KernelExactOutManyPoolCpmmProjectionCoverAudit,
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
        reserve0=int(payload["reserve0"]),
        reserve1=int(payload["reserve1"]),
        fee_bps=int(payload["fee_bps"]),
        lp_supply=int(payload["lp_supply"]),
        status=PoolStatus[status_raw],
        created_at=int(payload["created_at"]),
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
