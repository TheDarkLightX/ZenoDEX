from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, List, Mapping, Optional, Sequence, Tuple

from src.core.routing import (
    RouteHop,
    RouteLeg,
    RouteQuote,
    _build_asset_pool_index,
    _pool_connects,
    _pool_quote_exact_in,
    _quote_key,
    best_route_exact_in_2hop,
    best_split_many_pools_exact_in_for_pools,
    best_split_two_pools_exact_in_for_pools,
)
from src.state.balances import Amount, AssetId
from src.state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex
from src.state.pools import PoolState, PoolStatus

from .tau_witness import ARGMIN_STREAM_CERTIFICATE_V1, build_argmin_stream_certificate_v1_step

EXACT_IN_ROUTE_CERTIFICATE_SCHEMA = "zenodex/exact-in-route-certificate/v1"
EXACT_IN_ROUTE_ORACLE_CONTRACT_SCHEMA = "zenodex/exact-in-route-oracle-contract/v1"
EXACT_IN_ROUTE_GUARDED_QUOTE_PACKET_SCHEMA = "zenodex/exact-in-route-guarded-quote-packet/v1"
EXACT_IN_ROUTE_RANK_PROJECTION_PACKET_SCHEMA = "zenodex/exact-in-route-rank-projection-packet/v1"
EXACT_IN_ROUTE_TRUE_KEY_INTERPRETATION_PACKET_SCHEMA = "zenodex/exact-in-route-true-key-interpretation-packet/v1"
EXACT_IN_ROUTE_GUARD_MISMATCH_ERROR = "exact_in_runtime_not_canonical_on_audit_domain"
ExactInRouteCanonicalKey = tuple[int, int, int, str, str, str]


def _require_bool(value: object, *, name: str) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be a bool")
    return value


def _require_payload_int(payload: Mapping[str, Any], field_name: str) -> int:
    value = payload[field_name]
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{field_name} must be an int")
    return int(value)


def _require_amount_in_int(amount_in: object) -> int:
    if not isinstance(amount_in, int) or isinstance(amount_in, bool):
        raise ValueError("amount_in must be an int")
    return int(amount_in)


def exact_in_route_canonical_key(quote: RouteQuote) -> ExactInRouteCanonicalKey:
    hop_count, leg_count, pool_seq, mid, asset_out = _quote_key(quote)
    return (-int(quote.amount_out), int(hop_count), int(leg_count), str(pool_seq), str(mid), str(asset_out))


def enumerate_route_candidates_exact_in_2hop(
    *,
    pools_by_id: Dict[str, PoolState],
    asset_in: AssetId,
    asset_out: AssetId,
    amount_in: Amount,
    split_search_profile: str = "adaptive_v6",
    enable_mixed_direct_twohop_split: bool = False,
) -> tuple[RouteQuote, ...]:
    amount_in_i = _require_amount_in_int(amount_in)
    if amount_in_i <= 0 or asset_in == asset_out:
        return ()

    pools: Tuple[PoolState, ...] = tuple(sorted(pools_by_id.values(), key=lambda pool: pool.pool_id))
    by_asset = _build_asset_pool_index(pools)
    candidates: list[RouteQuote] = []
    best_direct_1hop: Optional[RouteQuote] = None
    twohop_candidates: List[Tuple[RouteQuote, PoolState, PoolState, AssetId]] = []

    for idx in by_asset.get(asset_in, ()):
        pool = pools[idx]
        if not _pool_connects(pool, asset_in, asset_out):
            continue
        out = _pool_quote_exact_in(pool, asset_in=asset_in, asset_out=asset_out, amount_in=amount_in)
        if out is None:
            continue
        amount_out_value, _pool_id = out
        hop = RouteHop(pool.pool_id, asset_in, asset_out, amount_in, amount_out_value)
        quote = RouteQuote(
            asset_in=asset_in,
            asset_out=asset_out,
            amount_in=amount_in,
            amount_out=amount_out_value,
            legs=(RouteLeg(hops=(hop,), amount_in=amount_in, amount_out=amount_out_value),),
        )
        candidates.append(quote)
        if best_direct_1hop is None or (quote.amount_out > best_direct_1hop.amount_out) or (
            quote.amount_out == best_direct_1hop.amount_out and _quote_key(quote) < _quote_key(best_direct_1hop)
        ):
            best_direct_1hop = quote

    for idx1 in by_asset.get(asset_in, ()):
        pool1 = pools[idx1]
        if asset_in == pool1.asset0:
            mid = pool1.asset1
        elif asset_in == pool1.asset1:
            mid = pool1.asset0
        else:
            continue
        if mid == asset_out or mid == asset_in:
            continue
        out1 = _pool_quote_exact_in(pool1, asset_in=asset_in, asset_out=mid, amount_in=amount_in)
        if out1 is None:
            continue
        amount_mid, _ = out1
        for idx2 in by_asset.get(mid, ()):
            pool2 = pools[idx2]
            out2 = _pool_quote_exact_in(pool2, asset_in=mid, asset_out=asset_out, amount_in=amount_mid)
            if out2 is None:
                continue
            amount_out_value, _ = out2
            hop1 = RouteHop(pool1.pool_id, asset_in, mid, amount_in, amount_mid)
            hop2 = RouteHop(pool2.pool_id, mid, asset_out, amount_mid, amount_out_value)
            quote = RouteQuote(
                asset_in=asset_in,
                asset_out=asset_out,
                amount_in=amount_in,
                amount_out=amount_out_value,
                legs=(RouteLeg(hops=(hop1, hop2), amount_in=amount_in, amount_out=amount_out_value),),
            )
            candidates.append(quote)
            twohop_candidates.append((quote, pool1, pool2, mid))

    direct_pools: list[tuple[Amount, PoolState]] = []
    for idx in by_asset.get(asset_in, ()):
        pool = pools[idx]
        if not _pool_connects(pool, asset_in, asset_out):
            continue
        out = _pool_quote_exact_in(pool, asset_in=asset_in, asset_out=asset_out, amount_in=amount_in)
        if out is None:
            continue
        amount_out_value, _ = out
        direct_pools.append((amount_out_value, pool))

    if len(direct_pools) >= 2:
        direct_pools.sort(key=lambda item: (-int(item[0]), item[1].pool_id))
        top_k = min(16, len(direct_pools))
        candidate_pools = [pool for _amount_out_value, pool in direct_pools[:top_k]]

        try:
            split_many = best_split_many_pools_exact_in_for_pools(
                candidate_pools,
                asset_in=asset_in,
                asset_out=asset_out,
                amount_in_total=amount_in,
                max_legs=4,
                max_candidates=top_k,
                max_iters=4096,
            )
        except ValueError:
            split_many = None
        if split_many is not None and split_many.amount_out_total > 0:
            legs: list[RouteLeg] = []
            for leg in split_many.legs:
                legs.append(
                    RouteLeg(
                        hops=(RouteHop(leg.pool_id, asset_in, asset_out, leg.amount_in, leg.amount_out),),
                        amount_in=leg.amount_in,
                        amount_out=leg.amount_out,
                    )
                )
            candidates.append(
                RouteQuote(
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_in=amount_in,
                    amount_out=split_many.amount_out_total,
                    legs=tuple(legs),
                )
            )

        top_k_two = min(12, top_k)
        candidate_pools_two = candidate_pools[:top_k_two]
        for left in range(top_k_two):
            for right in range(left + 1, top_k_two):
                pool0 = candidate_pools_two[left]
                pool1 = candidate_pools_two[right]
                try:
                    split = best_split_two_pools_exact_in_for_pools(
                        pool0,
                        pool1,
                        asset_in=asset_in,
                        asset_out=asset_out,
                        amount_in_total=amount_in,
                        search_profile=str(split_search_profile),
                    )
                except ValueError:
                    continue
                if split.amount_out_total <= 0:
                    continue
                leg0 = RouteLeg(
                    hops=(RouteHop(split.pool0_id, asset_in, asset_out, split.amount_in_0, split.amount_out_0),),
                    amount_in=split.amount_in_0,
                    amount_out=split.amount_out_0,
                )
                leg1 = RouteLeg(
                    hops=(RouteHop(split.pool1_id, asset_in, asset_out, split.amount_in_1, split.amount_out_1),),
                    amount_in=split.amount_in_1,
                    amount_out=split.amount_out_1,
                )
                candidates.append(
                    RouteQuote(
                        asset_in=asset_in,
                        asset_out=asset_out,
                        amount_in=amount_in,
                        amount_out=split.amount_out_total,
                        legs=(leg0, leg1),
                    )
                )

    if enable_mixed_direct_twohop_split and best_direct_1hop is not None and twohop_candidates:
        direct_pool_id = best_direct_1hop.legs[0].hops[0].pool_id
        direct_pool = pools_by_id.get(direct_pool_id)
        if direct_pool is not None:
            twohop_candidates.sort(key=lambda item: (-int(item[0].amount_out), _quote_key(item[0])))
            top_mixed = twohop_candidates[: min(8, len(twohop_candidates))]
            for _twohop_quote, pool1, pool2, mid in top_mixed:
                if direct_pool.pool_id in {pool1.pool_id, pool2.pool_id}:
                    continue
                total = int(amount_in)
                for direct_in in range(1, total):
                    routed_in = total - int(direct_in)
                    direct_out = _pool_quote_exact_in(
                        direct_pool,
                        asset_in=asset_in,
                        asset_out=asset_out,
                        amount_in=int(direct_in),
                    )
                    if direct_out is None:
                        continue
                    direct_amount_out, _ = direct_out
                    routed_mid = _pool_quote_exact_in(
                        pool1,
                        asset_in=asset_in,
                        asset_out=mid,
                        amount_in=int(routed_in),
                    )
                    if routed_mid is None:
                        continue
                    amount_mid, _ = routed_mid
                    routed_out = _pool_quote_exact_in(
                        pool2,
                        asset_in=mid,
                        asset_out=asset_out,
                        amount_in=int(amount_mid),
                    )
                    if routed_out is None:
                        continue
                    routed_amount_out, _ = routed_out
                    direct_leg = RouteLeg(
                        hops=(RouteHop(direct_pool.pool_id, asset_in, asset_out, int(direct_in), int(direct_amount_out)),),
                        amount_in=int(direct_in),
                        amount_out=int(direct_amount_out),
                    )
                    routed_leg = RouteLeg(
                        hops=(
                            RouteHop(pool1.pool_id, asset_in, mid, int(routed_in), int(amount_mid)),
                            RouteHop(pool2.pool_id, mid, asset_out, int(amount_mid), int(routed_amount_out)),
                        ),
                        amount_in=int(routed_in),
                        amount_out=int(routed_amount_out),
                    )
                    candidates.append(
                        RouteQuote(
                            asset_in=asset_in,
                            asset_out=asset_out,
                            amount_in=amount_in,
                            amount_out=int(direct_amount_out) + int(routed_amount_out),
                            legs=(direct_leg, routed_leg),
                        )
                    )

    return tuple(candidates)


@dataclass(frozen=True)
class ExactInRouteCandidateCertificate:
    candidate_index: int
    quote: RouteQuote
    route_key: ExactInRouteCanonicalKey
    route_key_rank_u64: int

    def __post_init__(self) -> None:
        if not isinstance(self.candidate_index, int) or isinstance(self.candidate_index, bool):
            raise TypeError("candidate_index must be an int")
        if self.candidate_index < 0 or self.candidate_index > 0xFFFFFFFF:
            raise ValueError(f"candidate_index out of range: {self.candidate_index}")
        if not isinstance(self.quote, RouteQuote):
            raise TypeError("quote must be a RouteQuote")
        if not isinstance(self.route_key, tuple) or len(self.route_key) != 6:
            raise TypeError("route_key must be a 6-tuple canonical key")
        if not isinstance(self.route_key_rank_u64, int) or isinstance(self.route_key_rank_u64, bool):
            raise TypeError("route_key_rank_u64 must be an int")
        if self.route_key_rank_u64 < 0 or self.route_key_rank_u64 > 0xFFFFFFFFFFFFFFFF:
            raise ValueError(f"route_key_rank_u64 out of range: {self.route_key_rank_u64}")

    def to_dict(self) -> dict[str, Any]:
        return {
            "candidate_index": int(self.candidate_index),
            "route_key_rank_u64": int(self.route_key_rank_u64),
            "route_key": _route_key_to_dict(self.route_key),
            "quote": _quote_to_dict(self.quote),
        }


@dataclass(frozen=True)
class ExactInRouteRankProjectionPacket:
    asset_in: AssetId
    asset_out: AssetId
    amount_in: Amount
    candidate_set_hash: str
    ordered_unique_route_keys: tuple[ExactInRouteCanonicalKey, ...]
    candidates: tuple[ExactInRouteCandidateCertificate, ...]
    ordered_unique_keys_sorted_unique: bool
    candidate_ranks_match_projection: bool
    rank_order_preserves_true_key_order: bool
    packet_ok: bool
    schema: str = EXACT_IN_ROUTE_RANK_PROJECTION_PACKET_SCHEMA

    def __post_init__(self) -> None:
        if not isinstance(self.asset_in, str) or not self.asset_in:
            raise ValueError("asset_in must be a non-empty string")
        if not isinstance(self.asset_out, str) or not self.asset_out:
            raise ValueError("asset_out must be a non-empty string")
        if not isinstance(self.amount_in, int) or isinstance(self.amount_in, bool) or self.amount_in <= 0:
            raise ValueError("amount_in must be a positive int")
        if not isinstance(self.candidate_set_hash, str) or not self.candidate_set_hash:
            raise ValueError("candidate_set_hash must be a non-empty string")
        if self.schema != EXACT_IN_ROUTE_RANK_PROJECTION_PACKET_SCHEMA:
            raise ValueError(f"unsupported schema: {self.schema!r}")
        if not self.ordered_unique_route_keys:
            raise ValueError("ordered_unique_route_keys must be non-empty")
        if not self.candidates:
            raise ValueError("candidates must be non-empty")
        for name in (
            "ordered_unique_keys_sorted_unique",
            "candidate_ranks_match_projection",
            "rank_order_preserves_true_key_order",
            "packet_ok",
        ):
            if not isinstance(getattr(self, name), bool):
                raise TypeError(f"{name} must be a bool")

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "asset_in": self.asset_in,
            "asset_out": self.asset_out,
            "amount_in": int(self.amount_in),
            "candidate_set_hash": self.candidate_set_hash,
            "ordered_unique_route_keys": [
                {
                    "route_key_rank_u64": int(rank),
                    "route_key": _route_key_to_dict(route_key),
                }
                for rank, route_key in enumerate(self.ordered_unique_route_keys)
            ],
            "candidates": [candidate.to_dict() for candidate in self.candidates],
            "ordered_unique_keys_sorted_unique": bool(self.ordered_unique_keys_sorted_unique),
            "candidate_ranks_match_projection": bool(self.candidate_ranks_match_projection),
            "rank_order_preserves_true_key_order": bool(self.rank_order_preserves_true_key_order),
            "packet_ok": bool(self.packet_ok),
        }


@dataclass(frozen=True)
class ExactInRouteTrueKeyInterpretationPacket:
    asset_in: AssetId
    asset_out: AssetId
    amount_in: Amount
    candidate_set_hash: str
    rank_projection_packet: ExactInRouteRankProjectionPacket
    certificate: ExactInRouteCanonicalCertificate
    extracted_route_keys: tuple[ExactInRouteCanonicalKey, ...]
    winner_index_in_range: bool
    candidate_indices_match_stream: bool
    candidate_route_keys_match_quotes: bool
    winner_matches_certificate_candidate: bool
    winner_true_key_minimal: bool
    packet_ok: bool
    schema: str = EXACT_IN_ROUTE_TRUE_KEY_INTERPRETATION_PACKET_SCHEMA

    def __post_init__(self) -> None:
        if not isinstance(self.asset_in, str) or not self.asset_in:
            raise ValueError("asset_in must be a non-empty string")
        if not isinstance(self.asset_out, str) or not self.asset_out:
            raise ValueError("asset_out must be a non-empty string")
        if not isinstance(self.amount_in, int) or isinstance(self.amount_in, bool) or self.amount_in <= 0:
            raise ValueError("amount_in must be a positive int")
        if not isinstance(self.candidate_set_hash, str) or not self.candidate_set_hash:
            raise ValueError("candidate_set_hash must be a non-empty string")
        if not isinstance(self.rank_projection_packet, ExactInRouteRankProjectionPacket):
            raise TypeError("rank_projection_packet must be an ExactInRouteRankProjectionPacket")
        if not isinstance(self.certificate, ExactInRouteCanonicalCertificate):
            raise TypeError("certificate must be an ExactInRouteCanonicalCertificate")
        if not self.extracted_route_keys:
            raise ValueError("extracted_route_keys must be non-empty")
        if self.schema != EXACT_IN_ROUTE_TRUE_KEY_INTERPRETATION_PACKET_SCHEMA:
            raise ValueError(f"unsupported schema: {self.schema!r}")
        for name in (
            "winner_index_in_range",
            "candidate_indices_match_stream",
            "candidate_route_keys_match_quotes",
            "winner_matches_certificate_candidate",
            "winner_true_key_minimal",
            "packet_ok",
        ):
            if not isinstance(getattr(self, name), bool):
                raise TypeError(f"{name} must be a bool")

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "asset_in": self.asset_in,
            "asset_out": self.asset_out,
            "amount_in": int(self.amount_in),
            "candidate_set_hash": self.candidate_set_hash,
            "rank_projection_packet": self.rank_projection_packet.to_dict(),
            "certificate": self.certificate.to_dict(),
            "extracted_route_keys": [
                {
                    "candidate_index": int(index),
                    "route_key": _route_key_to_dict(route_key),
                }
                for index, route_key in enumerate(self.extracted_route_keys)
            ],
            "winner_index_in_range": bool(self.winner_index_in_range),
            "candidate_indices_match_stream": bool(self.candidate_indices_match_stream),
            "candidate_route_keys_match_quotes": bool(self.candidate_route_keys_match_quotes),
            "winner_matches_certificate_candidate": bool(self.winner_matches_certificate_candidate),
            "winner_true_key_minimal": bool(self.winner_true_key_minimal),
            "packet_ok": bool(self.packet_ok),
        }


@dataclass(frozen=True)
class ExactInRouteCanonicalCertificate:
    asset_in: AssetId
    asset_out: AssetId
    amount_in: Amount
    candidate_set_hash: str
    winner_index: int
    winner_route_key_rank_u64: int
    winner_quote: RouteQuote
    candidates: tuple[ExactInRouteCandidateCertificate, ...]
    argmin_steps: tuple[dict[str, int], ...]
    schema: str = EXACT_IN_ROUTE_CERTIFICATE_SCHEMA
    tau_spec_id: str = ARGMIN_STREAM_CERTIFICATE_V1.spec_id

    def __post_init__(self) -> None:
        if not isinstance(self.asset_in, str) or not self.asset_in:
            raise ValueError("asset_in must be a non-empty string")
        if not isinstance(self.asset_out, str) or not self.asset_out:
            raise ValueError("asset_out must be a non-empty string")
        if not isinstance(self.amount_in, int) or isinstance(self.amount_in, bool) or self.amount_in <= 0:
            raise ValueError("amount_in must be a positive int")
        if not isinstance(self.candidate_set_hash, str) or not self.candidate_set_hash:
            raise ValueError("candidate_set_hash must be a non-empty string")
        if not isinstance(self.winner_index, int) or isinstance(self.winner_index, bool):
            raise TypeError("winner_index must be an int")
        if self.winner_index < 0 or self.winner_index > 0xFFFFFFFF:
            raise ValueError(f"winner_index out of range: {self.winner_index}")
        if not isinstance(self.winner_route_key_rank_u64, int) or isinstance(self.winner_route_key_rank_u64, bool):
            raise TypeError("winner_route_key_rank_u64 must be an int")
        if self.winner_route_key_rank_u64 < 0 or self.winner_route_key_rank_u64 > 0xFFFFFFFFFFFFFFFF:
            raise ValueError(f"winner_route_key_rank_u64 out of range: {self.winner_route_key_rank_u64}")
        if not isinstance(self.winner_quote, RouteQuote):
            raise TypeError("winner_quote must be a RouteQuote")
        if self.schema != EXACT_IN_ROUTE_CERTIFICATE_SCHEMA:
            raise ValueError(f"unsupported schema: {self.schema!r}")
        if self.tau_spec_id != ARGMIN_STREAM_CERTIFICATE_V1.spec_id:
            raise ValueError(f"unexpected tau_spec_id: {self.tau_spec_id!r}")
        if not self.candidates:
            raise ValueError("candidates must be non-empty")
        if not self.argmin_steps:
            raise ValueError("argmin_steps must be non-empty")

    def to_unsigned_dict(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "tau_spec_id": self.tau_spec_id,
            "asset_in": self.asset_in,
            "asset_out": self.asset_out,
            "amount_in": int(self.amount_in),
            "candidate_set_hash": self.candidate_set_hash,
            "winner_index": int(self.winner_index),
            "winner_route_key_rank_u64": int(self.winner_route_key_rank_u64),
            "winner_quote": _quote_to_dict(self.winner_quote),
            "candidates": [candidate.to_dict() for candidate in self.candidates],
            "argmin_steps": [dict(step) for step in self.argmin_steps],
        }

    def to_dict(self) -> dict[str, Any]:
        payload = self.to_unsigned_dict()
        payload["certificate_hash"] = self.certificate_hash_hex()
        return payload

    def certificate_hash_hex(self) -> str:
        return sha256_hex(
            domain_sep_bytes("exact_in_route_certificate", version=1) + canonical_json_bytes(self.to_unsigned_dict())
        )


@dataclass(frozen=True)
class ExactInRouteOracleContract:
    asset_in: AssetId
    asset_out: AssetId
    amount_in: Amount
    split_search_profile: str
    enable_mixed_direct_twohop_split: bool
    binding_ok: int
    pool_snapshots: tuple[dict[str, Any], ...]
    runtime_quote: RouteQuote
    canonical_winner_quote: RouteQuote
    runtime_matches_canonical: bool
    candidate_count: int
    certificate: ExactInRouteCanonicalCertificate

    def __post_init__(self) -> None:
        if not isinstance(self.asset_in, str) or not self.asset_in:
            raise ValueError("asset_in must be a non-empty string")
        if not isinstance(self.asset_out, str) or not self.asset_out:
            raise ValueError("asset_out must be a non-empty string")
        if not isinstance(self.amount_in, int) or isinstance(self.amount_in, bool) or self.amount_in <= 0:
            raise ValueError("amount_in must be a positive int")
        if not isinstance(self.split_search_profile, str) or not self.split_search_profile:
            raise ValueError("split_search_profile must be a non-empty string")
        if not isinstance(self.enable_mixed_direct_twohop_split, bool):
            raise TypeError("enable_mixed_direct_twohop_split must be a bool")
        if not isinstance(self.binding_ok, int) or isinstance(self.binding_ok, bool):
            raise TypeError("binding_ok must be an int")
        if int(self.binding_ok) not in {0, 1}:
            raise ValueError("binding_ok must be 0 or 1")
        if not self.pool_snapshots:
            raise ValueError("pool_snapshots must be non-empty")
        if not isinstance(self.runtime_quote, RouteQuote):
            raise TypeError("runtime_quote must be a RouteQuote")
        if not isinstance(self.canonical_winner_quote, RouteQuote):
            raise TypeError("canonical_winner_quote must be a RouteQuote")
        if not isinstance(self.runtime_matches_canonical, bool):
            raise TypeError("runtime_matches_canonical must be a bool")
        if not isinstance(self.candidate_count, int) or isinstance(self.candidate_count, bool) or self.candidate_count <= 0:
            raise ValueError("candidate_count must be a positive int")
        if not isinstance(self.certificate, ExactInRouteCanonicalCertificate):
            raise TypeError("certificate must be an ExactInRouteCanonicalCertificate")

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": EXACT_IN_ROUTE_ORACLE_CONTRACT_SCHEMA,
            "asset_in": self.asset_in,
            "asset_out": self.asset_out,
            "amount_in": int(self.amount_in),
            "split_search_profile": self.split_search_profile,
            "enable_mixed_direct_twohop_split": bool(self.enable_mixed_direct_twohop_split),
            "binding_ok": int(self.binding_ok),
            "pool_snapshots": [dict(snapshot) for snapshot in self.pool_snapshots],
            "runtime_quote": _quote_to_dict(self.runtime_quote),
            "canonical_winner_quote": _quote_to_dict(self.canonical_winner_quote),
            "runtime_matches_canonical": bool(self.runtime_matches_canonical),
            "candidate_count": int(self.candidate_count),
            "certificate": self.certificate.to_dict(),
        }


@dataclass(frozen=True)
class ExactInRouteGuardedQuotePacket:
    guard_ok: bool
    quote: RouteQuote | None
    error: str | None
    contract: ExactInRouteOracleContract
    schema: str = EXACT_IN_ROUTE_GUARDED_QUOTE_PACKET_SCHEMA

    def __post_init__(self) -> None:
        if self.schema != EXACT_IN_ROUTE_GUARDED_QUOTE_PACKET_SCHEMA:
            raise ValueError(f"unsupported schema: {self.schema!r}")
        if not isinstance(self.guard_ok, bool):
            raise TypeError("guard_ok must be a bool")
        if self.quote is not None and not isinstance(self.quote, RouteQuote):
            raise TypeError("quote must be a RouteQuote or None")
        if self.error is not None and (not isinstance(self.error, str) or not self.error):
            raise ValueError("error must be a non-empty string or None")
        if not isinstance(self.contract, ExactInRouteOracleContract):
            raise TypeError("contract must be an ExactInRouteOracleContract")
        if self.guard_ok:
            if self.quote is None:
                raise ValueError("quote must be present when guard_ok is true")
            if self.error is not None:
                raise ValueError("error must be None when guard_ok is true")
        else:
            if self.quote is not None:
                raise ValueError("quote must be None when guard_ok is false")
            if self.error is None:
                raise ValueError("error must be present when guard_ok is false")

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "guard_ok": bool(self.guard_ok),
            "quote": None if self.quote is None else _quote_to_dict(self.quote),
            "error": self.error,
            "contract": self.contract.to_dict(),
        }


def _validate_exact_in_route_quotes(quotes: Sequence[RouteQuote]) -> tuple[RouteQuote, tuple[RouteQuote, ...]]:
    if not isinstance(quotes, Sequence):
        raise TypeError("quotes must be a sequence")
    if not quotes:
        raise ValueError("quotes must be non-empty")
    normalized = tuple(quotes)
    first = normalized[0]
    if not isinstance(first, RouteQuote):
        raise TypeError("quotes must contain RouteQuote entries")
    for index, quote in enumerate(normalized):
        if not isinstance(quote, RouteQuote):
            raise TypeError("quotes must contain RouteQuote entries")
        if quote.asset_in != first.asset_in:
            raise ValueError(f"quote[{index}] asset_in mismatch")
        if quote.asset_out != first.asset_out:
            raise ValueError(f"quote[{index}] asset_out mismatch")
        if int(quote.amount_in) != int(first.amount_in):
            raise ValueError(f"quote[{index}] amount_in mismatch")
    return first, normalized


def build_exact_in_route_rank_projection_packet(
    quotes: Sequence[RouteQuote],
) -> ExactInRouteRankProjectionPacket:
    first, normalized = _validate_exact_in_route_quotes(quotes)
    indexed_keys = [(int(index), quote, exact_in_route_canonical_key(quote)) for index, quote in enumerate(normalized)]
    ordered_unique_keys, rank_by_key = compute_exact_in_route_rank_projection(normalized)
    candidates = tuple(
        ExactInRouteCandidateCertificate(
            candidate_index=index,
            quote=quote,
            route_key=route_key,
            route_key_rank_u64=int(rank_by_key[route_key]),
        )
        for index, quote, route_key in indexed_keys
    )
    ordered_unique_keys_sorted_unique = tuple(sorted(set(ordered_unique_keys))) == ordered_unique_keys
    candidate_ranks_match_projection = all(
        int(candidate.route_key_rank_u64) == int(rank_by_key[candidate.route_key]) for candidate in candidates
    )
    rank_order_preserves_true_key_order = True
    for left in candidates:
        for right in candidates:
            if left.route_key < right.route_key and not (left.route_key_rank_u64 < right.route_key_rank_u64):
                rank_order_preserves_true_key_order = False
                break
            if left.route_key == right.route_key and left.route_key_rank_u64 != right.route_key_rank_u64:
                rank_order_preserves_true_key_order = False
                break
        if not rank_order_preserves_true_key_order:
            break
    packet_ok = bool(
        ordered_unique_keys_sorted_unique and candidate_ranks_match_projection and rank_order_preserves_true_key_order
    )
    return ExactInRouteRankProjectionPacket(
        asset_in=first.asset_in,
        asset_out=first.asset_out,
        amount_in=int(first.amount_in),
        candidate_set_hash=_candidate_set_hash_hex(candidates),
        ordered_unique_route_keys=ordered_unique_keys,
        candidates=candidates,
        ordered_unique_keys_sorted_unique=bool(ordered_unique_keys_sorted_unique),
        candidate_ranks_match_projection=bool(candidate_ranks_match_projection),
        rank_order_preserves_true_key_order=bool(rank_order_preserves_true_key_order),
        packet_ok=bool(packet_ok),
    )


def build_exact_in_route_rank_projection_packet_for_pools(
    *,
    pools_by_id: Dict[str, PoolState],
    asset_in: AssetId,
    asset_out: AssetId,
    amount_in: Amount,
    split_search_profile: str = "adaptive_v6",
    enable_mixed_direct_twohop_split: bool = False,
) -> ExactInRouteRankProjectionPacket | None:
    quotes = enumerate_route_candidates_exact_in_2hop(
        pools_by_id=pools_by_id,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=amount_in,
        split_search_profile=split_search_profile,
        enable_mixed_direct_twohop_split=enable_mixed_direct_twohop_split,
    )
    if not quotes:
        return None
    return build_exact_in_route_rank_projection_packet(quotes)


def build_exact_in_route_true_key_interpretation_packet(
    quotes: Sequence[RouteQuote],
) -> ExactInRouteTrueKeyInterpretationPacket:
    first, normalized = _validate_exact_in_route_quotes(quotes)
    rank_projection_packet = build_exact_in_route_rank_projection_packet(normalized)
    certificate = build_exact_in_route_canonical_certificate(normalized)
    extracted_route_keys = tuple(exact_in_route_canonical_key(quote) for quote in normalized)
    winner_index = int(certificate.winner_index)
    winner_index_in_range = 0 <= winner_index < len(normalized)
    candidate_indices_match_stream = all(
        int(candidate.candidate_index) == int(index)
        for index, candidate in enumerate(certificate.candidates)
    )
    candidate_route_keys_match_quotes = (
        len(certificate.candidates) == len(normalized)
        and all(
            candidate.quote == normalized[index] and candidate.route_key == extracted_route_keys[index]
            for index, candidate in enumerate(certificate.candidates)
        )
    )
    winner_matches_certificate_candidate = bool(
        winner_index_in_range
        and certificate.candidates[winner_index].quote == certificate.winner_quote
        and certificate.candidates[winner_index].route_key == extracted_route_keys[winner_index]
        and int(certificate.candidates[winner_index].route_key_rank_u64) == int(certificate.winner_route_key_rank_u64)
    )
    winner_true_key_minimal = bool(
        winner_index_in_range
        and all(
            (extracted_route_keys[winner_index], winner_index) <= (route_key, index)
            for index, route_key in enumerate(extracted_route_keys)
        )
    )
    packet_ok = bool(
        rank_projection_packet.packet_ok
        and winner_index_in_range
        and candidate_indices_match_stream
        and candidate_route_keys_match_quotes
        and winner_matches_certificate_candidate
        and winner_true_key_minimal
    )
    return ExactInRouteTrueKeyInterpretationPacket(
        asset_in=first.asset_in,
        asset_out=first.asset_out,
        amount_in=int(first.amount_in),
        candidate_set_hash=certificate.candidate_set_hash,
        rank_projection_packet=rank_projection_packet,
        certificate=certificate,
        extracted_route_keys=extracted_route_keys,
        winner_index_in_range=bool(winner_index_in_range),
        candidate_indices_match_stream=bool(candidate_indices_match_stream),
        candidate_route_keys_match_quotes=bool(candidate_route_keys_match_quotes),
        winner_matches_certificate_candidate=bool(winner_matches_certificate_candidate),
        winner_true_key_minimal=bool(winner_true_key_minimal),
        packet_ok=bool(packet_ok),
    )


def build_exact_in_route_true_key_interpretation_packet_for_pools(
    *,
    pools_by_id: Dict[str, PoolState],
    asset_in: AssetId,
    asset_out: AssetId,
    amount_in: Amount,
    split_search_profile: str = "adaptive_v6",
    enable_mixed_direct_twohop_split: bool = False,
) -> ExactInRouteTrueKeyInterpretationPacket | None:
    quotes = enumerate_route_candidates_exact_in_2hop(
        pools_by_id=pools_by_id,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=amount_in,
        split_search_profile=split_search_profile,
        enable_mixed_direct_twohop_split=enable_mixed_direct_twohop_split,
    )
    if not quotes:
        return None
    return build_exact_in_route_true_key_interpretation_packet(quotes)


def build_exact_in_route_canonical_certificate(
    quotes: Sequence[RouteQuote],
    *,
    binding_ok: int = 1,
) -> ExactInRouteCanonicalCertificate:
    first, normalized = _validate_exact_in_route_quotes(quotes)
    indexed_keys = [(int(index), quote, exact_in_route_canonical_key(quote)) for index, quote in enumerate(normalized)]
    _ordered_unique_keys, rank_by_key = compute_exact_in_route_rank_projection(normalized)

    candidates = tuple(
        ExactInRouteCandidateCertificate(
            candidate_index=index,
            quote=quote,
            route_key=route_key,
            route_key_rank_u64=int(rank_by_key[route_key]),
        )
        for index, quote, route_key in indexed_keys
    )
    winner = min(candidates, key=lambda candidate: (candidate.route_key_rank_u64, candidate.candidate_index))
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
    return ExactInRouteCanonicalCertificate(
        asset_in=first.asset_in,
        asset_out=first.asset_out,
        amount_in=int(first.amount_in),
        candidate_set_hash=_candidate_set_hash_hex(candidates),
        winner_index=int(winner.candidate_index),
        winner_route_key_rank_u64=int(winner.route_key_rank_u64),
        winner_quote=winner.quote,
        candidates=candidates,
        argmin_steps=steps,
    )


def build_exact_in_route_canonical_certificate_for_pools(
    *,
    pools_by_id: Dict[str, PoolState],
    asset_in: AssetId,
    asset_out: AssetId,
    amount_in: Amount,
    split_search_profile: str = "adaptive_v6",
    enable_mixed_direct_twohop_split: bool = False,
    binding_ok: int = 1,
) -> Optional[ExactInRouteCanonicalCertificate]:
    quotes = enumerate_route_candidates_exact_in_2hop(
        pools_by_id=pools_by_id,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=amount_in,
        split_search_profile=split_search_profile,
        enable_mixed_direct_twohop_split=enable_mixed_direct_twohop_split,
    )
    if not quotes:
        return None
    return build_exact_in_route_canonical_certificate(quotes, binding_ok=binding_ok)


def build_exact_in_route_oracle_contract(
    *,
    pools_by_id: Dict[str, PoolState],
    asset_in: AssetId,
    asset_out: AssetId,
    amount_in: Amount,
    split_search_profile: str = "adaptive_v6",
    enable_mixed_direct_twohop_split: bool = False,
    binding_ok: int = 1,
) -> ExactInRouteOracleContract:
    amount_in_i = _require_amount_in_int(amount_in)
    runtime_quote = best_route_exact_in_2hop(
        pools_by_id=pools_by_id,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=amount_in_i,
        split_search_profile=split_search_profile,
        enable_mixed_direct_twohop_split=enable_mixed_direct_twohop_split,
    )
    certificate = build_exact_in_route_canonical_certificate_for_pools(
        pools_by_id=pools_by_id,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=amount_in_i,
        split_search_profile=split_search_profile,
        enable_mixed_direct_twohop_split=enable_mixed_direct_twohop_split,
        binding_ok=binding_ok,
    )
    if runtime_quote is None or certificate is None:
        raise ValueError("no feasible exact-in route")
    pool_snapshots = tuple(
        _pool_to_dict(pool)
        for pool in sorted(pools_by_id.values(), key=lambda candidate: candidate.pool_id)
    )
    return ExactInRouteOracleContract(
        asset_in=str(asset_in),
        asset_out=str(asset_out),
        amount_in=amount_in_i,
        split_search_profile=str(split_search_profile),
        enable_mixed_direct_twohop_split=bool(enable_mixed_direct_twohop_split),
        binding_ok=int(binding_ok),
        pool_snapshots=pool_snapshots,
        runtime_quote=runtime_quote,
        canonical_winner_quote=certificate.winner_quote,
        runtime_matches_canonical=runtime_quote == certificate.winner_quote,
        candidate_count=len(certificate.candidates),
        certificate=certificate,
    )


def guard_exact_in_route_runtime_canonicality(
    *,
    pools_by_id: Dict[str, PoolState],
    asset_in: AssetId,
    asset_out: AssetId,
    amount_in: Amount,
    split_search_profile: str = "adaptive_v6",
    enable_mixed_direct_twohop_split: bool = False,
    binding_ok: int = 1,
) -> tuple[bool, str | None, ExactInRouteOracleContract]:
    contract = build_exact_in_route_oracle_contract(
        pools_by_id=pools_by_id,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=amount_in,
        split_search_profile=split_search_profile,
        enable_mixed_direct_twohop_split=enable_mixed_direct_twohop_split,
        binding_ok=binding_ok,
    )
    if contract.runtime_matches_canonical:
        return True, None, contract
    return False, EXACT_IN_ROUTE_GUARD_MISMATCH_ERROR, contract


def quote_exact_in_route_guarded(
    *,
    pools_by_id: Dict[str, PoolState],
    asset_in: AssetId,
    asset_out: AssetId,
    amount_in: Amount,
    split_search_profile: str = "adaptive_v6",
    enable_mixed_direct_twohop_split: bool = False,
    binding_ok: int = 1,
) -> tuple[RouteQuote | None, str | None, ExactInRouteOracleContract]:
    ok, err, contract = guard_exact_in_route_runtime_canonicality(
        pools_by_id=pools_by_id,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=amount_in,
        split_search_profile=split_search_profile,
        enable_mixed_direct_twohop_split=enable_mixed_direct_twohop_split,
        binding_ok=binding_ok,
    )
    if ok:
        return contract.runtime_quote, None, contract
    return None, str(err or EXACT_IN_ROUTE_GUARD_MISMATCH_ERROR), contract


def build_exact_in_route_guarded_quote_packet(
    *,
    pools_by_id: Dict[str, PoolState],
    asset_in: AssetId,
    asset_out: AssetId,
    amount_in: Amount,
    split_search_profile: str = "adaptive_v6",
    enable_mixed_direct_twohop_split: bool = False,
    binding_ok: int = 1,
) -> ExactInRouteGuardedQuotePacket:
    quote, err, contract = quote_exact_in_route_guarded(
        pools_by_id=pools_by_id,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=amount_in,
        split_search_profile=split_search_profile,
        enable_mixed_direct_twohop_split=enable_mixed_direct_twohop_split,
        binding_ok=binding_ok,
    )
    if quote is None:
        return ExactInRouteGuardedQuotePacket(
            guard_ok=False,
            quote=None,
            error=str(err or EXACT_IN_ROUTE_GUARD_MISMATCH_ERROR),
            contract=contract,
        )
    return ExactInRouteGuardedQuotePacket(
        guard_ok=True,
        quote=quote,
        error=None,
        contract=contract,
    )


def verify_exact_in_route_canonical_certificate(
    quotes: Sequence[RouteQuote],
    *,
    certificate: ExactInRouteCanonicalCertificate,
    expected_binding_ok: int = 1,
) -> tuple[bool, str | None]:
    if not isinstance(certificate, ExactInRouteCanonicalCertificate):
        return False, "certificate must be an ExactInRouteCanonicalCertificate"
    if certificate.schema != EXACT_IN_ROUTE_CERTIFICATE_SCHEMA:
        return False, "unsupported certificate schema"
    if certificate.tau_spec_id != ARGMIN_STREAM_CERTIFICATE_V1.spec_id:
        return False, "unsupported tau spec id"
    expected = build_exact_in_route_canonical_certificate(quotes, binding_ok=expected_binding_ok)
    if certificate.asset_in != expected.asset_in:
        return False, "asset_in mismatch"
    if certificate.asset_out != expected.asset_out:
        return False, "asset_out mismatch"
    if int(certificate.amount_in) != int(expected.amount_in):
        return False, "amount_in mismatch"
    if certificate.candidate_set_hash != expected.candidate_set_hash:
        return False, "candidate_set_hash mismatch"
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


def verify_exact_in_route_canonical_certificate_payload(
    payload: object,
    *,
    expected_binding_ok: int = 1,
) -> tuple[bool, str | None]:
    try:
        quotes = extract_exact_in_route_certificate_quotes(payload)
    except (TypeError, ValueError) as exc:
        return False, str(exc)
    expected = build_exact_in_route_canonical_certificate(quotes, binding_ok=expected_binding_ok)
    if not isinstance(payload, dict):
        return False, "certificate payload must be a dict"
    if payload != expected.to_dict():
        return False, "certificate payload mismatch"
    return True, None


def verify_exact_in_route_oracle_contract_payload(payload: object) -> tuple[bool, str | None]:
    if not isinstance(payload, dict):
        return False, "oracle contract payload must be a dict"
    if payload.get("schema") != EXACT_IN_ROUTE_ORACLE_CONTRACT_SCHEMA:
        return False, "unsupported oracle contract schema"
    try:
        pools_payload = payload["pool_snapshots"]
        if not isinstance(pools_payload, list) or not pools_payload:
            return False, "pool_snapshots must be a non-empty list"
        pools = {
            pool.pool_id: pool
            for pool in tuple(_pool_from_dict(pool_payload) for pool_payload in pools_payload)
        }
        expected = build_exact_in_route_oracle_contract(
            pools_by_id=pools,
            asset_in=str(payload["asset_in"]),
            asset_out=str(payload["asset_out"]),
            amount_in=_require_payload_int(payload, "amount_in"),
            split_search_profile=str(payload["split_search_profile"]),
            enable_mixed_direct_twohop_split=_require_bool(
                payload["enable_mixed_direct_twohop_split"],
                name="enable_mixed_direct_twohop_split",
            ),
            binding_ok=_require_payload_int(payload, "binding_ok"),
        )
    except (KeyError, TypeError, ValueError) as exc:
        return False, str(exc)
    if payload != expected.to_dict():
        return False, "oracle contract payload mismatch"
    return True, None


def verify_exact_in_route_guarded_quote_packet_payload(payload: object) -> tuple[bool, str | None]:
    if not isinstance(payload, dict):
        return False, "guarded quote packet payload must be a dict"
    if payload.get("schema") != EXACT_IN_ROUTE_GUARDED_QUOTE_PACKET_SCHEMA:
        return False, "unsupported guarded quote packet schema"
    contract_payload = payload.get("contract")
    if not isinstance(contract_payload, dict):
        return False, "contract must be a dict"
    ok, err = verify_exact_in_route_oracle_contract_payload(contract_payload)
    if not ok:
        return False, err
    try:
        pools_payload = contract_payload["pool_snapshots"]
        if not isinstance(pools_payload, list) or not pools_payload:
            return False, "pool_snapshots must be a non-empty list"
        pools = {
            pool.pool_id: pool
            for pool in tuple(_pool_from_dict(pool_payload) for pool_payload in pools_payload)
        }
        expected = build_exact_in_route_guarded_quote_packet(
            pools_by_id=pools,
            asset_in=str(contract_payload["asset_in"]),
            asset_out=str(contract_payload["asset_out"]),
            amount_in=_require_payload_int(contract_payload, "amount_in"),
            split_search_profile=str(contract_payload["split_search_profile"]),
            enable_mixed_direct_twohop_split=_require_bool(
                contract_payload["enable_mixed_direct_twohop_split"],
                name="enable_mixed_direct_twohop_split",
            ),
            binding_ok=_require_payload_int(contract_payload, "binding_ok"),
        )
    except (KeyError, TypeError, ValueError) as exc:
        return False, str(exc)
    if payload != expected.to_dict():
        return False, "guarded quote packet payload mismatch"
    return True, None


def verify_exact_in_route_rank_projection_packet(
    quotes: Sequence[RouteQuote],
    *,
    packet: ExactInRouteRankProjectionPacket,
) -> tuple[bool, str | None]:
    if not isinstance(packet, ExactInRouteRankProjectionPacket):
        return False, "packet must be an ExactInRouteRankProjectionPacket"
    if packet.schema != EXACT_IN_ROUTE_RANK_PROJECTION_PACKET_SCHEMA:
        return False, "unsupported rank projection packet schema"
    expected = build_exact_in_route_rank_projection_packet(quotes)
    if packet.asset_in != expected.asset_in:
        return False, "asset_in mismatch"
    if packet.asset_out != expected.asset_out:
        return False, "asset_out mismatch"
    if int(packet.amount_in) != int(expected.amount_in):
        return False, "amount_in mismatch"
    if packet.candidate_set_hash != expected.candidate_set_hash:
        return False, "candidate_set_hash mismatch"
    if packet.ordered_unique_route_keys != expected.ordered_unique_route_keys:
        return False, "ordered_unique_route_keys mismatch"
    if packet.candidates != expected.candidates:
        return False, "candidate list mismatch"
    if packet.ordered_unique_keys_sorted_unique != expected.ordered_unique_keys_sorted_unique:
        return False, "ordered_unique_keys_sorted_unique mismatch"
    if packet.candidate_ranks_match_projection != expected.candidate_ranks_match_projection:
        return False, "candidate_ranks_match_projection mismatch"
    if packet.rank_order_preserves_true_key_order != expected.rank_order_preserves_true_key_order:
        return False, "rank_order_preserves_true_key_order mismatch"
    if packet.packet_ok != expected.packet_ok:
        return False, "packet_ok mismatch"
    return True, None


def verify_exact_in_route_rank_projection_packet_payload(payload: object) -> tuple[bool, str | None]:
    try:
        quotes = extract_exact_in_route_certificate_quotes(payload)
    except (TypeError, ValueError) as exc:
        return False, str(exc)
    expected = build_exact_in_route_rank_projection_packet(quotes)
    if not isinstance(payload, dict):
        return False, "rank projection packet payload must be a dict"
    if payload != expected.to_dict():
        return False, "rank projection packet payload mismatch"
    return True, None


def verify_exact_in_route_true_key_interpretation_packet(
    quotes: Sequence[RouteQuote],
    *,
    packet: ExactInRouteTrueKeyInterpretationPacket,
) -> tuple[bool, str | None]:
    if not isinstance(packet, ExactInRouteTrueKeyInterpretationPacket):
        return False, "packet must be an ExactInRouteTrueKeyInterpretationPacket"
    if packet.schema != EXACT_IN_ROUTE_TRUE_KEY_INTERPRETATION_PACKET_SCHEMA:
        return False, "unsupported true-key interpretation packet schema"
    expected = build_exact_in_route_true_key_interpretation_packet(quotes)
    if packet.asset_in != expected.asset_in:
        return False, "asset_in mismatch"
    if packet.asset_out != expected.asset_out:
        return False, "asset_out mismatch"
    if int(packet.amount_in) != int(expected.amount_in):
        return False, "amount_in mismatch"
    if packet.candidate_set_hash != expected.candidate_set_hash:
        return False, "candidate_set_hash mismatch"
    if packet.rank_projection_packet != expected.rank_projection_packet:
        return False, "rank_projection_packet mismatch"
    if packet.certificate != expected.certificate:
        return False, "certificate mismatch"
    if packet.extracted_route_keys != expected.extracted_route_keys:
        return False, "extracted_route_keys mismatch"
    if packet.winner_index_in_range != expected.winner_index_in_range:
        return False, "winner_index_in_range mismatch"
    if packet.candidate_indices_match_stream != expected.candidate_indices_match_stream:
        return False, "candidate_indices_match_stream mismatch"
    if packet.candidate_route_keys_match_quotes != expected.candidate_route_keys_match_quotes:
        return False, "candidate_route_keys_match_quotes mismatch"
    if packet.winner_matches_certificate_candidate != expected.winner_matches_certificate_candidate:
        return False, "winner_matches_certificate_candidate mismatch"
    if packet.winner_true_key_minimal != expected.winner_true_key_minimal:
        return False, "winner_true_key_minimal mismatch"
    if packet.packet_ok != expected.packet_ok:
        return False, "packet_ok mismatch"
    return True, None


def verify_exact_in_route_true_key_interpretation_packet_payload(payload: object) -> tuple[bool, str | None]:
    if not isinstance(payload, dict):
        return False, "true-key interpretation packet payload must be a dict"
    if str(payload.get("schema")) != EXACT_IN_ROUTE_TRUE_KEY_INTERPRETATION_PACKET_SCHEMA:
        return False, "unsupported true-key interpretation packet schema"
    certificate_payload = payload.get("certificate")
    if not isinstance(certificate_payload, dict):
        return False, "true-key interpretation packet must include certificate"
    try:
        quotes = extract_exact_in_route_certificate_quotes(certificate_payload)
    except (TypeError, ValueError) as exc:
        return False, str(exc)
    expected = build_exact_in_route_true_key_interpretation_packet(quotes)
    if payload != expected.to_dict():
        return False, "true-key interpretation packet payload mismatch"
    return True, None


def compute_exact_in_route_rank_projection(
    quotes: Sequence[RouteQuote],
) -> tuple[tuple[ExactInRouteCanonicalKey, ...], dict[ExactInRouteCanonicalKey, int]]:
    if not isinstance(quotes, Sequence):
        raise TypeError("quotes must be a sequence")
    keys = tuple(exact_in_route_canonical_key(quote) for quote in quotes)
    ordered_unique_keys = tuple(sorted(set(keys)))
    if len(ordered_unique_keys) > 0xFFFFFFFFFFFFFFFF:
        raise ValueError("too many unique route keys for u64 ranking")
    rank_by_key = {route_key: rank for rank, route_key in enumerate(ordered_unique_keys)}
    return ordered_unique_keys, rank_by_key


def extract_exact_in_route_certificate_quotes(payload: object) -> tuple[RouteQuote, ...]:
    if not isinstance(payload, dict):
        raise TypeError("certificate payload must be a dict")
    candidates = payload.get("candidates")
    if not isinstance(candidates, list) or not candidates:
        raise ValueError("certificate payload must include non-empty candidates")
    return tuple(_route_quote_from_candidate_dict(candidate) for candidate in candidates)


def _candidate_set_hash_hex(candidates: Sequence[ExactInRouteCandidateCertificate]) -> str:
    payload = [candidate.to_dict() for candidate in candidates]
    return sha256_hex(domain_sep_bytes("exact_in_route_candidate_set", version=1) + canonical_json_bytes(payload))


def _route_key_to_dict(route_key: ExactInRouteCanonicalKey) -> dict[str, Any]:
    amount_out_neg, hop_count, leg_count, pool_sequence, intermediate_asset, asset_out = route_key
    return {
        "amount_out": int(-int(amount_out_neg)),
        "amount_out_neg": int(amount_out_neg),
        "hop_count": int(hop_count),
        "leg_count": int(leg_count),
        "pool_sequence": str(pool_sequence),
        "intermediate_asset": str(intermediate_asset),
        "asset_out": str(asset_out),
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


def _quote_to_dict(quote: RouteQuote) -> dict[str, Any]:
    return {
        "asset_in": quote.asset_in,
        "asset_out": quote.asset_out,
        "amount_in": int(quote.amount_in),
        "amount_out": int(quote.amount_out),
        "legs": [_leg_to_dict(leg) for leg in quote.legs],
    }


def _leg_to_dict(leg: RouteLeg) -> dict[str, Any]:
    return {
        "amount_in": int(leg.amount_in),
        "amount_out": int(leg.amount_out),
        "hops": [_hop_to_dict(hop) for hop in leg.hops],
    }


def _hop_to_dict(hop: RouteHop) -> dict[str, Any]:
    return {
        "pool_id": hop.pool_id,
        "asset_in": hop.asset_in,
        "asset_out": hop.asset_out,
        "amount_in": int(hop.amount_in),
        "amount_out": int(hop.amount_out),
    }


def _route_quote_from_candidate_dict(candidate: object) -> RouteQuote:
    if not isinstance(candidate, dict):
        raise TypeError("certificate candidate must be a dict")
    quote = candidate.get("quote")
    return _route_quote_from_dict(quote)


def _route_quote_from_dict(payload: object) -> RouteQuote:
    if not isinstance(payload, dict):
        raise TypeError("route quote payload must be a dict")
    asset_in = payload.get("asset_in")
    asset_out = payload.get("asset_out")
    amount_in = payload.get("amount_in")
    amount_out = payload.get("amount_out")
    legs = payload.get("legs")
    if not isinstance(asset_in, str) or not asset_in:
        raise ValueError("route quote asset_in must be a non-empty string")
    if not isinstance(asset_out, str) or not asset_out:
        raise ValueError("route quote asset_out must be a non-empty string")
    if not isinstance(amount_in, int) or isinstance(amount_in, bool) or amount_in <= 0:
        raise ValueError("route quote amount_in must be a positive int")
    if not isinstance(amount_out, int) or isinstance(amount_out, bool) or amount_out <= 0:
        raise ValueError("route quote amount_out must be a positive int")
    if not isinstance(legs, list) or not legs:
        raise ValueError("route quote legs must be a non-empty list")
    return RouteQuote(
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=int(amount_in),
        amount_out=int(amount_out),
        legs=tuple(_route_leg_from_dict(leg) for leg in legs),
    )


def _route_leg_from_dict(payload: object) -> RouteLeg:
    if not isinstance(payload, dict):
        raise TypeError("route leg payload must be a dict")
    amount_in = payload.get("amount_in")
    amount_out = payload.get("amount_out")
    hops = payload.get("hops")
    if not isinstance(amount_in, int) or isinstance(amount_in, bool) or amount_in <= 0:
        raise ValueError("route leg amount_in must be a positive int")
    if not isinstance(amount_out, int) or isinstance(amount_out, bool) or amount_out <= 0:
        raise ValueError("route leg amount_out must be a positive int")
    if not isinstance(hops, list) or not hops:
        raise ValueError("route leg hops must be a non-empty list")
    return RouteLeg(
        hops=tuple(_route_hop_from_dict(hop) for hop in hops),
        amount_in=int(amount_in),
        amount_out=int(amount_out),
    )


def _route_hop_from_dict(payload: object) -> RouteHop:
    if not isinstance(payload, dict):
        raise TypeError("route hop payload must be a dict")
    pool_id = payload.get("pool_id")
    asset_in = payload.get("asset_in")
    asset_out = payload.get("asset_out")
    amount_in = payload.get("amount_in")
    amount_out = payload.get("amount_out")
    if not isinstance(pool_id, str) or not pool_id:
        raise ValueError("route hop pool_id must be a non-empty string")
    if not isinstance(asset_in, str) or not asset_in:
        raise ValueError("route hop asset_in must be a non-empty string")
    if not isinstance(asset_out, str) or not asset_out:
        raise ValueError("route hop asset_out must be a non-empty string")
    if not isinstance(amount_in, int) or isinstance(amount_in, bool) or amount_in <= 0:
        raise ValueError("route hop amount_in must be a positive int")
    if not isinstance(amount_out, int) or isinstance(amount_out, bool) or amount_out <= 0:
        raise ValueError("route hop amount_out must be a positive int")
    return RouteHop(
        pool_id=pool_id,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=int(amount_in),
        amount_out=int(amount_out),
    )
