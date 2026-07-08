"""Risc0 spot state-proof transaction-order certificate helpers."""

from __future__ import annotations

from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from hashlib import sha256
from itertools import permutations

U32_MAX = 2**32 - 1
U128_MAX = 2**128 - 1
MAX_EXACT_STALE_ROUTE_ORDER_TXS = 8
MAX_ROUTE_PRICE_INTERVALS = 64
MAX_ROUTE_PRICE_INTERVAL_STALENESS_SECONDS = 300
TX_EXECUTION_ORDER_DOMAIN_V1 = b"tau_state_proof_tx_execution_order_v1:"
ROUTE_PRICE_INTERVALS_ROOT_DOMAIN_V1 = "zenodex.route_order.price_intervals_root.v1"
ROUTE_PRICE_INTERVAL_AUTHORITY_SCHEMA_V1 = "zenodex.route_order.price_interval_authority.v1"
ROUTE_PRICE_INTERVAL_AUTHORITY_ROOT_DOMAIN_V1 = "zenodex.route_order.price_interval_authority_root.v1"
ROUTE_PRICE_INTERVAL_AUTHORITY_POLICY_SCHEMA_V1 = "zenodex.route_order.price_interval_authority_policy.v1"
ROUTE_PRICE_INTERVAL_AUTHORITY_POLICY_ROOT_DOMAIN_V1 = (
    "zenodex.route_order.price_interval_authority_policy_root.v1"
)
ROUTE_PRICE_INTERVAL_SOURCE_VERIFICATION_STATUS_VERIFIED = "verified"
RISC0_SPOT_PROOF_TYPE_V1 = "risc0.zenodex_spot_transition.v1"
TX_EXECUTION_ORDER_COMMITMENT_RECEIPT_SCHEMA_V0 = (
    "zenodex/zeno_ledger/risc0_tx_execution_order_commitment/v0"
)


@dataclass(frozen=True)
class TxExecutionOrderCertificateV1:
    """Validated context order and Rust-compatible journal commitment.

    The Rust verifier remains authoritative for route-acceptance optimality.
    This value object only makes the Python-emitted order vector canonical and
    byte-compatible with `tx_execution_order_commitment_v1`.
    """

    tx_execution_order: tuple[int, ...]
    tx_execution_order_commitment: str

    def context_patch(self) -> dict[str, list[int]]:
        return {"tx_execution_order": list(self.tx_execution_order)}


@dataclass(frozen=True)
class TxExecutionOrderInputV1:
    """Minimal Python view used to propose a Rust-verifiable tx order."""

    sender_pubkey: str
    route_read_pool_ids: tuple[str, ...] = ()
    pool_write_ids: tuple[str, ...] = ()
    protected_values: tuple[tuple[str, int], ...] = ()


@dataclass(frozen=True)
class RoutePriceIntervalV1:
    """Python mirror of the Rust route price interval ABI.

    Values are e8-scaled integer bounds. The Rust verifier remains
    authoritative for admitting a transaction order; this object only lets the
    host compute the exact public-input root that Rust commits in the journal.
    """

    asset: str
    low_e8: int
    point_e8: int
    high_e8: int


@dataclass(frozen=True)
class RoutePriceIntervalDistortionCertificateV1:
    """Deterministic bound on value distortion admitted by price intervals.

    Bounds are integer-only. Bps fields are relative to each interval's
    `point_e8`; protected-value distortion uses the larger one-sided bps bound
    for the matching asset.
    """

    route_price_intervals_root: str
    max_downside_e8: int
    max_upside_e8: int
    max_width_e8: int
    max_downside_bps: int
    max_upside_bps: int
    max_width_bps: int
    protected_value_distortion_atoms: tuple[tuple[str, int], ...]


@dataclass(frozen=True)
class RoutePriceIntervalAuthorityV1:
    """Source and freshness envelope for non-empty route price intervals."""

    schema: str
    source_id: str
    source_root: bytes
    price_timestamp: int
    max_staleness_seconds: int
    route_price_intervals_root: bytes


@dataclass(frozen=True)
class RoutePriceIntervalAuthorityPolicySourceV1:
    """Verified source row admitted by a route price interval policy."""

    source_id: str
    source_root: bytes
    verification_root: bytes
    verification_status: str


@dataclass(frozen=True)
class RoutePriceIntervalAuthorityPolicyV1:
    """Verifier-pinned source policy for route price interval authority."""

    schema: str
    policy_id: str
    sources: tuple[RoutePriceIntervalAuthorityPolicySourceV1, ...]


@dataclass(frozen=True)
class StaleRouteOrderPlanV1:
    """Bounded stale-route repair plan plus Rust-compatible commitment."""

    certificate: TxExecutionOrderCertificateV1
    accepted_route_protected_values: tuple[tuple[str, int], ...]
    baseline_accepted_route_protected_values: tuple[tuple[str, int], ...]
    accepted_route_count: int
    baseline_accepted_route_count: int
    deferred_route_count: int

    @property
    def tx_execution_order(self) -> tuple[int, ...]:
        return self.certificate.tx_execution_order

    @property
    def tx_execution_order_commitment(self) -> str:
        return self.certificate.tx_execution_order_commitment

    def context_patch(self) -> dict[str, list[int]]:
        return self.certificate.context_patch()


@dataclass(frozen=True)
class TxExecutionOrderReceiptRequirementV1:
    """Host-side requirement for a body-bound order commitment receipt."""

    required: bool
    reason: str
    plan: StaleRouteOrderPlanV1
    proof_type: str

    @property
    def tx_execution_order(self) -> tuple[int, ...]:
        return self.plan.tx_execution_order

    @property
    def tx_execution_order_commitment(self) -> str:
        return self.plan.tx_execution_order_commitment

    def receipt(self) -> dict[str, str]:
        return build_tx_execution_order_commitment_receipt_v0(
            self.plan.certificate,
            proof_type=self.proof_type,
        )


def build_stale_route_order_certificate_v1(
    txs: Sequence[TxExecutionOrderInputV1],
) -> StaleRouteOrderPlanV1:
    """Propose the best bounded order for pre-state route quote liveness.

    This mirrors the Rust verifier's small-domain objective: preserve same-sender
    order, maximize accepted routes, then choose the lexicographically smallest
    order. The Rust state-proof verifier remains the authority for full txs.
    """

    normalized_txs = tuple(_normalize_tx_order_input_v1(tx) for tx in txs)
    tx_count = _require_tx_count(len(normalized_txs))
    if tx_count > MAX_EXACT_STALE_ROUTE_ORDER_TXS:
        raise ValueError("stale-route order exact search tx_count exceeded")

    baseline_order = tuple(range(tx_count))
    baseline_stats = _evaluate_stale_route_order_v1(normalized_txs, baseline_order)
    best_order, best_stats = _best_stale_route_order_v1(normalized_txs)
    certificate = build_tx_execution_order_certificate_v1(best_order, tx_count=tx_count)
    return StaleRouteOrderPlanV1(
        certificate=certificate,
        accepted_route_protected_values=best_stats[0],
        baseline_accepted_route_protected_values=baseline_stats[0],
        accepted_route_count=best_stats[1],
        baseline_accepted_route_count=baseline_stats[1],
        deferred_route_count=best_stats[2],
    )


def build_tx_execution_order_certificate_v1(
    raw_order: Sequence[int] | None,
    *,
    tx_count: int,
) -> TxExecutionOrderCertificateV1:
    """Validate `raw_order` and return the exact context vector plus digest.

    `None` and `[]` mirror the Rust context parser: both mean identity order for
    the block's transaction count. Non-empty orders must be a permutation of
    `0..tx_count-1`.
    """

    normalized_order = normalize_tx_execution_order_context_v1(raw_order, tx_count=tx_count)
    return TxExecutionOrderCertificateV1(
        tx_execution_order=normalized_order,
        tx_execution_order_commitment=tx_execution_order_commitment_hex_v1(normalized_order),
    )


def build_tx_execution_order_commitment_receipt_v0(
    certificate: TxExecutionOrderCertificateV1,
    *,
    proof_type: str = RISC0_SPOT_PROOF_TYPE_V1,
) -> dict[str, str]:
    if not isinstance(certificate, TxExecutionOrderCertificateV1):
        raise TypeError("certificate must be TxExecutionOrderCertificateV1")
    proof_type = _require_non_empty_str(proof_type, "proof_type")
    return {
        "schema": TX_EXECUTION_ORDER_COMMITMENT_RECEIPT_SCHEMA_V0,
        "proof_type": proof_type,
        "tx_execution_order_commitment": certificate.tx_execution_order_commitment,
    }


def stale_route_order_receipt_requirement_v1(
    txs: Sequence[TxExecutionOrderInputV1],
    *,
    proof_type: str = RISC0_SPOT_PROOF_TYPE_V1,
) -> TxExecutionOrderReceiptRequirementV1:
    proof_type = _require_non_empty_str(proof_type, "proof_type")
    plan = build_stale_route_order_certificate_v1(txs)
    value_improved = _protected_values_dominate_v1(
        plan.accepted_route_protected_values,
        plan.baseline_accepted_route_protected_values,
    )
    count_improved = (
        plan.accepted_route_protected_values
        == plan.baseline_accepted_route_protected_values
        and plan.accepted_route_count > plan.baseline_accepted_route_count
    )
    required = value_improved or count_improved
    return TxExecutionOrderReceiptRequirementV1(
        required=required,
        reason=(
            "stale_route_protected_value_improvement"
            if value_improved
            else (
                "stale_route_liveness_improvement"
                if count_improved
                else "no_stale_route_liveness_improvement"
            )
        ),
        plan=plan,
        proof_type=proof_type,
    )


def validate_stale_route_order_receipt_policy_v1(
    txs: Sequence[TxExecutionOrderInputV1],
    proof_receipts: Sequence[Mapping[str, object]],
    *,
    proof_type: str = RISC0_SPOT_PROOF_TYPE_V1,
) -> TxExecutionOrderReceiptRequirementV1:
    requirement = stale_route_order_receipt_requirement_v1(txs, proof_type=proof_type)
    order_receipts = _matching_order_receipts_v0(proof_receipts, proof_type=requirement.proof_type)
    if len(order_receipts) > 1:
        raise ValueError("tx_execution_order receipt ambiguous")
    if not order_receipts:
        if requirement.required:
            raise ValueError("tx_execution_order receipt required for stale-route improvement")
        return requirement

    receipt_commitment = _require_receipt_commitment_v0(order_receipts[0])
    if receipt_commitment != requirement.tx_execution_order_commitment:
        raise ValueError("tx_execution_order receipt commitment mismatch")
    return requirement


def normalize_tx_execution_order_context_v1(
    raw_order: Sequence[int] | None,
    *,
    tx_count: int,
) -> tuple[int, ...]:
    tx_count = _require_tx_count(tx_count)
    if raw_order is None or len(raw_order) == 0:
        return tuple(range(tx_count))
    if len(raw_order) != tx_count:
        raise ValueError("tx_execution_order length mismatch")

    seen = [False] * tx_count
    normalized: list[int] = []
    for raw_index in raw_order:
        index = _require_u32_index(raw_index)
        if index >= tx_count:
            raise ValueError("tx_execution_order index out of range")
        if seen[index]:
            raise ValueError("tx_execution_order duplicate index")
        seen[index] = True
        normalized.append(index)
    return tuple(normalized)


def tx_execution_order_commitment_hex_v1(order: Sequence[int]) -> str:
    hasher = sha256()
    hasher.update(TX_EXECUTION_ORDER_DOMAIN_V1)
    hasher.update(_require_u32_index(len(order)).to_bytes(4, "big"))
    for raw_index in order:
        hasher.update(_require_u32_index(raw_index).to_bytes(4, "big"))
    return hasher.hexdigest()


def route_price_intervals_root_bytes_v1(raw_intervals: Sequence[RoutePriceIntervalV1]) -> bytes:
    """Return the Rust-compatible root for route price interval public inputs."""

    intervals = _normalize_route_price_intervals_v1(raw_intervals)
    hasher = sha256()
    hasher.update(
        _encode_length_prefixed_str_v1(
            ROUTE_PRICE_INTERVALS_ROOT_DOMAIN_V1,
            "route price intervals root domain",
        )
    )
    hasher.update(len(intervals).to_bytes(4, "big"))
    for interval in intervals:
        hasher.update(_encode_length_prefixed_str_v1(interval.asset, "route price interval asset"))
        hasher.update(interval.low_e8.to_bytes(16, "big"))
        hasher.update(interval.point_e8.to_bytes(16, "big"))
        hasher.update(interval.high_e8.to_bytes(16, "big"))
    return hasher.digest()


def route_price_intervals_root_hex_v1(raw_intervals: Sequence[RoutePriceIntervalV1]) -> str:
    return route_price_intervals_root_bytes_v1(raw_intervals).hex()


def route_price_interval_distortion_certificate_v1(
    raw_intervals: Sequence[RoutePriceIntervalV1],
    *,
    protected_values: Sequence[tuple[str, int]] = (),
) -> RoutePriceIntervalDistortionCertificateV1:
    """Return an integer certificate bounding route-price interval distortion.

    A positive-width interval with `point_e8 == 0` has unbounded relative error
    and is rejected by this certificate even though it remains hashable for ABI
    compatibility.
    """

    intervals = _normalize_route_price_intervals_v1(raw_intervals)
    route_price_intervals_root = route_price_intervals_root_hex_v1(intervals)
    max_downside_e8 = 0
    max_upside_e8 = 0
    max_width_e8 = 0
    max_downside_bps = 0
    max_upside_bps = 0
    max_width_bps = 0
    max_side_bps_by_asset: dict[str, int] = {}

    for interval in intervals:
        downside_e8 = interval.point_e8 - interval.low_e8
        upside_e8 = interval.high_e8 - interval.point_e8
        width_e8 = interval.high_e8 - interval.low_e8
        if interval.point_e8 == 0:
            if width_e8 != 0:
                raise ValueError("route price interval point_e8 zero with positive width")
            downside_bps = 0
            upside_bps = 0
            width_bps = 0
        else:
            downside_bps = _ceil_div_nonnegative(downside_e8 * 10_000, interval.point_e8)
            upside_bps = _ceil_div_nonnegative(upside_e8 * 10_000, interval.point_e8)
            width_bps = _ceil_div_nonnegative(width_e8 * 10_000, interval.point_e8)

        max_downside_e8 = max(max_downside_e8, downside_e8)
        max_upside_e8 = max(max_upside_e8, upside_e8)
        max_width_e8 = max(max_width_e8, width_e8)
        max_downside_bps = max(max_downside_bps, downside_bps)
        max_upside_bps = max(max_upside_bps, upside_bps)
        max_width_bps = max(max_width_bps, width_bps)
        max_side_bps_by_asset[interval.asset] = max(downside_bps, upside_bps)

    protected_value_distortion_atoms: list[tuple[str, int]] = []
    for asset, amount_atoms in _normalize_protected_values_v1(protected_values):
        max_side_bps = max_side_bps_by_asset.get(asset)
        if max_side_bps is None:
            raise ValueError("protected value asset missing route price interval")
        distortion_atoms = _ceil_div_nonnegative(amount_atoms * max_side_bps, 10_000)
        if distortion_atoms > U128_MAX:
            raise ValueError("protected value distortion_atoms overflow")
        if distortion_atoms > 0:
            protected_value_distortion_atoms.append((asset, distortion_atoms))

    return RoutePriceIntervalDistortionCertificateV1(
        route_price_intervals_root=route_price_intervals_root,
        max_downside_e8=max_downside_e8,
        max_upside_e8=max_upside_e8,
        max_width_e8=max_width_e8,
        max_downside_bps=max_downside_bps,
        max_upside_bps=max_upside_bps,
        max_width_bps=max_width_bps,
        protected_value_distortion_atoms=tuple(protected_value_distortion_atoms),
    )


def validate_route_price_interval_width_policy_v1(
    raw_intervals: Sequence[RoutePriceIntervalV1],
    *,
    max_width_bps: int,
) -> RoutePriceIntervalDistortionCertificateV1:
    """Reject intervals whose full width exceeds a deterministic bps policy."""

    max_width_bps = _require_u128_atoms(max_width_bps, "route price interval max_width_bps")
    certificate = route_price_interval_distortion_certificate_v1(raw_intervals)
    if certificate.max_width_bps > max_width_bps:
        raise ValueError("route price interval width exceeds policy")
    return certificate


def route_price_interval_authority_root_bytes_v1(
    authority: RoutePriceIntervalAuthorityV1 | None,
) -> bytes:
    hasher = sha256()
    hasher.update(
        _encode_length_prefixed_str_v1(
            ROUTE_PRICE_INTERVAL_AUTHORITY_ROOT_DOMAIN_V1,
            "route price interval authority root domain",
        )
    )
    if authority is None:
        hasher.update(bytes([0]))
        return hasher.digest()

    normalized = _normalize_route_price_interval_authority_v1(authority)
    hasher.update(bytes([1]))
    hasher.update(_encode_length_prefixed_str_v1(normalized.schema, "route price interval authority schema"))
    hasher.update(_encode_length_prefixed_str_v1(normalized.source_id, "route price interval authority source_id"))
    hasher.update(normalized.source_root)
    hasher.update(normalized.price_timestamp.to_bytes(8, "big"))
    hasher.update(normalized.max_staleness_seconds.to_bytes(8, "big"))
    hasher.update(normalized.route_price_intervals_root)
    return hasher.digest()


def route_price_interval_authority_root_hex_v1(
    authority: RoutePriceIntervalAuthorityV1 | None,
) -> str:
    return route_price_interval_authority_root_bytes_v1(authority).hex()


def route_price_interval_authority_policy_root_bytes_v1(
    policy: RoutePriceIntervalAuthorityPolicyV1 | None,
) -> bytes:
    hasher = sha256()
    hasher.update(
        _encode_length_prefixed_str_v1(
            ROUTE_PRICE_INTERVAL_AUTHORITY_POLICY_ROOT_DOMAIN_V1,
            "route price interval authority policy root domain",
        )
    )
    if policy is None:
        hasher.update(bytes([0]))
        return hasher.digest()

    normalized = _normalize_route_price_interval_authority_policy_v1(policy)
    hasher.update(bytes([1]))
    hasher.update(_encode_length_prefixed_str_v1(normalized.schema, "route price interval authority policy schema"))
    hasher.update(_encode_length_prefixed_str_v1(normalized.policy_id, "route price interval authority policy_id"))
    hasher.update(len(normalized.sources).to_bytes(4, "big"))
    for source in normalized.sources:
        hasher.update(_encode_length_prefixed_str_v1(source.source_id, "route price interval authority source_id"))
        hasher.update(source.source_root)
        hasher.update(source.verification_root)
        hasher.update(
            _encode_length_prefixed_str_v1(
                source.verification_status,
                "route price interval authority verification_status",
            )
        )
    return hasher.digest()


def route_price_interval_authority_policy_root_hex_v1(
    policy: RoutePriceIntervalAuthorityPolicyV1 | None,
) -> str:
    return route_price_interval_authority_policy_root_bytes_v1(policy).hex()


def validate_route_price_interval_authority_v1(
    raw_intervals: Sequence[RoutePriceIntervalV1],
    authority: RoutePriceIntervalAuthorityV1 | None,
    *,
    policy: RoutePriceIntervalAuthorityPolicyV1 | None = None,
    block_timestamp: int,
    max_interval_width_bps: int | None = None,
) -> tuple[str, str]:
    intervals_root = route_price_intervals_root_bytes_v1(raw_intervals)
    if max_interval_width_bps is not None:
        validate_route_price_interval_width_policy_v1(raw_intervals, max_width_bps=max_interval_width_bps)
    if len(raw_intervals) == 0:
        if authority is not None:
            raise ValueError("route price interval authority without intervals")
        if policy is not None:
            raise ValueError("route price interval authority policy without intervals")
        return (
            route_price_interval_authority_root_hex_v1(None),
            route_price_interval_authority_policy_root_hex_v1(None),
        )
    if authority is None:
        raise ValueError("route price interval authority required")
    if policy is None:
        raise ValueError("route price interval authority policy required")

    normalized = _normalize_route_price_interval_authority_v1(authority)
    normalized_policy = _normalize_route_price_interval_authority_policy_v1(policy)
    _validate_route_price_interval_authority_source_policy(normalized, normalized_policy)
    block_timestamp = _require_u64(normalized_value=block_timestamp, field_name="block_timestamp")
    if normalized.route_price_intervals_root != intervals_root:
        raise ValueError("route price interval authority root mismatch")
    if normalized.price_timestamp > block_timestamp:
        raise ValueError("route price interval authority timestamp future")
    if block_timestamp - normalized.price_timestamp > normalized.max_staleness_seconds:
        raise ValueError("route price interval authority stale")
    return (
        route_price_interval_authority_root_hex_v1(normalized),
        route_price_interval_authority_policy_root_hex_v1(normalized_policy),
    )


def _best_stale_route_order_v1(
    txs: tuple[TxExecutionOrderInputV1, ...],
) -> tuple[tuple[int, ...], tuple[tuple[tuple[str, int], ...], int, int]]:
    best_order: tuple[int, ...] | None = None
    best_stats: tuple[tuple[tuple[str, int], ...], int, int] | None = None
    for candidate in permutations(range(len(txs))):
        if not _preserves_same_sender_order_v1(txs, candidate):
            continue
        stats = _evaluate_stale_route_order_v1(txs, candidate)
        if best_order is None or _stale_route_order_is_better_v1(candidate, stats, best_order, best_stats):
            best_order = candidate
            best_stats = stats
    if best_order is None or best_stats is None:
        raise ValueError("stale-route order search found no valid order")
    return best_order, best_stats


def _stale_route_order_is_better_v1(
    candidate_order: tuple[int, ...],
    candidate_stats: tuple[tuple[tuple[str, int], ...], int, int],
    best_order: tuple[int, ...],
    best_stats: tuple[tuple[tuple[str, int], ...], int, int] | None,
) -> bool:
    if best_stats is None:
        return True
    candidate_values = candidate_stats[0]
    best_values = best_stats[0]
    if _protected_values_dominate_v1(candidate_values, best_values):
        return True
    if _protected_values_dominate_v1(best_values, candidate_values):
        return False
    return candidate_stats[1] > best_stats[1] or (
        candidate_stats[1] == best_stats[1] and candidate_order < best_order
    )


def _evaluate_stale_route_order_v1(
    txs: tuple[TxExecutionOrderInputV1, ...],
    order: tuple[int, ...],
) -> tuple[tuple[tuple[str, int], ...], int, int]:
    accepted_writer_pool_ids: set[str] = set()
    protected_values_by_asset: dict[str, int] = {}
    accepted_routes = 0
    deferred_routes = 0
    for index in order:
        tx = txs[index]
        route_read_pool_ids = set(tx.route_read_pool_ids)
        route_accepted = route_read_pool_ids.isdisjoint(accepted_writer_pool_ids)
        if route_read_pool_ids:
            if route_accepted:
                accepted_routes += 1
                _add_protected_values_v1(protected_values_by_asset, tx.protected_values)
            else:
                deferred_routes += 1
        if route_accepted:
            accepted_writer_pool_ids.update(_effective_pool_write_set_v1(tx))
    return tuple(sorted(protected_values_by_asset.items())), accepted_routes, deferred_routes


def _effective_pool_write_set_v1(tx: TxExecutionOrderInputV1) -> tuple[str, ...]:
    return _normalize_pool_ids_v1((*tx.pool_write_ids, *tx.route_read_pool_ids), "pool_write_ids")


def _preserves_same_sender_order_v1(
    txs: tuple[TxExecutionOrderInputV1, ...],
    order: tuple[int, ...],
) -> bool:
    position_by_index = {index: position for position, index in enumerate(order)}
    for left in range(len(txs)):
        for right in range(left + 1, len(txs)):
            if txs[left].sender_pubkey == txs[right].sender_pubkey:
                if position_by_index[left] > position_by_index[right]:
                    return False
    return True


def _normalize_tx_order_input_v1(tx: TxExecutionOrderInputV1) -> TxExecutionOrderInputV1:
    if not isinstance(tx, TxExecutionOrderInputV1):
        raise TypeError("tx order input must be TxExecutionOrderInputV1")
    if not isinstance(tx.sender_pubkey, str) or tx.sender_pubkey == "":
        raise ValueError("sender_pubkey must be a non-empty string")
    return TxExecutionOrderInputV1(
        sender_pubkey=tx.sender_pubkey,
        route_read_pool_ids=_normalize_pool_ids_v1(tx.route_read_pool_ids, "route_read_pool_ids"),
        pool_write_ids=_normalize_pool_ids_v1(tx.pool_write_ids, "pool_write_ids"),
        protected_values=_normalize_protected_values_v1(tx.protected_values),
    )


def _normalize_protected_values_v1(
    raw_values: Sequence[tuple[str, int]],
) -> tuple[tuple[str, int], ...]:
    values_by_asset: dict[str, int] = {}
    for raw_entry in raw_values:
        if not isinstance(raw_entry, tuple) or len(raw_entry) != 2:
            raise TypeError("protected_values entries must be (asset, amount_atoms) tuples")
        asset, amount_atoms = raw_entry
        asset = _require_non_empty_str(asset, "protected_values asset")
        amount_atoms = _require_u128_atoms(amount_atoms, "protected_values amount_atoms")
        if amount_atoms == 0:
            continue
        previous = values_by_asset.get(asset, 0)
        total = previous + amount_atoms
        if total > U128_MAX:
            raise ValueError("protected_values amount_atoms overflow")
        values_by_asset[asset] = total
    return tuple(sorted(values_by_asset.items()))


def _normalize_route_price_intervals_v1(
    raw_intervals: Sequence[RoutePriceIntervalV1],
) -> tuple[RoutePriceIntervalV1, ...]:
    if len(raw_intervals) > MAX_ROUTE_PRICE_INTERVALS:
        raise ValueError("route price intervals exceeds max")

    intervals_by_asset: dict[str, RoutePriceIntervalV1] = {}
    for raw_interval in raw_intervals:
        if not isinstance(raw_interval, RoutePriceIntervalV1):
            raise TypeError("route_price_intervals entries must be RoutePriceIntervalV1")
        if not isinstance(raw_interval.asset, str):
            raise TypeError("route price interval asset must be a string")
        if raw_interval.asset == "":
            raise ValueError("route price interval asset empty")
        asset = raw_interval.asset
        low_e8 = _require_u128_atoms(raw_interval.low_e8, "route price interval low_e8")
        point_e8 = _require_u128_atoms(raw_interval.point_e8, "route price interval point_e8")
        high_e8 = _require_u128_atoms(raw_interval.high_e8, "route price interval high_e8")
        if asset in intervals_by_asset:
            raise ValueError("duplicate route price interval asset")
        if low_e8 > point_e8 or point_e8 > high_e8:
            raise ValueError("route price interval bounds invalid")
        intervals_by_asset[asset] = RoutePriceIntervalV1(
            asset=asset,
            low_e8=low_e8,
            point_e8=point_e8,
            high_e8=high_e8,
        )
    return tuple(intervals_by_asset[asset] for asset in sorted(intervals_by_asset))


def _normalize_route_price_interval_authority_v1(
    authority: RoutePriceIntervalAuthorityV1,
) -> RoutePriceIntervalAuthorityV1:
    if not isinstance(authority, RoutePriceIntervalAuthorityV1):
        raise TypeError("authority must be RoutePriceIntervalAuthorityV1")
    if authority.schema != ROUTE_PRICE_INTERVAL_AUTHORITY_SCHEMA_V1:
        raise ValueError("route price interval authority schema mismatch")
    source_id = _require_non_empty_str(authority.source_id, "route price interval authority source_id")
    source_root = _require_bytes32(authority.source_root, "route price interval authority source_root")
    if source_root == bytes(32):
        raise ValueError("route price interval authority source root empty")
    price_timestamp = _require_u64(
        normalized_value=authority.price_timestamp,
        field_name="route price interval authority price_timestamp",
    )
    max_staleness_seconds = _require_u64(
        normalized_value=authority.max_staleness_seconds,
        field_name="route price interval authority max_staleness_seconds",
    )
    if max_staleness_seconds == 0:
        raise ValueError("route price interval authority staleness zero")
    if max_staleness_seconds > MAX_ROUTE_PRICE_INTERVAL_STALENESS_SECONDS:
        raise ValueError("route price interval authority staleness exceeds max")
    route_price_intervals_root = _require_bytes32(
        authority.route_price_intervals_root,
        "route price interval authority route_price_intervals_root",
    )
    return RoutePriceIntervalAuthorityV1(
        schema=authority.schema,
        source_id=source_id,
        source_root=source_root,
        price_timestamp=price_timestamp,
        max_staleness_seconds=max_staleness_seconds,
        route_price_intervals_root=route_price_intervals_root,
    )


def _normalize_route_price_interval_authority_policy_v1(
    policy: RoutePriceIntervalAuthorityPolicyV1,
) -> RoutePriceIntervalAuthorityPolicyV1:
    if not isinstance(policy, RoutePriceIntervalAuthorityPolicyV1):
        raise TypeError("policy must be RoutePriceIntervalAuthorityPolicyV1")
    if policy.schema != ROUTE_PRICE_INTERVAL_AUTHORITY_POLICY_SCHEMA_V1:
        raise ValueError("route price interval authority policy schema mismatch")
    policy_id = _require_non_empty_str(policy.policy_id, "route price interval authority policy_id")
    if len(policy.sources) == 0:
        raise ValueError("route price interval authority policy sources empty")
    if len(policy.sources) > 16:
        raise ValueError("route price interval authority policy sources exceeds max")

    seen: set[tuple[str, bytes]] = set()
    normalized_sources: list[RoutePriceIntervalAuthorityPolicySourceV1] = []
    for source in policy.sources:
        if not isinstance(source, RoutePriceIntervalAuthorityPolicySourceV1):
            raise TypeError("policy source must be RoutePriceIntervalAuthorityPolicySourceV1")
        source_id = _require_non_empty_str(source.source_id, "route price interval authority policy source_id")
        source_root = _require_bytes32(source.source_root, "route price interval authority policy source_root")
        if source_root == bytes(32):
            raise ValueError("route price interval authority policy source_root empty")
        verification_root = _require_bytes32(
            source.verification_root,
            "route price interval authority policy verification_root",
        )
        if verification_root == bytes(32):
            raise ValueError("route price interval authority policy verification_root empty")
        verification_status = _require_non_empty_str(
            source.verification_status,
            "route price interval authority policy verification_status",
        )
        if verification_status != ROUTE_PRICE_INTERVAL_SOURCE_VERIFICATION_STATUS_VERIFIED:
            raise ValueError("route price interval authority policy source unverified")
        key = (source_id, source_root)
        if key in seen:
            raise ValueError("route price interval authority policy duplicate source")
        seen.add(key)
        normalized_sources.append(
            RoutePriceIntervalAuthorityPolicySourceV1(
                source_id=source_id,
                source_root=source_root,
                verification_root=verification_root,
                verification_status=verification_status,
            )
        )
    return RoutePriceIntervalAuthorityPolicyV1(
        schema=policy.schema,
        policy_id=policy_id,
        sources=tuple(normalized_sources),
    )


def _validate_route_price_interval_authority_source_policy(
    authority: RoutePriceIntervalAuthorityV1,
    policy: RoutePriceIntervalAuthorityPolicyV1,
) -> None:
    for source in policy.sources:
        if source.source_id == authority.source_id and source.source_root == authority.source_root:
            return
    raise ValueError("route price interval authority source not in policy")


def _ceil_div_nonnegative(numerator: int, denominator: int) -> int:
    if numerator < 0:
        raise ValueError("ceil_div numerator must be nonnegative")
    if denominator <= 0:
        raise ValueError("ceil_div denominator must be positive")
    return (numerator + denominator - 1) // denominator


def _add_protected_values_v1(
    totals: dict[str, int],
    values: tuple[tuple[str, int], ...],
) -> None:
    for asset, amount_atoms in values:
        previous = totals.get(asset, 0)
        total = previous + amount_atoms
        if total > U128_MAX:
            raise ValueError("accepted route protected value overflow")
        totals[asset] = total


def _protected_values_dominate_v1(
    left: tuple[tuple[str, int], ...],
    right: tuple[tuple[str, int], ...],
) -> bool:
    left_map = dict(left)
    right_map = dict(right)
    strictly_greater = False
    for asset in set(left_map) | set(right_map):
        left_amount = left_map.get(asset, 0)
        right_amount = right_map.get(asset, 0)
        if left_amount < right_amount:
            return False
        if left_amount > right_amount:
            strictly_greater = True
    return strictly_greater


def _matching_order_receipts_v0(
    proof_receipts: Sequence[Mapping[str, object]],
    *,
    proof_type: str,
) -> tuple[Mapping[str, object], ...]:
    matches: list[Mapping[str, object]] = []
    for receipt in proof_receipts:
        if not isinstance(receipt, Mapping):
            raise TypeError("proof_receipts entries must be mappings")
        if receipt.get("schema") != TX_EXECUTION_ORDER_COMMITMENT_RECEIPT_SCHEMA_V0:
            continue
        if receipt.get("proof_type") != proof_type:
            continue
        matches.append(receipt)
    return tuple(matches)


def _require_receipt_commitment_v0(receipt: Mapping[str, object]) -> str:
    value = receipt.get("tx_execution_order_commitment")
    if not isinstance(value, str):
        raise TypeError("tx_execution_order receipt commitment must be a string")
    if len(value) != 64:
        raise ValueError("tx_execution_order receipt commitment must be 32-byte hex")
    try:
        bytes.fromhex(value)
    except ValueError as exc:
        raise ValueError("tx_execution_order receipt commitment must be hex") from exc
    return value.lower()


def _require_non_empty_str(value: str, field_name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{field_name} must be a string")
    if value == "":
        raise ValueError(f"{field_name} must be non-empty")
    return value


def _normalize_pool_ids_v1(raw_pool_ids: Sequence[str], field_name: str) -> tuple[str, ...]:
    pool_ids: set[str] = set()
    for raw_pool_id in raw_pool_ids:
        if not isinstance(raw_pool_id, str) or raw_pool_id == "":
            raise ValueError(f"{field_name} entries must be non-empty strings")
        pool_ids.add(raw_pool_id)
    return tuple(sorted(pool_ids))


def _require_tx_count(value: int) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError("tx_count must be an integer")
    if value < 0 or value > U32_MAX:
        raise ValueError("tx_count must be a u32")
    return value


def _require_u32_index(value: int) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError("tx_execution_order entries must be u32")
    if value < 0 or value > U32_MAX:
        raise ValueError("tx_execution_order entries must be u32")
    return value


def _require_u128_atoms(value: int, field_name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{field_name} must be an integer")
    if value < 0 or value > U128_MAX:
        raise ValueError(f"{field_name} must be a u128")
    return value


def _require_u64(*, normalized_value: int, field_name: str) -> int:
    if not isinstance(normalized_value, int) or isinstance(normalized_value, bool):
        raise TypeError(f"{field_name} must be an integer")
    if normalized_value < 0 or normalized_value > 2**64 - 1:
        raise ValueError(f"{field_name} must be a u64")
    return normalized_value


def _require_bytes32(value: bytes, field_name: str) -> bytes:
    if not isinstance(value, bytes):
        raise TypeError(f"{field_name} must be bytes")
    if len(value) != 32:
        raise ValueError(f"{field_name} must be 32 bytes")
    return value


def _encode_length_prefixed_str_v1(value: str, field_name: str) -> bytes:
    value = _require_non_empty_str(value, field_name)
    encoded = value.encode("utf-8")
    if len(encoded) > U32_MAX:
        raise ValueError(f"{field_name} length must be a u32")
    return len(encoded).to_bytes(4, "big") + encoded
