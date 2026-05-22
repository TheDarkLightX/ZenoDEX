from __future__ import annotations

"""
Deterministic boundary-path explorer for receipt verifiers.

This is an offline discovery tool. It explores distinct reject-order paths for
branchy receipt verification code and emits a replayable atlas of
outcome/path-signature pairs.
"""

import argparse
import copy
import hashlib
import heapq
import json
import sys
from dataclasses import asdict, dataclass, is_dataclass, replace
from enum import Enum
from pathlib import Path
from typing import Any, Callable, Sequence

ROOT_DIR = Path(__file__).resolve().parents[1]
if str(ROOT_DIR) not in sys.path:
    sys.path.insert(0, str(ROOT_DIR))

from src.core.amm_dispatch import swap_exact_in_for_pool, swap_exact_out_for_pool
from src.core.confidential_extension_receipts import (
    confidential_extension_receipt_hash,
    make_confidential_extension_receipt,
    verify_confidential_extension_receipt,
)
from src.core.quote_receipts import (
    make_route_quote_receipt,
    receipt_hash,
    verify_route_quote_receipt,
)
from src.core.routing import RouteHop, RouteLeg, RouteQuote
from src.state.pools import PoolState, PoolStatus


OutcomeFn = Callable[[Any], str]
MutationFn = Callable[[Any], Any]


def _pool(pid: str, a0: str, a1: str, r0: int, r1: int, fee_bps: int = 0) -> PoolState:
    return PoolState(
        pool_id=pid,
        asset0=min(a0, a1),
        asset1=max(a0, a1),
        reserve0=r0 if a0 < a1 else r1,
        reserve1=r1 if a0 < a1 else r0,
        fee_bps=fee_bps,
        lp_supply=1,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )


def _valid_quote_target() -> tuple[dict[str, Any], dict[str, PoolState]]:
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 1_000, 1_000, 0),
    }
    pool = pools["p_ab"]
    amount_out = 50
    amount_in, _ = swap_exact_out_for_pool(
        pool,
        reserve_in=int(pool.reserve0),
        reserve_out=int(pool.reserve1),
        amount_out=amount_out,
    )
    quote = RouteQuote(
        asset_in="A",
        asset_out="B",
        amount_in=int(amount_in),
        amount_out=amount_out,
        legs=(
            RouteLeg(
                amount_in=int(amount_in),
                amount_out=amount_out,
                hops=(
                    RouteHop(
                        pool_id="p_ab",
                        asset_in="A",
                        asset_out="B",
                        amount_in=int(amount_in),
                        amount_out=amount_out,
                    ),
                ),
            ),
        ),
    )
    return make_route_quote_receipt(kind="exact_out", quote=quote, pools_by_id=pools), pools


def _valid_quote_exact_in_target() -> tuple[dict[str, Any], dict[str, PoolState]]:
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 1_000, 1_000, 0),
    }
    pool = pools["p_ab"]
    amount_in = 50
    amount_out, _ = swap_exact_in_for_pool(
        pool,
        reserve_in=int(pool.reserve0),
        reserve_out=int(pool.reserve1),
        amount_in=amount_in,
    )
    quote = RouteQuote(
        asset_in="A",
        asset_out="B",
        amount_in=amount_in,
        amount_out=int(amount_out),
        legs=(
            RouteLeg(
                amount_in=amount_in,
                amount_out=int(amount_out),
                hops=(
                    RouteHop(
                        pool_id="p_ab",
                        asset_in="A",
                        asset_out="B",
                        amount_in=amount_in,
                        amount_out=int(amount_out),
                    ),
                ),
            ),
        ),
    )
    return make_route_quote_receipt(kind="exact_in", quote=quote, pools_by_id=pools), pools


NITRO_PCR0 = "a" * 96
NITRO_PCR8 = "b" * 96
POLICY_DIGEST = "0x" + ("d" * 64)
APPROVED_MEASUREMENTS = {f"nitro:pcr0:{NITRO_PCR0}:pcr8:{NITRO_PCR8}"}


def _valid_confidential_receipt() -> dict[str, Any]:
    return make_confidential_extension_receipt(
        extension_id="route-premium-v1",
        provider_id="provider-1",
        request_id="req-1",
        policy_version="tee-policy-v1",
        policy_digest=POLICY_DIGEST,
        measurement=f"nitro:pcr0:{NITRO_PCR0}:pcr8:{NITRO_PCR8}",
        do_execute=1,
        policy_ok=1,
        nonce_unused=1,
        output_bound_ok=1,
        current_epoch=10,
        attestation_epoch=8,
        max_attestation_age=2,
        fee_charged=7,
        receipt_fee=7,
        credit_before=40,
        credit_after=33,
        provider_balance_before=9,
        provider_balance_after=16,
    )


def _mutate_body_only(payload: object, mutator: Callable[[dict[str, Any]], None], *, rehash: bool) -> object:
    out = copy.deepcopy(payload)
    if not isinstance(out, dict):
        raise TypeError("payload must be a dict")
    body = out.get("body")
    if not isinstance(body, dict):
        raise TypeError("payload.body must be a dict")
    mutator(body)
    if rehash:
        schema = str(body.get("schema", ""))
        if schema == "zenodex/route_quote_receipt/v1":
            out["receipt_hash"] = receipt_hash(body)
        else:
            out["receipt_hash"] = confidential_extension_receipt_hash(body)
    return out


def _mutate_quote_seed(
    seed: object,
    *,
    receipt_mutator: Callable[[dict[str, Any]], dict[str, Any]] | None = None,
    pools_mutator: Callable[[dict[str, PoolState]], None] | None = None,
) -> object:
    if not isinstance(seed, tuple) or len(seed) != 2:
        raise TypeError("quote seed must be a (receipt, pools) tuple")
    receipt = copy.deepcopy(seed[0])
    pools = copy.deepcopy(seed[1])
    if receipt_mutator is not None:
        receipt = receipt_mutator(receipt)
    if pools_mutator is not None:
        if not isinstance(pools, dict):
            raise TypeError("quote pools must be a dict")
        pools_mutator(pools)
    return receipt, pools


@dataclass(frozen=True)
class Mutation:
    name: str
    apply: MutationFn


@dataclass(frozen=True)
class Target:
    name: str
    trace_files: tuple[Path, ...]
    valid_seed: Any
    outcome: OutcomeFn
    mutations: tuple[Mutation, ...]


@dataclass(frozen=True)
class BoundaryCase:
    mutation: str
    depth: int
    outcome_label: str
    path_id: str
    path_length: int


@dataclass(frozen=True)
class BoundaryTargetReport:
    target: str
    total_cases: int
    unique_outcome_count: int
    unique_path_count: int
    cases: tuple[BoundaryCase, ...]


QUOTE_FILE = (ROOT_DIR / "src/core/quote_receipts.py").resolve()
CONFIDENTIAL_FILE = (ROOT_DIR / "src/core/confidential_extension_receipts.py").resolve()


def _quote_outcome(payload: Any) -> str:
    receipt, pools = payload
    ok, err = verify_route_quote_receipt(receipt, pools_by_id=pools)
    return "ok" if ok else f"reject:{err}"


def _confidential_outcome(payload: Any) -> str:
    ok, err = verify_confidential_extension_receipt(payload, approved_measurements=APPROVED_MEASUREMENTS)
    return "ok" if ok else f"reject:{err}"


QUOTE_SEED = _valid_quote_target()
QUOTE_EXACT_IN_SEED = _valid_quote_exact_in_target()
CONFIDENTIAL_SEED = _valid_confidential_receipt()


TARGETS: tuple[Target, ...] = (
    Target(
        name="quote_receipt_verify",
        trace_files=(QUOTE_FILE,),
        valid_seed=QUOTE_SEED,
        outcome=_quote_outcome,
        mutations=(
            Mutation(
                "missing_receipt_hash",
                lambda seed: _mutate_quote_seed(
                    seed,
                    receipt_mutator=lambda receipt: {**copy.deepcopy(receipt), "receipt_hash": ""},
                ),
            ),
            Mutation(
                "hash_mismatch",
                lambda seed: _mutate_quote_seed(
                    seed,
                    receipt_mutator=lambda receipt: _mutate_body_only(
                        receipt,
                        lambda body: body.__setitem__("amount_out", 999),
                        rehash=False,
                    ),
                ),
            ),
            Mutation(
                "bad_kind",
                lambda seed: _mutate_quote_seed(
                    seed,
                    receipt_mutator=lambda receipt: _mutate_body_only(
                        receipt,
                        lambda body: body.__setitem__("kind", "weird"),
                        rehash=True,
                    ),
                ),
            ),
            Mutation(
                "unexpected_canonical_route_certificate",
                lambda seed: _mutate_quote_seed(
                    seed,
                    receipt_mutator=lambda receipt: _mutate_body_only(
                        receipt,
                        lambda body: body.__setitem__("canonical_route_certificate", {}),
                        rehash=True,
                    ),
                ),
            ),
            Mutation(
                "bad_quote_epoch",
                lambda seed: _mutate_quote_seed(
                    seed,
                    receipt_mutator=lambda receipt: _mutate_body_only(
                        receipt,
                        lambda body: body.__setitem__("quote_epoch", -1),
                        rehash=True,
                    ),
                ),
            ),
            Mutation(
                "bad_pools",
                lambda seed: _mutate_quote_seed(
                    seed,
                    receipt_mutator=lambda receipt: _mutate_body_only(
                        receipt,
                        lambda body: body.__setitem__("pools", []),
                        rehash=True,
                    ),
                ),
            ),
            Mutation(
                "bad_legs",
                lambda seed: _mutate_quote_seed(
                    seed,
                    receipt_mutator=lambda receipt: _mutate_body_only(
                        receipt,
                        lambda body: body.__setitem__("legs", {}),
                        rehash=True,
                    ),
                ),
            ),
            Mutation(
                "bad_body_assets",
                lambda seed: _mutate_quote_seed(
                    seed,
                    receipt_mutator=lambda receipt: _mutate_body_only(
                        receipt,
                        lambda body: body.__setitem__("asset_in", ""),
                        rehash=True,
                    ),
                ),
            ),
            Mutation(
                "bad_pool_fingerprint",
                lambda seed: _mutate_quote_seed(
                    seed,
                    receipt_mutator=lambda receipt: _mutate_body_only(
                        receipt,
                        lambda body: body["pools"].__setitem__("p_ab", 7),
                        rehash=True,
                    ),
                ),
            ),
            Mutation(
                "missing_pool_fingerprint",
                lambda seed: _mutate_quote_seed(
                    seed,
                    receipt_mutator=lambda receipt: _mutate_body_only(receipt, lambda body: body["pools"].clear(), rehash=True),
                ),
            ),
            Mutation(
                "missing_pool",
                lambda seed: _mutate_quote_seed(seed, pools_mutator=lambda pools: pools.clear()),
            ),
            Mutation(
                "pool_snapshot_mismatch",
                lambda seed: _mutate_quote_seed(
                    seed,
                    pools_mutator=lambda pools: pools.__setitem__(
                        "p_ab",
                        replace(pools["p_ab"], reserve0=int(pools["p_ab"].reserve0) + 1),
                    ),
                ),
            ),
            Mutation(
                "bad_leg",
                lambda seed: _mutate_quote_seed(
                    seed,
                    receipt_mutator=lambda receipt: _mutate_body_only(
                        receipt,
                        lambda body: body["legs"].__setitem__(0, []),
                        rehash=True,
                    ),
                ),
            ),
            Mutation(
                "bad_hops",
                lambda seed: _mutate_quote_seed(
                    seed,
                    receipt_mutator=lambda receipt: _mutate_body_only(
                        receipt,
                        lambda body: body["legs"][0].__setitem__("hops", {}),
                        rehash=True,
                    ),
                ),
            ),
            Mutation(
                "bad_leg_amounts",
                lambda seed: _mutate_quote_seed(
                    seed,
                    receipt_mutator=lambda receipt: _mutate_body_only(
                        receipt,
                        lambda body: body["legs"][0].__setitem__("amount_in", 0),
                        rehash=True,
                    ),
                ),
            ),
            Mutation(
                "bad_pool_id",
                lambda seed: _mutate_quote_seed(
                    seed,
                    receipt_mutator=lambda receipt: _mutate_body_only(
                        receipt,
                        lambda body: body["legs"][0]["hops"][0].__setitem__("pool_id", ""),
                        rehash=True,
                    ),
                ),
            ),
            Mutation(
                "bad_assets",
                lambda seed: _mutate_quote_seed(
                    seed,
                    receipt_mutator=lambda receipt: _mutate_body_only(
                        receipt,
                        lambda body: body["legs"][0]["hops"][0].__setitem__("asset_in", None),
                        rehash=True,
                    ),
                ),
            ),
            Mutation(
                "leg_asset_in_mismatch",
                lambda seed: _mutate_quote_seed(
                    seed,
                    receipt_mutator=lambda receipt: _mutate_body_only(
                        receipt,
                        lambda body: body["legs"][0]["hops"][0].__setitem__("asset_in", "Z"),
                        rehash=True,
                    ),
                ),
            ),
            Mutation(
                "bad_pool_direction",
                lambda seed: _mutate_quote_seed(
                    seed,
                    receipt_mutator=lambda receipt: _mutate_body_only(
                        receipt,
                        lambda body: body["legs"][0]["hops"][0].__setitem__("asset_out", "C"),
                        rehash=True,
                    ),
                ),
            ),
            Mutation(
                "hop_quote_error",
                lambda seed: _mutate_quote_seed(
                    seed,
                    receipt_mutator=lambda receipt: _mutate_body_only(
                        receipt,
                        lambda body: body["legs"][0]["hops"][0].__setitem__("amount_out", 1_001),
                        rehash=True,
                    ),
                ),
            ),
            Mutation(
                "hop_quote_mismatch",
                lambda seed: _mutate_quote_seed(
                    seed,
                    receipt_mutator=lambda receipt: _mutate_body_only(
                        receipt,
                        lambda body: body["legs"][0]["hops"][0].__setitem__("amount_in", 999),
                        rehash=True,
                    ),
                ),
            ),
            Mutation(
                "bad_body_amounts",
                lambda seed: _mutate_quote_seed(
                    seed,
                    receipt_mutator=lambda receipt: _mutate_body_only(
                        receipt,
                        lambda body: body.__setitem__("amount_out", "50"),
                        rehash=True,
                    ),
                ),
            ),
            Mutation(
                "totals_mismatch",
                lambda seed: _mutate_quote_seed(
                    seed,
                    receipt_mutator=lambda receipt: _mutate_body_only(
                        receipt,
                        lambda body: body.__setitem__("amount_out", 999),
                        rehash=True,
                    ),
                ),
            ),
            Mutation("whole_list", lambda seed: ([], copy.deepcopy(seed[1]))),
            Mutation("body_not_dict", lambda seed: ({**copy.deepcopy(seed[0]), "body": []}, copy.deepcopy(seed[1]))),
        ),
    ),
    Target(
        name="quote_receipt_verify_exact_in_certificate",
        trace_files=(QUOTE_FILE,),
        valid_seed=QUOTE_EXACT_IN_SEED,
        outcome=_quote_outcome,
        mutations=(
            Mutation(
                "missing_receipt_hash",
                lambda seed: _mutate_quote_seed(
                    seed,
                    receipt_mutator=lambda receipt: {**copy.deepcopy(receipt), "receipt_hash": ""},
                ),
            ),
            Mutation(
                "hash_mismatch",
                lambda seed: _mutate_quote_seed(
                    seed,
                    receipt_mutator=lambda receipt: _mutate_body_only(
                        receipt,
                        lambda body: body.__setitem__("amount_out", int(body["amount_out"]) + 1),
                        rehash=False,
                    ),
                ),
            ),
            Mutation(
                "bad_canonical_route_certificate_payload_type",
                lambda seed: _mutate_quote_seed(
                    seed,
                    receipt_mutator=lambda receipt: _mutate_body_only(
                        receipt,
                        lambda body: body.__setitem__("canonical_route_certificate", []),
                        rehash=True,
                    ),
                ),
            ),
            Mutation(
                "certificate_asset_in_mismatch",
                lambda seed: _mutate_quote_seed(
                    seed,
                    receipt_mutator=lambda receipt: _mutate_body_only(
                        receipt,
                        lambda body: body.__setitem__("asset_in", "Z"),
                        rehash=True,
                    ),
                ),
            ),
            Mutation(
                "certificate_asset_out_mismatch",
                lambda seed: _mutate_quote_seed(
                    seed,
                    receipt_mutator=lambda receipt: _mutate_body_only(
                        receipt,
                        lambda body: body.__setitem__("asset_out", "Z"),
                        rehash=True,
                    ),
                ),
            ),
            Mutation(
                "certificate_amount_in_mismatch",
                lambda seed: _mutate_quote_seed(
                    seed,
                    receipt_mutator=lambda receipt: _mutate_body_only(
                        receipt,
                        lambda body: body.__setitem__("amount_in", int(body["amount_in"]) + 1),
                        rehash=True,
                    ),
                ),
            ),
            Mutation(
                "certificate_amount_out_mismatch",
                lambda seed: _mutate_quote_seed(
                    seed,
                    receipt_mutator=lambda receipt: _mutate_body_only(
                        receipt,
                        lambda body: body.__setitem__("amount_out", int(body["amount_out"]) + 1),
                        rehash=True,
                    ),
                ),
            ),
            Mutation(
                "certificate_legs_mismatch",
                lambda seed: _mutate_quote_seed(
                    seed,
                    receipt_mutator=lambda receipt: _mutate_body_only(
                        receipt,
                        lambda body: body["legs"][0].__setitem__("amount_in", int(body["legs"][0]["amount_in"]) + 1),
                        rehash=True,
                    ),
                ),
            ),
            Mutation("whole_list", lambda seed: ([], copy.deepcopy(seed[1]))),
            Mutation("body_not_dict", lambda seed: ({**copy.deepcopy(seed[0]), "body": []}, copy.deepcopy(seed[1]))),
        ),
    ),
    Target(
        name="confidential_receipt_verify",
        trace_files=(CONFIDENTIAL_FILE,),
        valid_seed=CONFIDENTIAL_SEED,
        outcome=_confidential_outcome,
        mutations=(
            Mutation(
                "missing_receipt_hash",
                lambda seed: {**copy.deepcopy(seed), "receipt_hash": ""},
            ),
            Mutation(
                "hash_mismatch",
                lambda seed: _mutate_body_only(
                    seed,
                    lambda body: body["host"].__setitem__("nonce_unused", 0),
                    rehash=False,
                ),
            ),
            Mutation(
                "bad_schema",
                lambda seed: _mutate_body_only(seed, lambda body: body.__setitem__("schema", "bad"), rehash=True),
            ),
            Mutation(
                "bad_extension_id",
                lambda seed: _mutate_body_only(seed, lambda body: body.__setitem__("extension_id", ""), rehash=True),
            ),
            Mutation(
                "bad_provider_id",
                lambda seed: _mutate_body_only(seed, lambda body: body.__setitem__("provider_id", ""), rehash=True),
            ),
            Mutation(
                "bad_request_id",
                lambda seed: _mutate_body_only(seed, lambda body: body.__setitem__("request_id", ""), rehash=True),
            ),
            Mutation(
                "bad_policy_version",
                lambda seed: _mutate_body_only(seed, lambda body: body.__setitem__("policy_version", ""), rehash=True),
            ),
            Mutation(
                "bad_policy_digest",
                lambda seed: _mutate_body_only(seed, lambda body: body.__setitem__("policy_digest", "zzz"), rehash=True),
            ),
            Mutation(
                "bad_measurement",
                lambda seed: _mutate_body_only(seed, lambda body: body.__setitem__("measurement", "nitro:pcr0:abc"), rehash=True),
            ),
            Mutation(
                "measurement_not_approved",
                lambda seed: _mutate_body_only(
                    seed,
                    lambda body: body.__setitem__("measurement", f"nitro:pcr0:{'c' * 96}:pcr8:{'d' * 96}"),
                    rehash=True,
                ),
            ),
            Mutation("bad_host", lambda seed: _mutate_body_only(seed, lambda body: body.__setitem__("host", []), rehash=True)),
            Mutation(
                "bad_attestation",
                lambda seed: _mutate_body_only(seed, lambda body: body.__setitem__("attestation", []), rehash=True),
            ),
            Mutation(
                "bad_accounting",
                lambda seed: _mutate_body_only(seed, lambda body: body.__setitem__("accounting", []), rehash=True),
            ),
            Mutation(
                "bad_numeric_field",
                lambda seed: _mutate_body_only(
                    seed,
                    lambda body: body["accounting"].__setitem__("receipt_fee", "6"),
                    rehash=True,
                ),
            ),
            Mutation(
                "bad_do_execute",
                lambda seed: _mutate_body_only(
                    seed,
                    lambda body: body["host"].__setitem__("do_execute", 2),
                    rehash=True,
                ),
            ),
            Mutation(
                "bad_policy_ok",
                lambda seed: _mutate_body_only(
                    seed,
                    lambda body: body["host"].__setitem__("policy_ok", 2),
                    rehash=True,
                ),
            ),
            Mutation(
                "bad_nonce_unused",
                lambda seed: _mutate_body_only(
                    seed,
                    lambda body: body["host"].__setitem__("nonce_unused", 2),
                    rehash=True,
                ),
            ),
            Mutation(
                "bad_output_bound_ok",
                lambda seed: _mutate_body_only(
                    seed,
                    lambda body: body["host"].__setitem__("output_bound_ok", 2),
                    rehash=True,
                ),
            ),
            Mutation(
                "stale_attestation",
                lambda seed: _mutate_body_only(
                    seed,
                    lambda body: body["attestation"].__setitem__("current_epoch", 11),
                    rehash=True,
                ),
            ),
            Mutation(
                "attestation_guard_failed",
                lambda seed: _mutate_body_only(
                    seed,
                    lambda body: body["host"].__setitem__("nonce_unused", 0),
                    rehash=True,
                ),
            ),
            Mutation(
                "accounting_guard_failed",
                lambda seed: _mutate_body_only(
                    seed,
                    lambda body: body["accounting"].__setitem__("receipt_fee", 6),
                    rehash=True,
                ),
            ),
            Mutation("whole_list", lambda _seed: []),
            Mutation("body_not_dict", lambda seed: {**copy.deepcopy(seed), "body": []}),
        ),
    ),
)


TARGET_INDEX = {target.name: target for target in TARGETS}


def _hash_lines(lines: Sequence[str]) -> str:
    return hashlib.sha256("\n".join(lines).encode("utf-8")).hexdigest()[:16]


def _stable_jsonable(value: Any) -> Any:
    if value is None or isinstance(value, (bool, int, float, str)):
        return value
    if isinstance(value, Enum):
        return str(value.value)
    if isinstance(value, Path):
        return str(value)
    if is_dataclass(value):
        return _stable_jsonable(asdict(value))
    if isinstance(value, dict):
        return {str(key): _stable_jsonable(val) for key, val in sorted(value.items(), key=lambda item: str(item[0]))}
    if isinstance(value, (list, tuple)):
        return [_stable_jsonable(item) for item in value]
    if isinstance(value, set):
        return sorted(_stable_jsonable(item) for item in value)
    return repr(value)


def _payload_signature(payload: Any) -> str:
    canonical = json.dumps(_stable_jsonable(payload), sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()[:16]


def _payload_expandable(target: Target, payload: Any) -> bool:
    if target.name.startswith("quote_receipt_verify"):
        return (
            isinstance(payload, tuple)
            and len(payload) == 2
            and isinstance(payload[0], dict)
            and isinstance(payload[0].get("body"), dict)
            and isinstance(payload[1], dict)
        )
    if target.name == "confidential_receipt_verify":
        return isinstance(payload, dict) and isinstance(payload.get("body"), dict)
    return False


def _trace_outcome(target: Target, payload: Any) -> tuple[str, str, int]:
    trace_names = {str(path.resolve()) for path in target.trace_files}
    lines: list[str] = []
    last_loc: str | None = None

    def tracer(frame, event, arg):  # type: ignore[no-untyped-def]
        nonlocal last_loc
        if event == "line":
            filename = str(Path(frame.f_code.co_filename).resolve())
            if filename in trace_names:
                loc = f"{Path(filename).name}:{frame.f_lineno}"
                if loc != last_loc:
                    lines.append(loc)
                    last_loc = loc
        return tracer

    previous = sys.gettrace()
    try:
        sys.settrace(tracer)
        outcome = target.outcome(payload)
    finally:
        sys.settrace(previous)
    return outcome, _hash_lines(lines), len(lines)


def explore_target(name: str, *, max_depth: int = 2, max_frontier: int = 256) -> BoundaryTargetReport:
    target = TARGET_INDEX[name]
    cases: list[BoundaryCase] = []
    seen_pairs: set[tuple[str, str]] = set()
    seen_outcomes: set[str] = set()
    seen_paths: set[str] = set()
    seen_payloads: set[str] = {_payload_signature(target.valid_seed)}
    frontier: list[tuple[int, int, int, str, Any]] = [(0, 0, 0, "valid_seed", copy.deepcopy(target.valid_seed))]
    explored = 0
    schedule_seq = 1

    while frontier and explored < max_frontier:
        _priority, depth, _seq, mutation_name, payload = heapq.heappop(frontier)
        explored += 1
        outcome, path_id, path_length = _trace_outcome(target, payload)
        pair = (outcome, path_id)
        if pair not in seen_pairs:
            seen_pairs.add(pair)
            seen_outcomes.add(outcome)
            seen_paths.add(path_id)
            cases.append(
                BoundaryCase(
                    mutation=mutation_name,
                    depth=depth,
                    outcome_label=outcome,
                    path_id=path_id,
                    path_length=path_length,
                )
            )

        if depth >= max_depth or not _payload_expandable(target, payload):
            continue

        for order, mutation in enumerate(target.mutations):
            try:
                next_payload = mutation.apply(copy.deepcopy(payload))
            except Exception:
                continue
            signature = _payload_signature(next_payload)
            if signature in seen_payloads:
                continue
            seen_payloads.add(signature)
            next_name = mutation.name if mutation_name == "valid_seed" else f"{mutation_name}->{mutation.name}"
            # Prioritize children of deeper/longer traces first, while keeping a stable
            # mutation order inside a parent. This is a bounded scheduling heuristic,
            # not symbolic path solving.
            heapq.heappush(
                frontier,
                (-path_length, depth + 1, schedule_seq + order, next_name, next_payload),
            )
        schedule_seq += len(target.mutations)

    cases_sorted = tuple(sorted(cases, key=lambda case: (case.outcome_label, case.depth, case.mutation, case.path_id)))
    return BoundaryTargetReport(
        target=name,
        total_cases=len(cases_sorted),
        unique_outcome_count=len(seen_outcomes),
        unique_path_count=len(seen_paths),
        cases=cases_sorted,
    )


def explore_all_targets(*, max_depth: int = 2, max_frontier: int = 256) -> tuple[BoundaryTargetReport, ...]:
    return tuple(explore_target(target.name, max_depth=max_depth, max_frontier=max_frontier) for target in TARGETS)


def _reports_json(reports: Sequence[BoundaryTargetReport]) -> dict[str, Any]:
    return {
        "schema": "zenodex/receipt-boundary-concolic/v1",
        "reports": [asdict(report) for report in reports],
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Deterministic boundary-path explorer for receipt verifiers.")
    parser.add_argument(
        "--target",
        default="all",
        choices=("all",) + tuple(sorted(TARGET_INDEX)),
    )
    parser.add_argument(
        "--format",
        default="json",
        choices=("json", "text"),
    )
    parser.add_argument("--max-depth", type=int, default=2)
    parser.add_argument("--max-frontier", type=int, default=256)
    args = parser.parse_args(list(argv) if argv is not None else None)

    reports = (
        explore_all_targets(max_depth=args.max_depth, max_frontier=args.max_frontier)
        if args.target == "all"
        else (explore_target(args.target, max_depth=args.max_depth, max_frontier=args.max_frontier),)
    )
    if args.format == "json":
        print(json.dumps(_reports_json(reports), indent=2, sort_keys=True))
    else:
        for report in reports:
            print(f"[{report.target}] cases={report.total_cases} outcomes={report.unique_outcome_count} paths={report.unique_path_count}")
            for case in report.cases:
                print(
                    f"  - depth={case.depth} {case.mutation}: {case.outcome_label} "
                    f"path={case.path_id} len={case.path_length}"
                )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
