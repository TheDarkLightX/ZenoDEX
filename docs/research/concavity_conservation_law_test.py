#!/usr/bin/env python3
"""CPMM Concavity Evidence: Window Algebra, Lipschitz Increment, and Stateful Attack Bound.

The Lean file proves:
1. An algebraic identity: sqrt(2*L/m) = sqrt(M) when L=K/M, m=2*K/M^2
   (epsilon=0 case; production window includes epsilon).
2. A generic Lipschitz increment: f(a_A)-f(0) <= L*a_A for any L-Lipschitz f.
3. The stateful CPMM attack gain bound: out_B_without_A - out_B_with_A <= L*a_A
   for the exact CPMM model f(x) = K*x/(M+x), with K, M, a_A, a_B > 0.
4. The fee-bearing version: gain <= gamma*K*a_A/M for f(x) = K*gamma*x/(M+gamma*x).

The stateful gain bound (theorem 3-4) is the formal bridge between the generic
Lipschitz increment and the exact stateful CPMM attack model. The empirical
tests below verify the simulator matches the formal bound on a seeded corpus.

CONTINUOUS VS ROUNDED SCOPE: The Lean theorems prove the bound for the
continuous real-valued CPMM model. The empirical simulator uses
integer-truncated reserves after A fills. The [Lean PROVEN + empirical replay]
label means the continuous theorem is formally proven and the rounded
simulator corpus is consistent with it. The rounded-reserve semantics are NOT
formally proved.

LEAN-PROVEN vs EMPIRICAL:
- [Lean PROVEN]: algebraic identities (m formula, window=sqrt(M) at eps=0),
  generic Lipschitz increment, stateful attack gain bound, and
  donation/no-output optimizers.
- [Empirical]: depth-monotone gain, falsification of the concavity bound,
  min_out cap behavior, frontier characterization.

For CPMM f(x) = K*x/(M+x):
  m = 2*K*M / (M + x_max)^3  (strong concavity parameter)
  L = K/M  (spot price = Lipschitz constant)
  At margin (x=0): m = 2*K/M^2 = 2*L/M

TESTS:
1. CPMM concavity parameter formula: m = 2*K*gamma^2/M^2 [Lean PROVEN, gamma=1]
2. CPMM window identity: sqrt(2*L/m) = sqrt(M) [Lean PROVEN, epsilon=0]
3. Stateful gain vs Lipschitz envelope [Lean PROVEN + empirical replay]
4. Second-order concavity bound falsified [Empirical falsification, regression guard]
5. Actual stateful gain decreases with M [Empirical, NOT formalized]
6. Min_out cap makes sacrifice infeasible [Empirical]
7. Donation/no-output exact optimizer [Lean PROVEN + empirical replay]
7b. Fee-bearing donation/no-output exact optimizer [Lean PROVEN + empirical replay]
8. Filled-A vs donation optimizer scope split [Empirical falsification]
9. Tradeoff frontier characterization [Empirical]
10. Pool-parameter endpoint m certificate [Lean bridge + empirical replay]
11. Exact curvature m certificate [closed-form probe + deterministic replay]
12. Symmetric exact curvature minimizer at D/2 [Lean PROVEN + empirical replay]
13. Exact stationary curvature m certificate [Lean normalized bridge + exact rational replay]
14. Exact curvature float-overflow domain rejection [CBC boundary]
15. Rational interval m certificate [Lean interval bridge + exact replay]
16. Best-cover rational interval m certificate [exact replay portfolio]
17. Greedy interval-refinement m certificate [Lean monotonicity bridge]
18. Bounded optimal midpoint-refinement audit [exact DP replay]
19. Exact count audit

Determinism: All tests use fixed seeds.
"""

import math
import random
from dataclasses import dataclass
import hashlib
import json
from enum import Enum
from fractions import Fraction
from collections.abc import Mapping


@dataclass(frozen=True)
class Pool:
    reserve_in: int
    reserve_out: int
    fee_bps: int


POOL_M_CERTIFICATE_SCHEMA = "zenodex.cpmm_split_m_certificate.v1"
POOL_EXACT_M_CERTIFICATE_SCHEMA = "zenodex.cpmm_split_exact_m_certificate.v1"
POOL_STATIONARY_M_CERTIFICATE_SCHEMA = "zenodex.cpmm_split_stationary_m_certificate.v1"
POOL_INTERVAL_M_CERTIFICATE_SCHEMA = "zenodex.cpmm_split_interval_m_certificate.v1"
MAX_POOL_M_CERTIFICATE_BYTES = 4096
MAX_POOL_INTERVAL_M_CERTIFICATE_BYTES = 65536
MAX_INTERVAL_M_CERTIFICATE_INTERVALS = 256
MAX_OPTIMAL_MIDPOINT_INTERVALS = 16
MAX_ADAPTIVE_CENTER_DENOMINATOR = 1_000_000
MAX_RATIONAL_ABS_BITS = 4096
MAX_EXACT_CURVATURE_FLOAT_DOMAIN_BITS = 128
POOL_M_CERT_TOL = 1e-12
POOL_INTERVAL_CERTIFICATE_KEYS = frozenset({
    "authority_effects",
    "domain",
    "domain_hash",
    "endpoint_bound",
    "interval_count",
    "intervals",
    "m",
    "schema",
})
POOL_INTERVAL_ENTRY_KEYS = frozenset({"lo", "hi", "lower_bound"})
POOL_STATIONARY_CERTIFICATE_KEYS = frozenset({
    "authority_effects",
    "domain",
    "domain_hash",
    "endpoint_bound",
    "m",
    "minimizer_a",
    "q",
    "scale",
    "schema",
    "stationarity_lhs",
    "stationarity_rhs",
})


class PoolMReject(str, Enum):
    BAD_JSON = "bad_json"
    DUPLICATE_KEY = "duplicate_key"
    NONCANONICAL_BYTES = "noncanonical_bytes"
    CERTIFICATE_TOO_LARGE = "certificate_too_large"
    BAD_SCHEMA = "bad_schema"
    AUTHORITY_EFFECTS_PRESENT = "authority_effects_present"
    BAD_DOMAIN = "bad_domain"
    DOMAIN_HASH_MISMATCH = "domain_hash_mismatch"
    BAD_NUMERIC_FIELD = "bad_numeric_field"
    STALE_ENDPOINT_BOUND = "stale_endpoint_bound"
    STALE_EXACT_BOUND = "stale_exact_bound"
    STALE_MINIMIZER = "stale_minimizer"
    STALE_STATIONARITY = "stale_stationarity"
    BAD_RATIONAL_FIELD = "bad_rational_field"
    BAD_INTERVALS = "bad_intervals"
    TOO_MANY_INTERVALS = "too_many_intervals"
    STALE_INTERVAL_BOUND = "stale_interval_bound"
    BAD_M = "bad_m"


@dataclass(frozen=True)
class PoolMCheckResult:
    accepted: bool
    reject: PoolMReject | None
    m: float | None = None
    endpoint_bound: float | None = None
    exact_bound: float | None = None
    minimizer_a: float | None = None
    m_fraction: Fraction | None = None
    interval_bound: float | None = None
    interval_count: int | None = None
    domain_hash: str | None = None


class DuplicateKey(ValueError):
    pass


def cpmm_output_cont(p: Pool, amount_in: float) -> float:
    if amount_in <= 0.0:
        return 0.0
    gamma = 1.0 - p.fee_bps / 10000.0
    net = amount_in * gamma
    if net <= 0.0:
        return 0.0
    return p.reserve_out * net / (p.reserve_in + net)


def spot_price(p: Pool) -> float:
    gamma = 1.0 - p.fee_bps / 10000.0
    return gamma * p.reserve_out / p.reserve_in


def strong_concavity_param(p: Pool, x_max: float) -> float:
    K = p.reserve_out
    M = p.reserve_in
    gamma = 1.0 - p.fee_bps / 10000.0
    denom = M + gamma * x_max
    if denom <= 0:
        return 0.0
    return 2.0 * K * gamma * gamma * M / (denom ** 3)


def _pool_domain_valid(p: Pool) -> bool:
    return (
        isinstance(p.reserve_in, int)
        and isinstance(p.reserve_out, int)
        and isinstance(p.fee_bps, int)
        and p.reserve_in > 0
        and p.reserve_out > 0
        and 0 <= p.fee_bps < 10000
    )


def _bounded_int(value: object, *, positive: bool, max_bits: int) -> bool:
    if isinstance(value, bool) or not isinstance(value, int):
        return False
    if positive and value <= 0:
        return False
    if not positive and value < 0:
        return False
    return value.bit_length() <= max_bits


def _exact_curvature_float_domain_valid(p0: Pool, p1: Pool, D: int) -> bool:
    """Bound the research-only float minimizer before any float conversion."""
    return (
        _pool_domain_valid(p0)
        and _pool_domain_valid(p1)
        and _bounded_int(D, positive=False, max_bits=MAX_EXACT_CURVATURE_FLOAT_DOMAIN_BITS)
        and _bounded_int(p0.reserve_in, positive=True, max_bits=MAX_EXACT_CURVATURE_FLOAT_DOMAIN_BITS)
        and _bounded_int(p0.reserve_out, positive=True, max_bits=MAX_EXACT_CURVATURE_FLOAT_DOMAIN_BITS)
        and _bounded_int(p1.reserve_in, positive=True, max_bits=MAX_EXACT_CURVATURE_FLOAT_DOMAIN_BITS)
        and _bounded_int(p1.reserve_out, positive=True, max_bits=MAX_EXACT_CURVATURE_FLOAT_DOMAIN_BITS)
    )


def _pool_domain_payload(p0: Pool, p1: Pool, D: int) -> Mapping[str, object]:
    return {
        "D": D,
        "p0": {
            "reserve_in": p0.reserve_in,
            "reserve_out": p0.reserve_out,
            "fee_bps": p0.fee_bps,
        },
        "p1": {
            "reserve_in": p1.reserve_in,
            "reserve_out": p1.reserve_out,
            "fee_bps": p1.fee_bps,
        },
    }


def _canonical_json_bytes(obj: Mapping[str, object]) -> bytes:
    return json.dumps(
        obj,
        sort_keys=True,
        separators=(",", ":"),
        allow_nan=False,
    ).encode("utf-8")


def _reject_duplicate_keys(pairs: list[tuple[str, object]]) -> dict[str, object]:
    out: dict[str, object] = {}
    for key, value in pairs:
        if key in out:
            raise DuplicateKey(key)
        out[key] = value
    return out


def pool_parameter_m_domain_hash(p0: Pool, p1: Pool, D: int) -> str:
    payload = _pool_domain_payload(p0, p1, D)
    return hashlib.sha256(_canonical_json_bytes(payload)).hexdigest()


def split_endpoint_curvature_lower_bound(p0: Pool, p1: Pool, D: int) -> float:
    """Lean-proven conservative endpoint lower bound for split curvature."""
    if not (_pool_domain_valid(p0) and _pool_domain_valid(p1) and D >= 0):
        return 0.0
    return strong_concavity_param(p0, float(D)) + strong_concavity_param(p1, float(D))


def split_curvature_at(p0: Pool, p1: Pool, D: int, a: float) -> float:
    return strong_concavity_param(p0, a) + strong_concavity_param(p1, float(D) - a)


def split_exact_curvature_minimizer(p0: Pool, p1: Pool, D: int) -> float:
    """Closed-form minimizer for the two-pool split curvature curve.

    This is a research checker formula over Python floats. Lean currently
    consumes only a supplied curvature floor, not this minimizer derivation.
    """
    if not _exact_curvature_float_domain_valid(p0, p1, D):
        return float("nan")
    if D == 0:
        return 0.0

    c0 = 1.0 - p0.fee_bps / 10000.0
    c1 = 1.0 - p1.fee_bps / 10000.0
    k0 = float(p0.reserve_out)
    m0 = float(p0.reserve_in)
    k1 = float(p1.reserve_out)
    m1 = float(p1.reserve_in)
    coeff0 = 2.0 * c0 * c0 * k0 * m0
    coeff1 = 2.0 * c1 * c1 * k1 * m1
    ratio = (coeff0 * c0) / (coeff1 * c1)
    r = ratio ** 0.25
    total = float(D) + m0 / c0 + m1 / c1
    denom = r / c0 + 1.0 / c1
    v = total / denom
    u = r * v
    candidate = (u - m0) / c0
    return min(max(candidate, 0.0), float(D))


def split_exact_curvature_lower_bound(p0: Pool, p1: Pool, D: int) -> float:
    """Research-scope exact minimum of the split curvature curve."""
    if not _exact_curvature_float_domain_valid(p0, p1, D):
        return 0.0
    a_star = split_exact_curvature_minimizer(p0, p1, D)
    candidates = [
        split_curvature_at(p0, p1, D, 0.0),
        split_curvature_at(p0, p1, D, float(D)),
        split_curvature_at(p0, p1, D, a_star),
    ]
    if any(not math.isfinite(value) for value in candidates):
        return 0.0
    return min(candidates)


def _fee_multiplier_fraction(p: Pool) -> Fraction:
    return Fraction(10000 - p.fee_bps, 10000)


def _fraction_payload(value: Fraction) -> Mapping[str, object]:
    return {"num": value.numerator, "den": value.denominator}


def _fraction_from_payload(value: object) -> Fraction | None:
    if not isinstance(value, dict) or set(value.keys()) != {"num", "den"}:
        return None
    num = value.get("num")
    den = value.get("den")
    if isinstance(num, bool) or isinstance(den, bool):
        return None
    if not isinstance(num, int) or not isinstance(den, int) or den <= 0:
        return None
    if abs(num).bit_length() > MAX_RATIONAL_ABS_BITS or den.bit_length() > MAX_RATIONAL_ABS_BITS:
        return None
    out = Fraction(num, den)
    if out.numerator != num or out.denominator != den:
        return None
    return out


def _field_fraction(obj: Mapping[str, object], key: str) -> Fraction | None:
    return _fraction_from_payload(obj.get(key))


def strong_concavity_param_fraction(p: Pool, x: Fraction) -> Fraction:
    K = Fraction(p.reserve_out, 1)
    M = Fraction(p.reserve_in, 1)
    c = _fee_multiplier_fraction(p)
    denom = M + c * x
    if denom <= 0:
        return Fraction(0, 1)
    return 2 * K * c * c * M / (denom ** 3)


def split_endpoint_curvature_lower_bound_fraction(p0: Pool, p1: Pool, D: int) -> Fraction:
    if not (_pool_domain_valid(p0) and _pool_domain_valid(p1) and D >= 0):
        return Fraction(0, 1)
    return (
        strong_concavity_param_fraction(p0, Fraction(D, 1))
        + strong_concavity_param_fraction(p1, Fraction(D, 1))
    )


def split_interval_curvature_lower_bound_fraction(
    p0: Pool,
    p1: Pool,
    D: int,
    lo: Fraction,
    hi: Fraction,
) -> Fraction:
    return (
        strong_concavity_param_fraction(p0, hi)
        + strong_concavity_param_fraction(p1, Fraction(D, 1) - lo)
    )


def split_curvature_at_fraction(p0: Pool, p1: Pool, D: int, a: Fraction) -> Fraction:
    return (
        strong_concavity_param_fraction(p0, a)
        + strong_concavity_param_fraction(p1, Fraction(D, 1) - a)
    )


def _split_stationary_certificate_values(
    p0: Pool,
    p1: Pool,
    D: int,
    a: Fraction,
) -> dict[str, Fraction]:
    c0 = _fee_multiplier_fraction(p0)
    c1 = _fee_multiplier_fraction(p1)
    K0 = Fraction(p0.reserve_out, 1)
    M0 = Fraction(p0.reserve_in, 1)
    K1 = Fraction(p1.reserve_out, 1)
    M1 = Fraction(p1.reserve_in, 1)
    x0 = M0 + c0 * a
    y0 = M1 + c1 * (Fraction(D, 1) - a)
    coeff0 = 2 * c0 * c0 * K0 * M0
    coeff1 = 2 * c1 * c1 * K1 * M1
    stationarity_lhs = coeff0 * c0 * (y0 ** 4)
    stationarity_rhs = coeff1 * c1 * (x0 ** 4)
    scale = coeff0 / (x0 ** 3)
    q = c1 * x0 / (c0 * y0)
    m = split_curvature_at_fraction(p0, p1, D, a)
    return {
        "endpoint_bound": split_endpoint_curvature_lower_bound_fraction(p0, p1, D),
        "m": m,
        "q": q,
        "scale": scale,
        "stationarity_lhs": stationarity_lhs,
        "stationarity_rhs": stationarity_rhs,
    }


def _uniform_interval_bounds(D: int, interval_count: int) -> list[tuple[Fraction, Fraction]]:
    if D == 0:
        return [(Fraction(0, 1), Fraction(0, 1))]
    return [
        (Fraction(D * i, interval_count), Fraction(D * (i + 1), interval_count))
        for i in range(interval_count)
    ]


def _clamp_fraction(value: Fraction, lo: Fraction, hi: Fraction) -> Fraction:
    return min(max(value, lo), hi)


def _curvature_hint_fraction(p0: Pool, p1: Pool, D: int, interval_count: int) -> Fraction:
    if D == 0:
        return Fraction(0, 1)
    hint = split_exact_curvature_minimizer(p0, p1, D)
    if not math.isfinite(hint):
        return Fraction(D, 2)
    max_den = min(MAX_ADAPTIVE_CENTER_DENOMINATOR, max(1, D * interval_count * 16))
    return _clamp_fraction(
        Fraction.from_float(hint).limit_denominator(max_den),
        Fraction(0, 1),
        Fraction(D, 1),
    )


def _centered_power_interval_bounds(
    D: int,
    center: Fraction,
    interval_count: int,
    power: int,
) -> list[tuple[Fraction, Fraction]]:
    if D == 0:
        return [(Fraction(0, 1), Fraction(0, 1))]
    if interval_count <= 1:
        return _uniform_interval_bounds(D, interval_count)
    if power < 2:
        raise ValueError("power must be at least 2")

    end = Fraction(D, 1)
    center = _clamp_fraction(center, Fraction(0, 1), end)
    if center == 0:
        left_count = 0
        right_count = interval_count
    elif center == end:
        left_count = interval_count
        right_count = 0
    else:
        left_count = round(interval_count * float(center) / float(end))
        left_count = min(interval_count - 1, max(1, left_count))
        right_count = interval_count - left_count

    points: list[Fraction] = []
    if left_count:
        for i in range(left_count + 1):
            u = Fraction(left_count - i, left_count)
            points.append(center - center * (u ** power))
    else:
        points.append(Fraction(0, 1))

    if right_count:
        start = 1 if points[-1] == center else 0
        for i in range(start, right_count + 1):
            u = Fraction(i, right_count)
            points.append(center + (end - center) * (u ** power))

    return list(zip(points, points[1:]))


def _focused_interval_bounds(
    D: int,
    center: Fraction,
    interval_count: int,
    radius_denominator: int,
) -> list[tuple[Fraction, Fraction]]:
    if D == 0:
        return [(Fraction(0, 1), Fraction(0, 1))]
    if interval_count < 3:
        return _uniform_interval_bounds(D, interval_count)
    if radius_denominator <= 0:
        raise ValueError("radius denominator must be positive")

    end = Fraction(D, 1)
    center = _clamp_fraction(center, Fraction(0, 1), end)
    radius = Fraction(D, radius_denominator)
    focus_lo = _clamp_fraction(center - radius, Fraction(0, 1), end)
    focus_hi = _clamp_fraction(center + radius, Fraction(0, 1), end)

    segments: list[tuple[Fraction, Fraction, bool]] = []
    if focus_lo > 0:
        segments.append((Fraction(0, 1), focus_lo, False))
    if focus_hi > focus_lo:
        segments.append((focus_lo, focus_hi, True))
    if focus_hi < end:
        segments.append((focus_hi, end, False))

    counts = {idx: 1 for idx in range(len(segments))}
    remaining = interval_count - len(segments)
    focus_indexes = [idx for idx, (_, _, is_focus) in enumerate(segments) if is_focus]
    if focus_indexes and remaining > 0:
        target_focus = max(1, (3 * interval_count) // 4)
        focus_idx = focus_indexes[0]
        added = min(remaining, max(0, target_focus - counts[focus_idx]))
        counts[focus_idx] += added
        remaining -= added

    while remaining > 0:
        best_idx = max(
            range(len(segments)),
            key=lambda idx: float((segments[idx][1] - segments[idx][0]) / (counts[idx] + 1)),
        )
        counts[best_idx] += 1
        remaining -= 1

    points: list[Fraction] = []
    for idx, (lo, hi, _) in enumerate(segments):
        if not points:
            points.append(lo)
        count = counts[idx]
        for j in range(1, count + 1):
            points.append(lo + (hi - lo) * Fraction(j, count))

    return list(zip(points, points[1:]))


def _interval_floor_for_bounds(
    p0: Pool,
    p1: Pool,
    D: int,
    bounds: list[tuple[Fraction, Fraction]],
) -> Fraction:
    return min(
        split_interval_curvature_lower_bound_fraction(p0, p1, D, lo, hi)
        for lo, hi in bounds
    )


def _candidate_interval_bounds(
    p0: Pool,
    p1: Pool,
    D: int,
    interval_count: int,
) -> list[list[tuple[Fraction, Fraction]]]:
    center = _curvature_hint_fraction(p0, p1, D, interval_count)
    candidates = [_uniform_interval_bounds(D, interval_count)]
    candidates.extend(
        _centered_power_interval_bounds(D, center, interval_count, power)
        for power in (2, 3, 4)
    )
    candidates.extend(
        _focused_interval_bounds(D, center, interval_count, radius_denominator)
        for radius_denominator in (4, 8)
    )
    return candidates


def _refine_weakest_interval_bounds(
    p0: Pool,
    p1: Pool,
    D: int,
    bounds: list[tuple[Fraction, Fraction]],
    target_interval_count: int,
) -> list[tuple[Fraction, Fraction]]:
    out = list(bounds)
    while len(out) < target_interval_count:
        weakest_idx = min(
            range(len(out)),
            key=lambda idx: (
                split_interval_curvature_lower_bound_fraction(p0, p1, D, out[idx][0], out[idx][1]),
                out[idx][0],
                out[idx][1],
            ),
        )
        lo, hi = out[weakest_idx]
        if lo == hi:
            break
        mid = (lo + hi) / 2
        out[weakest_idx:weakest_idx + 1] = [(lo, mid), (mid, hi)]
    return out


def _optimal_midpoint_refinement_bounds(
    p0: Pool,
    p1: Pool,
    D: int,
    base_interval_count: int,
    target_interval_count: int,
) -> list[tuple[Fraction, Fraction]]:
    base_bounds = tuple(_uniform_interval_bounds(D, base_interval_count))
    extra_budget = target_interval_count - base_interval_count
    cache: dict[tuple[Fraction, Fraction, int], tuple[Fraction, tuple[tuple[Fraction, Fraction], ...]]] = {}

    def best_interval(
        lo: Fraction,
        hi: Fraction,
        leaf_count: int,
    ) -> tuple[Fraction, tuple[tuple[Fraction, Fraction], ...]]:
        key = (lo, hi, leaf_count)
        if key in cache:
            return cache[key]
        if leaf_count == 1 or lo == hi:
            out = (split_interval_curvature_lower_bound_fraction(p0, p1, D, lo, hi), ((lo, hi),))
            cache[key] = out
            return out

        mid = (lo + hi) / 2
        best_floor: Fraction | None = None
        best_state: tuple[tuple[Fraction, Fraction], ...] | None = None
        for left_count in range(1, leaf_count):
            right_count = leaf_count - left_count
            left_floor, left_state = best_interval(lo, mid, left_count)
            right_floor, right_state = best_interval(mid, hi, right_count)
            candidate_floor = min(left_floor, right_floor)
            candidate_state = left_state + right_state
            if (
                best_floor is None
                or candidate_floor > best_floor
                or (candidate_floor == best_floor and candidate_state < best_state)
            ):
                best_floor = candidate_floor
                best_state = candidate_state

        assert best_floor is not None
        assert best_state is not None
        out = (best_floor, best_state)
        cache[key] = out
        return out

    per_base: list[list[tuple[Fraction, tuple[tuple[Fraction, Fraction], ...]]]] = []
    for lo, hi in base_bounds:
        per_base.append([
            best_interval(lo, hi, leaf_count)
            for leaf_count in range(1, extra_budget + 2)
        ])

    best_global_floor: Fraction | None = None
    best_global_state: tuple[tuple[Fraction, Fraction], ...] | None = None

    def allocate(
        idx: int,
        remaining_extra: int,
        states: list[tuple[tuple[Fraction, Fraction], ...]],
        floors: list[Fraction],
    ) -> None:
        nonlocal best_global_floor, best_global_state
        if idx == len(base_bounds):
            if remaining_extra != 0:
                return
            candidate_floor = min(floors)
            candidate_state = tuple(interval for state in states for interval in state)
            if (
                best_global_floor is None
                or candidate_floor > best_global_floor
                or (candidate_floor == best_global_floor and candidate_state < best_global_state)
            ):
                best_global_floor = candidate_floor
                best_global_state = candidate_state
            return

        for extra_for_interval in range(remaining_extra + 1):
            floor, state = per_base[idx][extra_for_interval]
            allocate(
                idx + 1,
                remaining_extra - extra_for_interval,
                states + [state],
                floors + [floor],
            )

    allocate(0, extra_budget, [], [])
    assert best_global_state is not None
    return list(best_global_state)


def _field_float(obj: Mapping[str, object], key: str) -> float | None:
    value = obj.get(key)
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return None
    out = float(value)
    if not math.isfinite(out):
        return None
    return out


def _close(a: float, b: float, rel: float = POOL_M_CERT_TOL) -> bool:
    return abs(a - b) <= rel * max(1.0, abs(a), abs(b))


def build_pool_parameter_m_certificate(p0: Pool, p1: Pool, D: int) -> bytes:
    if not (_pool_domain_valid(p0) and _pool_domain_valid(p1) and D >= 0):
        raise ValueError("invalid pool-parameter m certificate domain")
    endpoint_bound = split_endpoint_curvature_lower_bound(p0, p1, D)
    if endpoint_bound <= 0.0 or not math.isfinite(endpoint_bound):
        raise ValueError("endpoint curvature bound must be positive and finite")
    payload: dict[str, object] = {
        "schema": POOL_M_CERTIFICATE_SCHEMA,
        "authority_effects": False,
        "domain": _pool_domain_payload(p0, p1, D),
        "domain_hash": pool_parameter_m_domain_hash(p0, p1, D),
        "endpoint_bound": endpoint_bound,
        "m": endpoint_bound,
    }
    raw = _canonical_json_bytes(payload)
    if len(raw) > MAX_POOL_INTERVAL_M_CERTIFICATE_BYTES:
        raise ValueError("interval curvature certificate too large")
    return raw


def build_exact_curvature_m_certificate(p0: Pool, p1: Pool, D: int) -> bytes:
    if not _exact_curvature_float_domain_valid(p0, p1, D):
        raise ValueError("invalid exact curvature m certificate domain")
    endpoint_bound = split_endpoint_curvature_lower_bound(p0, p1, D)
    exact_bound = split_exact_curvature_lower_bound(p0, p1, D)
    minimizer_a = split_exact_curvature_minimizer(p0, p1, D)
    if endpoint_bound <= 0.0 or not math.isfinite(endpoint_bound):
        raise ValueError("endpoint curvature bound must be positive and finite")
    if exact_bound <= 0.0 or not math.isfinite(exact_bound):
        raise ValueError("exact curvature bound must be positive and finite")
    if minimizer_a < 0.0 or minimizer_a > float(D) or not math.isfinite(minimizer_a):
        raise ValueError("exact curvature minimizer must be in [0,D]")
    payload: dict[str, object] = {
        "schema": POOL_EXACT_M_CERTIFICATE_SCHEMA,
        "authority_effects": False,
        "domain": _pool_domain_payload(p0, p1, D),
        "domain_hash": pool_parameter_m_domain_hash(p0, p1, D),
        "endpoint_bound": endpoint_bound,
        "exact_bound": exact_bound,
        "minimizer_a": minimizer_a,
        "m": exact_bound,
    }
    return _canonical_json_bytes(payload)


def build_stationary_curvature_m_certificate(
    p0: Pool,
    p1: Pool,
    D: int,
    minimizer_a: Fraction,
) -> bytes:
    if not (_pool_domain_valid(p0) and _pool_domain_valid(p1) and D >= 0):
        raise ValueError("invalid stationary curvature m certificate domain")
    if minimizer_a < 0 or minimizer_a > Fraction(D, 1):
        raise ValueError("stationary minimizer must be in [0,D]")

    values = _split_stationary_certificate_values(p0, p1, D, minimizer_a)
    if values["endpoint_bound"] <= 0 or values["m"] <= 0:
        raise ValueError("stationary curvature bounds must be positive")
    if values["stationarity_lhs"] != values["stationarity_rhs"]:
        raise ValueError("stationary curvature witness does not satisfy derivative equality")

    payload: dict[str, object] = {
        "schema": POOL_STATIONARY_M_CERTIFICATE_SCHEMA,
        "authority_effects": False,
        "domain": _pool_domain_payload(p0, p1, D),
        "domain_hash": pool_parameter_m_domain_hash(p0, p1, D),
        "endpoint_bound": _fraction_payload(values["endpoint_bound"]),
        "minimizer_a": _fraction_payload(minimizer_a),
        "stationarity_lhs": _fraction_payload(values["stationarity_lhs"]),
        "stationarity_rhs": _fraction_payload(values["stationarity_rhs"]),
        "q": _fraction_payload(values["q"]),
        "scale": _fraction_payload(values["scale"]),
        "m": _fraction_payload(values["m"]),
    }
    raw = _canonical_json_bytes(payload)
    if len(raw) > MAX_POOL_INTERVAL_M_CERTIFICATE_BYTES:
        raise ValueError("stationary curvature certificate too large")
    return raw


def _build_interval_curvature_m_certificate_from_bounds(
    p0: Pool,
    p1: Pool,
    D: int,
    bounds: list[tuple[Fraction, Fraction]],
) -> bytes:
    intervals: list[dict[str, object]] = []
    lower_bounds: list[Fraction] = []
    for lo, hi in bounds:
        lower_bound = split_interval_curvature_lower_bound_fraction(p0, p1, D, lo, hi)
        intervals.append({
            "lo": _fraction_payload(lo),
            "hi": _fraction_payload(hi),
            "lower_bound": _fraction_payload(lower_bound),
        })
        lower_bounds.append(lower_bound)

    m_floor = min(lower_bounds)
    endpoint_bound = split_endpoint_curvature_lower_bound_fraction(p0, p1, D)
    if endpoint_bound <= 0 or m_floor <= 0:
        raise ValueError("interval curvature bounds must be positive")
    payload: dict[str, object] = {
        "schema": POOL_INTERVAL_M_CERTIFICATE_SCHEMA,
        "authority_effects": False,
        "domain": _pool_domain_payload(p0, p1, D),
        "domain_hash": pool_parameter_m_domain_hash(p0, p1, D),
        "endpoint_bound": _fraction_payload(endpoint_bound),
        "interval_count": len(bounds),
        "intervals": intervals,
        "m": _fraction_payload(m_floor),
    }
    return _canonical_json_bytes(payload)


def build_interval_curvature_m_certificate(
    p0: Pool,
    p1: Pool,
    D: int,
    interval_count: int = 64,
) -> bytes:
    if not (_pool_domain_valid(p0) and _pool_domain_valid(p1) and D >= 0):
        raise ValueError("invalid interval curvature m certificate domain")
    if isinstance(interval_count, bool) or not isinstance(interval_count, int):
        raise ValueError("interval_count must be an integer")
    if D == 0:
        interval_count = 1
    if interval_count <= 0 or interval_count > MAX_INTERVAL_M_CERTIFICATE_INTERVALS:
        raise ValueError("interval_count out of bounds")
    return _build_interval_curvature_m_certificate_from_bounds(
        p0,
        p1,
        D,
        _uniform_interval_bounds(D, interval_count),
    )


def build_best_interval_curvature_m_certificate(
    p0: Pool,
    p1: Pool,
    D: int,
    interval_count: int = 64,
) -> bytes:
    if not (_pool_domain_valid(p0) and _pool_domain_valid(p1) and D >= 0):
        raise ValueError("invalid best-cover interval curvature m certificate domain")
    if isinstance(interval_count, bool) or not isinstance(interval_count, int):
        raise ValueError("interval_count must be an integer")
    if D == 0:
        interval_count = 1
    if interval_count <= 0 or interval_count > MAX_INTERVAL_M_CERTIFICATE_INTERVALS:
        raise ValueError("interval_count out of bounds")

    candidates = _candidate_interval_bounds(p0, p1, D, interval_count)
    best_bounds = max(
        candidates,
        key=lambda bounds: _interval_floor_for_bounds(p0, p1, D, bounds),
    )
    return _build_interval_curvature_m_certificate_from_bounds(p0, p1, D, best_bounds)


def build_refined_interval_curvature_m_certificate(
    p0: Pool,
    p1: Pool,
    D: int,
    base_interval_count: int = 16,
    target_interval_count: int = 64,
) -> bytes:
    if not (_pool_domain_valid(p0) and _pool_domain_valid(p1) and D >= 0):
        raise ValueError("invalid refined interval curvature m certificate domain")
    if (
        isinstance(base_interval_count, bool)
        or isinstance(target_interval_count, bool)
        or not isinstance(base_interval_count, int)
        or not isinstance(target_interval_count, int)
    ):
        raise ValueError("interval counts must be integers")
    if D == 0:
        base_interval_count = 1
        target_interval_count = 1
    if (
        base_interval_count <= 0
        or target_interval_count <= 0
        or base_interval_count > target_interval_count
        or target_interval_count > MAX_INTERVAL_M_CERTIFICATE_INTERVALS
    ):
        raise ValueError("interval counts out of bounds")

    base_bounds = _uniform_interval_bounds(D, base_interval_count)
    refined_bounds = _refine_weakest_interval_bounds(
        p0,
        p1,
        D,
        base_bounds,
        target_interval_count,
    )
    return _build_interval_curvature_m_certificate_from_bounds(p0, p1, D, refined_bounds)


def build_optimal_midpoint_interval_curvature_m_certificate(
    p0: Pool,
    p1: Pool,
    D: int,
    base_interval_count: int = 4,
    target_interval_count: int = 10,
) -> bytes:
    if not (_pool_domain_valid(p0) and _pool_domain_valid(p1) and D >= 0):
        raise ValueError("invalid optimal-midpoint interval curvature m certificate domain")
    if (
        isinstance(base_interval_count, bool)
        or isinstance(target_interval_count, bool)
        or not isinstance(base_interval_count, int)
        or not isinstance(target_interval_count, int)
    ):
        raise ValueError("interval counts must be integers")
    if D == 0:
        base_interval_count = 1
        target_interval_count = 1
    if (
        base_interval_count <= 0
        or target_interval_count <= 0
        or base_interval_count > target_interval_count
        or target_interval_count > MAX_OPTIMAL_MIDPOINT_INTERVALS
    ):
        raise ValueError("optimal midpoint interval counts out of bounds")

    optimal_bounds = _optimal_midpoint_refinement_bounds(
        p0,
        p1,
        D,
        base_interval_count,
        target_interval_count,
    )
    return _build_interval_curvature_m_certificate_from_bounds(p0, p1, D, optimal_bounds)


def verify_pool_parameter_m_certificate_bytes(
    p0: Pool,
    p1: Pool,
    D: int,
    raw: bytes,
) -> PoolMCheckResult:
    if len(raw) > MAX_POOL_M_CERTIFICATE_BYTES:
        return PoolMCheckResult(False, PoolMReject.CERTIFICATE_TOO_LARGE)
    if not (_pool_domain_valid(p0) and _pool_domain_valid(p1) and D >= 0):
        return PoolMCheckResult(False, PoolMReject.BAD_DOMAIN)
    try:
        decoded = json.loads(raw.decode("utf-8"), object_pairs_hook=_reject_duplicate_keys)
    except DuplicateKey:
        return PoolMCheckResult(False, PoolMReject.DUPLICATE_KEY)
    except (UnicodeDecodeError, json.JSONDecodeError):
        return PoolMCheckResult(False, PoolMReject.BAD_JSON)
    if not isinstance(decoded, dict):
        return PoolMCheckResult(False, PoolMReject.BAD_JSON)
    if _canonical_json_bytes(decoded) != raw:
        return PoolMCheckResult(False, PoolMReject.NONCANONICAL_BYTES)
    if decoded.get("schema") != POOL_M_CERTIFICATE_SCHEMA:
        return PoolMCheckResult(False, PoolMReject.BAD_SCHEMA)
    if decoded.get("authority_effects") is not False:
        return PoolMCheckResult(False, PoolMReject.AUTHORITY_EFFECTS_PRESENT)

    expected_domain = _pool_domain_payload(p0, p1, D)
    if decoded.get("domain") != expected_domain:
        return PoolMCheckResult(False, PoolMReject.DOMAIN_HASH_MISMATCH)
    expected_hash = pool_parameter_m_domain_hash(p0, p1, D)
    if decoded.get("domain_hash") != expected_hash:
        return PoolMCheckResult(False, PoolMReject.DOMAIN_HASH_MISMATCH)

    endpoint_bound = _field_float(decoded, "endpoint_bound")
    m = _field_float(decoded, "m")
    if endpoint_bound is None or m is None:
        return PoolMCheckResult(False, PoolMReject.BAD_NUMERIC_FIELD)
    recomputed = split_endpoint_curvature_lower_bound(p0, p1, D)
    if not _close(endpoint_bound, recomputed):
        return PoolMCheckResult(False, PoolMReject.STALE_ENDPOINT_BOUND)
    if m <= 0.0 or not _close(m, recomputed):
        return PoolMCheckResult(False, PoolMReject.BAD_M)
    return PoolMCheckResult(True, None, m=m, endpoint_bound=recomputed, domain_hash=expected_hash)


def verify_exact_curvature_m_certificate_bytes(
    p0: Pool,
    p1: Pool,
    D: int,
    raw: bytes,
) -> PoolMCheckResult:
    if len(raw) > MAX_POOL_M_CERTIFICATE_BYTES:
        return PoolMCheckResult(False, PoolMReject.CERTIFICATE_TOO_LARGE)
    if not _exact_curvature_float_domain_valid(p0, p1, D):
        return PoolMCheckResult(False, PoolMReject.BAD_DOMAIN)
    try:
        decoded = json.loads(raw.decode("utf-8"), object_pairs_hook=_reject_duplicate_keys)
    except DuplicateKey:
        return PoolMCheckResult(False, PoolMReject.DUPLICATE_KEY)
    except (UnicodeDecodeError, json.JSONDecodeError):
        return PoolMCheckResult(False, PoolMReject.BAD_JSON)
    if not isinstance(decoded, dict):
        return PoolMCheckResult(False, PoolMReject.BAD_JSON)
    if _canonical_json_bytes(decoded) != raw:
        return PoolMCheckResult(False, PoolMReject.NONCANONICAL_BYTES)
    if decoded.get("schema") != POOL_EXACT_M_CERTIFICATE_SCHEMA:
        return PoolMCheckResult(False, PoolMReject.BAD_SCHEMA)
    if decoded.get("authority_effects") is not False:
        return PoolMCheckResult(False, PoolMReject.AUTHORITY_EFFECTS_PRESENT)

    expected_domain = _pool_domain_payload(p0, p1, D)
    if decoded.get("domain") != expected_domain:
        return PoolMCheckResult(False, PoolMReject.DOMAIN_HASH_MISMATCH)
    expected_hash = pool_parameter_m_domain_hash(p0, p1, D)
    if decoded.get("domain_hash") != expected_hash:
        return PoolMCheckResult(False, PoolMReject.DOMAIN_HASH_MISMATCH)

    endpoint_bound = _field_float(decoded, "endpoint_bound")
    exact_bound = _field_float(decoded, "exact_bound")
    minimizer_a = _field_float(decoded, "minimizer_a")
    m = _field_float(decoded, "m")
    if endpoint_bound is None or exact_bound is None or minimizer_a is None or m is None:
        return PoolMCheckResult(False, PoolMReject.BAD_NUMERIC_FIELD)

    recomputed_endpoint = split_endpoint_curvature_lower_bound(p0, p1, D)
    recomputed_exact = split_exact_curvature_lower_bound(p0, p1, D)
    recomputed_minimizer = split_exact_curvature_minimizer(p0, p1, D)
    if not _close(endpoint_bound, recomputed_endpoint):
        return PoolMCheckResult(False, PoolMReject.STALE_ENDPOINT_BOUND)
    if not _close(exact_bound, recomputed_exact):
        return PoolMCheckResult(False, PoolMReject.STALE_EXACT_BOUND)
    if not _close(minimizer_a, recomputed_minimizer):
        return PoolMCheckResult(False, PoolMReject.STALE_MINIMIZER)
    if exact_bound < endpoint_bound * (1.0 - 1e-10):
        return PoolMCheckResult(False, PoolMReject.STALE_EXACT_BOUND)
    if m <= 0.0 or not _close(m, recomputed_exact):
        return PoolMCheckResult(False, PoolMReject.BAD_M)
    return PoolMCheckResult(
        True,
        None,
        m=m,
        endpoint_bound=recomputed_endpoint,
        exact_bound=recomputed_exact,
        minimizer_a=recomputed_minimizer,
        domain_hash=expected_hash,
    )


def verify_stationary_curvature_m_certificate_bytes(
    p0: Pool,
    p1: Pool,
    D: int,
    raw: bytes,
) -> PoolMCheckResult:
    if len(raw) > MAX_POOL_INTERVAL_M_CERTIFICATE_BYTES:
        return PoolMCheckResult(False, PoolMReject.CERTIFICATE_TOO_LARGE)
    if not (_pool_domain_valid(p0) and _pool_domain_valid(p1) and D >= 0):
        return PoolMCheckResult(False, PoolMReject.BAD_DOMAIN)
    try:
        decoded = json.loads(raw.decode("utf-8"), object_pairs_hook=_reject_duplicate_keys)
    except DuplicateKey:
        return PoolMCheckResult(False, PoolMReject.DUPLICATE_KEY)
    except (UnicodeDecodeError, json.JSONDecodeError):
        return PoolMCheckResult(False, PoolMReject.BAD_JSON)
    if not isinstance(decoded, dict):
        return PoolMCheckResult(False, PoolMReject.BAD_JSON)
    if _canonical_json_bytes(decoded) != raw:
        return PoolMCheckResult(False, PoolMReject.NONCANONICAL_BYTES)
    if set(decoded.keys()) != POOL_STATIONARY_CERTIFICATE_KEYS:
        return PoolMCheckResult(False, PoolMReject.BAD_SCHEMA)
    if decoded.get("schema") != POOL_STATIONARY_M_CERTIFICATE_SCHEMA:
        return PoolMCheckResult(False, PoolMReject.BAD_SCHEMA)
    if decoded.get("authority_effects") is not False:
        return PoolMCheckResult(False, PoolMReject.AUTHORITY_EFFECTS_PRESENT)

    expected_domain = _pool_domain_payload(p0, p1, D)
    if decoded.get("domain") != expected_domain:
        return PoolMCheckResult(False, PoolMReject.DOMAIN_HASH_MISMATCH)
    expected_hash = pool_parameter_m_domain_hash(p0, p1, D)
    if decoded.get("domain_hash") != expected_hash:
        return PoolMCheckResult(False, PoolMReject.DOMAIN_HASH_MISMATCH)

    minimizer_a = _field_fraction(decoded, "minimizer_a")
    if minimizer_a is None:
        return PoolMCheckResult(False, PoolMReject.BAD_RATIONAL_FIELD)
    if minimizer_a < 0 or minimizer_a > Fraction(D, 1):
        return PoolMCheckResult(False, PoolMReject.STALE_MINIMIZER)

    values = _split_stationary_certificate_values(p0, p1, D, minimizer_a)
    if values["stationarity_lhs"] != values["stationarity_rhs"]:
        return PoolMCheckResult(False, PoolMReject.STALE_STATIONARITY)

    endpoint_bound = _field_fraction(decoded, "endpoint_bound")
    stationarity_lhs = _field_fraction(decoded, "stationarity_lhs")
    stationarity_rhs = _field_fraction(decoded, "stationarity_rhs")
    q = _field_fraction(decoded, "q")
    scale = _field_fraction(decoded, "scale")
    m = _field_fraction(decoded, "m")
    if None in {endpoint_bound, stationarity_lhs, stationarity_rhs, q, scale, m}:
        return PoolMCheckResult(False, PoolMReject.BAD_RATIONAL_FIELD)

    if endpoint_bound != values["endpoint_bound"]:
        return PoolMCheckResult(False, PoolMReject.STALE_ENDPOINT_BOUND)
    if (
        stationarity_lhs != values["stationarity_lhs"]
        or stationarity_rhs != values["stationarity_rhs"]
        or q != values["q"]
        or scale != values["scale"]
    ):
        return PoolMCheckResult(False, PoolMReject.STALE_STATIONARITY)
    if m is None or m <= 0 or m != values["m"]:
        return PoolMCheckResult(False, PoolMReject.BAD_M)
    if values["m"] < values["endpoint_bound"]:
        return PoolMCheckResult(False, PoolMReject.STALE_EXACT_BOUND)

    return PoolMCheckResult(
        True,
        None,
        m=float(values["m"]),
        endpoint_bound=float(values["endpoint_bound"]),
        exact_bound=float(values["m"]),
        minimizer_a=float(minimizer_a),
        m_fraction=values["m"],
        domain_hash=expected_hash,
    )


def verify_interval_curvature_m_certificate_bytes(
    p0: Pool,
    p1: Pool,
    D: int,
    raw: bytes,
) -> PoolMCheckResult:
    if len(raw) > MAX_POOL_INTERVAL_M_CERTIFICATE_BYTES:
        return PoolMCheckResult(False, PoolMReject.CERTIFICATE_TOO_LARGE)
    if not (_pool_domain_valid(p0) and _pool_domain_valid(p1) and D >= 0):
        return PoolMCheckResult(False, PoolMReject.BAD_DOMAIN)
    try:
        decoded = json.loads(raw.decode("utf-8"), object_pairs_hook=_reject_duplicate_keys)
    except DuplicateKey:
        return PoolMCheckResult(False, PoolMReject.DUPLICATE_KEY)
    except (UnicodeDecodeError, json.JSONDecodeError):
        return PoolMCheckResult(False, PoolMReject.BAD_JSON)
    if not isinstance(decoded, dict):
        return PoolMCheckResult(False, PoolMReject.BAD_JSON)
    if _canonical_json_bytes(decoded) != raw:
        return PoolMCheckResult(False, PoolMReject.NONCANONICAL_BYTES)
    if decoded.get("schema") != POOL_INTERVAL_M_CERTIFICATE_SCHEMA:
        return PoolMCheckResult(False, PoolMReject.BAD_SCHEMA)
    if set(decoded.keys()) != POOL_INTERVAL_CERTIFICATE_KEYS:
        return PoolMCheckResult(False, PoolMReject.BAD_SCHEMA)
    if decoded.get("authority_effects") is not False:
        return PoolMCheckResult(False, PoolMReject.AUTHORITY_EFFECTS_PRESENT)

    expected_domain = _pool_domain_payload(p0, p1, D)
    if decoded.get("domain") != expected_domain:
        return PoolMCheckResult(False, PoolMReject.DOMAIN_HASH_MISMATCH)
    expected_hash = pool_parameter_m_domain_hash(p0, p1, D)
    if decoded.get("domain_hash") != expected_hash:
        return PoolMCheckResult(False, PoolMReject.DOMAIN_HASH_MISMATCH)

    endpoint_bound = _field_fraction(decoded, "endpoint_bound")
    m = _field_fraction(decoded, "m")
    if endpoint_bound is None or m is None:
        return PoolMCheckResult(False, PoolMReject.BAD_RATIONAL_FIELD)
    recomputed_endpoint = split_endpoint_curvature_lower_bound_fraction(p0, p1, D)
    if endpoint_bound != recomputed_endpoint:
        return PoolMCheckResult(False, PoolMReject.STALE_ENDPOINT_BOUND)

    interval_count = decoded.get("interval_count")
    intervals = decoded.get("intervals")
    if isinstance(interval_count, bool) or not isinstance(interval_count, int):
        return PoolMCheckResult(False, PoolMReject.BAD_INTERVALS)
    if not isinstance(intervals, list) or len(intervals) == 0:
        return PoolMCheckResult(False, PoolMReject.BAD_INTERVALS)
    if interval_count != len(intervals):
        return PoolMCheckResult(False, PoolMReject.BAD_INTERVALS)
    if interval_count > MAX_INTERVAL_M_CERTIFICATE_INTERVALS:
        return PoolMCheckResult(False, PoolMReject.TOO_MANY_INTERVALS)

    lower_bounds: list[Fraction] = []
    previous_hi = Fraction(0, 1)
    expected_end = Fraction(D, 1)
    for interval in intervals:
        if not isinstance(interval, dict):
            return PoolMCheckResult(False, PoolMReject.BAD_INTERVALS)
        if set(interval.keys()) != POOL_INTERVAL_ENTRY_KEYS:
            return PoolMCheckResult(False, PoolMReject.BAD_INTERVALS)
        lo = _field_fraction(interval, "lo")
        hi = _field_fraction(interval, "hi")
        lower_bound = _field_fraction(interval, "lower_bound")
        if lo is None or hi is None or lower_bound is None:
            return PoolMCheckResult(False, PoolMReject.BAD_RATIONAL_FIELD)
        if lo != previous_hi or lo < 0 or hi > expected_end:
            return PoolMCheckResult(False, PoolMReject.BAD_INTERVALS)
        if D == 0:
            if lo != 0 or hi != 0:
                return PoolMCheckResult(False, PoolMReject.BAD_INTERVALS)
        elif lo >= hi:
            return PoolMCheckResult(False, PoolMReject.BAD_INTERVALS)
        recomputed = split_interval_curvature_lower_bound_fraction(p0, p1, D, lo, hi)
        if lower_bound != recomputed:
            return PoolMCheckResult(False, PoolMReject.STALE_INTERVAL_BOUND)
        lower_bounds.append(recomputed)
        previous_hi = hi

    if previous_hi != expected_end:
        return PoolMCheckResult(False, PoolMReject.BAD_INTERVALS)
    m_floor = min(lower_bounds)
    if m_floor < endpoint_bound:
        return PoolMCheckResult(False, PoolMReject.STALE_INTERVAL_BOUND)
    if m <= 0 or m != m_floor:
        return PoolMCheckResult(False, PoolMReject.BAD_M)
    return PoolMCheckResult(
        True,
        None,
        m=float(m),
        endpoint_bound=float(endpoint_bound),
        m_fraction=m,
        interval_bound=float(m_floor),
        interval_count=interval_count,
        domain_hash=expected_hash,
    )


def concavity_param_at_margin(p: Pool) -> float:
    """m at x=0: m = 2*K*gamma^2*M / M^3 = 2*K*gamma^2 / M^2."""
    K = p.reserve_out
    M = p.reserve_in
    gamma = 1.0 - p.fee_bps / 10000.0
    return 2.0 * K * gamma * gamma / (M * M)


def algorithm_window(L: float, m: float, k: int = 2, epsilon: float = 2.0) -> float:
    """Window size from the argmax proximity theorem: sqrt(2*(L+epsilon)/m)."""
    if m <= 0:
        return float("inf")
    return math.sqrt(2.0 * (L + epsilon) / m)


def lipschitz_increment_value(L: float, a_A: float) -> float:
    """Value of the Lean-proven gain bound: L * a_A.

    Lean proves both:
    - Generic Lipschitz increment: f(a_A)-f(0) <= L*a_A (lipschitz_increment_bound)
    - Stateful CPMM attack gain: out_B_without_A - out_B_with_A <= L*a_A
      (cpmm_stateful_gain_bound, fee-free; cpmm_stateful_gain_bound_with_fee, with fee)

    This function returns the bound value used by both theorems.
    """
    return L * a_A


def adversarial_gain_concavity(m: float, a_A: float, a_B: float) -> float:
    """Falsified second-order approximation: (m/2)*a_A*(a_A + 2*a_B)."""
    return (m / 2.0) * a_A * (a_A + 2.0 * a_B)


def simulate_sacrifice_gain(p: Pool, a_A: float, a_B: float) -> float:
    """Simulate actual sacrifice attack gain.

    Gain = f(a_B) - f(a_A + a_B) where f is the CPMM output.
    (A doesn't fill, so B trades against the original pool vs pool with A.)
    """
    out_B_alone = cpmm_output_cont(p, a_B)
    out_B_after_A = cpmm_output_cont(p, a_A + a_B) - cpmm_output_cont(p, a_A)
    # Actually, the gain is: B's output when A is absent vs B's output after A filled
    # When A fills: pool state changes, B trades against modified pool
    # When A sacrifices: B trades against original pool
    # Gain = f(a_B, original_pool) - f(a_B, pool_after_A)
    K = p.reserve_out
    M = p.reserve_in
    gamma = 1.0 - p.fee_bps / 10000.0
    # A fills first
    out_A = cpmm_output_cont(p, a_A)
    M_after_A = M + a_A * gamma
    K_after_A = K - out_A
    # NOTE: integer-truncated reserves here. The Lean theorems
    # (cpmm_stateful_gain_bound, cpmm_stateful_gain_bound_with_fee) prove the
    # bound for the CONTINUOUS real-valued CPMM model. This simulator truncates
    # to int, so the empirical replay is consistent with but not formally
    # identical to the Lean theorem.
    pool_after_A = Pool(int(M_after_A), int(K_after_A), p.fee_bps)
    out_B_with_A = cpmm_output_cont(pool_after_A, a_B)
    # A sacrifices (B trades against original pool)
    out_B_without_A = cpmm_output_cont(p, a_B)
    # Gain = B's extra output from A's sacrifice
    gain = out_B_without_A - out_B_with_A
    return gain


def filled_state_gain_cont(p: Pool, a_A: float, a_B: float) -> float:
    """Continuous filled-A state-change gain used by the existing Lean bound.

    A receives CPMM output, so both input and output reserves change before B.
    This is the model in `cpmm_stateful_gain_bound_tight`.
    """
    if p.fee_bps != 0:
        raise ValueError("filled_state_gain_cont is scoped to fee-free CPMM")
    if a_A <= 0.0 or a_B <= 0.0:
        return 0.0
    K = float(p.reserve_out)
    M = float(p.reserve_in)
    return (
        K * a_B / (M + a_B)
        - K * M * a_B / ((M + a_A) * (M + a_A + a_B))
    )


def donation_no_output_gain_cont(p: Pool, a_A: float, a_B: float) -> float:
    """Donation/no-output perturbation gain.

    A adds input without taking output. This is the model whose exact finite
    optimizer is `a_B = sqrt(M*(M+a_A))`.
    """
    if p.fee_bps != 0:
        raise ValueError("donation_no_output_gain_cont is scoped to fee-free CPMM")
    if a_A <= 0.0 or a_B <= 0.0:
        return 0.0
    K = float(p.reserve_out)
    M = float(p.reserve_in)
    return K * a_A * a_B / ((M + a_B) * (M + a_A + a_B))


def donation_no_output_gain_with_fee_cont(p: Pool, a_A: float, a_B: float) -> float:
    """Donation/no-output perturbation gain with fee-scaled net inputs."""
    if a_A <= 0.0 or a_B <= 0.0:
        return 0.0
    gamma = 1.0 - p.fee_bps / 10000.0
    if gamma <= 0.0:
        return 0.0
    K = float(p.reserve_out)
    M = float(p.reserve_in)
    net_A = gamma * a_A
    net_B = gamma * a_B
    return K * net_A * net_B / ((M + net_B) * (M + net_A + net_B))


def donation_optimal_attacker_size(p: Pool, a_A: float) -> float:
    """Closed-form donation/no-output optimizer: sqrt(M*(M+a_A))."""
    if p.fee_bps != 0:
        raise ValueError("donation_optimal_attacker_size is scoped to fee-free CPMM")
    if a_A <= 0.0:
        return 0.0
    M = float(p.reserve_in)
    return math.sqrt(M * (M + a_A))


def donation_optimal_attacker_size_with_fee(p: Pool, a_A: float) -> float:
    """Fee-bearing raw optimizer: sqrt(M*(M+gamma*a_A)) / gamma."""
    if a_A <= 0.0:
        return 0.0
    gamma = 1.0 - p.fee_bps / 10000.0
    if gamma <= 0.0:
        raise ValueError("fee-bearing donation optimizer requires gamma > 0")
    M = float(p.reserve_in)
    return math.sqrt(M * (M + gamma * a_A)) / gamma


def donation_optimal_gain_bound(p: Pool, a_A: float) -> float:
    """Exact donation/no-output maximum at s=sqrt(M*(M+a_A))."""
    s = donation_optimal_attacker_size(p, a_A)
    return donation_no_output_gain_cont(p, a_A, s)


def donation_optimal_gain_bound_with_fee(p: Pool, a_A: float) -> float:
    """Exact fee-bearing donation/no-output maximum at net s."""
    s_raw = donation_optimal_attacker_size_with_fee(p, a_A)
    return donation_no_output_gain_with_fee_cont(p, a_A, s_raw)


# ---------------------------------------------------------------------------
# Test 1: CPMM concavity parameter formula [Lean PROVEN, gamma=1]
# ---------------------------------------------------------------------------

def test_cpmm_concavity_param_formula() -> None:
    """m = 2*K*gamma^2/M^2 = 2*gamma*L/M at the margin (x=0).

    For f(x) = K*gamma*x/(M+gamma*x):
      f''(x) = -2*K*gamma^2*M / (M+gamma*x)^3
      m(0) = 2*K*gamma^2 / M^2

    The spot price (Lipschitz constant) is L = gamma*K/M.
    So m = 2*gamma*L/M (NOT 2*L/M; the gamma factor comes from the
    second derivative having gamma^2 while the first has gamma).

    For fee=0 (gamma=1): m = 2*K/M^2 = 2*L/M (the Lean theorem case).
    """
    rng = random.Random(20260710)
    for _ in range(200):
        K = rng.randint(100, 50000)
        M = rng.randint(100, 50000)
        fee = rng.choice([0, 30, 100, 300])
        p = Pool(M, K, fee)
        gamma = 1.0 - fee / 10000.0
        L = spot_price(p)
        m_formula = 2.0 * K * gamma * gamma / (M * M)
        # Correct relation: m = 2*gamma*L/M (gamma factor from 2nd derivative)
        m_via_L = 2.0 * gamma * L / M
        assert abs(m_formula - m_via_L) < 1e-6, (
            f"m formula mismatch: {m_formula} vs {m_via_L} "
            f"(K={K}, M={M}, fee={fee}, gamma={gamma})")
    print(f"PASS: cpmm_concavity_param_formula (200 configs, m = 2*K*gamma^2/M^2 = 2*gamma*L/M)")


# ---------------------------------------------------------------------------
# Test 2: CPMM window identity [Lean PROVEN, epsilon=0]
# ---------------------------------------------------------------------------

def test_cpmm_conservation_tradeoff() -> None:
    """window = sqrt(M) when L and m are linked via m = 2*L/M (epsilon=0).

    Lean proves sqrt(2*L/m) = sqrt(M) for the epsilon=0 case. The production
    argmax window is sqrt(2*(L+epsilon)/m), which is strictly larger.
    """
    rng = random.Random(20260711)
    for _ in range(200):
        K = rng.randint(100, 50000)
        M = rng.randint(100, 50000)
        L = K / M  # spot price (no fee for clean check)
        m = 2.0 * L / M  # concavity at margin
        if m <= 0:
            continue
        window_eps0 = math.sqrt(2.0 * L / m)
        expected = math.sqrt(M)
        assert abs(window_eps0 - expected) < 1e-6, (
            f"window_eps0={window_eps0} != sqrt(M)={expected} "
            f"(K={K}, M={M}, L={L}, m={m})")
    print(f"PASS: cpmm_window_identity (200 configs, sqrt(2*L/m)=sqrt(M) at eps=0)")


# ---------------------------------------------------------------------------
# Test 3: Stateful gain vs Lipschitz envelope [Lean PROVEN + empirical replay]
# ---------------------------------------------------------------------------

def test_stateful_gain_lipschitz_envelope_empirical() -> None:
    """Simulated stateful sacrifice gain stays within the Lipschitz envelope.

    Lean proves the stateful attack gain bound:
      out_B_without_A - out_B_with_A <= K*a_A/M = L*a_A
    (cpmm_stateful_gain_bound, fee-free case)
    and the fee-bearing version:
      gain <= gamma*K*a_A/M
    (cpmm_stateful_gain_bound_with_fee)

    This test empirically replays the formal theorem on a seeded corpus,
    verifying the simulator matches the bound. The bound is now Lean-proven,
    not just empirical.
    """
    rng = random.Random(20260712)
    max_violation = 0.0
    worst: tuple = ()
    for _ in range(500):
        M = rng.randint(1000, 50000)
        K = rng.randint(1000, 50000)
        fee = rng.choice([0, 30, 100])
        p = Pool(M, K, fee)
        L = spot_price(p)
        a_A = rng.uniform(10, min(1000, M / 10))
        a_B = rng.uniform(100, min(5000, M / 2))
        gain = simulate_sacrifice_gain(p, a_A, a_B)
        bound = lipschitz_increment_value(L, a_A)
        if gain > bound + 1e-6:
            v = gain - bound
            max_violation = max(max_violation, v)
            worst = (M, K, fee, a_A, a_B, gain, bound)
    assert max_violation <= 1e-6, (
        f"STATEFUL GAIN EXCEEDED LIPSCHITZ BOUND [Lean PROVEN]: {max_violation}. Worst: {worst}")
    print(f"PASS: stateful_gain_lipschitz_envelope_empirical "
          f"(500 configs, stateful gain <= L*a_A [Lean PROVEN + empirical replay])")


# ---------------------------------------------------------------------------
# Test 4: Concavity bound falsification [Empirical, regression guard]
# ---------------------------------------------------------------------------

def test_concavity_bound_falsified_small_trades() -> None:
    """Concavity gain bound is an APPROXIMATION, not a universal bound.

    FALSIFICATION: The bound gain <= (m/2)*a_A*(a_A+2*a_B) derived from a
    second-order Taylor expansion of f(input) does NOT universally hold,
    even in the small-trade regime. The actual gain involves a pool STATE
    change (M -> M+a_A*gamma), not just an input change, so the Taylor
    expansion in input space is the wrong model.

    The generic Lipschitz increment f(a_A)-f(0) <= L*a_A is Lean-proven,
    and the stateful CPMM attack gain bound is also Lean-proven
    (cpmm_stateful_gain_bound). The falsified concavity bound (m/2)*a_A*(a_A+2*a_B)
    is a DIFFERENT, weaker formula that does not hold universally.
    """
    rng = random.Random(20260713)
    max_ratio = 0.0
    fail_count = 0
    total = 0
    for _ in range(500):
        M = rng.randint(1000, 50000)
        K = rng.randint(1000, 50000)
        fee = rng.choice([0, 30, 100])
        p = Pool(M, K, fee)
        max_trade = M / 10
        a_A = rng.uniform(1, max_trade / 3)
        a_B = rng.uniform(1, max_trade * 2 / 3)
        x_max = a_A + a_B
        m = strong_concavity_param(p, x_max)
        gain = simulate_sacrifice_gain(p, a_A, a_B)
        bound = adversarial_gain_concavity(m, a_A, a_B)
        if bound > 0:
            ratio = gain / bound
            total += 1
            if ratio > 1.0:
                fail_count += 1
            if ratio > max_ratio:
                max_ratio = ratio
    # HARD ASSERT: falsification must actually occur (regression guard)
    assert fail_count > 0, (
        "FALSIFICATION REGRESSION: no configs exceeded concavity bound; "
        "either the bound started holding or the test regime changed")
    assert max_ratio > 1.0, (
        "FALSIFICATION REGRESSION: max_ratio <= 1.0; concavity bound holds")
    print(f"PASS: concavity_bound_falsified_small_trades "
          f"(FALSIFICATION: {fail_count}/{total} configs exceed concavity bound, "
          f"max_ratio={max_ratio:.4f})")


def test_concavity_bound_fails_large_trades() -> None:
    """Document that the concavity bound FAILS for large trades.

    This is a FALSIFICATION: the concavity bound (m/2)*a_A*(a_A+2*a_B) is
    NOT a universal upper bound. For large trades (a_B ~ M/2), the actual
    gain exceeds the concavity bound by up to 2x.
    """
    rng = random.Random(20260714)
    max_ratio = 0.0
    worst: tuple = ()
    fail_count = 0
    total = 0
    for _ in range(500):
        M = rng.randint(1000, 5000)
        K = rng.randint(1000, 50000)
        fee = rng.choice([0, 30, 100])
        p = Pool(M, K, fee)
        # Large-trade regime: a_B up to M/2
        a_A = rng.uniform(10, min(100, M / 10))
        a_B = rng.uniform(100, M / 2)
        x_max = a_A + a_B
        m = strong_concavity_param(p, x_max)
        gain = simulate_sacrifice_gain(p, a_A, a_B)
        bound = adversarial_gain_concavity(m, a_A, a_B)
        if bound > 0:
            ratio = gain / bound
            total += 1
            if ratio > 1.0:
                fail_count += 1
            if ratio > max_ratio:
                max_ratio = ratio
                worst = (M, K, fee, a_A, a_B, gain, bound, ratio)
    # HARD ASSERT: falsification must actually occur (regression guard)
    assert fail_count > 0, (
        "FALSIFICATION REGRESSION: no large-trade configs exceeded concavity bound")
    assert max_ratio > 1.0, (
        "FALSIFICATION REGRESSION: max_ratio <= 1.0 for large trades")
    print(f"PASS: concavity_bound_fails_large_trades "
          f"({fail_count}/{total} large-trade configs EXCEED concavity bound, "
          f"max_ratio={max_ratio:.4f})")
    # Empirically replay the Lean-proven stateful gain bound for the worst case
    # (cpmm_stateful_gain_bound: gain <= L*a_A, Lean PROVEN)
    if worst:
        M_w, K_w, fee_w, a_A_w, a_B_w, _, _, _ = worst
        p_w = Pool(M_w, K_w, fee_w)
        L_w = spot_price(p_w)
        lip_bound = lipschitz_increment_value(L_w, a_A_w)
        actual_w = simulate_sacrifice_gain(p_w, a_A_w, a_B_w)
        assert actual_w <= lip_bound + 1e-6, (
            f"Stateful gain exceeded Lipschitz envelope: actual={actual_w} > L*a_A={lip_bound}")



# ---------------------------------------------------------------------------
# Test 5: Actual stateful gain decreases with M [Empirical]
# ---------------------------------------------------------------------------

def test_actual_gain_decreases_with_depth() -> None:
    """ACTUAL adversarial gain decreases as pool depth M increases.

    NOTE: This uses the ACTUAL simulated gain, not a bound. The Lipschitz
    bound L*a_A is constant (for balanced pools where L=K/M=1), so the
    Lipschitz product window*L*a_A = sqrt(M)*a_A is INCREASING in M.
    The actual gain DECREASES with M because the pool's curvature
    decreases, making the stateful gain smaller. This is an EMPIRICAL
    observation, not a formalized theorem.

    The concavity-based bound using MINIMUM curvature m, (m/2)*a_A*a_B, also
    decreases with M, but it is FALSIFIED as a stateful attack bound (ratio up
    to 1.88x). The empirical scaling probe in concavity_bounded_adversarial_test.py
    uses |f''(0)| (MAXIMUM curvature at the margin), which is a more
    conservative upper-bound constant than m since |f''(0)| >= m. That probe
    is empirical only, not a Lean theorem.
    The actual gain is the honest quantity to track.
    """
    a_A, a_B = 100.0, 2000.0
    gains_by_depth: dict[int, float] = {}
    for M in [1000, 5000, 10000, 50000, 100000]:
        K = M  # balanced pool (L = 1)
        p = Pool(M, K, 0)
        gain = simulate_sacrifice_gain(p, a_A, a_B)
        gains_by_depth[M] = gain
    # Actual gain should decrease with M (deeper = more secure)
    depths = sorted(gains_by_depth.keys())
    for i in range(len(depths) - 1):
        assert gains_by_depth[depths[i]] > gains_by_depth[depths[i + 1]], (
            f"Actual gain not decreasing: M={depths[i]} "
            f"gain={gains_by_depth[depths[i]]} vs M={depths[i+1]} "
            f"gain={gains_by_depth[depths[i+1]]}")
    print(f"PASS: actual_gain_decreases_with_depth "
          f"(gains={{{', '.join(f'M={m}:{g:.2f}' for m, g in gains_by_depth.items())}}})")


# ---------------------------------------------------------------------------
# Test 6: Min_out cap breaks the tradeoff [Empirical]
# ---------------------------------------------------------------------------

def test_min_out_cap_breaks_tradeoff() -> None:
    """Min_out cap at 90% makes sacrifice INFEASIBLE, so gain = 0.

    The cap mechanism: A's min_out is limited to 90% of the EXPECTED output
    (computed at spot price, i.e. linear approximation without price impact).
    The ACTUAL output includes price impact (concavity), so actual < expected.
    For small trades, actual >= 0.9 * expected, so A always fills.

    This test is NON-TAUTOLOGICAL: expected_out_A uses the linear spot price
    (L * a_A), while actual_out_A uses the full CPMM formula with price impact.
    The gap between them is the slippage. The test verifies that the 90% cap
    is above the slippage ratio for the tested regime, so A fills.
    """
    rng = random.Random(20260714)
    cap_ratio = 0.9
    cap_gains: list[float] = []
    nocap_gains: list[float] = []
    a_fills_count = 0
    total = 0
    min_slippage_ratio = 1.0
    for _ in range(200):
        M = rng.randint(1000, 10000)
        K = rng.randint(1000, 10000)
        p = Pool(M, K, 0)
        a_A = rng.uniform(10, min(100, M / 10))
        a_B = rng.uniform(100, min(5000, M / 2))
        total += 1
        # Without cap: actual gain (A can sacrifice)
        gain_nocap = simulate_sacrifice_gain(p, a_A, a_B)
        nocap_gains.append(gain_nocap)
        # With cap: A's min_out is capped at 90% of EXPECTED output (spot price * a_A)
        L = spot_price(p)
        expected_out_A = L * a_A  # linear approximation (no price impact)
        capped_min_out = expected_out_A * cap_ratio
        actual_out_A = cpmm_output_cont(p, a_A)  # full CPMM (with price impact)
        # Slippage ratio: actual / expected (always < 1 due to concavity)
        if expected_out_A > 0:
            slippage_ratio = actual_out_A / expected_out_A
            min_slippage_ratio = min(min_slippage_ratio, slippage_ratio)
        # A fills iff actual_out >= capped_min_out
        if actual_out_A >= capped_min_out - 1e-9:
            a_fills_count += 1
            # A fills: no sacrifice, gain = 0
            cap_gains.append(0.0)
        else:
            # A doesn't fill even with cap: sacrifice still possible
            cap_gains.append(gain_nocap)
    max_cap_gain = max(cap_gains) if cap_gains else 0.0
    max_nocap_gain = max(nocap_gains) if nocap_gains else 0.0
    # With cap at 90%, A should always fill (for small trades a_A << M)
    assert a_fills_count == total, (
        f"Cap should make A always fill: {a_fills_count}/{total} filled. "
        f"Some configs allow sacrifice despite cap.")
    assert max_cap_gain == 0.0, (
        f"Cap should make gain ZERO: max_cap_gain={max_cap_gain}")
    # Verify the test is non-tautological: slippage must be real (< 1.0)
    assert min_slippage_ratio < 1.0, (
        f"Slippage ratio must be < 1.0 (non-tautological): "
        f"min_slippage_ratio={min_slippage_ratio}")
    # Verify the cap is above the worst slippage (so A fills)
    assert min_slippage_ratio >= cap_ratio, (
        f"Worst slippage {min_slippage_ratio} below cap {cap_ratio}: "
        f"some configs would not fill")
    assert max_nocap_gain > 0.0, (
        f"Without cap, some gains should be positive: max_nocap_gain={max_nocap_gain}")
    print(f"PASS: min_out_cap_breaks_tradeoff "
          f"(cap: {a_fills_count}/{total} A fills, max_gain={max_cap_gain:.2f}, "
          f"nocap: max_gain={max_nocap_gain:.2f}, "
          f"min_slippage_ratio={min_slippage_ratio:.6f})")


# ---------------------------------------------------------------------------
# Test 7: Donation/no-output exact optimizer [Lean PROVEN + empirical replay]
# ---------------------------------------------------------------------------

def test_donation_no_output_exact_optimizer() -> None:
    """Donation/no-output attack gain is maximized at sqrt(M*(M+a_A)).

    Lean proves the algebraic certificate:

      K*a_A*a_B / ((M+a_B)*(M+a_A+a_B))
        <= K*a_A*s / ((M+s)*(M+a_A+s))

    for any positive `s` with `s^2 = M*(M+a_A)`. The proof avoids calculus:
    after cross multiplication, the gap factors as `s*(a_B-s)^2`.
    """
    rng = random.Random(20260715)
    max_ratio = 0.0
    worst: tuple = ()
    for i in range(300):
        M = rng.randint(100, 100000)
        K = rng.randint(100, 100000)
        a_A = rng.uniform(1, min(5000, M / 2))
        p = Pool(M, K, 0)
        s = donation_optimal_attacker_size(p, a_A)
        opt = donation_optimal_gain_bound(p, a_A)
        assert s > 0.0
        assert opt > 0.0

        candidates = [
            1e-9,
            s * 0.01,
            s * 0.1,
            s * 0.5,
            s * 0.9,
            s,
            s * 1.1,
            s * 2.0,
            s * 10.0,
            s * 100.0,
        ]
        candidates.extend(rng.uniform(1e-9, max(s * 20.0, 1.0)) for _ in range(40))
        for a_B in candidates:
            gain = donation_no_output_gain_cont(p, a_A, a_B)
            ratio = gain / opt
            if ratio > max_ratio:
                max_ratio = ratio
                worst = (M, K, a_A, a_B, s, gain, opt, ratio)
            assert gain <= opt + 1e-8, (
                f"Donation gain exceeded exact optimizer bound: "
                f"M={M}, K={K}, a_A={a_A}, a_B={a_B}, s={s}, gain={gain}, opt={opt}")

        left = donation_no_output_gain_cont(p, a_A, s * 0.99)
        right = donation_no_output_gain_cont(p, a_A, s * 1.01)
        assert left < opt
        assert right < opt

    print("PASS: donation_no_output_exact_optimizer "
          f"(300 configs, max_ratio={max_ratio:.12f}, worst={worst})")


def test_fee_bearing_donation_no_output_exact_optimizer() -> None:
    """Fee-bearing donation optimizer is exact after net-input rescaling.

    Lean proves the algebraic certificate:

      K*(gamma*a_A)*(gamma*a_B)
        / ((M+gamma*a_B)*(M+gamma*a_A+gamma*a_B))
      <=
      K*(gamma*a_A)*s / ((M+s)*(M+gamma*a_A+s))

    for positive `s` with `s^2 = M*(M+gamma*a_A)`. The raw attacker size is
    `s/gamma`; if gamma is zero, the raw finite optimizer is undefined and the
    builder rejects that domain.
    """
    rng = random.Random(20260801)
    fee_choices = [1, 5, 30, 100, 300, 1000, 3000, 5000, 9000]
    max_ratio = 0.0
    fee_aware_differs = 0
    worst: tuple = ()
    for _ in range(300):
        M = rng.randint(100, 100000)
        K = rng.randint(100, 100000)
        fee = rng.choice(fee_choices)
        p = Pool(M, K, fee)
        gamma = 1.0 - fee / 10000.0
        a_A = rng.uniform(1, min(5000, M / 2))
        raw_s = donation_optimal_attacker_size_with_fee(p, a_A)
        net_s = gamma * raw_s
        opt = donation_optimal_gain_bound_with_fee(p, a_A)
        fee_free_s = math.sqrt(M * (M + a_A))

        assert raw_s > 0.0
        assert opt > 0.0
        assert abs(net_s * net_s - M * (M + gamma * a_A)) <= 1e-7 * max(
            1.0,
            M * (M + gamma * a_A),
        )
        if abs(raw_s - fee_free_s) > 1e-6 * max(1.0, fee_free_s):
            fee_aware_differs += 1

        candidates = [
            1e-9,
            raw_s * 0.01,
            raw_s * 0.1,
            raw_s * 0.5,
            raw_s * 0.9,
            raw_s,
            raw_s * 1.1,
            raw_s * 2.0,
            raw_s * 10.0,
            raw_s * 100.0,
            fee_free_s,
        ]
        candidates.extend(rng.uniform(1e-9, max(raw_s * 20.0, 1.0)) for _ in range(40))
        for a_B in candidates:
            gain = donation_no_output_gain_with_fee_cont(p, a_A, a_B)
            ratio = gain / opt
            if ratio > max_ratio:
                max_ratio = ratio
                worst = (M, K, fee, a_A, a_B, raw_s, gain, opt, ratio)
            assert gain <= opt + 1e-8, (
                f"Fee-bearing donation gain exceeded exact optimizer bound: "
                f"M={M}, K={K}, fee={fee}, a_A={a_A}, a_B={a_B}, "
                f"raw_s={raw_s}, gain={gain}, opt={opt}")

        left = donation_no_output_gain_with_fee_cont(p, a_A, raw_s * 0.99)
        right = donation_no_output_gain_with_fee_cont(p, a_A, raw_s * 1.01)
        assert left < opt
        assert right < opt

    try:
        donation_optimal_attacker_size_with_fee(Pool(1000, 1000, 10000), 100.0)
        raise AssertionError("full-fee donation optimizer should reject gamma=0")
    except ValueError:
        pass

    assert fee_aware_differs > 0
    print("PASS: fee_bearing_donation_no_output_exact_optimizer "
          f"(300 configs, fee_aware_differs={fee_aware_differs}, "
          f"max_ratio={max_ratio:.12f}, worst={worst})")


# ---------------------------------------------------------------------------
# Test 8: Filled-A vs donation optimizer scope split [Empirical falsification]
# ---------------------------------------------------------------------------

def test_donation_optimizer_not_filled_stateful_gain() -> None:
    """The finite donation optimizer is false for the filled-A gain semantics.

    The P5 closed form applies to donation/no-output gain. For the filled-A
    state-change gain already modeled in Lean, gain approaches
    K*a_A/(M+a_A) as a_B grows. That asymptote can exceed the donation optimum,
    so applying the finite optimizer bound to filled-A gain is a real
    overclaim. This hard falsifier prevents the two models from being merged.
    """
    p = Pool(reserve_in=1000, reserve_out=1000, fee_bps=0)
    a_A = 100.0
    s = donation_optimal_attacker_size(p, a_A)
    donation_opt = donation_optimal_gain_bound(p, a_A)
    filled_at_s = filled_state_gain_cont(p, a_A, s)
    filled_large = filled_state_gain_cont(p, a_A, 1_000_000.0)
    filled_asymptote = p.reserve_out * a_A / (p.reserve_in + a_A)

    assert filled_at_s > donation_opt, (
        f"Even at donation optimizer s, filled-A gain should exceed donation optimum: "
        f"filled_at_s={filled_at_s}, donation_opt={donation_opt}")
    assert filled_large > donation_opt * 3.0, (
        f"Large filled-A attacker trade should strongly falsify donation optimum: "
        f"filled_large={filled_large}, donation_opt={donation_opt}")
    assert abs(filled_large - filled_asymptote) / filled_asymptote < 0.01, (
        f"filled_large should approach asymptote: {filled_large} vs {filled_asymptote}")

    print("PASS: donation_optimizer_not_filled_stateful_gain "
          f"(s={s:.4f}, donation_opt={donation_opt:.4f}, "
          f"filled_at_s={filled_at_s:.4f}, filled_large={filled_large:.4f}, "
          f"filled_asymptote={filled_asymptote:.4f})")


# ---------------------------------------------------------------------------
# Test 9: Tradeoff frontier characterization [Empirical]
# ---------------------------------------------------------------------------

def test_tradeoff_frontier_characterization() -> None:
    """Characterize a fixed row-set tradeoff probe across pool depths.

    For each M, compute:
    - window_eps0: sqrt(2*L/m) = sqrt(M) [Lean PROVEN, epsilon=0]
    - window_prod: sqrt(2*(L+epsilon)/m) [production, epsilon=2, NOT Lean]
    - lipschitz_increment: L*a_A [Lean PROVEN for both generic increment AND stateful gain]
    - actual gain: stateful simulator [empirical, decreases with M in this row set]
    - lip_product: window * L * a_A [INCREASING in M, NOT a frontier]

    The Lipschitz product is INCREASING in M, NOT decreasing.
    The actual gain DECREASES with M in this row set, but this is empirical.
    The concavity-based bound is FALSIFIED and is NOT shown here.

    Continuous-vs-rounded scope: the Lean theorems prove the bound for the
    continuous real-valued CPMM model. This simulator uses integer-truncated
    reserves after A fills. The [Lean PROVEN] label refers to the continuous
    theorem; the rounded simulator is an empirical replay, not a formal proof
    of the rounded-reserve semantics.
    """
    a_A, a_B = 100.0, 2000.0
    epsilon = 2.0
    print("\nTradeoff Frontier (a_A=100, a_B=2000, L=1, epsilon=2):")
    print(f"{'M':>8} | {'m':>10} | {'win_eps0':>10} | {'win_prod':>10} | "
          f"{'lip_incr':>10} | {'lip_prod':>10} | {'actual':>10}")
    print("-" * 85)
    previous_actual: float | None = None
    for M in [1000, 5000, 10000, 50000, 100000]:
        K = M  # L = 1
        p = Pool(M, K, 0)
        L = spot_price(p)
        m = concavity_param_at_margin(p)
        window_eps0 = math.sqrt(2.0 * L / m)  # Lean PROVEN: = sqrt(M)
        window_prod = algorithm_window(L, m, epsilon=epsilon)  # production
        lip_bound = lipschitz_increment_value(L, a_A)
        lip_product = window_prod * lip_bound
        actual = simulate_sacrifice_gain(p, a_A, a_B)
        print(f"{M:>8} | {m:>10.6f} | {window_eps0:>10.2f} | {window_prod:>10.2f} | "
              f"{lip_bound:>10.2f} | {lip_product:>10.2f} | {actual:>10.4f}")
        # window_eps0 must equal sqrt(M) [Lean PROVEN]
        assert abs(window_eps0 - math.sqrt(M)) < 1e-6, (
            f"window_eps0 {window_eps0} != sqrt(M) {math.sqrt(M)} at M={M}")
        # Actual gain <= L*a_A [Lean PROVEN: cpmm_stateful_gain_bound]
        assert actual <= lip_bound + 1e-6, (
            f"Actual gain {actual} > Lipschitz bound {lip_bound} at M={M} "
            f"[Lean PROVEN bound violated]")
        if previous_actual is not None:
            assert actual < previous_actual, (
                f"Actual gain not decreasing in frontier row set: "
                f"previous={previous_actual}, current={actual}, M={M}")
        previous_actual = actual
    print("PASS: tradeoff_frontier_characterization "
          "(window_eps0=sqrt(M) [Lean]; stateful gain <= L*a_A [Lean PROVEN]; "
          "actual decreases [empirical])")


# ---------------------------------------------------------------------------
# Test 10: Pool-parameter m certificate checker [Lean bridge + empirical replay]
# ---------------------------------------------------------------------------

def test_pool_parameter_m_certificate_accepts_valid_corpus() -> None:
    """Accept endpoint-curvature m certificates and check formula direction.

    Lean proves the arithmetic endpoint lower bound:
      m_endpoint <= T0(a) + T1(a) for all a in [0,D].

    This test checks the deterministic certificate boundary and samples the
    concrete curvature curve to catch sign, endpoint, or fee-direction mistakes.
    The sampling is empirical support; the universal inequality is Lean-proven.
    """
    rng = random.Random(20260721)
    accepted = 0
    conservative = 0
    tight_at_boundary = 0
    for i in range(300):
        p0 = Pool(
            reserve_in=rng.randint(100, 100_000),
            reserve_out=rng.randint(100, 100_000),
            fee_bps=rng.choice([0, 5, 30, 100, 300, 1000, 5000]),
        )
        p1 = Pool(
            reserve_in=rng.randint(100, 100_000),
            reserve_out=rng.randint(100, 100_000),
            fee_bps=rng.choice([0, 5, 30, 100, 300, 1000, 5000]),
        )
        D = 0 if i % 75 == 0 else rng.randint(1, 20_000)
        raw = build_pool_parameter_m_certificate(p0, p1, D)
        result = verify_pool_parameter_m_certificate_bytes(p0, p1, D, raw)
        assert result.accepted, result
        assert result.reject is None
        assert result.m is not None and result.m > 0.0
        assert result.endpoint_bound is not None and result.endpoint_bound > 0.0
        accepted += 1

        if D == 0:
            grid_min = split_curvature_at(p0, p1, D, 0.0)
        else:
            points = [D * i / 80.0 for i in range(81)]
            grid_min = min(split_curvature_at(p0, p1, D, a) for a in points)
        assert result.m <= grid_min * (1.0 + 1e-10), (
            f"Endpoint m certificate exceeded sampled curvature: m={result.m}, "
            f"grid_min={grid_min}, p0={p0}, p1={p1}, D={D}")
        if result.m < grid_min * (1.0 - 1e-6):
            conservative += 1
        else:
            tight_at_boundary += 1

    assert accepted == 300
    assert conservative > 0
    assert tight_at_boundary > 0
    print("PASS: pool_parameter_m_certificate_accepts_valid_corpus "
          f"({accepted} certificates, conservative={conservative}, "
          f"tight_at_boundary={tight_at_boundary})")


def test_pool_parameter_m_certificate_rejects_mutations() -> None:
    p0 = Pool(reserve_in=1000, reserve_out=1400, fee_bps=30)
    p1 = Pool(reserve_in=1800, reserve_out=900, fee_bps=100)
    D = 250
    raw = build_pool_parameter_m_certificate(p0, p1, D)
    valid = verify_pool_parameter_m_certificate_bytes(p0, p1, D, raw)
    assert valid.accepted and valid.m is not None
    cert = json.loads(raw.decode("utf-8"))

    cases: list[tuple[str, bytes, PoolMReject]] = []
    mutated = dict(cert)
    mutated["schema"] = "wrong"
    cases.append(("bad_schema", _canonical_json_bytes(mutated), PoolMReject.BAD_SCHEMA))

    mutated = dict(cert)
    mutated["authority_effects"] = True
    cases.append(("authority", _canonical_json_bytes(mutated), PoolMReject.AUTHORITY_EFFECTS_PRESENT))

    mutated = dict(cert)
    mutated["domain_hash"] = "0" * 64
    cases.append(("domain_hash", _canonical_json_bytes(mutated), PoolMReject.DOMAIN_HASH_MISMATCH))

    mutated = dict(cert)
    mutated["endpoint_bound"] = valid.m * 1.01
    cases.append(("stale_endpoint", _canonical_json_bytes(mutated), PoolMReject.STALE_ENDPOINT_BOUND))

    mutated = dict(cert)
    mutated["m"] = valid.m * 1.01
    cases.append(("inflated_m", _canonical_json_bytes(mutated), PoolMReject.BAD_M))

    mutated = dict(cert)
    mutated["m"] = valid.m * 0.99
    cases.append(("understated_m", _canonical_json_bytes(mutated), PoolMReject.BAD_M))

    mutated = dict(cert)
    mutated["m"] = 0.0
    cases.append(("zero_m", _canonical_json_bytes(mutated), PoolMReject.BAD_M))

    duplicate_raw = raw.replace(b'"schema":', b'"schema":"duplicate","schema":', 1)
    cases.append(("duplicate_key", duplicate_raw, PoolMReject.DUPLICATE_KEY))

    noncanonical_raw = json.dumps(cert, sort_keys=True, indent=2).encode("utf-8")
    cases.append(("noncanonical", noncanonical_raw, PoolMReject.NONCANONICAL_BYTES))

    too_large_raw = b"{" + b" " * (MAX_POOL_M_CERTIFICATE_BYTES + 1) + b"}"
    cases.append(("too_large", too_large_raw, PoolMReject.CERTIFICATE_TOO_LARGE))

    bad_domain = verify_pool_parameter_m_certificate_bytes(
        Pool(reserve_in=1000, reserve_out=1400, fee_bps=10000),
        p1,
        D,
        raw,
    )
    assert bad_domain.reject == PoolMReject.BAD_DOMAIN

    for name, mutated_raw, expected in cases:
        result = verify_pool_parameter_m_certificate_bytes(p0, p1, D, mutated_raw)
        assert not result.accepted, name
        assert result.reject == expected, (name, result.reject, expected)

    print("PASS: pool_parameter_m_certificate_rejects_mutations "
          f"({len(cases) + 1} negative cases)")


# ---------------------------------------------------------------------------
# Test 11: Exact curvature m certificate [closed-form probe + replay]
# ---------------------------------------------------------------------------

def test_endpoint_curvature_bound_is_not_exact() -> None:
    """A symmetric split shows the endpoint floor can be >2x conservative."""
    p0 = Pool(reserve_in=1000, reserve_out=1000, fee_bps=0)
    p1 = Pool(reserve_in=1000, reserve_out=1000, fee_bps=0)
    D = 1000

    endpoint = split_endpoint_curvature_lower_bound(p0, p1, D)
    exact = split_exact_curvature_lower_bound(p0, p1, D)
    minimizer = split_exact_curvature_minimizer(p0, p1, D)

    assert abs(minimizer - 500.0) <= 1e-9
    assert exact > endpoint * 2.0
    assert split_curvature_at(p0, p1, D, minimizer) == exact
    for a in [0.0, 1.0, 100.0, 250.0, 500.0, 750.0, 999.0, 1000.0]:
        assert split_curvature_at(p0, p1, D, a) >= exact * (1.0 - 1e-12)

    print("PASS: endpoint_curvature_bound_is_not_exact "
          f"(endpoint={endpoint:.12g}, exact={exact:.12g}, a*={minimizer:.6g})")


def test_symmetric_exact_curvature_minimizer_at_half() -> None:
    """Symmetric two-pool curvature is minimized at D/2.

    Lean proves this real-arithmetic inequality for the symmetric subfamily.
    This replay binds the theorem to the research checker formula and keeps
    boundary cases (`D=0`, tiny `D`, high but non-100% fees) in the corpus.
    """
    rng = random.Random(20260731)
    accepted = 0
    improved_over_endpoint = 0
    max_endpoint_improvement = 1.0
    fee_choices = [0, 5, 30, 100, 300, 1000, 5000, 9000]
    for i in range(200):
        pool = Pool(
            reserve_in=rng.randint(100, 100_000),
            reserve_out=rng.randint(100, 100_000),
            fee_bps=rng.choice(fee_choices),
        )
        D = 0 if i % 50 == 0 else rng.choice([1, 2, rng.randint(3, 20_000)])
        midpoint = float(D) / 2.0
        minimizer = split_exact_curvature_minimizer(pool, pool, D)
        exact = split_exact_curvature_lower_bound(pool, pool, D)
        midpoint_curvature = split_curvature_at(pool, pool, D, midpoint)
        endpoint = split_endpoint_curvature_lower_bound(pool, pool, D)

        assert abs(minimizer - midpoint) <= 1e-8 * max(1.0, float(D)), (
            f"symmetric minimizer drifted from midpoint: minimizer={minimizer}, "
            f"midpoint={midpoint}, pool={pool}, D={D}")
        assert _close(exact, midpoint_curvature, rel=1e-9), (
            f"exact bound should equal midpoint curvature for symmetric pools: "
            f"exact={exact}, midpoint={midpoint_curvature}, pool={pool}, D={D}")

        probe_points = [0.0, midpoint, float(D)]
        if D > 0:
            probe_points.extend(float(D) * j / 32.0 for j in range(33))
            probe_points.extend(rng.random() * float(D) for _ in range(8))
        for a in probe_points:
            curvature = split_curvature_at(pool, pool, D, a)
            assert curvature + 1e-12 >= midpoint_curvature * (1.0 - 1e-10), (
                f"symmetric midpoint lower bound violated: curvature={curvature}, "
                f"midpoint={midpoint_curvature}, a={a}, pool={pool}, D={D}")

        if D > 0:
            assert exact > endpoint * (1.0 + 1e-12), (
                f"symmetric exact floor should strictly improve endpoint when D>0: "
                f"exact={exact}, endpoint={endpoint}, pool={pool}, D={D}")
            improved_over_endpoint += 1
            max_endpoint_improvement = max(max_endpoint_improvement, exact / endpoint)
        accepted += 1

    assert accepted == 200
    assert improved_over_endpoint > 0
    print("PASS: symmetric_exact_curvature_minimizer_at_half "
          f"({accepted} configs, improved={improved_over_endpoint}, "
          f"max_endpoint_improvement={max_endpoint_improvement:.6g}x)")


def _construct_fee_free_stationary_case(
    reserve_in_0: int,
    reserve_in_1: int,
    D: int,
    minimizer_a: int,
) -> tuple[Pool, Pool, int, Fraction]:
    """Construct a fee-free asymmetric domain with exact rational stationarity."""
    if not (0 <= minimizer_a <= D):
        raise ValueError("minimizer_a must be inside [0,D]")
    x0 = reserve_in_0 + minimizer_a
    y0 = reserve_in_1 + D - minimizer_a
    p0 = Pool(
        reserve_in=reserve_in_0,
        reserve_out=reserve_in_1 * (x0 ** 4),
        fee_bps=0,
    )
    p1 = Pool(
        reserve_in=reserve_in_1,
        reserve_out=reserve_in_0 * (y0 ** 4),
        fee_bps=0,
    )
    return p0, p1, D, Fraction(minimizer_a, 1)


def test_stationary_curvature_m_certificate_accepts_constructive_asymmetric_corpus() -> None:
    """Exact rational stationary witnesses consume the Lean normalized theorem.

    The corpus constructs asymmetric fee-free pool pairs whose chosen split
    satisfies the derivative stationarity equality exactly. The verifier then
    checks the witness and emits the exact curvature floor as rational data.
    """
    rng = random.Random(20260801)
    accepted = 0
    non_midpoint = 0
    improved = 0
    max_endpoint_improvement = 1.0
    for i in range(200):
        reserve_in_0 = rng.randint(50, 1000)
        reserve_in_1 = rng.randint(50, 1000)
        D = rng.randint(4, 5000)
        minimizer_int = rng.randint(1, D - 1)
        if 2 * minimizer_int == D:
            minimizer_int = 1 if minimizer_int != 1 else D - 1
        p0, p1, D, minimizer_a = _construct_fee_free_stationary_case(
            reserve_in_0,
            reserve_in_1,
            D,
            minimizer_int,
        )

        raw = build_stationary_curvature_m_certificate(p0, p1, D, minimizer_a)
        result = verify_stationary_curvature_m_certificate_bytes(p0, p1, D, raw)
        assert result.accepted, result
        assert result.reject is None
        assert result.m_fraction is not None and result.m_fraction > 0
        assert result.minimizer_a == float(minimizer_a)
        accepted += 1

        exact_probe = split_exact_curvature_lower_bound(p0, p1, D)
        assert _close(float(result.m_fraction), exact_probe, rel=1e-8), (
            f"stationary rational floor diverged from float exact probe: "
            f"m={result.m_fraction}, exact_probe={exact_probe}, p0={p0}, p1={p1}, D={D}")

        endpoint = split_endpoint_curvature_lower_bound_fraction(p0, p1, D)
        if result.m_fraction > endpoint:
            improved += 1
            max_endpoint_improvement = max(
                max_endpoint_improvement,
                float(result.m_fraction / endpoint),
            )
        if minimizer_a != Fraction(D, 2):
            non_midpoint += 1

        probe_points = [Fraction(0, 1), minimizer_a, Fraction(D, 1)]
        probe_points.extend(Fraction(D * j, 32) for j in range(33))
        for _ in range(8):
            probe_points.append(Fraction(rng.randint(0, D * 1024), 1024))
        for a in probe_points:
            if 0 <= a <= D:
                curvature = split_curvature_at_fraction(p0, p1, D, a)
                assert curvature >= result.m_fraction, (
                    f"stationary certificate floor violated: curvature={curvature}, "
                    f"m={result.m_fraction}, a={a}, p0={p0}, p1={p1}, D={D}")

    assert accepted == 200
    assert non_midpoint == accepted
    assert improved > 0
    print("PASS: stationary_curvature_m_certificate_accepts_constructive_asymmetric_corpus "
          f"({accepted} certificates, non_midpoint={non_midpoint}, "
          f"improved={improved}, max_endpoint_improvement={max_endpoint_improvement:.6g}x)")


def test_stationary_curvature_m_certificate_rejects_mutations() -> None:
    p0, p1, D, minimizer_a = _construct_fee_free_stationary_case(100, 150, 80, 17)
    raw = build_stationary_curvature_m_certificate(p0, p1, D, minimizer_a)
    valid = verify_stationary_curvature_m_certificate_bytes(p0, p1, D, raw)
    assert valid.accepted and valid.m_fraction is not None
    cert = json.loads(raw.decode("utf-8"))

    cases: list[tuple[str, bytes, PoolMReject]] = []
    mutated = dict(cert)
    mutated["schema"] = "wrong"
    cases.append(("bad_schema", _canonical_json_bytes(mutated), PoolMReject.BAD_SCHEMA))

    mutated = dict(cert)
    mutated["authority_effects"] = True
    cases.append(("authority", _canonical_json_bytes(mutated), PoolMReject.AUTHORITY_EFFECTS_PRESENT))

    mutated = dict(cert)
    mutated["domain_hash"] = "0" * 64
    cases.append(("domain_hash", _canonical_json_bytes(mutated), PoolMReject.DOMAIN_HASH_MISMATCH))

    mutated = dict(cert)
    mutated["minimizer_a"] = _fraction_payload(Fraction(D + 1, 1))
    cases.append(("out_of_range_minimizer", _canonical_json_bytes(mutated), PoolMReject.STALE_MINIMIZER))

    mutated = dict(cert)
    mutated["minimizer_a"] = _fraction_payload(minimizer_a + 1)
    cases.append(("nonstationary_minimizer", _canonical_json_bytes(mutated), PoolMReject.STALE_STATIONARITY))

    mutated = dict(cert)
    stale_lhs = _fraction_from_payload(mutated["stationarity_lhs"])
    assert stale_lhs is not None
    mutated["stationarity_lhs"] = _fraction_payload(stale_lhs + 1)
    cases.append(("stale_stationarity_lhs", _canonical_json_bytes(mutated), PoolMReject.STALE_STATIONARITY))

    mutated = dict(cert)
    stale_q = _fraction_from_payload(mutated["q"])
    assert stale_q is not None
    mutated["q"] = _fraction_payload(stale_q + 1)
    cases.append(("stale_q", _canonical_json_bytes(mutated), PoolMReject.STALE_STATIONARITY))

    mutated = dict(cert)
    stale_scale = _fraction_from_payload(mutated["scale"])
    assert stale_scale is not None
    mutated["scale"] = _fraction_payload(stale_scale + 1)
    cases.append(("stale_scale", _canonical_json_bytes(mutated), PoolMReject.STALE_STATIONARITY))

    mutated = dict(cert)
    mutated["m"] = _fraction_payload(valid.m_fraction + 1)
    cases.append(("bad_m", _canonical_json_bytes(mutated), PoolMReject.BAD_M))

    duplicate_raw = raw.replace(b'"schema":', b'"schema":"duplicate","schema":', 1)
    cases.append(("duplicate_key", duplicate_raw, PoolMReject.DUPLICATE_KEY))

    noncanonical_raw = json.dumps(cert, sort_keys=True, indent=2).encode("utf-8")
    cases.append(("noncanonical", noncanonical_raw, PoolMReject.NONCANONICAL_BYTES))

    too_large_raw = b"{" + b" " * (MAX_POOL_INTERVAL_M_CERTIFICATE_BYTES + 1) + b"}"
    cases.append(("too_large", too_large_raw, PoolMReject.CERTIFICATE_TOO_LARGE))

    bad_domain = verify_stationary_curvature_m_certificate_bytes(
        Pool(reserve_in=100, reserve_out=p0.reserve_out, fee_bps=10000),
        p1,
        D,
        raw,
    )
    assert bad_domain.reject == PoolMReject.BAD_DOMAIN

    for name, mutated_raw, expected in cases:
        result = verify_stationary_curvature_m_certificate_bytes(p0, p1, D, mutated_raw)
        assert not result.accepted, name
        assert result.reject == expected, (name, result.reject, expected)

    print("PASS: stationary_curvature_m_certificate_rejects_mutations "
          f"({len(cases) + 1} negative cases)")


def test_exact_curvature_m_certificate_accepts_valid_corpus() -> None:
    """Accept exact-curvature certificates and replay the minimizer relation.

    The closed-form minimizer is a deterministic research checker path. Lean
    does not yet prove the minimizer formula; the replay checks direction,
    canonicalization, and domain binding so stale or inflated packets fail.
    """
    rng = random.Random(20260722)
    accepted = 0
    improved = 0
    max_improvement = 1.0
    for i in range(300):
        p0 = Pool(
            reserve_in=rng.randint(100, 100_000),
            reserve_out=rng.randint(100, 100_000),
            fee_bps=rng.choice([0, 5, 30, 100, 300, 1000, 5000]),
        )
        p1 = Pool(
            reserve_in=rng.randint(100, 100_000),
            reserve_out=rng.randint(100, 100_000),
            fee_bps=rng.choice([0, 5, 30, 100, 300, 1000, 5000]),
        )
        D = 0 if i % 75 == 0 else rng.randint(1, 20_000)
        raw = build_exact_curvature_m_certificate(p0, p1, D)
        result = verify_exact_curvature_m_certificate_bytes(p0, p1, D, raw)
        assert result.accepted, result
        assert result.reject is None
        assert result.m is not None and result.m > 0.0
        assert result.endpoint_bound is not None and result.endpoint_bound > 0.0
        assert result.exact_bound is not None and result.exact_bound > 0.0
        assert result.minimizer_a is not None
        assert 0.0 <= result.minimizer_a <= float(D)
        assert result.exact_bound >= result.endpoint_bound * (1.0 - 1e-10)
        accepted += 1

        if result.exact_bound > result.endpoint_bound * (1.0 + 1e-8):
            improved += 1
            max_improvement = max(max_improvement, result.exact_bound / result.endpoint_bound)

        grid_points = [0.0, float(D), result.minimizer_a]
        if D > 0:
            grid_points.extend(D * j / 80.0 for j in range(81))
        grid_min = min(split_curvature_at(p0, p1, D, a) for a in grid_points)
        assert result.m <= grid_min * (1.0 + 1e-10), (
            f"Exact m exceeded sampled curvature: m={result.m}, "
            f"grid_min={grid_min}, p0={p0}, p1={p1}, D={D}")
        assert grid_min <= result.m * (1.0 + 1e-8), (
            f"Exact minimizer was not represented in replay grid: m={result.m}, "
            f"grid_min={grid_min}, p0={p0}, p1={p1}, D={D}")

    assert accepted == 300
    assert improved > 0
    print("PASS: exact_curvature_m_certificate_accepts_valid_corpus "
          f"({accepted} certificates, improved={improved}, "
          f"max_improvement={max_improvement:.6g}x)")


def test_exact_curvature_m_certificate_rejects_mutations() -> None:
    p0 = Pool(reserve_in=1000, reserve_out=1400, fee_bps=30)
    p1 = Pool(reserve_in=1800, reserve_out=900, fee_bps=100)
    D = 250
    raw = build_exact_curvature_m_certificate(p0, p1, D)
    valid = verify_exact_curvature_m_certificate_bytes(p0, p1, D, raw)
    assert valid.accepted and valid.m is not None
    cert = json.loads(raw.decode("utf-8"))

    cases: list[tuple[str, bytes, PoolMReject]] = []
    mutated = dict(cert)
    mutated["schema"] = "wrong"
    cases.append(("bad_schema", _canonical_json_bytes(mutated), PoolMReject.BAD_SCHEMA))

    mutated = dict(cert)
    mutated["authority_effects"] = True
    cases.append(("authority", _canonical_json_bytes(mutated), PoolMReject.AUTHORITY_EFFECTS_PRESENT))

    mutated = dict(cert)
    mutated["domain_hash"] = "0" * 64
    cases.append(("domain_hash", _canonical_json_bytes(mutated), PoolMReject.DOMAIN_HASH_MISMATCH))

    mutated = dict(cert)
    mutated["minimizer_a"] = float(mutated["minimizer_a"]) + 1.0
    cases.append(("stale_minimizer", _canonical_json_bytes(mutated), PoolMReject.STALE_MINIMIZER))

    mutated = dict(cert)
    mutated["exact_bound"] = valid.m * 1.01
    cases.append(("stale_exact", _canonical_json_bytes(mutated), PoolMReject.STALE_EXACT_BOUND))

    mutated = dict(cert)
    mutated["m"] = valid.m * 1.01
    cases.append(("inflated_m", _canonical_json_bytes(mutated), PoolMReject.BAD_M))

    mutated = dict(cert)
    mutated["m"] = valid.m * 0.99
    cases.append(("understated_m", _canonical_json_bytes(mutated), PoolMReject.BAD_M))

    duplicate_raw = raw.replace(b'"schema":', b'"schema":"duplicate","schema":', 1)
    cases.append(("duplicate_key", duplicate_raw, PoolMReject.DUPLICATE_KEY))

    noncanonical_raw = json.dumps(cert, sort_keys=True, indent=2).encode("utf-8")
    cases.append(("noncanonical", noncanonical_raw, PoolMReject.NONCANONICAL_BYTES))

    too_large_raw = b"{" + b" " * (MAX_POOL_M_CERTIFICATE_BYTES + 1) + b"}"
    cases.append(("too_large", too_large_raw, PoolMReject.CERTIFICATE_TOO_LARGE))

    bad_domain = verify_exact_curvature_m_certificate_bytes(
        Pool(reserve_in=1000, reserve_out=1400, fee_bps=10000),
        p1,
        D,
        raw,
    )
    assert bad_domain.reject == PoolMReject.BAD_DOMAIN

    for name, mutated_raw, expected in cases:
        result = verify_exact_curvature_m_certificate_bytes(p0, p1, D, mutated_raw)
        assert not result.accepted, name
        assert result.reject == expected, (name, result.reject, expected)

    print("PASS: exact_curvature_m_certificate_rejects_mutations "
          f"({len(cases) + 1} negative cases)")


# ---------------------------------------------------------------------------
# Test 12: Exact curvature float-overflow domain rejection [CBC boundary]
# ---------------------------------------------------------------------------

def test_exact_curvature_m_certificate_rejects_float_overflow_domain() -> None:
    """Huge integer domains are rejected before the research float path."""
    overflow_reserve = 1 << MAX_EXACT_CURVATURE_FLOAT_DOMAIN_BITS
    unsafe_p0 = Pool(reserve_in=overflow_reserve, reserve_out=1000, fee_bps=0)
    p1 = Pool(reserve_in=1000, reserve_out=1000, fee_bps=0)
    D = 1

    assert _pool_domain_valid(unsafe_p0)
    assert not _exact_curvature_float_domain_valid(unsafe_p0, p1, D)
    assert math.isnan(split_exact_curvature_minimizer(unsafe_p0, p1, D))
    assert split_exact_curvature_lower_bound(unsafe_p0, p1, D) == 0.0

    try:
        build_exact_curvature_m_certificate(unsafe_p0, p1, D)
        raise AssertionError("unsafe exact-curvature float domain was accepted")
    except ValueError:
        pass

    safe_raw = build_exact_curvature_m_certificate(
        Pool(reserve_in=1000, reserve_out=1000, fee_bps=0),
        p1,
        D,
    )
    rejected = verify_exact_curvature_m_certificate_bytes(unsafe_p0, p1, D, safe_raw)
    assert not rejected.accepted
    assert rejected.reject == PoolMReject.BAD_DOMAIN

    print("PASS: exact_curvature_m_certificate_rejects_float_overflow_domain "
          f"(max_bits={MAX_EXACT_CURVATURE_FLOAT_DOMAIN_BITS})")


# ---------------------------------------------------------------------------
# Test 13: Rational interval m certificate [Lean interval bridge + exact replay]
# ---------------------------------------------------------------------------

def test_interval_curvature_m_certificate_refines_endpoint_bound() -> None:
    """A 64-interval rational certificate recovers most of the exact gain."""
    p0 = Pool(reserve_in=1000, reserve_out=1000, fee_bps=0)
    p1 = Pool(reserve_in=1000, reserve_out=1000, fee_bps=0)
    D = 1000

    endpoint = split_endpoint_curvature_lower_bound_fraction(p0, p1, D)
    exact = split_exact_curvature_lower_bound(p0, p1, D)
    raw = build_interval_curvature_m_certificate(p0, p1, D, interval_count=64)
    result = verify_interval_curvature_m_certificate_bytes(p0, p1, D, raw)

    assert result.accepted, result
    assert result.m_fraction is not None
    assert result.interval_count == 64
    assert result.m_fraction > endpoint * 2
    assert float(result.m_fraction) <= exact * (1.0 + 1e-12)

    print("PASS: interval_curvature_m_certificate_refines_endpoint_bound "
          f"(endpoint={float(endpoint):.12g}, interval={float(result.m_fraction):.12g}, "
          f"exact={exact:.12g})")


def test_interval_curvature_m_certificate_accepts_valid_corpus() -> None:
    """Accept rational interval certificates and compare against float exact probe.

    The interval floor is exact rational arithmetic and uses the Lean-proven
    interval monotonicity shape. The float exact minimizer remains a reference
    probe, not a required proof artifact.
    """
    rng = random.Random(20260723)
    accepted = 0
    improved = 0
    max_improvement = 1.0
    for i in range(300):
        p0 = Pool(
            reserve_in=rng.randint(100, 100_000),
            reserve_out=rng.randint(100, 100_000),
            fee_bps=rng.choice([0, 5, 30, 100, 300, 1000, 5000]),
        )
        p1 = Pool(
            reserve_in=rng.randint(100, 100_000),
            reserve_out=rng.randint(100, 100_000),
            fee_bps=rng.choice([0, 5, 30, 100, 300, 1000, 5000]),
        )
        D = 0 if i % 75 == 0 else rng.randint(1, 20_000)
        raw = build_interval_curvature_m_certificate(p0, p1, D, interval_count=64)
        result = verify_interval_curvature_m_certificate_bytes(p0, p1, D, raw)
        assert result.accepted, result
        assert result.reject is None
        assert result.m_fraction is not None and result.m_fraction > 0
        assert result.endpoint_bound is not None and result.endpoint_bound > 0.0
        assert result.interval_bound is not None and result.interval_bound > 0.0
        assert result.interval_count == (1 if D == 0 else 64)
        accepted += 1

        endpoint_fraction = split_endpoint_curvature_lower_bound_fraction(p0, p1, D)
        assert result.m_fraction >= endpoint_fraction
        exact_probe = split_exact_curvature_lower_bound(p0, p1, D)
        assert float(result.m_fraction) <= exact_probe * (1.0 + 1e-10)

        improvement = float(result.m_fraction / endpoint_fraction)
        if improvement > 1.0 + 1e-8:
            improved += 1
            max_improvement = max(max_improvement, improvement)

    assert accepted == 300
    assert improved > 0
    print("PASS: interval_curvature_m_certificate_accepts_valid_corpus "
          f"({accepted} certificates, improved={improved}, "
          f"max_improvement={max_improvement:.6g}x)")


def test_interval_curvature_m_certificate_rejects_mutations() -> None:
    p0 = Pool(reserve_in=1000, reserve_out=1400, fee_bps=30)
    p1 = Pool(reserve_in=1800, reserve_out=900, fee_bps=100)
    D = 250
    raw = build_interval_curvature_m_certificate(p0, p1, D, interval_count=8)
    valid = verify_interval_curvature_m_certificate_bytes(p0, p1, D, raw)
    assert valid.accepted and valid.m_fraction is not None
    cert = json.loads(raw.decode("utf-8"))

    cases: list[tuple[str, bytes, PoolMReject]] = []
    mutated = dict(cert)
    mutated["schema"] = "wrong"
    cases.append(("bad_schema", _canonical_json_bytes(mutated), PoolMReject.BAD_SCHEMA))

    mutated = dict(cert)
    mutated["authority_effects"] = True
    cases.append(("authority", _canonical_json_bytes(mutated), PoolMReject.AUTHORITY_EFFECTS_PRESENT))

    mutated = dict(cert)
    mutated["domain_hash"] = "0" * 64
    cases.append(("domain_hash", _canonical_json_bytes(mutated), PoolMReject.DOMAIN_HASH_MISMATCH))

    mutated = dict(cert)
    mutated["settlement_authority"] = True
    cases.append(("unexpected_top_level", _canonical_json_bytes(mutated), PoolMReject.BAD_SCHEMA))

    mutated = dict(cert)
    intervals = [dict(item) for item in cert["intervals"]]
    intervals[1] = dict(intervals[1])
    intervals[1]["lo"] = intervals[0]["lo"]
    mutated["intervals"] = intervals
    cases.append(("interval_gap", _canonical_json_bytes(mutated), PoolMReject.BAD_INTERVALS))

    mutated = dict(cert)
    intervals = [dict(item) for item in cert["intervals"]]
    intervals[0] = dict(intervals[0])
    intervals[0]["note"] = "ignored"
    mutated["intervals"] = intervals
    cases.append(("unexpected_interval_key", _canonical_json_bytes(mutated), PoolMReject.BAD_INTERVALS))

    mutated = dict(cert)
    intervals = [dict(item) for item in cert["intervals"]]
    intervals[0] = dict(intervals[0])
    stale = _fraction_from_payload(intervals[0]["lower_bound"])
    assert stale is not None
    intervals[0]["lower_bound"] = _fraction_payload(stale + 1)
    mutated["intervals"] = intervals
    cases.append(("stale_interval_bound", _canonical_json_bytes(mutated), PoolMReject.STALE_INTERVAL_BOUND))

    mutated = dict(cert)
    m_fraction = _fraction_from_payload(mutated["m"])
    assert m_fraction is not None
    mutated["m"] = _fraction_payload(m_fraction + 1)
    cases.append(("inflated_m", _canonical_json_bytes(mutated), PoolMReject.BAD_M))

    mutated = dict(cert)
    m_fraction = _fraction_from_payload(mutated["m"])
    assert m_fraction is not None
    mutated["m"] = _fraction_payload(m_fraction / 2)
    cases.append(("understated_m", _canonical_json_bytes(mutated), PoolMReject.BAD_M))

    mutated = dict(cert)
    bad_rational = dict(mutated["m"])
    bad_rational["num"] = bad_rational["den"]
    mutated["m"] = bad_rational
    cases.append(("bad_rational", _canonical_json_bytes(mutated), PoolMReject.BAD_RATIONAL_FIELD))

    mutated = dict(cert)
    mutated["interval_count"] = MAX_INTERVAL_M_CERTIFICATE_INTERVALS + 1
    minimal_interval = {
        "lo": {"num": 0, "den": 1},
        "hi": {"num": 0, "den": 1},
        "lower_bound": {"num": 1, "den": 1},
    }
    mutated["intervals"] = [minimal_interval] * (MAX_INTERVAL_M_CERTIFICATE_INTERVALS + 1)
    cases.append(("too_many_intervals", _canonical_json_bytes(mutated), PoolMReject.TOO_MANY_INTERVALS))

    duplicate_raw = raw.replace(b'"schema":', b'"schema":"duplicate","schema":', 1)
    cases.append(("duplicate_key", duplicate_raw, PoolMReject.DUPLICATE_KEY))

    noncanonical_raw = json.dumps(cert, sort_keys=True, indent=2).encode("utf-8")
    cases.append(("noncanonical", noncanonical_raw, PoolMReject.NONCANONICAL_BYTES))

    too_large_raw = b"{" + b" " * (MAX_POOL_INTERVAL_M_CERTIFICATE_BYTES + 1) + b"}"
    cases.append(("too_large", too_large_raw, PoolMReject.CERTIFICATE_TOO_LARGE))

    bad_domain = verify_interval_curvature_m_certificate_bytes(
        Pool(reserve_in=1000, reserve_out=1400, fee_bps=10000),
        p1,
        D,
        raw,
    )
    assert bad_domain.reject == PoolMReject.BAD_DOMAIN

    for name, mutated_raw, expected in cases:
        result = verify_interval_curvature_m_certificate_bytes(p0, p1, D, mutated_raw)
        assert not result.accepted, name
        assert result.reject == expected, (name, result.reject, expected)

    print("PASS: interval_curvature_m_certificate_rejects_mutations "
          f"({len(cases) + 1} negative cases)")


# ---------------------------------------------------------------------------
# Test 14: Best-cover rational interval m certificate [exact replay portfolio]
# ---------------------------------------------------------------------------

def test_best_interval_curvature_m_certificate_dominates_uniform_corpus() -> None:
    """The generated best-cover certificate is never worse than uniform replay."""
    p0 = Pool(reserve_in=1000, reserve_out=1000, fee_bps=0)
    p1 = Pool(reserve_in=1000, reserve_out=1000, fee_bps=0)
    D = 1000

    uniform_raw = build_interval_curvature_m_certificate(p0, p1, D, interval_count=64)
    best_raw = build_best_interval_curvature_m_certificate(p0, p1, D, interval_count=64)
    uniform = verify_interval_curvature_m_certificate_bytes(p0, p1, D, uniform_raw)
    best = verify_interval_curvature_m_certificate_bytes(p0, p1, D, best_raw)
    assert uniform.accepted and uniform.m_fraction is not None
    assert best.accepted and best.m_fraction is not None
    assert best.interval_count == 64
    assert best.m_fraction > uniform.m_fraction

    rng = random.Random(20260725)
    accepted = 0
    improved = 0
    max_improvement = 1.0
    for i in range(300):
        p0 = Pool(
            reserve_in=rng.randint(100, 100_000),
            reserve_out=rng.randint(100, 100_000),
            fee_bps=rng.choice([0, 5, 30, 100, 300, 1000, 5000]),
        )
        p1 = Pool(
            reserve_in=rng.randint(100, 100_000),
            reserve_out=rng.randint(100, 100_000),
            fee_bps=rng.choice([0, 5, 30, 100, 300, 1000, 5000]),
        )
        D = 0 if i % 75 == 0 else rng.randint(1, 20_000)
        uniform_raw = build_interval_curvature_m_certificate(p0, p1, D, interval_count=64)
        best_raw = build_best_interval_curvature_m_certificate(p0, p1, D, interval_count=64)
        uniform = verify_interval_curvature_m_certificate_bytes(p0, p1, D, uniform_raw)
        best = verify_interval_curvature_m_certificate_bytes(p0, p1, D, best_raw)

        assert uniform.accepted and uniform.m_fraction is not None
        assert best.accepted and best.m_fraction is not None
        assert best.m_fraction >= uniform.m_fraction
        exact_probe = split_exact_curvature_lower_bound(p0, p1, D)
        assert float(best.m_fraction) <= exact_probe * (1.0 + 1e-10)
        accepted += 1

        improvement = float(best.m_fraction / uniform.m_fraction)
        if improvement > 1.0 + 1e-12:
            improved += 1
            max_improvement = max(max_improvement, improvement)

    assert accepted == 300
    assert improved >= 250
    assert max_improvement > 1.005
    print("PASS: best_interval_curvature_m_certificate_dominates_uniform_corpus "
          f"({accepted} certificates, improved={improved}, "
          f"max_best_over_uniform={max_improvement:.6g}x)")


# ---------------------------------------------------------------------------
# Test 15: Greedy interval-refinement m certificate [Lean monotonicity bridge]
# ---------------------------------------------------------------------------

def test_refined_interval_curvature_m_certificate_monotone() -> None:
    """Exact interval splitting never lowers the certified child floors."""
    p0 = Pool(reserve_in=1000, reserve_out=1000, fee_bps=0)
    p1 = Pool(reserve_in=1000, reserve_out=1000, fee_bps=0)
    D = 1000

    base_raw = build_interval_curvature_m_certificate(p0, p1, D, interval_count=1)
    refined_raw = build_refined_interval_curvature_m_certificate(
        p0,
        p1,
        D,
        base_interval_count=1,
        target_interval_count=64,
    )
    base = verify_interval_curvature_m_certificate_bytes(p0, p1, D, base_raw)
    refined = verify_interval_curvature_m_certificate_bytes(p0, p1, D, refined_raw)
    assert base.accepted and base.m_fraction is not None
    assert refined.accepted and refined.m_fraction is not None
    assert refined.interval_count == 64
    assert refined.m_fraction > base.m_fraction

    rng = random.Random(20260726)
    local_splits_checked = 0
    accepted = 0
    improved_over_base = 0
    improved_over_uniform = 0
    max_base_improvement = 1.0
    max_uniform_improvement = 1.0
    for i in range(300):
        p0 = Pool(
            reserve_in=rng.randint(100, 100_000),
            reserve_out=rng.randint(100, 100_000),
            fee_bps=rng.choice([0, 5, 30, 100, 300, 1000, 5000]),
        )
        p1 = Pool(
            reserve_in=rng.randint(100, 100_000),
            reserve_out=rng.randint(100, 100_000),
            fee_bps=rng.choice([0, 5, 30, 100, 300, 1000, 5000]),
        )
        D = 0 if i % 75 == 0 else rng.randint(1, 20_000)

        if D > 0:
            lo = Fraction(rng.randint(0, D - 1), 1)
            hi = Fraction(rng.randint(int(lo) + 1, D), 1)
            mid = (lo + hi) / 2
            parent_floor = split_interval_curvature_lower_bound_fraction(p0, p1, D, lo, hi)
            left_floor = split_interval_curvature_lower_bound_fraction(p0, p1, D, lo, mid)
            right_floor = split_interval_curvature_lower_bound_fraction(p0, p1, D, mid, hi)
            assert left_floor >= parent_floor
            assert right_floor >= parent_floor
            local_splits_checked += 1

        base_count = 1 if D == 0 else 16
        target_count = 1 if D == 0 else 64
        base_raw = build_interval_curvature_m_certificate(p0, p1, D, interval_count=base_count)
        uniform_raw = build_interval_curvature_m_certificate(p0, p1, D, interval_count=target_count)
        refined_raw = build_refined_interval_curvature_m_certificate(
            p0,
            p1,
            D,
            base_interval_count=base_count,
            target_interval_count=target_count,
        )
        base = verify_interval_curvature_m_certificate_bytes(p0, p1, D, base_raw)
        uniform = verify_interval_curvature_m_certificate_bytes(p0, p1, D, uniform_raw)
        refined = verify_interval_curvature_m_certificate_bytes(p0, p1, D, refined_raw)

        assert base.accepted and base.m_fraction is not None
        assert uniform.accepted and uniform.m_fraction is not None
        assert refined.accepted and refined.m_fraction is not None
        assert refined.interval_count == target_count
        assert refined.m_fraction >= base.m_fraction
        exact_probe = split_exact_curvature_lower_bound(p0, p1, D)
        assert float(refined.m_fraction) <= exact_probe * (1.0 + 1e-10)
        accepted += 1

        base_improvement = float(refined.m_fraction / base.m_fraction)
        if base_improvement > 1.0 + 1e-12:
            improved_over_base += 1
            max_base_improvement = max(max_base_improvement, base_improvement)

        uniform_improvement = float(refined.m_fraction / uniform.m_fraction)
        if uniform_improvement > 1.0 + 1e-12:
            improved_over_uniform += 1
            max_uniform_improvement = max(max_uniform_improvement, uniform_improvement)

    assert local_splits_checked > 0
    assert accepted == 300
    assert improved_over_base >= 250
    assert improved_over_uniform >= 250
    print("PASS: refined_interval_curvature_m_certificate_monotone "
          f"({local_splits_checked} local splits, {accepted} certificates, "
          f"base_improved={improved_over_base}, uniform_improved={improved_over_uniform}, "
          f"max_base={max_base_improvement:.6g}x, "
          f"max_uniform={max_uniform_improvement:.6g}x)")


# ---------------------------------------------------------------------------
# Test 16: Bounded optimal midpoint-refinement audit [exact DP replay]
# ---------------------------------------------------------------------------

def test_optimal_midpoint_interval_curvature_m_certificate_audits_greedy() -> None:
    """Exact DP audits weakest-interval greedy refinement under small bounds."""
    p0 = Pool(reserve_in=1000, reserve_out=1000, fee_bps=0)
    p1 = Pool(reserve_in=1000, reserve_out=1000, fee_bps=0)
    D = 1000

    optimal_raw = build_optimal_midpoint_interval_curvature_m_certificate(
        p0,
        p1,
        D,
        base_interval_count=4,
        target_interval_count=10,
    )
    optimal = verify_interval_curvature_m_certificate_bytes(p0, p1, D, optimal_raw)
    assert optimal.accepted and optimal.m_fraction is not None
    assert optimal.interval_count == 10

    invalid_cases = [
        {"base_interval_count": 0, "target_interval_count": 10},
        {"base_interval_count": 4, "target_interval_count": 17},
        {"base_interval_count": 8, "target_interval_count": 4},
    ]
    for kwargs in invalid_cases:
        try:
            build_optimal_midpoint_interval_curvature_m_certificate(p0, p1, D, **kwargs)
            raise AssertionError(f"invalid optimal midpoint counts accepted: {kwargs}")
        except ValueError:
            pass

    rng = random.Random(20260801)
    accepted = 0
    greedy_matches = 0
    max_optimal_over_base = 1.0
    for i in range(300):
        p0 = Pool(
            reserve_in=rng.randint(1, 5000),
            reserve_out=rng.randint(1, 50_000),
            fee_bps=rng.choice([0, 30, 100, 300, 1000, 3000, 7000]),
        )
        p1 = Pool(
            reserve_in=rng.randint(1, 5000),
            reserve_out=rng.randint(1, 50_000),
            fee_bps=rng.choice([0, 30, 100, 300, 1000, 3000, 7000]),
        )
        D = 0 if i % 75 == 0 else rng.randint(2, 80)
        base_count = 1 if D == 0 else rng.choice([1, 2, 4, 8])
        if base_count > D and D > 0:
            base_count = 1
        target_count = 1 if D == 0 else rng.randint(base_count + 1, min(base_count + 5, 12))

        base_raw = build_interval_curvature_m_certificate(p0, p1, D, interval_count=base_count)
        greedy_bounds = _refine_weakest_interval_bounds(
            p0,
            p1,
            D,
            _uniform_interval_bounds(D, base_count),
            target_count,
        )
        optimal_bounds = _optimal_midpoint_refinement_bounds(
            p0,
            p1,
            D,
            base_count,
            target_count,
        )
        optimal_raw = build_optimal_midpoint_interval_curvature_m_certificate(
            p0,
            p1,
            D,
            base_interval_count=base_count,
            target_interval_count=target_count,
        )
        base = verify_interval_curvature_m_certificate_bytes(p0, p1, D, base_raw)
        optimal = verify_interval_curvature_m_certificate_bytes(p0, p1, D, optimal_raw)
        greedy_floor = _interval_floor_for_bounds(p0, p1, D, greedy_bounds)
        optimal_floor = _interval_floor_for_bounds(p0, p1, D, optimal_bounds)

        assert base.accepted and base.m_fraction is not None
        assert optimal.accepted and optimal.m_fraction is not None
        assert optimal.interval_count == target_count
        assert optimal.m_fraction == optimal_floor
        assert optimal_floor >= greedy_floor
        assert optimal.m_fraction >= base.m_fraction
        exact_probe = split_exact_curvature_lower_bound(p0, p1, D)
        assert float(optimal.m_fraction) <= exact_probe * (1.0 + 1e-10)

        if optimal_floor == greedy_floor:
            greedy_matches += 1
        max_optimal_over_base = max(max_optimal_over_base, float(optimal.m_fraction / base.m_fraction))
        accepted += 1

    assert accepted == 300
    assert greedy_matches == accepted
    assert max_optimal_over_base > 1.0
    print("PASS: optimal_midpoint_interval_curvature_m_certificate_audits_greedy "
          f"({accepted} certificates, greedy_counterexamples=0, "
          f"invalid_rejects={len(invalid_cases)}, "
          f"max_optimal_over_base={max_optimal_over_base:.6g}x)")


# ---------------------------------------------------------------------------
# Test 17: Exact count
# ---------------------------------------------------------------------------

def test_exact_count() -> None:
    empirical_test_names = [
        "test_cpmm_concavity_param_formula",
        "test_cpmm_conservation_tradeoff",
        "test_stateful_gain_lipschitz_envelope_empirical",
        "test_concavity_bound_falsified_small_trades",
        "test_concavity_bound_fails_large_trades",
        "test_actual_gain_decreases_with_depth",
        "test_min_out_cap_breaks_tradeoff",
        "test_donation_no_output_exact_optimizer",
        "test_fee_bearing_donation_no_output_exact_optimizer",
        "test_donation_optimizer_not_filled_stateful_gain",
        "test_tradeoff_frontier_characterization",
        "test_pool_parameter_m_certificate_accepts_valid_corpus",
        "test_pool_parameter_m_certificate_rejects_mutations",
        "test_endpoint_curvature_bound_is_not_exact",
        "test_symmetric_exact_curvature_minimizer_at_half",
        "test_stationary_curvature_m_certificate_accepts_constructive_asymmetric_corpus",
        "test_stationary_curvature_m_certificate_rejects_mutations",
        "test_exact_curvature_m_certificate_accepts_valid_corpus",
        "test_exact_curvature_m_certificate_rejects_mutations",
        "test_exact_curvature_m_certificate_rejects_float_overflow_domain",
        "test_interval_curvature_m_certificate_refines_endpoint_bound",
        "test_interval_curvature_m_certificate_accepts_valid_corpus",
        "test_interval_curvature_m_certificate_rejects_mutations",
        "test_best_interval_curvature_m_certificate_dominates_uniform_corpus",
        "test_refined_interval_curvature_m_certificate_monotone",
        "test_optimal_midpoint_interval_curvature_m_certificate_audits_greedy",
    ]
    assert len(empirical_test_names) == 26
    total = (
        200 + 200 + 500 + 500 + 500 + 5 + 200 + 300 + 301 + 1 + 5 + 300 + 11
        + 6 + 200 + 200 + 13 + 1 + 300 + 11 + 1 + 300 + 15 + 300 + 600 + 303
    )
    assert total == 5273, f"Expected 5273 total test configurations, got {total}"
    print(f"PASS: exact_count ({len(empirical_test_names)} empirical tests, "
          f"{total} total test configurations)")


if __name__ == "__main__":
    test_cpmm_concavity_param_formula()
    test_cpmm_conservation_tradeoff()
    test_stateful_gain_lipschitz_envelope_empirical()
    test_concavity_bound_falsified_small_trades()
    test_concavity_bound_fails_large_trades()
    test_actual_gain_decreases_with_depth()
    test_min_out_cap_breaks_tradeoff()
    test_donation_no_output_exact_optimizer()
    test_fee_bearing_donation_no_output_exact_optimizer()
    test_donation_optimizer_not_filled_stateful_gain()
    test_tradeoff_frontier_characterization()
    test_pool_parameter_m_certificate_accepts_valid_corpus()
    test_pool_parameter_m_certificate_rejects_mutations()
    test_endpoint_curvature_bound_is_not_exact()
    test_symmetric_exact_curvature_minimizer_at_half()
    test_stationary_curvature_m_certificate_accepts_constructive_asymmetric_corpus()
    test_stationary_curvature_m_certificate_rejects_mutations()
    test_exact_curvature_m_certificate_accepts_valid_corpus()
    test_exact_curvature_m_certificate_rejects_mutations()
    test_exact_curvature_m_certificate_rejects_float_overflow_domain()
    test_interval_curvature_m_certificate_refines_endpoint_bound()
    test_interval_curvature_m_certificate_accepts_valid_corpus()
    test_interval_curvature_m_certificate_rejects_mutations()
    test_best_interval_curvature_m_certificate_dominates_uniform_corpus()
    test_refined_interval_curvature_m_certificate_monotone()
    test_optimal_midpoint_interval_curvature_m_certificate_audits_greedy()
    test_exact_count()
    print("\nAll CPMM Concavity Evidence tests passed.")
    print("Lean-proven:")
    print("  1. CPMM concavity param: m = 2*K*gamma^2/M^2 = 2*gamma*L/M  [gamma=1]")
    print("  2. CPMM window identity: sqrt(2*L/m) = sqrt(M)  [epsilon=0]")
    print("  3. Generic Lipschitz increment: f(a_A)-f(0) <= L*a_A")
    print("  3b. Stateful CPMM attack gain bound: gain <= L*a_A  [fee-free + with fee]")
    print("  3c. Donation/no-output exact optimizer: a_B=sqrt(M*(M+a_A))  [fee-free]")
    print("  3d. Fee-bearing donation/no-output optimizer: a_B=sqrt(M*(M+gamma*a_A))/gamma")
    print("  3e. Pool-parameter m certificate soundness from endpoint curvature bound")
    print("  3f. Curvature-floor bridge accepts externally supplied m floors")
    print("  3g. Interval curvature floor: T0(a)+T1(a) >= T0(hi)+T1(lo)")
    print("  3h. Symmetric exact curvature minimizer: H(a) >= H(D/2)")
    print("  3i. Normalized asymmetric stationary minimizer certificate")
    print("Empirical (NOT Lean-proven):")
    print("  4. Concavity bound falsified  [empirical regression guard]")
    print("  4b. Concavity bound fails for large trades  [empirical]")
    print("  5. Actual stateful gain decreases with M  [empirical]")
    print("  6. Min_out cap makes sacrifice infeasible  [empirical]")
    print("  7. Donation/no-output optimizer replay  [Lean PROVEN + empirical replay]")
    print("  7b. Fee-bearing donation/no-output optimizer replay  [Lean PROVEN + empirical replay]")
    print("  8. Donation optimizer falsified for filled-A gain semantics  [empirical]")
    print("  9. Tradeoff frontier characterized  [empirical]")
    print("  10. Pool-parameter m certificate checker replay  [Lean bridge + empirical]")
    print("  11. Exact curvature minimizer certificate replay  [research checker]")
    print("  12. Symmetric exact curvature minimizer replay  [Lean PROVEN + empirical replay]")
    print("  13. Stationary curvature certificate replay  [Lean bridge + exact rational checker]")
    print("  14. Exact curvature float-overflow domain rejection  [CBC boundary]")
    print("  15. Rational interval curvature certificate replay  [Lean bridge + exact rational checker]")
    print("  16. Best-cover interval certificate replay  [exact rational cover portfolio]")
    print("  17. Greedy interval-refinement certificate replay  [Lean monotonicity bridge]")
    print("  18. Bounded optimal midpoint-refinement audit  [exact DP replay]")
