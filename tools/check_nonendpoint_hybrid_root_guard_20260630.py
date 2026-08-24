#!/usr/bin/env python3
"""Replay an exact root-side guard for non-endpoint hybrid argmax radius."""

from __future__ import annotations

import argparse
import hashlib
import json
import random
import sys
from dataclasses import dataclass
from enum import Enum
from fractions import Fraction
from pathlib import Path
from typing import Mapping, TypedDict, cast

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from docs.research.discrete_argmax_proximity_test import (  # noqa: E402
    Pool,
    _curvature_module,
    tight_argmax_domain_hash,
)
from tools import check_tight_argmax_exact_interval_certificate_20260630 as exact  # noqa: E402

OUT_DIR = REPO_ROOT / "generated" / "nonendpoint_hybrid_root_guard_20260630"
REPORT_JSON = OUT_DIR / "report.json"
SCHEMA = "zenodex.nonendpoint_hybrid_root_guard.v1"
INTERVAL_M_CERTIFICATE_SCHEMA = "zenodex.cpmm_split_interval_m_certificate.v1"
STATIONARY_M_CERTIFICATE_SCHEMA = "zenodex.cpmm_split_stationary_m_certificate.v1"
M_SOURCE_INTERVAL_CERTIFICATE = "interval_curvature_certificate"
M_SOURCE_STATIONARY_CERTIFICATE = "stationary_curvature_certificate"
MAX_PACKET_BYTES = 96_000
MAX_RATIO_BITS = 1024
DEFAULT_BRACKET_STEPS = 24
RADIUS_SEARCH_STEPS = 72
FEE_CHOICES = (0, 30, 100, 300, 1000, 3000, 5000, 9000)
RATIO_KEYS = frozenset({"num", "den"})
BASE_KEYS = frozenset(
    {
        "schema",
        "research_only",
        "authority_effects",
        "domain_hash",
        "anchor",
        "argmax",
        "interval_lo",
        "interval_hi",
        "m",
        "cont_star_upper",
        "alpha_upper",
        "rho_upper",
        "pair_distance",
        "perturbation_advantage",
        "lipschitz_upper",
        "radius",
        "distance_upper",
        "prod_anchor",
        "prod_argmax",
        "bracket_steps",
        "radius_steps",
        "m_source",
        "m_certificate_schema",
        "m_certificate_sha256",
    }
)


class GuardReject(str, Enum):
    BAD_PACKET_TYPE = "bad_packet_type"
    BAD_JSON = "bad_json"
    DUPLICATE_KEY = "duplicate_key"
    NONCANONICAL_BYTES = "noncanonical_bytes"
    PACKET_TOO_LARGE = "packet_too_large"
    BAD_SCHEMA = "bad_schema"
    AUTHORITY_EFFECTS_PRESENT = "authority_effects_present"
    BAD_DOMAIN = "bad_domain"
    DOMAIN_HASH_MISMATCH = "domain_hash_mismatch"
    BAD_INDEX = "bad_index"
    BAD_RATIO = "bad_ratio"
    BAD_M_SOURCE = "bad_m_source"
    BAD_M_CERTIFICATE_REF = "bad_m_certificate_ref"
    BAD_M_CERTIFICATE_RESOLVER = "bad_m_certificate_resolver"
    M_CERTIFICATE_MISSING = "m_certificate_missing"
    M_CERTIFICATE_HASH_MISMATCH = "m_certificate_hash_mismatch"
    M_CERTIFICATE_REJECTED = "m_certificate_rejected"
    M_SOURCE_MISMATCH = "m_source_mismatch"
    BAD_INTERVAL = "bad_interval"
    DERIVATIVE_BRACKET_FAILED = "derivative_bracket_failed"
    STALE_CONT_UPPER = "stale_cont_upper"
    STALE_ALPHA = "stale_alpha"
    STALE_RHO = "stale_rho"
    STALE_LIPSCHITZ = "stale_lipschitz"
    STALE_RADIUS = "stale_radius"
    STALE_DISTANCE = "stale_distance"
    STALE_PROD = "stale_prod"
    ARGMAX_NOT_CANONICAL_MAX = "argmax_not_canonical_max"
    ARGMAX_NOT_DOMINATING_ANCHOR = "argmax_not_dominating_anchor"
    PAIR_DISTANCE_ZERO_WITH_POSITIVE_ADVANTAGE = "pair_distance_zero_with_positive_advantage"
    RADIUS_CERTIFICATE_FAILED = "radius_certificate_failed"
    ROOT_SIDE_FAILED = "root_side_failed"
    RADIUS_UNDERSTATES_DISTANCE = "radius_understates_distance"


@dataclass(frozen=True)
class DuplicateKey(ValueError):
    key: str


@dataclass(frozen=True)
class AcceptedGuard:
    m_source: str
    anchor: int
    argmax: int
    interval_lo: Fraction
    interval_hi: Fraction
    m: Fraction
    alpha_upper: Fraction
    rho_upper: Fraction
    lipschitz_upper: Fraction
    radius: Fraction
    distance_upper: Fraction
    prod_argmax: int
    m_certificate_sha256: str


@dataclass(frozen=True)
class RejectedGuard:
    rejects: tuple[GuardReject, ...]


GuardResult = AcceptedGuard | RejectedGuard


class RootMetrics(TypedDict):
    anchor: int
    argmax: int
    prod_anchor: int
    prod_argmax: int
    lo: Fraction
    hi: Fraction
    cont_upper: Fraction
    alpha: Fraction
    rho: Fraction
    pair_distance: Fraction
    perturbation_advantage: Fraction
    lipschitz: Fraction | None
    distance: Fraction
    radius: Fraction | None


def _canonical_json_bytes(payload: Mapping[str, object]) -> bytes:
    return json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")


def _reject_duplicate_keys(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise DuplicateKey(key)
        result[key] = value
    return result


def _fraction_json(value: Fraction) -> dict[str, int]:
    return {"num": value.numerator, "den": value.denominator}


def _parse_fraction(value: object, *, nonnegative: bool) -> Fraction | None:
    if not isinstance(value, dict) or set(value.keys()) != RATIO_KEYS:
        return None
    num = value.get("num")
    den = value.get("den")
    if isinstance(num, bool) or isinstance(den, bool):
        return None
    if not isinstance(num, int) or not isinstance(den, int):
        return None
    if den <= 0:
        return None
    if nonnegative and num < 0:
        return None
    if abs(num).bit_length() > MAX_RATIO_BITS or den.bit_length() > MAX_RATIO_BITS:
        return None
    reduced = Fraction(num, den)
    if reduced.numerator != num or reduced.denominator != den:
        return None
    return reduced


def _int_field(value: object, *, minimum: int, maximum: int) -> int | None:
    if type(value) is not int:
        return None
    if value < minimum or value > maximum:
        return None
    return value


def _is_sha256_hex(value: object) -> bool:
    if not isinstance(value, str) or len(value) != 64:
        return False
    return all(char in "0123456789abcdef" for char in value)


def _m_schema(source: str) -> str | None:
    if source == M_SOURCE_INTERVAL_CERTIFICATE:
        return INTERVAL_M_CERTIFICATE_SCHEMA
    if source == M_SOURCE_STATIONARY_CERTIFICATE:
        return STATIONARY_M_CERTIFICATE_SCHEMA
    return None


def _m_verifier_name(source: str) -> str | None:
    if source == M_SOURCE_INTERVAL_CERTIFICATE:
        return "verify_interval_curvature_m_certificate_bytes"
    if source == M_SOURCE_STATIONARY_CERTIFICATE:
        return "verify_stationary_curvature_m_certificate_bytes"
    return None


def _resolve_m_fraction(
    p0: Pool,
    p1: Pool,
    D: int,
    source: object,
    cert_hash: object,
    resolver: Mapping[str, bytes] | None,
) -> tuple[Fraction | None, tuple[GuardReject, ...]]:
    if not isinstance(source, str) or _m_schema(source) is None:
        return None, (GuardReject.BAD_M_SOURCE,)
    if not _is_sha256_hex(cert_hash):
        return None, (GuardReject.BAD_M_CERTIFICATE_REF,)
    cert_hash = cast(str, cert_hash)
    if resolver is not None:
        if type(resolver) is not dict:
            return None, (GuardReject.BAD_M_CERTIFICATE_RESOLVER,)
        try:
            resolver = dict(resolver)
        except RuntimeError:
            return None, (GuardReject.BAD_M_CERTIFICATE_RESOLVER,)
        if any(
            type(key) is not str or not _is_sha256_hex(key) or type(value) is not bytes
            for key, value in resolver.items()
        ):
            return None, (GuardReject.BAD_M_CERTIFICATE_RESOLVER,)
    if resolver is None or cert_hash not in resolver:
        return None, (GuardReject.M_CERTIFICATE_MISSING,)
    raw = resolver[cert_hash]
    if hashlib.sha256(raw).hexdigest() != cert_hash:
        return None, (GuardReject.M_CERTIFICATE_HASH_MISMATCH,)
    verifier_name = _m_verifier_name(source)
    if verifier_name is None:
        return None, (GuardReject.BAD_M_SOURCE,)
    result = getattr(_curvature_module(), verifier_name)(p0, p1, D, raw)
    if not result.accepted or result.m_fraction is None:
        return None, (GuardReject.M_CERTIFICATE_REJECTED,)
    m_fraction = result.m_fraction
    if not isinstance(m_fraction, Fraction):
        return None, (GuardReject.M_CERTIFICATE_REJECTED,)
    return m_fraction, ()


def _best_continuous_integer_anchor(p0: Pool, p1: Pool, D: int) -> int:
    best = 0
    best_value = exact._split_cont(p0, p1, D, Fraction(0))
    for candidate in range(1, D + 1):
        value = exact._split_cont(p0, p1, D, Fraction(candidate))
        if value > best_value:
            best = candidate
            best_value = value
    return best


def _distance_upper(index: int, lo: Fraction, hi: Fraction) -> Fraction:
    return max(abs(Fraction(index) - lo), abs(Fraction(index) - hi))


def _root_obligations_hold(
    m: Fraction,
    alpha: Fraction,
    rho: Fraction,
    lipschitz: Fraction,
    radius: Fraction,
    distance: Fraction,
) -> bool:
    return (
        radius >= 0
        and distance <= radius
        and lipschitz <= m * radius
        and alpha + lipschitz * (radius + rho) <= Fraction(1, 2) * m * radius * radius
    )


def _least_admissible_radius(
    m: Fraction,
    alpha: Fraction,
    rho: Fraction,
    lipschitz: Fraction,
    distance: Fraction,
    steps: int,
) -> Fraction:
    if m <= 0:
        raise ValueError("m must be positive")
    lo = Fraction(0)
    hi = max(Fraction(1), distance)
    while not _root_obligations_hold(m, alpha, rho, lipschitz, hi, distance):
        hi *= 2
    for _ in range(steps):
        mid = (lo + hi) / 2
        if _root_obligations_hold(m, alpha, rho, lipschitz, mid, distance):
            hi = mid
        else:
            lo = mid
    return hi


def _metrics(
    p0: Pool,
    p1: Pool,
    D: int,
    m: Fraction,
    bracket_steps: int,
    radius_steps: int,
) -> RootMetrics:
    anchor = _best_continuous_integer_anchor(p0, p1, D)
    argmax, prod_argmax = exact._canonical_prod_argmax(p0, p1, D)
    prod_anchor = exact._prod_split(p0, p1, D, anchor)
    lo, hi = exact._build_bracket(p0, p1, D, bracket_steps)
    cont_upper = exact._split_cont_upper_for_interval(p0, p1, D, lo, hi)
    cont_anchor = exact._split_cont(p0, p1, D, Fraction(anchor))
    cont_argmax = exact._split_cont(p0, p1, D, Fraction(argmax))
    alpha = cont_upper - cont_anchor
    rho = _distance_upper(anchor, lo, hi)
    pair_distance = abs(Fraction(argmax - anchor))
    perturbation_advantage = (
        (Fraction(prod_argmax) - cont_argmax)
        - (Fraction(prod_anchor) - cont_anchor)
    )
    if pair_distance == 0:
        if perturbation_advantage > 0:
            lipschitz = None
        else:
            lipschitz = Fraction(0)
    else:
        lipschitz = max(Fraction(0), perturbation_advantage / pair_distance)
    distance = _distance_upper(argmax, lo, hi)
    radius = None if lipschitz is None else _least_admissible_radius(
        m,
        alpha,
        rho,
        lipschitz,
        distance,
        radius_steps,
    )
    return {
        "anchor": anchor,
        "argmax": argmax,
        "prod_anchor": prod_anchor,
        "prod_argmax": prod_argmax,
        "lo": lo,
        "hi": hi,
        "cont_upper": cont_upper,
        "alpha": alpha,
        "rho": rho,
        "pair_distance": pair_distance,
        "perturbation_advantage": perturbation_advantage,
        "lipschitz": lipschitz,
        "distance": distance,
        "radius": radius,
    }


def _build_payload(
    p0: Pool,
    p1: Pool,
    D: int,
    source: str,
    m_raw: bytes,
    bracket_steps: int,
    radius_steps: int,
) -> dict[str, object]:
    m_hash = hashlib.sha256(m_raw).hexdigest()
    m, rejects = _resolve_m_fraction(p0, p1, D, source, m_hash, {m_hash: m_raw})
    if rejects or m is None:
        raise ValueError(f"m certificate rejected: {rejects}")
    values = _metrics(p0, p1, D, m, bracket_steps, radius_steps)
    if values["lipschitz"] is None or values["radius"] is None:
        raise ValueError("zero pair distance has positive perturbation advantage")
    return {
        "schema": SCHEMA,
        "research_only": True,
        "authority_effects": False,
        "domain_hash": tight_argmax_domain_hash(p0, p1, D),
        "anchor": values["anchor"],
        "argmax": values["argmax"],
        "interval_lo": _fraction_json(values["lo"]),
        "interval_hi": _fraction_json(values["hi"]),
        "m": _fraction_json(m),
        "cont_star_upper": _fraction_json(values["cont_upper"]),
        "alpha_upper": _fraction_json(values["alpha"]),
        "rho_upper": _fraction_json(values["rho"]),
        "pair_distance": _fraction_json(values["pair_distance"]),
        "perturbation_advantage": _fraction_json(values["perturbation_advantage"]),
        "lipschitz_upper": _fraction_json(values["lipschitz"]),
        "radius": _fraction_json(values["radius"]),
        "distance_upper": _fraction_json(values["distance"]),
        "prod_anchor": values["prod_anchor"],
        "prod_argmax": values["prod_argmax"],
        "bracket_steps": bracket_steps,
        "radius_steps": radius_steps,
        "m_source": source,
        "m_certificate_schema": _m_schema(source),
        "m_certificate_sha256": m_hash,
    }


def build_nonendpoint_hybrid_root_guard_certificate(
    p0: Pool,
    p1: Pool,
    D: int,
    source: str,
    m_certificate_raw: bytes,
    bracket_steps: int = DEFAULT_BRACKET_STEPS,
    radius_steps: int = RADIUS_SEARCH_STEPS,
) -> bytes:
    owned_domain = exact._owned_domain(p0, p1, D)
    if owned_domain is None:
        raise ValueError("domain outside non-endpoint hybrid root guard bounds")
    p0, p1, D = owned_domain
    if (
        type(bracket_steps) is not int
        or type(radius_steps) is not int
        or bracket_steps < 0
        or bracket_steps > 64
        or radius_steps < 0
        or radius_steps > 96
    ):
        raise ValueError("step count outside bounds")
    return _canonical_json_bytes(_build_payload(p0, p1, D, source, m_certificate_raw, bracket_steps, radius_steps))


def verify_nonendpoint_hybrid_root_guard_certificate_bytes(
    p0: Pool,
    p1: Pool,
    D: int,
    raw: bytes,
    m_certificate_resolver: Mapping[str, bytes] | None = None,
) -> GuardResult:
    if type(raw) is not bytes:
        return RejectedGuard((GuardReject.BAD_PACKET_TYPE,))
    if len(raw) > MAX_PACKET_BYTES:
        return RejectedGuard((GuardReject.PACKET_TOO_LARGE,))
    owned_domain = exact._owned_domain(p0, p1, D)
    if owned_domain is None:
        return RejectedGuard((GuardReject.BAD_DOMAIN,))
    p0, p1, D = owned_domain
    try:
        parsed = json.loads(raw.decode("utf-8"), object_pairs_hook=_reject_duplicate_keys)
    except DuplicateKey:
        return RejectedGuard((GuardReject.DUPLICATE_KEY,))
    except (UnicodeDecodeError, json.JSONDecodeError):
        return RejectedGuard((GuardReject.BAD_JSON,))
    if not isinstance(parsed, dict):
        return RejectedGuard((GuardReject.BAD_JSON,))
    if _canonical_json_bytes(parsed) != raw:
        return RejectedGuard((GuardReject.NONCANONICAL_BYTES,))

    cert: Mapping[str, object] = parsed
    rejects: list[GuardReject] = []
    if cert.get("schema") != SCHEMA or set(cert.keys()) != BASE_KEYS:
        rejects.append(GuardReject.BAD_SCHEMA)
    if cert.get("research_only") is not True or cert.get("authority_effects") is not False:
        rejects.append(GuardReject.AUTHORITY_EFFECTS_PRESENT)
    if cert.get("domain_hash") != tight_argmax_domain_hash(p0, p1, D):
        rejects.append(GuardReject.DOMAIN_HASH_MISMATCH)
    source = cert.get("m_source")
    schema = _m_schema(str(source)) if isinstance(source, str) else None
    if schema is None:
        rejects.append(GuardReject.BAD_M_SOURCE)
    elif cert.get("m_certificate_schema") != schema:
        rejects.append(GuardReject.BAD_M_CERTIFICATE_REF)
    cert_hash = cert.get("m_certificate_sha256")
    if not _is_sha256_hex(cert_hash):
        rejects.append(GuardReject.BAD_M_CERTIFICATE_REF)

    anchor = _int_field(cert.get("anchor"), minimum=0, maximum=D)
    argmax = _int_field(cert.get("argmax"), minimum=0, maximum=D)
    bracket_steps = _int_field(cert.get("bracket_steps"), minimum=0, maximum=64)
    radius_steps = _int_field(cert.get("radius_steps"), minimum=0, maximum=96)
    if anchor is None or argmax is None or bracket_steps is None or radius_steps is None:
        rejects.append(GuardReject.BAD_INDEX)
    max_production_value = (1 << exact.MAX_INT_BITS) - 1
    prod_anchor = _int_field(cert.get("prod_anchor"), minimum=0, maximum=max_production_value)
    prod_argmax = _int_field(cert.get("prod_argmax"), minimum=0, maximum=max_production_value)
    if prod_anchor is None or prod_argmax is None:
        rejects.append(GuardReject.STALE_PROD)

    ratios = {
        "interval_lo": _parse_fraction(cert.get("interval_lo"), nonnegative=True),
        "interval_hi": _parse_fraction(cert.get("interval_hi"), nonnegative=True),
        "m": _parse_fraction(cert.get("m"), nonnegative=True),
        "cont_star_upper": _parse_fraction(cert.get("cont_star_upper"), nonnegative=True),
        "alpha_upper": _parse_fraction(cert.get("alpha_upper"), nonnegative=True),
        "rho_upper": _parse_fraction(cert.get("rho_upper"), nonnegative=True),
        "pair_distance": _parse_fraction(cert.get("pair_distance"), nonnegative=True),
        "perturbation_advantage": _parse_fraction(cert.get("perturbation_advantage"), nonnegative=False),
        "lipschitz_upper": _parse_fraction(cert.get("lipschitz_upper"), nonnegative=True),
        "radius": _parse_fraction(cert.get("radius"), nonnegative=True),
        "distance_upper": _parse_fraction(cert.get("distance_upper"), nonnegative=True),
    }
    if any(value is None for value in ratios.values()):
        rejects.append(GuardReject.BAD_RATIO)
    if rejects:
        return RejectedGuard(tuple(dict.fromkeys(rejects)))

    source = cast(str, source)
    cert_hash = cast(str, cert_hash)
    m, source_rejects = _resolve_m_fraction(p0, p1, D, source, cert_hash, m_certificate_resolver)
    if source_rejects:
        return RejectedGuard(source_rejects)
    if m is None:
        return RejectedGuard((GuardReject.M_CERTIFICATE_REJECTED,))
    anchor = cast(int, anchor)
    argmax = cast(int, argmax)
    bracket_steps = cast(int, bracket_steps)
    radius_steps = cast(int, radius_steps)
    prod_anchor = cast(int, prod_anchor)
    prod_argmax = cast(int, prod_argmax)
    lo = cast(Fraction, ratios["interval_lo"])
    hi = cast(Fraction, ratios["interval_hi"])
    claimed_m = cast(Fraction, ratios["m"])
    cont_upper = cast(Fraction, ratios["cont_star_upper"])
    alpha = cast(Fraction, ratios["alpha_upper"])
    rho = cast(Fraction, ratios["rho_upper"])
    pair_distance = cast(Fraction, ratios["pair_distance"])
    perturbation_advantage = cast(Fraction, ratios["perturbation_advantage"])
    lipschitz = cast(Fraction, ratios["lipschitz_upper"])
    radius = cast(Fraction, ratios["radius"])
    distance = cast(Fraction, ratios["distance_upper"])

    if not (0 <= lo <= hi <= D):
        rejects.append(GuardReject.BAD_INTERVAL)
    elif not exact._valid_bracket(p0, p1, D, lo, hi):
        rejects.append(GuardReject.DERIVATIVE_BRACKET_FAILED)
    if claimed_m != m:
        rejects.append(GuardReject.M_SOURCE_MISMATCH)

    expected = _metrics(p0, p1, D, m, bracket_steps, radius_steps)
    if expected["lipschitz"] is None or expected["radius"] is None:
        rejects.append(GuardReject.PAIR_DISTANCE_ZERO_WITH_POSITIVE_ADVANTAGE)
    expected_argmax, expected_prod_argmax = exact._canonical_prod_argmax(p0, p1, D)
    expected_prod_anchor = exact._prod_split(p0, p1, D, anchor)
    if prod_anchor != expected_prod_anchor or prod_argmax != exact._prod_split(p0, p1, D, argmax):
        rejects.append(GuardReject.STALE_PROD)
    if argmax != expected_argmax or prod_argmax != expected_prod_argmax:
        rejects.append(GuardReject.ARGMAX_NOT_CANONICAL_MAX)
    if expected_prod_anchor > expected_prod_argmax:
        rejects.append(GuardReject.ARGMAX_NOT_DOMINATING_ANCHOR)

    comparisons = (
        (expected["anchor"], anchor, GuardReject.BAD_INDEX),
        (expected["argmax"], argmax, GuardReject.BAD_INDEX),
        (expected["lo"], lo, GuardReject.BAD_INTERVAL),
        (expected["hi"], hi, GuardReject.BAD_INTERVAL),
        (expected["cont_upper"], cont_upper, GuardReject.STALE_CONT_UPPER),
        (expected["alpha"], alpha, GuardReject.STALE_ALPHA),
        (expected["rho"], rho, GuardReject.STALE_RHO),
        (expected["pair_distance"], pair_distance, GuardReject.STALE_LIPSCHITZ),
        (expected["perturbation_advantage"], perturbation_advantage, GuardReject.STALE_LIPSCHITZ),
        (expected["lipschitz"], lipschitz, GuardReject.STALE_LIPSCHITZ),
        (expected["radius"], radius, GuardReject.STALE_RADIUS),
        (expected["distance"], distance, GuardReject.STALE_DISTANCE),
    )
    for recomputed, claimed, reject in comparisons:
        if recomputed != claimed:
            rejects.append(reject)

    if not _root_obligations_hold(m, alpha, rho, lipschitz, radius, distance):
        if lipschitz > m * radius:
            rejects.append(GuardReject.ROOT_SIDE_FAILED)
        if alpha + lipschitz * (radius + rho) > Fraction(1, 2) * m * radius * radius:
            rejects.append(GuardReject.RADIUS_CERTIFICATE_FAILED)
        if distance > radius:
            rejects.append(GuardReject.RADIUS_UNDERSTATES_DISTANCE)

    unique = tuple(dict.fromkeys(rejects))
    if unique:
        return RejectedGuard(unique)
    return AcceptedGuard(
        m_source=source,
        anchor=anchor,
        argmax=argmax,
        interval_lo=lo,
        interval_hi=hi,
        m=m,
        alpha_upper=alpha,
        rho_upper=rho,
        lipschitz_upper=lipschitz,
        radius=radius,
        distance_upper=distance,
        prod_argmax=expected_prod_argmax,
        m_certificate_sha256=cert_hash,
    )


def _decimal(value: Fraction) -> float:
    return float(value.numerator) / float(value.denominator)


def _accepted_json(result: AcceptedGuard, endpoint_radius: Fraction | None = None) -> dict[str, object]:
    row: dict[str, object] = {
        "m_source": result.m_source,
        "anchor": result.anchor,
        "argmax": result.argmax,
        "interval_lo": _decimal(result.interval_lo),
        "interval_hi": _decimal(result.interval_hi),
        "interval_width": _decimal(result.interval_hi - result.interval_lo),
        "m": _decimal(result.m),
        "alpha_upper": _decimal(result.alpha_upper),
        "rho_upper": _decimal(result.rho_upper),
        "lipschitz_upper": _decimal(result.lipschitz_upper),
        "radius": _decimal(result.radius),
        "distance_upper": _decimal(result.distance_upper),
        "distance_over_radius": _decimal(result.distance_upper / result.radius) if result.radius > 0 else None,
    }
    if endpoint_radius is not None:
        row["endpoint_radius"] = _decimal(endpoint_radius)
        row["endpoint_over_source_radius"] = _decimal(endpoint_radius / result.radius)
    return row


def _endpoint_radius_for_same_surface(p0: Pool, p1: Pool, D: int, bracket_steps: int, radius_steps: int) -> Fraction:
    values = _metrics(p0, p1, D, exact._endpoint_m(p0, p1, D), bracket_steps, radius_steps)
    radius = values["radius"]
    if radius is None:
        raise ValueError("endpoint surface has positive advantage at zero pair distance")
    if not isinstance(radius, Fraction):
        raise ValueError("generated endpoint radius must be exact")
    return radius


def _sample_domain(rng: random.Random) -> tuple[Pool, Pool, int]:
    return (
        Pool(rng.randint(100, 20_000), rng.randint(100, 80_000), rng.choice(FEE_CHOICES)),
        Pool(rng.randint(100, 20_000), rng.randint(100, 80_000), rng.choice(FEE_CHOICES)),
        rng.randint(10, 250),
    )


def _build_interval_m(p0: Pool, p1: Pool, D: int) -> bytes:
    return _curvature_module().build_refined_interval_curvature_m_certificate(p0, p1, D, 16, 64)


def _stationary_domains(count: int) -> list[tuple[Pool, Pool, int, bytes]]:
    rng = random.Random(20261002)
    curvature = _curvature_module()
    construct = curvature._construct_fee_free_stationary_case
    build_stationary = curvature.build_stationary_curvature_m_certificate
    domains = []
    for _ in range(count):
        D = rng.randint(5, 200)
        minimizer = rng.randint(1, D - 1)
        if 2 * minimizer == D:
            minimizer = 1 if minimizer != 1 else D - 1
        p0, p1, D, minimizer_a = construct(rng.randint(10, 500), rng.randint(10, 500), D, minimizer)
        domains.append((p0, p1, D, build_stationary(p0, p1, D, minimizer_a)))
    return domains


def corpus_replay(interval_count: int = 80, stationary_count: int = 80) -> dict[str, object]:
    rng = random.Random(20261001)
    rows = []
    accepted = 0
    shrink_count = 0
    max_shrink = Fraction(0)
    max_distance_ratio = Fraction(0)

    interval_domains = [(*_sample_domain(rng), None) for _ in range(interval_count)]
    stationary_domains = _stationary_domains(stationary_count)
    all_domains: list[tuple[str, Pool, Pool, int, bytes | None]] = [
        (M_SOURCE_INTERVAL_CERTIFICATE, p0, p1, D, raw)
        for p0, p1, D, raw in interval_domains
    ] + [
        (M_SOURCE_STATIONARY_CERTIFICATE, p0, p1, D, raw)
        for p0, p1, D, raw in stationary_domains
    ]

    for source, p0, p1, D, raw in all_domains:
        m_raw = _build_interval_m(p0, p1, D) if raw is None else raw
        m_hash = hashlib.sha256(m_raw).hexdigest()
        packet = build_nonendpoint_hybrid_root_guard_certificate(p0, p1, D, source, m_raw)
        result = verify_nonendpoint_hybrid_root_guard_certificate_bytes(p0, p1, D, packet, {m_hash: m_raw})
        if not isinstance(result, AcceptedGuard):
            rows.append({"source": source, "accepted": False, "rejects": [reject.value for reject in result.rejects]})
            continue
        endpoint_radius = _endpoint_radius_for_same_surface(p0, p1, D, DEFAULT_BRACKET_STEPS, RADIUS_SEARCH_STEPS)
        accepted += 1
        shrink = endpoint_radius / result.radius
        distance_ratio = result.distance_upper / result.radius if result.radius > 0 else Fraction(0)
        if shrink > 1:
            shrink_count += 1
        max_shrink = max(max_shrink, shrink)
        max_distance_ratio = max(max_distance_ratio, distance_ratio)
        rows.append({
            "source": source,
            "accepted": True,
            "metrics": _accepted_json(result, endpoint_radius),
        })

    return {
        "ok": accepted == len(all_domains) and shrink_count > 0 and max_distance_ratio <= 1,
        "case_count": len(all_domains),
        "interval_count": interval_count,
        "stationary_count": stationary_count,
        "accepted_count": accepted,
        "shrink_count": shrink_count,
        "max_endpoint_over_source_radius": _decimal(max_shrink),
        "max_distance_over_radius": _decimal(max_distance_ratio),
        "examples": rows[:5],
    }


def unsafe_fixture_replay() -> dict[str, object]:
    curvature = _curvature_module()
    construct = curvature._construct_fee_free_stationary_case
    build_stationary = curvature.build_stationary_curvature_m_certificate
    p0, p1, D, minimizer = construct(315, 351, 126, 83)
    m_raw = build_stationary(p0, p1, D, minimizer)
    m_hash = hashlib.sha256(m_raw).hexdigest()
    packet = build_nonendpoint_hybrid_root_guard_certificate(
        p0,
        p1,
        D,
        M_SOURCE_STATIONARY_CERTIFICATE,
        m_raw,
    )
    result = verify_nonendpoint_hybrid_root_guard_certificate_bytes(p0, p1, D, packet, {m_hash: m_raw})
    if not isinstance(result, AcceptedGuard):
        return {"ok": False, "rejects": [reject.value for reject in result.rejects]}
    endpoint_radius = _endpoint_radius_for_same_surface(p0, p1, D, DEFAULT_BRACKET_STEPS, RADIUS_SEARCH_STEPS)
    return {
        "ok": result.distance_upper <= result.radius,
        "failure_family_repaired": "stationary_m_hybrid_under_radius",
        "accepted": _accepted_json(result, endpoint_radius),
    }


def negative_replay() -> dict[str, object]:
    p0 = Pool(1000, 1000, 0)
    p1 = Pool(1000, 1000, 0)
    D = 100
    m_raw = _build_interval_m(p0, p1, D)
    m_hash = hashlib.sha256(m_raw).hexdigest()
    raw = build_nonendpoint_hybrid_root_guard_certificate(p0, p1, D, M_SOURCE_INTERVAL_CERTIFICATE, m_raw)
    base = json.loads(raw.decode("utf-8"))
    if not isinstance(base, dict):
        raise ValueError("generated root guard must decode to an object")
    mutations: list[tuple[str, bytes, GuardReject, Mapping[str, bytes] | None]] = [
        ("duplicate_key", b'{"schema":"x","schema":"x"}', GuardReject.DUPLICATE_KEY, {m_hash: m_raw}),
        ("noncanonical", json.dumps(base, indent=2, sort_keys=True).encode("utf-8"), GuardReject.NONCANONICAL_BYTES, {m_hash: m_raw}),
        ("authority", _canonical_json_bytes(dict(base, authority_effects=True)), GuardReject.AUTHORITY_EFFECTS_PRESENT, {m_hash: m_raw}),
        ("bad_source", _canonical_json_bytes(dict(base, m_source="endpoint_lower_bound")), GuardReject.BAD_M_SOURCE, {m_hash: m_raw}),
        ("missing_resolver", raw, GuardReject.M_CERTIFICATE_MISSING, None),
        ("tampered_resolver", raw, GuardReject.M_CERTIFICATE_HASH_MISMATCH, {m_hash: m_raw + b"\\n"}),
        ("bad_bracket", _canonical_json_bytes(dict(base, interval_lo={"num": 0, "den": 1}, interval_hi={"num": 0, "den": 1})), GuardReject.DERIVATIVE_BRACKET_FAILED, {m_hash: m_raw}),
        ("stale_alpha", _canonical_json_bytes(dict(base, alpha_upper={"num": 0, "den": 1})), GuardReject.STALE_ALPHA, {m_hash: m_raw}),
        ("stale_radius", _canonical_json_bytes(dict(base, radius={"num": 1, "den": 1})), GuardReject.STALE_RADIUS, {m_hash: m_raw}),
        ("understated_distance", _canonical_json_bytes(dict(base, distance_upper={"num": 0, "den": 1})), GuardReject.STALE_DISTANCE, {m_hash: m_raw}),
        ("nonmax_argmax", _canonical_json_bytes(dict(base, argmax=0, prod_argmax=exact._prod_split(p0, p1, D, 0))), GuardReject.ARGMAX_NOT_CANONICAL_MAX, {m_hash: m_raw}),
    ]
    rows = []
    for mutation_id, mutated, expected, resolver in mutations:
        result = verify_nonendpoint_hybrid_root_guard_certificate_bytes(p0, p1, D, mutated, resolver)
        rejects = result.rejects if isinstance(result, RejectedGuard) else ()
        rows.append({
            "mutation_id": mutation_id,
            "expected_reject": expected.value,
            "rejects": [reject.value for reject in rejects],
            "ok": expected in rejects,
        })
    return {
        "ok": all(row["ok"] for row in rows),
        "case_count": len(rows),
        "cases": rows,
    }


def build_report() -> dict[str, object]:
    corpus = corpus_replay()
    unsafe = unsafe_fixture_replay()
    negative = negative_replay()
    ok = corpus["ok"] is True and unsafe["ok"] is True and negative["ok"] is True
    return {
        "schema": "zenodex.nonendpoint_hybrid_root_guard_report.v1",
        "date": "2026-06-30",
        "ok": ok,
        "claim": (
            "A non-endpoint hybrid radius can be admitted as a separate exact "
            "root-side certificate: bracket b*, upper-bound alpha and rho with "
            "rationals, compute pairwise perturbation at integer points exactly, "
            "and accept only when the recomputed radius contains the whole "
            "argmax-to-bracket distance."
        ),
        "world_model": (
            "This is a candidate research surface for interval and stationary m "
            "sources. It does not change the main tight-argmax verifier's current "
            "fail-closed ban on non-endpoint hybrid packets."
        ),
        "invariants": [
            "m source is interval or stationary and is resolved by SHA-256 before use",
            "the derivative bracket contains the continuous maximizer",
            "alpha, rho, pairwise perturbation advantage, Lipschitz budget, and radius are exact rationals",
            "accepted certificates satisfy alpha + L*(R+rho) <= (m/2)*R^2",
            "accepted certificates satisfy L <= m*R",
            "accepted certificates satisfy distance_upper <= R",
        ],
        "invalid_states": [
            "endpoint source submitted to this non-endpoint guard",
            "missing or tampered m certificate bytes",
            "stale bracket, alpha, rho, Lipschitz, radius, production value, or distance fields",
            "zero pair distance with positive perturbation advantage",
            "research certificate presented as routing, settlement, or consensus authority",
        ],
        "corpus": corpus,
        "unsafe_fixture": unsafe,
        "negative_replay": negative,
        "lean_bridge": [
            "lean-mathlib/Proofs/DiscreteArgmaxProximity.lean::abstract_anchor_lipschitz_perturbed_argmax_distance",
            "lean-mathlib/Proofs/CeilingFeeRounding.lean::cpmm_prod_anchor_lipschitz_argmax_distance",
        ],
        "non_claims": [
            "This is a research checker and does not alter production routing, settlement, or consensus behavior.",
            "The main verifier still rejects non-endpoint hybrid packets unless this exact guard is explicitly integrated later.",
            "The corpus is bounded replay, not a theorem over every CPMM domain.",
            "The rational bracket upper bound is conservative and can make the radius much larger near flat integer optima.",
        ],
        "replay_command": "python3 tools/check_nonendpoint_hybrid_root_guard_20260630.py",
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-json", type=Path, default=REPORT_JSON)
    args = parser.parse_args(argv)
    report = build_report()
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
