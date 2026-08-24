#!/usr/bin/env python3
"""Replay an exact rational interval certificate for tight-argmax proximity."""

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
from typing import Mapping, cast

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from docs.research.discrete_argmax_proximity_test import (  # noqa: E402
    Pool,
    _curvature_module,
    tight_argmax_domain_hash,
)

OUT_DIR = REPO_ROOT / "generated" / "tight_argmax_exact_interval_certificate_20260630"
REPORT_JSON = OUT_DIR / "report.json"
SCHEMA = "zenodex.tight_argmax_exact_interval_certificate.v2"
INTERVAL_M_CERTIFICATE_SCHEMA = "zenodex.cpmm_split_interval_m_certificate.v1"
M_SOURCE_ENDPOINT = "endpoint_lower_bound"
M_SOURCE_INTERVAL_CERTIFICATE = "interval_curvature_certificate"
MAX_PACKET_BYTES = 64_000
MAX_D = 4096
MAX_INT_BITS = 256
MAX_RATIO_BITS = 768
DEFAULT_STEPS = 24
FEE_CHOICES = (0, 30, 100, 300, 1000, 3000, 5000, 9000)
BASE_ROOT_KEYS = frozenset(
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
        "tau_upper",
        "radius_sq",
        "distance_sq_upper",
        "prod_anchor",
        "prod_argmax",
        "interval_steps",
        "m_source",
    }
)
ENDPOINT_ROOT_KEYS = BASE_ROOT_KEYS
INTERVAL_ROOT_KEYS = BASE_ROOT_KEYS | frozenset({"m_certificate_schema", "m_certificate_sha256"})
RATIO_KEYS = frozenset({"num", "den"})


class ExactReject(str, Enum):
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
    STALE_M = "stale_m"
    STALE_CONT_UPPER = "stale_cont_upper"
    STALE_TAU = "stale_tau"
    STALE_RADIUS = "stale_radius"
    STALE_DISTANCE = "stale_distance"
    STALE_PROD = "stale_prod"
    ARGMAX_NOT_CANONICAL_MAX = "argmax_not_canonical_max"
    ARGMAX_NOT_DOMINATING_ANCHOR = "argmax_not_dominating_anchor"
    RADIUS_UNDERSTATES_DISTANCE = "radius_understates_distance"


@dataclass(frozen=True)
class DuplicateKey(ValueError):
    key: str


@dataclass(frozen=True)
class AcceptedExactInterval:
    anchor: int
    argmax: int
    interval_lo: Fraction
    interval_hi: Fraction
    m: Fraction
    cont_star_upper: Fraction
    tau_upper: Fraction
    radius_sq: Fraction
    distance_sq_upper: Fraction
    prod_argmax: int
    m_source: str
    m_certificate_sha256: str | None = None


@dataclass(frozen=True)
class RejectedExactInterval:
    rejects: tuple[ExactReject, ...]


ExactResult = AcceptedExactInterval | RejectedExactInterval


def _canonical_json_bytes(payload: Mapping[str, object]) -> bytes:
    return json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")


def _reject_duplicate_keys(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise DuplicateKey(key)
        result[key] = value
    return result


def _int_field(value: object, *, minimum: int, maximum: int) -> int | None:
    if type(value) is not int:
        return None
    if value < minimum or value > maximum:
        return None
    if value.bit_length() > MAX_INT_BITS:
        return None
    return value


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


def _is_sha256_hex(value: object) -> bool:
    if not isinstance(value, str) or len(value) != 64:
        return False
    return all(char in "0123456789abcdef" for char in value)


def _expected_keys_for_source(source: object) -> frozenset[str] | None:
    if source == M_SOURCE_ENDPOINT:
        return ENDPOINT_ROOT_KEYS
    if source == M_SOURCE_INTERVAL_CERTIFICATE:
        return INTERVAL_ROOT_KEYS
    return None


def _owned_pool(value: object) -> Pool | None:
    try:
        reserve_in = value.reserve_in  # type: ignore[attr-defined]
        reserve_out = value.reserve_out  # type: ignore[attr-defined]
        fee_bps = value.fee_bps  # type: ignore[attr-defined]
    except Exception:
        return None
    if (
        type(reserve_in) is not int
        or type(reserve_out) is not int
        or type(fee_bps) is not int
        or reserve_in < 1
        or reserve_out < 1
        or not 0 <= fee_bps < 10_000
        or reserve_in.bit_length() > MAX_INT_BITS
        or reserve_out.bit_length() > MAX_INT_BITS
    ):
        return None
    return Pool(reserve_in=reserve_in, reserve_out=reserve_out, fee_bps=fee_bps)


def _owned_domain(p0: object, p1: object, D: object) -> tuple[Pool, Pool, int] | None:
    if type(D) is not int or not 1 <= D <= MAX_D:
        return None
    owned_p0 = _owned_pool(p0)
    owned_p1 = _owned_pool(p1)
    if owned_p0 is None or owned_p1 is None:
        return None
    return owned_p0, owned_p1, D


def _domain_valid(p0: Pool, p1: Pool, D: int) -> bool:
    return _owned_domain(p0, p1, D) is not None


def _gamma(pool: Pool) -> Fraction:
    return Fraction(10_000 - pool.fee_bps, 10_000)


def _cont_pool(pool: Pool, amount: Fraction) -> Fraction:
    if amount <= 0:
        return Fraction(0)
    net = _gamma(pool) * amount
    if net <= 0:
        return Fraction(0)
    return Fraction(pool.reserve_out) * net / (Fraction(pool.reserve_in) + net)


def _split_cont(p0: Pool, p1: Pool, D: int, a: Fraction) -> Fraction:
    return _cont_pool(p0, a) + _cont_pool(p1, Fraction(D) - a)


def _split_cont_upper_for_interval(p0: Pool, p1: Pool, D: int, lo: Fraction, hi: Fraction) -> Fraction:
    return _cont_pool(p0, hi) + _cont_pool(p1, Fraction(D) - lo)


def _derivative(p0: Pool, p1: Pool, D: int, a: Fraction) -> Fraction:
    c0 = _gamma(p0)
    c1 = _gamma(p1)
    term0 = Fraction(pool_term_num(p0), 1) * c0 / (Fraction(p0.reserve_in) + c0 * a) ** 2
    term1 = Fraction(pool_term_num(p1), 1) * c1 / (Fraction(p1.reserve_in) + c1 * (Fraction(D) - a)) ** 2
    return term0 - term1


def pool_term_num(pool: Pool) -> int:
    return pool.reserve_out * pool.reserve_in


def _endpoint_m(p0: Pool, p1: Pool, D: int) -> Fraction:
    d = Fraction(D)
    c0 = _gamma(p0)
    c1 = _gamma(p1)
    term0 = 2 * Fraction(p0.reserve_out) * c0**2 * Fraction(p0.reserve_in)
    term0 /= (Fraction(p0.reserve_in) + c0 * d) ** 3
    term1 = 2 * Fraction(p1.reserve_out) * c1**2 * Fraction(p1.reserve_in)
    term1 /= (Fraction(p1.reserve_in) + c1 * d) ** 3
    return term0 + term1


def _interval_certificate_m_fraction(
    p0: Pool,
    p1: Pool,
    D: int,
    interval_m_certificate_raw: bytes,
) -> Fraction | None:
    if type(interval_m_certificate_raw) is not bytes:
        return None
    curvature = _curvature_module()
    verifier = curvature.verify_interval_curvature_m_certificate_bytes
    result = verifier(p0, p1, D, interval_m_certificate_raw)
    if not result.accepted or result.m_fraction is None:
        return None
    value = result.m_fraction
    return value if isinstance(value, Fraction) else None


def _resolve_m_source(
    p0: Pool,
    p1: Pool,
    D: int,
    cert: Mapping[str, object],
    m_certificate_resolver: Mapping[str, bytes] | None,
) -> tuple[Fraction | None, str | None, tuple[ExactReject, ...]]:
    source = cert.get("m_source")
    expected_keys = _expected_keys_for_source(source)
    if expected_keys is None:
        return None, None, (ExactReject.BAD_M_SOURCE,)
    if set(cert.keys()) != expected_keys:
        return None, None, (ExactReject.BAD_SCHEMA,)
    if source == M_SOURCE_ENDPOINT:
        return _endpoint_m(p0, p1, D), None, ()

    rejects: list[ExactReject] = []
    if cert.get("m_certificate_schema") != INTERVAL_M_CERTIFICATE_SCHEMA:
        rejects.append(ExactReject.BAD_M_CERTIFICATE_REF)
    cert_hash = cert.get("m_certificate_sha256")
    if not _is_sha256_hex(cert_hash):
        rejects.append(ExactReject.BAD_M_CERTIFICATE_REF)
    if rejects:
        return None, None, tuple(dict.fromkeys(rejects))

    cert_hash = cast(str, cert_hash)
    if m_certificate_resolver is not None:
        if type(m_certificate_resolver) is not dict:
            return None, cert_hash, (ExactReject.BAD_M_CERTIFICATE_RESOLVER,)
        try:
            m_certificate_resolver = dict(m_certificate_resolver)
        except RuntimeError:
            return None, cert_hash, (ExactReject.BAD_M_CERTIFICATE_RESOLVER,)
        if any(
            type(key) is not str or not _is_sha256_hex(key) or type(value) is not bytes
            for key, value in m_certificate_resolver.items()
        ):
            return None, cert_hash, (ExactReject.BAD_M_CERTIFICATE_RESOLVER,)
    if m_certificate_resolver is None or cert_hash not in m_certificate_resolver:
        return None, cert_hash, (ExactReject.M_CERTIFICATE_MISSING,)
    raw = m_certificate_resolver[cert_hash]
    if hashlib.sha256(raw).hexdigest() != cert_hash:
        return None, cert_hash, (ExactReject.M_CERTIFICATE_HASH_MISMATCH,)
    m_fraction = _interval_certificate_m_fraction(p0, p1, D, raw)
    if m_fraction is None:
        return None, cert_hash, (ExactReject.M_CERTIFICATE_REJECTED,)
    return m_fraction, cert_hash, ()


def _prod_pool(pool: Pool, amount: int) -> int:
    if amount <= 0:
        return 0
    fee = (amount * pool.fee_bps + 9999) // 10000
    net = amount - fee
    if net <= 0:
        return 0
    return (pool.reserve_out * net) // (pool.reserve_in + net)


def _prod_split(p0: Pool, p1: Pool, D: int, a: int) -> int:
    return _prod_pool(p0, a) + _prod_pool(p1, D - a)


def _canonical_prod_argmax(p0: Pool, p1: Pool, D: int) -> tuple[int, int]:
    best_a = 0
    best_out = _prod_split(p0, p1, D, 0)
    for a in range(1, D + 1):
        out = _prod_split(p0, p1, D, a)
        if out > best_out:
            best_a = a
            best_out = out
    return best_a, best_out


def _valid_bracket(p0: Pool, p1: Pool, D: int, lo: Fraction, hi: Fraction) -> bool:
    if lo == 0 and hi == 0:
        return _derivative(p0, p1, D, Fraction(0)) <= 0
    if lo == D and hi == D:
        return _derivative(p0, p1, D, Fraction(D)) >= 0
    return _derivative(p0, p1, D, lo) >= 0 and _derivative(p0, p1, D, hi) <= 0


def _build_bracket(p0: Pool, p1: Pool, D: int, steps: int) -> tuple[Fraction, Fraction]:
    left = Fraction(0)
    right = Fraction(D)
    if _derivative(p0, p1, D, left) <= 0:
        return left, left
    if _derivative(p0, p1, D, right) >= 0:
        return right, right
    lo = left
    hi = right
    for _ in range(steps):
        mid = (lo + hi) / 2
        if _derivative(p0, p1, D, mid) >= 0:
            lo = mid
        else:
            hi = mid
    return lo, hi


def _distance_sq_upper(argmax: int, lo: Fraction, hi: Fraction) -> Fraction:
    left = (Fraction(argmax) - lo) ** 2
    right = (Fraction(argmax) - hi) ** 2
    return max(left, right)


def _build_payload(
    p0: Pool,
    p1: Pool,
    D: int,
    steps: int,
    m: Fraction,
    m_source: str,
    m_certificate_sha256: str | None = None,
) -> dict[str, object]:
    argmax, prod_argmax = _canonical_prod_argmax(p0, p1, D)
    lo, hi = _build_bracket(p0, p1, D, steps)
    cont_upper = _split_cont_upper_for_interval(p0, p1, D, lo, hi)
    tau = cont_upper - Fraction(prod_argmax)
    radius_sq = 2 * tau / m
    distance_sq = _distance_sq_upper(argmax, lo, hi)
    payload: dict[str, object] = {
        "schema": SCHEMA,
        "research_only": True,
        "authority_effects": False,
        "domain_hash": tight_argmax_domain_hash(p0, p1, D),
        "anchor": argmax,
        "argmax": argmax,
        "interval_lo": _fraction_json(lo),
        "interval_hi": _fraction_json(hi),
        "m": _fraction_json(m),
        "cont_star_upper": _fraction_json(cont_upper),
        "tau_upper": _fraction_json(tau),
        "radius_sq": _fraction_json(radius_sq),
        "distance_sq_upper": _fraction_json(distance_sq),
        "prod_anchor": prod_argmax,
        "prod_argmax": prod_argmax,
        "interval_steps": steps,
        "m_source": m_source,
    }
    if m_certificate_sha256 is not None:
        payload["m_certificate_schema"] = INTERVAL_M_CERTIFICATE_SCHEMA
        payload["m_certificate_sha256"] = m_certificate_sha256
    return payload


def build_exact_interval_certificate(p0: Pool, p1: Pool, D: int, steps: int = DEFAULT_STEPS) -> bytes:
    owned_domain = _owned_domain(p0, p1, D)
    if owned_domain is None:
        raise ValueError("domain outside exact interval certificate bounds")
    p0, p1, D = owned_domain
    if type(steps) is not int or steps < 0 or steps > 64:
        raise ValueError("interval steps outside bounds")
    return _canonical_json_bytes(_build_payload(p0, p1, D, steps, _endpoint_m(p0, p1, D), M_SOURCE_ENDPOINT))


def build_interval_m_backed_exact_interval_certificate(
    p0: Pool,
    p1: Pool,
    D: int,
    interval_m_certificate_raw: bytes,
    steps: int = DEFAULT_STEPS,
) -> bytes:
    owned_domain = _owned_domain(p0, p1, D)
    if owned_domain is None:
        raise ValueError("domain outside exact interval certificate bounds")
    p0, p1, D = owned_domain
    if type(steps) is not int or steps < 0 or steps > 64:
        raise ValueError("interval steps outside bounds")
    m = _interval_certificate_m_fraction(p0, p1, D, interval_m_certificate_raw)
    if m is None:
        raise ValueError("interval m certificate rejected")
    cert_hash = hashlib.sha256(interval_m_certificate_raw).hexdigest()
    return _canonical_json_bytes(
        _build_payload(
            p0,
            p1,
            D,
            steps,
            m,
            M_SOURCE_INTERVAL_CERTIFICATE,
            cert_hash,
        )
    )


def verify_exact_interval_certificate_bytes(
    p0: Pool,
    p1: Pool,
    D: int,
    raw: bytes,
    m_certificate_resolver: Mapping[str, bytes] | None = None,
) -> ExactResult:
    if type(raw) is not bytes:
        return RejectedExactInterval((ExactReject.BAD_PACKET_TYPE,))
    if len(raw) > MAX_PACKET_BYTES:
        return RejectedExactInterval((ExactReject.PACKET_TOO_LARGE,))
    owned_domain = _owned_domain(p0, p1, D)
    if owned_domain is None:
        return RejectedExactInterval((ExactReject.BAD_DOMAIN,))
    p0, p1, D = owned_domain
    try:
        parsed = json.loads(raw.decode("utf-8"), object_pairs_hook=_reject_duplicate_keys)
    except DuplicateKey:
        return RejectedExactInterval((ExactReject.DUPLICATE_KEY,))
    except (UnicodeDecodeError, json.JSONDecodeError):
        return RejectedExactInterval((ExactReject.BAD_JSON,))
    if not isinstance(parsed, dict):
        return RejectedExactInterval((ExactReject.BAD_JSON,))
    if _canonical_json_bytes(parsed) != raw:
        return RejectedExactInterval((ExactReject.NONCANONICAL_BYTES,))

    cert: Mapping[str, object] = parsed
    rejects: list[ExactReject] = []
    if cert.get("schema") != SCHEMA:
        rejects.append(ExactReject.BAD_SCHEMA)
    m_source = cert.get("m_source")
    expected_keys = _expected_keys_for_source(m_source)
    if expected_keys is None:
        rejects.append(ExactReject.BAD_M_SOURCE)
    elif set(cert.keys()) != expected_keys:
        rejects.append(ExactReject.BAD_SCHEMA)
    if cert.get("research_only") is not True or cert.get("authority_effects") is not False:
        rejects.append(ExactReject.AUTHORITY_EFFECTS_PRESENT)
    if cert.get("domain_hash") != tight_argmax_domain_hash(p0, p1, D):
        rejects.append(ExactReject.DOMAIN_HASH_MISMATCH)

    anchor = _int_field(cert.get("anchor"), minimum=0, maximum=D)
    argmax = _int_field(cert.get("argmax"), minimum=0, maximum=D)
    steps = _int_field(cert.get("interval_steps"), minimum=0, maximum=64)
    if anchor is None or argmax is None or steps is None:
        rejects.append(ExactReject.BAD_INDEX)
    max_production_value = (1 << MAX_INT_BITS) - 1
    prod_anchor = _int_field(cert.get("prod_anchor"), minimum=0, maximum=max_production_value)
    prod_argmax = _int_field(cert.get("prod_argmax"), minimum=0, maximum=max_production_value)
    if prod_anchor is None or prod_argmax is None:
        rejects.append(ExactReject.STALE_PROD)

    ratios = {
        "interval_lo": _parse_fraction(cert.get("interval_lo"), nonnegative=True),
        "interval_hi": _parse_fraction(cert.get("interval_hi"), nonnegative=True),
        "m": _parse_fraction(cert.get("m"), nonnegative=True),
        "cont_star_upper": _parse_fraction(cert.get("cont_star_upper"), nonnegative=True),
        "tau_upper": _parse_fraction(cert.get("tau_upper"), nonnegative=True),
        "radius_sq": _parse_fraction(cert.get("radius_sq"), nonnegative=True),
        "distance_sq_upper": _parse_fraction(cert.get("distance_sq_upper"), nonnegative=True),
    }
    if any(value is None for value in ratios.values()):
        rejects.append(ExactReject.BAD_RATIO)
    if rejects:
        return RejectedExactInterval(tuple(dict.fromkeys(rejects)))

    anchor = cast(int, anchor)
    argmax = cast(int, argmax)
    prod_anchor = cast(int, prod_anchor)
    prod_argmax = cast(int, prod_argmax)
    source_m, m_certificate_sha256, source_rejects = _resolve_m_source(
        p0,
        p1,
        D,
        cert,
        m_certificate_resolver,
    )
    if source_rejects:
        return RejectedExactInterval(source_rejects)
    if source_m is None:
        return RejectedExactInterval((ExactReject.M_CERTIFICATE_REJECTED,))

    lo = cast(Fraction, ratios["interval_lo"])
    hi = cast(Fraction, ratios["interval_hi"])
    m = cast(Fraction, ratios["m"])
    cont_upper = cast(Fraction, ratios["cont_star_upper"])
    tau = cast(Fraction, ratios["tau_upper"])
    radius_sq = cast(Fraction, ratios["radius_sq"])
    distance_sq = cast(Fraction, ratios["distance_sq_upper"])

    if not (0 <= lo <= hi <= D):
        rejects.append(ExactReject.BAD_INTERVAL)
    elif not _valid_bracket(p0, p1, D, lo, hi):
        rejects.append(ExactReject.DERIVATIVE_BRACKET_FAILED)
    if m <= 0:
        rejects.append(ExactReject.STALE_M)
    elif m != source_m:
        rejects.append(ExactReject.M_SOURCE_MISMATCH)
    expected_upper = _split_cont_upper_for_interval(p0, p1, D, lo, hi)
    if cont_upper != expected_upper:
        rejects.append(ExactReject.STALE_CONT_UPPER)
    expected_prod_anchor = _prod_split(p0, p1, D, anchor)
    expected_prod_argmax = _prod_split(p0, p1, D, argmax)
    if prod_anchor != expected_prod_anchor or prod_argmax != expected_prod_argmax:
        rejects.append(ExactReject.STALE_PROD)
    canonical_argmax, canonical_prod = _canonical_prod_argmax(p0, p1, D)
    if argmax != canonical_argmax or expected_prod_argmax != canonical_prod:
        rejects.append(ExactReject.ARGMAX_NOT_CANONICAL_MAX)
    if expected_prod_anchor > expected_prod_argmax:
        rejects.append(ExactReject.ARGMAX_NOT_DOMINATING_ANCHOR)
    expected_tau = expected_upper - Fraction(expected_prod_argmax)
    if tau != expected_tau:
        rejects.append(ExactReject.STALE_TAU)
    expected_radius_sq = 2 * expected_tau / source_m
    if radius_sq != expected_radius_sq:
        rejects.append(ExactReject.STALE_RADIUS)
    expected_distance_sq = _distance_sq_upper(argmax, lo, hi)
    if distance_sq != expected_distance_sq:
        rejects.append(ExactReject.STALE_DISTANCE)
    if expected_distance_sq > radius_sq:
        rejects.append(ExactReject.RADIUS_UNDERSTATES_DISTANCE)

    unique = tuple(dict.fromkeys(rejects))
    if unique:
        return RejectedExactInterval(unique)
    return AcceptedExactInterval(
        anchor=anchor,
        argmax=argmax,
        interval_lo=lo,
        interval_hi=hi,
        m=m,
        cont_star_upper=cont_upper,
        tau_upper=tau,
        radius_sq=radius_sq,
        distance_sq_upper=distance_sq,
        prod_argmax=expected_prod_argmax,
        m_source=str(m_source),
        m_certificate_sha256=m_certificate_sha256,
    )


def _fraction_decimal(value: Fraction) -> float:
    return float(value.numerator) / float(value.denominator)


def _accepted_json(result: AcceptedExactInterval) -> dict[str, object]:
    return {
        "anchor": result.anchor,
        "argmax": result.argmax,
        "prod_argmax": result.prod_argmax,
        "interval_lo": _fraction_decimal(result.interval_lo),
        "interval_hi": _fraction_decimal(result.interval_hi),
        "interval_width": _fraction_decimal(result.interval_hi - result.interval_lo),
        "m": _fraction_decimal(result.m),
        "tau_upper": _fraction_decimal(result.tau_upper),
        "radius_sq": _fraction_decimal(result.radius_sq),
        "distance_sq_upper": _fraction_decimal(result.distance_sq_upper),
    }


def _sample_domain(rng: random.Random) -> tuple[Pool, Pool, int]:
    return (
        Pool(rng.randint(100, 20_000), rng.randint(100, 80_000), rng.choice(FEE_CHOICES)),
        Pool(rng.randint(100, 20_000), rng.randint(100, 80_000), rng.choice(FEE_CHOICES)),
        rng.randint(10, 250),
    )


def valid_corpus_replay(count: int = 80) -> dict[str, object]:
    rng = random.Random(20260630)
    interior_cases = tuple(
        (Pool(1000 + idx * 137, 1000 + idx * 211, 0), Pool(1000 + idx * 137, 1000 + idx * 211, 0), 40 + idx * 10)
        for idx in range(1, 9)
    )
    domains = [_sample_domain(rng) for _ in range(count)]
    domains.extend(interior_cases)
    accepted = 0
    nonzero_window = 0
    nonzero_interval = 0
    max_radius_sq = Fraction(0)
    max_width = Fraction(0)
    for p0, p1, D in domains:
        raw = build_exact_interval_certificate(p0, p1, D)
        result = verify_exact_interval_certificate_bytes(p0, p1, D, raw)
        if not isinstance(result, AcceptedExactInterval):
            return {"ok": False, "rejects": [reject.value for reject in result.rejects]}
        accepted += 1
        if result.distance_sq_upper > 0:
            nonzero_window += 1
        if result.interval_hi > result.interval_lo:
            nonzero_interval += 1
        max_radius_sq = max(max_radius_sq, result.radius_sq)
        max_width = max(max_width, result.interval_hi - result.interval_lo)
    return {
        "ok": accepted == len(domains) and nonzero_window > 0 and nonzero_interval > 0,
        "case_count": len(domains),
        "random_case_count": count,
        "interior_case_count": len(interior_cases),
        "accepted_count": accepted,
        "nonzero_window_count": nonzero_window,
        "nonzero_interval_count": nonzero_interval,
        "max_radius_sq": _fraction_decimal(max_radius_sq),
        "max_interval_width": _fraction_decimal(max_width),
    }


def boundary_replay() -> dict[str, object]:
    cases = [
        ("left_boundary", Pool(1_000_000, 100, 0), Pool(100, 80_000, 0), 40),
        ("right_boundary", Pool(100, 80_000, 0), Pool(1_000_000, 100, 0), 40),
    ]
    outputs = []
    for case_id, p0, p1, D in cases:
        raw = build_exact_interval_certificate(p0, p1, D)
        result = verify_exact_interval_certificate_bytes(p0, p1, D, raw)
        if not isinstance(result, AcceptedExactInterval):
            return {"ok": False, "case_id": case_id, "rejects": [reject.value for reject in result.rejects]}
        outputs.append({"case_id": case_id, "accepted": _accepted_json(result)})
    return {"ok": True, "cases": outputs}


def _decoded(raw: bytes) -> dict[str, object]:
    parsed = json.loads(raw.decode("utf-8"))
    if not isinstance(parsed, dict):
        raise ValueError("generated certificate must decode to an object")
    return parsed


def _mutate_fraction(value: object, num_delta: int = 1) -> object:
    if not isinstance(value, dict):
        raise ValueError("generated fraction must decode to an object")
    return {"num": int(value["num"]) + num_delta, "den": int(value["den"])}


def _generated_int(payload: Mapping[str, object], key: str) -> int:
    value = payload.get(key)
    if type(value) is not int:
        raise ValueError(f"generated {key} must be an integer")
    return value


def negative_replay() -> dict[str, object]:
    p0 = Pool(4422, 22891, 0)
    p1 = Pool(14374, 71647, 100)
    D = 221
    raw = build_exact_interval_certificate(p0, p1, D)
    base = _decoded(raw)
    bad_argmax = 0 if _generated_int(base, "argmax") != 0 else D
    mutations: list[tuple[str, bytes, ExactReject]] = [
        ("duplicate_key", b'{"schema":"x","schema":"x"}', ExactReject.DUPLICATE_KEY),
        ("noncanonical", json.dumps(base, indent=2, sort_keys=True).encode("utf-8"), ExactReject.NONCANONICAL_BYTES),
        ("authority", _canonical_json_bytes(dict(base, authority_effects=True)), ExactReject.AUTHORITY_EFFECTS_PRESENT),
        ("bad_ratio", _canonical_json_bytes(dict(base, m={"num": 2, "den": 2})), ExactReject.BAD_RATIO),
        ("domain_hash", _canonical_json_bytes(dict(base, domain_hash="0" * 64)), ExactReject.DOMAIN_HASH_MISMATCH),
        ("bad_bracket", _canonical_json_bytes(dict(base, interval_lo={"num": 0, "den": 1}, interval_hi={"num": 0, "den": 1})), ExactReject.DERIVATIVE_BRACKET_FAILED),
        (
            "stale_prod",
            _canonical_json_bytes(dict(base, prod_argmax=_generated_int(base, "prod_argmax") + 1)),
            ExactReject.STALE_PROD,
        ),
        ("stale_tau", _canonical_json_bytes(dict(base, tau_upper=_mutate_fraction(base["tau_upper"]))), ExactReject.STALE_TAU),
        ("understated_radius", _canonical_json_bytes(dict(base, radius_sq={"num": 0, "den": 1})), ExactReject.STALE_RADIUS),
        ("nonmax_argmax", _canonical_json_bytes(dict(base, argmax=bad_argmax, prod_argmax=_prod_split(p0, p1, D, bad_argmax))), ExactReject.ARGMAX_NOT_CANONICAL_MAX),
    ]
    cases = []
    for mutation_id, mutated, expected in mutations:
        result = verify_exact_interval_certificate_bytes(p0, p1, D, mutated)
        rejects = result.rejects if isinstance(result, RejectedExactInterval) else ()
        cases.append(
            {
                "mutation_id": mutation_id,
                "expected_reject": expected.value,
                "rejects": [reject.value for reject in rejects],
                "ok": expected in rejects,
            }
        )
    return {
        "ok": all(case["ok"] for case in cases),
        "case_count": len(cases),
        "cases": cases,
    }


def build_report() -> dict[str, object]:
    valid = valid_corpus_replay()
    boundary = boundary_replay()
    negative = negative_replay()
    ok = valid["ok"] is True and boundary["ok"] is True and negative["ok"] is True
    return {
        "schema": "zenodex.tight_argmax_exact_interval_report.v1",
        "date": "2026-06-30",
        "ok": ok,
        "hypothesis": "exact rational interval certificates remove the float b_star and stale oracle-value dependency from bounded tight-argmax replay",
        "valid_corpus": valid,
        "boundary_replay": boundary,
        "negative_replay": negative,
        "non_claims": [
            "this is a bounded research checker and scans only D <= 4096",
            "the interval upper bound is conservative and does not claim exact continuous optimum value",
            "endpoint m is exact rational but still a lower-bound source, not the exact curvature minimum",
            "the checker grants no routing, settlement, production runtime, or consensus authority",
        ],
        "replay_command": "python3 tools/check_tight_argmax_exact_interval_certificate_20260630.py",
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
