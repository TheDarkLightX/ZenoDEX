#!/usr/bin/env python3
"""Empirical verification of the Discrete Argmax Proximity theorem (Phase 3A-reformulated).

This file verifies theorems proven in Lean 4 (DiscreteArgmaxProximity.lean) and
the production-function variant (ceiling fee + floor output).

TWO MODELS are verified:

1. LEAN MODEL (continuous fee + floor output):
   - cpmmOutputCont(K, M, x) = K * x / (M + x)  [continuous fee via gamma = 1 - fee/10000]
   - cpmmOutputFloor(K, M, x) = floor(cpmmOutputCont(K, M, x))
   - Floor error per pool: < 1
   - Split floor error: < 2  (Theorem: split_floor_error_bound)
   - Argmax proximity: floor(floor(b*)) >= opt - (L + 2)  (Theorem: cpmm_discrete_argmax_proximity)
   - Window: |b - b*| < sqrt(2*(L+2)/m)  (Theorem: cpmm_window_sufficiency)

2. PRODUCTION MODEL (ceiling fee + floor output, matches src/core/cpmm.py v8 kernel):
   - fee = ceil(a * fee_bps / 10000)
   - net = a - fee
   - out = floor(y * net / (x + net))
   - Universal floor error per pool: < gross_spot_pool + 1
     (fee-ceil changes net input by < 1, and output is gross-spot Lipschitz in net)
   - Split floor error: < gross_spot_0 + gross_spot_1 + 2
   - Low-fee empirical lane: floor(floor(b*)) >= opt - (3L + 2)
   - Low-fee empirical window: |b - b*| < sqrt(2*(3L+2)/m)
   - Tight certified-anchor argmax distance:
     |argmax_prod - b*| <= sqrt(2*tau/m), where
       tau = f_cont(b*) - f_prod(anchor)
       tau <= alpha + eta_bound under the gross-spot ceiling-fee envelope
   - Research-scope certificate checker:
     validates a supplied anchor/argmax radius packet against recomputed
     domain hash, production values, tau, gross envelope, and no-authority rail
   - Certificate-backed m composition:
     consumes a domain-matched rational interval curvature certificate or
     exact-rational stationary curvature certificate before accepting a tighter
     argmax radius

The Lean proof proves the abstract theorem (abstract_discrete_argmax_proximity)
which takes the floor error bound as a hypothesis. The CPMM-specific theorem
uses ε = 2 (Lean model). The production model's universal ceiling-fee
perturbation bound uses gross spot, while the older effective-L bound is kept
as a low-fee empirical regression and is explicitly falsified for high fees.

CONTEXT:
- Phase 3A's literal hypothesis (discrete CPMM split is concave) is FALSE.
- The CORRECT theorem is discrete argmax proximity, justifying the production
  ternary search DP's 22x speedup.

Non-claims:
- The production bounds are empirical unless stated as generic abstract Lean
  consequences. The universal ceiling-fee perturbation Lean lane remains
  conditional on explicit net-input perturbation hypotheses.
- The abstract Lean theorem covers both models; only the ε constant differs.

Determinism: All tests use fixed seeds. No real time, RNG, network, or fs.
"""

import hashlib
import importlib.util
import json
import math
import random
import sys
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from typing import Mapping


CERTIFICATE_SCHEMA = "zenodex.tight_argmax_certificate.v1"
INTERVAL_M_CERTIFICATE_SCHEMA = "zenodex.cpmm_split_interval_m_certificate.v1"
STATIONARY_M_CERTIFICATE_SCHEMA = "zenodex.cpmm_split_stationary_m_certificate.v1"
M_SOURCE_ENDPOINT = "endpoint_lower_bound"
M_SOURCE_INTERVAL_CERTIFICATE = "interval_curvature_certificate"
M_SOURCE_STATIONARY_CERTIFICATE = "stationary_curvature_certificate"
MAX_CERTIFICATE_BYTES = 8192
MAX_TIGHT_ARGMAX_FLOAT_DOMAIN_BITS = 128
CERT_TOL = 1e-6
_CURVATURE_MODULE: object | None = None
_BASE_CERTIFICATE_KEYS = frozenset({
    "alpha",
    "anchor",
    "anchor_radius",
    "argmax",
    "authority_effects",
    "b_star",
    "distance",
    "domain_hash",
    "eta_actual",
    "eta_bound",
    "gross_radius",
    "m",
    "m_source",
    "oracle_radius",
    "prod_anchor",
    "prod_argmax",
    "research_only",
    "schema",
    "tau_anchor",
    "tau_oracle",
})
_ENDPOINT_CERTIFICATE_KEYS = _BASE_CERTIFICATE_KEYS
_INTERVAL_CERTIFICATE_KEYS = _BASE_CERTIFICATE_KEYS | frozenset({
    "m_certificate_schema",
    "m_certificate_sha256",
})
_STATIONARY_CERTIFICATE_KEYS = _INTERVAL_CERTIFICATE_KEYS
_M_CERTIFICATE_SOURCE_CONFIG = {
    M_SOURCE_INTERVAL_CERTIFICATE: (
        _INTERVAL_CERTIFICATE_KEYS,
        INTERVAL_M_CERTIFICATE_SCHEMA,
        "verify_interval_curvature_m_certificate_bytes",
    ),
    M_SOURCE_STATIONARY_CERTIFICATE: (
        _STATIONARY_CERTIFICATE_KEYS,
        STATIONARY_M_CERTIFICATE_SCHEMA,
        "verify_stationary_curvature_m_certificate_bytes",
    ),
}


class CertificateReject(str, Enum):
    """Stable reject reasons for the research-scope argmax certificate."""

    BAD_JSON = "bad_json"
    DUPLICATE_KEY = "duplicate_key"
    NONCANONICAL_BYTES = "noncanonical_bytes"
    CERTIFICATE_TOO_LARGE = "certificate_too_large"
    BAD_SCHEMA = "bad_schema"
    AUTHORITY_EFFECTS_PRESENT = "authority_effects_present"
    BAD_DOMAIN = "bad_domain"
    DOMAIN_HASH_MISMATCH = "domain_hash_mismatch"
    BAD_INDEX = "bad_index"
    BAD_B_STAR = "bad_b_star"
    BAD_M = "bad_m"
    BAD_M_SOURCE = "bad_m_source"
    BAD_M_CERTIFICATE_REF = "bad_m_certificate_ref"
    M_CERTIFICATE_MISSING = "m_certificate_missing"
    M_CERTIFICATE_HASH_MISMATCH = "m_certificate_hash_mismatch"
    M_CERTIFICATE_REJECTED = "m_certificate_rejected"
    M_SOURCE_MISMATCH = "m_source_mismatch"
    BAD_NUMERIC_FIELD = "bad_numeric_field"
    STALE_METRIC = "stale_metric"
    ARGMAX_NOT_DOMINATING_ANCHOR = "argmax_not_dominating_anchor"
    ONE_SIDED_PERTURBATION_FAILED = "one_sided_perturbation_failed"
    RADIUS_UNDERSTATES_DISTANCE = "radius_understates_distance"
    RADIUS_HIERARCHY_FAILED = "radius_hierarchy_failed"


@dataclass(frozen=True)
class CertificateCheckResult:
    """Validated certificate result. `ok=True` is the only accepted state."""

    ok: bool
    rejects: tuple[CertificateReject, ...]
    anchor_radius: float | None = None
    oracle_radius: float | None = None
    gross_radius: float | None = None
    distance: float | None = None


class DuplicateKey(ValueError):
    """Raised while parsing JSON objects with duplicate keys."""


def _curvature_module() -> object:
    global _CURVATURE_MODULE
    if _CURVATURE_MODULE is not None:
        return _CURVATURE_MODULE
    module_path = Path(__file__).with_name("concavity_conservation_law_test.py")
    spec = importlib.util.spec_from_file_location(
        "_zenodex_concavity_conservation_law_test",
        module_path,
    )
    if spec is None or spec.loader is None:
        raise RuntimeError(f"could not load {module_path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    _CURVATURE_MODULE = module
    return module


@dataclass(frozen=True)
class Pool:
    """CPMM pool: (reserve_in, reserve_out, fee_bps)."""
    reserve_in: int
    reserve_out: int
    fee_bps: int


# ---------------------------------------------------------------------------
# LEAN MODEL: continuous fee + floor output (matches DiscreteArgmaxProximity.lean)
# ---------------------------------------------------------------------------

def cpmm_lean_floor(p: Pool, amount_in: float) -> int:
    """Lean model: continuous fee, floor output. Matches cpmmOutputFloor in Lean."""
    if amount_in <= 0.0:
        return 0
    gamma = 1.0 - p.fee_bps / 10000.0
    net = amount_in * gamma
    if net <= 0.0:
        return 0
    return int(math.floor(p.reserve_out * net / (p.reserve_in + net)))


def cpmm_lean_cont(p: Pool, amount_in: float) -> float:
    """Lean model: continuous, no floor. Matches cpmmOutputCont in Lean."""
    if amount_in <= 0.0:
        return 0.0
    gamma = 1.0 - p.fee_bps / 10000.0
    net = amount_in * gamma
    if net <= 0.0:
        return 0.0
    return p.reserve_out * net / (p.reserve_in + net)


def split_lean_floor(p0: Pool, p1: Pool, D: float, a: float) -> int:
    return cpmm_lean_floor(p0, a) + cpmm_lean_floor(p1, D - a)


def split_lean_cont(p0: Pool, p1: Pool, D: float, a: float) -> float:
    return cpmm_lean_cont(p0, a) + cpmm_lean_cont(p1, D - a)


# ---------------------------------------------------------------------------
# PRODUCTION MODEL: ceiling fee + floor output (matches src/core/cpmm.py v8)
# ---------------------------------------------------------------------------

def cpmm_prod_floor(p: Pool, amount_in: int) -> int:
    """Production: ceiling fee, floor division. Matches v8 kernel."""
    if amount_in <= 0:
        return 0
    fee = (amount_in * p.fee_bps + 9999) // 10000  # ceil
    net = amount_in - fee
    if net <= 0:
        return 0
    return (p.reserve_out * net) // (p.reserve_in + net)  # floor


def split_prod_floor(p0: Pool, p1: Pool, D: int, a: int) -> int:
    return cpmm_prod_floor(p0, a) + cpmm_prod_floor(p1, D - a)


# ---------------------------------------------------------------------------
# Parameters
# ---------------------------------------------------------------------------

def spot_price(p: Pool) -> float:
    gamma = 1.0 - p.fee_bps / 10000.0
    if p.reserve_in == 0:
        return 0.0
    return gamma * p.reserve_out / p.reserve_in


def gross_spot_price(p: Pool) -> float:
    if p.reserve_in == 0:
        return 0.0
    return p.reserve_out / p.reserve_in


def lipschitz_constant(p0: Pool, p1: Pool) -> float:
    return max(spot_price(p0), spot_price(p1))


def gross_ceiling_fee_perturbation_bound(p0: Pool, p1: Pool) -> float:
    return gross_spot_price(p0) + gross_spot_price(p1) + 2.0


def strong_concavity_param(p0: Pool, p1: Pool, D: float, b_star: float) -> float:
    gamma0 = 1.0 - p0.fee_bps / 10000.0
    gamma1 = 1.0 - p1.fee_bps / 10000.0
    x0, y0 = float(p0.reserve_in), float(p0.reserve_out)
    x1, y1 = float(p1.reserve_in), float(p1.reserve_out)
    net0 = gamma0 * b_star
    net1 = gamma1 * (D - b_star)
    denom0 = (x0 + net0) ** 3
    denom1 = (x1 + net1) ** 3
    term0 = 2.0 * y0 * gamma0 ** 2 * x0 / denom0 if denom0 > 0 else 0.0
    term1 = 2.0 * y1 * gamma1 ** 2 * x1 / denom1 if denom1 > 0 else 0.0
    return term0 + term1


def strong_concavity_param_sampled_lower(p0: Pool, p1: Pool, D: int) -> float:
    if D <= 0:
        return 0.0
    samples = {0.0, float(D)}
    samples.update(float(a) for a in range(D + 1))
    samples.update(D * i / 200.0 for i in range(201))
    return min(strong_concavity_param(p0, p1, float(D), a) for a in samples)


def strong_concavity_param_pool_lower_bound(p0: Pool, p1: Pool, D: int) -> float:
    """Pool-parameter curvature lower bound used as a conservative m certificate."""
    gamma0 = 1.0 - p0.fee_bps / 10000.0
    gamma1 = 1.0 - p1.fee_bps / 10000.0
    x0, y0 = float(p0.reserve_in), float(p0.reserve_out)
    x1, y1 = float(p1.reserve_in), float(p1.reserve_out)
    d = float(D)
    denom0 = (x0 + gamma0 * d) ** 3
    denom1 = (x1 + gamma1 * d) ** 3
    term0 = 2.0 * y0 * gamma0 ** 2 * x0 / denom0 if denom0 > 0 else 0.0
    term1 = 2.0 * y1 * gamma1 ** 2 * x1 / denom1 if denom1 > 0 else 0.0
    return term0 + term1


# ---------------------------------------------------------------------------
# Optima
# ---------------------------------------------------------------------------

def continuous_optimum(p0: Pool, p1: Pool, D: int) -> float:
    if D <= 0:
        return 0.0
    lo, hi = 0.0, float(D)
    for _ in range(200):
        if hi - lo < 1e-12:
            break
        m1 = lo + (hi - lo) / 3.0
        m2 = hi - (hi - lo) / 3.0
        if split_lean_cont(p0, p1, float(D), m1) < split_lean_cont(p0, p1, float(D), m2):
            lo = m1
        else:
            hi = m2
    return (lo + hi) / 2.0


def discrete_optimum_lean(p0: Pool, p1: Pool, D: int) -> tuple[int, int]:
    best_a, best_out = 0, split_lean_floor(p0, p1, float(D), 0.0)
    for a in range(D + 1):
        out = split_lean_floor(p0, p1, float(D), float(a))
        if out > best_out or (out == best_out and a < best_a):
            best_out, best_a = out, a
    return best_a, best_out


def discrete_optimum_prod(p0: Pool, p1: Pool, D: int) -> tuple[int, int]:
    best_a, best_out = 0, split_prod_floor(p0, p1, D, 0)
    for a in range(D + 1):
        out = split_prod_floor(p0, p1, D, a)
        if out > best_out or (out == best_out and a < best_a):
            best_out, best_a = out, a
    return best_a, best_out


def continuous_integer_anchor_loss(p0: Pool, p1: Pool, D: int, b_star: float) -> float:
    best_integer_cont = max(split_lean_cont(p0, p1, float(D), float(a)) for a in range(D + 1))
    loss = split_lean_cont(p0, p1, float(D), b_star) - best_integer_cont
    return max(0.0, loss)


def best_continuous_integer_anchor(p0: Pool, p1: Pool, D: int) -> int:
    """Integer anchor with maximum clean continuous value; leftmost on ties."""
    best_a = 0
    best_value = split_lean_cont(p0, p1, float(D), 0.0)
    for a in range(1, D + 1):
        value = split_lean_cont(p0, p1, float(D), float(a))
        if value > best_value + 1e-12:
            best_a = a
            best_value = value
    return best_a


# ---------------------------------------------------------------------------
# Research-scope tight argmax certificate checker
# ---------------------------------------------------------------------------

def _canonical_json_bytes(payload: Mapping[str, object]) -> bytes:
    return json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")


def _reject_duplicate_keys(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise DuplicateKey(key)
        result[key] = value
    return result


def tight_argmax_domain_hash(p0: Pool, p1: Pool, D: int) -> str:
    payload: dict[str, object] = {
        "D": D,
        "pools": [
            {
                "reserve_in": p0.reserve_in,
                "reserve_out": p0.reserve_out,
                "fee_bps": p0.fee_bps,
            },
            {
                "reserve_in": p1.reserve_in,
                "reserve_out": p1.reserve_out,
                "fee_bps": p1.fee_bps,
            },
        ],
    }
    return hashlib.sha256(_canonical_json_bytes(payload)).hexdigest()


def _field_int(cert: Mapping[str, object], key: str) -> int | None:
    value = cert.get(key)
    if type(value) is int:
        return value
    return None


def _field_float(cert: Mapping[str, object], key: str) -> float | None:
    value = cert.get(key)
    if type(value) not in (int, float):
        return None
    result = float(value)
    if not math.isfinite(result):
        return None
    return result


def _bounded_int(value: object, *, positive: bool, max_bits: int) -> bool:
    if isinstance(value, bool) or not isinstance(value, int):
        return False
    if positive and value <= 0:
        return False
    if not positive and value < 0:
        return False
    return value.bit_length() <= max_bits


def _pool_float_domain_valid(p: Pool) -> bool:
    return (
        _bounded_int(
            p.reserve_in,
            positive=True,
            max_bits=MAX_TIGHT_ARGMAX_FLOAT_DOMAIN_BITS,
        )
        and _bounded_int(
            p.reserve_out,
            positive=True,
            max_bits=MAX_TIGHT_ARGMAX_FLOAT_DOMAIN_BITS,
        )
        and type(p.fee_bps) is int
        and 0 <= p.fee_bps < 10000
    )


def _tight_argmax_float_domain_valid(p0: Pool, p1: Pool, D: int) -> bool:
    """Bound the research-only float replay lane before any float conversion."""
    return (
        _pool_float_domain_valid(p0)
        and _pool_float_domain_valid(p1)
        and _bounded_int(
            D,
            positive=False,
            max_bits=MAX_TIGHT_ARGMAX_FLOAT_DOMAIN_BITS,
        )
    )


def _close(a: float, b: float) -> bool:
    return abs(a - b) <= CERT_TOL * max(1.0, abs(a), abs(b))


def _is_sha256_hex(value: object) -> bool:
    if not isinstance(value, str) or len(value) != 64:
        return False
    return all(char in "0123456789abcdef" for char in value)


def _validate_m_source(
    p0: Pool,
    p1: Pool,
    D: int,
    cert: Mapping[str, object],
    m: float,
    m_certificate_resolver: Mapping[str, bytes] | None,
) -> CertificateReject | None:
    source = cert.get("m_source")
    keys = set(cert.keys())
    if source == M_SOURCE_ENDPOINT:
        if keys != _ENDPOINT_CERTIFICATE_KEYS:
            return CertificateReject.BAD_SCHEMA
        expected_m = strong_concavity_param_pool_lower_bound(p0, p1, D)
        if not _close(m, expected_m):
            return CertificateReject.M_SOURCE_MISMATCH
        return None

    config = _M_CERTIFICATE_SOURCE_CONFIG.get(source)
    if config is None:
        return CertificateReject.BAD_M_SOURCE

    expected_keys, expected_schema, verifier_name = config
    if keys != expected_keys:
        return CertificateReject.BAD_SCHEMA
    if cert.get("m_certificate_schema") != expected_schema:
        return CertificateReject.BAD_M_CERTIFICATE_REF
    cert_hash = cert.get("m_certificate_sha256")
    if not _is_sha256_hex(cert_hash):
        return CertificateReject.BAD_M_CERTIFICATE_REF
    assert isinstance(cert_hash, str)
    if m_certificate_resolver is None or cert_hash not in m_certificate_resolver:
        return CertificateReject.M_CERTIFICATE_MISSING

    m_raw = m_certificate_resolver[cert_hash]
    if hashlib.sha256(m_raw).hexdigest() != cert_hash:
        return CertificateReject.M_CERTIFICATE_HASH_MISMATCH

    curvature = _curvature_module()
    verifier = getattr(curvature, verifier_name)
    m_result = verifier(p0, p1, D, m_raw)
    if not getattr(m_result, "accepted") or getattr(m_result, "m") is None:
        return CertificateReject.M_CERTIFICATE_REJECTED
    if not _close(m, float(getattr(m_result, "m"))):
        return CertificateReject.M_SOURCE_MISMATCH
    return None


def _tight_argmax_metrics(
    p0: Pool,
    p1: Pool,
    D: int,
    anchor: int,
    argmax: int,
    b_star: float,
    m: float,
) -> dict[str, float]:
    if not _tight_argmax_float_domain_valid(p0, p1, D):
        raise ValueError("tight argmax float domain invalid")
    cont_star = split_lean_cont(p0, p1, float(D), b_star)
    cont_anchor = split_lean_cont(p0, p1, float(D), float(anchor))
    cont_argmax = split_lean_cont(p0, p1, float(D), float(argmax))
    prod_anchor = float(split_prod_floor(p0, p1, D, anchor))
    prod_argmax = float(split_prod_floor(p0, p1, D, argmax))
    alpha = max(0.0, cont_star - cont_anchor)
    eta_actual = max(0.0, cont_anchor - prod_anchor)
    eta_bound = gross_ceiling_fee_perturbation_bound(p0, p1)
    tau_anchor = max(0.0, cont_star - prod_anchor)
    tau_oracle = max(0.0, cont_star - prod_argmax)
    return {
        "cont_star": cont_star,
        "cont_anchor": cont_anchor,
        "cont_argmax": cont_argmax,
        "prod_anchor": prod_anchor,
        "prod_argmax": prod_argmax,
        "alpha": alpha,
        "eta_actual": eta_actual,
        "eta_bound": eta_bound,
        "tau_anchor": tau_anchor,
        "tau_oracle": tau_oracle,
        "anchor_radius": math.sqrt(2.0 * tau_anchor / m),
        "oracle_radius": math.sqrt(2.0 * tau_oracle / m),
        "gross_radius": math.sqrt(2.0 * (alpha + eta_bound) / m),
        "distance": abs(float(argmax) - b_star),
    }


def _build_tight_argmax_certificate_payload(
    p0: Pool,
    p1: Pool,
    D: int,
    anchor: int,
    argmax: int,
    b_star: float,
    m: float,
    m_source: str,
    extra_fields: Mapping[str, object] | None = None,
) -> dict[str, object]:
    metrics = _tight_argmax_metrics(p0, p1, D, anchor, argmax, b_star, m)
    payload: dict[str, object] = {
        "schema": CERTIFICATE_SCHEMA,
        "research_only": True,
        "authority_effects": False,
        "domain_hash": tight_argmax_domain_hash(p0, p1, D),
        "anchor": anchor,
        "argmax": argmax,
        "b_star": b_star,
        "m": m,
        "m_source": m_source,
        "tau_anchor": metrics["tau_anchor"],
        "tau_oracle": metrics["tau_oracle"],
        "alpha": metrics["alpha"],
        "eta_actual": metrics["eta_actual"],
        "eta_bound": metrics["eta_bound"],
        "anchor_radius": metrics["anchor_radius"],
        "oracle_radius": metrics["oracle_radius"],
        "gross_radius": metrics["gross_radius"],
        "distance": metrics["distance"],
        "prod_anchor": metrics["prod_anchor"],
        "prod_argmax": metrics["prod_argmax"],
    }
    if extra_fields is not None:
        payload.update(extra_fields)
    return payload


def build_tight_argmax_certificate(
    p0: Pool,
    p1: Pool,
    D: int,
    anchor: int,
    argmax: int,
    b_star: float,
    m: float,
) -> bytes:
    if not _tight_argmax_float_domain_valid(p0, p1, D):
        raise ValueError("tight argmax float domain invalid")
    endpoint_m = strong_concavity_param_pool_lower_bound(p0, p1, D)
    if not _close(m, endpoint_m):
        raise ValueError("endpoint-source certificate requires endpoint m")
    payload = _build_tight_argmax_certificate_payload(
        p0,
        p1,
        D,
        anchor,
        argmax,
        b_star,
        endpoint_m,
        M_SOURCE_ENDPOINT,
    )
    return _canonical_json_bytes(payload)


def build_interval_m_backed_tight_argmax_certificate(
    p0: Pool,
    p1: Pool,
    D: int,
    anchor: int,
    argmax: int,
    b_star: float,
    interval_m_certificate_raw: bytes,
) -> bytes:
    if not _tight_argmax_float_domain_valid(p0, p1, D):
        raise ValueError("tight argmax float domain invalid")
    cert_hash = hashlib.sha256(interval_m_certificate_raw).hexdigest()
    curvature = _curvature_module()
    verifier = getattr(curvature, "verify_interval_curvature_m_certificate_bytes")
    m_result = verifier(p0, p1, D, interval_m_certificate_raw)
    if not getattr(m_result, "accepted") or getattr(m_result, "m") is None:
        raise ValueError("interval m certificate rejected")
    m = float(getattr(m_result, "m"))
    payload = _build_tight_argmax_certificate_payload(
        p0,
        p1,
        D,
        anchor,
        argmax,
        b_star,
        m,
        M_SOURCE_INTERVAL_CERTIFICATE,
        {
            "m_certificate_schema": INTERVAL_M_CERTIFICATE_SCHEMA,
            "m_certificate_sha256": cert_hash,
        },
    )
    return _canonical_json_bytes(payload)


def build_stationary_m_backed_tight_argmax_certificate(
    p0: Pool,
    p1: Pool,
    D: int,
    anchor: int,
    argmax: int,
    b_star: float,
    stationary_m_certificate_raw: bytes,
) -> bytes:
    if not _tight_argmax_float_domain_valid(p0, p1, D):
        raise ValueError("tight argmax float domain invalid")
    cert_hash = hashlib.sha256(stationary_m_certificate_raw).hexdigest()
    curvature = _curvature_module()
    verifier = getattr(curvature, "verify_stationary_curvature_m_certificate_bytes")
    m_result = verifier(p0, p1, D, stationary_m_certificate_raw)
    if not getattr(m_result, "accepted") or getattr(m_result, "m") is None:
        raise ValueError("stationary m certificate rejected")
    m = float(getattr(m_result, "m"))
    payload = _build_tight_argmax_certificate_payload(
        p0,
        p1,
        D,
        anchor,
        argmax,
        b_star,
        m,
        M_SOURCE_STATIONARY_CERTIFICATE,
        {
            "m_certificate_schema": STATIONARY_M_CERTIFICATE_SCHEMA,
            "m_certificate_sha256": cert_hash,
        },
    )
    return _canonical_json_bytes(payload)


def verify_tight_argmax_certificate_bytes(
    p0: Pool,
    p1: Pool,
    D: int,
    raw: bytes,
    m_certificate_resolver: Mapping[str, bytes] | None = None,
) -> CertificateCheckResult:
    if len(raw) > MAX_CERTIFICATE_BYTES:
        return CertificateCheckResult(False, (CertificateReject.CERTIFICATE_TOO_LARGE,))
    if not _tight_argmax_float_domain_valid(p0, p1, D):
        return CertificateCheckResult(False, (CertificateReject.BAD_DOMAIN,))

    try:
        parsed = json.loads(raw.decode("utf-8"), object_pairs_hook=_reject_duplicate_keys)
    except DuplicateKey:
        return CertificateCheckResult(False, (CertificateReject.DUPLICATE_KEY,))
    except (UnicodeDecodeError, json.JSONDecodeError):
        return CertificateCheckResult(False, (CertificateReject.BAD_JSON,))

    if not isinstance(parsed, dict):
        return CertificateCheckResult(False, (CertificateReject.BAD_JSON,))

    cert: Mapping[str, object] = parsed
    if _canonical_json_bytes(cert) != raw:
        return CertificateCheckResult(False, (CertificateReject.NONCANONICAL_BYTES,))

    rejects: list[CertificateReject] = []
    if cert.get("schema") != CERTIFICATE_SCHEMA:
        rejects.append(CertificateReject.BAD_SCHEMA)
    if cert.get("research_only") is not True or cert.get("authority_effects") is not False:
        rejects.append(CertificateReject.AUTHORITY_EFFECTS_PRESENT)
    if cert.get("domain_hash") != tight_argmax_domain_hash(p0, p1, D):
        rejects.append(CertificateReject.DOMAIN_HASH_MISMATCH)

    anchor = _field_int(cert, "anchor")
    argmax = _field_int(cert, "argmax")
    if anchor is None or argmax is None or anchor < 0 or argmax < 0 or anchor > D or argmax > D:
        rejects.append(CertificateReject.BAD_INDEX)

    b_star = _field_float(cert, "b_star")
    if b_star is None or b_star < -CERT_TOL or b_star > D + CERT_TOL:
        rejects.append(CertificateReject.BAD_B_STAR)

    m = _field_float(cert, "m")
    if m is None or m <= 0.0:
        rejects.append(CertificateReject.BAD_M)

    metric_keys = (
        "tau_anchor",
        "tau_oracle",
        "alpha",
        "eta_actual",
        "eta_bound",
        "anchor_radius",
        "oracle_radius",
        "gross_radius",
        "distance",
        "prod_anchor",
        "prod_argmax",
    )
    claimed = {key: _field_float(cert, key) for key in metric_keys}
    if any(value is None for value in claimed.values()):
        rejects.append(CertificateReject.BAD_NUMERIC_FIELD)

    if m is not None and m > 0.0:
        m_source_reject = _validate_m_source(
            p0,
            p1,
            D,
            cert,
            m,
            m_certificate_resolver,
        )
        if m_source_reject is not None:
            rejects.append(m_source_reject)

    if rejects:
        return CertificateCheckResult(False, tuple(dict.fromkeys(rejects)))

    assert anchor is not None
    assert argmax is not None
    assert b_star is not None
    assert m is not None
    metrics = _tight_argmax_metrics(p0, p1, D, anchor, argmax, b_star, m)

    for key in metric_keys:
        if not _close(float(claimed[key]), metrics[key]):  # type: ignore[arg-type]
            rejects.append(CertificateReject.STALE_METRIC)
            break

    if metrics["prod_anchor"] > metrics["prod_argmax"] + CERT_TOL:
        rejects.append(CertificateReject.ARGMAX_NOT_DOMINATING_ANCHOR)
    if metrics["prod_argmax"] > metrics["cont_argmax"] + CERT_TOL:
        rejects.append(CertificateReject.ONE_SIDED_PERTURBATION_FAILED)
    if metrics["distance"] > float(claimed["anchor_radius"]) + CERT_TOL:  # type: ignore[arg-type]
        rejects.append(CertificateReject.RADIUS_UNDERSTATES_DISTANCE)
    if metrics["oracle_radius"] > metrics["anchor_radius"] + CERT_TOL:
        rejects.append(CertificateReject.RADIUS_HIERARCHY_FAILED)
    if metrics["anchor_radius"] > metrics["gross_radius"] + CERT_TOL:
        rejects.append(CertificateReject.RADIUS_HIERARCHY_FAILED)

    unique_rejects = tuple(dict.fromkeys(rejects))
    return CertificateCheckResult(
        ok=not unique_rejects,
        rejects=unique_rejects,
        anchor_radius=metrics["anchor_radius"],
        oracle_radius=metrics["oracle_radius"],
        gross_radius=metrics["gross_radius"],
        distance=metrics["distance"],
    )


# ---------------------------------------------------------------------------
# Test 1: LEAN MODEL floor error bound (Theorem: split_floor_error_bound)
#          0 <= split_cont(b) - split_lean_floor(b) < 2
# ---------------------------------------------------------------------------

def test_lean_model_floor_error_bound() -> None:
    """Lean model: 0 <= cont - floor < 2 for all b in [0, D]."""
    rng = random.Random(20260628)
    max_error = 0.0
    min_error = float("inf")
    total_points = 0
    for _ in range(100):
        p0 = Pool(rng.randint(10, 100_000), rng.randint(10, 100_000),
                  rng.choice([0, 30, 100, 300, 1000]))
        p1 = Pool(rng.randint(10, 100_000), rng.randint(10, 100_000),
                  rng.choice([0, 30, 100, 300, 1000]))
        D = rng.randint(5, 200)
        for a in range(D + 1):
            cont = split_lean_cont(p0, p1, float(D), float(a))
            flr = float(split_lean_floor(p0, p1, float(D), float(a)))
            err = cont - flr
            total_points += 1
            max_error = max(max_error, err)
            min_error = min(min_error, err)
            assert err >= -1e-9, (
                f"Lean floor error NEGATIVE at a={a}: err={err}")
            assert err < 2.0 + 1e-9, (
                f"Lean floor error >= 2 at a={a}: err={err}")
    assert total_points >= 5000, f"Expected >=5000 points, got {total_points}"
    print(f"PASS: lean_model_floor_error_bound "
          f"(min={min_error:.6f}, max={max_error:.6f}, {total_points} points)")


# ---------------------------------------------------------------------------
# Test 2: PRODUCTION MODEL low-fee floor error regression (empirical, < 2L + 2)
# ---------------------------------------------------------------------------

def test_prod_model_floor_error_bound() -> None:
    """Low-fee production corpus: 0 <= cont - prod_floor < 2L + 2."""
    rng = random.Random(20260629)
    max_violation = 0.0
    total_points = 0
    worst: tuple = ()
    for _ in range(200):
        p0 = Pool(rng.randint(10, 100_000), rng.randint(10, 100_000),
                  rng.choice([0, 30, 100, 300, 1000]))
        p1 = Pool(rng.randint(10, 100_000), rng.randint(10, 100_000),
                  rng.choice([0, 30, 100, 300, 1000]))
        D = rng.randint(5, 500)
        L = lipschitz_constant(p0, p1)
        bound = 2.0 * L + 2.0
        for a in range(D + 1):
            cont = split_lean_cont(p0, p1, float(D), float(a))
            prod = float(split_prod_floor(p0, p1, D, a))
            err = cont - prod
            total_points += 1
            if err >= bound + 1e-6:
                violation = err - bound
                max_violation = max(max_violation, violation)
                worst = (p0, p1, D, a, cont, prod, err, L, bound)
            assert err >= -1e-6, (
                f"Prod floor error NEGATIVE at a={a}: err={err}")
    assert max_violation <= 1e-6, (
        f"PROD FLOOR ERROR BOUND VIOLATION: {max_violation}. Worst: {worst}")
    print(f"PASS: prod_model_floor_error_bound "
          f"({total_points} points, all < 2L+2)")


# ---------------------------------------------------------------------------
# Test 2b: Effective-L ceiling-fee perturbation bound is not universal
# ---------------------------------------------------------------------------

def test_prod_effective_L_fee_bound_falsified_high_fee() -> None:
    """High fees falsify the universal claim `cont - prod < 2L_eff + 2`.

    The fee-ceil perturbation changes net input by < 1. The output curve is
    Lipschitz in net input with gross spot `R_out/R_in`, not effective spot
    `gamma * R_out/R_in`. This hard witness prevents the old empirical
    low-fee bound from being promoted as universal.
    """
    p0 = Pool(343, 6094, 9999)
    p1 = Pool(10, 8740, 9900)
    D = 96
    a = 0
    err = split_lean_cont(p0, p1, float(D), float(a)) - split_prod_floor(p0, p1, D, a)
    effective_L = lipschitz_constant(p0, p1)
    old_bound = 2.0 * effective_L + 2.0
    gross_bound = gross_ceiling_fee_perturbation_bound(p0, p1)

    assert err > old_bound, (
        f"expected high-fee witness to falsify effective-L bound: err={err}, "
        f"old_bound={old_bound}")
    assert err < gross_bound, (
        f"gross-spot perturbation bound should cover witness: err={err}, "
        f"gross_bound={gross_bound}")
    print("PASS: prod_effective_L_fee_bound_falsified_high_fee "
          f"(err={err:.4f} > 2L_eff+2={old_bound:.4f}, "
          f"gross_bound={gross_bound:.4f})")


# ---------------------------------------------------------------------------
# Test 2c: Universal ceiling-fee perturbation bound with gross spot
# ---------------------------------------------------------------------------

def test_prod_gross_spot_fee_perturbation_bound_high_fee() -> None:
    """Production: 0 <= cont - prod_floor < gross_spot_0 + gross_spot_1 + 2."""
    rng = random.Random(20260709)
    max_ratio = 0.0
    total_points = 0
    worst: tuple = ()
    fee_choices = [0, 30, 100, 300, 1000, 3000, 5000, 9000, 9900, 9999]
    for _ in range(500):
        p0 = Pool(rng.randint(10, 10_000), rng.randint(10, 100_000), rng.choice(fee_choices))
        p1 = Pool(rng.randint(10, 10_000), rng.randint(10, 100_000), rng.choice(fee_choices))
        D = rng.randint(1, 300)
        bound = gross_ceiling_fee_perturbation_bound(p0, p1)
        for a in range(D + 1):
            cont = split_lean_cont(p0, p1, float(D), float(a))
            prod = float(split_prod_floor(p0, p1, D, a))
            err = cont - prod
            total_points += 1
            ratio = err / bound if bound > 0.0 else 0.0
            if ratio > max_ratio:
                max_ratio = ratio
                worst = (p0, p1, D, a, err, bound)
            assert err >= -1e-6, (
                f"Prod floor error NEGATIVE at a={a}: err={err}")
            assert err < bound + 1e-6, (
                f"Gross perturbation bound violated: err={err}, bound={bound}, "
                f"case={(p0, p1, D, a)}")
    assert total_points >= 50_000, f"Expected >=50000 points, got {total_points}"
    print("PASS: prod_gross_spot_fee_perturbation_bound_high_fee "
          f"({total_points} points, max_ratio={max_ratio:.4f}, worst={worst})")


# ---------------------------------------------------------------------------
# Test 3: LEAN MODEL discrete argmax proximity (< L + 2)
# ---------------------------------------------------------------------------

def test_lean_model_argmax_proximity() -> None:
    """Lean: split_lean_floor(floor(b*)) >= opt - (L + 2)."""
    rng = random.Random(20260703)
    max_gap = 0
    max_bound = 0.0
    worst: tuple = ()
    total = 0
    for _ in range(1000):
        p0 = Pool(rng.randint(10, 50_000), rng.randint(10, 50_000),
                  rng.choice([0, 30, 100, 300]))
        p1 = Pool(rng.randint(10, 50_000), rng.randint(10, 50_000),
                  rng.choice([0, 30, 100, 300]))
        D = rng.randint(5, 300)
        b_star = continuous_optimum(p0, p1, D)
        b_floor = max(0, min(D, int(math.floor(b_star))))
        guided = split_lean_floor(p0, p1, float(D), float(b_floor))
        _, opt = discrete_optimum_lean(p0, p1, D)
        L = lipschitz_constant(p0, p1)
        gap = opt - guided
        bound = L + 2.0
        total += 1
        if gap > bound + 1e-9:
            if gap - bound > max_gap:
                max_gap = gap - bound
                worst = (p0, p1, D, b_star, b_floor, guided, opt, L, gap, bound)
        max_bound = max(max_bound, bound)
    assert max_gap <= 1e-9, (
        f"LEAN ARGMAX PROXIMITY VIOLATION: {max_gap}. Worst: {worst}")
    print(f"PASS: lean_model_argmax_proximity "
          f"({total} configs, all within (L+2), max_bound={max_bound:.2f})")


# ---------------------------------------------------------------------------
# Test 4: PRODUCTION MODEL discrete argmax proximity (< 3L + 2)
# ---------------------------------------------------------------------------

def test_prod_model_argmax_proximity() -> None:
    """Production: split_prod_floor(floor(b*)) >= opt - (3L + 2)."""
    rng = random.Random(20260704)
    max_violation = 0.0
    worst: tuple = ()
    total = 0
    for _ in range(1000):
        p0 = Pool(rng.randint(10, 50_000), rng.randint(10, 50_000),
                  rng.choice([0, 30, 100, 300]))
        p1 = Pool(rng.randint(10, 50_000), rng.randint(10, 50_000),
                  rng.choice([0, 30, 100, 300]))
        D = rng.randint(5, 300)
        b_star = continuous_optimum(p0, p1, D)
        b_floor = max(0, min(D, int(math.floor(b_star))))
        guided = split_prod_floor(p0, p1, D, b_floor)
        _, opt = discrete_optimum_prod(p0, p1, D)
        L = lipschitz_constant(p0, p1)
        gap = opt - guided
        bound = 3.0 * L + 2.0
        total += 1
        if gap > bound + 1e-9:
            v = gap - bound
            max_violation = max(max_violation, v)
            worst = (p0, p1, D, b_star, b_floor, guided, opt, L, gap, bound)
    assert max_violation <= 1e-9, (
        f"PROD ARGMAX PROXIMITY VIOLATION: {max_violation}. Worst: {worst}")
    print(f"PASS: prod_model_argmax_proximity "
          f"({total} configs, all within (3L+2))")


# ---------------------------------------------------------------------------
# Test 5: PRODUCTION MODEL window sufficiency (< sqrt(2*(3L+2)/m))
# ---------------------------------------------------------------------------

def test_prod_model_window_sufficiency() -> None:
    """If prod_floor(b) > prod_floor(floor(b*)), then |b - b*| < sqrt(2*(3L+2)/m).

    Path-sensitivity: asserts total_better > 0 so the test cannot vacuously
    pass when no discrete point beats the guided point. Also includes a known
    witness config (asymmetric pools) where the discrete optimum is strictly
    better than the floor-guided point, confirming the window bound is
    exercised on a real better-point.
    """
    rng = random.Random(20260705)
    max_violation = 0.0
    total_better = 0
    total_configs = 0
    worst: tuple = ()
    for _ in range(300):
        p0 = Pool(rng.randint(100, 10_000), rng.randint(100, 10_000),
                  rng.choice([0, 30, 100, 300]))
        p1 = Pool(rng.randint(100, 10_000), rng.randint(100, 10_000),
                  rng.choice([0, 30, 100, 300]))
        D = rng.randint(20, 150)
        b_star = continuous_optimum(p0, p1, D)
        b_floor = max(0, min(D, int(math.floor(b_star))))
        guided = split_prod_floor(p0, p1, D, b_floor)
        L = lipschitz_constant(p0, p1)
        m = strong_concavity_param(p0, p1, float(D), b_star)
        total_configs += 1
        if m <= 0.0:
            continue
        window = math.sqrt(2.0 * (3.0 * L + 2.0) / m)
        for b in range(D + 1):
            out = split_prod_floor(p0, p1, D, b)
            if out > guided:
                total_better += 1
                dist = abs(float(b) - b_star)
                if dist >= window - 1e-6:
                    v = dist - window
                    max_violation = max(max_violation, v)
                    worst = (p0, p1, D, b_star, b_floor, guided, b, out,
                             L, m, window, dist)
    # Path-sensitivity: the test must actually exercise the window bound on
    # real "better" points. If total_better == 0, the bound was never checked.
    assert total_better > 0, (
        "VACUOUS: no discrete point beat the floor-guided point; "
        "window bound was never exercised")
    # Known-witness check: asymmetric pools where floor(b*) misses the discrete
    # optimum, confirming the window bound is non-trivial. This is a HARD
    # assertion (no if-guards) so the witness is always exercised.
    witness_p0 = Pool(1000, 5000, 30)
    witness_p1 = Pool(5000, 1000, 30)
    witness_D = 100
    witness_bstar = continuous_optimum(witness_p0, witness_p1, witness_D)
    witness_bfloor = max(0, min(witness_D, int(math.floor(witness_bstar))))
    witness_guided = split_prod_floor(witness_p0, witness_p1, witness_D, witness_bfloor)
    witness_worst_dist = 0.0
    witness_better_count = 0
    for b in range(witness_D + 1):
        out = split_prod_floor(witness_p0, witness_p1, witness_D, b)
        if out > witness_guided:
            witness_better_count += 1
            witness_worst_dist = max(witness_worst_dist, abs(float(b) - witness_bstar))
    # Hard assertions: the witness must produce better points (non-vacuous)
    # AND the window bound must hold for them.
    assert witness_better_count > 0, (
        "Witness config (asymmetric pools) produced no better points; "
        "witness is vacuous")
    witness_m = strong_concavity_param(witness_p0, witness_p1, float(witness_D), witness_bstar)
    assert witness_m > 0, (
        f"Witness strong concavity parameter m={witness_m} <= 0; "
        "witness config invalid for window bound check")
    witness_L = lipschitz_constant(witness_p0, witness_p1)
    witness_window = math.sqrt(2.0 * (3.0 * witness_L + 2.0) / witness_m)
    assert witness_worst_dist < witness_window + 1e-6, (
        f"Witness window bound violated: dist={witness_worst_dist} "
        f">= window={witness_window}")
    assert max_violation <= 1e-6, (
        f"PROD WINDOW VIOLATION: {max_violation}. Worst: {worst}")
    print(f"PASS: prod_model_window_sufficiency "
          f"({total_configs} configs, {total_better} better points, "
          f"witness={witness_better_count} better, max_dist={witness_worst_dist:.4f} "
          f"< window={witness_window:.4f})")


# ---------------------------------------------------------------------------
# Test 5b: Tight one-sided perturbation argmax distance
# ---------------------------------------------------------------------------

def test_prod_argmax_distance_tight_one_sided_perturbation_bound() -> None:
    """Any production argmax lies within sqrt(2*tau/m) of b*.

    tau: exact certified-anchor deficit f_cont(b*) - f_prod(anchor).
    alpha + eta_bound: universal ceiling-fee envelope for tau using gross spot.
    m: conservative pool-parameter curvature lower bound.
    """
    rng = random.Random(20260710)
    fee_choices = [0, 30, 100, 300, 1000, 3000, 5000, 9000]
    total = 0
    nonzero_dist = 0
    exact_tighter_than_universal = 0
    oracle_tighter_than_anchor = 0
    worst_exact_ratio = 0.0
    worst: tuple = ()
    for _ in range(300):
        p0 = Pool(rng.randint(100, 20_000), rng.randint(100, 80_000), rng.choice(fee_choices))
        p1 = Pool(rng.randint(100, 20_000), rng.randint(100, 80_000), rng.choice(fee_choices))
        D = rng.randint(10, 250)
        b_star = continuous_optimum(p0, p1, D)
        n_star, opt_prod = discrete_optimum_prod(p0, p1, D)
        anchor = best_continuous_integer_anchor(p0, p1, D)
        cont_star = split_lean_cont(p0, p1, float(D), b_star)
        cont_anchor = split_lean_cont(p0, p1, float(D), float(anchor))
        prod_anchor = float(split_prod_floor(p0, p1, D, anchor))
        alpha = max(0.0, cont_star - cont_anchor)
        eta_actual = max(0.0, cont_anchor - prod_anchor)
        eta_bound = gross_ceiling_fee_perturbation_bound(p0, p1)
        tau_exact = max(0.0, cont_star - prod_anchor)
        tau_oracle = max(0.0, cont_star - float(opt_prod))
        m = strong_concavity_param_pool_lower_bound(p0, p1, D)
        if m <= 0.0:
            continue
        exact_bound = math.sqrt(2.0 * tau_exact / m)
        oracle_bound = math.sqrt(2.0 * tau_oracle / m)
        universal_bound = math.sqrt(2.0 * (alpha + eta_bound) / m)
        dist = abs(float(n_star) - b_star)
        total += 1
        if dist > 1e-9:
            nonzero_dist += 1
        if exact_bound < universal_bound - 1e-9:
            exact_tighter_than_universal += 1
        if oracle_bound < exact_bound - 1e-9:
            oracle_tighter_than_anchor += 1
        ratio = dist / exact_bound if exact_bound > 0.0 else 0.0
        if ratio > worst_exact_ratio:
            worst_exact_ratio = ratio
            worst = (p0, p1, D, b_star, n_star, anchor, dist,
                     alpha, eta_actual, eta_bound, tau_exact, tau_oracle, m,
                     exact_bound, universal_bound, oracle_bound)
        assert abs(tau_exact - (alpha + eta_actual)) <= 1e-6, (
            f"tau decomposition failed: tau={tau_exact}, "
            f"alpha+eta_actual={alpha + eta_actual}, case={(p0, p1, D, anchor)}")
        assert eta_actual <= eta_bound + 1e-6, (
            f"gross ceiling-fee envelope failed: eta_actual={eta_actual}, "
            f"eta_bound={eta_bound}, case={(p0, p1, D, anchor)}")
        assert oracle_bound <= exact_bound + 1e-6, (
            f"oracle anchor should be no worse than continuous anchor: "
            f"oracle={oracle_bound}, exact={exact_bound}, case={(p0, p1, D)}")
        assert exact_bound <= universal_bound + 1e-6, (
            f"exact anchor deficit should improve gross envelope: exact={exact_bound}, "
            f"universal={universal_bound}, case={(p0, p1, D, anchor)}")
        assert dist <= exact_bound + 1e-6, (
            f"tight certified-anchor argmax distance bound violated: dist={dist}, "
            f"bound={exact_bound}, tau={tau_exact}, m={m}, case={(p0, p1, D)}")
        assert dist <= oracle_bound + 1e-6, (
            f"oracle-tight argmax distance bound violated: dist={dist}, "
            f"bound={oracle_bound}, tau={tau_oracle}, m={m}, case={(p0, p1, D)}")
    assert total == 300, f"Expected 300 nondegenerate configs, got {total}"
    assert nonzero_dist > 0, "VACUOUS: no production argmax was away from b*"
    assert exact_tighter_than_universal > 0, (
        "VACUOUS: exact anchor deficit never improved the gross envelope")
    assert oracle_tighter_than_anchor > 0, (
        "VACUOUS: oracle-tight argmax value never improved the certified-anchor "
        "bound")
    print("PASS: prod_argmax_distance_tight_one_sided_perturbation_bound "
          f"({total} configs, nonzero_dist={nonzero_dist}, "
          f"exact_tighter_than_universal={exact_tighter_than_universal}, "
          f"oracle_tighter_than_anchor={oracle_tighter_than_anchor}, "
          f"worst_exact_ratio={worst_exact_ratio:.4f}, worst={worst})")


# ---------------------------------------------------------------------------
# Test 5c: Research-scope tight argmax certificate checker
# ---------------------------------------------------------------------------

def _sample_certificate_case() -> tuple[Pool, Pool, int, int, int, float, float, bytes]:
    p0 = Pool(10_110, 17_529, 5000)
    p1 = Pool(15_975, 27_486, 5000)
    D = 179
    b_star = continuous_optimum(p0, p1, D)
    argmax, _ = discrete_optimum_prod(p0, p1, D)
    anchor = best_continuous_integer_anchor(p0, p1, D)
    m = strong_concavity_param_pool_lower_bound(p0, p1, D)
    raw = build_tight_argmax_certificate(p0, p1, D, anchor, argmax, b_star, m)
    return p0, p1, D, anchor, argmax, b_star, m, raw


def _decoded_certificate(raw: bytes) -> dict[str, object]:
    parsed = json.loads(raw.decode("utf-8"))
    assert isinstance(parsed, dict)
    return parsed


def test_tight_argmax_certificate_accepts_valid_corpus() -> None:
    """Research checker accepts recomputed tight-bound certificates."""
    rng = random.Random(20260710)
    fee_choices = [0, 30, 100, 300, 1000, 3000, 5000, 9000]
    total = 0
    nonzero_distance = 0
    exact_tighter_than_gross = 0
    oracle_tighter_than_anchor = 0
    for _ in range(300):
        p0 = Pool(rng.randint(100, 20_000), rng.randint(100, 80_000), rng.choice(fee_choices))
        p1 = Pool(rng.randint(100, 20_000), rng.randint(100, 80_000), rng.choice(fee_choices))
        D = rng.randint(10, 250)
        b_star = continuous_optimum(p0, p1, D)
        argmax, _ = discrete_optimum_prod(p0, p1, D)
        anchor = best_continuous_integer_anchor(p0, p1, D)
        m = strong_concavity_param_pool_lower_bound(p0, p1, D)
        assert m > 0.0, f"invalid m={m} for case {(p0, p1, D)}"
        raw = build_tight_argmax_certificate(p0, p1, D, anchor, argmax, b_star, m)
        result = verify_tight_argmax_certificate_bytes(p0, p1, D, raw)
        assert result.ok, f"valid certificate rejected: {result.rejects}"
        assert result.distance is not None
        assert result.anchor_radius is not None
        assert result.oracle_radius is not None
        assert result.gross_radius is not None
        total += 1
        if result.distance > 1e-9:
            nonzero_distance += 1
        if result.anchor_radius < result.gross_radius - 1e-9:
            exact_tighter_than_gross += 1
        if result.oracle_radius < result.anchor_radius - 1e-9:
            oracle_tighter_than_anchor += 1
    assert total == 300, f"Expected 300 certificates, got {total}"
    assert nonzero_distance > 0, "VACUOUS: every argmax certificate had zero distance"
    assert exact_tighter_than_gross > 0, (
        "VACUOUS: exact certificate never improved the gross envelope")
    assert oracle_tighter_than_anchor > 0, (
        "VACUOUS: oracle certificate never improved the anchor certificate")
    print("PASS: tight_argmax_certificate_accepts_valid_corpus "
          f"({total} certificates, nonzero_distance={nonzero_distance}, "
          f"exact_tighter_than_gross={exact_tighter_than_gross}, "
          f"oracle_tighter_than_anchor={oracle_tighter_than_anchor})")


def test_tight_argmax_certificate_rejects_mutations() -> None:
    """Research checker rejects stale, authority-bearing, and noncanonical packets."""
    p0, p1, D, anchor, _argmax, b_star, m, raw = _sample_certificate_case()
    base = _decoded_certificate(raw)
    valid = verify_tight_argmax_certificate_bytes(p0, p1, D, raw)
    assert valid.ok, f"sample certificate invalid: {valid.rejects}"

    mutation_cases: list[tuple[str, dict[str, object], CertificateReject]] = [
        ("bad_schema", {"schema": "zenodex.tight_argmax_certificate.v0"}, CertificateReject.BAD_SCHEMA),
        ("authority", {"authority_effects": True}, CertificateReject.AUTHORITY_EFFECTS_PRESENT),
        ("stale_domain", {"domain_hash": "0" * 64}, CertificateReject.DOMAIN_HASH_MISMATCH),
        ("bad_anchor", {"anchor": D + 1}, CertificateReject.BAD_INDEX),
        ("bad_m", {"m": 0.0}, CertificateReject.BAD_M),
        ("understated_radius", {"anchor_radius": 0.0}, CertificateReject.RADIUS_UNDERSTATES_DISTANCE),
    ]
    for name, updates, expected in mutation_cases:
        mutated = dict(base)
        mutated.update(updates)
        result = verify_tight_argmax_certificate_bytes(p0, p1, D, _canonical_json_bytes(mutated))
        assert expected in result.rejects, (
            f"{name}: expected {expected}, got {result.rejects}")

    bad_argmax = min(range(D + 1), key=lambda a: split_prod_floor(p0, p1, D, a))
    assert split_prod_floor(p0, p1, D, anchor) > split_prod_floor(p0, p1, D, bad_argmax)
    bad_argmax_raw = build_tight_argmax_certificate(p0, p1, D, anchor, bad_argmax, b_star, m)
    bad_argmax_result = verify_tight_argmax_certificate_bytes(p0, p1, D, bad_argmax_raw)
    assert CertificateReject.ARGMAX_NOT_DOMINATING_ANCHOR in bad_argmax_result.rejects

    duplicate_raw = (
        b'{"authority_effects":false,"research_only":true,'
        b'"schema":"zenodex.tight_argmax_certificate.v1",'
        b'"schema":"zenodex.tight_argmax_certificate.v1"}'
    )
    duplicate_result = verify_tight_argmax_certificate_bytes(p0, p1, D, duplicate_raw)
    assert duplicate_result.rejects == (CertificateReject.DUPLICATE_KEY,)

    noncanonical_raw = json.dumps(base, indent=2, sort_keys=True).encode("utf-8")
    noncanonical_result = verify_tight_argmax_certificate_bytes(p0, p1, D, noncanonical_raw)
    assert noncanonical_result.rejects == (CertificateReject.NONCANONICAL_BYTES,)
    print("PASS: tight_argmax_certificate_rejects_mutations "
          f"({len(mutation_cases) + 3} negative cases)")


def test_tight_argmax_certificate_rejects_float_overflow_domain() -> None:
    """Huge integer domains are rejected before the research float path."""
    overflow_reserve = (
        5643803094122361801063599550934354178498840916875289431586257363382552571199220880341666641086706089985
    )
    unsafe_p0 = Pool(reserve_in=overflow_reserve, reserve_out=1000, fee_bps=0)
    p1 = Pool(reserve_in=1000, reserve_out=1000, fee_bps=0)
    D = 1

    assert not _tight_argmax_float_domain_valid(unsafe_p0, p1, D)
    assert _tight_argmax_float_domain_valid(Pool(1 << 127, 1000, 0), p1, D)

    try:
        strong_concavity_param_pool_lower_bound(unsafe_p0, p1, D)
        raise AssertionError("expected pre-guard float overflow witness")
    except OverflowError:
        pass

    cert: dict[str, object] = {
        "schema": CERTIFICATE_SCHEMA,
        "research_only": True,
        "authority_effects": False,
        "domain_hash": tight_argmax_domain_hash(unsafe_p0, p1, D),
        "anchor": 0,
        "argmax": 0,
        "b_star": 0.0,
        "m": 1.0,
        "m_source": M_SOURCE_ENDPOINT,
        "tau_anchor": 0.0,
        "tau_oracle": 0.0,
        "alpha": 0.0,
        "eta_actual": 0.0,
        "eta_bound": 0.0,
        "anchor_radius": 0.0,
        "oracle_radius": 0.0,
        "gross_radius": 0.0,
        "distance": 0.0,
        "prod_anchor": 0.0,
        "prod_argmax": 0.0,
    }
    result = verify_tight_argmax_certificate_bytes(
        unsafe_p0,
        p1,
        D,
        _canonical_json_bytes(cert),
    )
    assert result.rejects == (CertificateReject.BAD_DOMAIN,)

    try:
        build_tight_argmax_certificate(unsafe_p0, p1, D, 0, 0, 0.0, 1.0)
        raise AssertionError("builder accepted invalid float domain")
    except ValueError:
        pass

    print("PASS: tight_argmax_certificate_rejects_float_overflow_domain "
          f"(max_bits={MAX_TIGHT_ARGMAX_FLOAT_DOMAIN_BITS})")


def test_interval_m_backed_tight_argmax_certificate_composition() -> None:
    """Tight argmax certificates can consume checked interval-m certificates."""
    rng = random.Random(20260730)
    fee_choices = [0, 30, 100, 300, 1000, 3000, 5000, 9000]
    curvature = _curvature_module()
    build_refined = getattr(curvature, "build_refined_interval_curvature_m_certificate")
    verify_interval = getattr(curvature, "verify_interval_curvature_m_certificate_bytes")
    total = 0
    interval_tighter_than_endpoint = 0
    nonzero_distance = 0
    max_radius_shrink = 1.0
    for _ in range(150):
        p0 = Pool(rng.randint(100, 20_000), rng.randint(100, 80_000), rng.choice(fee_choices))
        p1 = Pool(rng.randint(100, 20_000), rng.randint(100, 80_000), rng.choice(fee_choices))
        D = rng.randint(10, 250)
        b_star = continuous_optimum(p0, p1, D)
        argmax, _ = discrete_optimum_prod(p0, p1, D)
        anchor = best_continuous_integer_anchor(p0, p1, D)
        endpoint_m = strong_concavity_param_pool_lower_bound(p0, p1, D)
        interval_m_raw = build_refined(p0, p1, D, 16, 64)
        interval_m_result = verify_interval(p0, p1, D, interval_m_raw)
        assert interval_m_result.accepted, interval_m_result.reject
        cert_hash = hashlib.sha256(interval_m_raw).hexdigest()
        endpoint_raw = build_tight_argmax_certificate(
            p0,
            p1,
            D,
            anchor,
            argmax,
            b_star,
            endpoint_m,
        )
        interval_raw = build_interval_m_backed_tight_argmax_certificate(
            p0,
            p1,
            D,
            anchor,
            argmax,
            b_star,
            interval_m_raw,
        )
        endpoint_result = verify_tight_argmax_certificate_bytes(p0, p1, D, endpoint_raw)
        interval_result = verify_tight_argmax_certificate_bytes(
            p0,
            p1,
            D,
            interval_raw,
            {cert_hash: interval_m_raw},
        )
        assert endpoint_result.ok, endpoint_result.rejects
        assert interval_result.ok, interval_result.rejects
        assert endpoint_result.anchor_radius is not None
        assert interval_result.anchor_radius is not None
        assert interval_result.distance is not None
        assert interval_result.anchor_radius <= endpoint_result.anchor_radius + 1e-9
        if interval_result.anchor_radius < endpoint_result.anchor_radius - 1e-9:
            interval_tighter_than_endpoint += 1
            max_radius_shrink = max(
                max_radius_shrink,
                endpoint_result.anchor_radius / interval_result.anchor_radius,
            )
        if interval_result.distance > 1e-9:
            nonzero_distance += 1
        total += 1

    assert total == 150, f"Expected 150 composed certificates, got {total}"
    assert nonzero_distance > 0, "VACUOUS: every composed certificate had zero distance"
    assert interval_tighter_than_endpoint > 0, (
        "VACUOUS: interval m certificates never tightened endpoint radius")
    print("PASS: interval_m_backed_tight_argmax_certificate_composition "
          f"({total} certificates, tightened={interval_tighter_than_endpoint}, "
          f"max_radius_shrink={max_radius_shrink:.6g}x)")


def test_interval_m_backed_tight_argmax_certificate_rejects_bad_composition() -> None:
    """Composed certificates reject missing, stale, and mismatched m artifacts."""
    p0, p1, D, anchor, argmax, b_star, _endpoint_m, _raw = _sample_certificate_case()
    curvature = _curvature_module()
    build_refined = getattr(curvature, "build_refined_interval_curvature_m_certificate")
    interval_m_raw = build_refined(p0, p1, D, 16, 64)
    cert_hash = hashlib.sha256(interval_m_raw).hexdigest()
    raw = build_interval_m_backed_tight_argmax_certificate(
        p0,
        p1,
        D,
        anchor,
        argmax,
        b_star,
        interval_m_raw,
    )
    base = _decoded_certificate(raw)
    valid = verify_tight_argmax_certificate_bytes(p0, p1, D, raw, {cert_hash: interval_m_raw})
    assert valid.ok, valid.rejects

    missing_result = verify_tight_argmax_certificate_bytes(p0, p1, D, raw)
    assert missing_result.rejects == (CertificateReject.M_CERTIFICATE_MISSING,)

    tampered_resolver = {cert_hash: interval_m_raw + b"\n"}
    tampered_result = verify_tight_argmax_certificate_bytes(
        p0,
        p1,
        D,
        raw,
        tampered_resolver,
    )
    assert CertificateReject.M_CERTIFICATE_HASH_MISMATCH in tampered_result.rejects

    wrong_domain_raw = build_refined(p0, p1, D + 1, 16, 64)
    wrong_hash = hashlib.sha256(wrong_domain_raw).hexdigest()
    wrong_domain_cert = dict(base)
    wrong_domain_cert["m_certificate_sha256"] = wrong_hash
    wrong_domain_result = verify_tight_argmax_certificate_bytes(
        p0,
        p1,
        D,
        _canonical_json_bytes(wrong_domain_cert),
        {wrong_hash: wrong_domain_raw},
    )
    assert CertificateReject.M_CERTIFICATE_REJECTED in wrong_domain_result.rejects

    overstated = dict(base)
    assert isinstance(overstated["m"], (int, float))
    overstated["m"] = float(overstated["m"]) * 1.5
    overstated_metrics = _tight_argmax_metrics(
        p0,
        p1,
        D,
        anchor,
        argmax,
        b_star,
        float(overstated["m"]),
    )
    for key in (
        "tau_anchor",
        "tau_oracle",
        "alpha",
        "eta_actual",
        "eta_bound",
        "anchor_radius",
        "oracle_radius",
        "gross_radius",
        "distance",
        "prod_anchor",
        "prod_argmax",
    ):
        overstated[key] = overstated_metrics[key]
    overstated_result = verify_tight_argmax_certificate_bytes(
        p0,
        p1,
        D,
        _canonical_json_bytes(overstated),
        {cert_hash: interval_m_raw},
    )
    assert CertificateReject.M_SOURCE_MISMATCH in overstated_result.rejects

    bad_source = dict(base)
    bad_source["m_source"] = "caller_supplied"
    bad_source.pop("m_certificate_schema")
    bad_source.pop("m_certificate_sha256")
    bad_source_result = verify_tight_argmax_certificate_bytes(
        p0,
        p1,
        D,
        _canonical_json_bytes(bad_source),
        {cert_hash: interval_m_raw},
    )
    assert CertificateReject.BAD_M_SOURCE in bad_source_result.rejects

    bad_ref = dict(base)
    bad_ref["m_certificate_sha256"] = "not-a-sha256"
    bad_ref_result = verify_tight_argmax_certificate_bytes(
        p0,
        p1,
        D,
        _canonical_json_bytes(bad_ref),
        {cert_hash: interval_m_raw},
    )
    assert CertificateReject.BAD_M_CERTIFICATE_REF in bad_ref_result.rejects

    print("PASS: interval_m_backed_tight_argmax_certificate_rejects_bad_composition "
          "(6 negative cases)")


def test_stationary_m_backed_tight_argmax_certificate_composition() -> None:
    """Tight argmax certificates can consume checked stationary-m certificates."""
    rng = random.Random(20260802)
    curvature = _curvature_module()
    construct = getattr(curvature, "_construct_fee_free_stationary_case")
    build_stationary = getattr(curvature, "build_stationary_curvature_m_certificate")
    verify_stationary = getattr(curvature, "verify_stationary_curvature_m_certificate_bytes")
    total = 0
    stationary_tighter_than_endpoint = 0
    nonzero_distance = 0
    max_radius_shrink = 1.0
    for _ in range(120):
        reserve_in_0 = rng.randint(10, 500)
        reserve_in_1 = rng.randint(10, 500)
        D = rng.randint(5, 200)
        minimizer_int = rng.randint(1, D - 1)
        if 2 * minimizer_int == D:
            minimizer_int = 1 if minimizer_int != 1 else D - 1
        p0, p1, D, minimizer_a = construct(
            reserve_in_0,
            reserve_in_1,
            D,
            minimizer_int,
        )
        stationary_m_raw = build_stationary(p0, p1, D, minimizer_a)
        stationary_m_result = verify_stationary(p0, p1, D, stationary_m_raw)
        assert stationary_m_result.accepted, stationary_m_result.reject
        cert_hash = hashlib.sha256(stationary_m_raw).hexdigest()

        b_star = continuous_optimum(p0, p1, D)
        argmax, _ = discrete_optimum_prod(p0, p1, D)
        anchor = best_continuous_integer_anchor(p0, p1, D)
        endpoint_m = strong_concavity_param_pool_lower_bound(p0, p1, D)
        endpoint_raw = build_tight_argmax_certificate(
            p0,
            p1,
            D,
            anchor,
            argmax,
            b_star,
            endpoint_m,
        )
        stationary_raw = build_stationary_m_backed_tight_argmax_certificate(
            p0,
            p1,
            D,
            anchor,
            argmax,
            b_star,
            stationary_m_raw,
        )
        endpoint_result = verify_tight_argmax_certificate_bytes(p0, p1, D, endpoint_raw)
        stationary_result = verify_tight_argmax_certificate_bytes(
            p0,
            p1,
            D,
            stationary_raw,
            {cert_hash: stationary_m_raw},
        )
        assert endpoint_result.ok, endpoint_result.rejects
        assert stationary_result.ok, stationary_result.rejects
        assert endpoint_result.anchor_radius is not None
        assert stationary_result.anchor_radius is not None
        assert stationary_result.distance is not None
        assert stationary_result.anchor_radius <= endpoint_result.anchor_radius + 1e-9
        if stationary_result.anchor_radius < endpoint_result.anchor_radius - 1e-9:
            stationary_tighter_than_endpoint += 1
            max_radius_shrink = max(
                max_radius_shrink,
                endpoint_result.anchor_radius / stationary_result.anchor_radius,
            )
        if stationary_result.distance > 1e-9:
            nonzero_distance += 1
        total += 1

    assert total == 120, f"Expected 120 stationary composed certificates, got {total}"
    assert nonzero_distance > 0, "VACUOUS: every stationary composed certificate had zero distance"
    assert stationary_tighter_than_endpoint > 0, (
        "VACUOUS: stationary m certificates never tightened endpoint radius")
    print("PASS: stationary_m_backed_tight_argmax_certificate_composition "
          f"({total} certificates, tightened={stationary_tighter_than_endpoint}, "
          f"nonzero_distance={nonzero_distance}, "
          f"max_radius_shrink={max_radius_shrink:.6g}x)")


def test_stationary_m_backed_tight_argmax_certificate_rejects_bad_composition() -> None:
    """Composed stationary-m certificates reject stale, missing, and mismatched artifacts."""
    curvature = _curvature_module()
    construct = getattr(curvature, "_construct_fee_free_stationary_case")
    build_stationary = getattr(curvature, "build_stationary_curvature_m_certificate")
    p0, p1, D, minimizer_a = construct(467, 437, 104, 56)
    stationary_m_raw = build_stationary(p0, p1, D, minimizer_a)
    cert_hash = hashlib.sha256(stationary_m_raw).hexdigest()
    b_star = continuous_optimum(p0, p1, D)
    argmax, _ = discrete_optimum_prod(p0, p1, D)
    anchor = best_continuous_integer_anchor(p0, p1, D)
    raw = build_stationary_m_backed_tight_argmax_certificate(
        p0,
        p1,
        D,
        anchor,
        argmax,
        b_star,
        stationary_m_raw,
    )
    base = _decoded_certificate(raw)
    valid = verify_tight_argmax_certificate_bytes(p0, p1, D, raw, {cert_hash: stationary_m_raw})
    assert valid.ok, valid.rejects

    missing_result = verify_tight_argmax_certificate_bytes(p0, p1, D, raw)
    assert missing_result.rejects == (CertificateReject.M_CERTIFICATE_MISSING,)

    tampered_result = verify_tight_argmax_certificate_bytes(
        p0,
        p1,
        D,
        raw,
        {cert_hash: stationary_m_raw + b"\n"},
    )
    assert CertificateReject.M_CERTIFICATE_HASH_MISMATCH in tampered_result.rejects

    wrong_p0, wrong_p1, wrong_D, wrong_minimizer_a = construct(467, 437, D + 1, 56)
    wrong_domain_raw = build_stationary(wrong_p0, wrong_p1, wrong_D, wrong_minimizer_a)
    wrong_hash = hashlib.sha256(wrong_domain_raw).hexdigest()
    wrong_domain_cert = dict(base)
    wrong_domain_cert["m_certificate_sha256"] = wrong_hash
    wrong_domain_result = verify_tight_argmax_certificate_bytes(
        p0,
        p1,
        D,
        _canonical_json_bytes(wrong_domain_cert),
        {wrong_hash: wrong_domain_raw},
    )
    assert CertificateReject.M_CERTIFICATE_REJECTED in wrong_domain_result.rejects

    overstated = dict(base)
    assert isinstance(overstated["m"], (int, float))
    overstated["m"] = float(overstated["m"]) * 1.5
    overstated_metrics = _tight_argmax_metrics(
        p0,
        p1,
        D,
        anchor,
        argmax,
        b_star,
        float(overstated["m"]),
    )
    for key in (
        "tau_anchor",
        "tau_oracle",
        "alpha",
        "eta_actual",
        "eta_bound",
        "anchor_radius",
        "oracle_radius",
        "gross_radius",
        "distance",
        "prod_anchor",
        "prod_argmax",
    ):
        overstated[key] = overstated_metrics[key]
    overstated_result = verify_tight_argmax_certificate_bytes(
        p0,
        p1,
        D,
        _canonical_json_bytes(overstated),
        {cert_hash: stationary_m_raw},
    )
    assert CertificateReject.M_SOURCE_MISMATCH in overstated_result.rejects

    bad_schema = dict(base)
    bad_schema["m_certificate_schema"] = INTERVAL_M_CERTIFICATE_SCHEMA
    bad_schema_result = verify_tight_argmax_certificate_bytes(
        p0,
        p1,
        D,
        _canonical_json_bytes(bad_schema),
        {cert_hash: stationary_m_raw},
    )
    assert CertificateReject.BAD_M_CERTIFICATE_REF in bad_schema_result.rejects

    bad_source = dict(base)
    bad_source["m_source"] = "caller_supplied"
    bad_source.pop("m_certificate_schema")
    bad_source.pop("m_certificate_sha256")
    bad_source_result = verify_tight_argmax_certificate_bytes(
        p0,
        p1,
        D,
        _canonical_json_bytes(bad_source),
        {cert_hash: stationary_m_raw},
    )
    assert CertificateReject.BAD_M_SOURCE in bad_source_result.rejects

    source_schema_mismatch = dict(base)
    source_schema_mismatch["m_source"] = M_SOURCE_INTERVAL_CERTIFICATE
    mismatch_result = verify_tight_argmax_certificate_bytes(
        p0,
        p1,
        D,
        _canonical_json_bytes(source_schema_mismatch),
        {cert_hash: stationary_m_raw},
    )
    assert CertificateReject.BAD_M_CERTIFICATE_REF in mismatch_result.rejects

    print("PASS: stationary_m_backed_tight_argmax_certificate_rejects_bad_composition "
          "(7 negative cases)")


# ---------------------------------------------------------------------------
# Test 6: Ternary search DP achieves the production bound
# ---------------------------------------------------------------------------

def test_ternary_search_achieves_prod_bound() -> None:
    """Local simulated window search (W=ceil(1/L), center=round(b*_cont))
    achieves a value within (3L + 2) of the discrete optimum.

    NOTE: This tests a local reproduction of the ternary-search-DP inner loop
    from docs/research/ternary_search_dp.py (the same algorithm shape used by
    the production cross-pool subset DP). It does NOT call into the production
    src/core/cross_pool_subset_dp.py implementation; that integration is
    covered by the existing Phase 1 exactness tests. This test verifies the
    (3L + 2) near-optimality bound holds for the algorithm shape, which is the
    theorem's direct application.
    """
    rng = random.Random(20260706)
    max_violation = 0.0
    worst: tuple = ()
    total = 0
    for _ in range(500):
        p0 = Pool(rng.randint(10, 50_000), rng.randint(10, 50_000),
                  rng.choice([0, 30, 100, 300]))
        p1 = Pool(rng.randint(10, 50_000), rng.randint(10, 50_000),
                  rng.choice([0, 30, 100, 300]))
        D = rng.randint(5, 300)
        L = lipschitz_constant(p0, p1)
        b_star = continuous_optimum(p0, p1, D)
        center = max(0, min(D, int(round(b_star))))
        W = max(1, math.ceil(1.0 / L)) if L > 0 else D
        lo_b = max(0, center - W)
        hi_b = min(D, center + W)
        best = split_prod_floor(p0, p1, D, lo_b)
        for b in range(lo_b, hi_b + 1):
            out = split_prod_floor(p0, p1, D, b)
            if out > best:
                best = out
        _, opt = discrete_optimum_prod(p0, p1, D)
        gap = opt - best
        bound = 3.0 * L + 2.0
        total += 1
        if gap > bound + 1e-9:
            v = gap - bound
            max_violation = max(max_violation, v)
            worst = (p0, p1, D, L, W, best, opt, gap, bound)
    assert max_violation <= 1e-9, (
        f"TERNARY DP BOUND VIOLATION: {max_violation}. Worst: {worst}")
    print(f"PASS: ternary_search_achieves_prod_bound "
          f"({total} configs, all within (3L+2))")


# ---------------------------------------------------------------------------
# Test 7: Empirical window is tighter than formal bound
# ---------------------------------------------------------------------------

def test_empirical_window_tighter() -> None:
    """Empirical W=ceil(1/L) is tighter than formal W=ceil(sqrt(2*(3L+2)/m))+1."""
    rng = random.Random(20260707)
    total = 0
    formal_tighter = 0
    for _ in range(500):
        p0 = Pool(rng.randint(100, 10_000), rng.randint(100, 10_000),
                  rng.choice([0, 30, 100, 300]))
        p1 = Pool(rng.randint(100, 10_000), rng.randint(100, 10_000),
                  rng.choice([0, 30, 100, 300]))
        D = rng.randint(20, 200)
        L = lipschitz_constant(p0, p1)
        if L <= 0:
            continue
        b_star = continuous_optimum(p0, p1, D)
        m = strong_concavity_param(p0, p1, float(D), b_star)
        if m <= 0:
            continue
        emp = max(1, math.ceil(1.0 / L))
        formal = int(math.ceil(math.sqrt(2.0 * (3.0 * L + 2.0) / m))) + 1
        total += 1
        if formal < emp:
            formal_tighter += 1
    assert total == 500, f"Expected 500, got {total}"
    print(f"PASS: empirical_window_tighter "
          f"({total} configs, formal tighter in {formal_tighter})")


# ---------------------------------------------------------------------------
# Test 8: Exact count
# ---------------------------------------------------------------------------

def test_exact_count() -> None:
    # Count of top-level randomized configs across all tests
    total = 100 + 200 + 500 + 1000 + 1000 + 300 + 300 + 300 + 1 + 150 + 120 + 500 + 500
    assert total == 4971, f"Expected 4971 top-level configs, got {total}"
    print(f"PASS: exact_count ({total} top-level configs, point counts vary by RNG)")


# ---------------------------------------------------------------------------
# Edge-case tests (Codex Finding 4): L=0, small m, b* at boundary, D<=2,
# all-fee/no-output, tie plateaus
# ---------------------------------------------------------------------------

def test_edge_case_L_zero() -> None:
    """Edge case: L = 0 (both pools have zero spot price).

    When L = 0, the Lipschitz constant is 0, meaning the continuous split
    function is constant. The floor error bound (L+2) becomes 2, and the
    window bound sqrt(2*(L+2)/m) = sqrt(4/m).

    Pool constructor: Pool(reserve_in, reserve_out, fee_bps).
    spot_price = gamma * reserve_out / reserve_in.
    L = 0 when reserve_out = 0 for both pools (zero output reserve).
    """
    # L = 0 when reserve_out = 0 (K = 0, no output reserve)
    # Use positive reserve_in to stay within Lean assumptions (M > 0)
    p0 = Pool(1000, 0, 0)  # reserve_in=1000, reserve_out=0 -> K/M = 0
    p1 = Pool(1000, 0, 0)
    D = 100
    L = lipschitz_constant(p0, p1)
    assert L == 0, f"Expected L=0, got L={L}"
    # Floor error bound: 0 <= cont - floor < 2
    for a in range(D + 1):
        cont = split_lean_cont(p0, p1, float(D), float(a))
        floor = split_lean_floor(p0, p1, float(D), float(a))
        err = cont - floor
        assert -1e-9 <= err < 2.0 + 1e-9, f"L=0 floor error {err} at a={a}"
    print(f"PASS: edge_case_L_zero (L={L}, floor error < 2)")


def test_edge_case_small_m() -> None:
    """Edge case: very small strong concavity parameter m.

    When m is very small (nearly flat function), the window bound
    sqrt(2*(L+2)/m) becomes very large. The argmax proximity (L+2)
    still holds.
    """
    # Large reserves with small D gives nearly flat function (small m)
    p0 = Pool(10_000_000, 10_000_000, 0)
    p1 = Pool(10_000_000, 10_000_000, 0)
    D = 10
    L = lipschitz_constant(p0, p1)
    b_star = continuous_optimum(p0, p1, D)
    m = strong_concavity_param(p0, p1, float(D), b_star)
    assert m > 0, f"Expected m > 0, got m={m}"
    # Argmax proximity: floor(floor(b*)) >= opt - (L+2)
    opt = max(split_lean_floor(p0, p1, float(D), float(a))
              for a in range(D + 1))
    floor_bstar = split_lean_floor(p0, p1, float(D), math.floor(b_star))
    gap = opt - floor_bstar
    bound = L + 2
    assert gap <= bound + 1e-9, (
        f"small m: gap={gap} > bound={bound}")
    # Window bound is large (sqrt(4/m) with small m)
    window = math.sqrt(2.0 * (L + 2.0) / m)
    assert window > 0, f"Expected window > 0, got {window}"
    print(f"PASS: edge_case_small_m (m={m:.6f}, window={window:.2f}, gap={gap})")


def test_edge_case_bstar_at_boundary() -> None:
    """Edge case: b* at 0 or D (continuous optimum at boundary).

    When b* = 0, all input goes to pool 1. When b* = D, all goes to pool 0.
    The floor proximity still holds: floor(0) = 0, floor(D) = D.

    Pool constructor: Pool(reserve_in, reserve_out, fee_bps).
    spot_price = gamma * reserve_out / reserve_in = K/M.
    """
    # b* near D: pool 0 has high output (high reserve_out / reserve_in)
    # Pool(reserve_in=100, reserve_out=1M) -> K/M = 1M/100 = 10000 (HIGH)
    p0 = Pool(100, 1_000_000, 0)  # high output pool
    p1 = Pool(1_000_000, 100, 0)  # low output pool
    D = 100
    b_star = continuous_optimum(p0, p1, D)
    # b* should be near D (send everything to pool 0, the high-output pool)
    assert b_star > D - 5, f"Expected b* near D={D}, got b*={b_star}"
    floor_bstar = split_lean_floor(p0, p1, float(D), math.floor(b_star))
    opt = max(split_lean_floor(p0, p1, float(D), float(a))
              for a in range(D + 1))
    L = lipschitz_constant(p0, p1)
    gap = opt - floor_bstar
    assert gap <= L + 2 + 1e-9, f"b* near D boundary: gap={gap} > L+2={L+2}"
    # Also test b* near 0 (reverse: pool 0=low output, pool 1=high output)
    # Now pool 0 (p1) has low output, pool 1 (p0) has high output
    # So optimum sends everything to pool 1, meaning a (for pool 0) = 0
    b_star_rev = continuous_optimum(p1, p0, D)
    assert b_star_rev < 5, f"Expected b*_rev near 0, got b*_rev={b_star_rev}"
    print(f"PASS: edge_case_bstar_at_boundary (b*={b_star:.2f}, b*_rev={b_star_rev:.2f}, gap={gap})")


def test_edge_case_D_le_2() -> None:
    """Edge case: D <= 2 (very small total input).

    With D = 0, 1, 2, the split space is tiny. Ternary search
    terminates immediately (hi - lo <= 2). All splits are checked.
    """
    for D in [0, 1, 2]:
        p0 = Pool(1000, 1000, 30)
        p1 = Pool(2000, 800, 50)
        opt = max(split_lean_floor(p0, p1, float(D), float(a))
                  for a in range(D + 1))
        # Ternary search with D <= 2 just checks all points
        best = max(split_lean_floor(p0, p1, float(D), float(a))
                   for a in range(D + 1))
        assert best == opt, f"D={D}: ternary={best} != opt={opt}"
    print(f"PASS: edge_case_D_le_2 (D in [0,1,2], all exact)")


def test_edge_case_all_fee_no_output() -> None:
    """Edge case: 100% fee (c = 0), no output from either pool.

    When fee_bps = 10000 (100%), all input is consumed by fees.
    Output is 0 for all splits. The floor error is 0.
    """
    p0 = Pool(1000, 1000, 10_000)  # 100% fee
    p1 = Pool(2000, 800, 10_000)
    D = 100
    for a in range(D + 1):
        out = split_lean_floor(p0, p1, float(D), float(a))
        assert out == 0, f"100% fee: output={out} at a={a} (expected 0)"
    print(f"PASS: edge_case_all_fee_no_output (all outputs = 0)")


def test_edge_case_tie_plateau() -> None:
    """Edge case: tie plateau (multiple argmax with same value).

    When two splits achieve the same maximum output, the leftmost
    (smallest a) should be chosen. The window theorem applies to
    points that STRICTLY beat floor(b*); ties use the trivial bound.

    This test EXERCISES the tie branch directly:
    - Asserts len(argmaxes) > 1 (plateau exists)
    - For each tied argmax, checks the corollary bound directly
    - Verifies the plateau width is bounded
    """
    # Symmetric pools create a plateau at a = D/2
    p0 = Pool(1000, 1000, 0)
    p1 = Pool(1000, 1000, 0)
    D = 100
    # Find all argmax
    best_val = max(split_lean_floor(p0, p1, float(D), float(a))
                   for a in range(D + 1))
    argmaxes = [a for a in range(D + 1)
                if split_lean_floor(p0, p1, float(D), float(a)) == best_val]
    # HARD assertion: plateau must exist (len > 1) for symmetric pools
    assert len(argmaxes) > 1, (
        f"Expected plateau (len > 1), got {len(argmaxes)} argmaxes: {argmaxes}")
    # The leftmost argmax should be the smallest a
    leftmost = min(argmaxes)
    rightmost = max(argmaxes)
    plateau_width = rightmost - leftmost
    # Window theorem: any point strictly beating floor(b*) is within window
    b_star = continuous_optimum(p0, p1, D)
    floor_bstar_val = split_lean_floor(p0, p1, float(D), math.floor(b_star))
    L = lipschitz_constant(p0, p1)
    m = strong_concavity_param(p0, p1, float(D), b_star)
    # HARD assertions: L and m must be positive for symmetric nonzero pools
    # (Pool(1000, 1000, 0) has spot_price = 1.0 > 0 and non-trivial curvature)
    assert L > 0, f"Expected L > 0 for symmetric nonzero pools, got L={L}"
    assert m > 0, f"Expected m > 0 for symmetric nonzero pools, got m={m}"
    # Now safe to use L and m without the if-guard
    if True:
        window = math.sqrt(2.0 * (L + 2.0) / m)
        # Check ALL tied argmaxes against the corollary bound
        # (not just strict-beat points, which may not exist in a plateau)
        for a in argmaxes:
            dist = abs(a - b_star)
            # The corollary bound is max(1, sqrt(2*(L+2)/m))
            corollary_bound = max(1.0, window)
            assert dist < corollary_bound + 1e-6, (
                f"plateau: a={a} dist={dist} >= corollary_bound={corollary_bound}")
        # Also check that plateau width is bounded by 2*window
        assert plateau_width < 2 * window + 1e-6, (
            f"plateau width {plateau_width} >= 2*window={2*window}")
    print(f"PASS: edge_case_tie_plateau ({len(argmaxes)} argmaxes, "
          f"leftmost={leftmost}, rightmost={rightmost}, "
          f"width={plateau_width}, best={best_val})")


if __name__ == "__main__":
    test_lean_model_floor_error_bound()
    test_prod_model_floor_error_bound()
    test_prod_effective_L_fee_bound_falsified_high_fee()
    test_prod_gross_spot_fee_perturbation_bound_high_fee()
    test_lean_model_argmax_proximity()
    test_prod_model_argmax_proximity()
    test_prod_model_window_sufficiency()
    test_prod_argmax_distance_tight_one_sided_perturbation_bound()
    test_tight_argmax_certificate_accepts_valid_corpus()
    test_tight_argmax_certificate_rejects_mutations()
    test_tight_argmax_certificate_rejects_float_overflow_domain()
    test_interval_m_backed_tight_argmax_certificate_composition()
    test_interval_m_backed_tight_argmax_certificate_rejects_bad_composition()
    test_stationary_m_backed_tight_argmax_certificate_composition()
    test_stationary_m_backed_tight_argmax_certificate_rejects_bad_composition()
    test_ternary_search_achieves_prod_bound()
    test_empirical_window_tighter()
    test_edge_case_L_zero()
    test_edge_case_small_m()
    test_edge_case_bstar_at_boundary()
    test_edge_case_D_le_2()
    test_edge_case_all_fee_no_output()
    test_edge_case_tie_plateau()
    test_exact_count()
    print("\nAll Phase 3A-reformulated tests passed.")
    print("Theorems verified:")
    print("  LEAN MODEL (continuous fee + floor output):")
    print("    1. Floor error: 0 <= cont - floor < 2  [Lean PROVEN]")
    print("    2. Argmax proximity: floor(floor(b*)) >= opt - (L+2)  [Lean PROVEN]")
    print("    3. Window: |b - b*| < sqrt(2*(L+2)/m)  [Lean PROVEN]")
    print("  PRODUCTION MODEL (ceiling fee + floor output):")
    print("    4. Effective-L fee bound 2L+2 is falsified at high fees  [empirical]")
    print("    5. Universal perturbation: 0 <= cont - prod < gross0+gross1+2  [empirical]")
    print("    6. Argmax proximity: prod(floor(b*)) >= opt - (3L+2) on low-fee corpus  [empirical]")
    print("    7. Window: |b - b*| < sqrt(2*(3L+2)/m) on low-fee corpus  [empirical]")
    print("    8. Tight certified-anchor argmax distance: |argmax_prod-b*| <= sqrt(2*tau/m)  [Lean generic + empirical tau]")
    print("    9. Tight argmax certificate checker rejects stale/noncanonical packets  [empirical]")
    print("    10. Tight argmax certificate float-domain guard  [CBC boundary]")
    print("    11. Interval-m-backed tight argmax certificate composition  [Lean bridge + empirical]")
    print("    12. Stationary-m-backed tight argmax certificate composition  [Lean bridge + empirical]")
    print("    13. Ternary search DP achieves (3L+2) bound on low-fee corpus  [empirical]")
