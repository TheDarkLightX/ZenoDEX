"""
Pool state management for DEX pools.
"""

from __future__ import annotations

import hashlib
from collections.abc import Mapping
from dataclasses import dataclass
from enum import Enum
from typing import Optional, Tuple

from .balances import Amount, AssetId
from .canonical import canonical_json_bytes

CURVE_TAG_CPMM = "CPMM"
CURVE_TAG_CUBIC_SUM_V1 = "CUBIC_SUM_V1"
CURVE_TAG_SUM_BOOST_V1 = "SUM_BOOST_V1"
CURVE_TAG_QUARTIC_BLEND_V1 = "QUARTIC_BLEND_V1"
CURVE_TAG_QUINTIC_BLEND_V1 = "QUINTIC_BLEND_V1"


@dataclass(frozen=True)
class _CurveParamSpec:
    name: str
    default: int
    minimum: int
    minimum_label: str


def _canonical_curve_params(params: dict[str, int]) -> str:
    return canonical_json_bytes(params).decode("utf-8")


def _decode_curve_params_for_tag(
    *,
    tag: str,
    curve_params: Optional[object],
    default: dict[str, int],
) -> Mapping[object, object]:
    params_obj: object = default if curve_params is None else curve_params
    if isinstance(params_obj, str):
        import json

        try:
            params_obj = json.loads(params_obj)
        except json.JSONDecodeError as exc:
            raise ValueError(f"invalid curve_params JSON for {tag}: {exc}") from exc
    if not isinstance(params_obj, Mapping):
        raise ValueError(f"curve_params for {tag} must be a JSON object")
    return params_obj


def _curve_param_int(
    params: Mapping[object, object],
    *,
    tag: str,
    spec: _CurveParamSpec,
) -> int:
    value = params.get(spec.name, spec.default)
    if not isinstance(value, int) or isinstance(value, bool) or value < spec.minimum:
        raise ValueError(f"{tag} param {spec.name} must be a {spec.minimum_label} int")
    return int(value)


def _normalize_non_negative_rational(c_num: int, c_den: int) -> Tuple[int, int]:
    # Canonicalize equivalent rational params before pool_id hashing.
    if c_num == 0:
        return 0, 1

    import math

    gcd = math.gcd(c_num, c_den)
    if gcd <= 1:
        return c_num, c_den
    return c_num // gcd, c_den // gcd


def _normalize_cubic_sum_curve_params(tag: str, curve_params: Optional[object]) -> str:
    params_obj = _decode_curve_params_for_tag(
        tag=tag, curve_params=curve_params, default={"p": 1, "q": 1}
    )
    p = _curve_param_int(
        params_obj,
        tag=tag,
        spec=_CurveParamSpec(name="p", default=1, minimum=1, minimum_label="positive"),
    )
    q = _curve_param_int(
        params_obj,
        tag=tag,
        spec=_CurveParamSpec(name="q", default=1, minimum=1, minimum_label="positive"),
    )
    return _canonical_curve_params({"p": p, "q": q})


def _normalize_sum_boost_curve_params(tag: str, curve_params: Optional[object]) -> str:
    params_obj = _decode_curve_params_for_tag(
        tag=tag,
        curve_params=curve_params,
        default={"mu_num": 200, "mu_den": 10_000},
    )
    mu_num = _curve_param_int(
        params_obj,
        tag=tag,
        spec=_CurveParamSpec(name="mu_num", default=200, minimum=0, minimum_label="non-negative"),
    )
    mu_den = _curve_param_int(
        params_obj,
        tag=tag,
        spec=_CurveParamSpec(name="mu_den", default=10_000, minimum=1, minimum_label="positive"),
    )
    return _canonical_curve_params({"mu_den": mu_den, "mu_num": mu_num})


def _normalize_quartic_blend_curve_params(tag: str, curve_params: Optional[object]) -> str:
    params_obj = _decode_curve_params_for_tag(
        tag=tag, curve_params=curve_params, default={"c_num": 8, "c_den": 1}
    )
    c_num = _curve_param_int(
        params_obj,
        tag=tag,
        spec=_CurveParamSpec(name="c_num", default=8, minimum=0, minimum_label="non-negative"),
    )
    c_den = _curve_param_int(
        params_obj,
        tag=tag,
        spec=_CurveParamSpec(name="c_den", default=1, minimum=1, minimum_label="positive"),
    )
    c_num_norm, c_den_norm = _normalize_non_negative_rational(c_num, c_den)
    return _canonical_curve_params({"c_den": c_den_norm, "c_num": c_num_norm})


def _normalize_quintic_blend_curve_params(tag: str, curve_params: Optional[object]) -> str:
    params_obj = _decode_curve_params_for_tag(
        tag=tag, curve_params=curve_params, default={"c_num": 2, "c_den": 1}
    )
    c_num = _curve_param_int(
        params_obj,
        tag=tag,
        spec=_CurveParamSpec(name="c_num", default=2, minimum=0, minimum_label="non-negative"),
    )
    c_den = _curve_param_int(
        params_obj,
        tag=tag,
        spec=_CurveParamSpec(name="c_den", default=1, minimum=1, minimum_label="positive"),
    )
    c_num_norm, c_den_norm = _normalize_non_negative_rational(c_num, c_den)
    return _canonical_curve_params({"c_den": c_den_norm, "c_num": c_num_norm})


def normalize_curve_config(
    *, curve_tag: Optional[object], curve_params: Optional[object]
) -> Tuple[str, str]:
    """
    Normalize and validate curve configuration.

    - Tags are canonicalized to upper-case.
    - CPMM uses the empty params string to preserve historical pool_ids.
    - Cubic-sum v1 uses canonical JSON params: {"p": <int>, "q": <int>}.
    - Sum-boost v1 uses canonical JSON params: {"mu_num": <int>, "mu_den": <int>}.
    - Quartic-blend v1 uses canonical JSON params: {"c_num": <int>, "c_den": <int>}.
    - Quintic-blend v1 uses canonical JSON params: {"c_num": <int>, "c_den": <int>}.
    """
    tag_raw = CURVE_TAG_CPMM if curve_tag is None else curve_tag
    if not isinstance(tag_raw, str) or not tag_raw.strip():
        raise ValueError("curve_tag must be a non-empty string")
    tag = tag_raw.strip().upper()

    if tag == CURVE_TAG_CPMM:
        if curve_params not in (None, "", {}):
            raise ValueError("CPMM pools must not specify curve_params")
        return CURVE_TAG_CPMM, ""

    if tag == CURVE_TAG_CUBIC_SUM_V1:
        return CURVE_TAG_CUBIC_SUM_V1, _normalize_cubic_sum_curve_params(tag, curve_params)

    if tag == CURVE_TAG_SUM_BOOST_V1:
        return CURVE_TAG_SUM_BOOST_V1, _normalize_sum_boost_curve_params(tag, curve_params)

    if tag == CURVE_TAG_QUARTIC_BLEND_V1:
        return CURVE_TAG_QUARTIC_BLEND_V1, _normalize_quartic_blend_curve_params(tag, curve_params)

    if tag == CURVE_TAG_QUINTIC_BLEND_V1:
        return CURVE_TAG_QUINTIC_BLEND_V1, _normalize_quintic_blend_curve_params(tag, curve_params)

    raise ValueError(f"unsupported curve_tag: {tag!r}")


def parse_cubic_sum_params(curve_params: str) -> Tuple[int, int]:
    """
    Parse (p,q) from a canonical JSON params string.
    """
    import json

    if not isinstance(curve_params, str):
        raise TypeError("curve_params must be a string")
    try:
        obj = json.loads(curve_params)
    except json.JSONDecodeError as exc:
        raise ValueError(f"invalid curve_params JSON: {exc}") from exc
    if not isinstance(obj, dict):
        raise ValueError("curve_params must decode to a JSON object")
    p = obj.get("p")
    q = obj.get("q")
    if not isinstance(p, int) or isinstance(p, bool) or p <= 0:
        raise ValueError("curve_params.p must be a positive int")
    if not isinstance(q, int) or isinstance(q, bool) or q <= 0:
        raise ValueError("curve_params.q must be a positive int")
    return int(p), int(q)


def parse_sum_boost_params(curve_params: str) -> Tuple[int, int]:
    """
    Parse (mu_num, mu_den) from a canonical JSON params string.
    """
    import json

    if not isinstance(curve_params, str):
        raise TypeError("curve_params must be a string")
    try:
        obj = json.loads(curve_params)
    except json.JSONDecodeError as exc:
        raise ValueError(f"invalid curve_params JSON: {exc}") from exc
    if not isinstance(obj, dict):
        raise ValueError("curve_params must decode to a JSON object")
    mu_num = obj.get("mu_num")
    mu_den = obj.get("mu_den")
    if not isinstance(mu_num, int) or isinstance(mu_num, bool) or mu_num < 0:
        raise ValueError("curve_params.mu_num must be a non-negative int")
    if not isinstance(mu_den, int) or isinstance(mu_den, bool) or mu_den <= 0:
        raise ValueError("curve_params.mu_den must be a positive int")
    return int(mu_num), int(mu_den)


def parse_quartic_blend_params(curve_params: str) -> Tuple[int, int]:
    """
    Parse (c_num, c_den) from a canonical JSON params string.
    """
    import json

    if not isinstance(curve_params, str):
        raise TypeError("curve_params must be a string")
    try:
        obj = json.loads(curve_params)
    except json.JSONDecodeError as exc:
        raise ValueError(f"invalid curve_params JSON: {exc}") from exc
    if not isinstance(obj, dict):
        raise ValueError("curve_params must decode to a JSON object")
    c_num = obj.get("c_num")
    c_den = obj.get("c_den")
    if not isinstance(c_num, int) or isinstance(c_num, bool) or c_num < 0:
        raise ValueError("curve_params.c_num must be a non-negative int")
    if not isinstance(c_den, int) or isinstance(c_den, bool) or c_den <= 0:
        raise ValueError("curve_params.c_den must be a positive int")
    return int(c_num), int(c_den)


def parse_quintic_blend_params(curve_params: str) -> Tuple[int, int]:
    """
    Parse (c_num, c_den) from a canonical JSON params string.
    """
    import json

    if not isinstance(curve_params, str):
        raise TypeError("curve_params must be a string")
    try:
        obj = json.loads(curve_params)
    except json.JSONDecodeError as exc:
        raise ValueError(f"invalid curve_params JSON: {exc}") from exc
    if not isinstance(obj, dict):
        raise ValueError("curve_params must decode to a JSON object")
    c_num = obj.get("c_num")
    c_den = obj.get("c_den")
    if not isinstance(c_num, int) or isinstance(c_num, bool) or c_num < 0:
        raise ValueError("curve_params.c_num must be a non-negative int")
    if not isinstance(c_den, int) or isinstance(c_den, bool) or c_den <= 0:
        raise ValueError("curve_params.c_den must be a positive int")
    return int(c_num), int(c_den)


class PoolStatus(Enum):
    """Pool status enumeration."""

    ACTIVE = "ACTIVE"
    FROZEN = "FROZEN"
    DISABLED = "DISABLED"


def canonical_pool_asset_id(asset: AssetId) -> AssetId:
    """
    Canonicalize hex asset identifiers before hashing pool IDs.

    Symbolic test assets such as "A"/"B" stay byte-for-byte unchanged; only
    0x-prefixed hex IDs are normalized so Python and Rust cannot fork on case.
    """
    if not isinstance(asset, str):
        raise TypeError("asset ids must be strings")
    if len(asset) < 3 or asset[:2].lower() != "0x":
        return asset
    body = asset[2:]
    if not body or any(ch not in "0123456789abcdefABCDEF" for ch in body):
        return asset
    return "0x" + body.lower()


def _require_strict_int(name: str, value: object) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    return int(value)


def compute_pool_id(
    asset0: AssetId,
    asset1: AssetId,
    fee_bps: int,
    *,
    curve_tag: str = "CPMM",
    curve_params: str = "",
) -> str:
    """
    Deterministically compute a pool_id for the given pool parameters.

    Matches the formula described in `src/core/liquidity.py`.
    """
    asset0_hash = canonical_pool_asset_id(asset0)
    asset1_hash = canonical_pool_asset_id(asset1)
    if asset0_hash >= asset1_hash:
        raise ValueError(f"Assets must be in canonical order: {asset0} < {asset1}")
    fee_bps_i = _require_strict_int("fee_bps", fee_bps)
    if not (0 <= fee_bps_i <= 10000):
        raise ValueError(f"fee_bps must be in [0, 10000]: {fee_bps}")
    if not isinstance(curve_tag, str) or not curve_tag:
        raise ValueError("curve_tag must be a non-empty string")
    if not isinstance(curve_params, str):
        raise ValueError("curve_params must be a string")

    pool_id_data = (
        b"TauSwapPool"
        + asset0_hash.encode("utf-8")
        + asset1_hash.encode("utf-8")
        + str(fee_bps_i).encode("utf-8")
        + curve_tag.encode("utf-8")
        + curve_params.encode("utf-8")
    )
    return "0x" + hashlib.sha256(pool_id_data).hexdigest()


@dataclass
class PoolState:
    """
    State of a DEX liquidity pool.

    Attributes:
        pool_id: 32-byte pool identifier (hex string)
        asset0: First asset identifier (must be < asset1 lexicographically)
        asset1: Second asset identifier
        reserve0: Reserve amount for asset0
        reserve1: Reserve amount for asset1
        fee_bps: Fee in basis points (0-10000)
        curve_tag: Curve family identifier ("CPMM", "CUBIC_SUM_V1", ...)
        curve_params: Curve parameter string (curve-specific, canonicalized)
        lp_supply: Total LP token supply
        status: Pool status
        created_at: Block height or timestamp when pool was created
    """

    pool_id: str
    asset0: AssetId
    asset1: AssetId
    reserve0: Amount
    reserve1: Amount
    fee_bps: int
    lp_supply: Amount
    status: PoolStatus
    created_at: int
    curve_tag: str = CURVE_TAG_CPMM
    curve_params: str = ""

    def __setattr__(self, name: str, value: object) -> None:
        if self.__dict__.get("_snapshot_sealed", False):
            raise TypeError("committed pool snapshot is immutable")
        object.__setattr__(self, name, value)

    def __post_init__(self):
        """Validate pool state invariants."""
        if not isinstance(self.pool_id, str) or not self.pool_id:
            raise TypeError("pool_id must be a non-empty string")
        if not isinstance(self.asset0, str) or not isinstance(self.asset1, str):
            raise TypeError("asset ids must be strings")

        # Pool IDs hash canonical asset text, so stored state must use the same
        # text before order checks or state-root encoders observe it.
        self.asset0 = canonical_pool_asset_id(self.asset0)
        self.asset1 = canonical_pool_asset_id(self.asset1)

        # Ensure canonical ordering
        if self.asset0 >= self.asset1:
            raise ValueError(f"Assets must be in canonical order: {self.asset0} < {self.asset1}")

        self.reserve0 = _require_strict_int("reserve0", self.reserve0)
        self.reserve1 = _require_strict_int("reserve1", self.reserve1)
        self.fee_bps = _require_strict_int("fee_bps", self.fee_bps)
        self.lp_supply = _require_strict_int("lp_supply", self.lp_supply)
        self.created_at = _require_strict_int("created_at", self.created_at)

        # Validate fee_bps
        if not (0 <= self.fee_bps <= 10000):
            raise ValueError(f"fee_bps must be in [0, 10000]: {self.fee_bps}")

        # Normalize curve config (fail-closed on unknown curves).
        tag, params = normalize_curve_config(
            curve_tag=self.curve_tag, curve_params=self.curve_params
        )
        self.curve_tag = tag
        self.curve_params = params

        # Validate non-negative reserves
        if self.reserve0 < 0 or self.reserve1 < 0:
            raise ValueError(f"Reserves must be non-negative: ({self.reserve0}, {self.reserve1})")

        # Validate non-negative LP supply
        if self.lp_supply < 0:
            raise ValueError(f"LP supply must be non-negative: {self.lp_supply}")
        if self.created_at < 0:
            raise ValueError(f"created_at must be non-negative: {self.created_at}")

    def get_reserve(self, asset: AssetId) -> Amount:
        """
        Get reserve for a specific asset.

        Args:
            asset: Asset identifier

        Returns:
            Reserve amount

        Raises:
            ValueError: If asset is not in this pool
        """
        if asset == self.asset0:
            return self.reserve0
        elif asset == self.asset1:
            return self.reserve1
        else:
            raise ValueError(f"Asset {asset} not in pool {self.pool_id}")

    def get_constant_product(self) -> int:
        """
        Compute k = reserve0 * reserve1 (CPMM constant).

        Returns:
            Constant product k
        """
        return self.reserve0 * self.reserve1

    def verify_invariant(self, min_k: int = 0) -> bool:
        """
        Verify CPMM invariant: reserve0 * reserve1 >= min_k.

        Args:
            min_k: Minimum allowed constant product

        Returns:
            True if invariant holds
        """
        k = self.get_constant_product()
        return k >= min_k

    def __repr__(self) -> str:
        return (
            f"PoolState(pool_id={self.pool_id[:16]}..., "
            f"assets=({self.asset0[:8]}..., {self.asset1[:8]}...), "
            f"reserves=({self.reserve0}, {self.reserve1}), "
            f"lp_supply={self.lp_supply}, status={self.status.value})"
        )


def copy_pool_state(source: PoolState) -> PoolState:
    """Return a fresh mutable scratch copy of one pool value.

    ``dataclasses.replace(source)`` preserves subclasses. That is unsafe when
    ``source`` is an immutable committed snapshot and the caller needs local
    mutation during settlement replay. Constructing the exact scratch type
    makes the committed-to-scratch boundary explicit.
    """

    if not isinstance(source, PoolState):
        raise TypeError("source must be a PoolState")
    return PoolState(
        pool_id=source.pool_id,
        asset0=source.asset0,
        asset1=source.asset1,
        reserve0=source.reserve0,
        reserve1=source.reserve1,
        fee_bps=source.fee_bps,
        lp_supply=source.lp_supply,
        status=source.status,
        created_at=source.created_at,
        curve_tag=source.curve_tag,
        curve_params=source.curve_params,
    )
