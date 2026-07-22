"""
Pool state management for DEX pools.
"""

from __future__ import annotations

import hashlib
from collections.abc import Mapping
from dataclasses import dataclass, field
from enum import Enum
from typing import Optional, Tuple

from .balances import Amount, AssetId
from .canonical import canonical_hex_fixed_allow_0x, canonical_json_bytes

CURVE_TAG_CPMM = "CPMM"
CURVE_TAG_CUBIC_SUM_V1 = "CUBIC_SUM_V1"
CURVE_TAG_SUM_BOOST_V1 = "SUM_BOOST_V1"
CURVE_TAG_QUARTIC_BLEND_V1 = "QUARTIC_BLEND_V1"
CURVE_TAG_QUINTIC_BLEND_V1 = "QUINTIC_BLEND_V1"


def _canonical_asset_id_if_hex(asset: AssetId, *, name: str) -> AssetId:
    """Canonicalize real 32-byte asset IDs while preserving symbolic test IDs."""
    if not isinstance(asset, str):
        raise TypeError(f"{name} must be a string")
    if asset.strip().lower().startswith("0x"):
        return canonical_hex_fixed_allow_0x(asset, nbytes=32, name=name)
    return asset


def _asset_order_bytes(asset: AssetId) -> bytes | None:
    if not isinstance(asset, str) or not asset.startswith("0x") or len(asset) != 66:
        return None
    try:
        return bytes.fromhex(asset[2:])
    except ValueError:
        return None


def normalize_pool_asset_pair(asset0: AssetId, asset1: AssetId) -> tuple[AssetId, AssetId]:
    """
    Normalize and validate a pool asset pair.

    Real 32-byte hex asset IDs are lowercased and ordered by decoded bytes, which
    matches the state-root/Rust commitment boundary. Non-hex symbolic IDs are
    kept for older algorithm tests and ordered by the legacy string rule.
    """
    asset0_norm = _canonical_asset_id_if_hex(asset0, name="asset0")
    asset1_norm = _canonical_asset_id_if_hex(asset1, name="asset1")
    asset0_b = _asset_order_bytes(asset0_norm)
    asset1_b = _asset_order_bytes(asset1_norm)
    if asset0_b is not None and asset1_b is not None:
        if asset0_b >= asset1_b:
            raise ValueError(f"Assets must be in canonical order: {asset0_norm} < {asset1_norm}")
        return asset0_norm, asset1_norm
    if asset0_norm >= asset1_norm:
        raise ValueError(f"Assets must be in canonical order: {asset0_norm} < {asset1_norm}")
    return asset0_norm, asset1_norm


def normalize_curve_config(*, curve_tag: Optional[object], curve_params: Optional[object]) -> Tuple[str, str]:
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
        params_obj: object = curve_params
        if params_obj is None:
            params_obj = {"p": 1, "q": 1}
        if isinstance(params_obj, str):
            import json

            try:
                params_obj = json.loads(params_obj)
            except Exception as exc:
                raise ValueError(f"invalid curve_params JSON for {tag}: {exc}") from exc
        if not isinstance(params_obj, Mapping):
            raise ValueError(f"curve_params for {tag} must be a JSON object")
        p = params_obj.get("p", 1)
        q = params_obj.get("q", 1)
        if not isinstance(p, int) or isinstance(p, bool) or p <= 0:
            raise ValueError(f"{tag} param p must be a positive int")
        if not isinstance(q, int) or isinstance(q, bool) or q <= 0:
            raise ValueError(f"{tag} param q must be a positive int")
        params_norm = {"p": int(p), "q": int(q)}
        return CURVE_TAG_CUBIC_SUM_V1, canonical_json_bytes(params_norm).decode("utf-8")

    if tag == CURVE_TAG_SUM_BOOST_V1:
        params_obj: object = curve_params
        if params_obj is None:
            params_obj = {"mu_num": 200, "mu_den": 10_000}
        if isinstance(params_obj, str):
            import json

            try:
                params_obj = json.loads(params_obj)
            except Exception as exc:
                raise ValueError(f"invalid curve_params JSON for {tag}: {exc}") from exc
        if not isinstance(params_obj, Mapping):
            raise ValueError(f"curve_params for {tag} must be a JSON object")
        mu_num = params_obj.get("mu_num", 200)
        mu_den = params_obj.get("mu_den", 10_000)
        if not isinstance(mu_num, int) or isinstance(mu_num, bool) or mu_num < 0:
            raise ValueError(f"{tag} param mu_num must be a non-negative int")
        if not isinstance(mu_den, int) or isinstance(mu_den, bool) or mu_den <= 0:
            raise ValueError(f"{tag} param mu_den must be a positive int")
        params_norm = {"mu_den": int(mu_den), "mu_num": int(mu_num)}
        return CURVE_TAG_SUM_BOOST_V1, canonical_json_bytes(params_norm).decode("utf-8")

    if tag == CURVE_TAG_QUARTIC_BLEND_V1:
        params_obj: object = curve_params
        if params_obj is None:
            # Default: c=8 is a conservative setting that reduces the frequency of large negative regressions vs CPMM
            # (at the cost of smaller average improvement).
            params_obj = {"c_num": 8, "c_den": 1}
        if isinstance(params_obj, str):
            import json

            try:
                params_obj = json.loads(params_obj)
            except Exception as exc:
                raise ValueError(f"invalid curve_params JSON for {tag}: {exc}") from exc
        if not isinstance(params_obj, Mapping):
            raise ValueError(f"curve_params for {tag} must be a JSON object")
        c_num = params_obj.get("c_num", 8)
        c_den = params_obj.get("c_den", 1)
        if not isinstance(c_num, int) or isinstance(c_num, bool) or c_num < 0:
            raise ValueError(f"{tag} param c_num must be a non-negative int")
        if not isinstance(c_den, int) or isinstance(c_den, bool) or c_den <= 0:
            raise ValueError(f"{tag} param c_den must be a positive int")

        import math

        c_num_i = int(c_num)
        c_den_i = int(c_den)
        if c_num_i == 0:
            c_den_i = 1
        else:
            g = math.gcd(c_num_i, c_den_i)
            if g > 1:
                c_num_i //= g
                c_den_i //= g
        params_norm = {"c_den": int(c_den_i), "c_num": int(c_num_i)}
        return CURVE_TAG_QUARTIC_BLEND_V1, canonical_json_bytes(params_norm).decode("utf-8")

    if tag == CURVE_TAG_QUINTIC_BLEND_V1:
        params_obj: object = curve_params
        if params_obj is None:
            # Default: c=2 => K(x,y)=x*y*(x+y)^3 (a stable, easy-to-reason-about special case).
            params_obj = {"c_num": 2, "c_den": 1}
        if isinstance(params_obj, str):
            import json

            try:
                params_obj = json.loads(params_obj)
            except Exception as exc:
                raise ValueError(f"invalid curve_params JSON for {tag}: {exc}") from exc
        if not isinstance(params_obj, Mapping):
            raise ValueError(f"curve_params for {tag} must be a JSON object")
        c_num = params_obj.get("c_num", 2)
        c_den = params_obj.get("c_den", 1)
        if not isinstance(c_num, int) or isinstance(c_num, bool) or c_num < 0:
            raise ValueError(f"{tag} param c_num must be a non-negative int")
        if not isinstance(c_den, int) or isinstance(c_den, bool) or c_den <= 0:
            raise ValueError(f"{tag} param c_den must be a positive int")
        # Canonicalize the rational to lowest terms so semantically identical params hash to the same pool_id.
        import math

        c_num_i = int(c_num)
        c_den_i = int(c_den)
        if c_num_i == 0:
            c_den_i = 1
        else:
            g = math.gcd(c_num_i, c_den_i)
            if g > 1:
                c_num_i //= g
                c_den_i //= g
        params_norm = {"c_den": int(c_den_i), "c_num": int(c_num_i)}
        return CURVE_TAG_QUINTIC_BLEND_V1, canonical_json_bytes(params_norm).decode("utf-8")

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
    except Exception as exc:
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
    except Exception as exc:
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
    except Exception as exc:
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
    except Exception as exc:
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
    asset0, asset1 = normalize_pool_asset_pair(asset0, asset1)
    if not (0 <= fee_bps <= 10000):
        raise ValueError(f"fee_bps must be in [0, 10000]: {fee_bps}")
    if not isinstance(curve_tag, str) or not curve_tag:
        raise ValueError("curve_tag must be a non-empty string")
    if not isinstance(curve_params, str):
        raise ValueError("curve_params must be a string")

    pool_id_data = (
        b"TauSwapPool"
        + asset0.encode("utf-8")
        + asset1.encode("utf-8")
        + str(int(fee_bps)).encode("utf-8")
        + curve_tag.encode("utf-8")
        + curve_params.encode("utf-8")
    )
    return "0x" + hashlib.sha256(pool_id_data).hexdigest()


def validate_pool_id_format(pool_id: object, *, allow_symbolic: bool) -> None:
    """Require a canonical 32-byte pool ID or an explicit local symbolic ID.

    Hex-looking values never fall through to symbolic compatibility. Production
    identifiers use exactly ``0x`` followed by 64 lowercase hex characters.
    """
    if not isinstance(allow_symbolic, bool):
        raise TypeError("allow_symbolic must be a bool")
    if not isinstance(pool_id, str):
        raise TypeError("pool_id must be a string")
    if not pool_id or pool_id != pool_id.strip():
        raise ValueError("pool_id must be non-empty and must not contain surrounding whitespace")

    try:
        canonical_pool_id = canonical_hex_fixed_allow_0x(
            pool_id,
            nbytes=32,
            name="pool_id",
        )
    except ValueError as exc:
        if pool_id.lower().startswith("0x"):
            raise ValueError(
                "pool_id must be a canonical lowercase 0x-prefixed 32-byte hex string"
            ) from exc
        if allow_symbolic:
            return
        raise ValueError(
            "pool_id must be a canonical lowercase 0x-prefixed 32-byte hex string"
        ) from exc

    if pool_id != canonical_pool_id:
        raise ValueError(
            "pool_id must be a canonical lowercase 0x-prefixed 32-byte hex string"
        )


@dataclass(slots=True)
class PoolState:
    """
    State of a DEX liquidity pool.
    
    Attributes:
        pool_id: Canonical parameter-bound 32-byte hex identifier. Symbolic
            values exist only for non-authoritative legacy compatibility.
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
    _snapshot_sealed: bool = field(default=False, init=False, repr=False, compare=False)

    def __setattr__(self, name: str, value: object) -> None:
        """Prevent base-descriptor writes through a sealed committed subtype."""

        if getattr(self, "_snapshot_sealed", False):
            raise TypeError("committed pool snapshot is immutable")
        object.__setattr__(self, name, value)
    
    def __post_init__(self):
        """Validate pool state invariants."""
        self.asset0, self.asset1 = normalize_pool_asset_pair(self.asset0, self.asset1)
        
        # Validate fee_bps
        if not (0 <= self.fee_bps <= 10000):
            raise ValueError(f"fee_bps must be in [0, 10000]: {self.fee_bps}")

        # Normalize curve config (fail-closed on unknown curves).
        tag, params = normalize_curve_config(curve_tag=self.curve_tag, curve_params=self.curve_params)
        self.curve_tag = tag
        self.curve_params = params

        # Validate non-negative reserves
        if self.reserve0 < 0 or self.reserve1 < 0:
            raise ValueError(
                f"Reserves must be non-negative: ({self.reserve0}, {self.reserve1})"
            )
        
        # Validate non-negative LP supply
        if self.lp_supply < 0:
            raise ValueError(f"LP supply must be non-negative: {self.lp_supply}")

        # Canonical hex IDs are authoritative and must bind the normalized pool
        # identity at construction. Symbolic legacy objects remain constructible
        # for local compatibility; snapshot/root boundaries reject them.
        validate_pool_identity(self, allow_symbolic=True)
    
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
    """Return an exact mutable scratch copy of one pool value.

    dataclasses.replace preserves subclasses. That is unsafe when a sealed
    committed pool is copied for local settlement mutation.
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


def validate_pool_identity(pool: PoolState, *, allow_symbolic: bool) -> None:
    """Bind a canonical pool ID to every parameter that defines pool identity."""
    if not isinstance(pool, PoolState):
        raise TypeError("pool must be a PoolState")
    validate_pool_id_format(pool.pool_id, allow_symbolic=allow_symbolic)

    try:
        canonical_hex_fixed_allow_0x(pool.pool_id, nbytes=32, name="pool_id")
    except ValueError:
        # ``validate_pool_id_format`` admits this branch only for an explicitly
        # enabled symbolic local/test identifier.
        return

    expected_pool_id = compute_pool_id(
        pool.asset0,
        pool.asset1,
        pool.fee_bps,
        curve_tag=pool.curve_tag,
        curve_params=pool.curve_params,
    )
    if pool.pool_id != expected_pool_id:
        raise ValueError(
            "pool_id does not match canonical pool identity: "
            f"expected={expected_pool_id} actual={pool.pool_id}"
        )
