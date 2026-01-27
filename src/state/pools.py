"""
Pool state management for DEX pools.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Optional, Tuple

import hashlib

from .balances import AssetId, Amount
from .canonical import canonical_json_bytes


CURVE_TAG_CPMM = "CPMM"
CURVE_TAG_CUBIC_SUM_V1 = "CUBIC_SUM_V1"
CURVE_TAG_SUM_BOOST_V1 = "SUM_BOOST_V1"
CURVE_TAG_QUARTIC_BLEND_V1 = "QUARTIC_BLEND_V1"
CURVE_TAG_QUINTIC_BLEND_V1 = "QUINTIC_BLEND_V1"


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
        if not isinstance(params_obj, dict):
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
        if not isinstance(params_obj, dict):
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
        if not isinstance(params_obj, dict):
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
        if not isinstance(params_obj, dict):
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
    if asset0 >= asset1:
        raise ValueError(f"Assets must be in canonical order: {asset0} < {asset1}")
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
    
    def __post_init__(self):
        """Validate pool state invariants."""
        # Ensure canonical ordering
        if self.asset0 >= self.asset1:
            raise ValueError(
                f"Assets must be in canonical order: {self.asset0} < {self.asset1}"
            )
        
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
