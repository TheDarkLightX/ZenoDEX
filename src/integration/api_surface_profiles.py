"""API surface admission profiles for the stdlib HTTP server."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Literal

API_SURFACE_PROFILE_LOCAL_DEMO = "local-demo"
API_SURFACE_PROFILE_PUBLIC_TESTNET = "public-testnet"
API_SURFACE_PROFILE_PRODUCTION_STRICT = "production-strict"

ApiSurfaceProfileId = Literal["local-demo", "public-testnet", "production-strict"]


@dataclass(frozen=True)
class ApiSurfaceProfile:
    profile_id: ApiSurfaceProfileId
    allow_demo_routes: bool
    require_token_for_demo_routes: bool


API_SURFACE_PROFILES: dict[str, ApiSurfaceProfile] = {
    API_SURFACE_PROFILE_LOCAL_DEMO: ApiSurfaceProfile(
        profile_id=API_SURFACE_PROFILE_LOCAL_DEMO,
        allow_demo_routes=True,
        require_token_for_demo_routes=False,
    ),
    API_SURFACE_PROFILE_PUBLIC_TESTNET: ApiSurfaceProfile(
        profile_id=API_SURFACE_PROFILE_PUBLIC_TESTNET,
        allow_demo_routes=True,
        require_token_for_demo_routes=True,
    ),
    API_SURFACE_PROFILE_PRODUCTION_STRICT: ApiSurfaceProfile(
        profile_id=API_SURFACE_PROFILE_PRODUCTION_STRICT,
        allow_demo_routes=False,
        require_token_for_demo_routes=True,
    ),
}


def api_surface_profile_ids() -> tuple[str, ...]:
    return tuple(API_SURFACE_PROFILES.keys())


def get_api_surface_profile(profile_id: str) -> ApiSurfaceProfile:
    if not isinstance(profile_id, str):
        raise TypeError(f"API surface profile id must be a string, got {type(profile_id).__name__}")
    if profile_id != profile_id.strip() or not profile_id:
        raise ValueError("API surface profile id must be non-empty and whitespace-trimmed")
    try:
        return API_SURFACE_PROFILES[profile_id]
    except KeyError as exc:
        allowed = ", ".join(api_surface_profile_ids())
        raise ValueError(f"unknown API surface profile: {profile_id!r}; expected one of: {allowed}") from exc


def _require_bool(value: object, *, field: str) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{field} must be a bool, got {type(value).__name__}")
    return value


def api_surface_profile_violations(
    *,
    profile_id: str,
    demo_api_token: str,
    perps_enabled: bool,
    zusd_enabled: bool,
    dex_enabled: bool,
    confidential_enabled: bool = False,
) -> tuple[str, ...]:
    """Return reasons an API server posture must not start."""

    profile = get_api_surface_profile(profile_id)
    if not isinstance(demo_api_token, str):
        raise TypeError(f"demo_api_token must be a string, got {type(demo_api_token).__name__}")
    perps_flag = _require_bool(perps_enabled, field="perps_enabled")
    zusd_flag = _require_bool(zusd_enabled, field="zusd_enabled")
    dex_flag = _require_bool(dex_enabled, field="dex_enabled")
    confidential_flag = _require_bool(confidential_enabled, field="confidential_enabled")
    demo_enabled = perps_flag or zusd_flag or dex_flag or confidential_flag
    reasons: list[str] = []
    if demo_enabled and not profile.allow_demo_routes:
        reasons.append(f"{profile.profile_id} forbids demo/value-moving API routes")
    if demo_enabled and profile.require_token_for_demo_routes and not demo_api_token:
        reasons.append(f"{profile.profile_id} requires an API bearer token for demo/value-moving API routes")
    return tuple(reasons)


def validate_api_surface_profile(
    *,
    profile_id: str,
    demo_api_token: str,
    perps_enabled: bool,
    zusd_enabled: bool,
    dex_enabled: bool,
    confidential_enabled: bool = False,
) -> tuple[bool, str | None]:
    reasons = api_surface_profile_violations(
        profile_id=profile_id,
        demo_api_token=demo_api_token,
        perps_enabled=perps_enabled,
        zusd_enabled=zusd_enabled,
        dex_enabled=dex_enabled,
        confidential_enabled=confidential_enabled,
    )
    if reasons:
        return False, "; ".join(reasons)
    return True, None
