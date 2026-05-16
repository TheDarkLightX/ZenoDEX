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
    try:
        return API_SURFACE_PROFILES[str(profile_id)]
    except KeyError as exc:
        allowed = ", ".join(api_surface_profile_ids())
        raise ValueError(f"unknown API surface profile: {profile_id!r}; expected one of: {allowed}") from exc


def api_surface_profile_violations(
    *,
    profile_id: str,
    demo_api_token: str,
    perps_enabled: bool,
    zusd_enabled: bool,
    dex_enabled: bool,
) -> tuple[str, ...]:
    """Return reasons an API server posture must not start."""

    profile = get_api_surface_profile(profile_id)
    demo_enabled = bool(perps_enabled or zusd_enabled or dex_enabled)
    reasons: list[str] = []
    if demo_enabled and not profile.allow_demo_routes:
        reasons.append(f"{profile.profile_id} forbids demo/value-moving API routes")
    if demo_enabled and profile.require_token_for_demo_routes and not str(demo_api_token or ""):
        reasons.append(f"{profile.profile_id} requires DEMO_API_TOKEN for demo/value-moving API routes")
    return tuple(reasons)


def validate_api_surface_profile(
    *,
    profile_id: str,
    demo_api_token: str,
    perps_enabled: bool,
    zusd_enabled: bool,
    dex_enabled: bool,
) -> tuple[bool, str | None]:
    reasons = api_surface_profile_violations(
        profile_id=profile_id,
        demo_api_token=demo_api_token,
        perps_enabled=perps_enabled,
        zusd_enabled=zusd_enabled,
        dex_enabled=dex_enabled,
    )
    if reasons:
        return False, "; ".join(reasons)
    return True, None
