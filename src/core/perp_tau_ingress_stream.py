from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping

REJECT_OK = "Ok"
REJECT_NO_PERP_STREAM = "NoPerpStream"
REJECT_LEGACY_DEX_CONFLICT = "LegacyDexConflict"
REJECT_LEGACY_LOOKS_LIKE_DEX = "LegacyLooksLikeDex"
REJECT_LEGACY_NOT_PERP = "LegacyNotPerp"


@dataclass(frozen=True)
class PerpTauIngressStreamOutcome:
    selected: bool
    upstream_stream_selected: bool
    legacy_fallback_used: bool
    reject_code: str
    checks: Mapping[str, bool]


def _require_bool(value: Any, *, name: str) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be a bool")
    return bool(value)


def evaluate_perp_tau_ingress_stream(
    *,
    upstream_stream_present: bool,
    legacy_stream_present: bool,
    legacy_dex_stream_present: bool,
    legacy_candidate_dex_like: bool,
    legacy_candidate_perp_like: bool,
) -> PerpTauIngressStreamOutcome:
    checks = {
        "upstream_stream_present": _require_bool(upstream_stream_present, name="upstream_stream_present"),
        "legacy_stream_present": _require_bool(legacy_stream_present, name="legacy_stream_present"),
        "legacy_dex_stream_present": _require_bool(legacy_dex_stream_present, name="legacy_dex_stream_present"),
        "legacy_candidate_dex_like": _require_bool(legacy_candidate_dex_like, name="legacy_candidate_dex_like"),
        "legacy_candidate_perp_like": _require_bool(legacy_candidate_perp_like, name="legacy_candidate_perp_like"),
    }
    upstream_selected = bool(checks["upstream_stream_present"])
    legacy_fallback_used = bool(
        not checks["upstream_stream_present"]
        and checks["legacy_stream_present"]
        and not checks["legacy_dex_stream_present"]
        and not checks["legacy_candidate_dex_like"]
        and checks["legacy_candidate_perp_like"]
    )
    if upstream_selected:
        reject_code = REJECT_OK
    elif not checks["legacy_stream_present"]:
        reject_code = REJECT_NO_PERP_STREAM
    elif checks["legacy_dex_stream_present"]:
        reject_code = REJECT_LEGACY_DEX_CONFLICT
    elif checks["legacy_candidate_dex_like"]:
        reject_code = REJECT_LEGACY_LOOKS_LIKE_DEX
    elif not checks["legacy_candidate_perp_like"]:
        reject_code = REJECT_LEGACY_NOT_PERP
    else:
        reject_code = REJECT_OK
    return PerpTauIngressStreamOutcome(
        selected=bool(upstream_selected or legacy_fallback_used),
        upstream_stream_selected=upstream_selected,
        legacy_fallback_used=legacy_fallback_used,
        reject_code=reject_code,
        checks=checks,
    )
