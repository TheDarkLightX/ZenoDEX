"""Runtime authority selector — the explicit Python/Rust authority boundary.

This module defines *which* runtime computes the canonical (authoritative)
result for a given surface and enforces fail-closed behavior when a shadow
runtime is configured. It is the single, auditable place where a surface's
authority can be promoted from Python to Rust.

Design rules (see ``docs/runtime/RUST_AUTHORITY_PROMOTION_GATE.md``):

* The default mode is ``python_authority``. No surface is Rust-authoritative
  unless a deployment profile explicitly promotes it *and* the surface is on
  the profile's ``promoted_surfaces`` list.
* ``rust_authority_with_python_shadow`` runs Rust as authority and re-runs
  Python as a shadow check; any disagreement **fails closed**.
* ``rust_shadow`` keeps Python authoritative and runs Rust as a check when it
  is available; an available-but-disagreeing shadow **fails closed**. A Rust
  engine that is simply not built is skipped (Python stays authoritative).
* A Rust error, timeout, or malformed output **fails closed** in any mode where
  Rust is authoritative.
* Every decision carries authority metadata (mode, which engine decided,
  whether the shadow agreed) so it is visible in receipts and logs.
* The authority policy is part of deployment facts (``config/deploy/*.yaml``).

No floats. No silent fallback. Unsupported modes raise.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Any, Callable, Mapping, Optional


class AuthorityMode(str, Enum):
    """Who computes the canonical result for a surface."""

    PYTHON_AUTHORITY = "python_authority"
    RUST_SHADOW = "rust_shadow"
    RUST_AUTHORITY_WITH_PYTHON_SHADOW = "rust_authority_with_python_shadow"
    RUST_AUTHORITY = "rust_authority"


#: The safe default: Python computes everything, Rust does not run.
DEFAULT_MODE = AuthorityMode.PYTHON_AUTHORITY

#: Modes in which Rust computes the canonical result.
RUST_AUTHORITATIVE_MODES = frozenset(
    {AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW, AuthorityMode.RUST_AUTHORITY}
)

#: Modes that run both engines and therefore can fail closed on disagreement.
SHADOW_PAIRED_MODES = frozenset(
    {AuthorityMode.RUST_SHADOW, AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW}
)

#: Deployment profiles that must never run a half-configured Rust authority.
STRICT_PROFILE_IDS = frozenset({"public-testnet", "production-strict"})

POLICY_SCHEMA_V1 = "zenodex/runtime_authority_policy/v1"
AUTHORITY_POLICY_KEYS = frozenset({"schema", "default", "per_surface", "promoted_surfaces"})

# Consensus-critical surfaces that may appear in strict deployment authority
# policy. This keeps Rust-authority promotion focused on the trusted core; API
# glue, dashboards, evidence tools, and other non-consensus paths stay outside
# deployment authority metadata unless this list is deliberately extended.
TRUSTED_CORE_AUTHORITY_SURFACES = frozenset(
    {
        "balances",
        "burn_receipts",
        "canonical",
        "cpmm_settlement",
        "fee_router",
        "perp_math",
        "perp_stateful",
        "replay_guard",
        "state_root",
        "zusd",
    }
)

# Public testnet is the shadow-checked Rust-authority soak lane for explicitly
# promoted full-CBC trusted-core surfaces. Partial-CBC surfaces remain Python
# authority until their public transition is linked to complete implementation
# evidence. Production-strict remains all-Python until a release decision.
PUBLIC_TESTNET_REQUIRED_RUST_AUTHORITY_SURFACES = (
    TRUSTED_CORE_AUTHORITY_SURFACES
    - frozenset(
        {
            "canonical",
            "cpmm_settlement",
            "perp_math",
            "perp_stateful",
            "state_root",
            "zusd",
        }
    )
)


class AuthorityError(RuntimeError):
    """Fail-closed marker: raised when a decision cannot be made safely.

    Raised on Python/Rust disagreement, on a Rust failure where Rust is
    authoritative, or when a required Rust engine is unavailable. Callers must
    treat this as a hard reject of the transition, never as a fallback.
    """


class RustUnavailable(Exception):
    """Signal from a ``rust_fn`` that the Rust engine is not built/present.

    In ``rust_shadow`` mode this is benign (the shadow is skipped and Python
    stays authoritative). In any Rust-authoritative mode it is fatal (the
    authority engine is missing) and is converted to :class:`AuthorityError`.
    """


def parse_authority_mode(value: object) -> AuthorityMode:
    """Parse a string (or AuthorityMode) into an AuthorityMode, else raise.

    Unsupported values raise ``ValueError`` — there is no silent default here so
    that a typo in a deployment profile fails closed at load time.
    """
    if isinstance(value, AuthorityMode):
        return value
    if not isinstance(value, str):
        raise ValueError(f"authority mode must be a string, got {type(value).__name__}")
    try:
        return AuthorityMode(value)
    except ValueError:
        valid = ", ".join(sorted(m.value for m in AuthorityMode))
        raise ValueError(f"unsupported authority mode {value!r}; valid: {valid}")


def _parse_surface_id(value: object, *, field: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{field} surface id must be a string, got {type(value).__name__}")
    if value != value.strip() or not value:
        raise ValueError(f"{field} surface id must be non-empty and whitespace-trimmed")
    return value


@dataclass(frozen=True)
class AuthorityDecision:
    """The outcome of an authority-gated transition, with audit metadata."""

    surface: str
    mode: AuthorityMode
    authority: str  # "python" | "rust"
    result: Any
    shadow_checked: bool
    agreed: Optional[bool]  # None when no shadow ran

    def metadata(self) -> dict[str, Any]:
        """Receipt/log-friendly authority facts (no result payload)."""
        return {
            "surface": self.surface,
            "authority_mode": self.mode.value,
            "decided_by": self.authority,
            "shadow_checked": self.shadow_checked,
            "shadow_agreed": self.agreed,
        }


@dataclass(frozen=True)
class AuthorityPolicy:
    """Per-surface authority configuration, drawn from deployment facts."""

    default: AuthorityMode
    per_surface: Mapping[str, AuthorityMode]
    promoted_surfaces: frozenset[str]

    def mode_for(self, surface: str) -> AuthorityMode:
        """The authority mode for a surface (per-surface override, else default)."""
        return self.per_surface.get(surface, self.default)


#: Process-wide active policy. Runtime bootstrap installs the deployment
#: profile's policy through ``set_active_authority_policy``. Until then every
#: surface stays on the safe all-Python default.
_ACTIVE_POLICY: AuthorityPolicy = AuthorityPolicy(DEFAULT_MODE, {}, frozenset())


def set_active_authority_policy(policy: AuthorityPolicy) -> None:
    """Install the process-wide authority policy, typically during startup."""

    if not isinstance(policy, AuthorityPolicy):
        raise TypeError("policy must be an AuthorityPolicy")
    global _ACTIVE_POLICY
    _ACTIVE_POLICY = policy


def active_authority_policy() -> AuthorityPolicy:
    """Return the currently installed process-wide authority policy."""

    return _ACTIVE_POLICY


def reset_active_authority_policy() -> None:
    """Restore the safe all-Python default, mainly for tests."""

    global _ACTIVE_POLICY
    _ACTIVE_POLICY = AuthorityPolicy(DEFAULT_MODE, {}, frozenset())


def active_mode(surface: str) -> AuthorityMode:
    """Return the active authority mode for ``surface``."""

    return _ACTIVE_POLICY.mode_for(surface)


def load_authority_policy(profile: Mapping[str, Any] | None) -> AuthorityPolicy:
    """Build an :class:`AuthorityPolicy` from a deployment-profile mapping.

    A profile with no ``runtime_authority_policy`` section yields the safe
    all-Python default. A malformed section raises.
    """
    if profile is None:
        return AuthorityPolicy(DEFAULT_MODE, {}, frozenset())
    if not isinstance(profile, Mapping):
        raise TypeError("deployment profile must be a mapping")
    section = profile.get("runtime_authority_policy")
    if section is None:
        return AuthorityPolicy(DEFAULT_MODE, {}, frozenset())
    if not isinstance(section, Mapping):
        raise TypeError("runtime_authority_policy must be a mapping")
    unknown_keys = sorted(
        (key for key in section.keys() if key not in AUTHORITY_POLICY_KEYS),
        key=repr,
    )
    if unknown_keys:
        raise ValueError(f"runtime_authority_policy has unknown keys: {unknown_keys}")

    schema = section.get("schema")
    if schema != POLICY_SCHEMA_V1:
        raise ValueError(
            f"runtime_authority_policy schema must be {POLICY_SCHEMA_V1!r}, got {schema!r}"
        )

    default = parse_authority_mode(section.get("default", DEFAULT_MODE.value))

    raw_per_surface = section.get("per_surface", {})
    if not isinstance(raw_per_surface, Mapping):
        raise TypeError("per_surface must be a mapping")
    per_surface = {
        _parse_surface_id(surface, field="per_surface"): parse_authority_mode(mode)
        for surface, mode in raw_per_surface.items()
    }

    raw_promoted = section.get("promoted_surfaces", [])
    if not isinstance(raw_promoted, (list, tuple)):
        raise TypeError("promoted_surfaces must be a list")
    promoted_list = [
        _parse_surface_id(surface, field="promoted_surfaces")
        for surface in raw_promoted
    ]
    if len(set(promoted_list)) != len(promoted_list):
        raise ValueError("promoted_surfaces must not contain duplicates")
    promoted = frozenset(promoted_list)

    return AuthorityPolicy(default, per_surface, promoted)


def validate_authority_policy(policy: AuthorityPolicy, *, profile_id: str) -> None:
    """Reject half-configured Rust authority under a strict deployment profile.

    Under a strict profile (``public-testnet`` or ``production-strict``):

    * only trusted-core consensus surfaces may appear in the authority policy;
    * `public-testnet` must cover every currently admitted Rust soak surface
      with ``rust_authority_with_python_shadow``;
    * the blanket ``default`` may not be a Rust-authoritative mode (that would
      promote every surface at once, including unshadowed ones);
    * pure ``rust_authority`` is not admitted by the current strict-profile
      schema; strict profiles use ``rust_authority_with_python_shadow`` until a
      future schema/version records the sustained soak evidence and sign-off;
    * a per-surface Rust-authoritative mode is only allowed for a surface that
      is admitted by the profile and explicitly listed in
      ``promoted_surfaces`` (i.e. has passed the gate).
    * every listed ``promoted_surfaces`` entry must actually be configured as a
      Rust-authoritative per-surface mode, so stale or misspelled promotion
      evidence cannot linger in strict deployment facts.

    Outside strict profiles this is advisory (no raise) so local-dev can
    experiment, but the same shape is recommended.
    """
    if profile_id not in STRICT_PROFILE_IDS:
        return

    if policy.default in RUST_AUTHORITATIVE_MODES:
        raise AuthorityError(
            f"profile {profile_id!r}: default mode {policy.default.value!r} would "
            "promote every surface to Rust authority; promote per-surface only"
        )

    unknown_policy_surfaces = sorted(
        (frozenset(policy.per_surface) | policy.promoted_surfaces)
        - TRUSTED_CORE_AUTHORITY_SURFACES
    )
    if unknown_policy_surfaces:
        raise AuthorityError(
            f"profile {profile_id!r}: authority policy contains non-trusted-core "
            f"surfaces: {unknown_policy_surfaces}"
        )

    pure_rust_surfaces = sorted(
        surface
        for surface, mode in policy.per_surface.items()
        if mode is AuthorityMode.RUST_AUTHORITY
    )
    if pure_rust_surfaces:
        raise AuthorityError(
            f"profile {profile_id!r}: pure rust_authority is not admitted by the "
            "current strict-profile schema; use rust_authority_with_python_shadow "
            f"for promoted trusted-core surfaces: {pure_rust_surfaces}"
        )

    if profile_id == "public-testnet":
        required_mode = AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW
        missing_required = sorted(
            PUBLIC_TESTNET_REQUIRED_RUST_AUTHORITY_SURFACES - frozenset(policy.per_surface)
        )
        if missing_required:
            raise AuthorityError(
                "profile 'public-testnet': missing trusted-core authority surfaces: "
                f"{missing_required}"
            )
        wrong_required_mode = sorted(
            surface
            for surface in PUBLIC_TESTNET_REQUIRED_RUST_AUTHORITY_SURFACES
            if policy.per_surface.get(surface) is not required_mode
        )
        if wrong_required_mode:
            raise AuthorityError(
                "profile 'public-testnet': trusted-core surfaces must use "
                "rust_authority_with_python_shadow: "
                f"{wrong_required_mode}"
            )

    rust_authoritative_surfaces = frozenset(
        surface
        for surface, mode in policy.per_surface.items()
        if mode in RUST_AUTHORITATIVE_MODES
    )

    if profile_id == "public-testnet":
        unadmitted_rust = sorted(
            rust_authoritative_surfaces
            - PUBLIC_TESTNET_REQUIRED_RUST_AUTHORITY_SURFACES
        )
        if unadmitted_rust:
            raise AuthorityError(
                "profile 'public-testnet': Rust authority is not admitted for "
                f"partial-CBC surfaces: {unadmitted_rust}"
            )

    if profile_id == "production-strict" and rust_authoritative_surfaces:
        raise AuthorityError(
            "profile 'production-strict': Rust authority requires an explicit "
            "release profile/schema promotion; current profile is Python authority: "
            f"{sorted(rust_authoritative_surfaces)}"
        )

    for surface, mode in policy.per_surface.items():
        if mode in RUST_AUTHORITATIVE_MODES and surface not in policy.promoted_surfaces:
            raise AuthorityError(
                f"profile {profile_id!r}: surface {surface!r} set to {mode.value!r} "
                "but is not in promoted_surfaces (half-configured Rust authority)"
            )

    stale_promotions = sorted(policy.promoted_surfaces - rust_authoritative_surfaces)
    if stale_promotions:
        raise AuthorityError(
            f"profile {profile_id!r}: promoted_surfaces contains surfaces that are not "
            f"configured for Rust authority: {stale_promotions}"
        )


def _agree(python_result: Any, rust_result: Any, compare: Optional[Callable[[Any, Any], bool]]) -> bool:
    if compare is not None:
        try:
            agreed = compare(python_result, rust_result)
        except Exception as exc:
            raise AuthorityError(f"authority comparator errored: {exc}") from exc
        if not isinstance(agreed, bool):
            raise AuthorityError(
                f"authority comparator must return bool, got {type(agreed).__name__}"
            )
        return agreed
    if python_result is None or rust_result is None:
        return False
    return python_result == rust_result


def decide(
    surface: str,
    mode: AuthorityMode | str,
    *,
    python_fn: Callable[[], Any],
    rust_fn: Optional[Callable[[], Any]] = None,
    compare: Optional[Callable[[Any, Any], bool]] = None,
) -> AuthorityDecision:
    """Run a surface transition under the selected authority mode, fail-closed.

    ``python_fn`` / ``rust_fn`` are zero-arg callables that return the canonical
    result for that engine (e.g. a receipt + post-state-root tuple). ``compare``
    customizes agreement (defaults to ``==``). A ``rust_fn`` may raise
    :class:`RustUnavailable` to signal the engine is not built.

    Raises :class:`AuthorityError` on any unsafe condition (disagreement, Rust
    failure where Rust is authoritative, missing authority engine).
    """
    mode = parse_authority_mode(mode)

    if mode is AuthorityMode.PYTHON_AUTHORITY:
        return AuthorityDecision(
            surface, mode, "python", python_fn(), shadow_checked=False, agreed=None
        )

    if mode is AuthorityMode.RUST_SHADOW:
        py = python_fn()
        if rust_fn is None:
            return AuthorityDecision(surface, mode, "python", py, False, None)
        try:
            ru = rust_fn()
        except RustUnavailable:
            # Shadow not built — Python remains authoritative, shadow skipped.
            return AuthorityDecision(surface, mode, "python", py, False, None)
        except Exception as exc:  # malformed / runtime error → divergence
            raise AuthorityError(
                f"surface {surface!r}: rust shadow errored: {exc}"
            ) from exc
        if not _agree(py, ru, compare):
            raise AuthorityError(
                f"surface {surface!r}: python/rust disagreement in rust_shadow mode"
            )
        return AuthorityDecision(surface, mode, "python", py, shadow_checked=True, agreed=True)

    if mode is AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW:
        if rust_fn is None:
            raise AuthorityError(
                f"surface {surface!r}: {mode.value} requires a rust engine"
            )
        try:
            ru = rust_fn()
        except RustUnavailable as exc:
            raise AuthorityError(
                f"surface {surface!r}: rust engine unavailable but is authority"
            ) from exc
        except Exception as exc:
            raise AuthorityError(
                f"surface {surface!r}: rust authority errored: {exc}"
            ) from exc
        try:
            py = python_fn()
        except Exception as exc:
            raise AuthorityError(
                f"surface {surface!r}: python shadow errored: {exc}"
            ) from exc
        if not _agree(py, ru, compare):
            raise AuthorityError(
                f"surface {surface!r}: python/rust disagreement (python shadow)"
            )
        return AuthorityDecision(surface, mode, "rust", ru, shadow_checked=True, agreed=True)

    if mode is AuthorityMode.RUST_AUTHORITY:
        if rust_fn is None:
            raise AuthorityError(
                f"surface {surface!r}: {mode.value} requires a rust engine"
            )
        try:
            ru = rust_fn()
        except RustUnavailable as exc:
            raise AuthorityError(
                f"surface {surface!r}: rust engine unavailable but is authority"
            ) from exc
        except Exception as exc:
            raise AuthorityError(
                f"surface {surface!r}: rust authority errored: {exc}"
            ) from exc
        return AuthorityDecision(surface, mode, "rust", ru, shadow_checked=False, agreed=None)

    # Unreachable: parse_authority_mode covers the enum exhaustively.
    raise AuthorityError(f"unhandled authority mode {mode!r}")
