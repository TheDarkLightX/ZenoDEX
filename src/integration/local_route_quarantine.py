"""Pure fail-closed admission for retired local Tau value routes."""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass
from typing import Final, NoReturn

QUARANTINED_ROUTE_ENVIRONMENT_V1: Final = (
    "PERPS_WALLET_API_ENABLED",
    "ZUSD_TAU_WALLET_API_ENABLED",
    "ZUSD_MONETARY_WALLET_API_ENABLED",
)
QUARANTINED_ROUTE_ALLOWED_VALUES_V1: Final = frozenset(("false", "0"))
QUARANTINED_ROUTE_ENVIRONMENT_ALIASES_V1: Final = (
    "PERPS_WALLET_API_ENABLE",
    "PERPS_WALLET_ENABLED",
    "PERPS_API_WALLET_ENABLED",
    "ZUSD_TAU_WALLET_API_ENABLE",
    "ZUSD_TAU_WALLET_ENABLED",
    "ZUSD_TAU_API_ENABLED",
    "ZUSD_MONETARY_WALLET_API_ENABLE",
    "ZUSD_MONETARY_WALLET_ENABLED",
    "ZUSD_MONETARY_API_ENABLED",
    "perps_wallet_api_enabled",
    "perps_wallet_api_enable",
    "perps_wallet_enabled",
    "perps_api_wallet_enabled",
    "zusd_tau_wallet_api_enabled",
    "zusd_tau_wallet_api_enable",
    "zusd_tau_wallet_enabled",
    "zusd_tau_api_enabled",
    "zusd_monetary_wallet_api_enabled",
    "zusd_monetary_wallet_api_enable",
    "zusd_monetary_wallet_enabled",
    "zusd_monetary_api_enabled",
)
CURRENT_LOCAL_OPERATOR_PROFILE_ID_V1: Final = "local-testnet-retired-bridge-quarantine-v1"
CURRENT_LOCAL_OPERATOR_RELEASE_BLOCKER_V1: Final = (
    "current profile quarantines stream-8 perps, stream-9 zUSD wallet, and stream-11 "
    "zUSD monetary routes; retained testnet artifacts cannot authorize a current release"
)


@dataclass(frozen=True)
class LocalRouteQuarantineRejectV1:
    """One deterministic startup rejection with no granted authority."""

    code: str
    variable: str

    def render(self) -> str:
        if self.code == "QUARANTINED_ROUTE_ENV_ALIAS":
            return (
                "Refusing to start: retired Tau route environment alias "
                f"{self.variable!r} is forbidden."
            )
        if self.code == "QUARANTINED_ROUTE_ENVIRONMENT_TYPE":
            return "Refusing to start: retired Tau route environment snapshot is not an exact object."
        return (
            "Refusing to start: retired Tau route environment variable "
            f"{self.variable!r} must be absent, exact 'false', or exact '0'."
        )


@dataclass(frozen=True)
class LocalOperatorReleaseAdmissionV1:
    """Fixed refusal consumed by packaging and release-publication shells."""

    profile_id: str
    current_release_eligible: bool
    authority: str
    vm_gates_closed: tuple[str, ...]
    blocker: str


class CurrentLocalOperatorProfileBlockedV1(RuntimeError):
    """Typed shell refusal for operations excluded by the current profile."""


def current_local_operator_release_admission_v1() -> LocalOperatorReleaseAdmissionV1:
    """Return the current profile's non-authoritative release admission result."""

    return LocalOperatorReleaseAdmissionV1(
        profile_id=CURRENT_LOCAL_OPERATOR_PROFILE_ID_V1,
        current_release_eligible=False,
        authority="NONE",
        vm_gates_closed=(),
        blocker=CURRENT_LOCAL_OPERATOR_RELEASE_BLOCKER_V1,
    )


def refuse_current_local_operator_operation_v1(operation: str) -> NoReturn:
    """Refuse a retired-route operation before any shell effect can occur."""

    if type(operation) is not str or not operation:
        raise TypeError("operation must be a nonempty exact string")
    admission = current_local_operator_release_admission_v1()
    raise CurrentLocalOperatorProfileBlockedV1(
        f"{operation} is unavailable: current profile quarantines retired Tau value routes; "
        f"profile={admission.profile_id}; authority={admission.authority}"
    )


def quarantined_route_environment_rejections_v1(
    environment: Mapping[str, object],
) -> tuple[LocalRouteQuarantineRejectV1, ...]:
    """Reject enabled canonical variables, aliases, and hostile mapping shapes."""

    if type(environment) is not dict or any(type(key) is not str for key in environment):
        return (
            LocalRouteQuarantineRejectV1(
                code="QUARANTINED_ROUTE_ENVIRONMENT_TYPE",
                variable="<environment>",
            ),
        )

    rejections: list[LocalRouteQuarantineRejectV1] = []
    for variable in QUARANTINED_ROUTE_ENVIRONMENT_V1:
        if variable not in environment:
            continue
        value = environment[variable]
        if type(value) is not str or value not in QUARANTINED_ROUTE_ALLOWED_VALUES_V1:
            rejections.append(
                LocalRouteQuarantineRejectV1(
                    code="QUARANTINED_ROUTE_ENV_VALUE",
                    variable=variable,
                )
            )
    for alias in QUARANTINED_ROUTE_ENVIRONMENT_ALIASES_V1:
        if alias in environment:
            rejections.append(
                LocalRouteQuarantineRejectV1(
                    code="QUARANTINED_ROUTE_ENV_ALIAS",
                    variable=alias,
                )
            )
    return tuple(rejections)
