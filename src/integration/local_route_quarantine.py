"""Pure fail-closed admission for retired local Tau value routes."""

from __future__ import annotations

import hashlib
import json
from collections.abc import Mapping
from dataclasses import dataclass
from typing import Final, NoReturn, cast

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
CURRENT_LOCAL_OPERATOR_SERVICE_IMAGES_V1: Final = (
    ("tau-local", "zenodex/tau-local:local-testnet"),
    ("zeno-ledger-bootstrap", "zenodex/operator-tools:local"),
    ("zeno-ledger-forwarder", "zenodex/operator-tools:local"),
    ("zeno-ledger-readonly", "zenodex/operator-tools:local"),
    ("zeno-ledger-writer", "zenodex/operator-tools:local"),
    ("zenodex-api", "zenodex/operator-tools:local"),
    ("zenodex-nginx", "zenodex:local"),
    ("zenodex-oracle", "zenodex/operator-tools:local"),
)
_CURRENT_LOCAL_OPERATOR_PROFILE_BODY_V1: Final = {
    "authority": "NONE",
    "enabled_lanes": [
        "CONFIDENTIAL_ATTESTATION_API_ENABLED",
        "DEX_API_ENABLED",
    ],
    "profile_id": CURRENT_LOCAL_OPERATOR_PROFILE_ID_V1,
    "service_images": dict(CURRENT_LOCAL_OPERATOR_SERVICE_IMAGES_V1),
    "quarantined_route_environment": {
        name: "false" for name in QUARANTINED_ROUTE_ENVIRONMENT_V1
    },
    "release_eligible": False,
    "schema": "zenodex.local_operator_profile.v1",
    "vm_gates_closed": [],
}
CURRENT_LOCAL_OPERATOR_PROFILE_DIGEST_V1: Final = "sha256:" + hashlib.sha256(
    json.dumps(
        _CURRENT_LOCAL_OPERATOR_PROFILE_BODY_V1,
        ensure_ascii=False,
        separators=(",", ":"),
        sort_keys=True,
    ).encode("utf-8")
).hexdigest()
CURRENT_LOCAL_OPERATOR_RELEASE_BLOCKER_V1: Final = (
    "current profile quarantines stream-8 perps, stream-9 zUSD wallet, and stream-11 "
    "zUSD monetary routes; retained testnet artifacts cannot authorize a current release"
)
RETIRED_ORIGIN_QUARANTINE_SCHEMA_V1: Final = (
    "zenodex.local_testnet.retired_origin_quarantine.v1"
)
_RETIRED_ORIGIN_QUARANTINE_FIELDS_V1: Final = frozenset(
    {
        "schema",
        "out_dir",
        "compose_project",
        "origin",
        "all_loopback_ports_quarantined",
        "authority",
        "release_eligible",
        "vm_gates_closed",
    }
)
_RETIRED_ORIGIN_FIELDS_V1: Final = frozenset({"scheme", "host", "port"})


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


@dataclass(frozen=True)
class CanonicalLoopbackOriginV1:
    """One exact historical origin that a managed tunnel may still target."""

    scheme: str
    host: str
    port: int

    def __post_init__(self) -> None:
        if (
            type(self.scheme) is not str
            or type(self.host) is not str
            or self.scheme != "http"
            or self.host != "127.0.0.1"
        ):
            raise ValueError("retired origin must be canonical loopback HTTP")
        if type(self.port) is not int or not (1 <= self.port <= 65535):
            raise ValueError("retired origin port must be an exact TCP port")

    def to_mapping(self) -> dict[str, object]:
        return {"scheme": self.scheme, "host": self.host, "port": self.port}


@dataclass(frozen=True)
class RetiredOriginQuarantineV1:
    """Monotonic non-authority marker that survives local stack replacement."""

    out_dir: str
    compose_project: str
    origin: CanonicalLoopbackOriginV1 | None
    all_loopback_ports_quarantined: bool

    def __post_init__(self) -> None:
        if type(self.out_dir) is not str or not self.out_dir.startswith("/"):
            raise ValueError("retired origin out_dir must be an absolute exact string")
        if type(self.compose_project) is not str or not self.compose_project:
            raise ValueError("retired origin compose project must be a nonempty exact string")
        if type(self.all_loopback_ports_quarantined) is not bool:
            raise ValueError("all_loopback_ports_quarantined must be an exact boolean")
        if self.origin is None and not self.all_loopback_ports_quarantined:
            raise ValueError("an unknown retired origin must quarantine all loopback ports")

    def blocks_port(self, port: int) -> bool:
        if type(port) is not int or not (1 <= port <= 65535):
            return True
        return self.all_loopback_ports_quarantined or (
            self.origin is not None and self.origin.port == port
        )

    def to_mapping(self) -> dict[str, object]:
        return {
            "schema": RETIRED_ORIGIN_QUARANTINE_SCHEMA_V1,
            "out_dir": self.out_dir,
            "compose_project": self.compose_project,
            "origin": None if self.origin is None else self.origin.to_mapping(),
            "all_loopback_ports_quarantined": self.all_loopback_ports_quarantined,
            "authority": "NONE",
            "release_eligible": False,
            "vm_gates_closed": [],
        }

    def canonical_bytes(self) -> bytes:
        return (
            json.dumps(
                self.to_mapping(),
                ensure_ascii=True,
                separators=(",", ":"),
                sort_keys=True,
            )
            + "\n"
        ).encode("utf-8")


def retired_origin_quarantine_from_manifest_v1(
    manifest: Mapping[str, object],
    *,
    expected_out_dir: str,
    expected_compose_project: str,
) -> RetiredOriginQuarantineV1:
    """Bind the two historical origin fields or quarantine every local port."""

    if type(manifest) is not dict or any(
        type(key) is not str for key in manifest
    ):
        raise TypeError("retired manifest must be an exact object")
    manifest_out_dir = manifest.get("out_dir")
    if type(manifest_out_dir) is not str or manifest_out_dir != expected_out_dir:
        raise ValueError("retired manifest out_dir identity mismatch")
    manifest_project = manifest.get("compose_project")
    if type(manifest_project) is not str or manifest_project != expected_compose_project:
        raise ValueError("retired manifest compose identity mismatch")

    raw_lanes = manifest.get("enabled_lanes")
    lanes_are_exact = type(raw_lanes) is list and all(
        type(lane) is str and lane for lane in raw_lanes
    )
    ports = manifest.get("ports")
    service_urls = manifest.get("service_urls")
    if type(ports) is dict and all(type(key) is str for key in ports):
        port = ports.get("ui")
    else:
        port = None
    if type(service_urls) is dict and all(
        type(key) is str for key in service_urls
    ):
        ui_url = service_urls.get("ui")
    else:
        ui_url = None
    canonical_url = (
        f"http://127.0.0.1:{port}"
        if type(port) is int and 1 <= port <= 65535
        else None
    )
    if (
        lanes_are_exact
        and canonical_url is not None
        and type(ui_url) is str
        and ui_url == canonical_url
    ):
        origin = CanonicalLoopbackOriginV1(
            scheme="http",
            host="127.0.0.1",
            port=cast(int, port),
        )
        return RetiredOriginQuarantineV1(
            out_dir=expected_out_dir,
            compose_project=expected_compose_project,
            origin=origin,
            all_loopback_ports_quarantined=False,
        )
    return RetiredOriginQuarantineV1(
        out_dir=expected_out_dir,
        compose_project=expected_compose_project,
        origin=None,
        all_loopback_ports_quarantined=True,
    )


def parse_retired_origin_quarantine_v1(
    value: object,
    *,
    expected_out_dir: str | None = None,
    expected_compose_project: str | None = None,
) -> RetiredOriginQuarantineV1:
    """Decode a closed exact tombstone into verifier-owned immutable values."""

    if type(value) is not dict or any(type(key) is not str for key in value):
        raise ValueError("retired origin quarantine must be an exact closed object")
    if frozenset(value) != _RETIRED_ORIGIN_QUARANTINE_FIELDS_V1:
        raise ValueError("retired origin quarantine must be an exact closed object")
    schema = value.get("schema")
    if type(schema) is not str or schema != RETIRED_ORIGIN_QUARANTINE_SCHEMA_V1:
        raise ValueError("retired origin quarantine schema mismatch")
    out_dir = value.get("out_dir")
    if type(out_dir) is not str or not out_dir.startswith("/"):
        raise ValueError("retired origin quarantine out_dir mismatch")
    if expected_out_dir is not None and out_dir != expected_out_dir:
        raise ValueError("retired origin quarantine out_dir mismatch")
    compose_project = value.get("compose_project")
    if type(compose_project) is not str or not compose_project:
        raise ValueError("retired origin quarantine compose identity mismatch")
    if (
        expected_compose_project is not None
        and compose_project != expected_compose_project
    ):
        raise ValueError("retired origin quarantine compose identity mismatch")
    authority = value.get("authority")
    if type(authority) is not str or authority != "NONE":
        raise ValueError("retired origin quarantine authority must be NONE")
    if value.get("release_eligible") is not False:
        raise ValueError("retired origin quarantine cannot be release eligible")
    if type(value.get("vm_gates_closed")) is not list or value["vm_gates_closed"]:
        raise ValueError("retired origin quarantine cannot close VM gates")
    all_ports = value.get("all_loopback_ports_quarantined")
    if type(all_ports) is not bool:
        raise ValueError("retired origin quarantine all-ports flag must be exact boolean")

    raw_origin = value.get("origin")
    origin: CanonicalLoopbackOriginV1 | None
    if raw_origin is None:
        origin = None
    else:
        if type(raw_origin) is not dict or any(
            type(key) is not str for key in raw_origin
        ):
            raise ValueError("retired origin must be an exact closed object")
        if frozenset(raw_origin) != _RETIRED_ORIGIN_FIELDS_V1:
            raise ValueError("retired origin must be an exact closed object")
        scheme = raw_origin.get("scheme")
        host = raw_origin.get("host")
        port = raw_origin.get("port")
        if type(scheme) is not str or type(host) is not str or type(port) is not int:
            raise ValueError("retired origin fields have invalid exact types")
        origin = CanonicalLoopbackOriginV1(
            scheme=scheme,
            host=host,
            port=port,
        )
    return RetiredOriginQuarantineV1(
        out_dir=out_dir,
        compose_project=compose_project,
        origin=origin,
        all_loopback_ports_quarantined=all_ports,
    )


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
