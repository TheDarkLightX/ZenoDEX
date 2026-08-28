"""Compose orchestration helpers: port allocation, project lifecycle,
health polling, Tau hello check."""

from __future__ import annotations

import json
import re
import shutil
import socket
import subprocess
import time
import urllib.error
import urllib.request
from contextlib import closing
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Sequence, cast

DEFAULT_UI_PORT = 18080
DEFAULT_HEALTH_TIMEOUT_S = 60.0
DEFAULT_HEALTH_POLL_INTERVAL_S = 1.0
TAU_HELLO_FRAME = b"hello version=1\r\n"
_COMPOSE_PROJECT_LABEL = "com.docker.compose.project"
_COMPOSE_SERVICE_LABEL = "com.docker.compose.service"
_LOCAL_PROFILE_ID_LABEL = "io.zenodex.local-operator-profile-id"
_LOCAL_PROFILE_DIGEST_LABEL = "io.zenodex.local-operator-profile-digest"
_CANONICAL_CONTAINER_ID_RE = re.compile(r"[0-9a-f]{64}")
_CANONICAL_IMAGE_ID_RE = re.compile(r"sha256:[0-9a-f]{64}")
_CANONICAL_ENVIRONMENT_NAME_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
_CANONICAL_PORT_KEY_RE = re.compile(r"([1-9][0-9]{0,4})/(tcp|udp|sctp)")
_CANONICAL_HOST_PORT_RE = re.compile(r"[1-9][0-9]{0,4}")
_RESTART_POLICY_NAMES = frozenset({"no", "always", "on-failure", "unless-stopped"})
_CONTAINER_STATE_NAMES = frozenset(
    {"created", "running", "paused", "restarting", "removing", "exited", "dead"}
)


@dataclass(frozen=True)
class ComposeEngine:
    binary: str  # "docker" or "podman"

    def base_cmd(self) -> list[str]:
        if self.binary == "docker":
            return ["docker", "compose"]
        # podman: `podman compose` exists on modern podman; the CLI surface
        # matches docker compose for `up -d`, `down`, `ps`, `logs`.
        return ["podman", "compose"]


@dataclass(frozen=True)
class ContainerStringVector:
    """Exact distinction between a JSON null and a JSON string array."""

    is_null: bool
    values: tuple[str, ...]


@dataclass(frozen=True, order=True)
class ContainerHostOverride:
    """One exact HostConfig.ExtraHosts mapping."""

    host: str
    address: str


@dataclass(frozen=True)
class ContainerHostOverrideVector:
    """Exact distinction between null and list-valued host overrides."""

    is_null: bool
    values: tuple[ContainerHostOverride, ...]


@dataclass(frozen=True, order=True)
class ContainerDevice:
    """One exact HostConfig.Devices mapping."""

    path_on_host: str
    path_in_container: str
    cgroup_permissions: str


@dataclass(frozen=True)
class ContainerDeviceVector:
    """Exact distinction between null and list-valued device mappings."""

    is_null: bool
    values: tuple[ContainerDevice, ...]


@dataclass(frozen=True, order=True)
class ContainerMount:
    """Canonical effective mount facts from one inspect record."""

    mount_type: str
    source: str
    destination: str
    name: str | None
    driver: str | None
    mode: str
    read_write: bool
    propagation: str


@dataclass(frozen=True, order=True)
class ContainerBind:
    """Canonical HostConfig.Binds entry."""

    source: str
    destination: str
    options: tuple[str, ...]


@dataclass(frozen=True)
class ContainerBindVector:
    """Exact distinction between null and list-valued HostConfig.Binds."""

    is_null: bool
    values: tuple[ContainerBind, ...]


@dataclass(frozen=True, order=True)
class ContainerPort:
    number: int
    protocol: str


@dataclass(frozen=True, order=True)
class ContainerPortBinding:
    container_port: ContainerPort
    host_ip: str
    host_port: int


@dataclass(frozen=True)
class ContainerPortBindings:
    """Canonical port bindings, retaining null-valued unbound ports."""

    unbound_ports: tuple[ContainerPort, ...]
    bindings: tuple[ContainerPortBinding, ...]


@dataclass(frozen=True)
class ContainerRestartPolicy:
    name: str
    maximum_retry_count: int


@dataclass(frozen=True)
class ContainerState:
    status: str
    running: bool
    paused: bool
    restarting: bool
    oom_killed: bool
    dead: bool
    pid: int
    exit_code: int
    error: str
    health_status: str | None


@dataclass(frozen=True)
class ProjectContainerEngineFacts:
    """Complete, strictly decoded execution facts from container inspect."""

    immutable_image_id: str
    config_image: str
    path: str
    args: tuple[str, ...]
    command: ContainerStringVector
    entrypoint: ContainerStringVector
    working_dir: str
    user: str
    mounts: tuple[ContainerMount, ...]
    binds: ContainerBindVector
    configured_ports: ContainerPortBindings
    published_ports: ContainerPortBindings
    restart_policy: ContainerRestartPolicy
    readonly_rootfs: bool
    network_mode: str
    privileged: bool
    cap_add: ContainerStringVector
    cap_drop: ContainerStringVector
    security_opt: ContainerStringVector
    pid_mode: str
    state: ContainerState
    extra_hosts: ContainerHostOverrideVector = ContainerHostOverrideVector(
        is_null=True,
        values=(),
    )
    devices: ContainerDeviceVector = ContainerDeviceVector(
        is_null=False,
        values=(),
    )
    attached_networks: tuple[str, ...] = ()


@dataclass(frozen=True)
class ImageReferenceEngineFacts:
    """Immutable image identity plus its exact inherited environment."""

    immutable_image_id: str
    environment: tuple[tuple[str, str], ...]
    exposed_ports: tuple[ContainerPort, ...]


@dataclass(frozen=True)
class ProjectContainerSnapshot:
    """Owned view of one untrusted container-engine record.

    ``engine_facts`` is optional only to preserve the existing caller-constructed
    test/API shape. Snapshots returned by :func:`inspect_project_containers`
    always populate it; consumers requiring live-engine evidence must reject
    ``None``.
    """

    container_id: str
    compose_project: str
    compose_service: str
    profile_id: str
    profile_digest: str
    image: str
    environment: tuple[tuple[str, str], ...]
    engine_facts: ProjectContainerEngineFacts | None = None

    def environment_value(self, name: str) -> str | None:
        for key, value in self.environment:
            if key == name:
                return value
        return None


def detect_engine(preferred: str = "auto") -> ComposeEngine:
    """Return a ComposeEngine for the first available container engine.
    Order: explicit `preferred`, then docker, then podman. Raises if
    none is on PATH."""
    if preferred == "docker":
        if not _has_binary("docker"):
            raise RuntimeError("preferred engine 'docker' not on PATH")
        return ComposeEngine(binary="docker")
    if preferred == "podman":
        if not _has_binary("podman"):
            raise RuntimeError("preferred engine 'podman' not on PATH")
        return ComposeEngine(binary="podman")
    if preferred != "auto":
        raise ValueError(f"unknown engine: {preferred!r}")

    if _has_binary("docker"):
        return ComposeEngine(binary="docker")
    if _has_binary("podman"):
        return ComposeEngine(binary="podman")
    raise RuntimeError(
        "no container engine on PATH (looked for docker, podman). "
        "Install Docker or Podman, then retry."
    )


def _has_binary(name: str) -> bool:
    return shutil.which(name) is not None


def check_host_port_free(port: int, *, host: str = "127.0.0.1") -> None:
    """Raise ValueError if `host:port` is already bound."""
    if not (1 <= port <= 65535):
        raise ValueError(f"port {port} out of range [1, 65535]")
    with closing(socket.socket(socket.AF_INET, socket.SOCK_STREAM)) as sock:
        sock.settimeout(0.25)
        try:
            sock.bind((host, port))
        except OSError as exc:
            raise ValueError(
                f"host port {host}:{port} is in use ({exc}). "
                "Pick a different --ui-port or stop the conflicting process."
            ) from None


def check_external_tau_testnet_present(repo_root: Path) -> None:
    """The local-testnet mode requires `external/tau-testnet/` (per the
    plan: no degraded mode). Refuse fast with an actionable message."""
    path = repo_root / "external" / "tau-testnet"
    if not path.is_dir():
        raise FileNotFoundError(
            f"required dependency missing: {path}. "
            "Clone with:\n"
            "  mkdir -p external && cd external && "
            "git clone https://github.com/IDNI/tau-testnet.git"
        )


def compose_up(
    *,
    engine: ComposeEngine,
    project_name: str,
    compose_files: Sequence[Path],
    env: dict[str, str] | None = None,
    extra_args: Sequence[str] = (),
) -> None:
    """Bring up the compose project in detached mode."""
    cmd = [
        *engine.base_cmd(),
        "-p",
        project_name,
    ]
    for f in compose_files:
        cmd += ["-f", str(f)]
    cmd += ["up", "-d", *extra_args]
    _run(cmd, env=env, check=True)


def compose_down(
    *,
    engine: ComposeEngine,
    project_name: str,
    compose_files: Sequence[Path],
    remove_volumes: bool = False,
    env: dict[str, str] | None = None,
) -> None:
    """Bring down the compose project and prove no project containers survive.

    Volumes are preserved unless `remove_volumes=True` (used by
    `reset --force`).
    """
    cmd = [
        *engine.base_cmd(),
        "-p",
        project_name,
    ]
    for f in compose_files:
        cmd += ["-f", str(f)]
    cmd += ["down", "--remove-orphans"]
    if remove_volumes:
        cmd += ["-v"]
    _run(cmd, env=env, check=True)

    survivors = _query_project_container_ids(
        engine=engine,
        project_name=project_name,
        env=env,
    )
    if survivors:
        survivor_list = ", ".join(survivors)
        raise RuntimeError(
            f"compose project {project_name!r} still has {len(survivors)} "
            f"container(s) after down: {survivor_list}"
        )


def inspect_project_containers(
    *,
    engine: ComposeEngine,
    project_name: str,
    env: dict[str, str] | None = None,
) -> tuple[ProjectContainerSnapshot, ...]:
    """Return exact typed snapshots for every container under one project label."""

    container_ids = _query_project_container_ids(
        engine=engine,
        project_name=project_name,
        env=env,
    )
    snapshots: tuple[ProjectContainerSnapshot, ...] = ()
    if container_ids:
        result = _run(
            [engine.binary, "inspect", "--type", "container", *container_ids],
            env=env,
            check=True,
            capture=True,
        )
        decoded = _decode_container_engine_json(
            result.stdout,
            operation="container inspect",
        )
        if type(decoded) is not list:
            raise RuntimeError("container inspect must return an exact JSON array")

        snapshots = tuple(
            _project_container_snapshot(item, expected_project=project_name)
            for item in decoded
        )
        observed_ids = tuple(snapshot.container_id for snapshot in snapshots)
        if len(observed_ids) != len(set(observed_ids)):
            raise RuntimeError("container inspect returned duplicate container records")
        if set(observed_ids) != set(container_ids):
            raise RuntimeError(
                "container inspect result does not match the project container query"
            )

    stable_ids = _query_project_container_ids(
        engine=engine,
        project_name=project_name,
        env=env,
    )
    if set(stable_ids) != set(container_ids):
        raise RuntimeError("project container membership changed during inspection")
    return tuple(sorted(snapshots, key=lambda snapshot: snapshot.container_id))


def inspect_image_reference(
    *,
    engine: ComposeEngine,
    image_reference: str,
    env: dict[str, str] | None = None,
) -> ImageReferenceEngineFacts:
    """Resolve one image reference to immutable identity and inherited facts."""

    if (
        type(image_reference) is not str
        or not image_reference
        or image_reference.startswith("-")
        or any(character.isspace() for character in image_reference)
        or "\x00" in image_reference
    ):
        raise ValueError("image reference must be one non-option, whitespace-free string")
    result = _run(
        [engine.binary, "image", "inspect", image_reference],
        env=env,
        check=True,
        capture=True,
    )
    decoded = _decode_container_engine_json(
        result.stdout,
        operation="image inspect",
    )
    if type(decoded) is not list or len(decoded) != 1:
        raise RuntimeError("image inspect must return exactly one JSON object")
    record = _exact_object(decoded[0], context="image inspect entry")
    config = _exact_object(record.get("Config"), context="image inspect Config")
    return ImageReferenceEngineFacts(
        immutable_image_id=_canonical_image_id(
            record.get("Id"), context="image inspect entry"
        ),
        environment=_environment_entries(
            config.get("Env"),
            context="image inspect environment",
        ),
        exposed_ports=_exposed_ports(config.get("ExposedPorts")),
    )


def inspect_image_reference_id(
    *,
    engine: ComposeEngine,
    image_reference: str,
    env: dict[str, str] | None = None,
) -> str:
    """Resolve one image reference to one canonical immutable engine image ID."""

    return inspect_image_reference(
        engine=engine,
        image_reference=image_reference,
        env=env,
    ).immutable_image_id


def _query_project_container_ids(
    *,
    engine: ComposeEngine,
    project_name: str,
    env: dict[str, str] | None,
) -> tuple[str, ...]:
    query_cmd = [
        engine.binary,
        "ps",
        "--all",
        "--quiet",
        "--no-trunc",
        "--filter",
        f"label={_COMPOSE_PROJECT_LABEL}={project_name}",
    ]
    result = _run(query_cmd, env=env, check=True, capture=True)
    if result.stdout is None:
        raise RuntimeError("container query returned no stdout")
    return tuple(sorted(_parse_canonical_container_ids(result.stdout)))


def _reject_duplicate_json_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    decoded: dict[str, Any] = {}
    for key, value in pairs:
        if type(key) is not str or key in decoded:
            raise ValueError("container-engine JSON contains a duplicate or non-string key")
        decoded[key] = value
    return decoded


def _reject_non_json_constant(value: str) -> None:
    raise ValueError(f"container-engine JSON contains invalid constant {value!r}")


def _decode_container_engine_json(output: object, *, operation: str) -> object:
    if type(output) is not str:
        raise RuntimeError(f"{operation} returned no stdout")
    try:
        return json.loads(
            output,
            object_pairs_hook=_reject_duplicate_json_keys,
            parse_constant=_reject_non_json_constant,
        )
    except (TypeError, ValueError, json.JSONDecodeError) as exc:
        raise RuntimeError(f"{operation} returned invalid JSON: {exc}") from None


def _exact_object(value: object, *, context: str) -> dict[str, object]:
    if type(value) is not dict:
        raise RuntimeError(f"{context} must be an exact JSON object")
    record = cast(dict[object, object], value)
    if any(type(key) is not str for key in record):
        raise RuntimeError(f"{context} contains a non-string key")
    return cast(dict[str, object], record)


def _exact_text(
    value: object,
    *,
    context: str,
    allow_empty: bool = True,
) -> str:
    if type(value) is not str or (not allow_empty and not value):
        requirement = "non-empty string" if not allow_empty else "string"
        raise RuntimeError(f"{context} must be an exact {requirement}")
    text = value
    if any(character in text for character in ("\x00", "\r", "\n")):
        raise RuntimeError(f"{context} contains a forbidden control character")
    return text


def _canonical_image_id(value: object, *, context: str) -> str:
    image_id = _exact_text(value, context=f"{context} image ID", allow_empty=False)
    if _CANONICAL_IMAGE_ID_RE.fullmatch(image_id) is None:
        raise RuntimeError(f"{context} has a non-canonical immutable image ID")
    return image_id


def _string_vector(
    value: object,
    *,
    context: str,
    allow_null: bool,
) -> ContainerStringVector:
    if value is None:
        if not allow_null:
            raise RuntimeError(f"{context} must be an exact string array")
        return ContainerStringVector(is_null=True, values=())
    if type(value) is not list:
        suffix = "null or an exact string array" if allow_null else "an exact string array"
        raise RuntimeError(f"{context} must be {suffix}")
    values = tuple(
        _exact_text(item, context=f"{context} item")
        for item in cast(list[object], value)
    )
    return ContainerStringVector(is_null=False, values=values)


def _host_overrides(value: object) -> ContainerHostOverrideVector:
    if value is None:
        return ContainerHostOverrideVector(is_null=True, values=())
    if type(value) is not list:
        raise RuntimeError(
            "container inspect HostConfig.ExtraHosts must be null or an exact array"
        )
    decoded: list[ContainerHostOverride] = []
    observed_hosts: set[str] = set()
    for item in cast(list[object], value):
        mapping = _exact_text(
            item,
            context="container inspect HostConfig.ExtraHosts item",
            allow_empty=False,
        )
        host, separator, address = mapping.partition(":")
        if (
            not separator
            or not host
            or not address
            or host != host.strip()
            or address != address.strip()
            or any(character.isspace() for character in host)
        ):
            raise RuntimeError("container inspect host override is malformed")
        if host in observed_hosts:
            raise RuntimeError("container inspect contains a duplicate host override")
        observed_hosts.add(host)
        decoded.append(ContainerHostOverride(host=host, address=address))
    return ContainerHostOverrideVector(
        is_null=False,
        values=tuple(sorted(decoded)),
    )


def _devices(value: object) -> ContainerDeviceVector:
    if value is None:
        return ContainerDeviceVector(is_null=True, values=())
    if type(value) is not list:
        raise RuntimeError(
            "container inspect HostConfig.Devices must be null or an exact array"
        )
    required_keys = frozenset(
        {"PathOnHost", "PathInContainer", "CgroupPermissions"}
    )
    decoded: list[ContainerDevice] = []
    destinations: set[str] = set()
    for item in cast(list[object], value):
        record = _exact_object(item, context="container inspect device")
        _reject_unknown_keys(
            record,
            allowed=required_keys,
            context="container inspect device",
        )
        if set(record) != required_keys:
            raise RuntimeError("container inspect device has missing required keys")
        path_on_host = _exact_text(
            record["PathOnHost"],
            context="container inspect device PathOnHost",
            allow_empty=False,
        )
        path_in_container = _exact_text(
            record["PathInContainer"],
            context="container inspect device PathInContainer",
            allow_empty=False,
        )
        if not path_on_host.startswith("/") or not path_in_container.startswith("/"):
            raise RuntimeError("container inspect device paths must be absolute")
        raw_permissions = _exact_text(
            record["CgroupPermissions"],
            context="container inspect device CgroupPermissions",
            allow_empty=False,
        )
        permission_set = set(raw_permissions)
        if not permission_set.issubset({"r", "w", "m"}) or len(
            permission_set
        ) != len(raw_permissions):
            raise RuntimeError("container inspect device permissions are malformed")
        if path_in_container in destinations:
            raise RuntimeError("container inspect has a duplicate device destination")
        destinations.add(path_in_container)
        decoded.append(
            ContainerDevice(
                path_on_host=path_on_host,
                path_in_container=path_in_container,
                cgroup_permissions="".join(
                    permission for permission in "rwm" if permission in permission_set
                ),
            )
        )
    return ContainerDeviceVector(
        is_null=False,
        values=tuple(sorted(decoded, key=lambda device: device.path_in_container)),
    )


def _attached_networks(value: object) -> tuple[str, ...]:
    record = _exact_object(
        value,
        context="container inspect NetworkSettings.Networks",
    )
    names: list[str] = []
    for raw_name, raw_settings in record.items():
        name = _exact_text(
            raw_name,
            context="container inspect attached network name",
            allow_empty=False,
        )
        if name != name.strip() or any(character.isspace() for character in name):
            raise RuntimeError("container inspect attached network name is malformed")
        _exact_object(
            raw_settings,
            context=f"container inspect attached network {name!r}",
        )
        names.append(name)
    return tuple(sorted(names))


def _environment_entries(
    value: object,
    *,
    context: str,
) -> tuple[tuple[str, str], ...]:
    if type(value) is not list:
        raise RuntimeError(f"{context} must be an exact string array")
    parsed: dict[str, str] = {}
    for raw_item in cast(list[object], value):
        item = _exact_text(raw_item, context=f"{context} entry")
        if "=" not in item:
            raise RuntimeError(f"{context} entry has no value delimiter")
        name, env_value = item.split("=", 1)
        if _CANONICAL_ENVIRONMENT_NAME_RE.fullmatch(name) is None or name in parsed:
            raise RuntimeError(f"{context} has an empty, malformed, or duplicate name")
        parsed[name] = env_value
    return tuple(sorted(parsed.items()))


def _reject_unknown_keys(
    record: dict[str, object],
    *,
    allowed: frozenset[str],
    context: str,
) -> None:
    unknown = sorted(set(record).difference(allowed))
    if unknown:
        raise RuntimeError(f"{context} contains unsupported keys: {', '.join(unknown)}")


def _mounts(value: object) -> tuple[ContainerMount, ...]:
    if type(value) is not list:
        raise RuntimeError("container inspect Mounts must be an exact array")
    allowed_keys = frozenset(
        {
            "Type",
            "Source",
            "Destination",
            "Name",
            "Driver",
            "Mode",
            "RW",
            "Propagation",
        }
    )
    required_keys = frozenset(
        {"Type", "Source", "Destination", "Mode", "RW", "Propagation"}
    )
    decoded: list[ContainerMount] = []
    destinations: set[str] = set()
    for item in cast(list[object], value):
        record = _exact_object(item, context="container inspect mount")
        _reject_unknown_keys(record, allowed=allowed_keys, context="container inspect mount")
        if not required_keys.issubset(record):
            raise RuntimeError("container inspect mount has missing required keys")
        mount_type = _exact_text(
            record["Type"], context="container inspect mount Type", allow_empty=False
        )
        source = _exact_text(record["Source"], context="container inspect mount Source")
        destination = _exact_text(
            record["Destination"],
            context="container inspect mount Destination",
            allow_empty=False,
        )
        if not destination.startswith("/"):
            raise RuntimeError("container inspect mount destination must be absolute")
        if destination in destinations:
            raise RuntimeError("container inspect has a duplicate mount destination")
        destinations.add(destination)
        read_write = record["RW"]
        if type(read_write) is not bool:
            raise RuntimeError("container inspect mount RW must be an exact boolean")
        name = (
            _exact_text(record["Name"], context="container inspect mount Name")
            if "Name" in record
            else None
        )
        driver = (
            _exact_text(record["Driver"], context="container inspect mount Driver")
            if "Driver" in record
            else None
        )
        decoded.append(
            ContainerMount(
                mount_type=mount_type,
                source=source,
                destination=destination,
                name=name,
                driver=driver,
                mode=_exact_text(record["Mode"], context="container inspect mount Mode"),
                read_write=read_write,
                propagation=_exact_text(
                    record["Propagation"],
                    context="container inspect mount Propagation",
                ),
            )
        )
    return tuple(sorted(decoded, key=lambda mount: mount.destination))


def _binds(value: object) -> ContainerBindVector:
    if value is None:
        return ContainerBindVector(is_null=True, values=())
    if type(value) is not list:
        raise RuntimeError("container inspect HostConfig.Binds must be null or an exact array")
    decoded: list[ContainerBind] = []
    destinations: set[str] = set()
    for item in cast(list[object], value):
        binding = _exact_text(
            item,
            context="container inspect HostConfig.Binds item",
            allow_empty=False,
        )
        components = binding.split(":")
        if len(components) not in (2, 3):
            raise RuntimeError("container inspect bind has an ambiguous field count")
        source, destination = components[:2]
        if not source or not destination or not destination.startswith("/"):
            raise RuntimeError("container inspect bind has a malformed source or destination")
        raw_options = components[2].split(",") if len(components) == 3 else []
        if any(not option for option in raw_options):
            raise RuntimeError("container inspect bind contains an empty option")
        if len(raw_options) != len(set(raw_options)):
            raise RuntimeError("container inspect bind contains a duplicate option")
        if "ro" in raw_options and "rw" in raw_options:
            raise RuntimeError("container inspect bind contains conflicting access options")
        if destination in destinations:
            raise RuntimeError("container inspect has a duplicate bind destination")
        destinations.add(destination)
        decoded.append(
            ContainerBind(
                source=source,
                destination=destination,
                options=tuple(sorted(raw_options)),
            )
        )
    return ContainerBindVector(
        is_null=False,
        values=tuple(sorted(decoded, key=lambda binding: binding.destination)),
    )


def _cross_check_binds(
    binds: ContainerBindVector,
    mounts: tuple[ContainerMount, ...],
) -> None:
    mounts_by_destination = {mount.destination: mount for mount in mounts}
    for binding in binds.values:
        mount = mounts_by_destination.get(binding.destination)
        if (
            mount is None
            or mount.mount_type != "bind"
            or mount.source != binding.source
        ):
            raise RuntimeError("container inspect bind disagrees with effective mounts")
        requested_read_write = "ro" not in binding.options
        if mount.read_write != requested_read_write:
            raise RuntimeError("container inspect bind access disagrees with effective mounts")


def _container_port(value: object, *, context: str) -> ContainerPort:
    port_key = _exact_text(value, context=context, allow_empty=False)
    matched = _CANONICAL_PORT_KEY_RE.fullmatch(port_key)
    if matched is None:
        raise RuntimeError(f"{context} is not a canonical container port")
    number = int(matched.group(1))
    if number > 65_535:
        raise RuntimeError(f"{context} is outside the valid port range")
    return ContainerPort(number=number, protocol=matched.group(2))


def _exposed_ports(value: object) -> tuple[ContainerPort, ...]:
    if value is None:
        return ()
    record = _exact_object(value, context="image inspect Config.ExposedPorts")
    ports: list[ContainerPort] = []
    for key, marker in record.items():
        if marker is not None:
            raise RuntimeError("image exposed-port marker must be null")
        ports.append(_container_port(key, context="image exposed port"))
    if len(ports) != len(set(ports)):
        raise RuntimeError("image inspect contains duplicate exposed ports")
    return tuple(sorted(ports))


def _port_bindings(value: object, *, context: str) -> ContainerPortBindings:
    record = _exact_object(value, context=context)
    unbound: list[ContainerPort] = []
    bindings: list[ContainerPortBinding] = []
    observed_bindings: set[ContainerPortBinding] = set()
    observed_host_endpoints: set[tuple[str, int, str]] = set()
    for port_key in sorted(record):
        container_port = _container_port(port_key, context=f"{context} key")
        raw_bindings = record[port_key]
        if raw_bindings is None:
            unbound.append(container_port)
            continue
        if type(raw_bindings) is not list:
            raise RuntimeError(f"{context} value must be null or an exact binding array")
        binding_items = cast(list[object], raw_bindings)
        if not binding_items:
            raise RuntimeError(f"{context} contains an ambiguous empty binding list")
        for item in binding_items:
            binding_record = _exact_object(item, context=f"{context} binding")
            _reject_unknown_keys(
                binding_record,
                allowed=frozenset({"HostIp", "HostPort"}),
                context=f"{context} binding",
            )
            if set(binding_record) != {"HostIp", "HostPort"}:
                raise RuntimeError(f"{context} binding has missing required keys")
            host_ip = _exact_text(
                binding_record["HostIp"], context=f"{context} binding HostIp"
            )
            host_port_text = _exact_text(
                binding_record["HostPort"],
                context=f"{context} binding HostPort",
                allow_empty=False,
            )
            if _CANONICAL_HOST_PORT_RE.fullmatch(host_port_text) is None:
                raise RuntimeError(f"{context} binding has a non-canonical host port")
            host_port = int(host_port_text)
            if host_port > 65_535:
                raise RuntimeError(f"{context} binding host port is out of range")
            binding = ContainerPortBinding(
                container_port=container_port,
                host_ip=host_ip,
                host_port=host_port,
            )
            if binding in observed_bindings:
                raise RuntimeError(f"{context} contains a duplicate port binding")
            observed_bindings.add(binding)
            endpoint_host = "0.0.0.0" if host_ip == "" else host_ip
            endpoint = (endpoint_host, host_port, container_port.protocol)
            if endpoint in observed_host_endpoints:
                raise RuntimeError(f"{context} contains a duplicate host port binding")
            observed_host_endpoints.add(endpoint)
            bindings.append(binding)
    return ContainerPortBindings(
        unbound_ports=tuple(sorted(unbound)),
        bindings=tuple(sorted(bindings)),
    )


def _restart_policy(value: object) -> ContainerRestartPolicy:
    record = _exact_object(value, context="container inspect restart policy")
    _reject_unknown_keys(
        record,
        allowed=frozenset({"Name", "MaximumRetryCount"}),
        context="container inspect restart policy",
    )
    if set(record) != {"Name", "MaximumRetryCount"}:
        raise RuntimeError("container inspect restart policy has missing required keys")
    name = _exact_text(
        record["Name"],
        context="container inspect restart policy Name",
        allow_empty=False,
    )
    if name not in _RESTART_POLICY_NAMES:
        raise RuntimeError("container inspect restart policy has an unsupported name")
    maximum_retry_count = record["MaximumRetryCount"]
    if (
        type(maximum_retry_count) is not int
        or maximum_retry_count < 0
        or maximum_retry_count > 2_147_483_647
    ):
        raise RuntimeError("container inspect restart retry count is not a valid integer")
    return ContainerRestartPolicy(
        name=name,
        maximum_retry_count=maximum_retry_count,
    )


def _container_state(value: object) -> ContainerState:
    record = _exact_object(value, context="container inspect State")
    required_keys = frozenset(
        {
            "Status",
            "Running",
            "Paused",
            "Restarting",
            "OOMKilled",
            "Dead",
            "Pid",
            "ExitCode",
            "Error",
        }
    )
    _reject_unknown_keys(
        record,
        allowed=required_keys
        | frozenset({"StartedAt", "FinishedAt", "Health"}),
        context="container inspect State",
    )
    if not required_keys.issubset(record):
        raise RuntimeError("container inspect State has missing required keys")
    status = _exact_text(
        record["Status"], context="container inspect State.Status", allow_empty=False
    )
    if status not in _CONTAINER_STATE_NAMES:
        raise RuntimeError("container inspect State.Status is unsupported")
    boolean_values: dict[str, bool] = {}
    for key in ("Running", "Paused", "Restarting", "OOMKilled", "Dead"):
        raw_value = record[key]
        if type(raw_value) is not bool:
            raise RuntimeError(f"container inspect State.{key} must be an exact boolean")
        boolean_values[key] = raw_value
    pid = record["Pid"]
    exit_code = record["ExitCode"]
    if type(pid) is not int or pid < 0 or pid > 2_147_483_647:
        raise RuntimeError("container inspect State.Pid must be a non-negative integer")
    if type(exit_code) is not int or exit_code < 0 or exit_code > 2_147_483_647:
        raise RuntimeError("container inspect State.ExitCode must be a non-negative integer")
    running = boolean_values["Running"]
    paused = boolean_values["Paused"]
    restarting = boolean_values["Restarting"]
    dead = boolean_values["Dead"]
    expected_live_status = (
        "paused" if paused else "restarting" if restarting else "running"
    )
    if running:
        if dead or status != expected_live_status or pid == 0:
            raise RuntimeError("container inspect State contains inconsistent live facts")
    elif paused or restarting or status in {"running", "paused", "restarting"}:
        raise RuntimeError("container inspect State contains inconsistent stopped facts")
    if dead != (status == "dead"):
        raise RuntimeError("container inspect State contains inconsistent dead facts")

    health_status: str | None = None
    if "Health" in record:
        health = _exact_object(record["Health"], context="container inspect State.Health")
        _reject_unknown_keys(
            health,
            allowed=frozenset({"Status", "FailingStreak", "Log"}),
            context="container inspect State.Health",
        )
        if "Status" not in health:
            raise RuntimeError("container inspect State.Health has no Status")
        health_status = _exact_text(
            health["Status"],
            context="container inspect State.Health.Status",
            allow_empty=False,
        )
        if health_status not in {"starting", "healthy", "unhealthy", "none"}:
            raise RuntimeError("container inspect State.Health.Status is unsupported")
    return ContainerState(
        status=status,
        running=running,
        paused=paused,
        restarting=restarting,
        oom_killed=boolean_values["OOMKilled"],
        dead=dead,
        pid=pid,
        exit_code=exit_code,
        error=_exact_text(record["Error"], context="container inspect State.Error"),
        health_status=health_status,
    )


def _project_container_snapshot(
    value: object,
    *,
    expected_project: str,
) -> ProjectContainerSnapshot:
    record = _exact_object(value, context="container inspect entry")
    container_id = record.get("Id")
    config = record.get("Config")
    if (
        type(container_id) is not str
        or _CANONICAL_CONTAINER_ID_RE.fullmatch(container_id) is None
    ):
        raise RuntimeError("container inspect entry has a non-canonical container ID")
    immutable_image_id = _canonical_image_id(record.get("Image"), context="container inspect entry")
    path = _exact_text(
        record.get("Path"),
        context="container inspect entry Path",
        allow_empty=False,
    )
    args = _string_vector(
        record.get("Args"),
        context="container inspect entry Args",
        allow_null=False,
    ).values
    state = _container_state(record.get("State"))
    config = _exact_object(config, context="container inspect Config")
    image = _exact_text(
        config.get("Image"),
        context="container inspect Config.Image",
        allow_empty=False,
    )
    if "Cmd" not in config or "Entrypoint" not in config:
        raise RuntimeError("container inspect Config lacks command or entrypoint facts")
    command = _string_vector(
        config["Cmd"],
        context="container inspect Config.Cmd",
        allow_null=True,
    )
    entrypoint = _string_vector(
        config["Entrypoint"],
        context="container inspect Config.Entrypoint",
        allow_null=True,
    )
    working_dir = _exact_text(
        config.get("WorkingDir"), context="container inspect Config.WorkingDir"
    )
    user = _exact_text(config.get("User"), context="container inspect Config.User")
    labels = config.get("Labels")
    environment = config.get("Env")
    labels = _exact_object(labels, context="container inspect Config.Labels")
    decoded_labels = {
        _exact_text(key, context="container inspect label name", allow_empty=False): _exact_text(
            item, context=f"container inspect label {key!r}"
        )
        for key, item in labels.items()
    }
    required_labels = (
        _COMPOSE_PROJECT_LABEL,
        _COMPOSE_SERVICE_LABEL,
        _LOCAL_PROFILE_ID_LABEL,
        _LOCAL_PROFILE_DIGEST_LABEL,
    )
    if any(name not in decoded_labels for name in required_labels):
        raise RuntimeError("container inspect entry has missing or non-string profile labels")
    if decoded_labels[_COMPOSE_PROJECT_LABEL] != expected_project:
        raise RuntimeError("container inspect project label mismatch")
    if any(not decoded_labels[name] for name in required_labels):
        raise RuntimeError("container inspect entry has an empty required profile label")
    if (
        _CANONICAL_IMAGE_ID_RE.fullmatch(decoded_labels[_LOCAL_PROFILE_DIGEST_LABEL])
        is None
    ):
        raise RuntimeError("container inspect profile digest is non-canonical")
    parsed_environment = _environment_entries(
        environment,
        context="container inspect environment",
    )

    host_config = _exact_object(
        record.get("HostConfig"), context="container inspect HostConfig"
    )
    host_required = frozenset(
        {
            "Binds",
            "ExtraHosts",
            "Devices",
            "PortBindings",
            "RestartPolicy",
            "ReadonlyRootfs",
            "NetworkMode",
            "Privileged",
            "CapAdd",
            "CapDrop",
            "SecurityOpt",
            "PidMode",
        }
    )
    if not host_required.issubset(host_config):
        raise RuntimeError("container inspect HostConfig lacks required runtime facts")
    mounts = _mounts(record.get("Mounts"))
    binds = _binds(host_config["Binds"])
    extra_hosts = _host_overrides(host_config["ExtraHosts"])
    devices = _devices(host_config["Devices"])
    _cross_check_binds(binds, mounts)
    configured_ports = _port_bindings(
        host_config["PortBindings"], context="container inspect HostConfig.PortBindings"
    )
    restart_policy = _restart_policy(host_config["RestartPolicy"])
    readonly_rootfs = host_config["ReadonlyRootfs"]
    if type(readonly_rootfs) is not bool:
        raise RuntimeError("container inspect ReadonlyRootfs must be an exact boolean")
    network_mode = _exact_text(
        host_config["NetworkMode"],
        context="container inspect HostConfig.NetworkMode",
        allow_empty=False,
    )
    privileged = host_config["Privileged"]
    if type(privileged) is not bool:
        raise RuntimeError("container inspect Privileged must be an exact boolean")
    cap_add = _string_vector(
        host_config["CapAdd"],
        context="container inspect HostConfig.CapAdd",
        allow_null=True,
    )
    cap_drop = _string_vector(
        host_config["CapDrop"],
        context="container inspect HostConfig.CapDrop",
        allow_null=True,
    )
    security_opt = _string_vector(
        host_config["SecurityOpt"],
        context="container inspect HostConfig.SecurityOpt",
        allow_null=True,
    )
    pid_mode = _exact_text(
        host_config["PidMode"],
        context="container inspect HostConfig.PidMode",
    )
    network_settings = _exact_object(
        record.get("NetworkSettings"), context="container inspect NetworkSettings"
    )
    if not {"Ports", "Networks"}.issubset(network_settings):
        raise RuntimeError(
            "container inspect NetworkSettings lacks required runtime facts"
        )
    published_ports = _port_bindings(
        network_settings["Ports"], context="container inspect NetworkSettings.Ports"
    )
    attached_networks = _attached_networks(network_settings["Networks"])
    engine_facts = ProjectContainerEngineFacts(
        immutable_image_id=immutable_image_id,
        config_image=image,
        path=path,
        args=args,
        command=command,
        entrypoint=entrypoint,
        working_dir=working_dir,
        user=user,
        mounts=mounts,
        binds=binds,
        configured_ports=configured_ports,
        published_ports=published_ports,
        restart_policy=restart_policy,
        readonly_rootfs=readonly_rootfs,
        network_mode=network_mode,
        privileged=privileged,
        cap_add=cap_add,
        cap_drop=cap_drop,
        security_opt=security_opt,
        pid_mode=pid_mode,
        state=state,
        extra_hosts=extra_hosts,
        devices=devices,
        attached_networks=attached_networks,
    )
    return ProjectContainerSnapshot(
        container_id=container_id,
        compose_project=decoded_labels[_COMPOSE_PROJECT_LABEL],
        compose_service=decoded_labels[_COMPOSE_SERVICE_LABEL],
        profile_id=decoded_labels[_LOCAL_PROFILE_ID_LABEL],
        profile_digest=decoded_labels[_LOCAL_PROFILE_DIGEST_LABEL],
        image=image,
        environment=parsed_environment,
        engine_facts=engine_facts,
    )


def _parse_canonical_container_ids(output: str) -> tuple[str, ...]:
    """Decode `ps --quiet --no-trunc` output without accepting ambiguity."""

    if output == "":
        return ()
    lines = output.splitlines()
    if output != "".join(f"{line}\n" for line in lines):
        raise RuntimeError("container query returned non-canonical output")
    if any(_CANONICAL_CONTAINER_ID_RE.fullmatch(line) is None for line in lines):
        raise RuntimeError("container query returned a non-canonical container ID")
    if len(lines) != len(set(lines)):
        raise RuntimeError("container query returned duplicate container IDs")
    return tuple(lines)


def compose_ps_json(
    *,
    engine: ComposeEngine,
    project_name: str,
    compose_files: Sequence[Path],
    env: dict[str, str] | None = None,
) -> list[dict[str, object]]:
    """Return parsed `docker compose ps --format json` output."""
    cmd = [*engine.base_cmd(), "-p", project_name]
    for f in compose_files:
        cmd += ["-f", str(f)]
    cmd += ["ps", "--format", "json"]
    result = _run(cmd, env=env, check=False, capture=True)
    if result.returncode != 0 or not result.stdout.strip():
        return []
    out: list[dict[str, object]] = []
    # Docker compose v2 emits NDJSON (one object per line); older versions
    # emit a JSON array. Tolerate both.
    text = result.stdout.strip()
    if text.startswith("["):
        try:
            arr = json.loads(text)
        except json.JSONDecodeError:
            return []
        if isinstance(arr, list):
            for item in arr:
                if isinstance(item, dict):
                    out.append(item)
        return out
    for line in text.splitlines():
        try:
            item = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(item, dict):
            out.append(item)
    return out


def compose_logs(
    *,
    engine: ComposeEngine,
    project_name: str,
    compose_files: Sequence[Path],
    service: str | None = None,
    tail: int | None = None,
    env: dict[str, str] | None = None,
) -> str:
    """Return raw log output. Used for error diagnostics when a health
    poll times out."""
    cmd = [*engine.base_cmd(), "-p", project_name]
    for f in compose_files:
        cmd += ["-f", str(f)]
    cmd += ["logs", "--no-color"]
    if tail is not None:
        cmd += ["--tail", str(int(tail))]
    if service is not None:
        cmd += [service]
    result = _run(cmd, env=env, check=False, capture=True)
    return result.stdout or ""


def compose_run(
    *,
    engine: ComposeEngine,
    project_name: str,
    compose_files: Sequence[Path],
    service: str,
    command: Sequence[str],
    env: dict[str, str] | None = None,
    extra_args: Sequence[str] = (),
    capture: bool = False,
    input_text: str | None = None,
) -> subprocess.CompletedProcess[str]:
    """Run a transient compose service command on the existing project network."""
    cmd = [*engine.base_cmd(), "-p", project_name]
    for f in compose_files:
        cmd += ["-f", str(f)]
    cmd += ["run", "--rm", "--no-deps", *extra_args, service, *command]
    return _run(
        cmd,
        env=env,
        check=False,
        capture=capture,
        input_text=input_text,
    )


def wait_for_http(
    url: str,
    *,
    timeout_s: float = DEFAULT_HEALTH_TIMEOUT_S,
    poll_interval_s: float = DEFAULT_HEALTH_POLL_INTERVAL_S,
    accept_status: Iterable[int] = (200, 204),
) -> None:
    """Poll `url` (GET) until response status is in `accept_status` or
    `timeout_s` elapsed. Raises TimeoutError with a diagnostic on
    failure."""
    deadline = time.monotonic() + timeout_s
    last_err: str = "no attempts made"
    while time.monotonic() < deadline:
        try:
            req = urllib.request.Request(url, method="GET")
            with urllib.request.urlopen(req, timeout=poll_interval_s) as resp:
                if resp.status in accept_status:
                    return
                last_err = f"status={resp.status}"
        except urllib.error.HTTPError as exc:
            if exc.code in accept_status:
                return
            last_err = f"HTTPError {exc.code}: {exc.reason}"
        except (urllib.error.URLError, socket.timeout, ConnectionError, OSError) as exc:
            last_err = f"{type(exc).__name__}: {exc}"
        time.sleep(poll_interval_s)
    raise TimeoutError(f"timed out after {timeout_s}s waiting for {url} (last error: {last_err})")


def wait_for_tau_hello(
    host: str,
    port: int,
    *,
    timeout_s: float = DEFAULT_HEALTH_TIMEOUT_S,
    poll_interval_s: float = DEFAULT_HEALTH_POLL_INTERVAL_S,
) -> None:
    """Wait for a Tau node to respond to the `hello version=1` handshake.
    Mirrors the existing pattern in `tools/tau_testnet_local_e2e.py`."""
    deadline = time.monotonic() + timeout_s
    last_err = "no attempts made"
    while time.monotonic() < deadline:
        try:
            with closing(socket.create_connection((host, port), timeout=poll_interval_s)) as sock:
                sock.sendall(TAU_HELLO_FRAME)
                sock.settimeout(poll_interval_s)
                data = sock.recv(64)
                if data:
                    return
                last_err = "empty response"
        except (socket.timeout, ConnectionError, OSError) as exc:
            last_err = f"{type(exc).__name__}: {exc}"
        time.sleep(poll_interval_s)
    raise TimeoutError(
        f"timed out after {timeout_s}s waiting for Tau hello on {host}:{port} "
        f"(last error: {last_err})"
    )


def _run(
    cmd: Sequence[str],
    *,
    env: dict[str, str] | None = None,
    check: bool = True,
    capture: bool = False,
    input_text: str | None = None,
) -> subprocess.CompletedProcess[str]:
    """subprocess wrapper. Always text mode."""
    result = subprocess.run(
        list(cmd),
        env=_merge_env(env),
        check=False,
        capture_output=capture,
        input=input_text,
        text=True,
    )
    if check and result.returncode != 0:
        tail = ""
        if capture and result.stderr:
            tail = f"\n--- stderr ---\n{result.stderr.strip()[-2000:]}"
        raise RuntimeError(
            f"command failed (exit {result.returncode}): {' '.join(cmd)}{tail}"
        )
    return result


def _merge_env(extra: dict[str, str] | None) -> dict[str, str] | None:
    if extra is None:
        return None
    import os

    merged = dict(os.environ)
    merged.update({k: str(v) for k, v in extra.items()})
    return merged
