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
from typing import Any, Iterable, Sequence

DEFAULT_UI_PORT = 18080
DEFAULT_HEALTH_TIMEOUT_S = 60.0
DEFAULT_HEALTH_POLL_INTERVAL_S = 1.0
TAU_HELLO_FRAME = b"hello version=1\r\n"
_COMPOSE_PROJECT_LABEL = "com.docker.compose.project"
_COMPOSE_SERVICE_LABEL = "com.docker.compose.service"
_LOCAL_PROFILE_ID_LABEL = "io.zenodex.local-operator-profile-id"
_LOCAL_PROFILE_DIGEST_LABEL = "io.zenodex.local-operator-profile-digest"
_CANONICAL_CONTAINER_ID_RE = re.compile(r"[0-9a-f]{64}")


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
class ProjectContainerSnapshot:
    """Minimal owned view of one untrusted container-engine record."""

    container_id: str
    compose_project: str
    compose_service: str
    profile_id: str
    profile_digest: str
    image: str
    environment: tuple[tuple[str, str], ...]

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
    if not container_ids:
        return ()
    result = _run(
        [engine.binary, "inspect", "--type", "container", *container_ids],
        env=env,
        check=True,
        capture=True,
    )
    if type(result.stdout) is not str:
        raise RuntimeError("container inspect returned no stdout")
    try:
        decoded = json.loads(result.stdout, object_pairs_hook=_reject_duplicate_json_keys)
    except (TypeError, ValueError, json.JSONDecodeError) as exc:
        raise RuntimeError(f"container inspect returned invalid JSON: {exc}") from None
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
        raise RuntimeError("container inspect result does not match the project container query")
    return tuple(sorted(snapshots, key=lambda snapshot: snapshot.container_id))


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
    return _parse_canonical_container_ids(result.stdout)


def _reject_duplicate_json_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    decoded: dict[str, Any] = {}
    for key, value in pairs:
        if type(key) is not str or key in decoded:
            raise ValueError("container inspect contains a duplicate or non-string key")
        decoded[key] = value
    return decoded


def _project_container_snapshot(
    value: object,
    *,
    expected_project: str,
) -> ProjectContainerSnapshot:
    if type(value) is not dict:
        raise RuntimeError("container inspect entry must be an exact JSON object")
    record = value
    container_id = record.get("Id")
    config = record.get("Config")
    if type(container_id) is not str or _CANONICAL_CONTAINER_ID_RE.fullmatch(container_id) is None:
        raise RuntimeError("container inspect entry has a non-canonical container ID")
    if type(config) is not dict:
        raise RuntimeError("container inspect entry has no exact Config object")
    image = config.get("Image")
    labels = config.get("Labels")
    environment = config.get("Env")
    if type(image) is not str or not image:
        raise RuntimeError("container inspect entry has no exact image reference")
    if type(labels) is not dict:
        raise RuntimeError("container inspect entry has no exact label object")
    required_labels = (
        _COMPOSE_PROJECT_LABEL,
        _COMPOSE_SERVICE_LABEL,
        _LOCAL_PROFILE_ID_LABEL,
        _LOCAL_PROFILE_DIGEST_LABEL,
    )
    if any(type(labels.get(name)) is not str for name in required_labels):
        raise RuntimeError("container inspect entry has missing or non-string profile labels")
    if labels[_COMPOSE_PROJECT_LABEL] != expected_project:
        raise RuntimeError("container inspect project label mismatch")
    if type(environment) is not list or any(type(item) is not str for item in environment):
        raise RuntimeError("container inspect entry has no exact environment list")
    parsed_environment: dict[str, str] = {}
    for item in environment:
        if "=" not in item:
            raise RuntimeError("container inspect environment entry has no value delimiter")
        name, env_value = item.split("=", 1)
        if not name or name in parsed_environment:
            raise RuntimeError("container inspect environment has an empty or duplicate name")
        parsed_environment[name] = env_value
    return ProjectContainerSnapshot(
        container_id=container_id,
        compose_project=labels[_COMPOSE_PROJECT_LABEL],
        compose_service=labels[_COMPOSE_SERVICE_LABEL],
        profile_id=labels[_LOCAL_PROFILE_ID_LABEL],
        profile_digest=labels[_LOCAL_PROFILE_DIGEST_LABEL],
        image=image,
        environment=tuple(sorted(parsed_environment.items())),
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
) -> subprocess.CompletedProcess[str]:
    """Run a transient compose service command on the existing project network."""
    cmd = [*engine.base_cmd(), "-p", project_name]
    for f in compose_files:
        cmd += ["-f", str(f)]
    cmd += ["run", "--rm", "--no-deps", *extra_args, service, *command]
    return _run(cmd, env=env, check=False, capture=capture)


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
) -> subprocess.CompletedProcess[str]:
    """subprocess wrapper. Always text mode."""
    result = subprocess.run(
        list(cmd),
        env=_merge_env(env),
        check=False,
        capture_output=capture,
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
