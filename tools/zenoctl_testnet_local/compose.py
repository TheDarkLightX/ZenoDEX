"""Compose orchestration helpers: port allocation, project lifecycle,
health polling, Tau hello check."""

from __future__ import annotations

import errno
import json
import shutil
import socket
import subprocess
import time
import urllib.error
import urllib.request
from contextlib import closing
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence

DEFAULT_UI_PORT = 18080
DEFAULT_HEALTH_TIMEOUT_S = 60.0
DEFAULT_HEALTH_POLL_INTERVAL_S = 1.0
TAU_HELLO_FRAME = b"hello version=1\r\n"


@dataclass(frozen=True)
class ComposeEngine:
    binary: str  # "docker" or "podman"

    def base_cmd(self) -> list[str]:
        if self.binary == "docker":
            return ["docker", "compose"]
        # podman: `podman compose` exists on modern podman; the CLI surface
        # matches docker compose for `up -d`, `down`, `ps`, `logs`.
        return ["podman", "compose"]


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
    with closing(socket.socket(socket.AF_INET, socket.SOCK_STREAM)) as probe:
        probe.settimeout(0.25)
        if probe.connect_ex((host, port)) == 0:
            raise ValueError(
                f"host port {host}:{port} is in use. "
                "Pick a different --ui-port or stop the conflicting process."
            )
    with closing(socket.socket(socket.AF_INET, socket.SOCK_STREAM)) as sock:
        sock.settimeout(0.25)
        # Treat TCP cleanup state from a recently closed local connection as
        # reusable, while an actively bound listener still rejects the bind.
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        try:
            sock.bind((host, port))
        except OSError as exc:
            if exc.errno == errno.EADDRINUSE:
                return
            raise ValueError(
                f"host port {host}:{port} is not bindable ({exc}). "
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
    """Bring down the compose project. Preserves volumes unless
    `remove_volumes=True` (used by `reset --force`)."""
    cmd = [
        *engine.base_cmd(),
        "-p",
        project_name,
    ]
    for f in compose_files:
        cmd += ["-f", str(f)]
    cmd += ["down"]
    if remove_volumes:
        cmd += ["-v"]
    _run(cmd, env=env, check=False)


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
    return _run(cmd, env=env, check=False, capture=capture, input_text=input_text)


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
