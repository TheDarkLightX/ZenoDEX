"""Toxiproxy harness for TCP fault injection in chaos experiments.

This module provides a Python wrapper around Toxiproxy for injecting
network faults into TCP connections. Designed for chaos engineering
experiments targeting imperative shell boundaries.

Supported toxics:
- limit_data: Truncate data after N bytes
- timeout: Add latency or cause timeouts
- reset_peer: Send TCP RST to close connection abruptly
- latency: Add fixed or jittered latency
- slow_close: Delay closing the connection

Usage:
    with ToxiproxyHarness(upstream_port=65432) as harness:
        harness.add_toxic("limit_data", attributes={"bytes": 50})
        # ... run test against harness.listen_port ...

Requires Toxiproxy server running (see docker-compose.chaos.yml).
"""

from __future__ import annotations

import hashlib
import json
import socket
import time
import urllib.error
import urllib.request
from contextlib import contextmanager
from dataclasses import dataclass, field
from typing import Any, Generator, Mapping, Optional


class ToxiproxyError(RuntimeError):
    pass


class ToxiproxyConnectionError(ToxiproxyError):
    pass


class ToxiproxyAPIError(ToxiproxyError):
    def __init__(self, message: str, status_code: int, body: str) -> None:
        super().__init__(message)
        self.status_code = int(status_code)
        self.body = str(body)


@dataclass(frozen=True)
class ToxiproxyConfig:
    api_host: str = "127.0.0.1"
    api_port: int = 8474
    proxy_listen_host: str = "0.0.0.0"
    host_reachable_from_proxy: str = "host.docker.internal"
    published_proxy_ports: tuple[int, ...] = (8475, 8476, 8477, 8478, 8479, 8480)
    connect_timeout_s: float = 5.0
    read_timeout_s: float = 10.0


_DEFAULT_CONFIG = ToxiproxyConfig()


@dataclass
class Toxic:
    name: str
    toxic_type: str
    stream: str  # "upstream" or "downstream"
    toxicity: float  # 0.0 to 1.0
    attributes: dict[str, Any] = field(default_factory=dict)


@dataclass
class Proxy:
    name: str
    listen: str
    upstream: str
    enabled: bool = True
    toxics: list[Toxic] = field(default_factory=list)


class ToxiproxyClient:
    def __init__(self, config: ToxiproxyConfig = _DEFAULT_CONFIG) -> None:
        self._cfg = config
        self._base_url = f"http://{config.api_host}:{config.api_port}"

    def _request(
        self,
        method: str,
        path: str,
        *,
        body: Optional[Mapping[str, Any]] = None,
        expected_status: tuple[int, ...] = (200, 201, 204),
    ) -> Optional[dict[str, Any]]:
        url = f"{self._base_url}{path}"
        headers = {"Content-Type": "application/json"}
        data = json.dumps(body).encode("utf-8") if body else None

        req = urllib.request.Request(url, data=data, headers=headers, method=method)

        try:
            with urllib.request.urlopen(
                req,
                timeout=float(self._cfg.connect_timeout_s + self._cfg.read_timeout_s),
            ) as resp:
                status = int(resp.status)
                resp_body = resp.read().decode("utf-8")
                if status not in expected_status:
                    raise ToxiproxyAPIError(
                        f"Unexpected status {status} for {method} {path}",
                        status_code=status,
                        body=resp_body,
                    )
                if resp_body.strip():
                    return json.loads(resp_body)
                return None
        except urllib.error.HTTPError as exc:
            body_text = ""
            try:
                body_text = exc.read().decode("utf-8")
            except Exception:
                pass
            raise ToxiproxyAPIError(
                f"HTTP {exc.code} for {method} {path}: {body_text[:200]}",
                status_code=int(exc.code),
                body=body_text,
            ) from exc
        except urllib.error.URLError as exc:
            raise ToxiproxyConnectionError(
                f"Failed to connect to Toxiproxy at {self._base_url}: {exc.reason}"
            ) from exc

    def health_check(self) -> bool:
        try:
            self._request("GET", "/version", expected_status=(200,))
            return True
        except ToxiproxyError:
            return False

    def reset(self) -> None:
        self._request("POST", "/reset", expected_status=(204,))

    def list_proxies(self) -> dict[str, Proxy]:
        resp = self._request("GET", "/proxies", expected_status=(200,))
        if not resp:
            return {}
        proxies: dict[str, Proxy] = {}
        for name, data in dict(resp).items():
            proxies[str(name)] = Proxy(
                name=str(data.get("name", name)),
                listen=str(data.get("listen", "")),
                upstream=str(data.get("upstream", "")),
                enabled=bool(data.get("enabled", True)),
            )
        return proxies

    def create_proxy(
        self,
        name: str,
        listen: str,
        upstream: str,
        *,
        enabled: bool = True,
    ) -> Proxy:
        body = {
            "name": str(name),
            "listen": str(listen),
            "upstream": str(upstream),
            "enabled": bool(enabled),
        }
        resp = self._request("POST", "/proxies", body=body, expected_status=(201,))
        if not resp:
            raise ToxiproxyError(f"No response body when creating proxy {name}")
        return Proxy(
            name=str(resp.get("name", name)),
            listen=str(resp.get("listen", listen)),
            upstream=str(resp.get("upstream", upstream)),
            enabled=bool(resp.get("enabled", enabled)),
        )

    def delete_proxy(self, name: str) -> None:
        self._request("DELETE", f"/proxies/{name}", expected_status=(204, 404))

    def get_proxy(self, name: str) -> Optional[Proxy]:
        try:
            resp = self._request("GET", f"/proxies/{name}", expected_status=(200,))
        except ToxiproxyAPIError as exc:
            if exc.status_code == 404:
                return None
            raise
        if not resp:
            return None
        return Proxy(
            name=str(resp.get("name", name)),
            listen=str(resp.get("listen", "")),
            upstream=str(resp.get("upstream", "")),
            enabled=bool(resp.get("enabled", True)),
        )

    def add_toxic(
        self,
        proxy_name: str,
        toxic_type: str,
        *,
        name: Optional[str] = None,
        stream: str = "downstream",
        toxicity: float = 1.0,
        attributes: Optional[Mapping[str, Any]] = None,
    ) -> Toxic:
        if name is None:
            name = f"{toxic_type}_{int(time.time() * 1000)}"
        body: dict[str, Any] = {
            "name": str(name),
            "type": str(toxic_type),
            "stream": str(stream),
            "toxicity": float(toxicity),
        }
        if attributes:
            body["attributes"] = dict(attributes)

        resp = self._request(
            "POST",
            f"/proxies/{proxy_name}/toxics",
            body=body,
            expected_status=(200,),
        )
        if not resp:
            raise ToxiproxyError(f"No response body when adding toxic to {proxy_name}")
        return Toxic(
            name=str(resp.get("name", name)),
            toxic_type=str(resp.get("type", toxic_type)),
            stream=str(resp.get("stream", stream)),
            toxicity=float(resp.get("toxicity", toxicity)),
            attributes=dict(resp.get("attributes") or {}),
        )

    def remove_toxic(self, proxy_name: str, toxic_name: str) -> None:
        self._request(
            "DELETE",
            f"/proxies/{proxy_name}/toxics/{toxic_name}",
            expected_status=(204, 404),
        )

    def list_toxics(self, proxy_name: str) -> list[Toxic]:
        resp = self._request(
            "GET",
            f"/proxies/{proxy_name}/toxics",
            expected_status=(200,),
        )
        if not resp:
            return []
        toxics: list[Toxic] = []
        for data in list(resp) if isinstance(resp, list) else []:
            toxics.append(
                Toxic(
                    name=str(data.get("name", "")),
                    toxic_type=str(data.get("type", "")),
                    stream=str(data.get("stream", "downstream")),
                    toxicity=float(data.get("toxicity", 1.0)),
                    attributes=dict(data.get("attributes") or {}),
                )
            )
        return toxics


def _find_free_port(host: str = "127.0.0.1") -> int:
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
        s.bind((host, 0))
        s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        return int(s.getsockname()[1])


def _port_accepts_connections(host: str, port: int) -> bool:
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
        s.settimeout(0.1)
        try:
            s.connect((host, int(port)))
            return True
        except OSError:
            return False


def _proxy_listen_port(listen_addr: str) -> Optional[int]:
    if not listen_addr:
        return None
    try:
        return int(str(listen_addr).rsplit(":", maxsplit=1)[1])
    except (IndexError, ValueError):
        return None


def _select_proxy_port(config: ToxiproxyConfig, client: ToxiproxyClient) -> int:
    published_ports = tuple(int(port) for port in config.published_proxy_ports)
    if not published_ports:
        return _find_free_port("127.0.0.1")

    try:
        used_ports = {
            port
            for proxy in client.list_proxies().values()
            if (port := _proxy_listen_port(proxy.listen)) is not None
        }
    except ToxiproxyError:
        return published_ports[0]

    for port in published_ports:
        if port not in used_ports:
            return port
    raise ToxiproxyError("no published Toxiproxy proxy ports available")


def _wait_for_listen_port(host: str, port: int, *, timeout_s: float = 3.0) -> None:
    deadline = time.monotonic() + float(timeout_s)
    while time.monotonic() < deadline:
        if _port_accepts_connections(host, int(port)):
            return
        time.sleep(0.05)
    raise ToxiproxyConnectionError(f"Toxiproxy proxy did not listen on {host}:{port}")


def _proxy_upstream_host(upstream_host: str, config: ToxiproxyConfig) -> str:
    if upstream_host in {"127.0.0.1", "localhost", "::1", "0.0.0.0"}:
        return config.host_reachable_from_proxy
    return upstream_host


class ToxiproxyHarness:
    def __init__(
        self,
        upstream_host: str = "127.0.0.1",
        upstream_port: int = 65432,
        *,
        listen_host: str = "127.0.0.1",
        listen_port: Optional[int] = None,
        proxy_name: Optional[str] = None,
        config: ToxiproxyConfig = _DEFAULT_CONFIG,
        auto_cleanup: bool = True,
    ) -> None:
        self._config = config
        self._client = ToxiproxyClient(config)
        self._upstream_host = _proxy_upstream_host(str(upstream_host), config)
        self._upstream_port = int(upstream_port)
        self._listen_host = str(listen_host)
        self._proxy_listen_host = str(config.proxy_listen_host)
        self._listen_port = int(listen_port) if listen_port else _select_proxy_port(config, self._client)
        self._auto_cleanup = bool(auto_cleanup)

        if proxy_name is None:
            h = hashlib.sha256(f"{upstream_host}:{upstream_port}:{time.time()}".encode()).hexdigest()[:12]
            proxy_name = f"chaos_{h}"
        self._proxy_name = str(proxy_name)

        self._proxy: Optional[Proxy] = None
        self._toxics: list[str] = []
        self._entered = False

    @property
    def listen_host(self) -> str:
        return self._listen_host

    @property
    def listen_port(self) -> int:
        return self._listen_port

    @property
    def listen_addr(self) -> str:
        return f"{self._listen_host}:{self._listen_port}"

    @property
    def proxy_listen_addr(self) -> str:
        return f"{self._proxy_listen_host}:{self._listen_port}"

    @property
    def upstream_addr(self) -> str:
        return f"{self._upstream_host}:{self._upstream_port}"

    @property
    def proxy_name(self) -> str:
        return self._proxy_name

    @property
    def is_active(self) -> bool:
        return self._proxy is not None

    def __enter__(self) -> "ToxiproxyHarness":
        if self._entered:
            raise RuntimeError("ToxiproxyHarness already entered")
        self._entered = True

        if not self._client.health_check():
            raise ToxiproxyConnectionError(
                f"Toxiproxy not available at {self._config.api_host}:{self._config.api_port}. "
                "Start Toxiproxy with: docker-compose -f docker-compose.chaos.yml up -d"
            )

        existing = self._client.get_proxy(self._proxy_name)
        if existing:
            self._client.delete_proxy(self._proxy_name)

        self._proxy = self._client.create_proxy(
            name=self._proxy_name,
            listen=self.proxy_listen_addr,
            upstream=self.upstream_addr,
        )
        _wait_for_listen_port(self._listen_host, self._listen_port)
        return self

    def __exit__(self, exc_type: Any, exc_val: Any, exc_tb: Any) -> None:
        if self._auto_cleanup and self._proxy is not None:
            try:
                self._client.delete_proxy(self._proxy_name)
            except ToxiproxyError:
                pass
        self._proxy = None
        self._toxics.clear()
        self._entered = False

    def add_toxic(
        self,
        toxic_type: str,
        *,
        name: Optional[str] = None,
        stream: str = "downstream",
        toxicity: float = 1.0,
        attributes: Optional[Mapping[str, Any]] = None,
    ) -> Toxic:
        if self._proxy is None:
            raise RuntimeError("Harness not active; use within 'with' block")
        toxic = self._client.add_toxic(
            self._proxy_name,
            toxic_type,
            name=name,
            stream=stream,
            toxicity=toxicity,
            attributes=attributes,
        )
        self._toxics.append(toxic.name)
        return toxic

    def remove_toxic(self, toxic_name: str) -> None:
        if self._proxy is None:
            raise RuntimeError("Harness not active; use within 'with' block")
        self._client.remove_toxic(self._proxy_name, toxic_name)
        if toxic_name in self._toxics:
            self._toxics.remove(toxic_name)

    def clear_toxics(self) -> None:
        if self._proxy is None:
            raise RuntimeError("Harness not active; use within 'with' block")
        for name in list(self._toxics):
            try:
                self._client.remove_toxic(self._proxy_name, name)
            except ToxiproxyError:
                pass
        self._toxics.clear()

    def list_toxics(self) -> list[Toxic]:
        if self._proxy is None:
            raise RuntimeError("Harness not active; use within 'with' block")
        return self._client.list_toxics(self._proxy_name)

    def limit_data(self, bytes_limit: int, *, stream: str = "downstream") -> Toxic:
        return self.add_toxic("limit_data", stream=stream, attributes={"bytes": int(bytes_limit)})

    def reset_peer(self, timeout_ms: int = 0, *, stream: str = "downstream") -> Toxic:
        return self.add_toxic("reset_peer", stream=stream, attributes={"timeout": int(timeout_ms)})

    def latency(
        self,
        latency_ms: int,
        jitter_ms: int = 0,
        *,
        stream: str = "downstream",
    ) -> Toxic:
        return self.add_toxic(
            "latency",
            stream=stream,
            attributes={"latency": int(latency_ms), "jitter": int(jitter_ms)},
        )

    def timeout(self, timeout_ms: int, *, stream: str = "downstream") -> Toxic:
        return self.add_toxic("timeout", stream=stream, attributes={"timeout": int(timeout_ms)})

    def slow_close(self, delay_ms: int, *, stream: str = "downstream") -> Toxic:
        return self.add_toxic("slow_close", stream=stream, attributes={"delay": int(delay_ms)})

    def bandwidth(self, rate_kb: int, *, stream: str = "downstream") -> Toxic:
        return self.add_toxic("bandwidth", stream=stream, attributes={"rate": int(rate_kb)})

    def slicer(
        self,
        average_size: int,
        size_variation: int = 0,
        delay_us: int = 0,
        *,
        stream: str = "downstream",
    ) -> Toxic:
        return self.add_toxic(
            "slicer",
            stream=stream,
            attributes={
                "average_size": int(average_size),
                "size_variation": int(size_variation),
                "delay": int(delay_us),
            },
        )


@contextmanager
def toxiproxy_session(
    upstream_host: str = "127.0.0.1",
    upstream_port: int = 65432,
    *,
    listen_port: Optional[int] = None,
    config: ToxiproxyConfig = _DEFAULT_CONFIG,
) -> Generator[ToxiproxyHarness, None, None]:
    harness = ToxiproxyHarness(
        upstream_host=upstream_host,
        upstream_port=upstream_port,
        listen_port=listen_port,
        config=config,
    )
    with harness:
        yield harness
