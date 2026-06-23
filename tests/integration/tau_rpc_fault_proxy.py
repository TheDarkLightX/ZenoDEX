from __future__ import annotations

import socket
import socketserver
import threading
from dataclasses import dataclass
from typing import Any


@dataclass(frozen=True)
class TauRpcFaultProxyStats:
    total_requests: int
    sendtx_requests: int
    truncated_sendtx_responses: int


class _TauRpcFaultProxyHandler(socketserver.StreamRequestHandler):
    def handle(self) -> None:
        line = self.rfile.readline()
        if not line:
            return
        is_sendtx = line.decode("utf-8", errors="replace").strip().startswith("sendtx ")
        server: _TauRpcFaultProxyServer = self.server  # type: ignore[assignment]
        with server.stats_lock:
            server.total_requests += 1
            if is_sendtx:
                server.sendtx_requests += 1

        response = bytearray()
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as upstream:
            upstream.settimeout(server.upstream_timeout_s)
            upstream.connect((server.upstream_host, server.upstream_port))
            upstream.sendall(line)
            remaining = server.max_response_bytes
            while remaining > 0:
                chunk = upstream.recv(min(4096, remaining))
                if not chunk:
                    break
                response += chunk
                remaining -= len(chunk)
                if b"\n" in response:
                    break

        if is_sendtx and server.truncate_sendtx_response_bytes is not None:
            with server.stats_lock:
                server.truncated_sendtx_responses += 1
            n = max(0, int(server.truncate_sendtx_response_bytes))
            if n > 0:
                self.wfile.write(bytes(response[:n]))
                self.wfile.flush()
            return

        self.wfile.write(bytes(response))
        self.wfile.flush()


class _TauRpcFaultProxyServer(socketserver.ThreadingTCPServer):
    allow_reuse_address = True
    daemon_threads = True

    def __init__(
        self,
        server_address: tuple[str, int],
        handler_class: type[socketserver.StreamRequestHandler],
        *,
        upstream_host: str,
        upstream_port: int,
        truncate_sendtx_response_bytes: int | None,
        upstream_timeout_s: float,
        max_response_bytes: int,
    ) -> None:
        super().__init__(server_address, handler_class)
        self.upstream_host = upstream_host
        self.upstream_port = int(upstream_port)
        self.truncate_sendtx_response_bytes = truncate_sendtx_response_bytes
        self.upstream_timeout_s = float(upstream_timeout_s)
        self.max_response_bytes = int(max_response_bytes)
        self.stats_lock = threading.Lock()
        self.total_requests = 0
        self.sendtx_requests = 0
        self.truncated_sendtx_responses = 0


class TauRpcFaultProxy:
    def __init__(
        self,
        *,
        upstream_host: str,
        upstream_port: int,
        listen_host: str = "127.0.0.1",
        listen_port: int = 0,
        truncate_sendtx_response_bytes: int | None = None,
        upstream_timeout_s: float = 2.0,
        max_response_bytes: int = 1_048_576,
    ) -> None:
        self._server = _TauRpcFaultProxyServer(
            (listen_host, int(listen_port)),
            _TauRpcFaultProxyHandler,
            upstream_host=upstream_host,
            upstream_port=int(upstream_port),
            truncate_sendtx_response_bytes=truncate_sendtx_response_bytes,
            upstream_timeout_s=float(upstream_timeout_s),
            max_response_bytes=int(max_response_bytes),
        )
        self._thread: threading.Thread | None = None

    @property
    def host(self) -> str:
        return str(self._server.server_address[0])

    @property
    def port(self) -> int:
        return int(self._server.server_address[1])

    def start(self) -> "TauRpcFaultProxy":
        if self._thread is not None:
            raise RuntimeError("proxy already started")
        self._thread = threading.Thread(target=self._server.serve_forever, daemon=True)
        self._thread.start()
        return self

    def close(self) -> None:
        self._server.shutdown()
        self._server.server_close()
        if self._thread is not None:
            self._thread.join(timeout=2.0)
            self._thread = None

    def stats(self) -> TauRpcFaultProxyStats:
        with self._server.stats_lock:
            return TauRpcFaultProxyStats(
                total_requests=int(self._server.total_requests),
                sendtx_requests=int(self._server.sendtx_requests),
                truncated_sendtx_responses=int(self._server.truncated_sendtx_responses),
            )

    def __enter__(self) -> "TauRpcFaultProxy":
        return self.start()

    def __exit__(self, *_exc: Any) -> None:
        self.close()
