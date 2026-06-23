"""Pytest fixtures for chaos engineering tests."""

from __future__ import annotations

import json
import os
import socket
import subprocess
import sys
import threading
import time
from pathlib import Path
from typing import Any, Generator, Optional

import pytest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))


def _find_free_port() -> int:
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
        s.bind(("127.0.0.1", 0))
        s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        return int(s.getsockname()[1])


@pytest.fixture
def chaos_output_dir(tmp_path: Path) -> Path:
    """Temporary directory for chaos experiment artifacts."""
    out = tmp_path / "chaos_output"
    out.mkdir(parents=True, exist_ok=True)
    return out


@pytest.fixture
def free_port() -> int:
    """Find a free TCP port for testing."""
    return _find_free_port()


class MockTcpServer:
    """Simple TCP server for testing TauNetTcpClient."""

    def __init__(self, host: str = "127.0.0.1", port: Optional[int] = None) -> None:
        self._host = str(host)
        self._port = int(port) if port else _find_free_port()
        self._socket: Optional[socket.socket] = None
        self._thread: Optional[threading.Thread] = None
        self._running = False
        self._response: bytes = b"OK\n"
        self._delay_ms: int = 0
        self._connections: list[tuple[float, str]] = []
        self._lock = threading.Lock()

    @property
    def host(self) -> str:
        return self._host

    @property
    def port(self) -> int:
        return self._port

    @property
    def addr(self) -> str:
        return f"{self._host}:{self._port}"

    @property
    def connection_count(self) -> int:
        with self._lock:
            return len(self._connections)

    def set_response(self, response: bytes) -> None:
        self._response = bytes(response)

    def set_delay_ms(self, delay_ms: int) -> None:
        self._delay_ms = int(delay_ms)

    def start(self) -> "MockTcpServer":
        if self._running:
            return self
        self._socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self._socket.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self._socket.bind((self._host, self._port))
        self._socket.listen(5)
        self._socket.settimeout(0.5)
        self._running = True
        self._thread = threading.Thread(target=self._serve, daemon=True)
        self._thread.start()
        return self

    def stop(self) -> None:
        self._running = False
        if self._socket:
            try:
                self._socket.close()
            except Exception:
                pass
        if self._thread:
            self._thread.join(timeout=2.0)

    def _serve(self) -> None:
        while self._running:
            try:
                conn, addr = self._socket.accept()  # type: ignore
            except socket.timeout:
                continue
            except Exception:
                break
            with self._lock:
                self._connections.append((time.time(), str(addr)))
            try:
                conn.settimeout(1.0)
                try:
                    conn.recv(4096)
                except Exception:
                    pass
                if self._delay_ms > 0:
                    time.sleep(float(self._delay_ms) / 1000.0)
                conn.sendall(self._response)
            except Exception:
                pass
            finally:
                try:
                    conn.close()
                except Exception:
                    pass

    def __enter__(self) -> "MockTcpServer":
        return self.start()

    def __exit__(self, *args: Any) -> None:
        self.stop()


@pytest.fixture
def mock_tcp_server() -> Generator[MockTcpServer, None, None]:
    """A mock TCP server for testing network clients."""
    server = MockTcpServer()
    with server:
        yield server


class MockTauBinary:
    """Mock tau binary for testing tau_runner without real tau."""

    def __init__(self, tmp_path: Path) -> None:
        self._tmp_path = tmp_path
        self._script_path = tmp_path / "mock_tau.py"
        self._behavior = "echo"
        self._exit_code = 0
        self._stdout_bytes = 0
        self._delay_s = 0.0

    @property
    def path(self) -> str:
        return str(self._script_path)

    def set_behavior(
        self,
        behavior: str,
        *,
        exit_code: int = 0,
        stdout_bytes: int = 0,
        delay_s: float = 0.0,
    ) -> "MockTauBinary":
        self._behavior = str(behavior)
        self._exit_code = int(exit_code)
        self._stdout_bytes = int(stdout_bytes)
        self._delay_s = float(delay_s)
        self._write_script()
        return self

    def _write_script(self) -> None:
        if self._behavior == "echo":
            script = f"""#!/usr/bin/env python3
import sys
sys.stdout.write("o1[0] := 1\\n")
sys.stdout.flush()
sys.exit({self._exit_code})
"""
        elif self._behavior == "flood_stdout":
            script = f"""#!/usr/bin/env python3
import sys
chunk = b"X" * 65536
remaining = {self._stdout_bytes}
while remaining > 0:
    n = min(65536, remaining)
    sys.stdout.buffer.write(chunk[:n])
    sys.stdout.buffer.flush()
    remaining -= n
sys.exit({self._exit_code})
"""
        elif self._behavior == "hang":
            script = f"""#!/usr/bin/env python3
import time
time.sleep({self._delay_s})
import sys
sys.exit({self._exit_code})
"""
        elif self._behavior == "slow_output":
            script = f"""#!/usr/bin/env python3
import time
import sys
time.sleep({self._delay_s})
sys.stdout.write("o1[0] := 1\\n")
sys.stdout.flush()
sys.exit({self._exit_code})
"""
        else:
            script = f"""#!/usr/bin/env python3
import sys
sys.exit({self._exit_code})
"""

        self._script_path.write_text(script)
        self._script_path.chmod(0o755)

    def create(self) -> "MockTauBinary":
        self._write_script()
        return self


@pytest.fixture
def mock_tau_binary(tmp_path: Path) -> MockTauBinary:
    """A mock tau binary for testing tau_runner."""
    return MockTauBinary(tmp_path).create()


def toxiproxy_available() -> bool:
    """Check if Toxiproxy is available."""
    try:
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
            s.settimeout(1.0)
            s.connect(("127.0.0.1", 8474))
            return True
    except Exception:
        return False


requires_toxiproxy = pytest.mark.skipif(
    not toxiproxy_available(),
    reason="Toxiproxy not available at 127.0.0.1:8474",
)
