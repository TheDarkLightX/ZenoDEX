"""Chaos tests for tau_net_client.py network fault resilience.

These tests verify fail-closed behavior under:
- Truncated TCP replies
- Connection reset (TCP RST)
- Timeout/latency
"""

from __future__ import annotations

import json
import socket
import sys
import threading
import time
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from src.integration.tau_net_client import (
    TauNetRpcError,
    TauNetTcpClient,
    TauNetTcpConfig,
)
from tests.chaos.conftest import MockTcpServer, requires_toxiproxy


class TestTauNetClientTruncatedTcp:
    """Test TauNetTcpClient fails closed under truncated TCP."""

    def test_truncated_response_raises_error(
        self, mock_tcp_server: MockTcpServer
    ) -> None:
        """Verify truncated response raises error, not partial parse."""
        full_response = b'{"status": "ok", "data": "some_long_value_here"}\n'
        mock_tcp_server.set_response(full_response[:20])  # Truncate

        config = TauNetTcpConfig(
            host=mock_tcp_server.host,
            port=mock_tcp_server.port,
            timeout_s=2.0,
        )
        client = TauNetTcpClient(config)

        with pytest.raises(TauNetRpcError, match="closed before response terminator") as exc_info:
            client.rpc("test")

        assert "some_long_value_here" not in str(exc_info.value)

    def test_truncated_json_not_parsed_as_valid(
        self, mock_tcp_server: MockTcpServer
    ) -> None:
        """Verify truncated JSON is not parsed as valid."""
        truncated = b'{"balance": 1000, "nonce":\n'  # Invalid JSON
        mock_tcp_server.set_response(truncated)

        config = TauNetTcpConfig(
            host=mock_tcp_server.host,
            port=mock_tcp_server.port,
            timeout_s=2.0,
        )
        client = TauNetTcpClient(config)

        result = client.rpc("getbalance test")

        with pytest.raises(json.JSONDecodeError):
            json.loads(result)

    def test_mid_frame_disconnect_handled(self) -> None:
        """Verify mid-frame disconnect is handled gracefully."""
        server_port = self._find_free_port()
        disconnected = threading.Event()

        def serve_and_disconnect() -> None:
            with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
                s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
                s.bind(("127.0.0.1", server_port))
                s.listen(1)
                s.settimeout(5.0)
                try:
                    conn, _ = s.accept()
                    conn.recv(1024)
                    conn.send(b'BALANCE:')  # Partial response
                    time.sleep(0.1)
                    conn.close()  # Disconnect mid-frame
                    disconnected.set()
                except Exception:
                    pass

        server_thread = threading.Thread(target=serve_and_disconnect, daemon=True)
        server_thread.start()
        time.sleep(0.1)

        config = TauNetTcpConfig(
            host="127.0.0.1",
            port=server_port,
            timeout_s=2.0,
        )
        client = TauNetTcpClient(config)

        with pytest.raises(TauNetRpcError, match="closed before response terminator") as exc_info:
            client.rpc("getbalance test")

        server_thread.join(timeout=2.0)
        assert disconnected.is_set()
        assert "BALANCE:" not in str(exc_info.value)

    def _find_free_port(self) -> int:
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
            s.bind(("127.0.0.1", 0))
            return int(s.getsockname()[1])


class TestTauNetClientResetPeer:
    """Test TauNetTcpClient handles reset_peer without retry storm."""

    def test_connection_reset_raises_error(self) -> None:
        """Verify connection reset raises error quickly."""
        server_port = self._find_free_port()

        def serve_and_reset() -> None:
            with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
                s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
                s.setsockopt(socket.SOL_SOCKET, socket.SO_LINGER, b'\x01\x00\x00\x00\x00\x00\x00\x00')
                s.bind(("127.0.0.1", server_port))
                s.listen(1)
                s.settimeout(5.0)
                try:
                    conn, _ = s.accept()
                    conn.setsockopt(socket.SOL_SOCKET, socket.SO_LINGER, b'\x01\x00\x00\x00\x00\x00\x00\x00')
                    conn.close()  # RST
                except Exception:
                    pass

        server_thread = threading.Thread(target=serve_and_reset, daemon=True)
        server_thread.start()
        time.sleep(0.1)

        config = TauNetTcpConfig(
            host="127.0.0.1",
            port=server_port,
            timeout_s=2.0,
        )
        client = TauNetTcpClient(config)

        t0 = time.monotonic()
        with pytest.raises((TauNetRpcError, ConnectionError, BrokenPipeError, OSError)):
            client.rpc("test")
        elapsed = time.monotonic() - t0

        assert elapsed < 3.0, f"Should fail quickly; elapsed={elapsed:.2f}s"
        server_thread.join(timeout=2.0)

    def test_no_retry_storm_on_reset(self) -> None:
        """Verify no retry storm (>3 connects in 1s) on reset."""
        server_port = self._find_free_port()
        connection_times: list[float] = []
        lock = threading.Lock()

        def count_connections() -> None:
            with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
                s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
                s.bind(("127.0.0.1", server_port))
                s.listen(10)
                s.settimeout(3.0)
                while True:
                    try:
                        conn, _ = s.accept()
                        with lock:
                            connection_times.append(time.time())
                        conn.close()
                    except socket.timeout:
                        break
                    except Exception:
                        break

        server_thread = threading.Thread(target=count_connections, daemon=True)
        server_thread.start()
        time.sleep(0.1)

        config = TauNetTcpConfig(
            host="127.0.0.1",
            port=server_port,
            timeout_s=1.0,
        )
        client = TauNetTcpClient(config)

        try:
            client.rpc("test")
        except Exception:
            pass

        server_thread.join(timeout=4.0)

        with lock:
            if len(connection_times) >= 2:
                time_span = connection_times[-1] - connection_times[0]
                connections_per_second = len(connection_times) / max(time_span, 0.001)
                assert connections_per_second < 10, f"Retry storm detected: {connections_per_second:.1f} conn/s"

    def _find_free_port(self) -> int:
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
            s.bind(("127.0.0.1", 0))
            return int(s.getsockname()[1])


class TestTauNetClientTimeout:
    """Test TauNetTcpClient handles timeouts correctly."""

    def test_timeout_raises_rpc_error(self, mock_tcp_server: MockTcpServer) -> None:
        """Verify timeout raises TauNetRpcError."""
        mock_tcp_server.set_delay_ms(5000)  # 5s delay

        config = TauNetTcpConfig(
            host=mock_tcp_server.host,
            port=mock_tcp_server.port,
            timeout_s=0.5,
        )
        client = TauNetTcpClient(config)

        t0 = time.monotonic()
        with pytest.raises(TauNetRpcError) as exc_info:
            client.rpc("test")
        elapsed = time.monotonic() - t0

        assert elapsed < 2.0, f"Should timeout quickly; elapsed={elapsed:.2f}s"
        msg = str(exc_info.value).lower()
        assert "timeout" in msg or "timed out" in msg

    def test_slow_response_within_timeout_succeeds(
        self, mock_tcp_server: MockTcpServer
    ) -> None:
        """Verify slow response within timeout succeeds."""
        mock_tcp_server.set_response(b"SEQUENCE:42\n")
        mock_tcp_server.set_delay_ms(100)  # 100ms delay

        config = TauNetTcpConfig(
            host=mock_tcp_server.host,
            port=mock_tcp_server.port,
            timeout_s=2.0,
        )
        client = TauNetTcpClient(config)

        result = client.rpc("getsequence test")

        assert "42" in result


@requires_toxiproxy
class TestTauNetClientToxiproxy:
    """Chaos tests using Toxiproxy for network fault injection."""

    def test_limit_data_toxic_handled(self, mock_tcp_server: MockTcpServer) -> None:
        """Verify limit_data toxic is handled gracefully."""
        from tools.chaos.toxiproxy_harness import ToxiproxyHarness

        mock_tcp_server.set_response(b'{"result": "this is a long response that will be truncated"}\n')

        with ToxiproxyHarness(
            upstream_host=mock_tcp_server.host,
            upstream_port=mock_tcp_server.port,
        ) as harness:
            harness.limit_data(50)

            config = TauNetTcpConfig(
                host=harness.listen_host,
                port=harness.listen_port,
                timeout_s=2.0,
            )
            client = TauNetTcpClient(config)

            with pytest.raises(TauNetRpcError, match="closed before response terminator"):
                client.rpc("test")

    def test_reset_peer_toxic_handled(self, mock_tcp_server: MockTcpServer) -> None:
        """Verify reset_peer toxic is handled gracefully."""
        from tools.chaos.toxiproxy_harness import ToxiproxyHarness

        mock_tcp_server.set_response(b"OK\n")

        with ToxiproxyHarness(
            upstream_host=mock_tcp_server.host,
            upstream_port=mock_tcp_server.port,
        ) as harness:
            harness.reset_peer(timeout_ms=0)

            config = TauNetTcpConfig(
                host=harness.listen_host,
                port=harness.listen_port,
                timeout_s=2.0,
            )
            client = TauNetTcpClient(config)

            with pytest.raises((TauNetRpcError, ConnectionError, OSError)):
                client.rpc("test")
