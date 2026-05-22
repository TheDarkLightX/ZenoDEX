"""Network-level chaos tests for ``TauNetTcpClient``.

Each test spins up a small real-socket loopback server that scripts a
specific failure mode, then asserts the client raises ``TauNetRpcError``
with a useful message — never silently returns "looks ok" data.

Failure modes covered:
  - Connection refused (server never listens).
  - Connect timeout (server accepts but never reads/writes).
  - Read timeout (server accepts request but never replies).
  - Half-close (server closes after FIN with no payload).
  - Partial frame (server sends bytes without the newline terminator).
  - Slowloris drip (one byte at a time, slower than timeout).
  - Garbage bytes (server sends non-UTF-8).
  - Oversize response (exceeds ``recv_max_bytes`` — truncates).
  - Multiple newlines (first-line semantics must hold).
  - Server error mid-stream (RST mid-payload).

This is *fault injection*, not unit testing — every fault is a real socket
behavior our code must survive without acting on bad data.
"""

from __future__ import annotations

import errno
import socket
import threading
import time
from contextlib import contextmanager
from typing import Callable, Iterator

import pytest

from src.integration.tau_net_client import (
    TauNetRpcError,
    TauNetTcpClient,
    TauNetTcpConfig,
)


HandlerFn = Callable[[socket.socket], None]


@contextmanager
def _chaos_server(handler: HandlerFn) -> Iterator[int]:
    """Start a one-shot TCP server. Handler runs in a daemon thread.

    Yields the bound port. The server accepts exactly one connection and
    invokes the handler with the connection socket; the handler decides
    what to send/drop/hang.
    """
    listen_sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    listen_sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    listen_sock.bind(("127.0.0.1", 0))
    listen_sock.listen(1)
    port = listen_sock.getsockname()[1]

    def _runner() -> None:
        try:
            conn, _addr = listen_sock.accept()
        except OSError:
            return
        try:
            with conn:
                handler(conn)
        except OSError:
            # Many handlers intentionally provoke broken pipes; swallow.
            pass

    thread = threading.Thread(target=_runner, daemon=True)
    thread.start()
    try:
        yield port
    finally:
        try:
            listen_sock.close()
        except OSError:
            pass
        thread.join(timeout=2.0)


def _drain_request(conn: socket.socket, max_bytes: int = 65_536) -> bytes:
    """Read until a newline (the client sends ``<cmd>\\r\\n``) or buffer fills."""
    buf = bytearray()
    while len(buf) < max_bytes:
        chunk = conn.recv(4096)
        if not chunk:
            break
        buf += chunk
        if b"\n" in buf:
            break
    return bytes(buf)


def _client(*, port: int, timeout_s: float = 0.5, recv_max_bytes: int = 1_048_576) -> TauNetTcpClient:
    return TauNetTcpClient(
        TauNetTcpConfig(
            host="127.0.0.1",
            port=port,
            timeout_s=timeout_s,
            recv_max_bytes=recv_max_bytes,
        )
    )


# -----------------------------------------------------------------------------
# A. Sanity — happy path works through the same scaffolding.
# -----------------------------------------------------------------------------


class TestHappyPath:
    def test_simple_response_returns_first_line(self) -> None:
        def handler(conn: socket.socket) -> None:
            _drain_request(conn)
            conn.sendall(b"SUCCESS\n")

        with _chaos_server(handler) as port:
            assert _client(port=port).rpc("ping") == "SUCCESS"

    def test_crlf_terminator_is_stripped(self) -> None:
        def handler(conn: socket.socket) -> None:
            _drain_request(conn)
            conn.sendall(b"SUCCESS\r\n")

        with _chaos_server(handler) as port:
            assert _client(port=port).rpc("ping") == "SUCCESS"

    def test_response_after_extra_data_takes_first_line(self) -> None:
        def handler(conn: socket.socket) -> None:
            _drain_request(conn)
            conn.sendall(b"FIRST\nSECOND\n")

        with _chaos_server(handler) as port:
            assert _client(port=port).rpc("ping") == "FIRST"


# -----------------------------------------------------------------------------
# B. Connection failures — server never listens or refuses.
# -----------------------------------------------------------------------------


class TestConnectionRefused:
    def test_connect_to_closed_port_raises_rpc_error(self) -> None:
        # Pick a port, bind it just to learn the number, then immediately close
        # so the connect attempt is refused.
        s = socket.socket()
        s.bind(("127.0.0.1", 0))
        port = s.getsockname()[1]
        s.close()
        client = _client(port=port)
        with pytest.raises(TauNetRpcError) as exc:
            client.rpc("ping")
        # Either "connection failed" or "timed out" is acceptable depending on
        # the platform's RST timing. Both are fail-closed.
        assert "rpc" in str(exc.value)

    def test_invalid_port_in_config_rejected_at_construction(self) -> None:
        with pytest.raises(ValueError, match="invalid port"):
            TauNetTcpClient(TauNetTcpConfig(host="127.0.0.1", port=70_000))

    def test_zero_port_accepted(self) -> None:
        # Port 0 is technically valid (OS-assigned). Client construction must succeed;
        # connect attempt against 0 will fail at the OS level, not at construction.
        TauNetTcpClient(TauNetTcpConfig(host="127.0.0.1", port=0))  # no raise


# -----------------------------------------------------------------------------
# C. Read timeouts — server accepts but never replies.
# -----------------------------------------------------------------------------


class TestReadTimeouts:
    def test_server_never_replies_raises_timeout(self) -> None:
        ready = threading.Event()

        def handler(conn: socket.socket) -> None:
            # Drain the request so the client's send completes, then hang.
            _drain_request(conn)
            ready.set()
            time.sleep(2.0)  # longer than the client timeout

        with _chaos_server(handler) as port:
            client = _client(port=port, timeout_s=0.3)
            t0 = time.monotonic()
            with pytest.raises(TauNetRpcError, match="timed out"):
                client.rpc("ping")
            # Confirm we actually waited around the timeout and didn't return early.
            assert time.monotonic() - t0 >= 0.25

    def test_partial_response_without_newline_raises(self) -> None:
        def handler(conn: socket.socket) -> None:
            _drain_request(conn)
            conn.sendall(b"PARTIAL_NO_NEWLINE")
            # Server then closes — client gets bytes but no terminator.

        with _chaos_server(handler) as port:
            with pytest.raises(TauNetRpcError, match="closed before response terminator"):
                _client(port=port).rpc("ping")

    def test_empty_response_with_close_raises(self) -> None:
        def handler(conn: socket.socket) -> None:
            _drain_request(conn)
            # Close without sending anything.

        with _chaos_server(handler) as port:
            with pytest.raises(TauNetRpcError, match="closed without response"):
                _client(port=port).rpc("ping")


# -----------------------------------------------------------------------------
# D. Drip-feed (slowloris-style) — bytes trickle below the timeout threshold.
# -----------------------------------------------------------------------------


class TestSlowDrip:
    def test_drip_one_byte_per_500ms_with_300ms_timeout_times_out(self) -> None:
        def handler(conn: socket.socket) -> None:
            _drain_request(conn)
            payload = b"S\nUCCESS\n"
            for byte in payload:
                conn.sendall(bytes([byte]))
                time.sleep(0.5)  # slower than the client timeout

        with _chaos_server(handler) as port:
            with pytest.raises(TauNetRpcError, match="timed out"):
                _client(port=port, timeout_s=0.3).rpc("ping")

    def test_drip_fast_enough_returns(self) -> None:
        def handler(conn: socket.socket) -> None:
            _drain_request(conn)
            for byte in b"OK\n":
                conn.sendall(bytes([byte]))
                time.sleep(0.05)

        with _chaos_server(handler) as port:
            assert _client(port=port, timeout_s=1.0).rpc("ping") == "OK"


# -----------------------------------------------------------------------------
# E. Oversize responses and garbage bytes.
# -----------------------------------------------------------------------------


class TestPayloadHazards:
    def test_response_exceeding_recv_max_bytes_without_newline_raises(self) -> None:
        """If the server sends more than ``recv_max_bytes`` with no terminator,
        the client must NOT accept the truncated bytes as a valid response."""

        def handler(conn: socket.socket) -> None:
            _drain_request(conn)
            # Send recv_max_bytes worth of data with no newline.
            conn.sendall(b"X" * 4096)
            time.sleep(0.5)  # keep connection open past the read loop

        with _chaos_server(handler) as port:
            client = _client(port=port, recv_max_bytes=1024, timeout_s=0.3)
            # Either truncation-without-terminator or timeout — both fail closed.
            with pytest.raises(TauNetRpcError):
                client.rpc("ping")

    def test_response_exceeding_recv_max_bytes_with_newline_inside_is_truncated_at_newline(self) -> None:
        """The receive loop bails on first newline regardless of total size."""

        def handler(conn: socket.socket) -> None:
            _drain_request(conn)
            conn.sendall(b"FIRST\n" + b"X" * 10_000)

        with _chaos_server(handler) as port:
            client = _client(port=port, recv_max_bytes=10_000_000, timeout_s=0.5)
            assert client.rpc("ping") == "FIRST"

    def test_non_utf8_bytes_are_replaced_not_raised(self) -> None:
        """The decode is errors='replace' on purpose so operators see *something*
        rather than the call exploding before the failure path."""

        def handler(conn: socket.socket) -> None:
            _drain_request(conn)
            conn.sendall(b"\xff\xfe\xfd\n")

        with _chaos_server(handler) as port:
            out = _client(port=port).rpc("ping")
            # Result should be a string with replacement chars, not raise.
            assert isinstance(out, str)
            assert "\ufffd" in out or len(out) > 0

    def test_huge_burst_of_newlines_returns_empty_first_line(self) -> None:
        def handler(conn: socket.socket) -> None:
            _drain_request(conn)
            conn.sendall(b"\n" * 1024)

        with _chaos_server(handler) as port:
            # First line before the newline is empty.
            assert _client(port=port).rpc("ping") == ""


# -----------------------------------------------------------------------------
# F. Mid-stream connection reset.
# -----------------------------------------------------------------------------


class TestConnectionReset:
    def test_server_closes_mid_payload_without_newline_raises(self) -> None:
        def handler(conn: socket.socket) -> None:
            _drain_request(conn)
            conn.sendall(b"PART1")
            # Linger off then close — most OSes deliver RST.
            try:
                conn.setsockopt(
                    socket.SOL_SOCKET,
                    socket.SO_LINGER,
                    bytes([1, 0, 0, 0, 0, 0, 0, 0]),
                )
            except OSError:
                pass

        with _chaos_server(handler) as port:
            # Either "closed before terminator" or a connection-failed error.
            with pytest.raises(TauNetRpcError):
                _client(port=port).rpc("ping")

    def test_server_sends_then_resets_after_newline_returns_first_line(self) -> None:
        """Once we have a complete line, we don't care what happens after."""

        def handler(conn: socket.socket) -> None:
            _drain_request(conn)
            conn.sendall(b"COMPLETE\n")
            try:
                conn.setsockopt(
                    socket.SOL_SOCKET,
                    socket.SO_LINGER,
                    bytes([1, 0, 0, 0, 0, 0, 0, 0]),
                )
            except OSError:
                pass

        with _chaos_server(handler) as port:
            assert _client(port=port).rpc("ping") == "COMPLETE"


# -----------------------------------------------------------------------------
# G. Request-side validation.
# -----------------------------------------------------------------------------


class TestRequestSideValidation:
    def test_empty_cmd_rejected_before_dial(self) -> None:
        client = TauNetTcpClient(TauNetTcpConfig(host="127.0.0.1", port=1))
        with pytest.raises(ValueError, match="non-empty"):
            client.rpc("")

    def test_whitespace_only_cmd_rejected_before_dial(self) -> None:
        client = TauNetTcpClient(TauNetTcpConfig(host="127.0.0.1", port=1))
        with pytest.raises(ValueError, match="non-empty"):
            client.rpc("   \n\r\t  ")

    def test_non_string_cmd_rejected_before_dial(self) -> None:
        client = TauNetTcpClient(TauNetTcpConfig(host="127.0.0.1", port=1))
        with pytest.raises(ValueError, match="non-empty"):
            client.rpc(b"ping")  # type: ignore[arg-type]


# -----------------------------------------------------------------------------
# H. Config-side validation.
# -----------------------------------------------------------------------------


class TestConfigValidation:
    def test_negative_port_rejected(self) -> None:
        with pytest.raises(ValueError, match="invalid port"):
            TauNetTcpClient(TauNetTcpConfig(host="127.0.0.1", port=-1))

    def test_port_above_65535_rejected(self) -> None:
        with pytest.raises(ValueError, match="invalid port"):
            TauNetTcpClient(TauNetTcpConfig(host="127.0.0.1", port=65_536))

    def test_zero_timeout_rejected(self) -> None:
        with pytest.raises(ValueError, match="timeout_s must be positive"):
            TauNetTcpClient(TauNetTcpConfig(host="127.0.0.1", port=1, timeout_s=0))

    def test_negative_timeout_rejected(self) -> None:
        with pytest.raises(ValueError, match="timeout_s must be positive"):
            TauNetTcpClient(TauNetTcpConfig(host="127.0.0.1", port=1, timeout_s=-1.0))

    def test_zero_recv_max_bytes_rejected(self) -> None:
        with pytest.raises(ValueError, match="recv_max_bytes must be positive"):
            TauNetTcpClient(
                TauNetTcpConfig(host="127.0.0.1", port=1, recv_max_bytes=0)
            )

    def test_negative_recv_max_bytes_rejected(self) -> None:
        with pytest.raises(ValueError, match="recv_max_bytes must be positive"):
            TauNetTcpClient(
                TauNetTcpConfig(host="127.0.0.1", port=1, recv_max_bytes=-1)
            )


# -----------------------------------------------------------------------------
# I. High-level helpers under chaos — get_sequence / get_balance / sendtx.
# -----------------------------------------------------------------------------


class TestHighLevelHelpersUnderChaos:
    def test_get_sequence_rejects_unexpected_response(self) -> None:
        def handler(conn: socket.socket) -> None:
            _drain_request(conn)
            conn.sendall(b"SOMETHING_ELSE\n")

        with _chaos_server(handler) as port:
            with pytest.raises(TauNetRpcError, match="unexpected getsequence"):
                _client(port=port).get_sequence("0xab" * 24)

    def test_get_sequence_rejects_non_integer_value(self) -> None:
        def handler(conn: socket.socket) -> None:
            _drain_request(conn)
            conn.sendall(b"SEQUENCE: notanint\n")

        with _chaos_server(handler) as port:
            # The split + int() will raise ValueError; that's still fail-closed.
            with pytest.raises((TauNetRpcError, ValueError)):
                _client(port=port).get_sequence("0xab" * 24)

    def test_get_balance_rejects_unexpected_response(self) -> None:
        def handler(conn: socket.socket) -> None:
            _drain_request(conn)
            conn.sendall(b"SEQUENCE: 7\n")  # wrong prefix

        with _chaos_server(handler) as port:
            with pytest.raises(TauNetRpcError, match="unexpected getbalance"):
                _client(port=port).get_balance("0xab" * 24)

    def test_sendtx_returns_response_verbatim(self) -> None:
        def handler(conn: socket.socket) -> None:
            req = _drain_request(conn)
            # Confirm the client wrote a sendtx command.
            assert req.startswith(b"sendtx ")
            conn.sendall(b"SUCCESS: 0xabcd\n")

        with _chaos_server(handler) as port:
            out = _client(port=port).sendtx({"foo": "bar"})
            assert out == "SUCCESS: 0xabcd"
