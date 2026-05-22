"""Adversarial server impersonation tests.

Honest-but-broken servers are covered in ``test_zeno_ledger_chaos_network.py``.
This file covers a *hostile* server: one that deliberately constructs
responses to fool the response parser into accepting a transaction or
misreporting a sequence/balance.

Attacks we simulate:

  - **Multi-line success embed**: ``SUCCESS\\nFAILURE: actually no\\n``.
    Parser must read only the first line.
  - **Prefix smuggling**: ``SUCCESS_HIJACK something\\n`` (looks like SUCCESS
    by string-startswith if rules slip).
  - **Substring smuggling**: ``ERROR: SUCCESS WAS NOT REACHED\\n``. Parser must
    NOT match on substring.
  - **Embedded NUL**: ``SUCCESS\\x00 truncate\\n``. Some C parsers stop on NUL,
    but our Python parser must treat the whole line consistently.
  - **Unicode normalization**: ``SUCCESS\\u0301`` (combining acute). The
    canonical bytes differ from plain ``SUCCESS``.
  - **Sequence forgery**: ``SEQUENCE: 0xff_ff_ff_ff`` (underscore-separated
    int), ``SEQUENCE: 0x10`` (hex when decimal expected), ``SEQUENCE: -1``,
    ``SEQUENCE: 1.5``, ``SEQUENCE: 1e3``.
  - **Balance forgery**: same shape, with attacker trying to inflate the
    reported balance.
  - **Huge prefix padding**: response that starts with ``SUCCESS`` after
    megabytes of whitespace.
  - **Mixed CR/LF**: ``SUCCESS\\r\\nFAILURE\\n`` — must take SUCCESS, not
    concatenate.
  - **Whitespace-only payload then SUCCESS**: ``\\n\\n\\nSUCCESS\\n`` — the
    first line is empty; only the empty string is returned.

For each scenario, we assert either:
  - The parser correctly rejects (raises ``TauNetRpcError``), OR
  - Returns the literal expected first-line bytes (no smuggling).
"""

from __future__ import annotations

import socket
import threading
from contextlib import contextmanager
from typing import Callable, Iterator

import pytest

from src.integration.tau_net_client import (
    TauNetRpcError,
    TauNetTcpClient,
    TauNetTcpConfig,
    tau_rpc_response_is_success,
)


HandlerFn = Callable[[socket.socket], None]


@contextmanager
def _hostile_server(handler: HandlerFn) -> Iterator[int]:
    listen_sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    listen_sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    listen_sock.bind(("127.0.0.1", 0))
    listen_sock.listen(1)
    port = listen_sock.getsockname()[1]

    def _runner() -> None:
        try:
            conn, _ = listen_sock.accept()
        except OSError:
            return
        try:
            with conn:
                handler(conn)
        except OSError:
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
    buf = bytearray()
    while len(buf) < max_bytes:
        chunk = conn.recv(4096)
        if not chunk:
            break
        buf += chunk
        if b"\n" in buf:
            break
    return bytes(buf)


def _client(*, port: int, timeout_s: float = 0.5) -> TauNetTcpClient:
    return TauNetTcpClient(
        TauNetTcpConfig(host="127.0.0.1", port=port, timeout_s=timeout_s)
    )


# -----------------------------------------------------------------------------
# A. Pure-function success parser — adversarial inputs.
# -----------------------------------------------------------------------------


class TestSuccessParserAdversarial:
    """The parser is the choke point. If it accepts hostile inputs, every
    downstream send-tx call inherits the vulnerability."""

    def test_success_substring_in_error_rejected(self) -> None:
        assert tau_rpc_response_is_success("ERROR: SUCCESS WAS NOT REACHED") is False

    def test_success_with_trailing_arbitrary_data(self) -> None:
        # "SUCCESS:something" is acceptable per protocol.
        assert tau_rpc_response_is_success("SUCCESS: anything goes here") is True

    def test_successful_word_rejected(self) -> None:
        # "SUCCESSFUL" doesn't match — no colon/space delimiter after SUCCESS.
        assert tau_rpc_response_is_success("SUCCESSFUL") is False

    def test_success_with_underscore_continuation_rejected(self) -> None:
        # Underscore is not a delimiter.
        assert tau_rpc_response_is_success("SUCCESS_HIJACK") is False

    def test_success_with_unicode_combining_mark_rejected(self) -> None:
        # "SUCCESS" + combining acute (U+0301). After .upper() this remains
        # distinct from "SUCCESS".
        assert tau_rpc_response_is_success("SUCCESS\u0301") is False

    def test_success_with_unicode_homoglyph_rejected(self) -> None:
        # Cyrillic 'С' (U+0421) looks like Latin 'C' but is a different char.
        assert tau_rpc_response_is_success("\u0421UCCESS") is False

    def test_embedded_null_in_success_rejected(self) -> None:
        # "SUCCESS\x00stuff" after strip()+upper() is "SUCCESS\x00STUFF" — no match.
        assert tau_rpc_response_is_success("SUCCESS\x00stuff") is False

    def test_success_preceded_by_whitespace_accepted(self) -> None:
        # strip() removes outer whitespace, so this matches.
        assert tau_rpc_response_is_success("   SUCCESS   ") is True

    def test_success_preceded_by_garbage_rejected(self) -> None:
        assert tau_rpc_response_is_success("garbage SUCCESS") is False

    def test_only_colon_rejected(self) -> None:
        assert tau_rpc_response_is_success("SUCCESS:") is True  # protocol allows
        assert tau_rpc_response_is_success(":SUCCESS") is False

    def test_empty_input_rejected(self) -> None:
        assert tau_rpc_response_is_success("") is False

    def test_whitespace_only_rejected(self) -> None:
        assert tau_rpc_response_is_success("    \t\n   ") is False

    def test_bytes_input_rejected(self) -> None:
        # Type-check at the top — bytes is not str.
        assert tau_rpc_response_is_success(b"SUCCESS") is False

    def test_int_input_rejected(self) -> None:
        assert tau_rpc_response_is_success(0) is False
        assert tau_rpc_response_is_success(1) is False

    def test_none_input_rejected(self) -> None:
        assert tau_rpc_response_is_success(None) is False

    def test_list_input_rejected(self) -> None:
        assert tau_rpc_response_is_success(["SUCCESS"]) is False

    def test_dict_input_rejected(self) -> None:
        assert tau_rpc_response_is_success({"status": "SUCCESS"}) is False


# -----------------------------------------------------------------------------
# B. End-to-end hostile server — multi-line, smuggling.
# -----------------------------------------------------------------------------


class TestHostileServerMultiLine:
    def test_first_line_only_taken_after_success(self) -> None:
        """Server sends SUCCESS\\nthen lies on subsequent lines. We must
        take only the first line."""

        def handler(conn: socket.socket) -> None:
            _drain_request(conn)
            conn.sendall(b"SUCCESS\nFAILURE: actually no\nERROR: rolled back\n")

        with _hostile_server(handler) as port:
            response = _client(port=port).rpc("ping")
            assert response == "SUCCESS"
            # And the parser accepts that response.
            assert tau_rpc_response_is_success(response) is True

    def test_first_line_failure_then_smuggled_success_takes_failure(self) -> None:
        """Server sends FAILURE first, then SUCCESS. We must NOT pick the
        SUCCESS line — only the first line counts."""

        def handler(conn: socket.socket) -> None:
            _drain_request(conn)
            conn.sendall(b"FAILURE: rejected\nSUCCESS: actually accepted\n")

        with _hostile_server(handler) as port:
            response = _client(port=port).rpc("ping")
            assert response == "FAILURE: rejected"
            assert tau_rpc_response_is_success(response) is False

    def test_blank_first_line_then_success_returns_blank(self) -> None:
        def handler(conn: socket.socket) -> None:
            _drain_request(conn)
            conn.sendall(b"\nSUCCESS\n")

        with _hostile_server(handler) as port:
            response = _client(port=port).rpc("ping")
            # First newline is at index 0, so first line is "".
            assert response == ""
            assert tau_rpc_response_is_success(response) is False

    def test_crlf_inside_then_success_takes_first_line(self) -> None:
        def handler(conn: socket.socket) -> None:
            _drain_request(conn)
            # The first newline character ends the first line. CR before LF
            # is stripped from the right.
            conn.sendall(b"SUCCESS\r\nFAILURE\r\n")

        with _hostile_server(handler) as port:
            response = _client(port=port).rpc("ping")
            assert response == "SUCCESS"


# -----------------------------------------------------------------------------
# C. Sequence forgery via hostile responses.
# -----------------------------------------------------------------------------


class TestSequenceForgery:
    def test_negative_sequence_rejected_or_returned_negative(self) -> None:
        def handler(conn: socket.socket) -> None:
            _drain_request(conn)
            conn.sendall(b"SEQUENCE: -1\n")

        with _hostile_server(handler) as port:
            # int("-1") returns -1. The client returns it; downstream logic
            # decides what to do. We confirm parsing doesn't crash.
            result = _client(port=port).get_sequence("0xab" * 24)
            assert result == -1

    def test_hex_sequence_rejected(self) -> None:
        def handler(conn: socket.socket) -> None:
            _drain_request(conn)
            conn.sendall(b"SEQUENCE: 0x10\n")

        with _hostile_server(handler) as port:
            # int("0x10") raises ValueError. The client should propagate.
            with pytest.raises((TauNetRpcError, ValueError)):
                _client(port=port).get_sequence("0xab" * 24)

    def test_underscore_separated_sequence_accepted_by_int_constructor(self) -> None:
        def handler(conn: socket.socket) -> None:
            _drain_request(conn)
            conn.sendall(b"SEQUENCE: 1_000_000\n")

        # int("1_000_000") is 1000000 in Python. So this is accepted.
        # We just check it doesn't silently truncate.
        with _hostile_server(handler) as port:
            assert _client(port=port).get_sequence("0xab" * 24) == 1_000_000

    def test_float_sequence_rejected(self) -> None:
        def handler(conn: socket.socket) -> None:
            _drain_request(conn)
            conn.sendall(b"SEQUENCE: 1.5\n")

        with _hostile_server(handler) as port:
            with pytest.raises((TauNetRpcError, ValueError)):
                _client(port=port).get_sequence("0xab" * 24)

    def test_scientific_notation_rejected(self) -> None:
        def handler(conn: socket.socket) -> None:
            _drain_request(conn)
            conn.sendall(b"SEQUENCE: 1e9\n")

        with _hostile_server(handler) as port:
            with pytest.raises((TauNetRpcError, ValueError)):
                _client(port=port).get_sequence("0xab" * 24)

    def test_sequence_prefix_in_different_case_rejected(self) -> None:
        def handler(conn: socket.socket) -> None:
            _drain_request(conn)
            conn.sendall(b"sequence: 42\n")

        # The high-level method checks startswith("SEQUENCE:") — case sensitive.
        with _hostile_server(handler) as port:
            with pytest.raises(TauNetRpcError, match="unexpected getsequence"):
                _client(port=port).get_sequence("0xab" * 24)

    def test_sequence_label_smuggling_rejected(self) -> None:
        def handler(conn: socket.socket) -> None:
            _drain_request(conn)
            conn.sendall(b"FAKE_SEQUENCE: 42\n")

        with _hostile_server(handler) as port:
            with pytest.raises(TauNetRpcError, match="unexpected getsequence"):
                _client(port=port).get_sequence("0xab" * 24)


# -----------------------------------------------------------------------------
# D. Balance forgery (parallel to sequence).
# -----------------------------------------------------------------------------


class TestBalanceForgery:
    def test_balance_with_wrong_prefix_rejected(self) -> None:
        def handler(conn: socket.socket) -> None:
            _drain_request(conn)
            conn.sendall(b"SEQUENCE: 99999\n")  # wrong prefix

        with _hostile_server(handler) as port:
            with pytest.raises(TauNetRpcError, match="unexpected getbalance"):
                _client(port=port).get_balance("0xab" * 24)

    def test_balance_negative_returned_as_is(self) -> None:
        def handler(conn: socket.socket) -> None:
            _drain_request(conn)
            conn.sendall(b"BALANCE: -100000\n")

        with _hostile_server(handler) as port:
            assert _client(port=port).get_balance("0xab" * 24) == -100000

    def test_balance_huge_value_returned(self) -> None:
        def handler(conn: socket.socket) -> None:
            _drain_request(conn)
            conn.sendall(b"BALANCE: 99999999999999999999999\n")

        with _hostile_server(handler) as port:
            assert _client(port=port).get_balance("0xab" * 24) == 99999999999999999999999


# -----------------------------------------------------------------------------
# E. Huge padding before legitimate response.
# -----------------------------------------------------------------------------


class TestHugePadding:
    def test_megabyte_of_whitespace_then_success_rejected(self) -> None:
        """A server that sends 1MB of whitespace before SUCCESS would
        exceed the recv_max_bytes budget. We must fail closed."""

        def handler(conn: socket.socket) -> None:
            _drain_request(conn)
            # 100KB of spaces, then SUCCESS. With recv_max_bytes=10KB this
            # truncates without a newline.
            conn.sendall(b" " * 100_000 + b"SUCCESS\n")

        with _hostile_server(handler) as port:
            client = TauNetTcpClient(
                TauNetTcpConfig(
                    host="127.0.0.1", port=port, timeout_s=0.5, recv_max_bytes=10_000
                )
            )
            with pytest.raises(TauNetRpcError):
                client.rpc("ping")

    def test_small_padding_then_success_first_line_empty(self) -> None:
        """Server sends spaces then newline then SUCCESS. The first line
        is the padding (not empty unless padding is 0 bytes)."""

        def handler(conn: socket.socket) -> None:
            _drain_request(conn)
            conn.sendall(b"      \nSUCCESS\n")

        with _hostile_server(handler) as port:
            response = _client(port=port).rpc("ping")
            # First newline at index 6; first line is "      ".
            assert response == "      "
            # The success parser strips whitespace before checking → False.
            assert tau_rpc_response_is_success(response) is False


# -----------------------------------------------------------------------------
# F. Replay protection — second connection sees different response.
# -----------------------------------------------------------------------------


class TestReplayConfusion:
    def test_two_separate_connections_each_see_their_own_response(self) -> None:
        """A hostile server could try to replay the *previous* client's
        response to a new connection. The client opens a fresh socket each
        time, so this is structurally impossible — verify."""

        responses = [b"SUCCESS: tx_1\n", b"SUCCESS: tx_2\n"]

        listen_sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        listen_sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        listen_sock.bind(("127.0.0.1", 0))
        listen_sock.listen(2)
        port = listen_sock.getsockname()[1]
        idx = [0]

        def server_loop() -> None:
            for _ in range(2):
                conn, _ = listen_sock.accept()
                _drain_request(conn)
                conn.sendall(responses[idx[0]])
                idx[0] += 1
                conn.close()

        t = threading.Thread(target=server_loop, daemon=True)
        t.start()
        try:
            client = _client(port=port)
            r1 = client.rpc("ping")
            r2 = client.rpc("ping")
            assert r1 == "SUCCESS: tx_1"
            assert r2 == "SUCCESS: tx_2"
            assert r1 != r2
        finally:
            listen_sock.close()
            t.join(timeout=2.0)


# -----------------------------------------------------------------------------
# G. Slow attacker — drip a forgery byte-by-byte to exploit a partial-frame
#    timing assumption.
# -----------------------------------------------------------------------------


class TestDripForgery:
    def test_success_dripped_byte_by_byte_within_timeout(self) -> None:
        """If we drip SUCCESS\\n one byte at a time but faster than the
        client's per-recv timeout, the client should still get it."""
        import time

        def handler(conn: socket.socket) -> None:
            _drain_request(conn)
            for byte in b"SUCCESS\n":
                conn.sendall(bytes([byte]))
                time.sleep(0.02)

        with _hostile_server(handler) as port:
            client = _client(port=port, timeout_s=1.5)
            assert client.rpc("ping") == "SUCCESS"

    def test_partial_success_then_close_rejected(self) -> None:
        """Attacker sends 'SUCC' then closes — we must NOT report it as success."""

        def handler(conn: socket.socket) -> None:
            _drain_request(conn)
            conn.sendall(b"SUCC")
            # Close without newline.

        with _hostile_server(handler) as port:
            with pytest.raises(TauNetRpcError, match="closed before response terminator"):
                _client(port=port).rpc("ping")
