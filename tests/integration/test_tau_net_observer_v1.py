from __future__ import annotations

import ast
import dataclasses
import inspect
import socket
from collections.abc import Callable, Sequence
from typing import cast
from unittest.mock import patch

import pytest

import src.integration.tau_net_observer_v1 as observer
from src.core.tau_net_observation_v1 import (
    TauMempoolStatusV1,
    TauObservationRejectCodeV1,
    TauObservationRejectV1,
    TauReadCommandV1,
    TauReadRequestV1,
    TauRemoteErrorObservationV1,
    TauTxConfirmedObservationV1,
    TauTxMempoolObservationV1,
    TauTxUnknownObservationV1,
)

_TX_HASH = "a" * 64
_BLOCK_HASH = "b" * 64
_HELLO = b"ok version=2 env=testnet node=tau-node\r\n"


class _FakeSocket:
    def __init__(
        self,
        chunks: Sequence[object],
        *,
        connect_error: BaseException | None = None,
        send_errors: list[BaseException | None] | None = None,
        settimeout_errors: list[BaseException | None] | None = None,
        receive_hook: Callable[[], None] | None = None,
    ) -> None:
        self._chunks = list(chunks)
        self._connect_error = connect_error
        self._send_errors = list(send_errors or [])
        self._settimeout_errors = list(settimeout_errors or [])
        self._receive_hook = receive_hook
        self.sent: list[bytes] = []
        self.timeouts: list[float] = []
        self.recv_sizes: list[int] = []
        self.connected: tuple[object, ...] | None = None
        self.closed = False

    def settimeout(self, timeout: float) -> None:
        self.timeouts.append(timeout)
        if self._settimeout_errors:
            error = self._settimeout_errors.pop(0)
            if error is not None:
                raise error

    def connect(self, endpoint: tuple[object, ...]) -> None:
        if self._connect_error is not None:
            raise self._connect_error
        self.connected = endpoint

    def sendall(self, frame: bytes) -> None:
        if self._send_errors:
            error = self._send_errors.pop(0)
            if error is not None:
                raise error
        self.sent.append(frame)

    def recv(self, maximum: int) -> object:
        self.recv_sizes.append(maximum)
        if self._receive_hook is not None:
            self._receive_hook()
        if not self._chunks:
            return b""
        next_chunk = self._chunks.pop(0)
        if isinstance(next_chunk, BaseException):
            raise next_chunk
        if type(next_chunk) is bytes:
            remainder = next_chunk[maximum:]
            if remainder:
                self._chunks.insert(0, remainder)
            return next_chunk[:maximum]
        return next_chunk

    def close(self) -> None:
        self.closed = True


class _Clock:
    def __init__(self) -> None:
        self.now = 0.0

    def __call__(self) -> float:
        return self.now

    def advance(self, seconds: float) -> None:
        self.now += seconds


def _request(command: TauReadCommandV1 = TauReadCommandV1.GET_TAU_STATE) -> TauReadRequestV1:
    if command is TauReadCommandV1.GET_TAU_STATE:
        return TauReadRequestV1(command)
    return TauReadRequestV1(command, _TX_HASH)


def _frame(payload: bytes) -> bytes:
    return payload + b"\r\n"


def _ok_rules() -> bytes:
    return b'{"status":"ok","command":"gettaustate","data":{"rules_state":"p."}}'


def _ok_tx(status: str) -> bytes:
    if status == "confirmed":
        return (
            b'{"status":"ok","command":"gettxstatus","data":{"tx_hash":"'
            + _TX_HASH.encode()
            + b'","status":"confirmed","block_hash":"'
            + _BLOCK_HASH.encode()
            + b'","block_number":7,"confirmations":1}}'
        )
    if status == "queued":
        return (
            b'{"status":"ok","command":"gettxstatus","data":{"tx_hash":"'
            + _TX_HASH.encode()
            + b'","status":"queued","sender":null,"sequence_number":null,'
            b'"received_at":"t0","fee_limit":0,"estimated_fee":0,"expires_at":"t1"}}'
        )
    return (
        b'{"status":"ok","command":"gettxstatus","data":{"tx_hash":"'
        + _TX_HASH.encode()
        + b'","status":"unknown"}}'
    )


def _observe_with(
    fake: _FakeSocket,
    request: TauReadRequestV1,
    config: observer.TauNetObserverConfigV1 | None = None,
) -> object:
    selected = config or observer.TauNetObserverConfigV1()
    with patch.object(observer.socket, "socket", return_value=fake) as factory:
        result = observer.observe_tau_net_v1(selected, request)
    assert factory.call_count == 1
    return result


def test_given_fragmented_handshake_and_response_when_observed_then_returns_owned_unauthenticated_data() -> (
    None
):
    fake = _FakeSocket([_HELLO[:9], _HELLO[9:], _frame(_ok_rules())[:17], _frame(_ok_rules())[17:]])

    result = _observe_with(fake, _request())

    assert isinstance(result, observer.TauNetObservedReadV1)
    assert result.hello.environment == "testnet"
    assert result.observation.body.rules_text == "p."
    assert result.authentication == "UNAUTHENTICATED"
    assert fake.sent == [b"hello version=2\r\n", b"gettaustate\r\n"]
    assert fake.closed is True
    with pytest.raises(dataclasses.FrozenInstanceError):
        result.config.port = 1  # type: ignore[misc]


def test_given_invalid_handshake_when_observed_then_does_not_send_read_command() -> None:
    fake = _FakeSocket([b"ok version=1 env=testnet node=tau-node\r\n"])

    result = _observe_with(fake, _request())

    assert result == TauObservationRejectV1(TauObservationRejectCodeV1.HANDSHAKE_MISMATCH)
    assert fake.sent == [b"hello version=2\r\n"]
    assert fake.closed is True


@pytest.mark.parametrize(
    ("read_request", "expected"),
    [
        (
            TauReadRequestV1(TauReadCommandV1.GET_ACCOUNT_STATE, "alice\r\ngetblocks"),
            TauObservationRejectCodeV1.INVALID_REQUEST,
        ),
        (
            TauReadRequestV1("getblocks", ""),
            TauObservationRejectCodeV1.UNSUPPORTED_COMMAND,
        ),
    ],
)
def test_given_disallowed_read_request_when_observed_then_rejects_before_socket(
    read_request: TauReadRequestV1, expected: TauObservationRejectCodeV1
) -> None:
    with patch.object(observer.socket, "socket") as factory:
        result = observer.observe_tau_net_v1(observer.TauNetObserverConfigV1(), read_request)

    assert result == TauObservationRejectV1(expected)
    factory.assert_not_called()


@pytest.mark.parametrize(
    "config",
    [
        observer.TauNetObserverConfigV1(host="localhost"),
        observer.TauNetObserverConfigV1(host="a" * 46),
        observer.TauNetObserverConfigV1(port=True),
        observer.TauNetObserverConfigV1(port=65_536),
        observer.TauNetObserverConfigV1(timeout_ms=0),
        observer.TauNetObserverConfigV1(
            max_response_bytes=observer.MAX_TAU_OBSERVATION_BYTES_V1 + 1
        ),
    ],
)
def test_given_invalid_config_when_observed_then_rejects_before_socket(
    config: observer.TauNetObserverConfigV1,
) -> None:
    with patch.object(observer.socket, "socket") as factory:
        result = observer.observe_tau_net_v1(config, _request())

    assert result == TauObservationRejectV1(TauObservationRejectCodeV1.INVALID_REQUEST)
    factory.assert_not_called()


def test_given_tiny_response_limit_when_observed_then_handshake_keeps_hello_ceiling() -> None:
    fake = _FakeSocket([_HELLO, b"x\r\n"])
    config = observer.TauNetObserverConfigV1(max_response_bytes=1)

    result = _observe_with(fake, _request(), config)

    assert result == TauObservationRejectV1(TauObservationRejectCodeV1.INVALID_RESPONSE)
    assert fake.sent == [b"hello version=2\r\n", b"gettaustate\r\n"]
    assert fake.recv_sizes == [observer.MAX_TAU_HELLO_BYTES_V1 + 2, 3]


def test_given_uninitialized_or_deleted_request_when_observed_then_rejects_before_socket() -> None:
    uninitialized = cast(TauReadRequestV1, object.__new__(TauReadRequestV1))
    deleted = _request()
    object.__delattr__(deleted, "argument")
    for malformed_request in (uninitialized, deleted):
        with patch.object(observer.socket, "socket") as factory:
            result = observer.observe_tau_net_v1(
                observer.TauNetObserverConfigV1(), malformed_request
            )

        assert result == TauObservationRejectV1(TauObservationRejectCodeV1.INVALID_REQUEST)
        factory.assert_not_called()


def test_given_truncated_or_surplus_frame_when_observed_then_fails_closed_and_closes() -> None:
    truncated = _FakeSocket([_HELLO, b'{"status":"ok"'])
    surplus = _FakeSocket([_HELLO + _frame(_ok_rules())])

    first = _observe_with(truncated, _request())
    second = _observe_with(surplus, _request())

    assert first == TauObservationRejectV1(TauObservationRejectCodeV1.INVALID_FRAME)
    assert second == TauObservationRejectV1(TauObservationRejectCodeV1.INVALID_FRAME)
    assert truncated.closed is True
    assert surplus.closed is True


@pytest.mark.parametrize(
    ("failure", "expected"),
    [
        (OSError("down"), TauObservationRejectCodeV1.UNAVAILABLE),
        (socket.timeout("slow"), TauObservationRejectCodeV1.TIMEOUT),
    ],
)
def test_given_connect_failure_when_observed_then_returns_typed_failure_and_closes(
    failure: BaseException, expected: TauObservationRejectCodeV1
) -> None:
    fake = _FakeSocket([], connect_error=failure)

    result = _observe_with(fake, _request())

    assert result == TauObservationRejectV1(expected)
    assert fake.sent == []
    assert fake.closed is True


@pytest.mark.parametrize(
    ("failure", "expected"),
    [
        (OSError("down"), TauObservationRejectCodeV1.UNAVAILABLE),
        (socket.timeout("slow"), TauObservationRejectCodeV1.TIMEOUT),
    ],
)
def test_given_socket_creation_failure_when_observed_then_returns_typed_failure(
    failure: BaseException, expected: TauObservationRejectCodeV1
) -> None:
    with patch.object(observer.socket, "socket", side_effect=failure) as factory:
        result = observer.observe_tau_net_v1(observer.TauNetObserverConfigV1(), _request())

    assert result == TauObservationRejectV1(expected)
    assert factory.call_count == 1


@pytest.mark.parametrize(
    ("failure", "expected"),
    [
        (OSError("down"), TauObservationRejectCodeV1.UNAVAILABLE),
        (socket.timeout("slow"), TauObservationRejectCodeV1.TIMEOUT),
    ],
)
def test_given_settimeout_failure_at_each_tcp_stage_when_observed_then_closes(
    failure: BaseException, expected: TauObservationRejectCodeV1
) -> None:
    expected_sent_counts = (0, 0, 1, 1, 2)
    for stage, expected_sent_count in enumerate(expected_sent_counts):
        chunks = [_HELLO] if stage >= 3 else []
        fake = _FakeSocket(
            chunks,
            settimeout_errors=[None] * stage + [failure],
        )

        result = _observe_with(fake, _request())

        assert result == TauObservationRejectV1(expected)
        assert len(fake.sent) == expected_sent_count
        assert len(fake.timeouts) == stage + 1
        assert fake.closed is True


@pytest.mark.parametrize(
    ("failure", "expected"),
    [
        (OSError("down"), TauObservationRejectCodeV1.UNAVAILABLE),
        (socket.timeout("slow"), TauObservationRejectCodeV1.TIMEOUT),
    ],
)
def test_given_send_or_receive_failure_at_each_stage_when_observed_then_closes(
    failure: BaseException, expected: TauObservationRejectCodeV1
) -> None:
    hello_send = _FakeSocket([], send_errors=[failure])
    hello_receive = _FakeSocket([failure])
    request_send = _FakeSocket([_HELLO], send_errors=[None, failure])
    response_receive = _FakeSocket([_HELLO, failure])

    for fake, expected_sent in (
        (hello_send, []),
        (hello_receive, [b"hello version=2\r\n"]),
        (request_send, [b"hello version=2\r\n"]),
        (response_receive, [b"hello version=2\r\n", b"gettaustate\r\n"]),
    ):
        result = _observe_with(fake, _request())

        assert result == TauObservationRejectV1(expected)
        assert fake.sent == expected_sent
        assert fake.closed is True


def test_given_frame_at_limit_and_overflow_when_read_then_enforces_exact_body_limit() -> None:
    clock = _Clock()
    exact = _FakeSocket([b"x" * 8 + b"\r\n"])
    overflow = _FakeSocket([b"x" * 9 + b"\r\n"])
    with patch.object(observer.time, "monotonic", clock):
        assert observer._read_crlf_frame_v1(cast(socket.socket, exact), 1.0, 8) == b"x" * 8
        assert observer._read_crlf_frame_v1(
            cast(socket.socket, overflow), 1.0, 8
        ) == TauObservationRejectV1(TauObservationRejectCodeV1.RESOURCE_LIMIT)
    assert exact.recv_sizes == [10]
    assert overflow.recv_sizes == [10]


def test_given_each_nonempty_chunking_of_one_frame_when_read_then_body_is_invariant() -> None:
    payload = b"chunk-safe"
    frame = _frame(payload)
    clock = _Clock()
    with patch.object(observer.time, "monotonic", clock):
        for split in range(1, len(frame)):
            fake = _FakeSocket([frame[:split], frame[split:]])
            assert (
                observer._read_crlf_frame_v1(cast(socket.socket, fake), 1.0, len(payload))
                == payload
            )
        bytewise = _FakeSocket([frame[index : index + 1] for index in range(len(frame))])
        assert (
            observer._read_crlf_frame_v1(cast(socket.socket, bytewise), 1.0, len(payload))
            == payload
        )


def test_given_bare_lf_split_across_chunks_when_read_then_frame_rejects() -> None:
    fake = _FakeSocket([b"abc", b"\n"])

    with patch.object(observer.time, "monotonic", _Clock()):
        result = observer._read_crlf_frame_v1(cast(socket.socket, fake), 1.0, 3)

    assert result == TauObservationRejectV1(TauObservationRejectCodeV1.INVALID_FRAME)


@pytest.mark.parametrize(
    "chunks",
    [
        [b"{\n}\r\n"],
        [b"\nbody\r\n"],
        [b"frame1\nframe2\r\n"],
    ],
)
def test_given_earlier_or_leading_lf_when_read_then_frame_rejects(chunks: list[bytes]) -> None:
    fake = _FakeSocket(chunks)

    with patch.object(observer.time, "monotonic", _Clock()):
        result = observer._read_crlf_frame_v1(cast(socket.socket, fake), 1.0, 64)

    assert result == TauObservationRejectV1(TauObservationRejectCodeV1.INVALID_FRAME)


def test_given_crlf_split_between_chunks_when_read_then_frame_accepts() -> None:
    fake = _FakeSocket([b"safe\r", b"\n"])

    with patch.object(observer.time, "monotonic", _Clock()):
        result = observer._read_crlf_frame_v1(cast(socket.socket, fake), 1.0, 4)

    assert result == b"safe"


def test_given_wrong_response_echo_when_observed_then_core_subject_check_rejects() -> None:
    wrong_echo = b'{"status":"ok","command":"getaccountstate","data":{}}'
    fake = _FakeSocket([_HELLO, _frame(wrong_echo)])

    result = _observe_with(fake, _request())

    assert result == TauObservationRejectV1(TauObservationRejectCodeV1.SUBJECT_MISMATCH)
    assert fake.closed is True


def test_given_request_mutation_during_io_when_observed_then_response_keeps_sent_subject() -> None:
    request = _request(TauReadCommandV1.GET_TX_STATUS)
    altered = "c" * 64
    did_mutate = False

    def mutate_once() -> None:
        nonlocal did_mutate
        if not did_mutate:
            object.__setattr__(request, "argument", altered)
            did_mutate = True

    fake = _FakeSocket([_HELLO, _frame(_ok_tx("unknown"))], receive_hook=mutate_once)

    result = _observe_with(fake, request)

    assert isinstance(result, observer.TauNetObservedReadV1)
    assert result.observation.request.argument == _TX_HASH
    assert fake.sent[-1] == f"gettxstatus {_TX_HASH}\r\n".encode("ascii")


def test_given_slow_fragment_drip_when_observed_then_one_deadline_expires_without_command() -> None:
    clock = _Clock()
    fake = _FakeSocket([_HELLO[:8], _HELLO[8:]], receive_hook=lambda: clock.advance(0.6))
    config = observer.TauNetObserverConfigV1(timeout_ms=1_000)
    with patch.object(observer.time, "monotonic", clock):
        result = _observe_with(fake, _request(), config)

    assert result == TauObservationRejectV1(TauObservationRejectCodeV1.TIMEOUT)
    assert fake.sent == [b"hello version=2\r\n"]
    assert fake.timeouts == sorted(fake.timeouts, reverse=True)
    assert fake.closed is True


def test_given_handshake_decode_exhausts_deadline_when_observed_then_does_not_send_read() -> None:
    clock = _Clock()
    fake = _FakeSocket([_HELLO])
    original_decode = observer.decode_tau_hello_v1

    def decode_then_elapse(raw: object) -> object:
        decoded = original_decode(raw)
        clock.advance(1.0)
        return decoded

    with patch.object(observer.time, "monotonic", clock):
        with patch.object(observer, "decode_tau_hello_v1", side_effect=decode_then_elapse):
            result = _observe_with(
                fake,
                _request(),
                observer.TauNetObserverConfigV1(timeout_ms=1_000),
            )

    assert result == TauObservationRejectV1(TauObservationRejectCodeV1.TIMEOUT)
    assert fake.sent == [b"hello version=2\r\n"]
    assert fake.closed is True


def test_given_response_decode_exhausts_deadline_when_observed_then_returns_timeout() -> None:
    clock = _Clock()
    fake = _FakeSocket([_HELLO, _frame(_ok_rules())])
    original_decode = observer.decode_tau_read_response_v1

    def decode_then_elapse(request: object, raw: object) -> object:
        decoded = original_decode(request, raw)
        clock.advance(1.0)
        return decoded

    with patch.object(observer.time, "monotonic", clock):
        with patch.object(observer, "decode_tau_read_response_v1", side_effect=decode_then_elapse):
            result = _observe_with(
                fake,
                _request(),
                observer.TauNetObserverConfigV1(timeout_ms=1_000),
            )

    assert result == TauObservationRejectV1(TauObservationRejectCodeV1.TIMEOUT)
    assert fake.closed is True


def test_given_response_loss_then_explicit_second_call_uses_fresh_socket_without_automatic_retry() -> (
    None
):
    first = _FakeSocket([_HELLO, b""])
    second = _FakeSocket([_HELLO, _frame(_ok_rules())])
    sockets = [first, second]
    with patch.object(observer.socket, "socket", side_effect=sockets) as factory:
        lost = observer.observe_tau_net_v1(observer.TauNetObserverConfigV1(), _request())
        recovered = observer.observe_tau_net_v1(observer.TauNetObserverConfigV1(), _request())

    assert lost == TauObservationRejectV1(TauObservationRejectCodeV1.INVALID_FRAME)
    assert isinstance(recovered, observer.TauNetObservedReadV1)
    assert factory.call_count == 2
    assert first.sent == [b"hello version=2\r\n", b"gettaustate\r\n"]
    assert second.sent == [b"hello version=2\r\n", b"gettaustate\r\n"]
    assert first.closed is True
    assert second.closed is True


def test_given_remote_error_and_status_reorg_history_when_observed_then_preserves_observations_without_finality() -> (
    None
):
    remote_error = (
        b'{"status":"error","command":"gettaustate","error":'
        b'{"code":"unavailable","message":"temporary"}}'
    )
    remote = _observe_with(_FakeSocket([_HELLO, _frame(remote_error)]), _request())
    assert isinstance(remote, observer.TauNetObservedReadV1)
    assert isinstance(remote.observation.body, TauRemoteErrorObservationV1)

    bodies = []
    for status in ("confirmed", "queued", "unknown"):
        result = _observe_with(
            _FakeSocket([_HELLO, _frame(_ok_tx(status))]),
            _request(TauReadCommandV1.GET_TX_STATUS),
        )
        assert isinstance(result, observer.TauNetObservedReadV1)
        bodies.append(result.observation.body)
    assert isinstance(bodies[0], TauTxConfirmedObservationV1)
    assert isinstance(bodies[1], TauTxMempoolObservationV1)
    assert bodies[1].status is TauMempoolStatusV1.QUEUED
    assert isinstance(bodies[2], TauTxUnknownObservationV1)


def test_observer_has_no_signing_store_or_writer_dependency() -> None:
    tree = ast.parse(inspect.getsource(observer))
    imported = {
        alias.name
        for node in ast.walk(tree)
        if isinstance(node, ast.Import)
        for alias in node.names
    }
    imported.update(
        node.module or "" for node in ast.walk(tree) if isinstance(node, ast.ImportFrom)
    )
    forbidden = ("sign", "store", "writer", "sendtx", "tau_net_client")
    assert not any(fragment in name.lower() for name in imported for fragment in forbidden)
