"""Bounded TCP acquisition for unauthenticated Tau read observations."""

from __future__ import annotations

import ipaddress
import socket
import time
from dataclasses import dataclass
from typing import Final, Literal

from ..core.tau_net_observation_v1 import (
    MAX_TAU_HELLO_BYTES_V1,
    MAX_TAU_OBSERVATION_BYTES_V1,
    TauHelloObservationV1,
    TauObservationRejectCodeV1,
    TauObservationRejectV1,
    TauReadObservationV1,
    TauReadRequestV1,
    canonicalize_tau_read_request_v1,
    decode_tau_hello_v1,
    decode_tau_read_response_v1,
    encode_tau_read_request_v1,
)

MAX_TAU_OBSERVER_FRAGMENTS_V1: Final = 1_024
_HELLO_FRAME_V1: Final = b"hello version=2\r\n"
_CRLF: Final = b"\r\n"
_RECV_BYTES_V1: Final = 65_536


@dataclass(frozen=True, slots=True)
class TauNetObserverConfigV1:
    host: str = "127.0.0.1"
    port: int = 65_432
    timeout_ms: int = 3_000
    max_response_bytes: int = MAX_TAU_OBSERVATION_BYTES_V1


@dataclass(frozen=True, slots=True)
class TauNetObservedReadV1:
    """Unauthenticated, advisory transport provenance with no finality or authority."""

    config: TauNetObserverConfigV1
    hello: TauHelloObservationV1
    observation: TauReadObservationV1

    @property
    def authentication(self) -> Literal["UNAUTHENTICATED"]:
        """This TCP exchange supplies no authentication or settlement witness."""

        return "UNAUTHENTICATED"


def _reject(code: TauObservationRejectCodeV1) -> TauObservationRejectV1:
    return TauObservationRejectV1(code)


def _validated_config_v1(
    config: object,
) -> tuple[TauNetObserverConfigV1, int, tuple[object, ...], float, int] | TauObservationRejectV1:
    if type(config) is not TauNetObserverConfigV1:
        return _reject(TauObservationRejectCodeV1.INVALID_REQUEST)
    try:
        host, port, timeout_ms, maximum = (
            config.host,
            config.port,
            config.timeout_ms,
            config.max_response_bytes,
        )
    except AttributeError:
        return _reject(TauObservationRejectCodeV1.INVALID_REQUEST)
    if type(host) is not str or not 1 <= len(host) <= 45 or "%" in host:
        return _reject(TauObservationRejectCodeV1.INVALID_REQUEST)
    if type(port) is not int or not 1 <= port <= 65_535:
        return _reject(TauObservationRejectCodeV1.INVALID_REQUEST)
    if type(timeout_ms) is not int or not 1 <= timeout_ms <= 60_000:
        return _reject(TauObservationRejectCodeV1.INVALID_REQUEST)
    if type(maximum) is not int or not 1 <= maximum <= MAX_TAU_OBSERVATION_BYTES_V1:
        return _reject(TauObservationRejectCodeV1.INVALID_REQUEST)
    try:
        address = ipaddress.ip_address(host)
    except ValueError:
        return _reject(TauObservationRejectCodeV1.INVALID_REQUEST)
    owned = TauNetObserverConfigV1(host, port, timeout_ms, maximum)
    if address.version == 4:
        return owned, socket.AF_INET, (host, port), timeout_ms / 1_000.0, maximum
    return owned, socket.AF_INET6, (host, port, 0, 0), timeout_ms / 1_000.0, maximum


def _set_remaining_timeout_v1(
    sock: socket.socket, deadline: float
) -> TauObservationRejectV1 | None:
    remaining = deadline - time.monotonic()
    if remaining <= 0:
        return _reject(TauObservationRejectCodeV1.TIMEOUT)
    try:
        sock.settimeout(remaining)
    except TimeoutError:
        return _reject(TauObservationRejectCodeV1.TIMEOUT)
    except OSError:
        return _reject(TauObservationRejectCodeV1.UNAVAILABLE)
    return None


def _send_frame_v1(
    sock: socket.socket, frame: bytes, deadline: float
) -> TauObservationRejectV1 | None:
    failure = _set_remaining_timeout_v1(sock, deadline)
    if failure is not None:
        return failure
    try:
        sock.sendall(frame)
    except TimeoutError:
        return _reject(TauObservationRejectCodeV1.TIMEOUT)
    except OSError:
        return _reject(TauObservationRejectCodeV1.UNAVAILABLE)
    return None


def _read_crlf_frame_v1(
    sock: socket.socket, deadline: float, maximum: int
) -> bytes | TauObservationRejectV1:
    buffer = bytearray()
    fragments = 0
    while True:
        remaining_bytes = maximum + len(_CRLF) - len(buffer)
        if remaining_bytes <= 0:
            return _reject(TauObservationRejectCodeV1.RESOURCE_LIMIT)
        failure = _set_remaining_timeout_v1(sock, deadline)
        if failure is not None:
            return failure
        try:
            chunk = sock.recv(min(_RECV_BYTES_V1, remaining_bytes))
        except TimeoutError:
            return _reject(TauObservationRejectCodeV1.TIMEOUT)
        except OSError:
            return _reject(TauObservationRejectCodeV1.UNAVAILABLE)
        if time.monotonic() >= deadline:
            return _reject(TauObservationRejectCodeV1.TIMEOUT)
        if type(chunk) is not bytes or not chunk:
            return _reject(TauObservationRejectCodeV1.INVALID_FRAME)
        fragments += 1
        if fragments > MAX_TAU_OBSERVER_FRAGMENTS_V1:
            return _reject(TauObservationRejectCodeV1.RESOURCE_LIMIT)
        previous_length = len(buffer)
        buffer.extend(chunk)
        scan_start = max(0, previous_length - 1)
        first_lf = buffer.find(b"\n", scan_start)
        if first_lf >= 0:
            if first_lf != len(buffer) - 1 or first_lf == 0 or buffer[first_lf - 1] != 0x0D:
                return _reject(TauObservationRejectCodeV1.INVALID_FRAME)
            if first_lf - 1 > maximum:
                return _reject(TauObservationRejectCodeV1.RESOURCE_LIMIT)
            return bytes(buffer[: first_lf - 1])
        if len(buffer) > maximum + 1:
            return _reject(TauObservationRejectCodeV1.RESOURCE_LIMIT)


def _validated_request_frame_v1(
    request: object,
) -> tuple[TauReadRequestV1, bytes] | TauObservationRejectV1:
    snapshot = canonicalize_tau_read_request_v1(request)
    if isinstance(snapshot, TauObservationRejectV1):
        return snapshot
    encoded = encode_tau_read_request_v1(snapshot)
    if isinstance(encoded, TauObservationRejectV1):
        return encoded
    if type(encoded) is not bytes or not encoded or b"\r" in encoded or b"\n" in encoded:
        return _reject(TauObservationRejectCodeV1.INVALID_REQUEST)
    return snapshot, encoded


def observe_tau_net_v1(
    config: object, request: object
) -> TauNetObservedReadV1 | TauObservationRejectV1:
    """Fetch one read-only Tau observation through a fresh, bounded TCP exchange."""

    checked_config = _validated_config_v1(config)
    if isinstance(checked_config, TauObservationRejectV1):
        return checked_config
    checked_request = _validated_request_frame_v1(request)
    if isinstance(checked_request, TauObservationRejectV1):
        return checked_request
    owned_config, family, endpoint, timeout_s, maximum = checked_config
    sent_request, request_frame = checked_request
    deadline = time.monotonic() + timeout_s
    sock: socket.socket | None = None
    try:
        try:
            sock = socket.socket(family, socket.SOCK_STREAM)
        except TimeoutError:
            return _reject(TauObservationRejectCodeV1.TIMEOUT)
        except OSError:
            return _reject(TauObservationRejectCodeV1.UNAVAILABLE)
        failure = _set_remaining_timeout_v1(sock, deadline)
        if failure is not None:
            return failure
        try:
            sock.connect(endpoint)
        except TimeoutError:
            return _reject(TauObservationRejectCodeV1.TIMEOUT)
        except OSError:
            return _reject(TauObservationRejectCodeV1.UNAVAILABLE)
        failure = _send_frame_v1(sock, _HELLO_FRAME_V1, deadline)
        if failure is not None:
            return failure
        hello_raw = _read_crlf_frame_v1(sock, deadline, MAX_TAU_HELLO_BYTES_V1)
        if isinstance(hello_raw, TauObservationRejectV1):
            return hello_raw
        hello = decode_tau_hello_v1(hello_raw)
        if isinstance(hello, TauObservationRejectV1):
            return hello
        if time.monotonic() >= deadline:
            return _reject(TauObservationRejectCodeV1.TIMEOUT)
        failure = _send_frame_v1(sock, request_frame + _CRLF, deadline)
        if failure is not None:
            return failure
        response_raw = _read_crlf_frame_v1(sock, deadline, maximum)
        if isinstance(response_raw, TauObservationRejectV1):
            return response_raw
        observation = decode_tau_read_response_v1(sent_request, response_raw)
        if isinstance(observation, TauObservationRejectV1):
            return observation
        if time.monotonic() >= deadline:
            return _reject(TauObservationRejectCodeV1.TIMEOUT)
        return TauNetObservedReadV1(owned_config, hello, observation)
    finally:
        if sock is not None:
            try:
                sock.close()
            except OSError:
                pass
