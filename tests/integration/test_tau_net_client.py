from __future__ import annotations

import socket

import pytest

import src.integration.tau_net_client as tau_net_client

pytest.importorskip("py_ecc.bls", reason="py_ecc not installed (install py-ecc to run Tau client signing tests)")


def test_tau_net_client_bls_requirement_and_privkey_parsing_edges(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(tau_net_client, "_BLS_AVAILABLE", False)
    with pytest.raises(tau_net_client.TauNetRpcError, match="py_ecc.bls is required"):
        tau_net_client.bls_pubkey_hex_from_privkey(1)
    assert tau_net_client.verify_tau_transaction_payload_signature({}) is False
    monkeypatch.setattr(tau_net_client, "_BLS_AVAILABLE", True)

    assert tau_net_client._parse_privkey_int(5) == 5
    with pytest.raises(ValueError, match="privkey must be positive"):
        tau_net_client._parse_privkey_int(0)
    monkeypatch.setattr(tau_net_client, "_BLS12_381_CURVE_ORDER", 10)
    with pytest.raises(ValueError, match="privkey out of range"):
        tau_net_client._parse_privkey_int(10)
    monkeypatch.setattr(tau_net_client, "_BLS12_381_CURVE_ORDER", None)

    assert tau_net_client._parse_privkey_bytes(b"\x00" * 31 + b"\x01") == 1
    assert tau_net_client._parse_privkey_to_int(b"\x00" * 31 + b"\x02") == 2
    with pytest.raises(ValueError, match="privkey bytes must be length 32"):
        tau_net_client._parse_privkey_bytes(b"\x01")

    assert tau_net_client._parse_privkey_str("0x" + "00" * 31 + "01") == 1
    assert tau_net_client._parse_privkey_str("00" * 31 + "01") == 1
    assert tau_net_client._parse_privkey_str("7") == 7
    assert tau_net_client._parse_privkey_to_int("8") == 8
    with pytest.raises(ValueError, match="privkey must be non-empty"):
        tau_net_client._parse_privkey_str(" ")
    with pytest.raises(ValueError, match="privkey hex must contain only 0-9a-f"):
        tau_net_client._parse_privkey_str("0xzz")
    with pytest.raises(ValueError, match="privkey hex must decode to 32 bytes"):
        tau_net_client._parse_privkey_str("0x01")
    with pytest.raises(ValueError, match="privkey must be 32-byte hex"):
        tau_net_client._parse_privkey_str("not-a-key")
    with pytest.raises(TypeError, match="privkey must be str\\|int\\|bytes"):
        tau_net_client._parse_privkey_to_int(object())  # type: ignore[arg-type]

    monkeypatch.setattr(tau_net_client, "_BLS_AVAILABLE", True)
    monkeypatch.setattr(tau_net_client, "G2Basic", None)
    with pytest.raises(tau_net_client.TauNetRpcError, match="py_ecc.bls is required"):
        tau_net_client.bls_pubkey_hex_from_privkey(1)
    assert tau_net_client.verify_tau_transaction_payload_signature({}) is False


def test_tau_net_client_signing_and_encoding_edges() -> None:
    payload = tau_net_client.build_signed_tau_transaction(
        privkey=1,
        sequence_number=2,
        expiration_time=3,
        operations={"0": {"mint": [1]}, "1": "reserved", "9": {"x": 1}, "8": 7},
        fee_limit=0,
    )
    assert payload["operations"]["0"] == {"mint": [1]}
    assert payload["operations"]["1"] == "reserved"
    assert payload["operations"]["8"] == 7
    assert payload["operations"]["9"] == "{\"x\":1}"
    assert tau_net_client.verify_tau_transaction_payload_signature(payload) is True

    with pytest.raises(ValueError, match="bool values are not allowed"):
        tau_net_client.encode_tau_operations_for_wire({"9": True})

    payload_from_numeric_text = tau_net_client.build_signed_tau_transaction(
        privkey=1,
        sequence_number="4",
        expiration_time=5.0,
        operations={"9": {"x": 1}},
        fee_limit=0,
    )
    assert payload_from_numeric_text["sequence_number"] == 4
    assert payload_from_numeric_text["expiration_time"] == 5

    with pytest.raises(ValueError, match="sequence_number must be a non-negative integer"):
        tau_net_client.build_signed_tau_transaction(
            privkey=1,
            sequence_number=True,
            expiration_time=3,
            operations={"9": {"x": 1}},
            fee_limit=0,
        )

    with pytest.raises(ValueError, match="expiration_time must be a non-negative integer"):
        tau_net_client.build_signed_tau_transaction(
            privkey=1,
            sequence_number=2,
            expiration_time=-1,
            operations={"9": {"x": 1}},
            fee_limit=0,
        )

    bad_sender = dict(payload)
    bad_sender["sender_pubkey"] = 9
    assert tau_net_client.verify_tau_transaction_payload_signature(bad_sender) is False

    bad_sig = dict(payload)
    bad_sig["signature"] = "zz"
    assert tau_net_client.verify_tau_transaction_payload_signature(bad_sig) is False


def test_tau_net_transaction_signing_rejects_noncanonical_json_values() -> None:
    with pytest.raises(TypeError, match="floats are not allowed"):
        tau_net_client.build_signed_tau_transaction(
            privkey=1,
            sequence_number=2,
            expiration_time=3,
            operations={"9": {"x": 1.5}},
            fee_limit=0,
        )


def test_sign_perp_op_for_engine_validates_inputs() -> None:
    op = {
        "module": "TauPerp",
        "version": "1.0",
        "market_id": "m1",
        "action": "init_market_2p",
        "quote_asset": "USD",
        "account_a_pubkey": tau_net_client.bls_pubkey_hex_from_privkey(11),
        "account_b_pubkey": tau_net_client.bls_pubkey_hex_from_privkey(12),
        "deadline": 99,
        "nonce_a": 1,
        "nonce_b": 2,
    }
    sig = tau_net_client.sign_perp_op_for_engine(
        op,
        privkey=11,
        chain_id="tau-local",
        signer_pubkey=tau_net_client.bls_pubkey_hex_from_privkey(11),
        nonce=1,
    )
    assert sig.startswith("0x")
    with pytest.raises(ValueError, match="signer_pubkey must be a non-empty string"):
        tau_net_client.sign_perp_op_for_engine(
            op,
            privkey=11,
            chain_id="tau-local",
            signer_pubkey="",
            nonce=1,
        )
    with pytest.raises(ValueError, match="nonce must be a positive int"):
        tau_net_client.sign_perp_op_for_engine(
            op,
            privkey=11,
            chain_id="tau-local",
            signer_pubkey=tau_net_client.bls_pubkey_hex_from_privkey(11),
            nonce=0,
        )


class _FakeSocket:
    def __init__(
        self,
        chunks: list[object],
        *,
        connect_error: Exception | None = None,
        send_error: Exception | None = None,
    ) -> None:
        self._chunks = list(chunks)
        self._connect_error = connect_error
        self._send_error = send_error
        self.timeout = None
        self.connected = None
        self.sent = []

    def __enter__(self) -> _FakeSocket:
        return self

    def __exit__(self, exc_type, exc, tb) -> bool:
        return False

    def settimeout(self, timeout: float) -> None:
        self.timeout = timeout

    def connect(self, addr: tuple[str, int]) -> None:
        if self._connect_error is not None:
            raise self._connect_error
        self.connected = addr

    def sendall(self, data: bytes) -> None:
        if self._send_error is not None:
            raise self._send_error
        self.sent.append(data)

    def recv(self, _size: int) -> bytes:
        if not self._chunks:
            return b""
        item = self._chunks.pop(0)
        if isinstance(item, Exception):
            raise item
        assert isinstance(item, bytes)
        return item


def test_tau_net_tcp_client_rpc_socket_paths(monkeypatch: pytest.MonkeyPatch) -> None:
    newline_sock = _FakeSocket([b"BALANCE: 7\nignored"])
    monkeypatch.setattr(tau_net_client.socket, "socket", lambda *args, **kwargs: newline_sock)
    client = tau_net_client.TauNetTcpClient()
    assert client.rpc("getbalance abc") == "BALANCE: 7"
    assert newline_sock.connected == ("127.0.0.1", 65432)
    assert newline_sock.sent[0].endswith(b"\r\n")

    raw_sock = _FakeSocket([b"RAW", b""])
    monkeypatch.setattr(tau_net_client.socket, "socket", lambda *args, **kwargs: raw_sock)
    with pytest.raises(tau_net_client.TauNetRpcError, match="closed before response terminator"):
        client.rpc("raw")

    blank_sock = _FakeSocket([b""])
    monkeypatch.setattr(tau_net_client.socket, "socket", lambda *args, **kwargs: blank_sock)
    with pytest.raises(tau_net_client.TauNetRpcError, match="closed without response"):
        client.rpc("ping\r\n")

    limited_sock = _FakeSocket([b"A"])
    monkeypatch.setattr(tau_net_client.socket, "socket", lambda *args, **kwargs: limited_sock)
    limited_client = tau_net_client.TauNetTcpClient(
        tau_net_client.TauNetTcpConfig(recv_max_bytes=1),
    )
    with pytest.raises(tau_net_client.TauNetRpcError, match="closed before response terminator"):
        limited_client.rpc("limited")

    connect_fail_sock = _FakeSocket([], connect_error=ConnectionRefusedError("refused"))
    monkeypatch.setattr(tau_net_client.socket, "socket", lambda *args, **kwargs: connect_fail_sock)
    with pytest.raises(tau_net_client.TauNetRpcError, match="rpc connection failed") as connect_err:
        client.rpc("sendtx private_payload")
    assert "sendtx private_payload" not in str(connect_err.value)

    send_fail_sock = _FakeSocket([], send_error=BrokenPipeError("broken"))
    monkeypatch.setattr(tau_net_client.socket, "socket", lambda *args, **kwargs: send_fail_sock)
    with pytest.raises(tau_net_client.TauNetRpcError, match="rpc connection failed") as send_err:
        client.rpc("sendtx private_payload")
    assert "sendtx private_payload" not in str(send_err.value)

    recv_reset_sock = _FakeSocket([ConnectionResetError("reset")])
    monkeypatch.setattr(tau_net_client.socket, "socket", lambda *args, **kwargs: recv_reset_sock)
    with pytest.raises(tau_net_client.TauNetRpcError, match="waiting for response") as recv_err:
        client.rpc("sendtx private_payload")
    assert "sendtx private_payload" not in str(recv_err.value)

    timeout_sock = _FakeSocket([b"PARTIAL_PRIVATE_RESPONSE", socket.timeout("slow")])
    monkeypatch.setattr(tau_net_client.socket, "socket", lambda *args, **kwargs: timeout_sock)
    with pytest.raises(tau_net_client.TauNetRpcError, match="rpc timed out") as timeout_err:
        client.rpc("sendtx private_payload")
    assert "sendtx private_payload" not in str(timeout_err.value)
    assert "PARTIAL_PRIVATE_RESPONSE" not in str(timeout_err.value)

    with pytest.raises(ValueError, match="cmd must be a non-empty string"):
        client.rpc(" ")


def test_tau_net_tcp_client_methods_and_send_signed_tx(monkeypatch: pytest.MonkeyPatch) -> None:
    with pytest.raises(ValueError, match="invalid port"):
        tau_net_client.TauNetTcpClient(tau_net_client.TauNetTcpConfig(port=70000))
    with pytest.raises(ValueError, match="timeout_s must be positive"):
        tau_net_client.TauNetTcpClient(tau_net_client.TauNetTcpConfig(timeout_s=0))
    with pytest.raises(ValueError, match="recv_max_bytes must be positive"):
        tau_net_client.TauNetTcpClient(tau_net_client.TauNetTcpConfig(recv_max_bytes=0))

    client = tau_net_client.TauNetTcpClient()
    calls: list[str] = []

    def _rpc(cmd: str) -> str:
        calls.append(cmd)
        if cmd.startswith("getsequence ok"):
            return "SEQUENCE: 9"
        if cmd.startswith("getsequence bad"):
            return "BAD"
        if cmd.startswith("getbalance ok"):
            return "BALANCE: 12"
        if cmd.startswith("getbalance bad"):
            return "BAD"
        return f"resp:{cmd}"

    monkeypatch.setattr(client, "rpc", _rpc)
    assert client.get_sequence("ok") == 9
    with pytest.raises(tau_net_client.TauNetRpcError, match="unexpected getsequence response"):
        client.get_sequence("bad")
    assert client.get_balance("ok") == 12
    with pytest.raises(tau_net_client.TauNetRpcError, match="unexpected getbalance response"):
        client.get_balance("bad")
    assert client.sendtx({"a": 1}) == 'resp:sendtx {"a":1}'
    assert client.createblock() == "resp:createblock"
    assert client.getappstate() == "resp:getappstate"
    assert client.getappstate(full=True) == "resp:getappstate full"
    assert client.getdexstate(full=True) == "resp:getappstate full"
    assert client.getstateproof() == "resp:getstateproof"
    assert client.getstateproof(full=True) == "resp:getstateproof full"

    sent_payloads: list[dict[str, object]] = []
    monkeypatch.setattr(client, "sendtx", lambda payload: sent_payloads.append(dict(payload)) or "submitted")
    monkeypatch.setattr(client, "get_sequence", lambda sender: 14)
    monkeypatch.setattr(tau_net_client.time, "time", lambda: 1000)
    assert client.send_signed_tx(privkey=1, operations={"9": {"ok": 1}}, fee_limit="2") == "submitted"
    assert sent_payloads[-1]["sequence_number"] == 14
    assert sent_payloads[-1]["expiration_time"] == 4600
    assert sent_payloads[-1]["fee_limit"] == "2"

    monkeypatch.setattr(client, "get_sequence", lambda sender: (_ for _ in ()).throw(AssertionError("should not be called")))
    assert client.send_signed_tx(
        privkey=1,
        operations={"9": {"ok": 1}},
        sequence_number=3,
        expiration_seconds=10,
    ) == "submitted"
    assert sent_payloads[-1]["sequence_number"] == 3

    for bad_sequence in (True, -1, 1.5):
        with pytest.raises(ValueError, match="sequence_number must be a non-negative integer"):
            client.send_signed_tx(
                privkey=1,
                operations={"9": {"ok": 1}},
                sequence_number=bad_sequence,  # type: ignore[arg-type]
                expiration_seconds=10,
            )

    for bad_expiration in (True, 0, -1, 1.5):
        with pytest.raises(ValueError, match="expiration_seconds must be"):
            client.send_signed_tx(
                privkey=1,
                operations={"9": {"ok": 1}},
                sequence_number=3,
                expiration_seconds=bad_expiration,  # type: ignore[arg-type]
            )
