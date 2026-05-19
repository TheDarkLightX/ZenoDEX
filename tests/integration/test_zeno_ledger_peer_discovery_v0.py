from __future__ import annotations

import pytest

from src.integration.zeno_ledger_peer_discovery_v0 import (
    build_peer_registry_admission_v0,
    build_peer_registry_v0,
    validate_peer_registry_admission_v0,
    validate_peer_registry_v0,
)


def test_peer_registry_is_canonical_and_hash_bound() -> None:
    registry = build_peer_registry_v0(
        network_id="zeno-ledger-peer-discovery-testnet-0",
        chain_id="zeno-ledger-peer-discovery-testnet-0",
        writer_urls=["http://127.0.0.1:8800"],
        peer_urls=["http://127.0.0.1:8800", "http://127.0.0.1:8801/"],
    )

    assert registry["writer_count"] == 1
    assert registry["peer_count"] == 2
    assert [peer["url"] for peer in registry["peers"]] == [
        "http://127.0.0.1:8800",
        "http://127.0.0.1:8801",
    ]
    assert registry["peers"][0]["role"] == "writer"
    assert registry["peers"][1]["role"] == "peer"
    validate_peer_registry_v0(registry)


def test_peer_registry_rejects_unsafe_urls() -> None:
    with pytest.raises(ValueError, match="http or https"):
        build_peer_registry_v0(
            network_id="zeno-ledger-peer-discovery-testnet-0",
            chain_id="zeno-ledger-peer-discovery-testnet-0",
            writer_urls=["file:///tmp/node"],
            peer_urls=[],
        )

    with pytest.raises(ValueError, match="userinfo"):
        build_peer_registry_v0(
            network_id="zeno-ledger-peer-discovery-testnet-0",
            chain_id="zeno-ledger-peer-discovery-testnet-0",
            writer_urls=["https://user@example.com/node"],
            peer_urls=[],
        )


def test_peer_registry_admission_requires_config_url_match() -> None:
    registry = build_peer_registry_v0(
        network_id="zeno-ledger-peer-discovery-testnet-0",
        chain_id="zeno-ledger-peer-discovery-testnet-0",
        writer_urls=["http://127.0.0.1:8800"],
        peer_urls=["http://127.0.0.1:8801"],
    )
    admission = build_peer_registry_admission_v0(
        network_id="zeno-ledger-peer-discovery-testnet-0",
        chain_id="zeno-ledger-peer-discovery-testnet-0",
        writer_urls=["http://127.0.0.1:8800"],
        peer_urls=["http://127.0.0.1:8801"],
        peer_registry=registry,
    )

    validate_peer_registry_admission_v0(
        admission=admission,
        network_id="zeno-ledger-peer-discovery-testnet-0",
        chain_id="zeno-ledger-peer-discovery-testnet-0",
        writer_urls=["http://127.0.0.1:8800"],
        peer_urls=["http://127.0.0.1:8801"],
        peer_registry=registry,
    )
    with pytest.raises(ValueError, match="configured URLs"):
        build_peer_registry_admission_v0(
            network_id="zeno-ledger-peer-discovery-testnet-0",
            chain_id="zeno-ledger-peer-discovery-testnet-0",
            writer_urls=["http://127.0.0.1:8800"],
            peer_urls=["http://127.0.0.1:9999"],
            peer_registry=registry,
        )


def test_peer_registry_admission_rejects_tampered_registry_hash() -> None:
    registry = build_peer_registry_v0(
        network_id="zeno-ledger-peer-discovery-testnet-0",
        chain_id="zeno-ledger-peer-discovery-testnet-0",
        writer_urls=["http://127.0.0.1:8800"],
        peer_urls=[],
    )
    tampered = dict(registry)
    tampered["peer_registry_hash"] = "0x" + "11" * 32

    with pytest.raises(ValueError, match="binding mismatch"):
        validate_peer_registry_v0(tampered)
