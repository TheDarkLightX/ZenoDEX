"""Hash-bound peer discovery registries for ZenoLedger public networks."""

from __future__ import annotations

from typing import Any, Mapping, Sequence
from urllib.parse import urlsplit

from src.integration.zeno_ledger_v0 import hash_v0
from src.state.canonical import canonical_hex_fixed_allow_0x


PEER_REGISTRY_SCHEMA_V0 = "zenodex/zeno_ledger/peer_registry/v0"
PEER_REGISTRY_ADMISSION_SCHEMA_V0 = "zenodex/zeno_ledger/peer_registry_admission/v0"
PEER_TRANSPORT_V0 = "http_json_v0"


def _require_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be a JSON object")
    return value


def _require_sequence(value: object, *, name: str) -> Sequence[object]:
    if not isinstance(value, Sequence) or isinstance(value, (str, bytes, bytearray)):
        raise TypeError(f"{name} must be a sequence")
    return value


def _require_str(value: object, *, name: str, allow_empty: bool = False) -> str:
    if not isinstance(value, str) or (value == "" and not allow_empty):
        requirement = "a str" if allow_empty else "a non-empty str"
        raise ValueError(f"{name} must be {requirement}")
    return value


def _require_root(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    canonical = canonical_hex_fixed_allow_0x(value, nbytes=32, name=name)
    if value != canonical:
        raise ValueError(f"{name} must be canonical lowercase 0x-prefixed hex")
    return canonical


def _canonical_peer_url(value: object, *, name: str) -> str:
    url = _require_str(value, name=name).strip()
    if url != value:
        raise ValueError(f"{name} must not contain surrounding whitespace")
    parsed = urlsplit(url)
    if parsed.scheme not in {"http", "https"}:
        raise ValueError(f"{name} must use http or https")
    if parsed.netloc == "":
        raise ValueError(f"{name} must include a network location")
    if parsed.username is not None or parsed.password is not None:
        raise ValueError(f"{name} must not contain userinfo")
    if parsed.fragment != "":
        raise ValueError(f"{name} must not contain a fragment")
    return url.rstrip("/")


def _unique_urls(urls: Sequence[object], *, name: str) -> list[str]:
    out: list[str] = []
    seen: set[str] = set()
    for index, raw in enumerate(_require_sequence(urls, name=name)):
        url = _canonical_peer_url(raw, name=f"{name}[{index}]")
        if url in seen:
            continue
        seen.add(url)
        out.append(url)
    return out


def _peer_entry(url: str, *, role: str) -> dict[str, Any]:
    if role not in {"writer", "peer"}:
        raise ValueError("peer role must be writer or peer")
    body = {
        "peer_id": hash_v0("zeno_ledger_peer_id_v0", {"url": url}),
        "url": url,
        "role": role,
        "transport": PEER_TRANSPORT_V0,
        "status": "active",
    }
    return {**body, "peer_entry_hash": hash_v0("zeno_ledger_peer_entry_v0", body)}


def _peer_registry_hash_v0(registry: Mapping[str, Any]) -> str:
    body = {key: value for key, value in dict(registry).items() if key != "peer_registry_hash"}
    return hash_v0("zeno_ledger_peer_registry_v0", body)


def build_peer_registry_v0(
    *,
    network_id: str,
    chain_id: str,
    writer_urls: Sequence[object],
    peer_urls: Sequence[object],
) -> dict[str, Any]:
    """Build a canonical peer registry from public writer and peer URLs."""

    writers = _unique_urls(writer_urls, name="writer_urls")
    peers = _unique_urls(peer_urls, name="peer_urls")
    if not writers:
        raise ValueError("peer registry requires at least one writer URL")
    role_by_url: dict[str, str] = {url: "peer" for url in peers}
    for url in writers:
        role_by_url[url] = "writer"
    entries = [_peer_entry(url, role=role) for url, role in sorted(role_by_url.items())]
    writer_count = sum(1 for entry in entries if entry["role"] == "writer")
    body = {
        "schema": PEER_REGISTRY_SCHEMA_V0,
        "network_id": _require_str(network_id, name="network_id"),
        "chain_id": _require_str(chain_id, name="chain_id", allow_empty=True),
        "transport": PEER_TRANSPORT_V0,
        "writer_count": writer_count,
        "peer_count": len(entries),
        "peers": entries,
    }
    return {**body, "peer_registry_hash": _peer_registry_hash_v0(body)}


def validate_peer_registry_v0(registry: Mapping[str, Any]) -> None:
    obj = _require_mapping(registry, name="peer_registry")
    if obj.get("schema") != PEER_REGISTRY_SCHEMA_V0:
        raise ValueError("peer registry schema mismatch")
    if obj.get("transport") != PEER_TRANSPORT_V0:
        raise ValueError("peer registry transport mismatch")
    entries = [
        _require_mapping(item, name=f"peer_registry.peers[{index}]")
        for index, item in enumerate(_require_sequence(obj.get("peers"), name="peer_registry.peers"))
    ]
    writer_urls: list[str] = []
    peer_urls: list[str] = []
    seen_ids: set[str] = set()
    for index, entry in enumerate(entries):
        peer_id = _require_root(entry.get("peer_id"), name=f"peer_registry.peers[{index}].peer_id")
        if peer_id in seen_ids:
            raise ValueError("duplicate peer_id")
        seen_ids.add(peer_id)
        url = _canonical_peer_url(entry.get("url"), name=f"peer_registry.peers[{index}].url")
        role = _require_str(entry.get("role"), name=f"peer_registry.peers[{index}].role")
        if entry.get("transport") != PEER_TRANSPORT_V0:
            raise ValueError("peer entry transport mismatch")
        if entry.get("status") != "active":
            raise ValueError("peer entry status mismatch")
        expected_entry = _peer_entry(url, role=role)
        if dict(entry) != expected_entry:
            raise ValueError("peer entry binding mismatch")
        peer_urls.append(url)
        if role == "writer":
            writer_urls.append(url)
        elif role != "peer":
            raise ValueError("peer role must be writer or peer")
    expected = build_peer_registry_v0(
        network_id=_require_str(obj.get("network_id"), name="peer_registry.network_id"),
        chain_id=_require_str(obj.get("chain_id"), name="peer_registry.chain_id", allow_empty=True),
        writer_urls=writer_urls,
        peer_urls=peer_urls,
    )
    if dict(obj) != expected:
        raise ValueError("peer registry binding mismatch")


def build_peer_registry_admission_v0(
    *,
    network_id: str,
    chain_id: str,
    writer_urls: Sequence[object],
    peer_urls: Sequence[object],
    peer_registry: Mapping[str, Any],
) -> dict[str, Any]:
    """Admit a peer registry only when it is exactly derived from config URLs."""

    registry = dict(_require_mapping(peer_registry, name="peer_registry"))
    validate_peer_registry_v0(registry)
    expected_registry = build_peer_registry_v0(
        network_id=network_id,
        chain_id=chain_id,
        writer_urls=writer_urls,
        peer_urls=peer_urls,
    )
    if registry != expected_registry:
        raise ValueError("peer registry does not match configured URLs")
    body = {
        "schema": PEER_REGISTRY_ADMISSION_SCHEMA_V0,
        "ok": True,
        "status": "accepted",
        "network_id": _require_str(network_id, name="network_id"),
        "chain_id": _require_str(chain_id, name="chain_id", allow_empty=True),
        "peer_registry_hash": registry["peer_registry_hash"],
        "writer_count": registry["writer_count"],
        "peer_count": registry["peer_count"],
    }
    return {**body, "admission_hash": hash_v0("zeno_ledger_peer_registry_admission_v0", body)}


def validate_peer_registry_admission_v0(
    *,
    admission: Mapping[str, Any],
    network_id: str,
    chain_id: str,
    writer_urls: Sequence[object],
    peer_urls: Sequence[object],
    peer_registry: Mapping[str, Any],
) -> None:
    obj = _require_mapping(admission, name="peer_registry_admission")
    if obj.get("schema") != PEER_REGISTRY_ADMISSION_SCHEMA_V0:
        raise ValueError("peer registry admission schema mismatch")
    expected = build_peer_registry_admission_v0(
        network_id=network_id,
        chain_id=chain_id,
        writer_urls=writer_urls,
        peer_urls=peer_urls,
        peer_registry=peer_registry,
    )
    if dict(obj) != expected:
        raise ValueError("peer registry admission binding mismatch")
