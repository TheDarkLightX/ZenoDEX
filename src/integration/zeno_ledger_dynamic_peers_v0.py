"""Bounded dynamic peer exchange admission for ZenoLedger public nodes."""

from __future__ import annotations

from typing import Any, Mapping, Sequence
from urllib.parse import urlsplit

from src.integration.zeno_ledger_v0 import hash_v0


DYNAMIC_PEER_CANDIDATE_SCHEMA_V0 = "zenodex/zeno_ledger/dynamic_peer_candidate/v0"
DYNAMIC_PEER_ADMISSION_SCHEMA_V0 = "zenodex/zeno_ledger/dynamic_peer_admission/v0"
DEFAULT_DYNAMIC_PEER_TTL_SECONDS = 300


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


def _require_nonnegative_int(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise ValueError(f"{name} must be a nonnegative integer")
    return value


def _require_positive_int(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value <= 0:
        raise ValueError(f"{name} must be a positive integer")
    return value


def canonical_peer_url_v0(value: object, *, name: str) -> str:
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


def canonical_peer_urls_v0(values: Sequence[object], *, name: str) -> list[str]:
    out: list[str] = []
    seen: set[str] = set()
    for index, raw in enumerate(_require_sequence(values, name=name)):
        url = canonical_peer_url_v0(raw, name=f"{name}[{index}]")
        if url in seen:
            continue
        seen.add(url)
        out.append(url)
    return out


def _candidate_hash_v0(candidate: Mapping[str, Any]) -> str:
    body = {key: value for key, value in dict(candidate).items() if key != "candidate_hash"}
    return hash_v0("zeno_ledger_dynamic_peer_candidate_v0", body)


def _admission_hash_v0(admission: Mapping[str, Any]) -> str:
    body = {key: value for key, value in dict(admission).items() if key != "admission_hash"}
    return hash_v0("zeno_ledger_dynamic_peer_admission_v0", body)


def build_dynamic_peer_candidate_v0(
    *,
    network_id: str,
    chain_id: str,
    source_node_id: str,
    source_peer_url: str,
    candidate_peer_urls: Sequence[object],
    observed_at_height: int,
    ttl_seconds: int = DEFAULT_DYNAMIC_PEER_TTL_SECONDS,
) -> dict[str, Any]:
    """Build a canonical dynamic peer candidate announcement."""

    candidates = canonical_peer_urls_v0(candidate_peer_urls, name="candidate_peer_urls")
    if not candidates:
        raise ValueError("dynamic peer candidate requires at least one candidate URL")
    body = {
        "schema": DYNAMIC_PEER_CANDIDATE_SCHEMA_V0,
        "ok": True,
        "status": "candidate",
        "network_id": _require_str(network_id, name="network_id"),
        "chain_id": _require_str(chain_id, name="chain_id", allow_empty=True),
        "source_node_id": _require_str(source_node_id, name="source_node_id"),
        "source_peer_url": canonical_peer_url_v0(source_peer_url, name="source_peer_url"),
        "candidate_peer_urls": candidates,
        "candidate_count": len(candidates),
        "observed_at_height": _require_nonnegative_int(observed_at_height, name="observed_at_height"),
        "ttl_seconds": _require_positive_int(ttl_seconds, name="ttl_seconds"),
    }
    return {**body, "candidate_hash": _candidate_hash_v0(body)}


def validate_dynamic_peer_candidate_v0(candidate: Mapping[str, Any]) -> None:
    obj = dict(_require_mapping(candidate, name="dynamic_peer_candidate"))
    if obj.get("schema") != DYNAMIC_PEER_CANDIDATE_SCHEMA_V0:
        raise ValueError("dynamic peer candidate schema mismatch")
    if obj.get("ok") is not True or obj.get("status") != "candidate":
        raise ValueError("dynamic peer candidate status mismatch")
    expected = build_dynamic_peer_candidate_v0(
        network_id=_require_str(obj.get("network_id"), name="dynamic_peer_candidate.network_id"),
        chain_id=_require_str(obj.get("chain_id"), name="dynamic_peer_candidate.chain_id", allow_empty=True),
        source_node_id=_require_str(obj.get("source_node_id"), name="dynamic_peer_candidate.source_node_id"),
        source_peer_url=canonical_peer_url_v0(
            obj.get("source_peer_url"),
            name="dynamic_peer_candidate.source_peer_url",
        ),
        candidate_peer_urls=canonical_peer_urls_v0(
            _require_sequence(obj.get("candidate_peer_urls"), name="dynamic_peer_candidate.candidate_peer_urls"),
            name="dynamic_peer_candidate.candidate_peer_urls",
        ),
        observed_at_height=_require_nonnegative_int(
            obj.get("observed_at_height"),
            name="dynamic_peer_candidate.observed_at_height",
        ),
        ttl_seconds=_require_positive_int(obj.get("ttl_seconds"), name="dynamic_peer_candidate.ttl_seconds"),
    )
    if obj != expected:
        raise ValueError("dynamic peer candidate binding mismatch")


def _peer_check_urls(peer_check_report: Mapping[str, Any]) -> list[str]:
    peers = _require_sequence(peer_check_report.get("peers"), name="peer_check_report.peers")
    return [
        canonical_peer_url_v0(
            _require_mapping(item, name=f"peer_check_report.peers[{index}]").get("peer_url"),
            name=f"peer_check_report.peers[{index}].peer_url",
        )
        for index, item in enumerate(peers)
    ]


def build_dynamic_peer_admission_v0(
    *,
    current_peer_urls: Sequence[object],
    candidate: Mapping[str, Any],
    peer_check_report: Mapping[str, Any],
    max_peer_count: int,
) -> dict[str, Any]:
    """Admit dynamic peers only after local peer checks and a peer-count cap."""

    candidate_obj = dict(_require_mapping(candidate, name="candidate"))
    validate_dynamic_peer_candidate_v0(candidate_obj)
    cap = _require_positive_int(max_peer_count, name="max_peer_count")
    current = canonical_peer_urls_v0(current_peer_urls, name="current_peer_urls")
    candidate_urls = canonical_peer_urls_v0(
        _require_sequence(candidate_obj.get("candidate_peer_urls"), name="candidate.candidate_peer_urls"),
        name="candidate.candidate_peer_urls",
    )
    if peer_check_report.get("schema") != "zenodex.zeno_ledger.node_peer_check_report.v0":
        raise ValueError("dynamic peer admission requires a peer-check report")
    if peer_check_report.get("network_id") != candidate_obj["network_id"]:
        raise ValueError("dynamic peer peer-check network mismatch")
    if peer_check_report.get("chain_id") != candidate_obj["chain_id"]:
        raise ValueError("dynamic peer peer-check chain mismatch")
    if peer_check_report.get("ok") is not True:
        raise ValueError("dynamic peer peer-check did not pass")
    if _peer_check_urls(peer_check_report) != candidate_urls:
        raise ValueError("dynamic peer peer-check URLs do not match candidate")
    for index, peer in enumerate(_require_sequence(peer_check_report.get("peers"), name="peer_check_report.peers")):
        peer_obj = _require_mapping(peer, name=f"peer_check_report.peers[{index}]")
        if peer_obj.get("ok") is not True:
            raise ValueError("dynamic peer candidate contains a rejected peer")

    current_set = set(current)
    admitted = [url for url in candidate_urls if url not in current_set]
    final_peer_urls = canonical_peer_urls_v0([*current, *admitted], name="final_peer_urls")
    if len(final_peer_urls) > cap:
        raise ValueError("dynamic peer admission exceeds max_peer_count")
    body = {
        "schema": DYNAMIC_PEER_ADMISSION_SCHEMA_V0,
        "ok": True,
        "status": "accepted",
        "network_id": candidate_obj["network_id"],
        "chain_id": candidate_obj["chain_id"],
        "candidate_hash": candidate_obj["candidate_hash"],
        "peer_check_hash": hash_v0("zeno_ledger_dynamic_peer_check_v0", dict(peer_check_report)),
        "max_peer_count": cap,
        "current_peer_count": len(current),
        "candidate_peer_count": len(candidate_urls),
        "admitted_peer_count": len(admitted),
        "final_peer_count": len(final_peer_urls),
        "admitted_peer_urls": admitted,
        "final_peer_urls": final_peer_urls,
    }
    return {**body, "admission_hash": _admission_hash_v0(body)}


def validate_dynamic_peer_admission_v0(
    *,
    admission: Mapping[str, Any],
    current_peer_urls: Sequence[object],
    candidate: Mapping[str, Any],
    peer_check_report: Mapping[str, Any],
    max_peer_count: int,
) -> None:
    expected = build_dynamic_peer_admission_v0(
        current_peer_urls=current_peer_urls,
        candidate=candidate,
        peer_check_report=peer_check_report,
        max_peer_count=max_peer_count,
    )
    if dict(_require_mapping(admission, name="dynamic_peer_admission")) != expected:
        raise ValueError("dynamic peer admission binding mismatch")
