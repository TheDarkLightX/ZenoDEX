#!/usr/bin/env python3
"""Run a Dockerized multi-node ZenoLedger network scenario.

The script is role-aware so Docker Compose can run each node in its own
container while a separate controller drives live writes, follower sync, and
adversarial HTTP checks.
"""

from __future__ import annotations

import argparse
import json
import os
import shutil
import sys
import tarfile
import tempfile
import time
from http import HTTPStatus
from pathlib import Path
from typing import Any
from urllib.error import HTTPError, URLError
from urllib.parse import urljoin, urlparse
from urllib.request import Request, urlopen

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.tau_net_client import bls_pubkey_hex_from_privkey, sign_dex_intent_for_engine
from src.integration.zeno_ledger_v0 import hash_v0
from src.state.pools import compute_pool_id
from tools.zeno_ledger_make_public_testnet_bundle import build_public_testnet_bundle_v0
from tools.zeno_ledger_make_testnet_bundle import (
    DEFAULT_ASSET0,
    DEFAULT_ASSET1,
    DEFAULT_BOOTSTRAP_SENDER,
    DEFAULT_CHAIN_ID,
    DEFAULT_RELEASE_TESTNET_TOKEN_SYMBOL,
    DEFAULT_SEQUENCER_ID,
    DEFAULT_TIME_MS,
)
from tools.zeno_ledger_node import (
    check_peer_status_v0,
    run_node_once_v0,
    serve_node_v0,
)
from tools.zeno_log_redaction import json_dumps_for_log


REPORT_SCHEMA = "zenodex.zeno_ledger.multidocker_scenario_report.v0"
PLAN_SCHEMA = "zenodex.zeno_ledger.multidocker_scenario_plan.v0"
NODE_IDENTITY_SCHEMA_V0 = "zenodex/zenoctl_node_identity/v0"
DEFAULT_TOKEN_ENV = "ZENO_LEDGER_WRITER_TOKEN"
MAX_HTTP_JSON_BYTES = 2 * 1024 * 1024
MAX_BUNDLE_ARCHIVE_BYTES = 32 * 1024 * 1024
PUBLIC_BUNDLE_ARCHIVE_NAME = "public_testnet_bundle.tar.gz"


def _write_stdout_json(value: Mapping[str, Any]) -> None:
    os.write(1, (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("utf-8"))
CONTROLLER_SENDER_PRIVKEY = 41


def _controller_sender_pubkey_v0() -> str:
    return "0x" + bls_pubkey_hex_from_privkey(CONTROLLER_SENDER_PRIVKEY)


def _with_controller_signature_v0(operation: dict[str, Any], *, chain_id: str) -> dict[str, Any]:
    signed = dict(operation)
    signed["signature"] = sign_dex_intent_for_engine(
        operation,
        privkey=CONTROLLER_SENDER_PRIVKEY,
        chain_id=chain_id,
    )
    return signed


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _load_json(path: Path) -> dict[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, dict):
        raise ValueError(f"{path} must decode to an object")
    return obj


def _is_http_base_url(value: str) -> bool:
    parsed = urlparse(value)
    return (
        parsed.scheme in {"http", "https"}
        and bool(parsed.netloc)
        and not parsed.username
        and not parsed.password
        and not parsed.query
        and not parsed.fragment
    )


def _require_http_base_url(value: str, *, name: str) -> str:
    if not isinstance(value, str) or not _is_http_base_url(value):
        raise ValueError(f"{name} must be an http(s) URL without embedded credentials, query, or fragment")
    return value.rstrip("/")


def _join_endpoint(base_url: str, endpoint: str) -> str:
    return urljoin(_require_http_base_url(base_url, name="base_url") + "/", endpoint.lstrip("/"))


def _run_chaos_harness_v0() -> dict[str, Any]:
    from tools.zeno_ledger_chaos_harness import run_chaos_harness

    result = run_chaos_harness()
    if isinstance(result, dict):
        return result
    return {"ok": False, "error": "chaos_harness_returned_non_object"}


def _read_bounded_response(response: Any, *, max_bytes: int, url: str) -> bytes:
    length = response.headers.get("Content-Length")
    if length is not None:
        try:
            declared = int(length)
        except ValueError as exc:
            raise ValueError(f"invalid Content-Length from {url}") from exc
        if declared > max_bytes:
            raise ValueError(f"response too large from {url}")
    data = response.read(max_bytes + 1)
    if len(data) > max_bytes:
        raise ValueError(f"response too large from {url}")
    return data


def validate_controller_config_v0(
    *,
    machine_count: int,
    writer_url: str,
    forwarder_url: str | None,
    readonly_url: str | None,
    node_data_dirs: list[Path],
) -> dict[str, Any]:
    errors: list[str] = []
    if machine_count not in {2, 3}:
        errors.append("machine_count_must_be_2_or_3")
    for name, value, required in (
        ("writer_url", writer_url, True),
        ("forwarder_url", forwarder_url, machine_count >= 2),
        ("readonly_url", readonly_url, machine_count >= 3),
    ):
        if value is None:
            if required:
                errors.append(f"{name}_required")
            continue
        try:
            _require_http_base_url(value, name=name)
        except ValueError:
            errors.append(f"{name}_invalid")
    if machine_count == 2 and readonly_url is not None:
        errors.append("readonly_url_not_allowed_for_two_machine_run")
    if len(node_data_dirs) < machine_count:
        errors.append("node_data_dir_count_below_machine_count")
    return {
        "schema": "zenodex.zeno_ledger.multidocker_controller_config_validation.v0",
        "ok": not errors,
        "errors": errors,
        "machine_count": machine_count,
        "node_data_dir_count": len(node_data_dirs),
    }


def _is_relative_safe_tar_name(name: str) -> bool:
    member_path = Path(name)
    return not member_path.is_absolute() and ".." not in member_path.parts


def _write_bundle_archive(*, bundle_root: Path, tar_out: Path) -> None:
    tar_out.parent.mkdir(parents=True, exist_ok=True)
    sidecar = bundle_root / PUBLIC_BUNDLE_ARCHIVE_NAME
    if sidecar.is_file() and sidecar.resolve() != tar_out.resolve():
        sidecar.unlink()
    with tarfile.open(tar_out, "w:gz") as archive:
        archive.add(bundle_root, arcname="bundle")


def _publish_bundle_archive_sidecar(*, bundle_root: Path, archive_path: Path) -> None:
    sidecar = bundle_root / PUBLIC_BUNDLE_ARCHIVE_NAME
    sidecar.parent.mkdir(parents=True, exist_ok=True)
    if archive_path.resolve() != sidecar.resolve():
        shutil.copyfile(archive_path, sidecar)


def _extract_bundle_archive(*, archive_path: Path, bundle_root: Path) -> None:
    with tarfile.open(archive_path, "r:gz") as archive:
        members = archive.getmembers()
        if not members:
            raise ValueError("bundle archive is empty")
        for member in members:
            if not _is_relative_safe_tar_name(member.name):
                raise ValueError(f"unsafe bundle archive member: {member.name}")
            if member.issym() or member.islnk():
                raise ValueError(f"bundle archive links are not allowed: {member.name}")
            if not (member.isdir() or member.isfile()):
                raise ValueError(f"bundle archive member type is not allowed: {member.name}")
        with tempfile.TemporaryDirectory(prefix="zeno-ledger-bundle-") as tmp:
            tmp_root = Path(tmp)
            for member in members:
                target = (tmp_root / member.name).resolve()
                try:
                    target.relative_to(tmp_root.resolve())
                except ValueError as exc:
                    raise ValueError(f"unsafe bundle archive target: {member.name}") from exc
                if member.isdir():
                    target.mkdir(parents=True, exist_ok=True)
                    continue
                source = archive.extractfile(member)
                if source is None:
                    raise ValueError(f"bundle archive member could not be read: {member.name}")
                target.parent.mkdir(parents=True, exist_ok=True)
                with source, target.open("wb") as out:
                    shutil.copyfileobj(source, out)
            extracted = tmp_root / "bundle"
            if not (extracted / "public_testnet_manifest.json").is_file():
                raise ValueError("bundle archive did not contain public_testnet_manifest.json")
            if bundle_root.exists():
                shutil.rmtree(bundle_root)
            bundle_root.parent.mkdir(parents=True, exist_ok=True)
            shutil.copytree(extracted, bundle_root)


def fetch_bundle_archive_v0(*, bundle_url: str, bundle_root: Path) -> dict[str, Any]:
    bundle_url = _require_http_base_url(bundle_url, name="bundle_url")
    with tempfile.TemporaryDirectory(prefix="zeno-ledger-bundle-fetch-") as tmp:
        archive_path = Path(tmp) / "bundle.tar.gz"
        with urlopen(bundle_url, timeout=60.0) as response:  # noqa: S310 - operator-supplied test URL
            if int(response.status) != HTTPStatus.OK:
                raise ValueError(f"bundle fetch failed with status {response.status}")
            archive_path.write_bytes(
                _read_bounded_response(response, max_bytes=MAX_BUNDLE_ARCHIVE_BYTES, url=bundle_url)
            )
        _extract_bundle_archive(archive_path=archive_path, bundle_root=bundle_root)
    return {
        "schema": "zenodex.zeno_ledger.multidocker_bundle_fetch_report.v0",
        "ok": True,
        "status": "accepted",
        "bundle_url": bundle_url,
        "bundle_root": str(bundle_root),
    }


def derive_docker_node_hash_v0(*, network_id: str, chain_id: str, node_identity: str) -> str:
    if network_id == "" or chain_id == "" or node_identity == "":
        raise ValueError("network_id, chain_id, and node_identity must be non-empty")
    body = {
        "schema": NODE_IDENTITY_SCHEMA_V0,
        "network_id": network_id,
        "chain_id": chain_id,
        "identity_kind": "docker-node-public-identity",
        "node_identity": node_identity,
    }
    return hash_v0("zenoctl_node_identity_v0", body)


def build_multidocker_plan_v0(*, machine_count: int, network_id: str, chain_id: str) -> dict[str, Any]:
    if machine_count not in {2, 3}:
        raise ValueError("machine_count must be 2 or 3")
    if network_id == "" or chain_id == "":
        raise ValueError("network_id and chain_id must be non-empty")
    nodes: list[dict[str, Any]] = []
    for index, name in enumerate(("writer", "forwarder", "readonly")[:machine_count]):
        identity = f"docker://zeno-ledger-{name}/{network_id}/{chain_id}"
        nodes.append(
            {
                "index": index,
                "role": name,
                "node_identity": identity,
                "node_hash": derive_docker_node_hash_v0(
                    network_id=network_id,
                    chain_id=chain_id,
                    node_identity=identity,
                ),
                "url": f"http://zeno-ledger-{name}:8787",
            }
        )
    return {
        "schema": PLAN_SCHEMA,
        "ok": True,
        "machine_count": machine_count,
        "network_id": network_id,
        "chain_id": chain_id,
        "nodes": nodes,
        "live_trade_series": [
            "writer_faucet_existing_asset",
            "writer_swap_exact_in",
            "writer_faucet_new_asset",
            "writer_create_pool",
            "writer_add_liquidity",
            "writer_remove_liquidity",
            "forwarded_faucet_from_follower",
        ],
        "adversarial_http_checks": [
            "unauthorized_writer_faucet_rejected",
            "malformed_writer_tx_rejected",
            "oversized_writer_faucet_rejected",
            "readonly_follower_faucet_rejected",
        ],
        "model_chaos_checks": [
            "peer_churn",
            "gossip_flood",
            "equivocation",
            "fork_choice",
            "auth_failures",
            "validator_schedule",
            "live_quorum",
            "degraded_network",
        ],
        "disaster_states": [
            "unauthorized_write_accepted",
            "malformed_tx_accepted",
            "oversized_faucet_accepted",
            "readonly_node_mutated",
            "follower_failed_to_converge",
            "same_height_conflict_silent",
            "duplicate_gossip_applied_twice",
            "wrong_chain_peer_admitted",
        ],
    }


def _http_json(url: str, *, timeout: float = 10.0) -> tuple[int, dict[str, Any]]:
    _require_http_base_url(url, name="url")
    with urlopen(url, timeout=timeout) as response:  # noqa: S310 - local Docker test network
        body = _read_bounded_response(response, max_bytes=MAX_HTTP_JSON_BYTES, url=url).decode("utf-8")
        obj = json.loads(body)
        if not isinstance(obj, dict):
            raise ValueError(f"{url} returned non-object JSON")
        return int(response.status), obj


def _post_json(
    url: str,
    value: dict[str, Any],
    *,
    token: str | None = None,
    timeout: float = 10.0,
) -> tuple[int, dict[str, Any]]:
    _require_http_base_url(url, name="url")
    payload = json.dumps(value, sort_keys=True).encode("utf-8")
    if len(payload) > MAX_HTTP_JSON_BYTES:
        raise ValueError("request body too large")
    headers = {"Content-Type": "application/json"}
    if token is not None:
        headers["Authorization"] = f"Bearer {token}"
    request = Request(url, data=payload, headers=headers, method="POST")
    try:
        with urlopen(request, timeout=timeout) as response:  # noqa: S310 - local Docker test network
            body = _read_bounded_response(response, max_bytes=MAX_HTTP_JSON_BYTES, url=url).decode("utf-8")
            obj = json.loads(body)
            if not isinstance(obj, dict):
                raise ValueError(f"{url} returned non-object JSON")
            return int(response.status), obj
    except HTTPError as exc:
        body = exc.read(MAX_HTTP_JSON_BYTES + 1)
        if len(body) > MAX_HTTP_JSON_BYTES:
            raise ValueError(f"error response too large from {url}") from exc
        text = body.decode("utf-8")
        try:
            obj = json.loads(text)
        except json.JSONDecodeError:
            obj = {"ok": False, "error": text}
        if not isinstance(obj, dict):
            obj = {"ok": False, "error": str(obj)}
        return int(exc.code), obj


def _wait_for_status(url: str, *, timeout_seconds: float) -> dict[str, Any]:
    url = _require_http_base_url(url, name="url")
    deadline = time.monotonic() + timeout_seconds
    last_error: str | None = None
    while time.monotonic() < deadline:
        try:
            status, obj = _http_json(_join_endpoint(url, "status"), timeout=5.0)
            if status == HTTPStatus.OK and obj.get("ok") is True:
                return obj
            last_error = f"status={status} body={obj}"
        except (OSError, URLError, ValueError) as exc:
            last_error = str(exc)
        time.sleep(0.5)
    raise TimeoutError(f"node did not become ready at {url}: {last_error}")


def _wait_for_tip(url: str, *, height: int, timeout_seconds: float) -> dict[str, Any]:
    url = _require_http_base_url(url, name="url")
    deadline = time.monotonic() + timeout_seconds
    last: dict[str, Any] | None = None
    while time.monotonic() < deadline:
        _, network = _http_json(_join_endpoint(url, "network"), timeout=5.0)
        last = network
        tip = network.get("local_tip")
        if isinstance(tip, dict) and int(tip.get("height", -1)) >= height:
            return network
        time.sleep(0.5)
    raise TimeoutError(f"{url} did not reach height {height}; last={last}")


def _auth_token_from_env(env_name: str) -> str:
    token = os.environ.get(env_name)
    if token is None or token == "":
        raise ValueError(f"{env_name} must be set")
    return token


def _lp_duration_risk_policy(policy_name: str):
    if policy_name in {"", "none"}:
        return None
    if policy_name == "zeno-oracle":
        from src.integration.zeno_oracle_fail_closed_config import (  # pylint: disable=import-outside-toplevel
            ZENO_ORACLE_LP_DURATION_RISK_POLICY,
        )

        return ZENO_ORACLE_LP_DURATION_RISK_POLICY
    raise ValueError(f"unsupported LP duration-risk policy: {policy_name}")


def _wait_for_bundle(bundle_root: Path, *, timeout_seconds: float = 120.0) -> None:
    manifest = bundle_root / "public_testnet_manifest.json"
    deadline = time.monotonic() + timeout_seconds
    while time.monotonic() < deadline:
        if manifest.is_file():
            return
        time.sleep(0.25)
    raise TimeoutError(f"bundle manifest did not appear: {manifest}")


def _wait_for_bundle_archive_sidecar(bundle_root: Path, *, timeout_seconds: float = 30.0) -> None:
    archive = bundle_root / PUBLIC_BUNDLE_ARCHIVE_NAME
    deadline = time.monotonic() + timeout_seconds
    while time.monotonic() < deadline:
        if archive.is_file() and archive.stat().st_size > 0:
            return
        time.sleep(0.25)


def bootstrap_bundle_v0(
    *,
    bundle_root: Path,
    network_id: str,
    chain_id: str,
    report_out: Path,
    bundle_tar_out: Path | None = None,
    token_symbol: str = DEFAULT_RELEASE_TESTNET_TOKEN_SYMBOL,
    fixture_key_bundle_path: Path | None = None,
) -> dict[str, Any]:
    report = build_public_testnet_bundle_v0(
        out_dir=bundle_root,
        network_id=network_id,
        chain_id=chain_id,
        sequencer_id=DEFAULT_SEQUENCER_ID,
        time_ms=DEFAULT_TIME_MS,
        token_symbol=token_symbol,
        fixture_key_bundle_path=fixture_key_bundle_path,
    )
    wrapped = {
        "schema": "zenodex.zeno_ledger.multidocker_bootstrap_report.v0",
        "ok": report.get("ok") is True,
        "status": "accepted" if report.get("ok") is True else "rejected",
        "bundle_root": str(bundle_root),
        "bundle_tar_out": str(bundle_tar_out) if bundle_tar_out is not None else None,
        "build_report": report,
    }
    if wrapped["ok"] and bundle_tar_out is not None:
        _write_bundle_archive(bundle_root=bundle_root, tar_out=bundle_tar_out)
        _publish_bundle_archive_sidecar(bundle_root=bundle_root, archive_path=bundle_tar_out)
    _write_json(report_out, wrapped)
    return wrapped


def serve_role_v0(
    *,
    role: str,
    bundle_root: Path,
    bundle_url: str | None,
    data_dir: Path,
    network_id: str,
    chain_id: str,
    host: str,
    port: int,
    peer_urls: list[str],
    poll_seconds: int,
    write_auth_token_env: str | None,
    submit_peer_url: str | None,
    submit_peer_auth_token_env: str | None,
    enable_testnet_intake: bool,
    enable_testnet_faucet: bool,
    expose_testnet_faucet_http: bool,
    min_lp_position_age_seconds: int,
    lp_duration_risk_policy_name: str,
) -> None:
    peer_urls = [_require_http_base_url(url, name="peer_url") for url in peer_urls]
    submit_peer_url = (
        _require_http_base_url(submit_peer_url, name="submit_peer_url")
        if submit_peer_url is not None
        else None
    )
    if bundle_url and not (bundle_root / "public_testnet_manifest.json").is_file():
        fetch_bundle_archive_v0(bundle_url=bundle_url, bundle_root=bundle_root)
    _wait_for_bundle(bundle_root)
    _wait_for_bundle_archive_sidecar(bundle_root)
    data_dir.mkdir(parents=True, exist_ok=True)
    local_bundle_root = data_dir / "bundle"
    if not (local_bundle_root / "public_testnet_manifest.json").is_file():
        if local_bundle_root.exists():
            shutil.rmtree(local_bundle_root)
        shutil.copytree(bundle_root, local_bundle_root)
    identity = f"docker://zeno-ledger-{role}/{network_id}/{chain_id}"
    node_hash = derive_docker_node_hash_v0(network_id=network_id, chain_id=chain_id, node_identity=identity)
    watcher_path = local_bundle_root / "bootstrap" / "watcher_attestations" / "bootstrap_range_1_5.json"
    run_node_once_v0(
        bundle_root=local_bundle_root,
        node_id=node_hash,
        data_dir=data_dir,
        peer_watcher_attestation_paths=[watcher_path],
    )
    write_auth_token = _auth_token_from_env(write_auth_token_env) if write_auth_token_env else None
    submit_peer_auth_token = _auth_token_from_env(submit_peer_auth_token_env) if submit_peer_auth_token_env else None
    serve_node_v0(
        data_dir=data_dir,
        host=host,
        port=port,
        peer_urls=peer_urls,
        poll_seconds=poll_seconds,
        enable_testnet_intake=enable_testnet_intake,
        enable_testnet_faucet=enable_testnet_faucet,
        expose_testnet_faucet_http=expose_testnet_faucet_http,
        min_lp_position_age_seconds=min_lp_position_age_seconds,
        lp_duration_risk_policy=_lp_duration_risk_policy(lp_duration_risk_policy_name),
        submit_peer_url=submit_peer_url,
        write_auth_token=write_auth_token or None,
        submit_peer_auth_token=submit_peer_auth_token or None,
    )


def _swap_tx(asset_a: str, asset_b: str, *, sender_pubkey: str, chain_id: str) -> dict[str, Any]:
    operation = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "SWAP_EXACT_IN",
        "intent_id": "0x" + "bb" * 32,
        "sender_pubkey": sender_pubkey,
        "deadline": 1_999_999_999,
        "nonce": 1,
        "pool_id": compute_pool_id(asset_a, asset_b, 30),
        "asset_in": asset_a,
        "asset_out": asset_b,
        "amount_in": 100,
        "min_amount_out": 1,
        "recipient": sender_pubkey,
    }
    return {
        "tx_id": "multidocker-live-swap-v0",
        "block_timestamp": (DEFAULT_TIME_MS + 1_001_000) // 1000,
        "tx_sender_pubkey": sender_pubkey,
        "operations": {"19": [_with_controller_signature_v0(operation, chain_id=chain_id)]},
    }


def _create_pool_tx(asset_a: str, new_asset: str, *, sender_pubkey: str, chain_id: str) -> dict[str, Any]:
    asset0 = min(asset_a, new_asset)
    asset1 = max(asset_a, new_asset)
    operation = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "CREATE_POOL",
        "intent_id": "0x" + "cc" * 32,
        "sender_pubkey": sender_pubkey,
        "deadline": 1_999_999_999,
        "nonce": 2,
        "asset0": asset0,
        "asset1": asset1,
        "fee_bps": 30,
        "amount0": 10_000,
        "amount1": 10_000,
        "created_at": (DEFAULT_TIME_MS + 1_003_000) // 1000,
    }
    return {
        "tx_id": "multidocker-create-fake-token-pool-v0",
        "block_timestamp": (DEFAULT_TIME_MS + 1_003_000) // 1000,
        "tx_sender_pubkey": sender_pubkey,
        "operations": {"19": [_with_controller_signature_v0(operation, chain_id=chain_id)]},
    }


def _liquidity_tx(
    *,
    kind: str,
    pool_id: str,
    tx_id: str,
    intent_byte: str,
    nonce: int,
    sender_pubkey: str,
    chain_id: str,
) -> dict[str, Any]:
    operation: dict[str, Any] = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": kind,
        "intent_id": "0x" + intent_byte * 32,
        "sender_pubkey": sender_pubkey,
        "deadline": 1_999_999_999,
        "nonce": nonce,
        "pool_id": pool_id,
        "amount0_min": 0,
        "amount1_min": 0,
        "recipient": sender_pubkey,
    }
    if kind == "ADD_LIQUIDITY":
        operation.update({"amount0_desired": 100, "amount1_desired": 100})
    else:
        operation.update({"lp_amount": 1})
    timestamp_base_ms = DEFAULT_TIME_MS + (4_004_000 if kind == "REMOVE_LIQUIDITY" else 1_004_000)
    return {
        "tx_id": tx_id,
        "block_timestamp": (timestamp_base_ms + nonce) // 1000,
        "tx_sender_pubkey": sender_pubkey,
        "operations": {"19": [_with_controller_signature_v0(operation, chain_id=chain_id)]},
    }


def _valid_trade_series(writer_url: str, forwarder_url: str | None, *, token: str, chain_id: str) -> dict[str, Any]:
    asset_a = min(DEFAULT_ASSET0, DEFAULT_ASSET1)
    asset_b = max(DEFAULT_ASSET0, DEFAULT_ASSET1)
    new_asset = "0x" + "33" * 32
    pool_id = compute_pool_id(min(asset_a, new_asset), max(asset_a, new_asset), 30)
    sender_pubkey = _controller_sender_pubkey_v0()
    steps: list[dict[str, Any]] = []

    def post(path: str, body: dict[str, Any], *, url: str = writer_url) -> dict[str, Any]:
        status, response = _post_json(_join_endpoint(url, path), body, token=token, timeout=30.0)
        accepted = (
            status == HTTPStatus.OK
            and response.get("ok") is True
            and _append_response_accepted_v0(path=path, response=response)
        )
        steps.append({"path": path, "url": url, "status": status, "ok": accepted, "response": response})
        if not accepted:
            raise RuntimeError(f"valid scenario step failed: {url}{path} status={status} response={response}")
        return response

    faucet_existing = post(
        "/faucet",
        {
            "to_pubkey": sender_pubkey,
            "asset": asset_a,
            "amount": 100_000,
            "local_fixture_mode": True,
            "time_ms": DEFAULT_TIME_MS + 1_000_000,
            "tx_id": "multidocker-faucet-existing-asset-v0",
        },
    )
    swap = post(
        "/tx",
        {
            "tx": _swap_tx(asset_a, asset_b, sender_pubkey=sender_pubkey, chain_id=chain_id),
            "time_ms": DEFAULT_TIME_MS + 1_001_000,
        },
    )
    faucet_new = post(
        "/faucet",
        {
            "to_pubkey": sender_pubkey,
            "asset": new_asset,
            "amount": 100_000,
            "local_fixture_mode": True,
            "time_ms": DEFAULT_TIME_MS + 1_002_000,
            "tx_id": "multidocker-faucet-new-asset-v0",
        },
    )
    create_pool = post(
        "/tx",
        {
            "tx": _create_pool_tx(asset_a, new_asset, sender_pubkey=sender_pubkey, chain_id=chain_id),
            "time_ms": DEFAULT_TIME_MS + 1_003_000,
        },
    )
    add_liquidity = post(
        "/tx",
        {
            "tx": _liquidity_tx(
                kind="ADD_LIQUIDITY",
                pool_id=pool_id,
                tx_id="multidocker-add-fake-token-liquidity-v0",
                intent_byte="cd",
                nonce=3,
                sender_pubkey=sender_pubkey,
                chain_id=chain_id,
            ),
            "time_ms": DEFAULT_TIME_MS + 1_004_000,
        },
    )
    remove_liquidity = post(
        "/tx",
        {
            "tx": _liquidity_tx(
                kind="REMOVE_LIQUIDITY",
                pool_id=pool_id,
                tx_id="multidocker-remove-fake-token-liquidity-v0",
                intent_byte="ce",
                nonce=4,
                sender_pubkey=sender_pubkey,
                chain_id=chain_id,
            ),
            "time_ms": DEFAULT_TIME_MS + 1_005_000,
        },
    )
    forwarded_faucet: dict[str, Any] | None = None
    if forwarder_url is not None:
        forwarded_faucet = post(
            "/faucet",
            {
                "to_pubkey": sender_pubkey,
                "asset": asset_a,
                "amount": 55,
                "local_fixture_mode": True,
                "time_ms": DEFAULT_TIME_MS + 1_006_000,
                "tx_id": "multidocker-forwarded-faucet-v0",
            },
            url=forwarder_url,
        )

    expected_height = 12 if forwarded_faucet is not None else 11
    return {
        "ok": True,
        "steps": steps,
        "expected_final_height": expected_height,
        "heights": {
            "faucet_existing": faucet_existing["height"],
            "swap": swap["height"],
            "faucet_new_asset": faucet_new["height"],
            "create_pool": create_pool["height"],
            "add_liquidity": add_liquidity["height"],
            "remove_liquidity": remove_liquidity["height"],
            "forwarded_faucet": forwarded_faucet.get("height") if forwarded_faucet else None,
        },
    }


def _append_response_accepted_v0(*, path: str, response: dict[str, Any]) -> bool:
    """Return whether a live append response actually accepted the operation.

    ZenoLedger append endpoints can return HTTP 200 with ``ok=true`` while the
    transaction receipt rejects the operation. The multi-node live scenario is
    a success-path controller, so it must fail on those receipt-level rejects.
    """
    if response.get("tx_accepted") is False:
        return False
    receipt = response.get("receipt")
    if isinstance(receipt, dict) and receipt.get("accepted") is False:
        return False
    if path == "/tx":
        return response.get("tx_accepted") is True or (
            isinstance(receipt, dict) and receipt.get("accepted") is True
        )
    if path == "/faucet":
        return not isinstance(receipt, dict) or receipt.get("accepted") is True
    return True


def _adversarial_http_checks(
    *,
    writer_url: str,
    readonly_url: str | None,
    token: str,
) -> dict[str, Any]:
    checks: list[dict[str, Any]] = []

    def record(name: str, status: int, response: dict[str, Any], accepted_statuses: set[int]) -> None:
        checks.append(
            {
                "name": name,
                "ok": status in accepted_statuses and response.get("ok") is not True,
                "status": status,
                "response": response,
            }
        )

    status, response = _post_json(
        _join_endpoint(writer_url, "faucet"),
        {
            "to_pubkey": DEFAULT_BOOTSTRAP_SENDER,
            "asset": min(DEFAULT_ASSET0, DEFAULT_ASSET1),
            "amount": 1,
            "tx_id": "multidocker-unauthorized-faucet-v0",
        },
        token=None,
    )
    record("unauthorized_writer_faucet_rejected", status, response, {HTTPStatus.UNAUTHORIZED})

    status, response = _post_json(
        _join_endpoint(writer_url, "tx"),
        {"tx": "bad", "time_ms": DEFAULT_TIME_MS + 2_000_000},
        token=token,
    )
    record("malformed_writer_tx_rejected", status, response, {HTTPStatus.BAD_REQUEST})

    status, response = _post_json(
        _join_endpoint(writer_url, "faucet"),
        {
            "to_pubkey": DEFAULT_BOOTSTRAP_SENDER,
            "asset": min(DEFAULT_ASSET0, DEFAULT_ASSET1),
            "amount": 10**18,
            "tx_id": "multidocker-oversized-faucet-v0",
        },
        token=token,
    )
    # Fixture-ack hardening can reject before amount validation; both layers are fail-closed.
    record("oversized_writer_faucet_rejected", status, response, {HTTPStatus.BAD_REQUEST, HTTPStatus.FORBIDDEN})

    if readonly_url is not None:
        status, response = _post_json(
            _join_endpoint(readonly_url, "faucet"),
            {
                "to_pubkey": DEFAULT_BOOTSTRAP_SENDER,
                "asset": min(DEFAULT_ASSET0, DEFAULT_ASSET1),
                "amount": 1,
                "tx_id": "multidocker-readonly-faucet-v0",
            },
            token=token,
        )
        record("readonly_follower_faucet_rejected", status, response, {HTTPStatus.FORBIDDEN})

    return {
        "ok": all(check["ok"] for check in checks),
        "check_count": len(checks),
        "checks": checks,
    }


def run_controller_v0(
    *,
    machine_count: int,
    writer_url: str,
    forwarder_url: str | None,
    readonly_url: str | None,
    node_data_dirs: list[Path],
    network_id: str,
    chain_id: str,
    write_auth_token_env: str,
    report_out: Path,
    timeout_seconds: float,
) -> dict[str, Any]:
    start = time.perf_counter()
    validation = validate_controller_config_v0(
        machine_count=machine_count,
        writer_url=writer_url,
        forwarder_url=forwarder_url,
        readonly_url=readonly_url,
        node_data_dirs=node_data_dirs,
    )
    if not validation["ok"]:
        report = {
            "schema": REPORT_SCHEMA,
            "ok": False,
            "status": "rejected",
            "errors": list(validation["errors"]),
            "elapsed_ms": (time.perf_counter() - start) * 1000.0,
            "machine_count": machine_count,
            "network_id": network_id,
            "chain_id": chain_id,
            "controller_config_validation": validation,
            "report_out": str(report_out),
        }
        _write_json(report_out, report)
        return report
    token = _auth_token_from_env(write_auth_token_env)
    plan = build_multidocker_plan_v0(machine_count=machine_count, network_id=network_id, chain_id=chain_id)
    urls = [writer_url]
    if forwarder_url is not None:
        urls.append(forwarder_url)
    if readonly_url is not None:
        urls.append(readonly_url)
    statuses = [_wait_for_status(url, timeout_seconds=timeout_seconds) for url in urls]
    adversarial = _adversarial_http_checks(writer_url=writer_url, readonly_url=readonly_url, token=token)
    trade_series = _valid_trade_series(writer_url, forwarder_url, token=token, chain_id=chain_id)
    expected_height = int(trade_series["expected_final_height"])
    tip_reports = [_wait_for_tip(url, height=expected_height, timeout_seconds=timeout_seconds) for url in urls]
    peer_checks = [
        check_peer_status_v0(data_dir=data_dir, peer_urls=[writer_url])
        for data_dir in node_data_dirs[1:]
        if data_dir.exists()
    ]
    chaos = _run_chaos_harness_v0()
    errors: list[str] = []
    if not adversarial["ok"]:
        errors.append("one or more adversarial HTTP checks failed")
    if not all(check.get("ok") is True for check in peer_checks):
        errors.append("one or more follower peer checks failed")
    if chaos.get("ok") is not True:
        errors.append("deterministic chaos harness failed")
    for network in tip_reports:
        tip = network.get("local_tip")
        if not isinstance(tip, dict) or int(tip.get("height", -1)) < expected_height:
            errors.append("a node did not converge to the expected final height")
    observed_node_hashes = [str(status["node_id"]) for status in statuses]
    planned_hashes = [str(node["node_hash"]) for node in plan["nodes"]]
    if observed_node_hashes != planned_hashes[: len(observed_node_hashes)]:
        errors.append("observed node hashes do not match the multidocker plan")
    report = {
        "schema": REPORT_SCHEMA,
        "ok": not errors,
        "status": "accepted" if not errors else "rejected",
        "errors": errors,
        "elapsed_ms": (time.perf_counter() - start) * 1000.0,
        "machine_count": machine_count,
        "network_id": network_id,
        "chain_id": chain_id,
        "controller_config_validation": validation,
        "plan": plan,
        "node_statuses": statuses,
        "observed_node_hashes": observed_node_hashes,
        "adversarial_http": adversarial,
        "trade_series": trade_series,
        "tip_reports": tip_reports,
        "peer_checks": peer_checks,
        "chaos_harness": chaos,
        "report_out": str(report_out),
    }
    _write_json(report_out, report)
    return report


def _cmd_plan(args: argparse.Namespace) -> int:
    plan = build_multidocker_plan_v0(machine_count=args.machine_count, network_id=args.network_id, chain_id=args.chain_id)
    print(json.dumps(plan, indent=2, sort_keys=True))
    return 0


def _cmd_bootstrap(args: argparse.Namespace) -> int:
    report = bootstrap_bundle_v0(
        bundle_root=args.bundle_root,
        network_id=args.network_id,
        chain_id=args.chain_id,
        report_out=args.report_out,
        bundle_tar_out=args.bundle_tar_out,
        token_symbol=args.token_symbol,
        fixture_key_bundle_path=args.fixture_key_bundle,
    )
    public_report = {
        key: report[key]
        for key in (
            "schema",
            "ok",
            "status",
            "bundle_root",
            "public_manifest_path",
            "launch_manifest_path",
            "testnet_status_path",
            "testnet_status_hash",
            "bundle_archive_path",
            "bundle_archive_sha256",
            "report_path",
        )
        if key in report
    }
    if report.get("ok") is not True:
        errors = report.get("errors")
        public_report["error_count"] = len(errors) if isinstance(errors, list) else 1
    _write_stdout_json(public_report)
    sys.stdout.flush()
    if args.stay_alive and report["ok"]:
        while True:
            time.sleep(3600)
    return 0 if report["ok"] else 1


def _cmd_fetch_bundle(args: argparse.Namespace) -> int:
    report = fetch_bundle_archive_v0(bundle_url=args.bundle_url, bundle_root=args.bundle_root)
    if args.report_out is not None:
        _write_json(args.report_out, report)
    print(json_dumps_for_log(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


def _cmd_serve_node(args: argparse.Namespace) -> int:
    serve_role_v0(
        role=args.role,
        bundle_root=args.bundle_root,
        bundle_url=args.bundle_url,
        data_dir=args.data_dir,
        network_id=args.network_id,
        chain_id=args.chain_id,
        host=args.host,
        port=args.port,
        peer_urls=args.peer_url,
        poll_seconds=args.poll_seconds,
        write_auth_token_env=args.write_auth_token_env,
        submit_peer_url=args.submit_peer_url,
        submit_peer_auth_token_env=args.submit_peer_auth_token_env,
        enable_testnet_intake=args.enable_testnet_intake,
        enable_testnet_faucet=args.enable_testnet_faucet,
        expose_testnet_faucet_http=args.expose_testnet_faucet_http,
        min_lp_position_age_seconds=args.min_lp_position_age_seconds,
        lp_duration_risk_policy_name=args.lp_duration_risk_policy,
    )
    return 0


def _cmd_controller(args: argparse.Namespace) -> int:
    report = run_controller_v0(
        machine_count=args.machine_count,
        writer_url=args.writer_url,
        forwarder_url=args.forwarder_url,
        readonly_url=args.readonly_url,
        node_data_dirs=args.node_data_dir,
        network_id=args.network_id,
        chain_id=args.chain_id,
        write_auth_token_env=args.write_auth_token_env,
        report_out=args.report_out,
        timeout_seconds=args.timeout_seconds,
    )
    print(json_dumps_for_log(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)

    plan = sub.add_parser("plan", help="print the expected multi-Docker node plan")
    plan.add_argument("--machine-count", type=int, choices=[2, 3], default=3)
    plan.add_argument("--network-id", default=DEFAULT_CHAIN_ID)
    plan.add_argument("--chain-id", default=DEFAULT_CHAIN_ID)
    plan.set_defaults(func=_cmd_plan)

    bootstrap = sub.add_parser("bootstrap", help="build the shared public-testnet bundle")
    bootstrap.add_argument("--bundle-root", required=True, type=Path)
    bootstrap.add_argument("--network-id", default=DEFAULT_CHAIN_ID)
    bootstrap.add_argument("--chain-id", default=DEFAULT_CHAIN_ID)
    bootstrap.add_argument("--report-out", required=True, type=Path)
    bootstrap.add_argument("--bundle-tar-out", type=Path)
    bootstrap.add_argument("--token-symbol", default=DEFAULT_RELEASE_TESTNET_TOKEN_SYMBOL)
    bootstrap.add_argument("--fixture-key-bundle", type=Path)
    bootstrap.add_argument("--stay-alive", action="store_true", help="keep the bootstrap container alive after success")
    bootstrap.set_defaults(func=_cmd_bootstrap)

    fetch = sub.add_parser("fetch-bundle", help="fetch and unpack a bootstrap bundle archive")
    fetch.add_argument("--bundle-url", required=True)
    fetch.add_argument("--bundle-root", required=True, type=Path)
    fetch.add_argument("--report-out", type=Path)
    fetch.set_defaults(func=_cmd_fetch_bundle)

    serve = sub.add_parser("serve-node", help="run and serve one Dockerized node role")
    serve.add_argument("--role", required=True, choices=["writer", "forwarder", "readonly"])
    serve.add_argument("--bundle-root", required=True, type=Path)
    serve.add_argument("--bundle-url", help="fetch this bundle archive URL if bundle-root is empty")
    serve.add_argument("--data-dir", required=True, type=Path)
    serve.add_argument("--network-id", default=DEFAULT_CHAIN_ID)
    serve.add_argument("--chain-id", default=DEFAULT_CHAIN_ID)
    serve.add_argument("--host", default="0.0.0.0")
    serve.add_argument("--port", type=int, default=8787)
    serve.add_argument("--peer-url", action="append", default=[])
    serve.add_argument("--poll-seconds", type=int, default=0)
    serve.add_argument("--write-auth-token-env")
    serve.add_argument("--submit-peer-url")
    serve.add_argument("--submit-peer-auth-token-env")
    serve.add_argument("--enable-testnet-intake", action="store_true")
    serve.add_argument("--enable-testnet-faucet", action="store_true")
    serve.add_argument("--expose-testnet-faucet-http", action="store_true")
    serve.add_argument("--min-lp-position-age-seconds", type=int, default=0)
    serve.add_argument("--lp-duration-risk-policy", choices=["none", "zeno-oracle"], default="none")
    serve.set_defaults(func=_cmd_serve_node)

    controller = sub.add_parser("controller", help="drive writes, adversarial checks, convergence, and evidence")
    controller.add_argument("--machine-count", type=int, choices=[2, 3], default=3)
    controller.add_argument("--writer-url", required=True)
    controller.add_argument("--forwarder-url")
    controller.add_argument("--readonly-url")
    controller.add_argument("--node-data-dir", action="append", default=[], type=Path)
    controller.add_argument("--network-id", default=DEFAULT_CHAIN_ID)
    controller.add_argument("--chain-id", default=DEFAULT_CHAIN_ID)
    controller.add_argument("--write-auth-token-env", default=DEFAULT_TOKEN_ENV)
    controller.add_argument("--report-out", required=True, type=Path)
    controller.add_argument("--timeout-seconds", type=float, default=120.0)
    controller.set_defaults(func=_cmd_controller)

    args = parser.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
